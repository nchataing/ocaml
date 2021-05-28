(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1998 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Types

let get_unboxed_type_representation env ty =
  match Typedecl_unboxed.get_unboxed_type_representation env ty with
  | Typedecl_unboxed.This x -> Some x
  | _ -> None

let scrape_ty env ty =
  let ty = Ctype.expand_head_opt env (Ctype.correct_levels ty) in
  match ty.desc with
  | Tconstr (p, _, _) ->
      begin match Env.find_type p env with
      | {type_kind = ( Type_variant (_, Variant_unboxed)
                     | Type_record (_, Record_unboxed _) ); _} ->
        begin match get_unboxed_type_representation env ty with
        | None -> ty
        | Some ty2 -> ty2
        end
      | _ -> ty
      | exception Not_found -> ty
      end
  | _ -> ty

exception Conflict

type t = head_shape

let any = { head_imm = Shape_any; head_blocks = Shape_any }

let none = { head_imm = Shape_set []; head_blocks = Shape_set [] }

let block_shape tags =
  { head_imm = Shape_set []; head_blocks = Shape_set tags }

let cstrs_shape ~num_consts ~num_nonconsts =
  let int_list n = List.init n Fun.id in
  {
    head_imm = Shape_set (int_list num_consts);
    head_blocks = Shape_set (int_list num_nonconsts)
  }

let disjoint_union hd1 hd2 =
  let union s1 s2 = match s1, s2 with
  | Shape_any, Shape_set [] | Shape_set [], Shape_any -> Shape_any
  | Shape_any, _ | _, Shape_any -> raise Conflict
  | Shape_set l1, Shape_set l2 ->
      (* invariant : l1 and l2 are sorted *)
      let rec merge l1 l2 = match l1, l2 with
      | [], l | l, [] -> l
      | x :: xx, y :: yy ->
          if x = y then raise Conflict
          else if x < y then x :: (merge xx l2)
          else y :: (merge l1 yy)
      in Shape_set (merge l1 l2)
  in
  {
    head_imm = union hd1.head_imm hd2.head_imm;
    head_blocks = union hd1.head_blocks hd2.head_blocks
  }

let rec of_type env ty =
  let ty = scrape_ty env ty in
  match ty.desc with
  | Tvar _ | Tunivar _ -> any
  | Tconstr (p, args, _abbrev) ->
      if Path.same p Predef.path_float then block_shape [Obj.double_tag]
      else if Path.same p Predef.path_string
           || Path.same p Predef.path_bytes then block_shape [Obj.string_tag]
      else if Path.same p Predef.path_array then
        block_shape
          (if Config.flat_float_array then [0]
           else [0; Obj.double_array_tag])
      else if Path.same p Predef.path_floatarray then
        block_shape [Obj.double_array_tag]
      else if Path.same p Predef.path_int then
        { head_imm = Shape_any; head_blocks = Shape_set [] }
      else if Path.same p Predef.path_lazy_t then
        (* Lazy values can 'shortcut' the lazy block, and thus have many
           different tags. When Config.flat_float_array, they
           cannot be floats, so we might want to refine that if there
           are strong use-cases. *)
        any
      else if Path.same p Predef.path_nativeint
           || Path.same p Predef.path_int32
           || Path.same p Predef.path_int64 then
        block_shape [Obj.custom_tag]
      else begin
        match Env.find_type_descrs p env, Env.find_type p env with
        | exception Not_found -> any
        | descr, decl ->
            let params = decl.type_params in
            of_typedescr env descr ~params ~args
      end
  | Ttuple _ -> block_shape [0]
  | Tarrow _ | Tpackage _ | Tobject _ | Tnil | Tvariant _ ->
      failwith "TODO"
  | Tlink _ | Tsubst _ | Tpoly _ | Tfield _ ->
      assert false


and of_typedescr env ty_descr ~params ~args =
  (* we called scrape_ty on the type expression in the function above, thus
     it isnt a single constructor unboxed type *)
  match ty_descr with
  | Type_abstract -> any
  | Type_record (_, Record_regular) -> block_shape [0]
  | Type_record (_, Record_float) -> block_shape [Obj.double_array_tag]
  | Type_record (_, Record_unboxed _) -> failwith "TODO"
  | Type_record (_, Record_inlined _)
  | Type_record (_, Record_extension _) -> assert false
  | Type_open -> block_shape [0]
  | Type_variant ([],_) -> none
  | Type_variant ((fst_descr :: _) as cstr_descrs,_) ->
      (* the head shape of boxed constructors is equivalent to the nb of
         constant constructors and the nb of non constant constructors *)
      let num_consts = fst_descr.cstr_consts in
      let num_nonconsts = fst_descr.cstr_nonconsts in
      let boxed_shape = cstrs_shape ~num_consts ~num_nonconsts in
      let unboxed_shapes = List.filter_map
        (fun descr ->
          match descr.cstr_tag with
          | Cstr_constant _ | Cstr_block _ | Cstr_extension _ -> None
          | Cstr_unboxed (ty, thunk) -> begin
              let compute_head_shape () =
                (* we instantiate the formal type variables with the
                   type expression parameters at use site *)
                let ty = Ctype.apply env params ty args in
                of_type env ty
              in
              match Delayed.force compute_head_shape thunk with
              | Ok shape -> Some shape
              | Error Delayed.Cycle -> raise Conflict
            end
        ) cstr_descrs
      in
      (* now checking that the unboxed constructors are compatible with the
         base head shape of boxed constructors *)
      List.fold_left disjoint_union boxed_shape unboxed_shapes

let pp_shape ppf = function
  | Shape_any -> Format.fprintf ppf "Shape_any"
  | Shape_set l ->
      Format.fprintf ppf "Shape_set [%a]"
        (Format.pp_print_list
          ~pp_sep:(fun ppf () -> Format.fprintf ppf "; ")
          Format.pp_print_int) l

let pp ppf {head_imm; head_blocks} =
  Format.fprintf ppf "{head_imm = %a; head_blocks = %a}"
    pp_shape head_imm
    pp_shape head_blocks
