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

(* Auxiliaries for type-based optimizations, e.g. array kinds *)

open Path
open Types
open Asttypes
open Typedtree
open Lambda

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

let scrape env ty =
  (scrape_ty env ty).desc

let is_function_type env ty =
  match scrape env ty with
  | Tarrow (_, lhs, rhs, _) -> Some (lhs, rhs)
  | _ -> None

let is_base_type env ty base_ty_path =
  match scrape env ty with
  | Tconstr(p, _, _) -> Path.same p base_ty_path
  | _ -> false

let maybe_pointer_type env ty =
  let ty = scrape_ty env ty in
  if Ctype.maybe_pointer_type env ty then
    Pointer
  else
    Immediate

let maybe_pointer exp = maybe_pointer_type exp.exp_env exp.exp_type

type classification =
  | Int
  | Float
  | Lazy
  | Addr  (* anything except a float or a lazy *)
  | Any

module Head_shape = struct
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

  let rec of_type ?(detect_cycle=true) env ty =
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
              of_typedescr ~detect_cycle env descr ~params ~args
        end
    | Ttuple _ -> block_shape [0]
    | Tarrow _ | Tpackage _ | Tobject _ | Tnil | Tvariant _ ->
        failwith "TODO"
    | Tlink _ | Tsubst _ | Tpoly _ | Tfield _ ->
        assert false

  and of_typedescr ?(detect_cycle=true) env ty_descr ~params ~args =
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
            | Cstr_unboxed thunk -> begin
                if detect_cycle then
                  let compute_head_shape ty =
                    (* we instantiate the formal type variables with the
                       type expression parameters at use site *)
                    let ty = Ctype.apply env params ty args in
                    of_type ~detect_cycle env ty
                  in
                  match Semi_thunk.force compute_head_shape thunk with
                  | Ok shape -> Some shape
                  | Error Semi_thunk.Cycle -> raise Conflict
              else
                let ty = Semi_thunk.get_first_arg thunk in
                let ty = Ctype.apply env params ty args in
                Some (of_type ~detect_cycle env ty)
            end
          ) cstr_descrs
        in
        (* now checking that the unboxed constructors are compatible with the
           base head shape of boxed constructors *)
        try
          List.fold_left disjoint_union boxed_shape unboxed_shapes
        with Conflict -> begin
          (* Cycles error have already been raised at this point. We can
             safely recompute the head shape without cycle detection.
             It enables to expand more at the call site.
             TODO : put an example there *)
          if detect_cycle then
            of_typedescr ~detect_cycle:false env ty_descr ~params ~args
          else
            (* if we are already in the no cycle detection mode, reraise *)
            raise Conflict
        end

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
end

let classify env ty =
  let ty = scrape_ty env ty in
  if maybe_pointer_type env ty = Immediate then Int
  else match ty.desc with
  | Tvar _ | Tunivar _ ->
      Any
  | Tconstr (p, _args, _abbrev) ->
      if Path.same p Predef.path_float then Float
      else if Path.same p Predef.path_lazy_t then Lazy
      else if Path.same p Predef.path_string
           || Path.same p Predef.path_bytes
           || Path.same p Predef.path_array
           || Path.same p Predef.path_nativeint
           || Path.same p Predef.path_int32
           || Path.same p Predef.path_int64 then Addr
      else begin
        try
          match (Env.find_type p env).type_kind with
          | Type_abstract ->
              Any
          | Type_record _ | Type_variant _ | Type_open ->
              Addr
        with Not_found ->
          (* This can happen due to e.g. missing -I options,
             causing some .cmi files to be unavailable.
             Maybe we should emit a warning. *)
          Any
      end
  | Tarrow _ | Ttuple _ | Tpackage _ | Tobject _ | Tnil | Tvariant _ ->
      Addr
  | Tlink _ | Tsubst _ | Tpoly _ | Tfield _ ->
      assert false

let array_type_kind env ty =
  match scrape env ty with
  | Tconstr(p, [elt_ty], _) | Tpoly({desc = Tconstr(p, [elt_ty], _)}, _)
    when Path.same p Predef.path_array ->
      begin match classify env elt_ty with
      | Any -> if Config.flat_float_array then Pgenarray else Paddrarray
      | Float -> if Config.flat_float_array then Pfloatarray else Paddrarray
      | Addr | Lazy -> Paddrarray
      | Int -> Pintarray
      end
  | Tconstr(p, [], _) | Tpoly({desc = Tconstr(p, [], _)}, _)
    when Path.same p Predef.path_floatarray ->
      Pfloatarray
  | _ ->
      (* This can happen with e.g. Obj.field *)
      Pgenarray

let array_kind exp = array_type_kind exp.exp_env exp.exp_type

let array_pattern_kind pat = array_type_kind pat.pat_env pat.pat_type

let bigarray_decode_type env ty tbl dfl =
  match scrape env ty with
  | Tconstr(Pdot(Pident mod_id, type_name), [], _)
    when Ident.name mod_id = "Stdlib__Bigarray" ->
      begin try List.assoc type_name tbl with Not_found -> dfl end
  | _ ->
      dfl

let kind_table =
  ["float32_elt", Pbigarray_float32;
   "float64_elt", Pbigarray_float64;
   "int8_signed_elt", Pbigarray_sint8;
   "int8_unsigned_elt", Pbigarray_uint8;
   "int16_signed_elt", Pbigarray_sint16;
   "int16_unsigned_elt", Pbigarray_uint16;
   "int32_elt", Pbigarray_int32;
   "int64_elt", Pbigarray_int64;
   "int_elt", Pbigarray_caml_int;
   "nativeint_elt", Pbigarray_native_int;
   "complex32_elt", Pbigarray_complex32;
   "complex64_elt", Pbigarray_complex64]

let layout_table =
  ["c_layout", Pbigarray_c_layout;
   "fortran_layout", Pbigarray_fortran_layout]

let bigarray_type_kind_and_layout env typ =
  match scrape env typ with
  | Tconstr(_p, [_caml_type; elt_type; layout_type], _abbrev) ->
      (bigarray_decode_type env elt_type kind_table Pbigarray_unknown,
       bigarray_decode_type env layout_type layout_table
                            Pbigarray_unknown_layout)
  | _ ->
      (Pbigarray_unknown, Pbigarray_unknown_layout)

let value_kind env ty =
  match scrape env ty with
  | Tconstr(p, _, _) when Path.same p Predef.path_int ->
      Pintval
  | Tconstr(p, _, _) when Path.same p Predef.path_char ->
      Pintval
  | Tconstr(p, _, _) when Path.same p Predef.path_float ->
      Pfloatval
  | Tconstr(p, _, _) when Path.same p Predef.path_int32 ->
      Pboxedintval Pint32
  | Tconstr(p, _, _) when Path.same p Predef.path_int64 ->
      Pboxedintval Pint64
  | Tconstr(p, _, _) when Path.same p Predef.path_nativeint ->
      Pboxedintval Pnativeint
  | _ ->
      Pgenval

let function_return_value_kind env ty =
  match is_function_type env ty with
  | Some (_lhs, rhs) -> value_kind env rhs
  | None -> Pgenval

(** Whether a forward block is needed for a lazy thunk on a value, i.e.
    if the value can be represented as a float/forward/lazy *)
let lazy_val_requires_forward env ty =
  match classify env ty with
  | Any | Lazy -> true
  | Float -> Config.flat_float_array
  | Addr | Int -> false

(** The compilation of the expression [lazy e] depends on the form of e:
    constants, floats and identifiers are optimized.  The optimization must be
    taken into account when determining whether a recursive binding is safe. *)
let classify_lazy_argument : Typedtree.expression ->
                             [`Constant_or_function
                             |`Float_that_cannot_be_shortcut
                             |`Identifier of [`Forward_value|`Other]
                             |`Other] =
  fun e -> match e.exp_desc with
    | Texp_constant
        ( Const_int _ | Const_char _ | Const_string _
        | Const_int32 _ | Const_int64 _ | Const_nativeint _ )
    | Texp_function _
    | Texp_construct (_, {cstr_arity = 0}, _) ->
       `Constant_or_function
    | Texp_constant(Const_float _) ->
       if Config.flat_float_array
       then `Float_that_cannot_be_shortcut
       else `Constant_or_function
    | Texp_ident _ when lazy_val_requires_forward e.exp_env e.exp_type ->
       `Identifier `Forward_value
    | Texp_ident _ ->
       `Identifier `Other
    | _ ->
       `Other

let value_kind_union k1 k2 =
  if k1 = k2 then k1
  else Pgenval
