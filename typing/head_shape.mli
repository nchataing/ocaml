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

exception Conflict

type t = Types.head_shape

val of_type : Env.t -> Types.type_expr -> t

val of_typedescr :
  Env.t -> Env.type_descriptions ->
  params:(Types.type_expr list) -> args:(Types.type_expr list) -> t

val pp : Format.formatter -> t -> unit
