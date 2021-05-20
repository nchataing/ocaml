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

type ('a, 'b) state =
  | Todo of 'a
  | In_progress
  | Done of 'b

type ('a, 'b) t = ('a, 'b) state ref

let make x = ref (Todo x)

type cycle = Cycle

let force f st = match !st with
 | In_progress -> Error Cycle
 | Done v -> Ok v
 | Todo x ->
     begin
       st := In_progress;
       let v = f x in
       st := Done v;
       Ok v
     end

let get st = match !st with
  | Todo _ | In_progress -> invalid_arg "Semi_thunk.get"
  | Done v -> v
