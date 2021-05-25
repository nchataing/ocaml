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

type 'b state =
  | Todo
  | In_progress
  | Done of 'b

type ('a, 'b) t = 'b state ref * 'a

let make x = ref Todo, x

let get_first_arg (_,x) = x

type cycle = Cycle

let force f (st,x) = match !st with
 | In_progress -> Error Cycle
 | Done v -> Ok v
 | Todo ->
     begin
       st := In_progress;
       let v = f x in
       st := Done v;
       Ok v
     end

let get (st,_) = match !st with
  | Todo | In_progress -> invalid_arg "Semi_thunk.get"
  | Done v -> v
