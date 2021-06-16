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

type 'a state =
  | Todo
  | In_progress
  | Done of 'a

type 'a t = 'a state ref

let make () = ref Todo

type cycle = Cycle

let force f st = match !st with
 | In_progress -> Error Cycle
 | Done v -> Ok v
 | Todo ->
     begin
       st := In_progress;
       let v = f () in
       st := Done v;
       Ok v
     end

let get st = match !st with
  | Todo | In_progress -> invalid_arg "Delayed.get"
  | Done v -> v
