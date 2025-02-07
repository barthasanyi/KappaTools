(******************************************************************************)
(*  _  __ * The Kappa Language                                                *)
(* | |/ / * Copyright 2010-2020 CNRS - Harvard Medical School - INRIA - IRIF  *)
(* | ' /  *********************************************************************)
(* | . \  * This file is distributed under the terms of the                   *)
(* |_|\_\ * GNU Lesser General Public License Version 3                       *)
(******************************************************************************)

val updateFontSize : delta:float -> unit
val set_parameters_as_default : unit -> unit

val init : unit -> unit Lwt.t
(** run on application init *)

val sync : unit -> unit Lwt.t
(** to synch state of application with runtime *)

(* TODO: move to state_project? *)
val agent_coloring : unit Js.t
(** In reality d3color Js.js_array Js.t.

    It is visualizer responsability to fill/use it, we have it here
   only to ensure consistency/sharing in between tabs *)
