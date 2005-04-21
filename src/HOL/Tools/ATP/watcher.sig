(*  ID:         $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

(***************************************************************************)
(*  The watcher process starts a Spass process when it receives a        *)
(*  message from Isabelle                                                  *)
(*  Signals Isabelle, puts output of child into pipe to Isabelle,          *)
(*  and removes dead processes.  Also possible to kill all the vampire     *)
(*  processes currently running.                                           *)
(***************************************************************************)


signature WATCHER =
sig

(*****************************************************************************************)
(*  Send request to Watcher for multiple spasses to be called for filenames in arg       *)
(*  callResProvers (outstreamtoWatcher, prover name,prover-command, (settings,file) list             *)
(*****************************************************************************************)

val callResProvers : TextIO.outstream *(string* string*string *string*string*string*string*string*string) list -> unit



(************************************************************************)
(* Send message to watcher to kill currently running resolution provers *)
(************************************************************************)

val callSlayer : TextIO.outstream -> unit



(**********************************************************)
(* Start a watcher and set up signal handlers             *)
(**********************************************************)

val createWatcher : Thm.thm -> TextIO.instream * TextIO.outstream * Posix.Process.pid



(**********************************************************)
(* Kill watcher process                                   *)
(**********************************************************)

val killWatcher : (Posix.Process.pid) -> unit


end
