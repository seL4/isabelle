(*  Title:      VampireCommunication.ML
    ID:         $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

structure VampireCommunication =
struct

(***************************************************************************)
(*  Code to deal with the transfer of proofs from a Vampire process        *)
(***************************************************************************)

(***********************************)
(*  Write vampire output to a file *)
(***********************************)

fun logVampInput (instr, fd) =
    let val thisLine = TextIO.inputLine instr
    in if thisLine = "%==============  End of proof. ==================\n"
       then TextIO.output (fd, thisLine)
       else (
             TextIO.output (fd, thisLine); logVampInput (instr,fd))
    end;

(**********************************************************************)
(*  Transfer the vampire output from the watcher to the input pipe of *)
(*  the main Isabelle process                                         *)
(**********************************************************************)

fun transferVampInput (fromChild, toParent, ppid) =
    let
      val thisLine = TextIO.inputLine fromChild
    in
      if (thisLine = "%==============  End of proof. ==================\n" )
      then (
            TextIO.output (toParent, thisLine);
            TextIO.flushOut toParent
            )
      else (
            TextIO.output (toParent, thisLine);
            TextIO.flushOut toParent;
            transferVampInput (fromChild, toParent, ppid)
            )
    end;


(*********************************************************************************)
(*  Inspect the output of a vampire process to see if it has found a proof,      *)
(*  and if so, transfer output to the input pipe of the main Isabelle process    *)
(*********************************************************************************)

fun startVampireTransfer (fromChild, toParent, ppid, childCmd) =
    if (isSome (TextIO.canInput(fromChild, 5)))
    then
      (
       let val thisLine = TextIO.inputLine fromChild
       in
         if (thisLine = "% Proof found. Thanks to Tanya!\n" )
         then
           (
            Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr1);
            TextIO.output (toParent,childCmd^"\n" );
            TextIO.flushOut toParent;
            TextIO.output (toParent, thisLine);
            TextIO.flushOut toParent;

            transferVampInput (fromChild, toParent, ppid);
            true)
         else if (thisLine = "% Unprovable.\n" )
         then
           (
            Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr1);
            TextIO.output (toParent,childCmd^"\n" );
            TextIO.flushOut toParent;
            TextIO.output (toParent, thisLine);
            TextIO.flushOut toParent;

            true)
         else if (thisLine = "% Proof not found.\n")
         then
           (Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr1);
            TextIO.output (toParent,childCmd^"\n" );
            TextIO.flushOut toParent;
            TextIO.output (toParent, thisLine);
            TextIO.flushOut toParent;
            true)
         else
           (
            startVampireTransfer (fromChild, toParent, ppid, childCmd)
            )
       end
         )
    else (false)


(***********************************************************************)
(*  Function used by the Isabelle process to read in a vampire proof   *)
(***********************************************************************)

fun getVampInput instr =
  let val thisLine = TextIO.inputLine instr
  in
    if thisLine = "%==============  End of proof. ==================\n" then
      Pretty.writeln (Pretty.str (concat ["vampire", thisLine]))
    else if thisLine = "% Unprovable.\n" then
      Pretty.writeln (Pretty.str (concat ["vampire", thisLine]))
    else if thisLine = "% Proof not found.\n" then
      Pretty.writeln (Pretty.str (concat ["vampire", thisLine]))
    else
      (Pretty.writeln (Pretty.str (concat ["vampire", thisLine])); getVampInput instr)
  end;

end;
