(*  Title:      VampCommunication.ml
    ID:         $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

(***************************************************************************)
(*  Code to deal with the transfer of proofs from a Vampire process          *)
(***************************************************************************)
signature VAMP_COMM =
  sig
    val getVampInput : TextIO.instream -> string * string * string
    val checkVampProofFound: 
          TextIO.instream * TextIO.outstream * Posix.Process.pid * string *
          string * string * thm * int * (ResClause.clause * thm) Array.array * int -> bool
  end;

structure VampComm : VAMP_COMM =
struct

(***********************************)
(*  Write Vampire output to a file *)
(***********************************)

fun logVampInput (instr, fd) =
    let val thisLine = TextIO.inputLine instr
    in if (thisLine = "%==============  End of proof. ==================\n" )
       then TextIO.output (fd, thisLine)
       else (TextIO.output (fd, thisLine); logVampInput (instr,fd))
    end;

(**********************************************************************)
(*  Reconstruct the Vampire proof w.r.t. thmstring (string version of   *)
(*  Isabelle goal to be proved), then transfer the reconstruction     *)
(*  steps as a string to the input pipe of the main Isabelle process  *)
(**********************************************************************)

fun reconstruct_tac proofextract thmstring goalstring toParent ppid sg_num 
                    clause_arr num_of_clauses =
    SELECT_GOAL
      (EVERY1
        [rtac ccontr, ResLib.atomize_tac, skolemize_tac,
	 METAHYPS(fn negs =>
		     (Recon_Transfer.vampString_to_lemmaString proofextract thmstring 
		       goalstring toParent ppid negs clause_arr  num_of_clauses ))]) sg_num


fun transferVampInput (fromChild, toParent, ppid,thmstring,goalstring, currentString, thm, sg_num,clause_arr,  num_of_clauses) =
  let val thisLine = TextIO.inputLine fromChild
  in
    if (thisLine = "%==============  End of proof. ==================\n" )
    then let val proofextract = Recon_Parse.extract_proof (currentString^thisLine)
	 in
	   File.write (File.tmp_path (Path.basic"extracted-prf-vamp")) proofextract; 
	   reconstruct_tac proofextract thmstring goalstring toParent ppid sg_num  
	                   clause_arr num_of_clauses thm
	 end
    else transferVampInput (fromChild, toParent, ppid,thmstring, goalstring, 
             currentString^thisLine, thm, sg_num, clause_arr, num_of_clauses)
  end;


(*********************************************************************************)
(*  Inspect the output of a Vampire process to see if it has found a proof,      *)
(*  and if so, transfer output to the input pipe of the main Isabelle process    *)
(*********************************************************************************)


fun startVampTransfer (fromChild, toParent, ppid, thmstring,goalstring,childCmd,
                       thm, sg_num,clause_arr, num_of_clauses) =
    if isSome (TextIO.canInput(fromChild, 5))
    then
       let val thisLine = TextIO.inputLine fromChild
       in
         if (thisLine = "%================== Proof: ======================\n")
         then
          (File.append (File.tmp_path (Path.basic "transfer-vamp"))
                       ("about to transfer proof, thm is: " ^ string_of_thm thm);
           transferVampInput (fromChild, toParent, ppid,thmstring, goalstring,
                              thisLine, thm, sg_num,clause_arr,  num_of_clauses);
           true)
         else
            startVampTransfer (fromChild, toParent, ppid, thmstring, goalstring,
                               childCmd, thm, sg_num,clause_arr, num_of_clauses)
       end
    else false


fun checkVampProofFound (fromChild, toParent, ppid,thmstring,goalstring, childCmd, thm, sg_num, clause_arr,  num_of_clauses) =
    let val vamp_proof_file = TextIO.openAppend(File.platform_path(File.tmp_path (Path.basic "vamp_proof")))
        val _ = File.write (File.tmp_path (Path.basic "checking-prf-vamp"))
                           ("checking if proof found, thm is: " ^ string_of_thm thm)
    in
      if (isSome (TextIO.canInput(fromChild, 5)))
      then
        (
         let val thisLine = TextIO.inputLine fromChild
         in if (thisLine = "% Proof found. Thanks to Tanya!\n" )
            then
               let val  outfile = TextIO.openOut(File.platform_path(File.tmp_path (Path.basic "foo_proof")));   
                        val _ = TextIO.output (outfile, (thisLine))

                        val _ =  TextIO.closeOut outfile
               in
                 startVampTransfer (fromChild, toParent, ppid, thmstring,goalstring,childCmd, thm, sg_num, clause_arr,  num_of_clauses)
               end
            else if (thisLine = "% Unprovable.\n" )
            then
               let    val  outfile = TextIO.openOut(File.platform_path(File.tmp_path (Path.basic "foo_proof")));                                                                               (* val _ =  Posix.Process.sleep(Time.fromSeconds 3 );*)
                           val _ = TextIO.output (outfile, (thisLine))

                           val _ =  TextIO.closeOut outfile
               in

                 TextIO.output (toParent,childCmd^"\n" );
                 TextIO.flushOut toParent;
                 TextIO.output (vamp_proof_file, (thisLine));
                 TextIO.flushOut vamp_proof_file;
                 TextIO.closeOut vamp_proof_file;
                 (*TextIO.output (toParent, thisLine);
                  TextIO.flushOut toParent;
                  TextIO.output (toParent, "bar\n");
                  TextIO.flushOut toParent;*)

                 TextIO.output (toParent, thisLine^"\n");
                 TextIO.flushOut toParent;
                 TextIO.output (toParent, thmstring^"\n");
                 TextIO.flushOut toParent;
                 TextIO.output (toParent, goalstring^"\n");
                 TextIO.flushOut toParent;
                 Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
                 (* Attempt to prevent several signals from turning up simultaneously *)
                 Posix.Process.sleep(Time.fromSeconds 1);
                 true
               end
            else if (thisLine = "% Proof not found. Time limit expired.\n")
            then
              (let    val  outfile = TextIO.openOut(File.platform_path(File.tmp_path (Path.basic "foo_proof")));                                                                               (* val _ =  Posix.Process.sleep(Time.fromSeconds 3 );*)
                           val _ = TextIO.output (outfile, (thisLine))

                           val _ =  TextIO.closeOut outfile
               in

                 TextIO.output (toParent,childCmd^"\n" );
                 TextIO.flushOut toParent;
                 TextIO.output (vamp_proof_file, (thisLine));
                 TextIO.flushOut vamp_proof_file;
                 TextIO.closeOut vamp_proof_file;
                 (*TextIO.output (toParent, thisLine);
                  TextIO.flushOut toParent;
                  TextIO.output (toParent, "bar\n");
                  TextIO.flushOut toParent;*)

                 TextIO.output (toParent, thisLine^"\n");
                 TextIO.flushOut toParent;
                 TextIO.output (toParent, thmstring^"\n");
                 TextIO.flushOut toParent;
                 TextIO.output (toParent, goalstring^"\n");
                 TextIO.flushOut toParent;
                 Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
                 (* Attempt to prevent several signals from turning up simultaneously *)
                 Posix.Process.sleep(Time.fromSeconds 1);
                 true
               end
              )

            else
              (TextIO.output (vamp_proof_file, (thisLine));
               TextIO.flushOut vamp_proof_file;
               checkVampProofFound  (fromChild, toParent, ppid, thmstring,goalstring,childCmd, thm, sg_num, clause_arr,  num_of_clauses))

         end
           )
      else
        (TextIO.output (vamp_proof_file, ("No proof output seen \n"));TextIO.closeOut vamp_proof_file;false)
    end


(***********************************************************************)
(*  Function used by the Isabelle process to read in a vamp proof   *)
(***********************************************************************)

fun getVampInput instr =
    if (isSome (TextIO.canInput(instr, 2)))
    then
      let val thisLine = TextIO.inputLine instr
          val  outfile = TextIO.openOut(File.platform_path(File.tmp_path (Path.basic "foo_thisLine")));                                                                     val _ = TextIO.output (outfile, (thisLine))

                                                                                                                                                                            val _ =  TextIO.closeOut outfile
      in    (* reconstructed proof string *)
        if ( (substring (thisLine, 0,1))= "[")
        then
          (*Pretty.writeln(Pretty.str (thisLine))*)
          let val reconstr = thisLine
              val thmstring = TextIO.inputLine instr
              val goalstring = TextIO.inputLine instr
          in
            (reconstr, thmstring, goalstring)
          end
        else if (thisLine = "% Unprovable.\n" )
        then
          (
           let val reconstr = thisLine
               val thmstring = TextIO.inputLine instr
               val goalstring = TextIO.inputLine instr
           in
             (reconstr, thmstring, goalstring)
           end
             )
        else  if (thisLine = "% Proof not found. Time limit expired.\n")
        then
          (
           let val reconstr = thisLine
               val thmstring = TextIO.inputLine instr
               val goalstring = TextIO.inputLine instr
           in
             (reconstr, thmstring, goalstring)
           end
             )
        else if (String.isPrefix   "Rules from"  thisLine)
        then
          (
           let val reconstr = thisLine
               val thmstring = TextIO.inputLine instr
               val goalstring = TextIO.inputLine instr
           in
             (reconstr, thmstring, goalstring)
           end
             )

        else if (thisLine = "Proof found but translation failed!")
        then
          (
           let val reconstr = thisLine
               val thmstring = TextIO.inputLine instr
               val goalstring = TextIO.inputLine instr
               val  outfile = TextIO.openOut(File.platform_path(File.tmp_path (Path.basic "foo_getVamp")));
                    val _ = TextIO.output (outfile, (thisLine))
                    val _ =  TextIO.closeOut outfile
           in
             (reconstr, thmstring, goalstring)
           end
             )
        else
          getVampInput instr

      end
    else
      ("No output from reconstruction process.\n","","")
end;
