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

exception EOF;

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
		       goalstring toParent ppid negs clause_arr num_of_clauses))]) sg_num


fun transferVampInput (fromChild, toParent, ppid,thmstring,goalstring, 
                       currentString, thm, sg_num,clause_arr, num_of_clauses) =
  let val thisLine = TextIO.inputLine fromChild
  in
    if thisLine = "" (*end of file?*)
    then (File.write (File.tmp_path (Path.basic"vampire_extraction_failed")) currentString;
	  raise EOF)                    
    else if (thisLine = "%==============  End of proof. ==================\n" )
    then let val proofextract = Recon_Parse.extract_proof (currentString^thisLine)
	 in
	   File.write (File.tmp_path (Path.basic"vampire_extracted_prf")) proofextract; 
	   reconstruct_tac proofextract thmstring goalstring toParent ppid sg_num  
	                   clause_arr num_of_clauses thm
	 end
    else transferVampInput (fromChild, toParent, ppid,thmstring, goalstring, 
             currentString^thisLine, thm, sg_num, clause_arr, num_of_clauses)
  end;


(*********************************************************************************)
(*  Inspect the output of a Vampire process to see if it has found a proof,     *)
(*  and if so, transfer output to the input pipe of the main Isabelle process    *)
(*********************************************************************************)


fun startVampTransfer (fromChild, toParent, ppid, thmstring,goalstring,childCmd,
                       thm, sg_num,clause_arr, num_of_clauses) =
    let val thisLine = TextIO.inputLine fromChild
    in
      if thisLine = "" then false
      else if (thisLine = "%================== Proof: ======================\n")
      then
       (File.append (File.tmp_path (Path.basic "vampire_transfer"))
		    ("about to transfer proof, thm is: " ^ string_of_thm thm);
	transferVampInput (fromChild, toParent, ppid,thmstring, goalstring,
			   thisLine, thm, sg_num,clause_arr, num_of_clauses);
	true) handle EOF => false
      else
	 startVampTransfer (fromChild, toParent, ppid, thmstring, goalstring,
			    childCmd, thm, sg_num,clause_arr, num_of_clauses)
    end


fun checkVampProofFound (fromChild, toParent, ppid,thmstring,goalstring, childCmd, 
                         thm, sg_num, clause_arr, num_of_clauses) =
 let val vamp_proof_file = TextIO.openAppend
	   (File.platform_path(File.tmp_path (Path.basic "vampire_proof")))
     val _ = File.write (File.tmp_path (Path.basic "vampire_checking_prf"))
			("checking if proof found, thm is: " ^ string_of_thm thm)
     val thisLine = TextIO.inputLine fromChild
 in   
     if thisLine = "" 
     then (TextIO.output (vamp_proof_file, ("No proof output seen \n"));
	   TextIO.closeOut vamp_proof_file;
	   false)
     else if thisLine = "% Proof found. Thanks to Tanya!\n"
     then
      (File.write (File.tmp_path (Path.basic "vampire_response")) thisLine;
       startVampTransfer (fromChild, toParent, ppid, thmstring, goalstring,
			  childCmd, thm, sg_num, clause_arr, num_of_clauses))
     else if (thisLine = "% Unprovable.\n" )
     then
      (File.write (File.tmp_path (Path.basic "vampire_response")) thisLine;
       TextIO.output (toParent,childCmd^"\n" );
       TextIO.flushOut toParent;
       TextIO.output (vamp_proof_file, thisLine);
       TextIO.closeOut vamp_proof_file;
       (*TextIO.output (toParent, thisLine);
	TextIO.flushOut toParent;
	TextIO.output (toParent, "bar\n");
	TextIO.flushOut toParent;*)

       TextIO.output (toParent, thisLine^"\n");
       TextIO.output (toParent, thmstring^"\n");
       TextIO.output (toParent, goalstring^"\n");
       TextIO.flushOut toParent;
       Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
       (* Attempt to prevent several signals from turning up simultaneously *)
       Posix.Process.sleep(Time.fromSeconds 1);
       true)
     else if (thisLine = "% Proof not found. Time limit expired.\n")
     then
      (File.write (File.tmp_path (Path.basic "vampire_response")) thisLine;
       TextIO.output (toParent,childCmd^"\n" );
       TextIO.flushOut toParent;
       TextIO.output (vamp_proof_file, thisLine);
       TextIO.closeOut vamp_proof_file;

       TextIO.output (toParent, thisLine^"\n");
       TextIO.output (toParent, thmstring^"\n");
       TextIO.output (toParent, goalstring^"\n");
       TextIO.flushOut toParent;
       Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
       (* Attempt to prevent several signals from turning up simultaneously *)
       Posix.Process.sleep(Time.fromSeconds 1);
       true)
     else
       (TextIO.output (vamp_proof_file, thisLine);
	TextIO.flushOut vamp_proof_file;
	checkVampProofFound  (fromChild, toParent, ppid, thmstring,
	   goalstring,childCmd, thm, sg_num, clause_arr, num_of_clauses))
  end


(***********************************************************************)
(*  Function used by the Isabelle process to read in a Vampire proof   *)
(***********************************************************************)

fun getVampInput instr =
    let val thisLine = TextIO.inputLine instr
	val _ = File.write (File.tmp_path (Path.basic "vampire_line")) thisLine
    in    (* reconstructed proof string *)
      if thisLine = "" then ("No output from reconstruction process.\n","","")
      else if String.sub (thisLine, 0) = #"[" orelse
              thisLine = "% Unprovable.\n" orelse
              thisLine ="% Proof not found. Time limit expired.\n" orelse
              String.isPrefix "Rules from" thisLine
      then
	let val thmstring = TextIO.inputLine instr
	    val goalstring = TextIO.inputLine instr
	in (thisLine, thmstring, goalstring) end
      else if thisLine = "Proof found but translation failed!"
      then
	 let val thmstring = TextIO.inputLine instr
	     val goalstring = TextIO.inputLine instr
	     val _ = debug "getVampInput: translation of proof failed"
	 in (thisLine, thmstring, goalstring) end
      else getVampInput instr
    end

end;
