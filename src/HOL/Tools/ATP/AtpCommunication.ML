(*  Title:      VampCommunication.ml
    ID:         $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

(***************************************************************************)
(*  Code to deal with the transfer of proofs from a Vampire process          *)
(***************************************************************************)
signature ATP_COMMUNICATION =
  sig
    val reconstruct : bool ref
    val checkEProofFound: 
          TextIO.instream * TextIO.outstream * Posix.Process.pid * 
          string * string * (ResClause.clause * thm) Array.array -> bool
    val checkVampProofFound: 
          TextIO.instream * TextIO.outstream * Posix.Process.pid * 
          string * string * (ResClause.clause * thm) Array.array -> bool
    val checkSpassProofFound:  
          TextIO.instream * TextIO.outstream * Posix.Process.pid * 
          string * string * thm * int * (ResClause.clause * thm) Array.array -> bool
  end;

structure AtpCommunication : ATP_COMMUNICATION =
struct

(* switch for whether to reconstruct a proof found, or just list the lemmas used *)
val reconstruct = ref false;

exception EOF;

val start_E = "# Proof object starts here."
val end_E   = "# Proof object ends here."
val start_V6 = "%================== Proof: ======================"
val end_V6   = "%==============  End of proof. =================="
val start_V8 = "=========== Refutation =========="
val end_V8 = "======= End of refutation ======="

(*Identifies the start/end lines of an ATP's output*)
local open Recon_Parse in
fun extract_proof s =
  if cut_exists "Here is a proof with" s then
    (kill_lines 0
     o snd o cut_after ":"
     o snd o cut_after "Here is a proof with"
     o fst o cut_after " ||  -> .") s
  else if cut_exists start_V8 s then
    (kill_lines 0    (*Vampire 8.0*)
     o snd o cut_after start_V8
     o fst o cut_before end_V8) s
  else if cut_exists end_E s then
    (kill_lines 0    (*eproof*)
     o snd o cut_after start_E
     o fst o cut_before end_E) s
  else "??extract_proof failed" (*Couldn't find a proof*)
end;


(*********************************************************************************)
(*  Inspect the output of an ATP process to see if it has found a proof,     *)
(*  and if so, transfer output to the input pipe of the main Isabelle process    *)
(*********************************************************************************)

fun startTransfer (startS,endS)
      (fromChild, toParent, ppid, goalstring, childCmd, clause_arr) =
 let val thisLine = TextIO.inputLine fromChild
     fun transferInput currentString =
      let val thisLine = TextIO.inputLine fromChild
      in
	if thisLine = "" (*end of file?*)
	then (File.write (File.tmp_path (Path.basic"extraction_failed")) 
	                 ("start bracket: " ^ startS ^
	                  "\nend bracket: " ^ endS ^
	                  "\naccumulated text: " ^ currentString);
	      raise EOF)                    
	else if String.isPrefix endS thisLine
	then let val proofextract = extract_proof (currentString^thisLine)
	     in
	       File.write (File.tmp_path (Path.basic"extracted_prf")) proofextract; 
	       Recon_Transfer.prover_lemma_list proofextract goalstring toParent ppid clause_arr
	     end
	else transferInput (currentString^thisLine)
      end
 in
   if thisLine = "" then false
   else if String.isPrefix startS thisLine
   then
    (File.append (File.tmp_path (Path.basic "transfer_start"))
		 ("about to transfer proof, first line is: " ^ thisLine);
     transferInput thisLine;
     true) handle EOF => false
   else
      startTransfer (startS,endS)
                    (fromChild, toParent, ppid, goalstring,
		     childCmd, clause_arr)
 end

(*Called from watcher. Returns true if the Vampire process has returned a verdict.*)
fun checkVampProofFound (fromChild, toParent, ppid, goalstring, childCmd, clause_arr) =
 let val proof_file = TextIO.openAppend
	   (File.platform_path(File.tmp_path (Path.basic "vampire_proof")))
     val _ = File.write (File.tmp_path (Path.basic "vampire_checking_prf"))
			("checking if proof found. childCmd is " ^ childCmd ^
			 "\ngoalstring is: " ^ goalstring)
     val thisLine = TextIO.inputLine fromChild
 in   
     File.write (File.tmp_path (Path.basic "vampire_response")) thisLine;
     if thisLine = "" 
     then (TextIO.output (proof_file, "No proof output seen \n");
	   TextIO.closeOut proof_file;
	   false)
     else if String.isPrefix "Refutation found. Thanks to Tanya" thisLine
     then
       startTransfer (start_V8, end_V8)
	      (fromChild, toParent, ppid, goalstring,
	       childCmd, clause_arr)
     else if (String.isPrefix "Satisfiability detected" thisLine) orelse
             (String.isPrefix "Refutation not found" thisLine)
     then
       (TextIO.output (toParent, "Failure\n");
	TextIO.output (toParent, goalstring^"\n");
	TextIO.flushOut toParent;
	TextIO.output (proof_file, thisLine);
	TextIO.closeOut proof_file;
	Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
	(* Attempt to prevent several signals from turning up simultaneously *)
	Posix.Process.sleep(Time.fromSeconds 1);
	true)
     else
       (TextIO.output (proof_file, thisLine);
	TextIO.flushOut proof_file;
	checkVampProofFound  (fromChild, toParent, ppid, 
	   goalstring,childCmd, clause_arr))
  end


(*Called from watcher. Returns true if the E process has returned a verdict.*)
fun checkEProofFound (fromChild, toParent, ppid,goalstring, childCmd, clause_arr) = 
 let val E_proof_file = TextIO.openAppend
	   (File.platform_path(File.tmp_path (Path.basic "e_proof")))
     val _ = File.write (File.tmp_path (Path.basic "e_checking_prf"))
			("checking if proof found. childCmd is " ^ childCmd ^
			 "\ngoalstring is: " ^ goalstring)
     val thisLine = TextIO.inputLine fromChild  
 in   
     File.write (File.tmp_path (Path.basic "e_response")) thisLine;
     if thisLine = "" 
     then (TextIO.output (E_proof_file, "No proof output seen \n");
	    TextIO.closeOut E_proof_file;
	    false)
     else if thisLine = "# TSTP exit status: Unsatisfiable\n"
     then      
       startTransfer (start_E, end_E)
             (fromChild, toParent, ppid, goalstring, childCmd, clause_arr)
     else if String.isPrefix "# Problem is satisfiable" thisLine
     then  
       (TextIO.output (toParent, "Invalid\n");
	TextIO.output (toParent, goalstring^"\n");
	TextIO.flushOut toParent;
	TextIO.output (E_proof_file, thisLine);
	TextIO.closeOut E_proof_file;
	Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
	(* Attempt to prevent several signals from turning up simultaneously *)
	Posix.Process.sleep(Time.fromSeconds 1);
	true)
     else if String.isPrefix "# Failure: Resource limit exceeded" thisLine
     then  (*In fact, E distingishes "out of time" and "out of memory"*)
       (File.write (File.tmp_path (Path.basic "e_response")) thisLine;
	TextIO.output (toParent, "Failure\n");
	TextIO.output (toParent, goalstring^"\n");
	TextIO.flushOut toParent;
	Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
	TextIO.output (E_proof_file, "signalled parent\n");
	TextIO.closeOut E_proof_file;
	(* Attempt to prevent several signals from turning up simultaneously *)
	Posix.Process.sleep(Time.fromSeconds 1);
	true)
     else
	(TextIO.output (E_proof_file, thisLine);
	TextIO.flushOut E_proof_file;
	checkEProofFound (fromChild, toParent, ppid, goalstring, childCmd, clause_arr))
 end


(**********************************************************************)
(*  Reconstruct the Spass proof w.r.t. thmstring (string version of   *)
(*  Isabelle goal to be proved), then transfer the reconstruction     *)
(*  steps as a string to the input pipe of the main Isabelle process  *)
(**********************************************************************)

fun spass_reconstruct_tac proofextract goalstring toParent ppid sg_num 
                    clause_arr = 
 SELECT_GOAL
  (EVERY1 [rtac ccontr, ObjectLogic.atomize_tac, skolemize_tac, 
	   METAHYPS(fn negs => 
  Recon_Transfer.spass_reconstruct proofextract goalstring toParent ppid negs clause_arr)]) sg_num;


fun transferSpassInput (fromChild, toParent, ppid, goalstring, 
                        currentString, thm, sg_num, clause_arr) = 
 let val thisLine = TextIO.inputLine fromChild 
 in 
    if thisLine = "" (*end of file?*)
    then (File.write (File.tmp_path (Path.basic"spass_extraction_failed")) currentString;
	  raise EOF)                    
    else if String.isPrefix "--------------------------SPASS-STOP" thisLine
    then 
      let val proofextract = extract_proof (currentString^thisLine)
      in 
	 File.write (File.tmp_path (Path.basic"spass_extracted_prf")) proofextract;
	 if !reconstruct 
	 then (spass_reconstruct_tac proofextract goalstring toParent ppid sg_num 
		clause_arr thm; ())
	 else Recon_Transfer.spass_lemma_list proofextract goalstring 
	        toParent ppid clause_arr 
      end
    else transferSpassInput (fromChild, toParent, ppid, goalstring,
			     (currentString^thisLine), thm, sg_num, clause_arr)
 end;


(*********************************************************************************)
(*  Inspect the output of a Spass   process to see if it has found a proof,     *)
(*  and if so, transfer output to the input pipe of the main Isabelle process    *)
(*********************************************************************************)

 
fun startSpassTransfer (fromChild, toParent, ppid, goalstring,childCmd,
                        thm, sg_num,clause_arr) = 
   let val thisLine = TextIO.inputLine fromChild  
   in                 
      if thisLine = "" then false
      else if String.isPrefix "Here is a proof" thisLine then     
	 (File.append (File.tmp_path (Path.basic "spass_transfer"))
		      ("about to transfer proof, thm is: " ^ string_of_thm thm ^ "\n");
	  transferSpassInput (fromChild, toParent, ppid, goalstring,thisLine, 
 	                     thm, sg_num,clause_arr);
	  true) handle EOF => false
      else startSpassTransfer (fromChild, toParent, ppid, goalstring,
                               childCmd, thm, sg_num,clause_arr)
    end


(*Called from watcher. Returns true if the E process has returned a verdict.*)
fun checkSpassProofFound (fromChild, toParent, ppid, goalstring, childCmd,
                          thm, sg_num, clause_arr) = 
 let val spass_proof_file = TextIO.openAppend
           (File.platform_path(File.tmp_path (Path.basic "spass_proof")))
     val _ = File.write(File.tmp_path (Path.basic "spass_checking_prf"))
		("checking if proof found, thm is: "^(string_of_thm thm))
     val thisLine = TextIO.inputLine fromChild  
 in    
     File.write (File.tmp_path (Path.basic "spass_response")) thisLine;
     if thisLine = "" 
     then (TextIO.output (spass_proof_file, ("No proof output seen \n"));
	   TextIO.closeOut spass_proof_file;
	   false)
     else if thisLine = "SPASS beiseite: Proof found.\n"
     then      
        startSpassTransfer (fromChild, toParent, ppid, goalstring,
	                    childCmd, thm, sg_num, clause_arr)
     else if thisLine = "SPASS beiseite: Completion found.\n"
     then  
       (TextIO.output (spass_proof_file, thisLine);
	TextIO.closeOut spass_proof_file;
	TextIO.output (toParent, "Invalid\n");
	TextIO.output (toParent, goalstring^"\n");
	TextIO.flushOut toParent;
	Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
	(* Attempt to prevent several signals from turning up simultaneously *)
	Posix.Process.sleep(Time.fromSeconds 1);
	true)
     else if thisLine = "SPASS beiseite: Ran out of time.\n" orelse
             thisLine = "SPASS beiseite: Maximal number of loops exceeded.\n"
     then  
       (TextIO.output (toParent, "Failure\n");
	TextIO.output (toParent, goalstring^"\n");
	TextIO.flushOut toParent;
	Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
	TextIO.output (spass_proof_file, "signalled parent\n");
	TextIO.closeOut spass_proof_file;
	(* Attempt to prevent several signals from turning up simultaneously *)
	Posix.Process.sleep(Time.fromSeconds 1);
	true)
    else
       (TextIO.output (spass_proof_file, thisLine);
       TextIO.flushOut spass_proof_file;
       checkSpassProofFound  (fromChild, toParent, ppid, goalstring,
       childCmd, thm, sg_num, clause_arr))
 end

end;
