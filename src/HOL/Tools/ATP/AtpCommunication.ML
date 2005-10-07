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
          string * (ResClause.clause * thm) Array.array -> bool
    val checkVampProofFound: 
          TextIO.instream * TextIO.outstream * Posix.Process.pid * 
          string * (ResClause.clause * thm) Array.array -> bool
    val checkSpassProofFound:  
          TextIO.instream * TextIO.outstream * Posix.Process.pid * 
          string * thm * int * (ResClause.clause * thm) Array.array -> bool
    val signal_parent:  
          TextIO.outstream * Posix.Process.pid * string * string -> unit
  end;

structure AtpCommunication : ATP_COMMUNICATION =
struct

(* switch for whether to reconstruct a proof found, or just list the lemmas used *)
val reconstruct = ref false;

val trace_path = Path.basic "atp_trace";

fun trace s = if !Output.show_debug_msgs then File.append (File.tmp_path trace_path) s 
              else ();

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
  else if cut_exists end_V8 s then
    (kill_lines 0    (*Vampire 8.0*)
     o fst o cut_before end_V8) s
  else if cut_exists end_E s then
    (kill_lines 0    (*eproof*)
     o fst o cut_before end_E) s
  else "??extract_proof failed" (*Couldn't find a proof*)
end;


(*********************************************************************************)
(*  Inspect the output of an ATP process to see if it has found a proof,     *)
(*  and if so, transfer output to the input pipe of the main Isabelle process    *)
(*********************************************************************************)

fun startTransfer (endS, fromChild, toParent, ppid, probfile, clause_arr) =
 let fun transferInput currentString =
      let val thisLine = TextIO.inputLine fromChild
      in
	if thisLine = "" (*end of file?*)
	then (trace ("\n extraction_failed.  End bracket: " ^ endS ^
	             "\naccumulated text: " ^ currentString);
	      raise EOF)                    
	else if String.isPrefix endS thisLine
	then let val proofextract = extract_proof (currentString^thisLine)
	         val lemma_list = if endS = end_V8 
			  	  then Recon_Transfer.vamp_lemma_list
			  	  else Recon_Transfer.e_lemma_list
	     in
	       trace ("\nExtracted proof:\n" ^ proofextract); 
	       lemma_list proofextract probfile toParent ppid clause_arr
	     end
	else transferInput (currentString^thisLine)
      end
 in
     transferInput "";  true
 end handle EOF => false


(*The signal handler in watcher.ML must be able to read the output of this.*)
fun signal_parent (toParent, ppid, msg, probfile) =
 (TextIO.output (toParent, msg);
  TextIO.output (toParent, probfile ^ "\n");
  TextIO.flushOut toParent;
  trace ("\nSignalled parent: " ^ msg ^ probfile);
  Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
  (*Give the parent time to respond before possibly sending another signal*)
  OS.Process.sleep (Time.fromMilliseconds 600));

(*Called from watcher. Returns true if the Vampire process has returned a verdict.*)
fun checkVampProofFound (fromChild, toParent, ppid, probfile, clause_arr) =
 let val thisLine = TextIO.inputLine fromChild
 in   
     trace thisLine;
     if thisLine = "" 
     then (trace "\nNo proof output seen"; false)
     else if String.isPrefix start_V8 thisLine
     then startTransfer (end_V8, fromChild, toParent, ppid, probfile, clause_arr)
     else if (String.isPrefix "Satisfiability detected" thisLine) orelse
             (String.isPrefix "Refutation not found" thisLine)
     then (signal_parent (toParent, ppid, "Failure\n", probfile);
	   true)
     else
        checkVampProofFound  (fromChild, toParent, ppid, probfile, clause_arr)
  end


(*Called from watcher. Returns true if the E process has returned a verdict.*)
fun checkEProofFound (fromChild, toParent, ppid, probfile, clause_arr) = 
 let val thisLine = TextIO.inputLine fromChild  
 in   
     trace thisLine;
     if thisLine = "" 
     then (trace "\nNo proof output seen"; false)
     else if String.isPrefix start_E thisLine
     then      
       startTransfer (end_E, fromChild, toParent, ppid, probfile, clause_arr)
     else if String.isPrefix "# Problem is satisfiable" thisLine
     then (signal_parent (toParent, ppid, "Invalid\n", probfile);
	   true)
     else if String.isPrefix "# Cannot determine problem status within resource limit" thisLine
     then (signal_parent (toParent, ppid, "Failure\n", probfile);
	   true)
     else
	checkEProofFound (fromChild, toParent, ppid, probfile, clause_arr)
 end


(**********************************************************************)
(*  Reconstruct the Spass proof w.r.t. thmstring (string version of   *)
(*  Isabelle goal to be proved), then transfer the reconstruction     *)
(*  steps as a string to the input pipe of the main Isabelle process  *)
(**********************************************************************)

fun spass_reconstruct_tac proofextract toParent ppid probfile sg_num clause_arr = 
 SELECT_GOAL
  (EVERY1 [rtac ccontr, ObjectLogic.atomize_tac, skolemize_tac, 
	   METAHYPS(fn negs => 
		  Recon_Transfer.spass_reconstruct proofextract probfile 
				toParent ppid negs clause_arr)]) sg_num;


fun transferSpassInput (fromChild, toParent, ppid, probfile,
                        currentString, thm, sg_num, clause_arr) = 
 let val thisLine = TextIO.inputLine fromChild 
 in 
    trace thisLine;
    if thisLine = "" (*end of file?*)
    then (trace ("\nspass_extraction_failed: " ^ currentString);
	  raise EOF)                    
    else if String.isPrefix "--------------------------SPASS-STOP" thisLine
    then 
      let val proofextract = extract_proof (currentString^thisLine)
      in 
	 trace ("\nextracted spass proof: " ^ proofextract);
	 if !reconstruct 
	 then (spass_reconstruct_tac proofextract toParent ppid probfile sg_num 
		clause_arr thm; ())
	 else Recon_Transfer.spass_lemma_list proofextract probfile toParent
	        ppid clause_arr 
      end
    else transferSpassInput (fromChild, toParent, ppid, probfile,
			     (currentString^thisLine), thm, sg_num, clause_arr)
 end;


(*********************************************************************************)
(*  Inspect the output of a Spass   process to see if it has found a proof,     *)
(*  and if so, transfer output to the input pipe of the main Isabelle process    *)
(*********************************************************************************)

 
fun startSpassTransfer (fromChild, toParent, ppid, probfile,
                        thm, sg_num,clause_arr) = 
   let val thisLine = TextIO.inputLine fromChild  
   in                 
      if thisLine = "" then false
      else if String.isPrefix "Here is a proof" thisLine then     
	 (trace ("\nabout to transfer SPASS proof\n:");
	  transferSpassInput (fromChild, toParent, ppid, probfile, thisLine, 
 	                     thm, sg_num,clause_arr);
	  true) handle EOF => false
      else startSpassTransfer (fromChild, toParent, ppid, probfile, thm, sg_num,clause_arr)
    end


(*Called from watcher. Returns true if the SPASS process has returned a verdict.*)
fun checkSpassProofFound (fromChild, toParent, ppid, probfile,
                          thm, sg_num, clause_arr) = 
 let val thisLine = TextIO.inputLine fromChild  
 in    
     trace thisLine;
     if thisLine = "" then (trace "\nNo proof output seen"; false)
     else if thisLine = "SPASS beiseite: Proof found.\n"
     then      
        startSpassTransfer (fromChild, toParent, ppid, probfile, thm, sg_num, clause_arr)
     else if thisLine = "SPASS beiseite: Completion found.\n"
     then (signal_parent (toParent, ppid, "Invalid\n", probfile);
	   true)
     else if thisLine = "SPASS beiseite: Ran out of time.\n" orelse
             thisLine = "SPASS beiseite: Maximal number of loops exceeded.\n"
     then (signal_parent (toParent, ppid, "Failure\n", probfile);
	   true)
    else checkSpassProofFound (fromChild, toParent, ppid, probfile, thm, sg_num, clause_arr)
 end

end;
