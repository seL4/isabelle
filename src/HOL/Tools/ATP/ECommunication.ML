(*  Title:      SpassCommunication.ml
    ID:         $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

(***************************************************************************)
(*  Code to deal with the transfer of proofs from a E process          *)
(***************************************************************************)
signature E_COMM =
  sig
    val E: bool ref
    val getEInput : TextIO.instream -> string * string * string
    val checkEProofFound: 
          TextIO.instream * TextIO.outstream * Posix.Process.pid * string * 
          string * string * thm * int * (ResClause.clause * thm) Array.array * int -> bool
  end;

structure EComm : E_COMM =
struct

val E = ref false;

exception EOF;

(**********************************************************************)
(*  Reconstruct the E proof w.r.t. thmstring (string version of   *)
(*  Isabelle goal to be proved), then transfer the reconstruction     *)
(*  steps as a string to the input pipe of the main Isabelle process  *)
(**********************************************************************)

fun reconstruct_tac proofextract thmstring goalstring toParent ppid sg_num 
                    clause_arr num_of_clauses = 
   SELECT_GOAL
    (EVERY1 [rtac ccontr, ResLib.atomize_tac, skolemize_tac, 
             METAHYPS(fn negs => 
    (Recon_Transfer.EString_to_lemmaString proofextract thmstring goalstring 
              toParent ppid negs clause_arr  num_of_clauses ))]) sg_num	


fun transferEInput (fromChild, toParent, ppid,thmstring,goalstring, 
                    currentString, thm, sg_num,clause_arr, num_of_clauses) = 
 let val thisLine = TextIO.inputLine fromChild 
 in 
     File.append (File.tmp_path (Path.basic "eprover_transfer"))
		      ("transferEInput input line: " ^ thisLine);        
    if thisLine = "" (*end of file?*)
    then (File.write (File.tmp_path (Path.basic"eprover_extraction_failed")) currentString;
	  raise EOF)                    
    else if thisLine = "# Proof object ends here.\n"
    then 
      let val proofextract = Recon_Parse.extract_proof (currentString^thisLine)
      in 
	  File.write (File.tmp_path (Path.basic"eprover_extracted_prf")) proofextract;
	  reconstruct_tac proofextract thmstring goalstring toParent ppid sg_num 
	      clause_arr num_of_clauses thm
      end
    else transferEInput (fromChild, toParent, ppid,thmstring, goalstring,
			     (currentString^thisLine), thm, sg_num, clause_arr, 
			     num_of_clauses)
 end;


(*********************************************************************************)
(*  Inspect the output of an E process to see if it has found a proof,     *)
(*  and if so, transfer output to the input pipe of the main Isabelle process    *)
(*********************************************************************************)

 
fun startETransfer (fromChild, toParent, ppid, thmstring,goalstring,childCmd,
                    thm, sg_num,clause_arr, num_of_clauses) = 
    let val thisLine = TextIO.inputLine fromChild  
    in                 
      if thisLine = "" then false
      else if String.isPrefix "# Proof object starts" thisLine 
      then     
	 (File.append (File.tmp_path (Path.basic "eprover_transfer"))
		      ("about to transfer proof, thm is: " ^ string_of_thm thm ^ "\n");
	  transferEInput (fromChild, toParent, ppid,thmstring, goalstring,thisLine, 
			      thm, sg_num,clause_arr, num_of_clauses);
	  true) handle EOF => false
      else startETransfer (fromChild, toParent, ppid, thmstring, goalstring,
			       childCmd, thm, sg_num,clause_arr, num_of_clauses)
     end


fun checkEProofFound (fromChild, toParent, ppid,thmstring,goalstring, childCmd,
                      thm, sg_num, clause_arr, num_of_clauses) = 
 let val E_proof_file = TextIO.openAppend
	   (File.platform_path(File.tmp_path (Path.basic "eprover_proof")))
     val _ = File.write (File.tmp_path (Path.basic "eprover_checking_prf"))
			("checking if proof found, thm is: " ^ string_of_thm thm)
     val thisLine = TextIO.inputLine fromChild  
 in   
     if thisLine = "" 
     then (TextIO.output (E_proof_file, ("No proof output seen \n"));
	    TextIO.closeOut E_proof_file;
	    false)
     else if (*thisLine = "# Problem is unsatisfiable (or provable), constructing proof object\n"*)
	 thisLine = "# TSTP exit status: Unsatisfiable\n"
     then      
       (File.write (File.tmp_path (Path.basic "eprover_response")) thisLine;
	startETransfer (fromChild, toParent, ppid, thmstring,goalstring,
			childCmd, thm, sg_num, clause_arr, num_of_clauses))
     else if thisLine= "# Problem is satisfiable (or invalid), generating saturation derivation\n"
     then  
       (File.write (File.tmp_path (Path.basic "eprover_response")) thisLine;
	TextIO.output (toParent,childCmd^"\n" );
	TextIO.flushOut toParent;
	TextIO.output (E_proof_file, thisLine);
	TextIO.closeOut E_proof_file;

	TextIO.output (toParent, thisLine^"\n");
	TextIO.output (toParent, thmstring^"\n");
	TextIO.output (toParent, goalstring^"\n");
	TextIO.flushOut toParent;
	Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
	(* Attempt to prevent several signals from turning up simultaneously *)
	Posix.Process.sleep(Time.fromSeconds 1);
	 true)
     else if thisLine = "# Failure: Resource limit exceeded (time)\n" 
     then  
       (File.write (File.tmp_path (Path.basic "eprover_response")) thisLine;
	TextIO.output (toParent, thisLine^"\n");
	TextIO.output (toParent, thmstring^"\n");
	TextIO.output (toParent, goalstring^"\n");
	TextIO.flushOut toParent;
	Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
	TextIO.output (E_proof_file, "signalled parent\n");
	TextIO.closeOut E_proof_file;
	(* Attempt to prevent several signals from turning up simultaneously *)
	Posix.Process.sleep(Time.fromSeconds 1);
	true)
     else if thisLine = "# Failure: Resource limit exceeded (memory)\n"                                                            		                 
     then
	(Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
	 TextIO.output (toParent,childCmd^"\n" );
	 TextIO.flushOut toParent;
	 TextIO.output (toParent, thisLine);
	 TextIO.flushOut toParent;
	 true)
     else
	(TextIO.output (E_proof_file, thisLine);
	TextIO.flushOut E_proof_file;
	checkEProofFound  (fromChild, toParent, ppid, thmstring,goalstring,
	childCmd, thm, sg_num, clause_arr, num_of_clauses))
 end


  
(***********************************************************************)
(*  Function used by the Isabelle process to read in an E proof   *)
(***********************************************************************)

fun getEInput instr = 
    let val thisLine = TextIO.inputLine instr 
        val _ = File.write (File.tmp_path (Path.basic "eprover_line")) thisLine
    in 
      if thisLine = "" then ("No output from reconstruction process.\n","","")
      else if String.sub (thisLine, 0) = #"["
      then 
	let val reconstr = thisLine
	    val thmstring = TextIO.inputLine instr 
	    val goalstring = TextIO.inputLine instr   
	in
	    (reconstr, thmstring, goalstring)
	end
      else if String.isPrefix "SPASS beiseite:" thisLine (*FIXME: wrong!!*)
      then 
	 let val reconstr = thisLine
	     val thmstring = TextIO.inputLine instr
	     val goalstring = TextIO.inputLine instr
	 in
	     (reconstr, thmstring, goalstring)
	 end

       else if String.isPrefix "# No proof" thisLine 
      then 
	 let val reconstr = thisLine
	     val thmstring = TextIO.inputLine instr
	     val goalstring = TextIO.inputLine instr
	 in
	     (reconstr, thmstring, goalstring)
	 end

       else if String.isPrefix "# Failure" thisLine 
      then 
	 let val reconstr = thisLine
	     val thmstring = TextIO.inputLine instr
	     val goalstring = TextIO.inputLine instr
	 in
	     (reconstr, thmstring, goalstring)
	 end
      else if String.isPrefix  "Rules from"  thisLine
      then 
	   let val reconstr = thisLine
	       val thmstring = TextIO.inputLine instr
	       val goalstring = TextIO.inputLine instr
	   in
	       (reconstr, thmstring, goalstring)
	   end
      else if substring (thisLine, 0,5) = "Proof"
      then
	let val reconstr = thisLine
	    val thmstring = TextIO.inputLine instr
	    val goalstring = TextIO.inputLine instr
	in
          File.write (File.tmp_path (Path.basic "foo_getSpass")) thisLine;
          (reconstr, thmstring, goalstring)
        end
      else if substring (thisLine, 0,1) = "%"
      then
	let val reconstr = thisLine
	    val thmstring = TextIO.inputLine instr
	    val goalstring = TextIO.inputLine instr
	in
           File.write (File.tmp_path (Path.basic "foo_getSpass")) thisLine;
	   (reconstr, thmstring, goalstring)
	end
      else getEInput instr
     end
end;
