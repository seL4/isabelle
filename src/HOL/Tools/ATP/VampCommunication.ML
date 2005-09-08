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
    val getEInput : TextIO.instream -> string * string * string
    val checkEProofFound: 
          TextIO.instream * TextIO.outstream * Posix.Process.pid * string * 
          string * string * thm * int * (ResClause.clause * thm) Array.array * int -> bool

    val getVampInput : TextIO.instream -> string * string * string
    val checkVampProofFound: 
          TextIO.instream * TextIO.outstream * Posix.Process.pid * string *
          string * string * thm * int * (ResClause.clause * thm) Array.array * int -> bool
  end;

structure VampComm : VAMP_COMM =
struct

exception EOF;

(**********************************************************************)
(*  Reconstruct the Vampire/E proof w.r.t. thmstring (string version of   *)
(*  Isabelle goal to be proved), then transfer the reconstruction     *)
(*  steps as a string to the input pipe of the main Isabelle process  *)
(**********************************************************************)

fun reconstruct_tac proofextract thmstring goalstring toParent ppid sg_num 
                    clause_arr num_of_clauses =
    SELECT_GOAL
      (EVERY1
        [rtac ccontr, ResLib.atomize_tac, skolemize_tac,
	 METAHYPS(fn negs =>
		     (Recon_Transfer.proverString_to_lemmaString proofextract thmstring 
		       goalstring toParent ppid negs clause_arr num_of_clauses))]) sg_num


(*********************************************************************************)
(*  Inspect the output of an ATP process to see if it has found a proof,     *)
(*  and if so, transfer output to the input pipe of the main Isabelle process    *)
(*********************************************************************************)

fun startTransfer (startS,endS)
      (fromChild, toParent, ppid, thmstring,goalstring,childCmd,
       thm, sg_num,clause_arr, num_of_clauses) =
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
	then let val proofextract = Recon_Parse.extract_proof (currentString^thisLine)
	     in
	       File.write (File.tmp_path (Path.basic"extracted_prf")) proofextract; 
	       reconstruct_tac proofextract thmstring goalstring toParent ppid sg_num  
			       clause_arr num_of_clauses thm
	     end
	else transferInput (currentString^thisLine)
      end
 in
   if thisLine = "" then false
   else if String.isPrefix startS thisLine
   then
    (File.append (File.tmp_path (Path.basic "transfer_start"))
		 ("about to transfer proof, thm is: " ^ string_of_thm thm);
     transferInput thisLine;
     true) handle EOF => false
   else
      startTransfer (startS,endS)
                    (fromChild, toParent, ppid, thmstring, goalstring,
		     childCmd, thm, sg_num,clause_arr, num_of_clauses)
 end


fun checkVampProofFound (fromChild, toParent, ppid,thmstring,goalstring, childCmd, 
                         thm, sg_num, clause_arr, num_of_clauses) =
 let val proof_file = TextIO.openAppend
	   (File.platform_path(File.tmp_path (Path.basic "atp_proof")))
     val _ = File.write (File.tmp_path (Path.basic "atp_checking_prf"))
			("checking if proof found, thm is: " ^ string_of_thm thm)
     val thisLine = TextIO.inputLine fromChild
 in   
     if thisLine = "" 
     then (TextIO.output (proof_file, "No proof output seen \n");
	   TextIO.closeOut proof_file;
	   false)
     else if thisLine = "% Proof found. Thanks to Tanya!\n"
     then
       (File.write (File.tmp_path (Path.basic "atp_response")) thisLine;
	startTransfer (Recon_Parse.start_V6, Recon_Parse.end_V6)
	      (fromChild, toParent, ppid, thmstring, goalstring,
	       childCmd, thm, sg_num, clause_arr, num_of_clauses))
     else if (thisLine = "% Unprovable.\n" ) orelse
             (thisLine = "% Proof not found. Time limit expired.\n")
     then
       (File.write (File.tmp_path (Path.basic "atp_response")) thisLine;
	TextIO.output (toParent,childCmd^"\n");
	TextIO.flushOut toParent;
	TextIO.output (proof_file, thisLine);
	TextIO.closeOut proof_file;
 
	TextIO.output (toParent, thisLine^"\n");
	TextIO.output (toParent, thmstring^"\n");
	TextIO.output (toParent, goalstring^"\n");
	TextIO.flushOut toParent;
	Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
	(* Attempt to prevent several signals from turning up simultaneously *)
	Posix.Process.sleep(Time.fromSeconds 1);
	true)
     else
       (TextIO.output (proof_file, thisLine);
	TextIO.flushOut proof_file;
	checkVampProofFound  (fromChild, toParent, ppid, thmstring,
	   goalstring,childCmd, thm, sg_num, clause_arr, num_of_clauses))
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
     else if thisLine = "# TSTP exit status: Unsatisfiable\n"
     then      
       (File.write (File.tmp_path (Path.basic "eprover_response")) thisLine;
       startTransfer (Recon_Parse.start_E, Recon_Parse.end_E)
             (fromChild, toParent, ppid, thmstring, goalstring,
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
(*  Function used by the Isabelle process to read in a Vampire proof   *)
(***********************************************************************)

fun getVampInput instr =
    let val thisLine = TextIO.inputLine instr
	val _ = File.write (File.tmp_path (Path.basic "atp_line")) thisLine
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


(*FIXME!!: The following code is a mess. It mostly refers to SPASS-specific things*)

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
