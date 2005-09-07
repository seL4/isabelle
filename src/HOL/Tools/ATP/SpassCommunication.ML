(*  Title:      SpassCommunication.ml
    ID:         $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

(***************************************************************************)
(*  Code to deal with the transfer of proofs from a Spass process          *)
(***************************************************************************)
signature SPASS_COMM =
  sig
    val reconstruct : bool ref
    val getSpassInput : TextIO.instream -> string * string * string
    val checkSpassProofFound:  
          TextIO.instream * TextIO.outstream * Posix.Process.pid * string * 
          string * string * thm * int * (ResClause.clause * thm) Array.array * int -> bool
  end;

structure SpassComm : SPASS_COMM =
struct

(* switch for whether to reconstruct a proof found, or just list the lemmas used *)
val reconstruct = ref false;

exception EOF;

(**********************************************************************)
(*  Reconstruct the Spass proof w.r.t. thmstring (string version of   *)
(*  Isabelle goal to be proved), then transfer the reconstruction     *)
(*  steps as a string to the input pipe of the main Isabelle process  *)
(**********************************************************************)

fun reconstruct_tac proofextract thmstring goalstring toParent ppid sg_num 
                    clause_arr num_of_clauses = 
 let val f = if !reconstruct then Recon_Transfer.spassString_to_reconString
                             else Recon_Transfer.spassString_to_lemmaString
 in                             
   SELECT_GOAL
    (EVERY1 [rtac ccontr, ResLib.atomize_tac, skolemize_tac, 
             METAHYPS(fn negs => 
    f proofextract thmstring goalstring 
              toParent ppid negs clause_arr num_of_clauses)]) sg_num	
 end;


fun transferSpassInput (fromChild, toParent, ppid,thmstring,goalstring, 
                        currentString, thm, sg_num,clause_arr, num_of_clauses) = 
 let val thisLine = TextIO.inputLine fromChild 
 in 
    if thisLine = "" (*end of file?*)
    then (File.write (File.tmp_path (Path.basic"eprover_extraction_failed")) currentString;
	  raise EOF)                    
    else if thisLine = "--------------------------SPASS-STOP------------------------------\n"
    then 
      let val proofextract = Recon_Parse.extract_proof (currentString^thisLine)
      in 
	  File.write (File.tmp_path (Path.basic"spass_extracted_prf")) proofextract;
	  reconstruct_tac proofextract thmstring goalstring toParent ppid sg_num 
	      clause_arr num_of_clauses thm
      end
    else transferSpassInput (fromChild, toParent, ppid,thmstring, goalstring,
			     (currentString^thisLine), thm, sg_num, clause_arr, 
			     num_of_clauses)
 end;


(*********************************************************************************)
(*  Inspect the output of a Spass   process to see if it has found a proof,     *)
(*  and if so, transfer output to the input pipe of the main Isabelle process    *)
(*********************************************************************************)

 
fun startSpassTransfer (fromChild, toParent, ppid, thmstring,goalstring,childCmd,
                        thm, sg_num,clause_arr, num_of_clauses) = 
   let val thisLine = TextIO.inputLine fromChild  
   in                 
      if thisLine = "" then false
      else if String.isPrefix "Here is a proof" thisLine then     
	 (File.append (File.tmp_path (Path.basic "spass_transfer"))
		      ("about to transfer proof, thm is: " ^ string_of_thm thm ^ "\n");
	  transferSpassInput (fromChild, toParent, ppid,thmstring, goalstring,thisLine, 
 	                     thm, sg_num,clause_arr, num_of_clauses);
	  true) handle EOF => false
      else startSpassTransfer (fromChild, toParent, ppid, thmstring, goalstring,
                               childCmd, thm, sg_num,clause_arr, num_of_clauses)
    end


fun checkSpassProofFound (fromChild, toParent, ppid,thmstring,goalstring, childCmd,
                          thm, sg_num, clause_arr, (num_of_clauses:int )) = 
 let val spass_proof_file = TextIO.openAppend
           (File.platform_path(File.tmp_path (Path.basic "spass_proof")))
     val _ = File.write(File.tmp_path (Path.basic "spass_checking_prf"))
		("checking if proof found, thm is: "^(string_of_thm thm))
     val thisLine = TextIO.inputLine fromChild  
 in    
     if thisLine = "" 
     then (TextIO.output (spass_proof_file, ("No proof output seen \n"));
	   TextIO.closeOut spass_proof_file;
	   false)
     else if thisLine = "SPASS beiseite: Proof found.\n"
     then      
       (File.write (File.tmp_path (Path.basic "spass_response")) thisLine;
	startSpassTransfer (fromChild, toParent, ppid, thmstring,goalstring,
	                    childCmd, thm, sg_num, clause_arr, num_of_clauses))
     else if thisLine = "SPASS beiseite: Completion found.\n"
     then  
       (File.write (File.tmp_path (Path.basic "spass_response")) thisLine;
	TextIO.output (toParent,childCmd^"\n" );
	TextIO.flushOut toParent;
	TextIO.output (spass_proof_file, thisLine);
	TextIO.flushOut spass_proof_file;
	TextIO.closeOut spass_proof_file;

	TextIO.output (toParent, thisLine^"\n");
	TextIO.output (toParent, thmstring^"\n");
	TextIO.output (toParent, goalstring^"\n");
	TextIO.flushOut toParent;
	Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
	(* Attempt to prevent several signals from turning up simultaneously *)
	Posix.Process.sleep(Time.fromSeconds 1);
	true)
     else if thisLine = "SPASS beiseite: Ran out of time.\n" 
     then  
       (File.write (File.tmp_path (Path.basic "spass_response")) thisLine;
        TextIO.output (toParent, thisLine^"\n");
	TextIO.output (toParent, thmstring^"\n");
	TextIO.output (toParent, goalstring^"\n");
	TextIO.flushOut toParent;
	Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
	TextIO.output (spass_proof_file, "signalled parent\n");
	TextIO.closeOut spass_proof_file;
	(* Attempt to prevent several signals from turning up simultaneously *)
	Posix.Process.sleep(Time.fromSeconds 1);
	true)
    else if thisLine = "SPASS beiseite: Maximal number of loops exceeded.\n"                                                            		                 
    then
       (Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
	TextIO.output (toParent,childCmd^"\n" );
	TextIO.flushOut toParent;
	TextIO.output (toParent, thisLine);
	TextIO.flushOut toParent;
	true)
    else
       (TextIO.output (spass_proof_file, thisLine);
       TextIO.flushOut spass_proof_file;
       checkSpassProofFound  (fromChild, toParent, ppid, thmstring,goalstring,
       childCmd, thm, sg_num, clause_arr, num_of_clauses))
 end

  
(***********************************************************************)
(*  Function used by the Isabelle process to read in a spass proof   *)
(***********************************************************************)

fun getSpassInput instr = 
    let val thisLine = TextIO.inputLine instr 
        val _ = File.write (File.tmp_path (Path.basic "spass_line")) thisLine
    in 
      if thisLine = "" then ("No output from reconstruction process.\n","","")
      else if String.sub (thisLine, 0) = #"[" orelse
         String.isPrefix "SPASS beiseite:" thisLine orelse
         String.isPrefix  "Rules from" thisLine
      then 
	let val thmstring = TextIO.inputLine instr 
	    val goalstring = TextIO.inputLine instr   
	in (thisLine, thmstring, goalstring) end
      else if substring (thisLine,0,5) = "Proof" orelse
              String.sub (thisLine, 0) = #"%"
      then
	let val thmstring = TextIO.inputLine instr
	    val goalstring = TextIO.inputLine instr
	in
          File.write (File.tmp_path (Path.basic "getSpassInput")) thisLine;
          (thisLine, thmstring, goalstring)
        end
      else getSpassInput instr
     end


end;
