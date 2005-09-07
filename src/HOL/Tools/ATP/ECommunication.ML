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

(***********************************)
(*  Write E   output to a file *)
(***********************************)

fun logEInput (instr, fd) = 
  let val thisLine = TextIO.inputLine instr 
  in if thisLine = "# Proof object ends here.\n" 
     then TextIO.output (fd, thisLine)
     else (TextIO.output (fd, thisLine); logEInput (instr,fd))
  end;

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


fun transferEInput (fromChild, toParent, ppid,thmstring,goalstring, currentString, thm, sg_num,clause_arr,  num_of_clauses) = 
  let val thisLine = TextIO.inputLine fromChild 
  in 
     if thisLine = "# Proof object ends here.\n"
     then 
       let val proofextract = Recon_Parse.extract_proof (currentString^thisLine)
       in 
	   File.write (File.tmp_path (Path.basic"extracted-prf-E")) proofextract;
	   reconstruct_tac proofextract thmstring goalstring toParent ppid sg_num 
	       clause_arr num_of_clauses thm
       end
     else transferEInput (fromChild, toParent, ppid,thmstring, goalstring,
                              (currentString^thisLine), thm, sg_num, clause_arr,  
                              num_of_clauses)
  end;


(*********************************************************************************)
(*  Inspect the output of an E process to see if it has found a proof,      *)
(*  and if so, transfer output to the input pipe of the main Isabelle process    *)
(*********************************************************************************)

 
fun startETransfer (fromChild, toParent, ppid, thmstring,goalstring,childCmd,
                    thm, sg_num,clause_arr, num_of_clauses) = 
  if isSome (TextIO.canInput(fromChild, 5))
  then
    let val thisLine = TextIO.inputLine fromChild  
    in                 
      if String.isPrefix "# Proof object starts" thisLine 
      then     
	 (File.append (File.tmp_path (Path.basic "transfer-E"))
		      ("about to transfer proof, thm is: " ^ string_of_thm thm);
	  transferEInput (fromChild, toParent, ppid,thmstring, goalstring,thisLine, 
			      thm, sg_num,clause_arr,  num_of_clauses);
	  true)
      else startETransfer (fromChild, toParent, ppid, thmstring, goalstring,
			       childCmd, thm, sg_num,clause_arr, num_of_clauses)
     end
   else false


fun checkEProofFound (fromChild, toParent, ppid,thmstring,goalstring, childCmd, thm, sg_num, clause_arr,  num_of_clauses) = 
  let val E_proof_file = TextIO.openAppend(File.platform_path(File.tmp_path (Path.basic "E_proof")))
        val _ = File.write (File.tmp_path (Path.basic "checking-prf-E"))
                           ("checking if proof found, thm is: " ^ string_of_thm thm)
  in 
  if (isSome (TextIO.canInput(fromChild, 5)))
  then
  let val thisLine = TextIO.inputLine fromChild  
      in if (*thisLine = "# Problem is unsatisfiable (or provable), constructing proof object\n"*)
             thisLine = "# TSTP exit status: Unsatisfiable\n"
	 then      
	    let val outfile = TextIO.openAppend(File.platform_path(File.tmp_path (Path.basic "foo_proof")));                                                                                (*val _ =  Posix.Process.sleep(Time.fromSeconds 3 );*)
		val _ = TextIO.output (outfile, thisLine)
	
		val _ = TextIO.closeOut outfile
	    in 
	       startETransfer (fromChild, toParent, ppid, thmstring,goalstring,childCmd, thm, sg_num, clause_arr,  num_of_clauses) 
	    end
	 else if thisLine= "# Problem is satisfiable (or invalid), generating saturation derivation\n"
	 then  
	    let val  outfile = TextIO.openAppend(File.platform_path(File.tmp_path (Path.basic "foo_proof"))); 
		val _ = TextIO.output (outfile, thisLine)
		val _ =  TextIO.closeOut outfile
	    in
	      TextIO.output (toParent,childCmd^"\n" );
	      TextIO.flushOut toParent;
	      TextIO.output (E_proof_file, thisLine);
	      TextIO.flushOut E_proof_file;
	      TextIO.closeOut E_proof_file;
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
	   else if thisLine = "# Failure: Resource limit exceeded (time)\n" 
	   then  
	     let val outfile = TextIO.openAppend(File.platform_path(File.tmp_path (Path.basic "foo_proof")));                                          	(*val _ =  Posix.Process.sleep(Time.fromSeconds 3 );*)
	     val _ = TextIO.output (outfile, thisLine)
 	     in TextIO.output (toParent, thisLine^"\n");
		TextIO.flushOut toParent;
		TextIO.output (toParent, thmstring^"\n");
		TextIO.flushOut toParent;
		TextIO.output (toParent, goalstring^"\n");
		TextIO.flushOut toParent;
		Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
		TextIO.output (outfile, ("signalled parent\n"));TextIO.closeOut outfile;
	        (* Attempt to prevent several signals from turning up simultaneously *)
	        Posix.Process.sleep(Time.fromSeconds 1);
		true 
	     end
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
	     childCmd, thm, sg_num, clause_arr,  num_of_clauses))
	 end
    else 
	(TextIO.output (E_proof_file, ("No proof output seen \n"));
	 TextIO.closeOut E_proof_file;
	 false)
 end


  
(***********************************************************************)
(*  Function used by the Isabelle process to read in a E proof   *)
(***********************************************************************)

fun getEInput instr = 
  if isSome (TextIO.canInput(instr, 2))
  then
    let val thisLine = TextIO.inputLine instr 
	val outfile = TextIO.openAppend(File.platform_path(File.tmp_path (Path.basic "foo_thisLine")));
	val _ = TextIO.output (outfile, thisLine)
	val _ =  TextIO.closeOut outfile
    in 
      if substring (thisLine, 0,1) = "["
      then 
	(*Pretty.writeln(Pretty.str thisLine)*)
	let val reconstr = thisLine
	    val thmstring = TextIO.inputLine instr 
	    val goalstring = TextIO.inputLine instr   
	in
	    (reconstr, thmstring, goalstring)
	end
      else if String.isPrefix "SPASS beiseite:" thisLine 
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
  else 
      ("No output from reconstruction process.\n","","")

end;
