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
    val spass: bool ref
    val getSpassInput : TextIO.instream -> string * string * string
    val checkSpassProofFound:  TextIO.instream * TextIO.outstream * Posix.Process.pid * string * 
                               string *string * Thm.thm * int *(ResClause.clause * Thm.thm) Array.array  * int -> bool
    
  end;

structure SpassComm :SPASS_COMM =
struct

(* switch for whether to reconstruct a proof found, or just list the lemmas used *)
val reconstruct = ref true;
val spass = ref true;

(***********************************)
(*  Write Spass   output to a file *)
(***********************************)

fun logSpassInput (instr, fd) = let val thisLine = TextIO.inputLine instr 
			 in if thisLine = "--------------------------SPASS-STOP------------------------------\n" 
			    then TextIO.output (fd, thisLine)
      			  else (
				TextIO.output (fd, thisLine); logSpassInput (instr,fd))
 			 end;

(**********************************************************************)
(*  Reconstruct the Spass proof w.r.t. thmstring (string version of   *)
(*  Isabelle goal to be proved), then transfer the reconstruction     *)
(*  steps as a string to the input pipe of the main Isabelle process  *)
(**********************************************************************)


val atomize_tac =    SUBGOAL
     (fn (prop,_) =>
	 let val ts = Logic.strip_assums_hyp prop
	 in EVERY1 
		[METAHYPS
		     (fn hyps => (cut_facts_tac (map (ObjectLogic.atomize_thm o forall_intr_vars) hyps) 1)),
	  REPEAT_DETERM_N (length ts) o (etac thin_rl)]
     end);


fun reconstruct_tac proofextract thmstring goalstring toParent ppid sg_num clause_arr  (num_of_clauses:int ) = 
 let val foo =   TextIO.openOut( File.platform_path(File.tmp_path (Path.basic"foobar3")));
 in
SELECT_GOAL
  (EVERY1 [rtac ccontr,atomize_tac, skolemize_tac, 
  METAHYPS(fn negs => (if !reconstruct 
		       then 
			   Recon_Transfer.spassString_to_reconString proofextract thmstring goalstring 
								     toParent ppid negs clause_arr  num_of_clauses 
		       else
			   Recon_Transfer.spassString_to_lemmaString proofextract thmstring goalstring 
								     toParent ppid negs clause_arr  num_of_clauses ))]) sg_num	
 end ;


fun transferSpassInput (fromChild, toParent, ppid,thmstring,goalstring, currentString, thm, sg_num,clause_arr,  num_of_clauses) = let 
                         val thisLine = TextIO.inputLine fromChild 
			 in 
                            if (thisLine = "--------------------------SPASS-STOP------------------------------\n" )
			    then ( 
                                    let val proofextract = Recon_Parse.extract_proof (currentString^thisLine)
                                        val foo =   TextIO.openOut( File.platform_path(File.tmp_path (Path.basic"foobar2")));
                                
			            in 

                                        TextIO.output(foo,(proofextract));TextIO.closeOut foo;
                                        reconstruct_tac proofextract thmstring goalstring toParent ppid sg_num  clause_arr  num_of_clauses thm
                                               
                                    end
                                  )
      			    else (
				
                                transferSpassInput (fromChild, toParent, ppid,thmstring, goalstring,(currentString^thisLine), thm, sg_num, clause_arr,  num_of_clauses)
                                )
 			 end;




(*********************************************************************************)
(*  Inspect the output of a Spass   process to see if it has found a proof,      *)
(*  and if so, transfer output to the input pipe of the main Isabelle process    *)
(*********************************************************************************)

 
fun startSpassTransfer (fromChild, toParent, ppid, thmstring,goalstring,childCmd,thm, sg_num,clause_arr, num_of_clauses) = 
                                      (*let val _ = Posix.Process.wait ()
                                      in*)
                                       
                                       if (isSome (TextIO.canInput(fromChild, 5)))
                                       then
                                       (
                                       let val thisLine = TextIO.inputLine fromChild  
                                           in                 
                                             if (String.isPrefix "Here is a proof" thisLine )
                                             then     
                                              ( 
                                                 let 
                                               val outfile =  TextIO.openAppend(File.platform_path(File.tmp_path (Path.basic "foo_transfer")));
                                               val _=  TextIO.output (outfile, "about to transfer proof, thm is: "^(string_of_thm thm));
                                               val _ =  TextIO.closeOut outfile;
                                               in
                                                transferSpassInput (fromChild, toParent, ppid,thmstring, goalstring,thisLine, thm, sg_num,clause_arr,  num_of_clauses);
                                                true
                                               end)
                                             
                                             else 
                                                (
                                                 startSpassTransfer (fromChild, toParent, ppid, thmstring, goalstring,childCmd, thm, sg_num,clause_arr, num_of_clauses)
                                                )
                                            end
                                           )
                                         else (false)
                                     (*  end*)



fun checkSpassProofFound (fromChild, toParent, ppid,thmstring,goalstring, childCmd, thm, sg_num, clause_arr,  (num_of_clauses:int )) = 
                                       let val spass_proof_file =  TextIO.openAppend(File.platform_path(File.tmp_path (Path.basic "spass_proof")))
                                            val  outfile = TextIO.openOut(File.platform_path(File.tmp_path (Path.basic "foo_checkspass")));                                                                            
                                            val _ = TextIO.output (outfile, "checking if proof found, thm is: "^(string_of_thm thm))
                                             
                                            val _ =  TextIO.closeOut outfile
                                       in 
                                       if (isSome (TextIO.canInput(fromChild, 5)))
                                       then
                                       (
                                       let val thisLine = TextIO.inputLine fromChild  
                                           in if ( thisLine = "SPASS beiseite: Proof found.\n" )
                                              then      
                                              (  
                                                 let val  outfile = TextIO.openAppend(File.platform_path(File.tmp_path (Path.basic "foo_proof")));                                                                                (*val _ =  Posix.Process.sleep(Time.fromSeconds 3 );*)
                                                     val _ = TextIO.output (outfile, (thisLine))
                                             
                                                     val _ =  TextIO.closeOut outfile
                                                 in 
                                                    startSpassTransfer (fromChild, toParent, ppid, thmstring,goalstring,childCmd, thm, sg_num, clause_arr,  num_of_clauses) 
                                                 end
                                               )   
                                               else if (thisLine= "SPASS beiseite: Completion found.\n" )
                                                   then  

                                                 (
                                                      let    val  outfile = TextIO.openAppend(File.platform_path(File.tmp_path (Path.basic "foo_proof")));                                                                               (* val _ =  Posix.Process.sleep(Time.fromSeconds 3 );*)
                                                             val _ = TextIO.output (outfile, (thisLine))
                                             
                                                             val _ =  TextIO.closeOut outfile
                                                      in
                                                       
                                                        TextIO.output (toParent,childCmd^"\n" );
                                                        TextIO.flushOut toParent;
                                                        TextIO.output (spass_proof_file, (thisLine));
                                                        TextIO.flushOut spass_proof_file;
                                                        TextIO.closeOut spass_proof_file;
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
                                                      end) 
                                                     else if ( thisLine = "SPASS beiseite: Ran out of time.\n" ) 
                                                          then  
                                                		( let val  outfile = TextIO.openAppend(File.platform_path(File.tmp_path (Path.basic "foo_proof")));                                          	(*val _ =  Posix.Process.sleep(Time.fromSeconds 3 );*)
                                                     		val _ = TextIO.output (outfile, (thisLine))
                                             	
                                                    
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
                                                       		end)


 
                                                    else if ( thisLine = "SPASS beiseite: Maximal number of loops exceeded.\n" )                                                           		    then
                                                 (
                                                        Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
                                                        TextIO.output (toParent,childCmd^"\n" );
                                                        TextIO.flushOut toParent;
                                                        TextIO.output (toParent, thisLine);
                                                        TextIO.flushOut toParent;

                                                        true)
                                                    else
                                                       (TextIO.output (spass_proof_file, (thisLine));
                                                       TextIO.flushOut spass_proof_file;
                                                       checkSpassProofFound  (fromChild, toParent, ppid, thmstring,goalstring,childCmd, thm, sg_num, clause_arr,  num_of_clauses))

                                              end
                                          )
                                         else 
                                             (TextIO.output (spass_proof_file, ("No proof output seen \n"));TextIO.closeOut spass_proof_file;false)
                                      end

  
(***********************************************************************)
(*  Function used by the Isabelle process to read in a spass proof   *)
(***********************************************************************)



fun getSpassInput instr = if (isSome (TextIO.canInput(instr, 2)))
                          then
                               let val thisLine = TextIO.inputLine instr 
                                   val  outfile = TextIO.openAppend(File.platform_path(File.tmp_path (Path.basic "foo_thisLine")));                                                                     val _ = TextIO.output (outfile, (thisLine))

                                             
                                   val _ =  TextIO.closeOut outfile
			       in 
                                     if ( (substring (thisLine, 0,1))= "[")
                                     then 
			                 (*Pretty.writeln(Pretty.str (thisLine))*)
                                             let val reconstr = thisLine
                                                 val thmstring = TextIO.inputLine instr 
                                                 val goalstring = TextIO.inputLine instr   
                                             in
                                                 (reconstr, thmstring, goalstring)
                                             end
                                     else if (String.isPrefix "SPASS beiseite:" thisLine ) 
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

                                         else if ((substring (thisLine, 0,5)) = "Proof") 
                                              then
  						(
						   let val reconstr = thisLine
                                                       val thmstring = TextIO.inputLine instr
                                                       val goalstring = TextIO.inputLine instr
						      val  outfile = TextIO.openOut(File.platform_path(File.tmp_path (Path.basic "foo_getSpass")));
                                    		val _ = TextIO.output (outfile, (thisLine))
                                     			 val _ =  TextIO.closeOut outfile
                                                   in
                                                      (reconstr, thmstring, goalstring)
                                                   end
						)
                                        else if ((substring (thisLine, 0,1)) = "%") 
                                              then
  						(
						   let val reconstr = thisLine
                                                       val thmstring = TextIO.inputLine instr
                                                       val goalstring = TextIO.inputLine instr
						      val  outfile = TextIO.openOut(File.platform_path(File.tmp_path (Path.basic "foo_getSpass")));
                                    		val _ = TextIO.output (outfile, (thisLine))
                                     			 val _ =  TextIO.closeOut outfile
                                                   in
                                                      (reconstr, thmstring, goalstring)
                                                   end
						)
                                        	 else
                                                     getSpassInput instr
                                            
 			        end
                          else 
                              ("No output from reconstruction process.\n","","")


end;
