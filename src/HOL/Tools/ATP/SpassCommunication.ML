(*  Title:      SpassCommunication.ml
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

(***************************************************************************)
(*  Code to deal with the transfer of proofs from a Spass process          *)
(***************************************************************************)

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



fun transferSpassInput (fromChild, toParent, ppid,thmstring,goalstring, currentString) = let 
                         val thisLine = TextIO.inputLine fromChild 
			 in 
                            if (thisLine = "--------------------------SPASS-STOP------------------------------\n" )
			    then ( 
                                    let val proofextract = Recon_Parse.extract_proof (currentString^thisLine)
                                        val reconstr = Recon_Transfer.spassString_to_reconString (currentString^thisLine) thmstring
                                        val foo =   TextIO.openOut( File.sysify_path(File.tmp_path (Path.basic"foobar2")));
                               in
                                         TextIO.output(foo,(reconstr^thmstring));TextIO.closeOut foo;
                                   
                                         TextIO.output (toParent, reconstr^"\n");
                                         TextIO.flushOut toParent;
                                         TextIO.output (toParent, thmstring^"\n");
                                         TextIO.flushOut toParent;
                                         TextIO.output (toParent, goalstring^"\n");
                                         TextIO.flushOut toParent;
                                          
                                         Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
                                         (* Attempt to prevent several signals from turning up simultaneously *)
                                         OS.Process.sleep(Time.fromSeconds 1)
                                               
                                    end
                                      
                                  )
      			    else (
				
                                transferSpassInput (fromChild, toParent, ppid,thmstring, goalstring,(currentString^thisLine))
                                )
 			 end;



(*********************************************************************************)
(*  Inspect the output of a Spass   process to see if it has found a proof,      *)
(*  and if so, transfer output to the input pipe of the main Isabelle process    *)
(*********************************************************************************)

 
fun startSpassTransfer (fromChild, toParent, ppid, thmstring,goalstring,childCmd) = 
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
                                                 
                                                
                                                transferSpassInput (fromChild, toParent, ppid,thmstring, goalstring,thisLine);
                                                true)
                                             
                                             else 
                                                (
                                                 startSpassTransfer (fromChild, toParent, ppid, thmstring, goalstring,childCmd)
                                                )
                                            end
                                           )
                                         else (false)
                                     (*  end*)

fun checkSpassProofFound (fromChild, toParent, ppid,thmstring,goalstring, childCmd) = 
                                       let val spass_proof_file =  TextIO.openAppend(File.sysify_path(File.tmp_path (Path.basic "spass_proof")))
                                            val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "foo_checkspass")));                                                                            
                                            val _ = TextIO.output (outfile, "checking proof found")
                                             
                                            val _ =  TextIO.closeOut outfile
                                       in 
                                       if (isSome (TextIO.canInput(fromChild, 5)))
                                       then
                                       (
                                       let val thisLine = TextIO.inputLine fromChild  
                                           in if ( thisLine = "SPASS beiseite: Proof found.\n" )
                                              then      
                                              (  
                                                 let val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "foo_proof")));                                                                                (*val _ =  OS.Process.sleep(Time.fromSeconds 3 );*)
                                                     val _ = TextIO.output (outfile, (thisLine))
                                             
                                                     val _ =  TextIO.closeOut outfile
                                                 in 
                                                    startSpassTransfer (fromChild, toParent, ppid, thmstring,goalstring,childCmd) 
                                                 end
                                               )   
                                               else if (thisLine= "SPASS beiseite: Completion found.\n" )
                                                   then  

                                                 (
                                                      let    val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "foo_proof")));                                                                               (* val _ =  OS.Process.sleep(Time.fromSeconds 3 );*)
                                                             val _ = TextIO.output (outfile, (thisLine))
                                             
                                                             val _ =  TextIO.closeOut outfile
                                                      in
                                                       
                                                        (*TextIO.output (toParent,childCmd^"\n" );
                                                        TextIO.flushOut toParent;*)
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
                                                       OS.Process.sleep(Time.fromSeconds 1);
                                                        true  
                                                      end) 
                                                     else if ( thisLine = "SPASS beiseite: Ran out of time.\n" ) 
                                                          then  
                                                (
                                                        Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
                                                        TextIO.output (toParent,childCmd^"\n" );
                                                        TextIO.flushOut toParent;
                                                        TextIO.output (toParent, thisLine);
                                                        TextIO.flushOut toParent;

                                                        true) 
                                                          else if ( thisLine = "SPASS beiseite: Maximal number of loops exceeded.\n" )                                                             then
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
                                                       checkSpassProofFound  (fromChild, toParent, ppid, thmstring,goalstring,childCmd))

                                              end
                                          )
                                         else 
                                             (TextIO.output (spass_proof_file, ("No proof output seen \n"));TextIO.closeOut spass_proof_file;false)
                                      end

  
(***********************************************************************)
(*  Function used by the Isabelle process to read in a spass proof   *)
(***********************************************************************)


(***********************************************************************)
(*  Function used by the Isabelle process to read in a vampire proof   *)
(***********************************************************************)

(*fun getVampInput instr = let val thisLine = TextIO.inputLine instr 
			 in 
                           if (thisLine = "%==============  End of proof. ==================\n" )
			    then
                               (
                                (Pretty.writeln(Pretty.str  (concat["vampire",thisLine])));()
                               )
                             else if (thisLine = "% Unprovable.\n" ) 
                                  then 
                                     (
                                      (Pretty.writeln(Pretty.str (concat["vampire",thisLine])));()
                                      )
                                   else if (thisLine = "% Proof not found.\n")
                                        then 
                                            (
                                             Pretty.writeln(Pretty.str (concat["vampire", thisLine]));()
                                             )


                                         else 
                                            (
				              Pretty.writeln(Pretty.str (concat["vampire",thisLine])); getVampInput instr
                                             )
 			 end;

*)

fun getSpassInput instr = if (isSome (TextIO.canInput(instr, 2)))
                          then
                               let val thisLine = TextIO.inputLine instr 
                                   val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "foo_thisLine")));                                                                     val _ = TextIO.output (outfile, (thisLine))
                                             
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
                                     else if (thisLine = "SPASS beiseite: Completion found.\n" ) 
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
						      val  outfile = TextIO.openOut(File.sysify_path(File.tmp_path (Path.basic "foo_getSpass")));
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
                              ("No output from Spass.\n","","")


