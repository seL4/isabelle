(*  Title:      Watcher.ML
    ID:         $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
 *)

 (***************************************************************************)
 (*  The watcher process starts a resolution process when it receives a     *)
(*  message from Isabelle                                                  *)
(*  Signals Isabelle, puts output of child into pipe to Isabelle,          *)
(*  and removes dead processes.  Also possible to kill all the resolution  *)
(*  processes currently running.                                           *)
(*  Hardwired version of where to pick up the tptp files for the moment    *)
(***************************************************************************)


signature WATCHER =
sig

(*****************************************************************************************)
(*  Send request to Watcher for multiple spasses to be called for filenames in arg       *)
(*  callResProvers (outstreamtoWatcher, prover name,prover-command, (settings,file) list             *)
(*****************************************************************************************)

val callResProvers :
    TextIO.outstream * (string*string*string*string*string*string*string*string) list 
    -> unit

(************************************************************************)
(* Send message to watcher to kill currently running resolution provers *)
(************************************************************************)

val callSlayer : TextIO.outstream -> unit

(**********************************************************)
(* Start a watcher and set up signal handlers             *)
(**********************************************************)

val createWatcher : thm*(ResClause.clause * thm) Array.array *  int -> TextIO.instream * TextIO.outstream * Posix.Process.pid

(**********************************************************)
(* Kill watcher process                                   *)
(**********************************************************)

val killWatcher : Posix.Process.pid -> unit

end




structure Watcher: WATCHER =
  struct

open ReconPrelim Recon_Transfer

val goals_being_watched = ref 0;

(*****************************************)
(*  The result of calling createWatcher  *)
(*****************************************)

datatype proc = PROC of {
        pid : Posix.Process.pid,
        instr : TextIO.instream,
        outstr : TextIO.outstream
      };

(*****************************************)
(*  The result of calling executeToList  *)
(*****************************************)

datatype cmdproc = CMDPROC of {
        prover: string,             (* Name of the resolution prover used, e.g. Vampire, SPASS *)
        cmd:  string,              (* The file containing the goal for res prover to prove *)     
        thmstring: string,         (* string representation of subgoal after negation, skolemization*) 
        goalstring: string,         (* string representation of subgoal*) 
        proc_handle : (TextIO.instream,TextIO.outstream) Unix.proc,
        instr : TextIO.instream,   (*  Input stream to child process *)
        outstr : TextIO.outstream  (*  Output stream from child process *)
      };

type signal = Posix.Signal.signal
datatype exit_status = datatype Posix.Process.exit_status

val fromStatus = Posix.Process.fromStatus


fun reap(pid, instr, outstr) =
        let
		val u = TextIO.closeIn instr;
	        val u = TextIO.closeOut outstr;
	
		val (_, status) =
			Posix.Process.waitpid(Posix.Process.W_CHILD pid, [])
	in
		status
	end

fun fdReader (name : string, fd : Posix.IO.file_desc) =
	  Posix.IO.mkTextReader {initBlkMode = true,name = name,fd = fd };

fun fdWriter (name, fd) =
          Posix.IO.mkTextWriter {
	      appendMode = false,
              initBlkMode = true,
              name = name,  
              chunkSize=4096,
              fd = fd
            };

fun openOutFD (name, fd) =
	  TextIO.mkOutstream (
	    TextIO.StreamIO.mkOutstream (
	      fdWriter (name, fd), IO.BLOCK_BUF));

fun openInFD (name, fd) =
	  TextIO.mkInstream (
	    TextIO.StreamIO.mkInstream (
	      fdReader (name, fd), ""));

fun killChild child_handle = Unix.reap child_handle 

fun childInfo (PROC{pid,instr,outstr }) = (pid,(instr,outstr));

fun cmdstreamsOf (CMDPROC{instr,outstr,...}) = (instr, outstr);

fun cmdInStream (CMDPROC{instr,outstr,...}) = (instr);

fun cmdchildInfo (CMDPROC{prover,cmd,thmstring,proc_handle,goalstring,instr,outstr}) = (prover,(cmd, (instr,outstr)));

fun cmdchildHandle (CMDPROC{prover,cmd,thmstring,goalstring,proc_handle,instr,outstr})  = proc_handle;

fun cmdProver (CMDPROC{prover,cmd,thmstring,goalstring,proc_handle,instr,outstr})  = (prover);

fun cmdThm (CMDPROC{prover,cmd,thmstring,goalstring,proc_handle,instr,outstr})  = (thmstring);

fun cmdGoal (CMDPROC{prover,cmd,thmstring,goalstring,proc_handle,instr,outstr})  = (goalstring);

fun sendOutput (outstr,str) = (TextIO.outputSubstr (outstr, (Substring.all str));TextIO.flushOut outstr);

(********************************************************************************************)
(*  takes a list of arguments and sends them individually to the watcher process by pipe    *)
(********************************************************************************************)

fun outputArgs (toWatcherStr, []) = ()
|   outputArgs (toWatcherStr, (x::xs)) = (TextIO.output (toWatcherStr, x); 
                                          TextIO.flushOut toWatcherStr;
                                         outputArgs (toWatcherStr, xs))

(********************************************************************************)
(*    gets individual args from instream and concatenates them into a list      *)
(********************************************************************************)

fun getArgs (fromParentStr, toParentStr,ys) =  let 
                                       val thisLine = TextIO.input fromParentStr
                                    in
                                        ((ys@[thisLine]))
                                    end

                            
(********************************************************************************)
(*  Send request to Watcher for a vampire to be called for filename in arg      *)
(********************************************************************************)
                    
fun callResProver (toWatcherStr,  arg) = 
      (sendOutput (toWatcherStr, arg^"\n"); 
       TextIO.flushOut toWatcherStr)

(*****************************************************************************************)
(*  Send request to Watcher for multiple provers to be called for filenames in arg       *)
(*  need to do the dfg stuff in the watcher, not here! send over the clasimp and stuff files too*)
(*****************************************************************************************)

    
(*Uses the $-character to separate items sent to watcher*)
fun callResProvers (toWatcherStr,  []) = 
      (sendOutput (toWatcherStr, "End of calls\n");  TextIO.flushOut toWatcherStr)
|   callResProvers (toWatcherStr,
                    (prover,thmstring,goalstring, proverCmd,settings, 
                     axfile, hypsfile,probfile)  ::  args) =
      let val _ = File.write (File.tmp_path (Path.basic "tog_comms"))
                             (prover^thmstring^goalstring^proverCmd^settings^
                              hypsfile^probfile)
      in sendOutput (toWatcherStr,    
            (prover^"$"^thmstring^"$"^goalstring^"$"^proverCmd^"$"^
             settings^"$"^hypsfile^"$"^probfile^"\n"));
         goals_being_watched := (!goals_being_watched) + 1;
	 TextIO.flushOut toWatcherStr;
	 callResProvers (toWatcherStr,args)
      end   
                                                
                                    
 
(**************************************************************)
(* Send message to watcher to kill currently running vampires *)
(**************************************************************)

fun callSlayer (toWatcherStr) = (sendOutput (toWatcherStr, "Kill vampires\n"); 
                            TextIO.flushOut toWatcherStr)



(**************************************************************)
(* Remove \n token from a vampire goal filename and extract   *)
(* prover, proverCmd, settings and file from input string     *)
(**************************************************************)

fun separateFields str =
  let val _ = File.append (File.tmp_path (Path.basic "sep_field"))
                          ("In separateFields, str is: " ^ str ^ "\n\n") 
      val [prover,thmstring,goalstring,proverCmd,settingstr,hypsfile,probfile] = 
          String.tokens (fn c => c = #"$") str
      val settings = String.tokens (fn c => c = #"%") settingstr
      val _ = File.append (File.tmp_path (Path.basic "sep_comms"))                                                                                
                  ("Sep comms are: "^ str ^"**"^
                   prover^" thmstring: "^thmstring^"\n goalstr:  "^goalstring^
                   " \n provercmd: "^proverCmd^
                   " \n hyps "^hypsfile^"\n prob  "^probfile^"\n\n")
  in
     (prover,thmstring,goalstring, proverCmd, settings, hypsfile, probfile)
  end

                      
fun formatCmd (prover,thmstring,goalstring, proverCmd, settings, hypsfile ,probfile) = 
  let
    val _ =  File.append (File.tmp_path (Path.basic"thmstring_in_watcher"))
	       (thmstring ^ "\n goals_watched" ^ 
	       (string_of_int(!goals_being_watched)) ^ probfile^"\n")
  in
    (prover, thmstring, goalstring, proverCmd, settings, probfile)	
  end;

val remove_newlines = String.translate (fn c => if c = #"\n" then "" else str c);

fun getCmd cmdStr = 
  let val cmdStr' = remove_newlines cmdStr
  in
      File.write (File.tmp_path (Path.basic"sepfields_call")) 
		 ("about to call sepfields with " ^ cmdStr');
      formatCmd (separateFields cmdStr')
  end;
                      

fun getProofCmd (a,b,c,d,e,f) = d

                        
(**************************************************************)
(* Get commands from Isabelle                                 *)
(**************************************************************)
(* FIX: or perhaps do the tptp2x stuff here - so it's get commands and then format them, before passing them to spass *)

fun getCmds (toParentStr,fromParentStr, cmdList) = 
  let val thisLine = TextIO.inputLine fromParentStr 
      val _ = File.append (File.tmp_path (Path.basic "parent_comms")) thisLine
  in
     if (thisLine = "End of calls\n") 
     then cmdList
     else if (thisLine = "Kill children\n") 
     then 
	 (   TextIO.output (toParentStr,thisLine ); 
	     TextIO.flushOut toParentStr;
	   (("","","","Kill children",[],"")::cmdList)
	  )
     else  let val thisCmd = getCmd (thisLine) 
	       (*********************************************************)
	       (* thisCmd = (prover,thmstring,proverCmd, settings, file)*)
	       (* i.e. put back into tuple format                       *)
	       (*********************************************************)
	   in
	     (*TextIO.output (toParentStr, thisCmd); 
	       TextIO.flushOut toParentStr;*)
	       getCmds (toParentStr,fromParentStr, (thisCmd::cmdList))
	   end
  end
	    
                                                                  
(**************************************************************)
(*  Get Io-descriptor for polling of an input stream          *)
(**************************************************************)

fun getInIoDesc someInstr = 
    let val (rd, buf) = TextIO.StreamIO.getReader(TextIO.getInstream someInstr)
        val _ = TextIO.output (TextIO.stdOut, buf)
        val ioDesc = 
	    case rd
	      of TextPrimIO.RD{ioDesc = SOME iod, ...} =>SOME iod
	       | _ => NONE
     in (* since getting the reader will have terminated the stream, we need
	 * to build a new stream. *)
	TextIO.setInstream(someInstr, TextIO.StreamIO.mkInstream(rd, buf));
	ioDesc
    end


(*************************************)
(*  Set up a Watcher Process         *)
(*************************************)

fun setupWatcher (thm,clause_arr, num_of_clauses) = 
  let
    (** pipes for communication between parent and watcher **)
    val p1 = Posix.IO.pipe ()
    val p2 = Posix.IO.pipe ()
    fun closep () = (
	  Posix.IO.close (#outfd p1); 
	  Posix.IO.close (#infd p1);
	  Posix.IO.close (#outfd p2); 
	  Posix.IO.close (#infd p2)
	)
    (***********************************************************)
    (****** fork a watcher process and get it set up and going *)
    (***********************************************************)
    fun startWatcher (procList) =
     (case  Posix.Process.fork() (***************************************)
      of SOME pid =>  pid           (* parent - i.e. main Isabelle process *)
				    (***************************************)

				      (*************************)
       | NONE => let                  (* child - i.e. watcher  *)
	   val oldchildin = #infd p1  (*************************)
	   val fromParent = Posix.FileSys.wordToFD 0w0
	   val oldchildout = #outfd p2
	   val toParent = Posix.FileSys.wordToFD 0w1
	   val fromParentIOD = Posix.FileSys.fdToIOD fromParent
	   val fromParentStr = openInFD ("_exec_in_parent", fromParent)
	   val toParentStr = openOutFD ("_exec_out_parent", toParent)
	   val sign = sign_of_thm thm
	   val prems = prems_of thm
	   val prems_string =  Meson.concat_with_and (map (Sign.string_of_term sign) prems) 
	   val _ = debug ("subgoals forked to startWatcher: "^prems_string);
	   fun killChildren [] = ()
	|      killChildren  (child_handle::children) =
	         (killChild child_handle; killChildren children)

	 (*************************************************************)
	 (* take an instream and poll its underlying reader for input *)
	 (*************************************************************)

	 fun pollParentInput () = 
	   let val pd = OS.IO.pollDesc (fromParentIOD)
	   in 
	     if isSome pd then 
		 let val pd' = OS.IO.pollIn (valOf pd)
		     val pdl = OS.IO.poll ([pd'], SOME (Time.fromMilliseconds 2000)) 
		     val _ = File.append (File.tmp_path (Path.basic "parent_poll")) 
		       ("In parent_poll\n")	
		 in
		    if null pdl 
		    then
		       NONE
		    else if (OS.IO.isIn (hd pdl)) 
			 then SOME (getCmds (toParentStr, fromParentStr, []))
			 else NONE
		 end
	       else NONE
	   end
		 
	  fun pollChildInput (fromStr) = 
	   let val _ = File.append (File.tmp_path (Path.basic "child_poll")) 
			 ("In child_poll\n")
	       val iod = getInIoDesc fromStr
	   in 
	     if isSome iod 
	     then 
	       let val pd = OS.IO.pollDesc (valOf iod)
	       in 
	       if isSome pd then 
		   let val pd' = OS.IO.pollIn (valOf pd)
		       val pdl = OS.IO.poll ([pd'], SOME (Time.fromMilliseconds 2000)) 
		   in
		      if null pdl 
		      then
			(File.append (File.tmp_path (Path.basic"child_poll_res")) "Null pdl\n"; 
			 NONE)
		      else if OS.IO.isIn (hd pdl)
		      then
			   let val inval =  (TextIO.inputLine fromStr)
			       val _ = File.append (File.tmp_path (Path.basic "child_poll_res")) (inval^"\n")
			   in SOME inval end
		      else
                        (File.append (File.tmp_path (Path.basic"child_poll_res")) "Null pdl \n";
                         NONE)
		   end
		 else NONE
		 end
	     else NONE
	end


	(****************************************************************************)
	(* Check all vampire processes currently running for output                 *)
	(****************************************************************************) 
						   (*********************************)
	 fun checkChildren ([], toParentStr) = []  (*** no children to check ********)
						   (*********************************)
	 |   checkChildren ((childProc::otherChildren), toParentStr) = 
	       let val _ = File.append (File.tmp_path (Path.basic "child_check")) 
			      ("In check child, length of queue:"^
			       (string_of_int (length (childProc::otherChildren)))^"\n")
		   val (childInput,childOutput) =  cmdstreamsOf childProc
		   val child_handle= cmdchildHandle childProc
		   (* childCmd is the .dfg file that the problem is in *)
		   val childCmd = fst(snd (cmdchildInfo childProc))
		   val _ = File.append (File.tmp_path (Path.basic "child_command")) 
			      (childCmd^"\n")
		   (* now get the number of the subgoal from the filename *)
		   val path_parts = String.tokens(fn c => c = #"/") childCmd
		   val digits = String.translate 
		                  (fn c => if Char.isDigit c then str c else "")
		                  (List.last path_parts);
		   val sg_num = (case Int.fromString digits of SOME n => n
                                  | NONE => error ("Watcher could not read subgoal nunber: " ^ childCmd));

		   val childIncoming = pollChildInput childInput
		   val _ = File.append (File.tmp_path (Path.basic "child_check_polled")) 
			      ("finished polling child \n")
		   val parentID = Posix.ProcEnv.getppid()
		   val prover = cmdProver childProc
		   val thmstring = cmdThm childProc
		   val sign = sign_of_thm thm
		   val prems = prems_of thm
		   val prems_string =  Meson.concat_with_and (map (Sign.string_of_term sign) prems) 
		   val _ = debug("subgoals forked to checkChildren: "^prems_string)
		   val goalstring = cmdGoal childProc							
		   val _ = File.append (File.tmp_path (Path.basic "child_comms")) 
			      (prover^thmstring^goalstring^childCmd^"\n")
	       in 
		 if isSome childIncoming
		 then 
		   (* check here for prover label on child*)
		   let val _ = File.write (File.tmp_path (Path.basic "child_incoming")) 
			      ("subgoals forked to checkChildren:"^
			      prems_string^prover^thmstring^goalstring^childCmd) 
		       val childDone = (case prover of
			   "vampire" => VampComm.checkVampProofFound(childInput, toParentStr, parentID,thmstring,goalstring, childCmd, thm, sg_num,clause_arr, num_of_clauses)  
			    | "E" => VampComm.checkEProofFound(childInput, toParentStr, parentID,thmstring,goalstring, childCmd, thm, sg_num,clause_arr, num_of_clauses)             
			  |"spass" => SpassComm.checkSpassProofFound(childInput, toParentStr, parentID,thmstring,goalstring, childCmd, thm, sg_num,clause_arr, num_of_clauses)  )
		    in
		     if childDone      (**********************************************)
		     then (* child has found a proof and transferred it *)
			(* Remove this child and go on to check others*)
			(**********************************************)
			(Unix.reap child_handle;
			 checkChildren(otherChildren, toParentStr))
		     else 
			(**********************************************)
			(* Keep this child and go on to check others  *)
			(**********************************************)
		       (childProc::(checkChildren (otherChildren, toParentStr)))
		  end
		else
		  (File.append (File.tmp_path (Path.basic "child_incoming")) "No child output ";
		   childProc::(checkChildren (otherChildren, toParentStr)))
	       end

	
     (********************************************************************)                  
     (* call resolution processes                                        *)
     (* settings should be a list of strings                             *)
     (* e.g. ["-t 300", "-m 100000"]         (TextIO.input instr)^                            *)
     (* takes list of (string, string, string list, string)list proclist *)
     (********************************************************************)


(*** add subgoal id num to this *)
	fun execCmds  [] procList = procList
	|   execCmds  ((prover, thmstring,goalstring,proverCmd,settings,file)::cmds) procList  =             let val _ = File.append (File.tmp_path (Path.basic "pre_exec_child"))  ("\nAbout to execute command for goal:\n"^goalstring^proverCmd^(concat settings)^file^" at "^(Date.toString(Date.fromTimeLocal(Time.now()))))
	  in 
	    if prover = "spass"
	    then 
	      let val childhandle:(TextIO.instream,TextIO.outstream) Unix.proc  = 
		       (Unix.execute(proverCmd, (["-FullRed=0"]@settings@[file])))
		  val (instr, outstr) = Unix.streamsOf childhandle
		  val newProcList =    (((CMDPROC{
				       prover = prover,
				       cmd = file,
				       thmstring = thmstring,
				       goalstring = goalstring,
				       proc_handle = childhandle,
				       instr = instr,
				       outstr = outstr })::procList))
		   val _ = File.append (File.tmp_path (Path.basic "exec_child"))  
			("\nexecuting command for goal:\n"^
			 goalstring^proverCmd^(concat settings)^file^
			 " at "^(Date.toString(Date.fromTimeLocal(Time.now()))))
	      in
		 Posix.Process.sleep (Time.fromSeconds 1);
		 execCmds cmds newProcList
	      end
	    else 
	      let val childhandle:(TextIO.instream,TextIO.outstream) Unix.proc  = 
		       (Unix.execute(proverCmd, (settings@[file])))
		  val (instr, outstr) = Unix.streamsOf childhandle
		  
		  val newProcList = (CMDPROC{
				       prover = prover,
				       cmd = file,
				       thmstring = thmstring,
				       goalstring = goalstring,
				       proc_handle = childhandle,
				       instr = instr,
				       outstr = outstr }) :: procList
     
		  val _ = File.append (File.tmp_path (Path.basic "exec_child")) 
			    ("executing command for goal:\n"^
			     goalstring^proverCmd^(concat settings)^file^
			     " at "^(Date.toString(Date.fromTimeLocal(Time.now()))))
	      in
		Posix.Process.sleep (Time.fromSeconds 1); 
		execCmds cmds newProcList
	      end
	   end


     (****************************************)                  
     (* call resolution processes remotely   *)
     (* settings should be a list of strings *)
     (* e.g. ["-t 300", "-m 100000"]         *)
     (****************************************)

      (*  fun execRemoteCmds  [] procList = procList
	|   execRemoteCmds ((prover, thmstring,goalstring,proverCmd ,settings,file)::cmds) procList  =  
				  let val  newProcList =  mySshExecuteToList ("/usr/bin/ssh",([prover,thmstring,goalstring,"-t", "shep"]@[proverCmd]@settings@[file]), procList)
				      in
					   execRemoteCmds  cmds newProcList
				      end
*)

	fun printList (outStr, []) = ()
	|   printList (outStr, (x::xs)) = (TextIO.output (outStr, x);TextIO.flushOut outStr; printList (outStr,xs))                  


     (**********************************************)                  
     (* Watcher Loop                               *)
     (**********************************************)
         val iterations_left = ref 1000;  (*200 seconds, 5 iterations per sec*)

	 fun keepWatching (toParentStr, fromParentStr,procList) = 
	   let fun loop (procList) =  
		let val _ = Posix.Process.sleep (Time.fromMilliseconds 200)
		    val cmdsFromIsa = pollParentInput ()
		    fun killchildHandler ()  = 
			  (TextIO.output(toParentStr, "Timeout: Killing proof processes!\n");
			   TextIO.flushOut toParentStr;
			   killChildren (map (cmdchildHandle) procList);
			   ())
		in 
		   (*Signal.signal (Posix.Signal.usr2, Signal.SIG_HANDLE killchildHandler);*)
		   iterations_left := !iterations_left - 1;
		   if !iterations_left = 0 then killchildHandler ()
		   else if isSome cmdsFromIsa
		   then (*  deal with input from Isabelle *)
		     if getProofCmd(hd(valOf cmdsFromIsa)) = "Kill children" 
		     then 
		       let val child_handles = map cmdchildHandle procList 
		       in
			  killChildren child_handles;
			  (*Posix.Process.kill(Posix.Process.K_PROC (Posix.ProcEnv.getppid()), Posix.Signal.usr2);*)    
			  loop []
		       end
		     else
		       if length procList < 5     (********************)
		       then                        (* Execute locally  *)
			 let 
			   val newProcList = execCmds (valOf cmdsFromIsa) procList
			   val parentID = Posix.ProcEnv.getppid()
			      val _ = (File.append (File.tmp_path (Path.basic "prekeep_watch")) "Just execed a child\n ")
			   val newProcList' =checkChildren (newProcList, toParentStr) 

			   val _ = debug("off to keep watching...")
			  val _ = (File.append (File.tmp_path (Path.basic "keep_watch")) "Off to keep watching...\n ")
			 in
			   loop newProcList'
			 end
		       else  (* Execute remotely              *)
			     (* (actually not remote for now )*)
			 let 
			   val newProcList = execCmds (valOf cmdsFromIsa) procList
			   val parentID = Posix.ProcEnv.getppid()
			   val newProcList' =checkChildren (newProcList, toParentStr) 
			 in
			   loop newProcList'
			 end
		   else (* No new input from Isabelle *)
		     let val newProcList = checkChildren ((procList), toParentStr)
		     in
		      (File.append (File.tmp_path (Path.basic "keep_watch")) "Off to keep watching.2..\n ");
		       loop newProcList
		     end
		 end
	   in  
	       loop procList
	   end
	   

	   in
	    (***************************)
	    (*** Sort out pipes ********)
	    (***************************)

	     Posix.IO.close (#outfd p1);
	     Posix.IO.close (#infd p2);
	     Posix.IO.dup2{old = oldchildin, new = fromParent};
	     Posix.IO.close oldchildin;
	     Posix.IO.dup2{old = oldchildout, new = toParent};
	     Posix.IO.close oldchildout;

	     (***************************)
	     (* start the watcher loop  *)
	     (***************************)
	     keepWatching (toParentStr, fromParentStr, procList);
	     (****************************************************************************)
(* fake return value - actually want the watcher to loop until killed *)
	     (****************************************************************************)
	     Posix.Process.wordToPid 0w0
	   end);
     (* end case *)


    val _ = TextIO.flushOut TextIO.stdOut

    (*******************************)
    (***  set watcher going ********)
    (*******************************)

    val procList = []
    val pid = startWatcher (procList)
    (**************************************************)
    (* communication streams to watcher               *)
    (**************************************************)

    val instr = openInFD ("_exec_in", #infd p2)
    val outstr = openOutFD ("_exec_out", #outfd p1)
    
    in
     (*******************************)
     (* close the child-side fds    *)
     (*******************************)
      Posix.IO.close (#outfd p2);
      Posix.IO.close (#infd p1);
      (* set the fds close on exec *)
      Posix.IO.setfd (#infd p2, Posix.IO.FD.flags [Posix.IO.FD.cloexec]);
      Posix.IO.setfd (#outfd p1, Posix.IO.FD.flags [Posix.IO.FD.cloexec]);
       
     (*******************************)
     (* return value                *)
     (*******************************)
      PROC{pid = pid,
	instr = instr,
	outstr = outstr
      }
   end;



(**********************************************************)
(* Start a watcher and set up signal handlers             *)
(**********************************************************)

fun killWatcher pid= Posix.Process.kill(Posix.Process.K_PROC pid, Posix.Signal.kill);

fun reapWatcher(pid, instr, outstr) =
  let val u = TextIO.closeIn instr;
      val u = TextIO.closeOut outstr;
      val (_, status) = Posix.Process.waitpid(Posix.Process.W_CHILD pid, [])
  in
	  status
  end


fun createWatcher (thm,clause_arr, num_of_clauses) =
 let val mychild = childInfo (setupWatcher(thm,clause_arr,  num_of_clauses))
     val streams = snd mychild
     val childin = fst streams
     val childout = snd streams
     val childpid = fst mychild
     val sign = sign_of_thm thm
     val prems = prems_of thm
     val prems_string =  Meson.concat_with_and (map (Sign.string_of_term sign) prems) 
     val _ = debug ("subgoals forked to createWatcher: "^prems_string);
(*FIXME: do we need an E proofHandler??*)
     fun vampire_proofHandler (n) =
	(Pretty.writeln(Pretty.str ( (concat[(oct_char "360"), (oct_char "377")])));
	 VampComm.getVampInput childin; Pretty.writeln(Pretty.str (oct_char "361")))               
     fun spass_proofHandler (n) = (
       let val _ = File.append (File.tmp_path (Path.basic "spass_signal_in"))
                               "Starting SPASS signal handler\n"
	   val (reconstr, goalstring, thmstring) = SpassComm.getSpassInput childin
	   val _ = File.append (File.tmp_path (Path.basic "spass_signal_out"))
		       ("In SPASS signal handler "^reconstr^thmstring^goalstring^
		       "goals_being_watched: "^ string_of_int (!goals_being_watched))
       in (* if a proof has been found and sent back as a reconstruction proof *)
	 if substring (reconstr, 0,1) = "["
	 then (Pretty.writeln(Pretty.str ( (concat[(oct_char "360"), (oct_char "377")])));
	       Recon_Transfer.apply_res_thm reconstr goalstring;
	       Pretty.writeln(Pretty.str  (oct_char "361"));
	       
	       goals_being_watched := (!goals_being_watched) - 1;
       
	       if !goals_being_watched = 0
	       then 
		  let val _ = File.write (File.tmp_path (Path.basic "reap_found"))
                                   ("Reaping a watcher, goals watched now "^
                                    string_of_int (!goals_being_watched)^"\n")
		   in
		       killWatcher childpid; reapWatcher (childpid,childin, childout); ()
		   end
		else () )
	 (* if there's no proof, but a message from Spass *)
	 else if substring (reconstr, 0,5) = "SPASS"
	 then (goals_being_watched := (!goals_being_watched) -1;
	       Pretty.writeln(Pretty.str ( (concat[(oct_char "360"), (oct_char "377")])));
	       Pretty.writeln(Pretty.str ((Recon_Transfer.restore_linebreaks goalstring)^reconstr));
	       Pretty.writeln(Pretty.str  (oct_char "361"));
	       if (!goals_being_watched = 0)
	       then (File.write (File.tmp_path (Path.basic "foo_reap_comp"))
	              ("Reaping a watcher, goals watched is: " ^
	                 (string_of_int (!goals_being_watched))^"\n");
	             killWatcher (childpid); reapWatcher (childpid,childin, childout); ())
		else () ) 
	(* print out a list of rules used from clasimpset*)
	 else if substring (reconstr, 0,5) = "Rules"
	 then (goals_being_watched := (!goals_being_watched) -1;
	       Pretty.writeln(Pretty.str ( (concat[(oct_char "360"), (oct_char "377")])));
	       Pretty.writeln(Pretty.str (goalstring^reconstr));
	       Pretty.writeln(Pretty.str  (oct_char "361"));
	       if (!goals_being_watched = 0)
	       then (File.write (File.tmp_path (Path.basic "foo_reap_comp"))
	              ("Reaping a watcher, goals watched is: " ^
	                 (string_of_int (!goals_being_watched))^"\n");
	             killWatcher (childpid);  reapWatcher (childpid,childin, childout);()
		     )
	       else () )
	  (* if proof translation failed *)
	 else if substring (reconstr, 0,5) = "Proof"
	 then (goals_being_watched := (!goals_being_watched) -1;
	       Pretty.writeln(Pretty.str ( (concat[(oct_char "360"), (oct_char "377")])));
	       Pretty.writeln(Pretty.str (goalstring^(Recon_Transfer.restore_linebreaks reconstr)));
	       Pretty.writeln(Pretty.str  (oct_char "361"));
	       if (!goals_being_watched = 0)
	       then (File.write (File.tmp_path (Path.basic "foo_reap_comp"))
	              ("Reaping a watcher, goals watched is: " ^
	                 (string_of_int (!goals_being_watched))^"\n");
	             killWatcher (childpid);  reapWatcher (childpid,childin, childout);()
		     )
	       else () )

	 else if substring (reconstr, 0,1) = "%"
	 then (goals_being_watched := (!goals_being_watched) -1;
	       Pretty.writeln(Pretty.str ( (concat[(oct_char "360"), (oct_char "377")])));
	       Pretty.writeln(Pretty.str (goalstring^(Recon_Transfer.restore_linebreaks reconstr)));
	       Pretty.writeln(Pretty.str  (oct_char "361"));
	       if (!goals_being_watched = 0)
	       then (File.write (File.tmp_path (Path.basic "foo_reap_comp"))
	              ("Reaping a watcher, goals watched is: " ^
	                 (string_of_int (!goals_being_watched))^"\n");
	             killWatcher (childpid);  reapWatcher (childpid,childin, childout);()
		     )
	       else () )

	 else  (* add something here ?*)
	      (goals_being_watched := (!goals_being_watched) -1;
	       Pretty.writeln(Pretty.str ( (concat[(oct_char "360"), (oct_char "377")])));
	       Pretty.writeln(Pretty.str ("Ran out of options in handler"));
	       Pretty.writeln(Pretty.str  (oct_char "361"));
	       if (!goals_being_watched = 0)
	       then (File.write (File.tmp_path (Path.basic "foo_reap_comp"))
		     ("Reaping a watcher, goals watched is: " ^
			(string_of_int (!goals_being_watched))^"\n");
		    killWatcher (childpid);  reapWatcher (childpid,childin, childout);()
		    )
	       else () )
       end)

 in IsaSignal.signal (IsaSignal.usr1, IsaSignal.SIG_HANDLE vampire_proofHandler);
    IsaSignal.signal (IsaSignal.usr2, IsaSignal.SIG_HANDLE spass_proofHandler);
    (childin, childout, childpid)

  end

end (* structure Watcher *)
