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

(*  Send request to Watcher for multiple spasses to be called for filenames in arg       *)
(* callResProvers (outstreamtoWatcher, prover name,prover-command, (settings,file) list *)

val callResProvers :
    TextIO.outstream * (string*string*string*string*string) list 
    -> unit

(* Send message to watcher to kill currently running resolution provers *)
val callSlayer : TextIO.outstream -> unit

(* Start a watcher and set up signal handlers             *)
val createWatcher : 
    thm * (ResClause.clause * thm) Array.array -> 
    TextIO.instream * TextIO.outstream * Posix.Process.pid

(* Kill watcher process                                   *)
val killWatcher : Posix.Process.pid -> unit
val killWatcher' : int -> unit
end



structure Watcher: WATCHER =
struct

open Recon_Transfer

val goals_being_watched = ref 0;

val trace_path = Path.basic "watcher_trace";

fun trace s = if !Output.show_debug_msgs then File.append (File.tmp_path trace_path) s 
              else ();

(*  The result of calling createWatcher  *)
datatype proc = PROC of {
        pid : Posix.Process.pid,
        instr : TextIO.instream,
        outstr : TextIO.outstream
      };

(*  The result of calling executeToList  *)
datatype cmdproc = CMDPROC of {
        prover: string,       (* Name of the resolution prover used, e.g. Vampire*)
        cmd:  string,         (* The file containing the goal for res prover to prove *)     
        goalstring: string,   (* string representation of subgoal*) 
        proc_handle : (TextIO.instream,TextIO.outstream) Unix.proc,
        instr : TextIO.instream,   (*  Input stream to child process *)
        outstr : TextIO.outstream};  (*  Output stream from child process *)

type signal = Posix.Signal.signal
datatype exit_status = datatype Posix.Process.exit_status

val fromStatus = Posix.Process.fromStatus

fun reap(pid, instr, outstr) =
  let val u = TextIO.closeIn instr;
      val u = TextIO.closeOut outstr;
      val (_, status) = Posix.Process.waitpid(Posix.Process.W_CHILD pid, [])
  in status end

fun fdReader (name : string, fd : Posix.IO.file_desc) =
	  Posix.IO.mkTextReader {initBlkMode = true,name = name,fd = fd };

fun fdWriter (name, fd) =
          Posix.IO.mkTextWriter {
	      appendMode = false,
              initBlkMode = true,
              name = name,  
              chunkSize=4096,
              fd = fd};

fun openOutFD (name, fd) =
	  TextIO.mkOutstream (
	    TextIO.StreamIO.mkOutstream (
	      fdWriter (name, fd), IO.BLOCK_BUF));

fun openInFD (name, fd) =
	  TextIO.mkInstream (
	    TextIO.StreamIO.mkInstream (
	      fdReader (name, fd), ""));

fun childInfo (PROC{pid,instr,outstr }) = (pid,(instr,outstr));

fun cmdstreamsOf (CMDPROC{instr,outstr,...}) = (instr, outstr);

fun cmdInStream (CMDPROC{instr,outstr,...}) = instr;

fun cmdchildInfo (CMDPROC{prover,cmd,proc_handle,goalstring,instr,outstr}) = 
  (prover,(cmd, (instr,outstr)));

fun cmdchildHandle (CMDPROC{prover,cmd,goalstring,proc_handle,instr,outstr})  = 
  proc_handle;

fun cmdProver (CMDPROC{prover,cmd,goalstring,proc_handle,instr,outstr})  =
  prover;

fun cmdGoal (CMDPROC{prover,cmd,goalstring,proc_handle,instr,outstr})  =
  goalstring;


(*    gets individual args from instream and concatenates them into a list      *)
fun getArgs (fromParentStr, toParentStr, ys) =  
  let val thisLine = TextIO.input fromParentStr
  in ys@[thisLine] end

                            
(*  Send request to Watcher for a vampire to be called for filename in arg      *)
                   
fun callResProver (toWatcherStr,  arg) = 
      (TextIO.output (toWatcherStr, arg^"\n"); 
       TextIO.flushOut toWatcherStr)

(*****************************************************************************************)
(*  Send request to Watcher for multiple provers to be called for filenames in arg       *)
(*  need to do the dfg stuff in the watcher, not here! send over the clasimp and stuff files too*)
(*****************************************************************************************)

    
(*Uses the $-character to separate items sent to watcher*)
fun callResProvers (toWatcherStr,  []) = 
      (TextIO.output (toWatcherStr, "End of calls\n");  TextIO.flushOut toWatcherStr)
|   callResProvers (toWatcherStr,
                    (prover,goalstring, proverCmd,settings, 
                     probfile)  ::  args) =
      let val _ = trace (space_implode "\n" 
		         (["\ncallResProvers:",prover,goalstring,proverCmd,settings,
			  probfile]))
      in TextIO.output (toWatcherStr,    
            (prover^"$"^goalstring^"$"^proverCmd^"$"^
             settings^"$"^probfile^"\n"));
         goals_being_watched := (!goals_being_watched) + 1;
	 TextIO.flushOut toWatcherStr;
	 callResProvers (toWatcherStr,args)
      end   
                                                
                                    
 
(**************************************************************)
(* Send message to watcher to kill currently running vampires *)
(**************************************************************)

fun callSlayer toWatcherStr = (TextIO.output (toWatcherStr, "Kill vampires\n"); 
                            TextIO.flushOut toWatcherStr)


(**************************************************************)
(* Remove \n token from a vampire goal filename and extract   *)
(* prover, proverCmd, settings and file from input string     *)
(**************************************************************)

val remove_newlines = String.translate (fn c => if c = #"\n" then "" else str c);

fun getCmd cmdStr = 
  let val [prover,goalstring,proverCmd,settingstr,probfile] = 
            String.tokens (fn c => c = #"$") (remove_newlines cmdStr)
      val settings = String.tokens (fn c => c = #"%") settingstr
      val _ = trace ("getCmd: " ^ cmdStr ^
		    "\nprover" ^ prover ^ " goalstr:  "^goalstring^
		    "\nprovercmd: " ^ proverCmd^
		    "\nprob  " ^ probfile ^ "\n\n")
  in (prover,goalstring, proverCmd, settings, probfile) end
                      
(**************************************************************)
(* Get commands from Isabelle                                 *)
(**************************************************************)
fun getCmds (toParentStr,fromParentStr, cmdList) = 
  let val thisLine = TextIO.inputLine fromParentStr 
      val _ = trace("\nGot command from parent: " ^ thisLine)
  in
     if thisLine = "End of calls\n" orelse thisLine = "" then cmdList
     else if thisLine = "Kill children\n"
     then (TextIO.output (toParentStr,thisLine ); 
	   TextIO.flushOut toParentStr;
	   (("","","Kill children",[],"")::cmdList)  )
     else let val thisCmd = getCmd thisLine 
	   in getCmds (toParentStr, fromParentStr, thisCmd::cmdList) end
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

fun getProofCmd (a,c,d,e,f) = d

(* for tracing: encloses each string element in brackets. *)
val concat_with_and = space_implode " & " o map (enclose "(" ")");

fun prems_string_of th =
  concat_with_and (map (Sign.string_of_term (sign_of_thm th)) (prems_of th))

fun killChild proc = (Unix.kill(proc, Posix.Signal.kill); Unix.reap proc);

fun killChildren procs = List.app (ignore o killChild) procs;

 (*************************************************************)
 (* take an instream and poll its underlying reader for input *)
 (*************************************************************)
 
 fun pollParentInput (fromParentIOD, fromParentStr, toParentStr) = 
   case OS.IO.pollDesc fromParentIOD of
      SOME pd =>
	 (case OS.IO.poll ([OS.IO.pollIn pd], SOME (Time.fromSeconds 2)) of
	      [] => NONE
	    | pd''::_ => if OS.IO.isIn pd''
	 	         then SOME (getCmds (toParentStr, fromParentStr, []))
	 	         else NONE)
   | NONE => NONE;

(*get the number of the subgoal from the filename: the last digit string*)
fun number_from_filename s =
  case String.tokens (not o Char.isDigit) s of
      [] => (trace "\nWatcher could not read subgoal nunber!!"; raise ERROR)
    | numbers => valOf (Int.fromString (List.last numbers));

fun setupWatcher (thm,clause_arr) = 
  let
    (** pipes for communication between parent and watcher **)
    val p1 = Posix.IO.pipe ()
    val p2 = Posix.IO.pipe ()
    fun closep () = 
	 (Posix.IO.close (#outfd p1); 
	  Posix.IO.close (#infd p1);
	  Posix.IO.close (#outfd p2); 
	  Posix.IO.close (#infd p2))
    (***********************************************************)
    (****** fork a watcher process and get it set up and going *)
    (***********************************************************)
    fun startWatcher procList =
     (case  Posix.Process.fork() (***************************************)
      of SOME pid =>  pid           (* parent - i.e. main Isabelle process *)
				    (***************************************)

				      (*************************)
       | NONE => let                  (* child - i.e. watcher  *)
	  val oldchildin = #infd p1   (*************************)
	  val fromParent = Posix.FileSys.wordToFD 0w0
	  val oldchildout = #outfd p2
	  val toParent = Posix.FileSys.wordToFD 0w1
	  val fromParentIOD = Posix.FileSys.fdToIOD fromParent
	  val fromParentStr = openInFD ("_exec_in_parent", fromParent)
	  val toParentStr = openOutFD ("_exec_out_parent", toParent)
	  val _ = debug ("subgoals forked to startWatcher: "^ prems_string_of thm);
	 
	  fun pollChildInput fromStr = 
	     case getInIoDesc fromStr of
	       SOME iod => 
		 (case OS.IO.pollDesc iod of
		    SOME pd =>
			let val pd' = OS.IO.pollIn pd
			in
			  case OS.IO.poll ([pd'], SOME (Time.fromSeconds 2)) of
			      [] => false
			    | pd''::_ => OS.IO.isIn pd''
			end
		   | NONE => false)
	     | NONE => false


	  (* Check all ATP processes currently running for output                 *)
	  fun checkChildren ([], toParentStr) = []  (* no children to check *)
	  |   checkChildren (childProc::otherChildren, toParentStr) = 
	       let val _ = trace ("\nIn check child, length of queue:"^
			          Int.toString (length (childProc::otherChildren)))
		   val (childInput,childOutput) = cmdstreamsOf childProc
		   val child_handle = cmdchildHandle childProc
		   (* childCmd is the file that the problem is in *)
		   val childCmd = fst(snd (cmdchildInfo childProc))
		   val _ = trace ("\nchildCmd = " ^ childCmd)
		   val sg_num = number_from_filename childCmd
		   val childIncoming = pollChildInput childInput
		   val parentID = Posix.ProcEnv.getppid()
		   val prover = cmdProver childProc
		   val prems_string = prems_string_of thm
		   val goalstring = cmdGoal childProc							
	       in 
		 trace("\nsubgoals forked to checkChildren: " ^ goalstring);
		 if childIncoming
		 then 
		   (* check here for prover label on child*)
		   let val _ = trace ("\nInput available from child: " ^
				      childCmd ^ 
				      "\ngoalstring is " ^ goalstring ^ "\n\n")
		       val childDone = (case prover of
			   "vampire" => AtpCommunication.checkVampProofFound(childInput, toParentStr, parentID,goalstring, childCmd, clause_arr)  
			    | "E" => AtpCommunication.checkEProofFound(childInput, toParentStr, parentID,goalstring, childCmd, clause_arr)             
			  |"spass" => AtpCommunication.checkSpassProofFound(childInput, toParentStr, parentID,goalstring, childCmd, thm, sg_num,clause_arr)  )
		    in
		     if childDone
		     then (* child has found a proof and transferred it *)
			(* Remove this child and go on to check others*)
			(Unix.reap child_handle;
			 OS.FileSys.remove childCmd;
			 checkChildren(otherChildren, toParentStr))
		     else (* Keep this child and go on to check others  *)
		       childProc :: checkChildren (otherChildren, toParentStr)
		  end
		else (trace "\nNo child output";
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
	|   execCmds  ((prover, goalstring,proverCmd,settings,file)::cmds) procList  =
	      let val _ = trace 
	                    (space_implode "\n" 
	                      (["\nAbout to execute command for goal:",
	                        goalstring, proverCmd] @ settings @
	                       [file, Date.toString(Date.fromTimeLocal(Time.now()))]))
	          val childhandle:(TextIO.instream,TextIO.outstream) Unix.proc  = 
		       (Unix.execute(proverCmd, (settings@[file])))
		  val (instr, outstr) = Unix.streamsOf childhandle
		  val newProcList = (CMDPROC{
				       prover = prover,
				       cmd = file,
				       goalstring = goalstring,
				       proc_handle = childhandle,
				       instr = instr,
				       outstr = outstr }) :: procList
     
		  val _ = trace ("\nFinished at " ^
			         Date.toString(Date.fromTimeLocal(Time.now())))
	      in execCmds cmds newProcList end


     (****************************************)                  
     (* call resolution processes remotely   *)
     (* settings should be a list of strings *)
     (* e.g. ["-t300", "-m100000"]         *)
     (****************************************)

      (*  fun execRemoteCmds  [] procList = procList
	|   execRemoteCmds ((prover, goalstring,proverCmd ,settings,file)::cmds) procList  =  
	      let val  newProcList =  mySshExecuteToList ("/usr/bin/ssh",([prover,goalstring,"-t", "shep"]@[proverCmd]@settings@[file]), procList)
		  in
		       execRemoteCmds  cmds newProcList
		  end
*)

     (**********************************************)                  
     (* Watcher Loop                               *)
     (**********************************************)
         val iterations_left = ref 500;  (*don't let it run forever*)

	 fun keepWatching (procList) = 
	   let fun loop procList =  
		let val _ = trace ("\nCalling pollParentInput: " ^ 
			           Int.toString (!iterations_left));
		    val cmdsFromIsa = pollParentInput 
		                       (fromParentIOD, fromParentStr, toParentStr)
		in 
		   OS.Process.sleep (Time.fromMilliseconds 100);
		   iterations_left := !iterations_left - 1;
		   if !iterations_left <= 0 
		   then 
		    (trace "\nTimeout: Killing proof processes";
	             TextIO.output(toParentStr, "Timeout: Killing proof processes!\n");
		     TextIO.flushOut toParentStr;
		     killChildren (map cmdchildHandle procList);
		     exit 0)
		   else if isSome cmdsFromIsa
		   then (*  deal with input from Isabelle *)
		     if getProofCmd(hd(valOf cmdsFromIsa)) = "Kill children" 
		     then 
		       let val child_handles = map cmdchildHandle procList 
		       in
			  killChildren child_handles;
			  loop []
		       end
		     else
		       if length procList < 5     (********************)
		       then                        (* Execute locally  *)
			 let 
			   val newProcList = execCmds (valOf cmdsFromIsa) procList
			   val _ = Posix.ProcEnv.getppid()
			   val _ = trace "\nJust execed a child"
			   val newProcList' = checkChildren (newProcList, toParentStr) 
			 in
			   trace ("\nOff to keep watching: " ^ 
			          Int.toString (!iterations_left));
			   loop newProcList'
			 end
		       else  (* Execute remotely              *)
			     (* (actually not remote for now )*)
			 let 
			   val newProcList = execCmds (valOf cmdsFromIsa) procList
			   val _ = Posix.ProcEnv.getppid()
			   val newProcList' =checkChildren (newProcList, toParentStr) 
			 in
			   loop newProcList'
			 end
		   else (* No new input from Isabelle *)
		     let val newProcList = checkChildren (procList, toParentStr)
		     in
		       trace ("\nNo new input, still watching: " ^ 
			      Int.toString (!iterations_left));
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
	     keepWatching (procList);
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
    val pid = startWatcher procList
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
    PROC{pid = pid, instr = instr, outstr = outstr}
  end;



(**********************************************************)
(* Start a watcher and set up signal handlers             *)
(**********************************************************)

fun killWatcher pid = Posix.Process.kill(Posix.Process.K_PROC pid, Posix.Signal.kill);

val killWatcher' = killWatcher o ResLib.pidOfInt;

fun reapWatcher(pid, instr, outstr) =
  (TextIO.closeIn instr; TextIO.closeOut outstr;
   Posix.Process.waitpid(Posix.Process.W_CHILD pid, []); ())

fun createWatcher (thm, clause_arr) =
 let val (childpid,(childin,childout)) = childInfo (setupWatcher(thm,clause_arr))
     fun decr_watched() =
	  (goals_being_watched := !goals_being_watched - 1;
	   if !goals_being_watched = 0
	   then 
	     (debug ("\nReaping a watcher, childpid = "^
		     LargeWord.toString (Posix.Process.pidToWord childpid));
	      killWatcher childpid; reapWatcher (childpid,childin, childout))
	    else ())
     val _ = debug ("subgoals forked to createWatcher: "^ prems_string_of thm);
     fun proofHandler n = 
       let val outcome = TextIO.inputLine childin
	   val goalstring = TextIO.inputLine childin
	   val _ = debug ("In signal handler. outcome = \"" ^ outcome ^ 
		        "\"\ngoalstring = " ^ goalstring ^
		        "\ngoals_being_watched: "^  Int.toString (!goals_being_watched))
       in 
	 if String.isPrefix "[" outcome (*indicates a proof reconstruction*)
	 then (priority (Recon_Transfer.apply_res_thm outcome goalstring);
	       decr_watched())
	 else if String.isPrefix "Invalid" outcome
	 then (priority (goalstring ^ "is not provable");
	       decr_watched())
	 else if String.isPrefix "Failure" outcome
	 then (priority (goalstring ^ "proof attempt failed");
	       decr_watched()) 
	(* print out a list of rules used from clasimpset*)
	 else if String.isPrefix "Success" outcome
	 then (priority (goalstring^outcome);
	       decr_watched())
	  (* if proof translation failed *)
	 else if String.isPrefix "Translation failed" outcome
	 then (priority (goalstring ^ outcome);
	       decr_watched())
	 else (priority "System error in proof handler";
	       decr_watched())
       end
 in IsaSignal.signal (IsaSignal.usr2, IsaSignal.SIG_HANDLE proofHandler);
    (childin, childout, childpid)
  end

end (* structure Watcher *)
