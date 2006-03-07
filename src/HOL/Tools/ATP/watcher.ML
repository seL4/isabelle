(*  Title:      Watcher.ML
    ID:         $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
 *)

(*  The watcher process starts a resolution process when it receives a     *)
(*  message from Isabelle                                                  *)
(*  Signals Isabelle, puts output of child into pipe to Isabelle,          *)
(*  and removes dead processes.  Also possible to kill all the resolution  *)
(*  processes currently running.                                           *)

signature WATCHER =
sig

(*  Send request to Watcher for multiple spasses to be called for filenames in arg       *)
(* callResProvers (outstreamtoWatcher, prover name,prover-command, (settings,file) list *)

val callResProvers : TextIO.outstream * (string*string*string*string) list -> unit

(* Send message to watcher to kill resolution provers *)
val callSlayer : TextIO.outstream -> unit

(* Start a watcher and set up signal handlers             *)
val createWatcher : 
    thm * string Array.array -> 
    TextIO.instream * TextIO.outstream * Posix.Process.pid
val killWatcher : Posix.Process.pid -> unit
val setting_sep : char
end



structure Watcher: WATCHER =
struct

(*Field separators, used to pack items onto a text line*)
val command_sep = #"\t"
and setting_sep = #"%";

val goals_being_watched = ref 0;

val trace_path = Path.basic "watcher_trace";

fun trace s = if !Output.show_debug_msgs then File.append (File.tmp_path trace_path) s 
              else ();

(*Representation of a watcher process*)
type proc = {pid : Posix.Process.pid,
             instr : TextIO.instream,
             outstr : TextIO.outstream};

(*Representation of a child (ATP) process*)
type cmdproc = {
        prover: string,       (* Name of the resolution prover used, e.g. "spass"*)
        file:  string,        (* The file containing the goal for the ATP to prove *)     
        proc_handle : (TextIO.instream,TextIO.outstream) Unix.proc,
        instr : TextIO.instream,     (*Output of the child process *)
        outstr : TextIO.outstream};  (*Input to the child process *)


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

                            
(*  Send request to Watcher for a vampire to be called for filename in arg*)
fun callResProver (toWatcherStr,  arg) = 
      (TextIO.output (toWatcherStr, arg^"\n"); 
       TextIO.flushOut toWatcherStr)

(*  Send request to Watcher for multiple provers to be called*)
fun callResProvers (toWatcherStr,  []) = 
      (TextIO.output (toWatcherStr, "End of calls\n");  TextIO.flushOut toWatcherStr)
  | callResProvers (toWatcherStr,
                    (prover,proverCmd,settings,probfile)  ::  args) =
      (trace (space_implode ", " (["\ncallResProvers:", prover, proverCmd, probfile]));
       (*Uses a special character to separate items sent to watcher*)
       TextIO.output (toWatcherStr,
          space_implode (str command_sep) [prover, proverCmd, settings, probfile, "\n"]);
       goals_being_watched := (!goals_being_watched) + 1;
       TextIO.flushOut toWatcherStr;
       callResProvers (toWatcherStr,args))
                                                

(*Send message to watcher to kill currently running vampires. NOT USED and possibly
  buggy. Note that killWatcher kills the entire process group anyway.*)
fun callSlayer toWatcherStr = (TextIO.output (toWatcherStr, "Kill children\n"); 
                            TextIO.flushOut toWatcherStr)

                    
(* Get commands from Isabelle*)
fun getCmds (toParentStr, fromParentStr, cmdList) = 
  let val thisLine = TextIO.inputLine fromParentStr 
  in
     trace("\nGot command from parent: " ^ thisLine);
     if thisLine = "End of calls\n" orelse thisLine = "" then cmdList
     else if thisLine = "Kill children\n"
     then (TextIO.output (toParentStr,thisLine); 
	   TextIO.flushOut toParentStr;
	   [("","Kill children",[],"")])
     else
       let val [prover,proverCmd,settingstr,probfile,_] = 
                   String.tokens (fn c => c = command_sep) thisLine
           val settings = String.tokens (fn c => c = setting_sep) settingstr
       in
           trace ("\nprover: " ^ prover ^ "  prover path: " ^ proverCmd ^
                  "\n  problem file: " ^ probfile);
           getCmds (toParentStr, fromParentStr, 
                    (prover, proverCmd, settings, probfile)::cmdList) 
       end
       handle Bind => 
          (trace "\ngetCmds: command parsing failed!";
           getCmds (toParentStr, fromParentStr, cmdList))
  end
	    
                                                                  
(*Get Io-descriptor for polling of an input stream*)
fun getInIoDesc someInstr = 
    let val (rd, buf) = TextIO.StreamIO.getReader(TextIO.getInstream someInstr)
        val _ = TextIO.output (TextIO.stdOut, buf)
        val ioDesc = 
	    case rd
	      of TextPrimIO.RD{ioDesc = SOME iod, ...} => SOME iod
	       | _ => NONE
     in (* since getting the reader will have terminated the stream, we need
	 * to build a new stream. *)
	TextIO.setInstream(someInstr, TextIO.StreamIO.mkInstream(rd, buf));
	ioDesc
    end

fun pollChild fromStr = 
   case getInIoDesc fromStr of
     SOME iod => 
       (case OS.IO.pollDesc iod of
	  SOME pd =>
	      let val pd' = OS.IO.pollIn pd in
		case OS.IO.poll ([pd'], SOME (Time.fromSeconds 2)) of
		    [] => false
		  | pd''::_ => OS.IO.isIn pd''
	      end
	 | NONE => false)
   | NONE => false


(*************************************)
(*  Set up a Watcher Process         *)
(*************************************)

fun killChild proc = (Unix.kill(proc, Posix.Signal.kill); Unix.reap proc);

val killChildren = List.app (ignore o killChild o #proc_handle) : cmdproc list -> unit;

fun killWatcher (toParentStr, procList) =
      (trace "\nWatcher timeout: Killing proof processes";
       TextIO.output(toParentStr, "Timeout: Killing proof processes!\n");
       TextIO.flushOut toParentStr;
       killChildren procList;
       Posix.Process.exit 0w0);

(* take an instream and poll its underlying reader for input *)
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
      [] => (trace ("\nWatcher could not read subgoal nunber! " ^ s); 
             error "")
    | numbers => valOf (Int.fromString (List.last numbers));

(* call ATP.  Settings should be a list of strings  ["-t300", "-m100000"]*)
fun execCmds [] procList = procList
  | execCmds ((prover,proverCmd,settings,file)::cmds) procList  =
      let val _ = trace ("\nAbout to execute command: " ^ proverCmd ^ " " ^ file)
	  val childhandle:(TextIO.instream,TextIO.outstream) Unix.proc  = 
	       Unix.execute(proverCmd, settings@[file])
	  val (instr, outstr) = Unix.streamsOf childhandle
	  val newProcList = {prover=prover, file=file, proc_handle=childhandle,
			     instr=instr, outstr=outstr} :: procList
	  val _ = trace ("\nFinished at " ^
			 Date.toString(Date.fromTimeLocal(Time.now())))
      in execCmds cmds newProcList end

fun checkChildren (th, names_arr, toParentStr, children) = 
  let fun check [] = []  (* no children to check *)
	| check (child::children) = 
	   let val {prover, file, proc_handle, instr=childIn, ...} : cmdproc =
		   child
	       val _ = trace ("\nprobfile = " ^ file)
	       val sgno = number_from_filename file
	       val ppid = Posix.ProcEnv.getppid()
	   in 
	     if pollChild childIn
	     then (* check here for prover label on child*)
	       let val _ = trace ("\nInput available from child: " ^ file)
		   val childDone = (case prover of
		       "vampire" => AtpCommunication.checkVampProofFound
			    (childIn, toParentStr, ppid, file, names_arr)  
		     | "E" => AtpCommunication.checkEProofFound
			    (childIn, toParentStr, ppid, file, names_arr)             
		     | "spass" => AtpCommunication.checkSpassProofFound
			    (childIn, toParentStr, ppid, file, th, sgno,names_arr)  
		     | _ => (trace ("\nBad prover! " ^ prover); true) )
		in
		 if childDone (*child has found a proof and transferred it*)
		 then (Unix.reap proc_handle; OS.FileSys.remove file;
		       check children)
		 else child :: check children
	      end
	    else (trace "\nNo child output";  child :: check children)
	   end
  in 
    trace ("\nIn checkChildren, length of queue: " ^  Int.toString(length children));
    check children 
  end;


fun setupWatcher (th,names_arr) = 
  let
    val p1 = Posix.IO.pipe()   (*pipes for communication between parent and watcher*)
    val p2 = Posix.IO.pipe()
    (****** fork a watcher process and get it set up and going ******)
    fun startWatcher procList =
      case  Posix.Process.fork() of
         SOME pid => pid (* parent - i.e. main Isabelle process *)
       | NONE => 
          let            (* child - i.e. watcher  *)
	    val oldchildin = #infd p1  
	    val fromParent = Posix.FileSys.wordToFD 0w0
	    val oldchildout = #outfd p2
	    val toParent = Posix.FileSys.wordToFD 0w1
	    val fromParentIOD = Posix.FileSys.fdToIOD fromParent
	    val fromParentStr = openInFD ("_exec_in_parent", fromParent)
	    val toParentStr = openOutFD ("_exec_out_parent", toParent)
	    val pid = Posix.ProcEnv.getpid()
	    val () = Posix.ProcEnv.setpgid {pid = SOME pid, pgid = SOME pid}
		     (*set process group id: allows killing all children*)
	    val () = trace "\nsubgoals forked to startWatcher"
	    val limit = ref 200;  (*don't let watcher run forever*)
	    (*Watcher Loop : Check running ATP processes for output*)
	    fun keepWatching procList = 
	      (trace ("\npollParentInput. Limit = " ^ Int.toString (!limit) ^ 
				"  length(procList) = " ^ Int.toString(length procList));
	       OS.Process.sleep (Time.fromMilliseconds 100);  limit := !limit - 1;
	       if !limit < 0 then killWatcher (toParentStr, procList) 
	       else 
	       case pollParentInput(fromParentIOD, fromParentStr, toParentStr) of
		  SOME [(_,"Kill children",_,_)] => 
		    (trace "\nReceived Kill command"; 
		     killChildren procList; keepWatching [])
		| SOME cmds => (*  deal with commands from Isabelle process *)
		    if length procList < 40 then    (* Execute locally  *)                    
		      let val _ = trace("\nCommands from parent: " ^ 
					Int.toString(length cmds))
			  val newProcList' = checkChildren(th, names_arr, toParentStr, 
						execCmds cmds procList) 
		      in trace "\nCommands executed"; keepWatching newProcList' end
		    else  (* Execute remotely [FIXME: NOT REALLY]  *)
		      let val newProcList' = checkChildren (th, names_arr, toParentStr, 
						execCmds cmds procList) 
		      in keepWatching newProcList' end
		| NONE => (* No new input from Isabelle *)
		    (trace "\nNothing from parent...";  
		     keepWatching(checkChildren(th, names_arr, toParentStr, procList))))
	     handle exn => (*FIXME: exn handler is too general!*)
	       (trace ("\nkeepWatching exception handler: " ^ Toplevel.exn_message exn);
		keepWatching procList);
	  in
	    (*** Sort out pipes ********)
	    Posix.IO.close (#outfd p1);  Posix.IO.close (#infd p2);
	    Posix.IO.dup2{old = oldchildin, new = fromParent};
	    Posix.IO.close oldchildin;
	    Posix.IO.dup2{old = oldchildout, new = toParent};
	    Posix.IO.close oldchildout;
	    keepWatching (procList)
	  end; 

    val _ = TextIO.flushOut TextIO.stdOut
    val pid = startWatcher []
    (* communication streams to watcher*)
    val instr = openInFD ("_exec_in", #infd p2)
    val outstr = openOutFD ("_exec_out", #outfd p1)
  in
   (* close the child-side fds*)
    Posix.IO.close (#outfd p2);  Posix.IO.close (#infd p1);
    (* set the fds close on exec *)
    Posix.IO.setfd (#infd p2, Posix.IO.FD.flags [Posix.IO.FD.cloexec]);
    Posix.IO.setfd (#outfd p1, Posix.IO.FD.flags [Posix.IO.FD.cloexec]);
    {pid = pid, instr = instr, outstr = outstr}
  end;



(**********************************************************)
(* Start a watcher and set up signal handlers             *)
(**********************************************************)

fun reapAll s = (*Signal handler to tidy away dead processes*)
     (case Posix.Process.waitpid_nh(Posix.Process.W_ANY_CHILD, []) of
	  SOME _ => reapAll s | NONE => ()) 
     handle OS.SysErr _ => ()

(*FIXME: does the main process need something like this?
    IsaSignal.signal (IsaSignal.chld, IsaSignal.SIG_HANDLE reap)??*)

fun killWatcher pid = 
  (goals_being_watched := 0;
   Posix.Process.kill(Posix.Process.K_GROUP pid, Posix.Signal.kill);
   reapAll());

fun reapWatcher(pid, instr, outstr) = ignore
  (TextIO.closeIn instr; TextIO.closeOut outstr;
   Posix.Process.waitpid(Posix.Process.W_CHILD pid, []))
  handle OS.SysErr _ => ()

fun string_of_subgoal th i =
    string_of_cterm (List.nth(cprems_of th, i-1))
    handle Subscript => "Subgoal number out of range!"

fun prems_string_of th = space_implode "\n" (map string_of_cterm (cprems_of th))

fun createWatcher (th, names_arr) =
 let val {pid=childpid, instr=childin, outstr=childout} = setupWatcher (th,names_arr)
     fun decr_watched() =
	  (goals_being_watched := !goals_being_watched - 1;
	   if !goals_being_watched = 0
	   then 
	     (Output.debug ("\nReaping a watcher, childpid = " ^ string_of_pid childpid);
	      killWatcher childpid (*???; reapWatcher (childpid, childin, childout)*) )
	    else ())
     fun proofHandler _ = 
       let val _ = trace("\nIn signal handler for pid " ^ string_of_pid childpid)
           val outcome = TextIO.inputLine childin
	   val probfile = TextIO.inputLine childin
	   val sgno = number_from_filename probfile
	   val text = string_of_subgoal th sgno
	   fun report s = priority ("Subgoal " ^ Int.toString sgno ^ ": " ^ s);
       in 
	 Output.debug ("In signal handler. outcome = \"" ^ outcome ^ 
		       "\"\nprobfile = " ^ probfile ^
		       "\nGoals being watched: "^  Int.toString (!goals_being_watched));
	 if String.isPrefix "[" outcome (*indicates a proof reconstruction*)
	 then (priority (Recon_Transfer.apply_res_thm outcome);
	       decr_watched())
	 else if String.isPrefix "Invalid" outcome
	 then (report ("Subgoal is not provable:\n" ^ text);
	       decr_watched())
	 else if String.isPrefix "Failure" outcome
	 then (report ("Proof attempt failed:\n" ^ text);
	       decr_watched()) 
	(* print out a list of rules used from clasimpset*)
	 else if String.isPrefix "Success" outcome
	 then (report (outcome ^ text);
	       decr_watched())
	  (* if proof translation failed *)
	 else if String.isPrefix "Translation failed" outcome
	 then (report (outcome ^ text);
	       decr_watched())
	 else (report "System error in proof handler";
	       decr_watched())
       end
 in Output.debug ("subgoals forked to createWatcher: "^ prems_string_of th);
    IsaSignal.signal (IsaSignal.usr2, IsaSignal.SIG_HANDLE proofHandler);
    (childin, childout, childpid)
  end

end (* structure Watcher *)
