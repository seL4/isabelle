
(****************************************************************)
(****** Slightly modified version of sml Unix structure *********)
(****************************************************************)

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
        pid : Posix.Process.pid,
        instr : TextIO.instream,   (*  Input stream to child process *)
        outstr : TextIO.outstream  (*  Output stream from child process *)
      };



fun killChild pid = Posix.Process.kill(Posix.Process.K_PROC pid, Posix.Signal.kill);

fun childInfo (PROC{pid,instr,outstr}) = ((pid, (instr,outstr)));

fun cmdstreamsOf (CMDPROC{instr,outstr,...}) = (instr, outstr);

fun cmdInStream (CMDPROC{instr,outstr,...}) = (instr);

fun cmdchildInfo (CMDPROC{prover,cmd,thmstring,goalstring,pid,instr,outstr}) = (prover,(cmd,(pid, (instr,outstr))));

fun cmdchildPid (CMDPROC{prover,cmd,thmstring,goalstring,pid,instr,outstr})  = (pid);

fun cmdProver (CMDPROC{prover,cmd,thmstring,goalstring,pid,instr,outstr})  = (prover);

fun cmdThm (CMDPROC{prover,cmd,thmstring,goalstring,pid,instr,outstr})  = (thmstring);

fun cmdGoal (CMDPROC{prover,cmd,thmstring,goalstring,pid,instr,outstr})  = (goalstring);
(***************************************************************************)
(*  Takes a command - e.g. 'vampire', a list of arguments for the command, *)
(*  and a list of currently running processes.  Creates a new process for  *)
(*  cmd and argv and adds it to procList                                   *)
(***************************************************************************)




fun mySshExecuteToList (cmd, argv, procList) = let
          val p1 = Posix.IO.pipe ()
          val p2 = Posix.IO.pipe ()
          val prover = hd argv
          val thmstring = hd(tl argv)
          val goalstring = hd(tl(tl argv))
          val argv = tl (tl argv)
          
          (* Turn the arguments into a single string.  Perhaps we should quote the
                   arguments.  *)
                fun convArgs [] = []
                  | convArgs [s] = [s]
                  | convArgs (hd::tl) = hd :: " " :: convArgs tl
                val cmd_args = concat(convArgs(cmd :: argv))

	  fun closep () = (
                Posix.IO.close (#outfd p1); 
                Posix.IO.close (#infd p1);
                Posix.IO.close (#outfd p2); 
                Posix.IO.close (#infd p2)
              )
          fun startChild () =(case  Posix.Process.fork()
		 of SOME pid =>  pid           (* parent *)
                  | NONE => let                 
		      val oldchildin = #infd p1
		      val newchildin = Posix.FileSys.wordToFD 0w0
		      val oldchildout = #outfd p2
		      val newchildout = Posix.FileSys.wordToFD 0w1
                      (*val args = (["shep"]@([cmd]@argv))
                      val newcmd = "/usr/bin/ssh"*)
                      
                      in
			Posix.IO.close (#outfd p1);
			Posix.IO.close (#infd p2);
			Posix.IO.dup2{old = oldchildin, new = newchildin};
                        Posix.IO.close oldchildin;
			Posix.IO.dup2{old = oldchildout, new = newchildout};
                        Posix.IO.close oldchildout;
                       (* Run the command. *)
                       (* Run this as a shell command.  The command and arguments have
                          to be a single argument. *)
                       Posix.Process.exec("/bin/sh", ["sh", "-c", cmd_args])
			(*Posix.Process.exec(newcmd, args)*)
		      end
		(* end case *))
          val _ = TextIO.flushOut TextIO.stdOut
          val pid = (startChild ()) handle ex => (closep(); raise ex)
	  val instr = openInFD ("_exec_in", #infd p2)
          val outstr = openOutFD ("_exec_out", #outfd p1)
          val cmd = hd (rev argv)
          in
              (* close the child-side fds *)
            Posix.IO.close (#outfd p2);
            Posix.IO.close (#infd p1);
              (* set the fds close on exec *)
            Posix.IO.setfd (#infd p2, Posix.IO.FD.flags [Posix.IO.FD.cloexec]);
            Posix.IO.setfd (#outfd p1, Posix.IO.FD.flags [Posix.IO.FD.cloexec]);
            (((CMDPROC{
              prover = prover,
              cmd = cmd,
              thmstring = thmstring,
              goalstring = goalstring,
              pid = pid,
              instr = instr,
              outstr = outstr
            })::procList))
          end;


fun myexecuteInEnv (cmd, argv, env) = let
          val p1 = Posix.IO.pipe ()
          val p2 = Posix.IO.pipe ()
          fun closep () = (
                Posix.IO.close (#outfd p1); 
                Posix.IO.close (#infd p1);
                Posix.IO.close (#outfd p2); 
                Posix.IO.close (#infd p2)
              )
          fun startChild () =(case  Posix.Process.fork()
                 of SOME pid =>  pid           (* parent *)
                  | NONE => let
                      val oldchildin = #infd p1
                      val newchildin = Posix.FileSys.wordToFD 0w0
                      val oldchildout = #outfd p2
                      val newchildout = Posix.FileSys.wordToFD 0w1
                      in
                        Posix.IO.close (#outfd p1);
                        Posix.IO.close (#infd p2);
                        Posix.IO.dup2{old = oldchildin, new = newchildin};
                        Posix.IO.close oldchildin;
                        Posix.IO.dup2{old = oldchildout, new = newchildout};
                        Posix.IO.close oldchildout;
                        Posix.Process.exece(cmd, argv, env)
                      end
                (* end case *))
          val _ = TextIO.flushOut TextIO.stdOut
          val pid = (startChild ()) handle ex => (closep(); raise ex)
          val instr = openInFD ("_exec_in", #infd p2)
          val outstr = openOutFD ("_exec_out", #outfd p1)
          in
              (* close the child-side fds *)
            Posix.IO.close (#outfd p2);
            Posix.IO.close (#infd p1);
              (* set the fds close on exec *)
            Posix.IO.setfd (#infd p2, Posix.IO.FD.flags [Posix.IO.FD.cloexec]);
            Posix.IO.setfd (#outfd p1, Posix.IO.FD.flags [Posix.IO.FD.cloexec]);
            PROC{pid = pid,
              instr = instr,
              outstr = outstr
            }
          end;




fun myexecuteToList (cmd, argv, procList) = let
          val p1 = Posix.IO.pipe ()
          val p2 = Posix.IO.pipe ()
          val prover = hd argv
          val thmstring = hd(tl argv)
          val goalstring = hd(tl(tl argv))
          val argv = tl (tl (tl(argv)))
          
	  fun closep () = (
                Posix.IO.close (#outfd p1); 
                Posix.IO.close (#infd p1);
                Posix.IO.close (#outfd p2); 
                Posix.IO.close (#infd p2)
              )
          fun startChild () =(case  Posix.Process.fork()
		 of SOME pid =>  pid           (* parent *)
                  | NONE => let
		      val oldchildin = #infd p1
		      val newchildin = Posix.FileSys.wordToFD 0w0
		      val oldchildout = #outfd p2
		      val newchildout = Posix.FileSys.wordToFD 0w1
                      in
			Posix.IO.close (#outfd p1);
			Posix.IO.close (#infd p2);
			Posix.IO.dup2{old = oldchildin, new = newchildin};
                        Posix.IO.close oldchildin;
			Posix.IO.dup2{old = oldchildout, new = newchildout};
                        Posix.IO.close oldchildout;
			Posix.Process.exec(cmd, argv)
		      end
		(* end case *))
          val _ = TextIO.flushOut TextIO.stdOut
          val pid = (startChild ()) handle ex => (closep(); raise ex)
	  val instr = openInFD ("_exec_in", #infd p2)
          val outstr = openOutFD ("_exec_out", #outfd p1)
          val cmd = hd (rev argv)
          in
              (* close the child-side fds *)
            Posix.IO.close (#outfd p2);
            Posix.IO.close (#infd p1);
              (* set the fds close on exec *)
            Posix.IO.setfd (#infd p2, Posix.IO.FD.flags [Posix.IO.FD.cloexec]);
            Posix.IO.setfd (#outfd p1, Posix.IO.FD.flags [Posix.IO.FD.cloexec]);
            (((CMDPROC{
              prover = prover,
              cmd = cmd,
              thmstring = thmstring,
              goalstring = goalstring,
              pid = pid,
              instr = instr,
              outstr = outstr
            })::procList))
          end;
