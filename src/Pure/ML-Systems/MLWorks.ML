(*  Title:      Pure/MLWorks.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge

Compatibility file for MLWorks

Build Pure by typing to MLWorks (in directory Pure)
        use "ML-Systems/MLWorks.ML";
        use "ROOT.ML";
	collect_as_much_as_possible ();
	Shell.saveImage ("/anfs/bigdisc/lcp/heaps/mlworks/Pure", false);

Execute saved image by typing to the shell
	mlimage -load /anfs/bigdisc/lcp/heaps/mlworks/Pure
*)

(*** Poly/ML emulation ***)

(*Just for versions of MLWorks that don't provide the Option structure*)
structure Option = General;

(*To exit the system with an exit code -- an alternative to ^D *)
fun exit 0 = OS.Process.exit OS.Process.success
  | exit _ = OS.Process.exit OS.Process.failure;
fun quit () = exit 0;

(*To limit the printing depth [divided by 2 for comparibility with Poly/ML]*)
fun print_depth n = ();

(*Interface for toplevel pretty printers, see also Pure/install_pp.ML
  CURRENTLY UNAVAILABLE*)
fun make_pp path pprint = ();
fun install_pp _ = ();


(*** New Jersey ML parameters ***)

(*** Character/string functions which are compatible with 0.93 and Poly/ML ***)

fun ord s = Char.ord (String.sub(s,0));
val chr = str o Char.chr;
val explode = (map str) o String.explode;
val implode = String.concat;


(*** Timing functions ***)

(*A conditional timing function: applies f to () and, if the flag is true,
  prints its runtime. *)
fun cond_timeit flag f =
  if flag then
    let open Time  (*...for Time.toString, Time.+ and Time.- *)
	val CPUtimer = Timer.startCPUTimer();
        val {gc=gct1,sys=syst1,usr=usrt1} = Timer.checkCPUTimer(CPUtimer);
        val result = f();
        val {gc=gct2,sys=syst2,usr=usrt2} = Timer.checkCPUTimer(CPUtimer)
    in  print("User " ^ toString (usrt2-usrt1) ^
              "  GC " ^ toString (gct2-gct1) ^
              "  All "^ toString (syst2-syst1 + usrt2-usrt1 + gct2-gct1) ^
              " secs\n")
	  handle Time => ();
        result
    end
  else f();


(*** File handling ***)

(*Get time of last modification; if file doesn't exist return an empty string*)
fun file_info "" = ""
  | file_info name = Time.toString (OS.FileSys.modTime name) handle _ =>"";


(*** ML command execution ***)

val tmpName = OS.FileSys.tmpName();

(*Can one redirect 'use' directly to an instream?*)
fun use_strings slist =
  let val tmpFile = TextIO.openOut tmpName
  in app (fn s => TextIO.output (tmpFile, s)) slist;
     TextIO.closeOut tmpFile;
     use tmpName
  end;


(*** System command execution ***)

(*Execute an Unix command which doesn't take any input from stdin and
  sends its output to stdout.
  This could be done more easily by Unix.execute, but that function
  doesn't use the PATH.*)
fun execute command =
  let val is = (OS.Process.system (command ^ " > " ^ tmpName);
                TextIO.openIn tmpName);
      val result = TextIO.inputAll is;
  in TextIO.closeIn is;
     OS.FileSys.remove tmpName;
     result
  end;


(* getenv *)

local
  fun drop_last [] = []
    | drop_last [x] = []
    | drop_last (x :: xs) = x :: drop_last xs;

  val drop_last_char = implode o drop_last o explode;
in
  fun getenv var = drop_last_char
    (execute ("env | grep '^" ^ var ^ "=' | sed -e 's/" ^ var ^ "=//'"));
end;


(*Non-printing and 8-bit chars are forbidden in string constants*)
val needs_filtered_use = true;

