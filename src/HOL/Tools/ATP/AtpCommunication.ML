(*  Title:      VampCommunication.ml
    ID:         $Id$
    Author:     Claire Quigley
    Copyright   2004  University of Cambridge
*)

(***************************************************************************)
(*  Code to deal with the transfer of proofs from a Vampire process          *)
(***************************************************************************)
signature ATP_COMMUNICATION =
  sig
    val checkEProofFound: 
          TextIO.instream * TextIO.outstream * Posix.Process.pid * 
          string * thm * int * string Vector.vector -> bool
    val checkVampProofFound: 
          TextIO.instream * TextIO.outstream * Posix.Process.pid * 
          string * thm * int * string Vector.vector -> bool
    val checkSpassProofFound:  
          TextIO.instream * TextIO.outstream * Posix.Process.pid * 
          string * thm * int * string Vector.vector -> bool
    val signal_parent:  
          TextIO.outstream * Posix.Process.pid * string * string -> unit
  end;

structure AtpCommunication : ATP_COMMUNICATION =
struct

val trace_path = Path.basic "atp_trace";

fun trace s = if !Output.show_debug_msgs then File.append (File.tmp_path trace_path) s 
              else ();

exception EOF;

(**** retrieve the axioms that were used in the proof ****)

(*Get names of axioms used. Axioms are indexed from 1, while the vector is indexed from 0*)
fun get_axiom_names (thm_names: string vector) step_nums = 
    let fun is_axiom n = n <= Vector.length thm_names 
        fun index i = Vector.sub(thm_names, i-1)
        val axnums = List.filter is_axiom step_nums
        val axnames = sort_distinct string_ord (map index axnums)
    in
	if length axnums = length step_nums then "UNSOUND!!" :: axnames
	else axnames
    end

 (*String contains multiple lines. We want those of the form 
     "253[0:Inp] et cetera..."
  A list consisting of the first number in each line is returned. *)
fun get_spass_linenums proofstr = 
  let val toks = String.tokens (not o Char.isAlphaNum)
      fun inputno (ntok::"0"::"Inp"::_) = Int.fromString ntok
        | inputno _ = NONE
      val lines = String.tokens (fn c => c = #"\n") proofstr
  in  List.mapPartial (inputno o toks) lines  end

fun get_axiom_names_spass proofstr thm_names =
   get_axiom_names thm_names (get_spass_linenums proofstr);
    
fun not_comma c = c <>  #",";

(*A valid TSTP axiom line has the form  cnf(NNN,axiom,...) where NNN is a positive integer.*)
fun parse_tstp_line s =
  let val ss = Substring.full (unprefix "cnf(" (nospaces s))
      val (intf,rest) = Substring.splitl not_comma ss
      val (rolef,rest) = Substring.splitl not_comma (Substring.triml 1 rest)
      (*We only allow negated_conjecture because the line number will be removed in
        get_axiom_names above, while suppressing the UNSOUND warning*)
      val ints = if Substring.string rolef mem_string ["axiom","negated_conjecture"]
                 then Substring.string intf 
                 else "error" 
  in  Int.fromString ints  end
  handle Fail _ => NONE; 

fun get_axiom_names_tstp proofstr thm_names =
   get_axiom_names thm_names (List.mapPartial parse_tstp_line (split_lines proofstr));
    
 (*String contains multiple lines. We want those of the form 
     "*********** [448, input] ***********".
  A list consisting of the first number in each line is returned. *)
fun get_vamp_linenums proofstr = 
  let val toks = String.tokens (not o Char.isAlphaNum)
      fun inputno [ntok,"input"] = Int.fromString ntok
        | inputno _ = NONE
      val lines = String.tokens (fn c => c = #"\n") proofstr
  in  List.mapPartial (inputno o toks) lines  end

fun get_axiom_names_vamp proofstr thm_names =
   get_axiom_names thm_names (get_vamp_linenums proofstr);
    
fun rules_to_string [] = "NONE"
  | rules_to_string xs = space_implode "  " xs


(*The signal handler in watcher.ML must be able to read the output of this.*)
fun prover_lemma_list_aux getax proofstr probfile toParent ppid thm_names = 
 let val _ = trace
               ("\n\nGetting lemma names. proofstr is " ^ proofstr ^
                "\nprobfile is " ^ probfile ^
                "  num of clauses is " ^ string_of_int (Vector.length thm_names))
     val ax_str = rules_to_string (getax proofstr thm_names)
    in 
	 trace ("\nDone. Lemma list is " ^ ax_str);
         TextIO.output (toParent, "Success. Lemmas used in automatic proof: " ^
                  ax_str ^ "\n");
	 TextIO.output (toParent, probfile ^ "\n");
	 TextIO.flushOut toParent;
	 Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2)
    end
    handle exn => (*FIXME: exn handler is too general!*)
     (trace ("\nprover_lemma_list_aux: In exception handler: " ^ 
             Toplevel.exn_message exn);
      TextIO.output (toParent, "Translation failed for the proof: " ^ 
                     String.toString proofstr ^ "\n");
      TextIO.output (toParent, probfile);
      TextIO.flushOut toParent;
      Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2));

val e_lemma_list = prover_lemma_list_aux get_axiom_names_tstp;

val vamp_lemma_list = prover_lemma_list_aux get_axiom_names_vamp;

val spass_lemma_list = prover_lemma_list_aux get_axiom_names_spass;


(**** Extracting proofs from an ATP's output ****)

(*Return everything in s that comes before the string t*)
fun cut_before t s = 
  let val (s1,s2) = Substring.position t (Substring.full s)
  in  if Substring.size s2 = 0 then error "cut_before: string not found" 
      else Substring.string s2
  end;

val start_E = "# Proof object starts here."
val end_E   = "# Proof object ends here."
val start_V6 = "%================== Proof: ======================"
val end_V6   = "%==============  End of proof. =================="
val start_V8 = "=========== Refutation =========="
val end_V8 = "======= End of refutation ======="
val end_SPASS = "Formulae used in the proof"

(*********************************************************************************)
(*  Inspect the output of an ATP process to see if it has found a proof,     *)
(*  and if so, transfer output to the input pipe of the main Isabelle process    *)
(*********************************************************************************)

fun startTransfer (endS, fromChild, toParent, ppid, probfile, th, sgno, thm_names) =
 let fun transferInput currentString =
      let val thisLine = TextIO.inputLine fromChild
      in
	if thisLine = "" (*end of file?*)
	then (trace ("\n extraction_failed.  End bracket: " ^ endS ^
	             "\naccumulated text: " ^ currentString);
	      raise EOF)                    
	else if String.isPrefix endS thisLine
	then let val proofextract = currentString ^ cut_before endS thisLine
	         val lemma_list = if endS = end_V8 then vamp_lemma_list
			  	  else if endS = end_SPASS then spass_lemma_list
			  	  else e_lemma_list
	     in
	       trace ("\nExtracted proof:\n" ^ proofextract); 
	       lemma_list proofextract probfile toParent ppid thm_names
	     end
	else transferInput (currentString^thisLine)
      end
 in
     transferInput "";  true
 end handle EOF => false


(*The signal handler in watcher.ML must be able to read the output of this.*)
fun signal_parent (toParent, ppid, msg, probfile) =
 (TextIO.output (toParent, msg);
  TextIO.output (toParent, probfile ^ "\n");
  TextIO.flushOut toParent;
  trace ("\nSignalled parent: " ^ msg ^ probfile);
  Posix.Process.kill(Posix.Process.K_PROC ppid, Posix.Signal.usr2);
  (*Give the parent time to respond before possibly sending another signal*)
  OS.Process.sleep (Time.fromMilliseconds 600));

(*Called from watcher. Returns true if the Vampire process has returned a verdict.*)
fun checkVampProofFound (fromChild, toParent, ppid, probfile, th, sgno, thm_names) =
 let val thisLine = TextIO.inputLine fromChild
 in   
     trace thisLine;
     if thisLine = "" 
     then (trace "\nNo proof output seen"; false)
     else if String.isPrefix start_V8 thisLine
     then startTransfer (end_V8, fromChild, toParent, ppid, probfile, th, sgno, thm_names)
     else if (String.isPrefix "Satisfiability detected" thisLine) orelse
             (String.isPrefix "Refutation not found" thisLine)
     then (signal_parent (toParent, ppid, "Failure\n", probfile);
	   true)
     else checkVampProofFound  (fromChild, toParent, ppid, probfile, th, sgno, thm_names)
  end

(*Called from watcher. Returns true if the E process has returned a verdict.*)
fun checkEProofFound (fromChild, toParent, ppid, probfile, th, sgno, thm_names) = 
 let val thisLine = TextIO.inputLine fromChild  
 in   
     trace thisLine;
     if thisLine = "" then (trace "\nNo proof output seen"; false)
     else if String.isPrefix start_E thisLine
     then startTransfer (end_E, fromChild, toParent, ppid, probfile, th, sgno, thm_names)
     else if String.isPrefix "# Problem is satisfiable" thisLine
     then (signal_parent (toParent, ppid, "Invalid\n", probfile);
	   true)
     else if String.isPrefix "# Cannot determine problem status within resource limit" thisLine
     then (signal_parent (toParent, ppid, "Failure\n", probfile);
	   true)
     else checkEProofFound (fromChild, toParent, ppid, probfile, th, sgno, thm_names)
 end;

(*Called from watcher. Returns true if the SPASS process has returned a verdict.*)
fun checkSpassProofFound (fromChild, toParent, ppid, probfile, th, sgno, thm_names) = 
 let val thisLine = TextIO.inputLine fromChild  
 in    
     trace thisLine;
     if thisLine = "" then (trace "\nNo proof output seen"; false)
     else if String.isPrefix "Here is a proof" thisLine
     then      
        startTransfer (end_SPASS, fromChild, toParent, ppid, probfile, th, sgno, thm_names)
     else if thisLine = "SPASS beiseite: Completion found.\n"
     then (signal_parent (toParent, ppid, "Invalid\n", probfile);
	   true)
     else if thisLine = "SPASS beiseite: Ran out of time.\n" orelse
             thisLine = "SPASS beiseite: Maximal number of loops exceeded.\n"
     then (signal_parent (toParent, ppid, "Failure\n", probfile);
	   true)
    else checkSpassProofFound (fromChild, toParent, ppid, probfile, th, sgno, thm_names)
 end

end;
