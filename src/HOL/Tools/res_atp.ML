(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

ATPs with TPTP format input.
*)

signature RES_ATP =
sig
  val prover: string ref
  val custom_spass: string list ref
  val destdir: string ref
  val hook_count: int ref
  val problem_name: string ref
end;

structure ResAtp: RES_ATP =
struct

val call_atp = ref false;
val hook_count = ref 0;

val prover = ref "E";   (* use E as the default prover *)
val custom_spass =   (*specialized options for SPASS*)
      ref ["Auto=0","-FullRed=0","-IORe","-IOFc","-RTaut","-RFSub","-RBSub",
           "-DocProof","-TimeLimit=60"];

val destdir = ref "";   (*Empty means write files to /tmp*)
val problem_name = ref "prob";

fun prob_pathname() = 
  if !destdir = "" then File.platform_path (File.tmp_path (Path.basic (!problem_name)))
  else if File.exists (File.unpack_platform_path (!destdir))
  then !destdir ^ "/" ^ !problem_name
  else error ("No such directory: " ^ !destdir);


(**** for Isabelle/ML interface  ****)

(*Remove unwanted characters such as ? and newline from the textural 
  representation of a theorem (surely they don't need to be produced in 
  the first place?) *)

fun is_proof_char ch = (#" " <= ch andalso ch <= #"~" andalso ch <> #"?");

val proofstring =
    String.translate (fn c => if is_proof_char c then str c else "");


(**** For running in Isar ****)

(* same function as that in res_axioms.ML *)
fun repeat_RS thm1 thm2 =
    let val thm1' =  thm1 RS thm2 handle THM _ => thm1
    in
        if eq_thm(thm1,thm1') then thm1' else (repeat_RS thm1' thm2)
    end;

(* a special version of repeat_RS *)
fun repeat_someI_ex thm = repeat_RS thm someI_ex;


(* write out a subgoal as tptp clauses to the file "xxxx_N"*)
fun tptp_inputs_tfrees thms n axclauses =
    let
      val _ = debug ("in tptp_inputs_tfrees 0")
      val clss = map (ResClause.make_conjecture_clause_thm) thms
      val _ = debug ("in tptp_inputs_tfrees 1")
      val (tptp_clss,tfree_litss) = ListPair.unzip (map ResClause.clause2tptp clss)
      val _ = debug ("in tptp_inputs_tfrees 2")
      val tfree_clss = map ResClause.tfree_clause (ResLib.flat_noDup tfree_litss)
      val _ = debug ("in tptp_inputs_tfrees 3")
      val probfile = prob_pathname() ^ "_" ^ string_of_int n
      val out = TextIO.openOut(probfile)
    in
      ResLib.writeln_strs out (List.concat (map ResClause.tptp_clause axclauses));
      ResLib.writeln_strs out (tfree_clss @ tptp_clss);
      TextIO.closeOut out;
      debug probfile
    end;

(* write out a subgoal in DFG format to the file "xxxx_N"*)
fun dfg_inputs_tfrees thms n axclauses = 
    let val clss = map (ResClause.make_conjecture_clause_thm) thms
        val probfile = prob_pathname() ^ "_" ^ (string_of_int n)
        val _ = debug ("about to write out dfg prob file " ^ probfile)
        val probN = ResClause.clauses2dfg clss (!problem_name ^ "_" ^ string_of_int n)
                        axclauses [] [] []    
	val out = TextIO.openOut(probfile)
    in
	(ResLib.writeln_strs out [probN]; TextIO.closeOut out; debug probfile )
    end;


(*********************************************************************)
(* call prover with settings and problem file for the current subgoal *)
(*********************************************************************)
(* now passing in list of skolemized thms and list of sgterms to go with them *)
fun watcher_call_provers sign sg_terms (childin, childout,pid) =
  let
    fun make_atp_list [] n = []
      | make_atp_list ((sg_term)::xs) n =
          let
            val goalstring = proofstring (Sign.string_of_term sign sg_term)
            val _ = debug ("goalstring in make_atp_lists is " ^ goalstring)

            val probfile = prob_pathname() ^ "_" ^ string_of_int n
            val _ = debug ("problem file in watcher_call_provers is " ^ probfile)
          in
            (*Avoid command arguments containing spaces: Poly/ML and SML/NJ
              versions of Unix.execute treat them differently!*)
            if !prover = "spass"
            then
              let val optionline = 
		      if !AtpCommunication.reconstruct 
		          (*Proof reconstruction works for only a limited set of 
		            inference rules*)
                      then "-" ^ space_implode "%-" (!custom_spass)
                      else "-DocProof%-TimeLimit=60%-SOS%-FullRed=0" (*Auto mode*)
                  val _ = debug ("SPASS option string is " ^ optionline)
                  val _ = ResLib.helper_path "SPASS_HOME" "SPASS"
                    (*We've checked that SPASS is there for ATP/spassshell to run.*)
              in 
                  ([("spass", goalstring,
                     getenv "ISABELLE_HOME" ^ "/src/HOL/Tools/ATP/spassshell",
                     optionline, probfile)] @ 
                  (make_atp_list xs (n+1)))
              end
            else if !prover = "vampire"
	    then 
              let val vampire = ResLib.helper_path "VAMPIRE_HOME" "vampire"
              in
                ([("vampire", goalstring, vampire, "-t 60%-m 100000", probfile)] @
                 (make_atp_list xs (n+1)))       (*BEWARE! spaces in options!*)
              end
      	     else if !prover = "E"
      	     then
	       let val Eprover = ResLib.helper_path "E_HOME" "eproof"
	       in
		  ([("E", goalstring, Eprover, 
		     "--tptp-in%-l5%-xAuto%-tAuto%--soft-cpu-limit=60",
		     probfile)] @
		   (make_atp_list xs (n+1)))
	       end
	     else error ("Invalid prover name: " ^ !prover)
          end

    val atp_list = make_atp_list sg_terms 1
  in
    Watcher.callResProvers(childout,atp_list);
    debug "Sent commands to watcher!"
  end

(*We write out problem files for each subgoal, but work is repeated (skolemize)*)
fun write_problem_files axclauses thm n =
    if n=0 then ()
     else
       (SELECT_GOAL
        (EVERY1 [rtac ccontr, ResLib.atomize_tac, skolemize_tac, 
          METAHYPS(fn negs => 
            (if !prover = "spass" 
             then dfg_inputs_tfrees (make_clauses negs) n axclauses
             else tptp_inputs_tfrees (make_clauses negs) n axclauses;
             write_problem_files axclauses thm (n-1); 
             all_tac))]) n thm;
        ());

val last_watcher_pid = ref (NONE : Posix.Process.pid option);

(******************************************************************)
(* called in Isar automatically                                   *)
(* writes out the current clasimpset to a tptp file               *)
(* turns off xsymbol at start of function, restoring it at end    *)
(******************************************************************)
(*FIX changed to clasimp_file *)
val isar_atp = setmp print_mode [] 
 (fn (ctxt, thm) =>
  if Thm.no_prems thm then ()
  else
    let
      val _= debug ("in isar_atp")
      val thy = ProofContext.theory_of ctxt
      val prems = Thm.prems_of thm
      val prems_string = Meson.concat_with_and (map (Sign.string_of_term thy) prems)

      val _ = (case !last_watcher_pid of NONE => ()
               | SOME pid => (*FIXME: should kill ATP processes too; at least they time out*)
                  (debug ("Killing old watcher, pid = " ^ 
                          Int.toString (ResLib.intOfPid pid));
                   Watcher.killWatcher pid))
              handle OS.SysErr _ => debug "Attempt to kill watcher failed";
      (*set up variables for writing out the clasimps to a tptp file*)
      val (clause_arr, axclauses) = ResClasimp.get_clasimp_lemmas ctxt (hd prems) 
              (*FIXME: hack!! need to consider relevance for all prems*)
      val _ = debug ("claset and simprules total clauses = " ^ 
                     string_of_int (Array.length clause_arr))
      val (childin, childout, pid) = Watcher.createWatcher (thm, clause_arr)
    in
      last_watcher_pid := SOME pid;
      debug ("subgoals: " ^ prems_string);
      debug ("pid: " ^ Int.toString (ResLib.intOfPid pid));
      write_problem_files axclauses thm (length prems);
      watcher_call_provers (sign_of_thm thm) (Thm.prems_of thm) (childin, childout, pid)
    end);

val isar_atp_writeonly = setmp print_mode [] 
 (fn (ctxt, thm) =>
  if Thm.no_prems thm then ()
  else
    let val prems = Thm.prems_of thm
        val (_, axclauses) = ResClasimp.get_clasimp_lemmas ctxt (hd prems) 
    in
      write_problem_files axclauses thm (length prems)
    end);


(** the Isar toplevel hook **)

val invoke_atp = Toplevel.unknown_proof o Toplevel.keep (fn state =>
  let
    val proof = Toplevel.proof_of state
    val (ctxt, (_, goal)) = Proof.get_goal proof
        handle Proof.STATE _ => error "No goal present";
    val thy = ProofContext.theory_of ctxt;
  in
    debug ("initial thm in isar_atp: " ^ 
           Pretty.string_of (ProofContext.pretty_thm ctxt goal));
    debug ("subgoals in isar_atp: " ^ 
           Pretty.string_of (ProofContext.pretty_term ctxt
             (Logic.mk_conjunction_list (Thm.prems_of goal))));
    debug ("number of subgoals in isar_atp: " ^ string_of_int (Thm.nprems_of goal));
    debug ("current theory: " ^ Context.theory_name thy);
    hook_count := !hook_count +1;
    debug ("in hook for time: " ^(string_of_int (!hook_count)) );
    ResClause.init thy;
    if !destdir = "" then isar_atp (ctxt, goal)
    else isar_atp_writeonly (ctxt, goal)
  end);

val call_atpP =
  OuterSyntax.improper_command 
    "ProofGeneral.call_atp" 
    "call automatic theorem provers" 
    OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o invoke_atp));

val _ = OuterSyntax.add_parsers [call_atpP];

end;
