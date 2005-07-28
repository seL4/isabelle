(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

ATPs with TPTP format input.
*)

signature RES_ATP =
sig
  val call_atp: bool ref
  val axiom_file : Path.T
  val hyps_file : Path.T
  val prob_file : Path.T;
(*val atp_ax_tac : thm list -> int -> Tactical.tactic*)
(*val atp_tac : int -> Tactical.tactic*)
  val full_spass: bool ref
(*val spass: bool ref*)
  val vampire: bool ref
  val custom_spass: string list ref
end;

structure ResAtp: RES_ATP =
struct

val call_atp = ref false;

fun debug_tac tac = (debug "testing"; tac);

val full_spass = ref false;

(* use spass as default prover *)
(*val spass = ref true;*)

val custom_spass = ref ["Auto=0","-IORe","-IOFc","-RTaut","-RFSub","-RBSub","-DocProof","-TimeLimit=60"];
val vampire = ref false;

val skolem_tac = skolemize_tac;

val num_of_clauses = ref 0;
val clause_arr = Array.array (3500, ("empty", 0));


val atomize_tac =
    SUBGOAL
     (fn (prop,_) =>
         let val ts = Logic.strip_assums_hyp prop
         in EVERY1
                [METAHYPS
                     (fn hyps => (cut_facts_tac (map (ObjectLogic.atomize_thm o forall_intr_vars) hyps) 1)),
          REPEAT_DETERM_N (length ts) o (etac thin_rl)]
     end);

(* temporarily use these files, which will be loaded by Vampire *)
val file_id_num = ref 0;
fun new_prob_file () = "prob" ^ string_of_int (inc file_id_num);

val axiom_file = File.tmp_path (Path.basic "axioms");
val clasimp_file = File.tmp_path (Path.basic "clasimp");
val hyps_file = File.tmp_path (Path.basic "hyps");
val prob_file = File.tmp_path (Path.basic "prob");
val dummy_tac = all_tac;


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


(*FIXME: is function isar_atp_h used? If not, delete!*)
(*********************************************************************)
(* convert clauses from "assume" to conjecture. write to file "hyps" *)
(* hypotheses of the goal currently being proved                     *)
(*********************************************************************)
(*perhaps have 2 different versions of this, depending on whether or not SpassComm.spass is set *)
fun isar_atp_h thms =
    let val prems = map (skolemize o make_nnf o ObjectLogic.atomize_thm) thms
        val prems' = map repeat_someI_ex prems
        val prems'' = make_clauses prems'
        val prems''' = ResAxioms.rm_Eps [] prems''
        val clss = map ResClause.make_conjecture_clause prems'''
	val (tptp_clss,tfree_litss) = ListPair.unzip (map ResClause.clause2tptp clss) 
	val tfree_lits = ResLib.flat_noDup tfree_litss
        (* tfree clause is different in tptp and dfg versions *)
	val tfree_clss = map ResClause.tfree_clause tfree_lits 
        val hypsfile = File.platform_path hyps_file
        val out = TextIO.openOut(hypsfile)
    in
        ResLib.writeln_strs out (tfree_clss @ tptp_clss);
        TextIO.closeOut out; debug hypsfile;
        tfree_lits
    end;


(*********************************************************************)
(* write out a subgoal as tptp clauses to the file "probN"           *)
(* where N is the number of this subgoal                             *)
(*********************************************************************)

fun tptp_inputs_tfrees thms n tfrees =
    let
      val _ = debug ("in tptp_inputs_tfrees 0")
      val clss = map (ResClause.make_conjecture_clause_thm) thms
      val _ = debug ("in tptp_inputs_tfrees 1")
      val (tptp_clss,tfree_litss) = ListPair.unzip (map ResClause.clause2tptp clss)
      val _ = debug ("in tptp_inputs_tfrees 2")
      val tfree_clss = map ResClause.tfree_clause ((ResLib.flat_noDup tfree_litss) \\ tfrees)
      val _ = debug ("in tptp_inputs_tfrees 3")
      val probfile = File.platform_path prob_file ^ "_" ^ string_of_int n
      val out = TextIO.openOut(probfile)
    in
      ResLib.writeln_strs out (tfree_clss @ tptp_clss);
      TextIO.closeOut out;
      debug probfile
    end;


(*********************************************************************)
(* write out a subgoal as DFG clauses to the file "probN"           *)
(* where N is the number of this subgoal                             *)
(*********************************************************************)
(*
fun dfg_inputs_tfrees thms n tfrees = 
    let val _ = (debug ("in dfg_inputs_tfrees 0"))
        val clss = map (ResClause.make_conjecture_clause_thm) thms
         val _ = (debug ("in dfg_inputs_tfrees 1"))
	val (dfg_clss,tfree_litss) = ListPair.unzip (map ResClause.clause2dfg clss)
        val _ = (debug ("in dfg_inputs_tfrees 2"))
	val tfree_clss = map ResClause.tfree_clause ((ResLib.flat_noDup tfree_litss) \\ tfrees) 
         val _ = (debug ("in dfg_inputs_tfrees 3"))
        val probfile = (File.platform_path prob_file) ^ "_" ^ (string_of_int n)
	val out = TextIO.openOut(probfile)
    in
	(ResLib.writeln_strs out (tfree_clss @ dfg_clss); TextIO.closeOut out; debug probfile
    end;*)

(*********************************************************************)
(* call SPASS with settings and problem file for the current subgoal *)
(* should be modified to allow other provers to be called            *)
(*********************************************************************)
(* now passing in list of skolemized thms and list of sgterms to go with them *)
fun call_resolve_tac  (thms: thm list list)  sign (sg_terms:  term list) (childin, childout,pid) n  =
  let
    val axfile = (File.platform_path axiom_file)

    val hypsfile = (File.platform_path hyps_file)
    val clasimpfile = (File.platform_path clasimp_file)

    fun make_atp_list [] sign n = []
      | make_atp_list ((sko_thm, sg_term)::xs) sign n =
          let
            val thmstr = proofstring (Meson.concat_with_and (map string_of_thm sko_thm))
            val _ = debug ("thmstring in make_atp_lists is " ^ thmstr)

            val goalstring = proofstring (Sign.string_of_term sign sg_term)
            val _ = debug ("goalstring in make_atp_lists is " ^ goalstring)

            val probfile = File.platform_path prob_file ^ "_" ^ (string_of_int n)
            val _ = debug ("prob file in call_resolve_tac is " ^ probfile)
          in
            if !SpassComm.spass
            then
              let val optionline = (*Custom SPASS options, or default?*)
		      if !full_spass (*Auto mode: all SPASS inference rules*)
                      then "-DocProof%-TimeLimit=60%-SOS"
                      else "-" ^ space_implode "%-" (!custom_spass)
                  val _ = debug ("SPASS option string is " ^ optionline)
                  val _ = ResLib.helper_path "SPASS_HOME" "SPASS"
                    (*We've checked that SPASS is there for ATP/spassshell to run.*)
              in 
                  ([("spass", thmstr, goalstring,
                     getenv "ISABELLE_HOME" ^ "/src/HOL/Tools/ATP/spassshell",
                     optionline, clasimpfile, axfile, hypsfile, probfile)] @ 
                  (make_atp_list xs sign (n+1)))
              end
            else
              let val vampire = ResLib.helper_path "VAMPIRE_HOME" "vkernel"
              in
                ([("vampire", thmstr, goalstring, vampire, "-t 60%-m 100000",
                   clasimpfile, axfile, hypsfile, probfile)] @
                 (make_atp_list xs sign (n+1)))
              end
          end

    val atp_list = make_atp_list (ListPair.zip (thms, sg_terms)) sign 1
  in
    Watcher.callResProvers(childout,atp_list);
    debug "Sent commands to watcher!";
    dummy_tac
  end

(**********************************************************)
(* write out the current subgoal as a tptp file, probN,   *)
(* then call dummy_tac - should be call_res_tac           *)
(**********************************************************)

fun get_sko_thms tfrees sign sg_terms (childin, childout, pid) thm n sko_thms =
  if n = 0 then
    (call_resolve_tac (rev sko_thms)
      sign sg_terms (childin, childout, pid) (List.length sg_terms);
     dummy_tac thm)
  else
    SELECT_GOAL
      (EVERY1 [rtac ccontr, atomize_tac, skolemize_tac,
        METAHYPS (fn negs =>
          (tptp_inputs_tfrees (make_clauses negs) n tfrees;
           get_sko_thms tfrees sign sg_terms (childin, childout, pid) thm (n - 1)
             (negs::sko_thms); dummy_tac))]) n thm;


(**********************************************)
(* recursively call atp_tac_g on all subgoals *)
(* sg_term is the nth subgoal as a term - used*)
(* in proof reconstruction                    *)
(**********************************************)

fun isar_atp_goal' thm n tfree_lits (childin, childout, pid) =
  let
    val prems = Thm.prems_of thm
    (*val sg_term = get_nth k prems*)
    val sign = sign_of_thm thm
    val thmstring = string_of_thm thm
  in
    debug("in isar_atp_goal'");
    debug("thmstring in isar_atp_goal': " ^ thmstring);
    (* go and call callResProvers with this subgoal *)
    (* isar_atp_g tfree_lits  sg_term (childin, childout, pid) k thm; *)
    (* recursive call to pick up the remaining subgoals *)
    (* isar_atp_goal' thm (k+1) n tfree_lits  (childin, childout, pid) *)
    get_sko_thms tfree_lits sign prems (childin, childout, pid) thm n []
  end;


(**************************************************)
(* convert clauses from "assume" to conjecture.   *)
(* i.e. apply make_clauses and then get tptp for  *)
(* any hypotheses in the goal produced by assume  *)
(* statements;                                    *)
(* write to file "hyps"                           *)
(**************************************************)

fun isar_atp_aux thms thm n_subgoals  (childin, childout, pid) =
  let val tfree_lits = isar_atp_h thms
  in
    debug ("in isar_atp_aux");
    isar_atp_goal' thm n_subgoals tfree_lits (childin, childout, pid)
  end;

(******************************************************************)
(* called in Isar automatically                                   *)
(* writes out the current clasimpset to a tptp file               *)
(* passes all subgoals on to isar_atp_aux for further processing  *)
(* turns off xsymbol at start of function, restoring it at end    *)
(******************************************************************)
(*FIX changed to clasimp_file *)
val isar_atp' = setmp print_mode [] (fn (ctxt, thms, thm) =>
  if Thm.no_prems thm then ()
  else
    let
      val _= debug ("in isar_atp'")
      val thy = ProofContext.theory_of ctxt
      val prems = Thm.prems_of thm
      val thms_string = Meson.concat_with_and (map string_of_thm thms)
      val thm_string = string_of_thm thm
      val prems_string = Meson.concat_with_and (map (Sign.string_of_term thy) prems)

      (*set up variables for writing out the clasimps to a tptp file*)
      val (clause_arr, num_of_clauses) =
        ResClasimp.write_out_clasimp (File.platform_path clasimp_file) thy
          (hd prems) (*FIXME: hack!! need to do all prems*)
      val _ = debug ("clasimp_file is " ^ File.platform_path clasimp_file)
      val (childin, childout, pid) = Watcher.createWatcher (thm, clause_arr, num_of_clauses)
      val pid_string =
        string_of_int (Word.toInt (Word.fromLargeWord (Posix.Process.pidToWord pid)))
    in
      debug ("initial thms: " ^ thms_string);
      debug ("initial thm: " ^ thm_string);
      debug ("subgoals: " ^ prems_string);
      debug ("pid: "^ pid_string);
      isar_atp_aux thms thm (length prems) (childin, childout, pid);
      ()
    end);


fun get_thms_cs claset =
  let val {safeEs, safeIs, hazEs, hazIs, ...} = rep_cs claset
  in safeEs @ safeIs @ hazEs @ hazIs end;

fun append_name name [] _ = []
  | append_name name (thm :: thms) k =
      Thm.name_thm ((name ^ "_" ^ string_of_int k), thm) :: append_name name thms (k + 1);

fun append_names (name :: names) (thms :: thmss) =
  append_name name thms 0 :: append_names names thmss;

fun get_thms_ss [] = []
  | get_thms_ss thms =
      let
        val names = map Thm.name_of_thm thms
        val thms' = map (mksimps mksimps_pairs) thms
        val thms'' = append_names names thms'
      in
        ResLib.flat_noDup thms''
      end;


(* convert locally declared rules to axiom clauses *)
(* write axiom clauses to ax_file *)
(* what about clasimpset - it should already be in the ax file - perhaps append to ax file rather than just *)
(* write out ? Or keep as a separate file and then cat them all together in the watcher, like we do with the *)
(*claset file and prob file*)
(* FIX*)
(*fun isar_local_thms (delta_cs, delta_ss_thms) =
    let val thms_cs = get_thms_cs delta_cs
        val thms_ss = get_thms_ss delta_ss_thms
        val thms_clauses = ResLib.flat_noDup (map ResAxioms.clausify_axiom (thms_cs @ thms_ss))
        val clauses_strs = ResLib.flat_noDup (map ResClause.tptp_clause thms_clauses) (*string list*)
        val ax_file = File.platform_path axiom_file
        val out = TextIO.openOut ax_file
    in
        ResLib.writeln_strs out clauses_strs; 
        debug ("axiom file is "^ax_file));
        TextIO.closeOut out
    end;
*)


fun subtract_simpset thy ctxt =
  let
    val rules1 = #rules (#1 (rep_ss (simpset_of thy)));
    val rules2 = #rules (#1 (rep_ss (local_simpset_of ctxt)));
  in map #thm (Net.subtract MetaSimplifier.eq_rrule rules1 rules2) end;

fun subtract_claset thy ctxt =
  let
    val (netI1, netE1) = #xtra_netpair (rep_cs (claset_of thy));
    val (netI2, netE2) = #xtra_netpair (rep_cs (local_claset_of ctxt));
    val subtract = map (#2 o #2) oo Net.subtract Tactic.eq_kbrl;
  in subtract netI1 netI2 @ subtract netE1 netE2 end;



(** the Isar toplevel hook **)

val _ = Toplevel.print_state_hook (fn _ => fn state =>
  let
    val _ = if ! call_atp then () else raise Toplevel.UNDEF;
    val prf =
      (case Toplevel.node_of state of Toplevel.Proof prf => prf | _ => raise Toplevel.UNDEF);
    val _ = Proof.assert_backward (the (ProofHistory.previous prf));
    val proof = Proof.assert_forward (ProofHistory.current prf);
    val (ctxt, (_, goal)) = Proof.get_goal proof;

    val thy = ProofContext.theory_of ctxt;
    val prems_string = Meson.concat_with_and (map (Sign.string_of_term thy) (Thm.prems_of goal));

    (* FIXME presently unused *)
    val ss_thms = subtract_simpset thy ctxt;
    val cs_thms = subtract_claset thy ctxt;
  in
    debug ("initial thm in isar_atp: " ^ string_of_thm goal);
    debug ("subgoals in isar_atp: " ^ prems_string);
    debug ("number of subgoals in isar_atp: " ^ string_of_int (Thm.nprems_of goal));
    ResClause.init thy;
    isar_atp' (ctxt, ProofContext.prems_of ctxt, goal)
  end);

end;
