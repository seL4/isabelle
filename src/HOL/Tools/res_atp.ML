(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

ATPs with TPTP format input.
*)

(*Jia: changed: isar_atp now processes entire proof context.  fetch thms from delta simpset/claset*)

signature RES_ATP = 
sig

val trace_res : bool ref
val axiom_file : Path.T
val hyps_file : Path.T
val isar_atp : ProofContext.context * Thm.thm -> unit
val prob_file : Path.T
val atp_ax_tac : Thm.thm list -> int -> Tactical.tactic
val atp_tac : int -> Tactical.tactic
val debug: bool ref

end;

structure ResAtp : RES_ATP =

struct

(* used for debug *)
val debug = ref false;

fun debug_tac tac = (warning "testing";tac);
(* default value is false *)

val trace_res = ref false;

val skolem_tac = skolemize_tac;


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
val prob_file = File.tmp_path (Path.basic "prob");
val axiom_file = File.tmp_path (Path.basic "axioms");
val hyps_file = File.tmp_path (Path.basic "hyps");
val dummy_tac = PRIMITIVE(fn thm => thm );



fun tptp_inputs thms n = 
    let val clss = map (ResClause.make_conjecture_clause_thm) thms
	val tptp_clss = ResLib.flat_noDup(map ResClause.tptp_clause clss) 
        val probfile = (File.sysify_path prob_file) ^ "_" ^ (string_of_int n)
	val out = TextIO.openOut(probfile)
    in
	(ResLib.writeln_strs out tptp_clss; TextIO.closeOut out; (if !trace_res then (warning probfile) else ()))
    end;


(**** for Isabelle/ML interface  ****)

fun call_atp_tac thms n = (tptp_inputs thms n; dummy_tac);




fun atp_tac n = SELECT_GOAL
  (EVERY1 [rtac ccontr,atomize_tac, skolemize_tac, 
  METAHYPS(fn negs => (call_atp_tac (make_clauses negs) n))]) n;


fun atp_ax_tac axioms n = 
    let val axcls = ResLib.flat_noDup(map ResAxioms.clausify_axiom axioms)
	val axcls_str = ResClause.tptp_clauses2str (ResLib.flat_noDup(map ResClause.tptp_clause axcls))
	val axiomfile = File.sysify_path axiom_file
	val out = TextIO.openOut (axiomfile)
    in
	(TextIO.output(out,axcls_str);TextIO.closeOut out; if !trace_res then (warning axiomfile) else (); atp_tac n)
    end;


fun atp thm =
    let val prems = prems_of thm
    in
	case prems of [] => () 
		    | _ => (atp_tac 1 thm; ())
    end;


(**** For running in Isar ****)

(* same function as that in res_axioms.ML *)
fun repeat_RS thm1 thm2 =
    let val thm1' =  thm1 RS thm2 handle THM _ => thm1
    in
	if eq_thm(thm1,thm1') then thm1' else (repeat_RS thm1' thm2)
    end;

(* a special version of repeat_RS *)
fun repeat_someI_ex thm = repeat_RS thm someI_ex;


(* convert clauses from "assume" to conjecture. write to file "hyps" *)
fun isar_atp_h thms =
    let val prems = map (skolemize o make_nnf o ObjectLogic.atomize_thm) thms
	val prems' = map repeat_someI_ex prems
	val prems'' = make_clauses prems'
	val prems''' = ResAxioms.rm_Eps [] prems''
	val clss = map ResClause.make_conjecture_clause prems'''
	val tptp_clss = ResLib.flat_noDup (map ResClause.tptp_clause clss)
        val hypsfile = File.sysify_path hyps_file
	val out = TextIO.openOut(hypsfile)
    in
	(ResLib.writeln_strs out tptp_clss; TextIO.closeOut out; if !trace_res then (warning hypsfile) else ())
    end;




val isar_atp_g = atp_tac;


fun isar_atp_goal' thm k n = 
    if (k > n) then () else (isar_atp_g k thm; isar_atp_goal' thm (k+1) n);


fun isar_atp_goal thm n_subgoals = (if (!debug) then warning (string_of_thm thm) else (isar_atp_goal' thm 1 n_subgoals));



fun isar_atp_aux thms thm n_subgoals = 
    (isar_atp_h thms; isar_atp_goal thm n_subgoals); (* convert both to conjecture clauses, but write to different files *)


fun isar_atp' (thms, thm) =
    let val prems = prems_of thm
    in
	case prems of [] => (if (!debug) then warning "entering forward, no goal" else ())
		    | _ => (isar_atp_aux thms thm (length prems))
    end;




local

fun retr_thms ([]:MetaSimplifier.rrule list) = []
	  | retr_thms (r::rs) = (#thm r)::(retr_thms rs);


fun snds [] = []
  |   snds ((x,y)::l) = y::(snds l);




fun get_thms_cs claset =
    let val clsset = rep_cs claset
	val safeEs = #safeEs clsset
	val safeIs = #safeIs clsset
	val hazEs = #hazEs clsset
	val hazIs = #hazIs clsset
    in
	safeEs @ safeIs @ hazEs @ hazIs
    end;



fun append_name name [] _ = []
  | append_name name (thm::thms) k = (Thm.name_thm ((name ^ "_" ^ (string_of_int k)),thm)) :: (append_name name thms (k+1));

fun append_names (name::names) (thms::thmss) =
    let val thms' = append_name name thms 0
    in
	thms'::(append_names names thmss)
    end;


fun get_thms_ss [] = []
  | get_thms_ss thms =
    let val names = map Thm.name_of_thm thms 
        val thms' = map (mksimps mksimps_pairs) thms
        val thms'' = append_names names thms'
    in
	ResLib.flat_noDup thms''
    end;




in


(* convert locally declared rules to axiom clauses *)
(* write axiom clauses to ax_file *)
fun isar_local_thms (delta_cs, delta_ss_thms) =
    let val thms_cs = get_thms_cs delta_cs
	val thms_ss = get_thms_ss delta_ss_thms
	val thms_clauses = ResLib.flat_noDup (map ResAxioms.clausify_axiom (thms_cs @ thms_ss))
	val clauses_strs = ResLib.flat_noDup (map ResClause.tptp_clause thms_clauses) (*string list*)
	val ax_file = File.sysify_path axiom_file
	val out = TextIO.openOut ax_file
    in
	(ResLib.writeln_strs out clauses_strs; TextIO.closeOut out)
    end;





(* called in Isar automatically *)
fun isar_atp (ctxt,thm) =
    let val prems = ProofContext.prems_of ctxt
      val d_cs = Classical.get_delta_claset ctxt
      val d_ss_thms = Simplifier.get_delta_simpset ctxt
    in
	(isar_local_thms (d_cs,d_ss_thms); isar_atp' (prems, thm))
    end;

end




end;

Proof.atp_hook := ResAtp.isar_atp;


