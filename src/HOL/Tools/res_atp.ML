(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

ATPs with TPTP format input.
*)
signature RES_ATP = 
sig

val trace_res : bool ref
val axiom_file : Path.T
val hyps_file : Path.T
val isar_atp : Thm.thm list * Thm.thm -> unit
val prob_file : Path.T
val atp_ax_tac : Thm.thm list -> int -> Tactical.tactic
val atp_tac : int -> Tactical.tactic

end;

structure ResAtp : RES_ATP =

struct

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



fun tptp_inputs thms = 
    let val clss = map (ResClause.make_conjecture_clause_thm) thms
	val tptp_clss = ResLib.flat_noDup(map ResClause.tptp_clause clss) 
        val probfile = File.sysify_path prob_file
	val out = TextIO.openOut(probfile)
    in
	(ResLib.writeln_strs out tptp_clss; TextIO.closeOut out; (if !trace_res then (warning probfile) else ()))
    end;


(**** for Isabelle/ML interface  ****)

fun call_atp_tac thms = (tptp_inputs thms; dummy_tac);


val atp_tac = SELECT_GOAL
  (EVERY1 [rtac ccontr, atomize_tac, skolemize_tac, 
  METAHYPS(fn negs => (call_atp_tac(make_clauses negs)))]);


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



fun isar_atp_h thms =
    let val prems = map (skolemize o make_nnf o ObjectLogic.atomize_thm) thms
	val prems' = map repeat_someI_ex prems
	val prems'' = make_clauses prems'
	val prems''' = ResAxioms.rm_Eps [] prems''
	val clss = map ResClause.make_hypothesis_clause prems'''
	val tptp_clss = ResLib.flat_noDup (map ResClause.tptp_clause clss)
        val hypsfile = File.sysify_path hyps_file
	val out = TextIO.openOut(hypsfile)
    in
	(ResLib.writeln_strs out tptp_clss; TextIO.closeOut out; if !trace_res then (warning hypsfile) else ())
    end;




val isar_atp_g = atp_tac;

fun isar_atp_aux thms thm = 
    (isar_atp_h thms; isar_atp_g 1 thm;());





(* called in Isar automatically *)
fun isar_atp (thms, thm) =
    let val prems = prems_of thm
    in
	case prems of [] => () 
		    | _ => (isar_atp_aux thms thm)
    end;

end;

Proof.atp_hook := ResAtp.isar_atp;


