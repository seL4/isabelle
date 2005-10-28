(* ID: $Id$ 
   Author: Jia Meng, NICTA

*)
structure ResAtpSetup =

struct

val keep_atp_input = ref false;
val debug = ref true;
val filter_ax = ref false;


fun warning_thm thm nm = warning (nm ^ " " ^ (string_of_thm thm));

fun warning_thms_n n thms nm =
    let val _ = warning ("total " ^ (string_of_int n) ^ " " ^ nm)
	fun warning_thms_aux [] = warning ("no more " ^ nm)
	  | warning_thms_aux (th::ths) = (warning_thm th nm; warning_thms_aux ths)
    in
	warning_thms_aux thms
    end;


(*******************************************************)
(* set up the output paths                             *)
(*******************************************************)

val claset_file = File.tmp_path (Path.basic "claset");
val simpset_file = File.tmp_path (Path.basic "simp");

val prob_file = File.tmp_path (Path.basic "prob");
val hyps_file = File.tmp_path (Path.basic "hyps");

val types_sorts_file =  File.tmp_path (Path.basic "typsorts");

(*******************************************************)
(* operations on Isabelle theorems:                    *)
(* retrieving from ProofContext,                       *)
(* modifying local theorems,                           *)
(* CNF                                                 *)
(*******************************************************)

(* a special version of repeat_RS *)
fun repeat_someI_ex thm = ResAxioms.repeat_RS thm someI_ex;

val include_simpset = ref false;
val include_claset = ref false; 

val add_simpset = (fn () => include_simpset:=true);
val add_claset = (fn () => include_claset:=true);
val add_clasimp = (fn () => include_simpset:=true;include_claset:=true);
val rm_simpset = (fn () => include_simpset:=false);
val rm_claset = (fn () => include_claset:=false);
val rm_clasimp = (fn () => include_simpset:=false;include_claset:=false);



val rules_modifiers =
  Simplifier.simp_modifiers @ Splitter.split_modifiers @
  Classical.cla_modifiers @ iff_modifiers;



fun get_local_claR ctxt = 
    let val cla_rules = rep_cs (Classical.get_local_claset ctxt) 
	val safeEs = #safeEs cla_rules
	val safeIs = #safeIs cla_rules
	val hazEs = #hazEs cla_rules
	val hazIs = #hazIs cla_rules
    in
	map ResAxioms.pairname (safeEs @ safeIs @ hazEs @ hazIs)
    end;


fun get_local_simpR ctxt = 
    let val simpset_rules = #rules(fst (rep_ss (Simplifier.get_local_simpset ctxt)))
    in
	map (fn r => (#name r, #thm r)) (Net.entries simpset_rules) end;



(***************************************************************)
(* prover-specific output format:                              *)
(* TPTP                                                        *)
(***************************************************************)




(***************** TPTP format *********************************)

(* convert each (sub)goal clause (Thm.thm) into one or more TPTP clauses.  The additional TPTP clauses are tfree_lits.  Write the output TPTP clauses to a problem file *)

fun mk_conjectures is_fol terms =
    if is_fol then
	ListPair.unzip (map ResClause.clause2tptp (ResClause.make_conjecture_clauses terms))
    else
	ListPair.unzip (map ResHolClause.clause2tptp (ResHolClause.make_conjecture_clauses terms));


fun tptp_form_g is_fol thms n tfrees =
    let val terms = map prop_of thms
	val (tptp_clss,tfree_litss) = mk_conjectures is_fol terms
	val tfree_clss = map ResClause.tfree_clause ((ResClause.union_all tfree_litss) \\ tfrees)
	val probfile = File.platform_path prob_file ^ "_" ^ string_of_int n
	val out = TextIO.openOut(probfile)		 	
    in
	ResAtp.writeln_strs out (tfree_clss @ tptp_clss);
	TextIO.closeOut out;
	warning probfile; (* show the location for debugging *)
	probfile (* return the location *)
	
    end;


val tptp_form = tptp_form_g true;
val tptp_formH = tptp_form_g false;

fun tptp_hyps_g _ [] = ([], [])
  | tptp_hyps_g is_fol thms =
    let val mk_nnf = if is_fol then make_nnf else make_nnf1
	val prems = map (skolemize o mk_nnf o ObjectLogic.atomize_thm) thms
        val prems' = map repeat_someI_ex prems
        val prems'' = make_clauses prems'
        val prems''' = ResAxioms.rm_Eps [] prems''
	val (tptp_clss,tfree_litss) = mk_conjectures is_fol prems'''
	val tfree_lits = ResClause.union_all tfree_litss
	val tfree_clss = map ResClause.tfree_clause tfree_lits 
        val hypsfile = File.platform_path hyps_file
        val out = TextIO.openOut(hypsfile)
    in
        ResAtp.writeln_strs out (tfree_clss @ tptp_clss);
        TextIO.closeOut out; warning hypsfile;
        ([hypsfile],tfree_lits)
    end;
 

val tptp_hyps = tptp_hyps_g true;
val tptp_hypsH = tptp_hyps_g false;

fun subtract_simpset thy ctxt =
  let
    val rules1 = #rules (#1 (rep_ss (simpset_of thy)));
    val rules2 = #rules (#1 (rep_ss (local_simpset_of ctxt)));
  in map ResAxioms.pairname (map #thm (Net.subtract MetaSimplifier.eq_rrule rules1 rules2)) end;

fun subtract_claset thy ctxt =
  let
    val (netI1, netE1) = #xtra_netpair (rep_cs (claset_of thy));
    val (netI2, netE2) = #xtra_netpair (rep_cs (local_claset_of ctxt));
    val subtract = map (#2 o #2) oo Net.subtract Tactic.eq_kbrl;
  in map ResAxioms.pairname (subtract netI1 netI2 @ subtract netE1 netE2) end;


fun mk_axioms is_fol rules =
    if is_fol then 
	(let val  clss = ResClause.union_all(ResAxioms.clausify_rules_pairs rules)
	     val (clss',names) = ListPair.unzip clss
	     val (tptpclss,_) = ListPair.unzip(map ResClause.clause2tptp clss')
	 in tptpclss end)
    else
	(let val  clss = ResClause.union_all(ResAxioms.clausify_rules_pairsH rules)
	     val (clss',names) = ListPair.unzip clss
	     val (tptpclss,_) = ListPair.unzip(map ResHolClause.clause2tptp clss')
	 in tptpclss end)


local

fun write_rules_g is_fol [] file = [](* no rules, then no need to write anything, thus no clasimp file *)
  | write_rules_g is_fol rules file =
    let val out = TextIO.openOut(file)
	val tptpclss = mk_axioms is_fol rules
    in
	ResAtp.writeln_strs out tptpclss;
	TextIO.closeOut out; warning file;
	[file]
    end;


val write_rules = write_rules_g true;
val write_rulesH = write_rules_g false;

in

(* TPTP Isabelle theorems *)
fun tptp_cnf_rules_g write_rules (clasetR,simpsetR) =
    let val simpfile = File.platform_path simpset_file
	val clafile =  File.platform_path claset_file
    in
	(write_rules clasetR clafile) @ (write_rules simpsetR simpfile)
    end;

val tptp_cnf_rules = tptp_cnf_rules_g write_rules;
val tptp_cnf_rulesH = tptp_cnf_rules_g write_rulesH;

end

fun tptp_cnf_clasimp_g tptp_cnf_rules ctxt (include_claset,include_simpset) =
    let val local_claR = if include_claset then get_local_claR ctxt else (subtract_claset (ProofContext.theory_of ctxt) ctxt)
	val local_simpR = if include_simpset then get_local_simpR ctxt else (subtract_simpset (ProofContext.theory_of ctxt) ctxt)

    in
	tptp_cnf_rules (local_claR,local_simpR)
    end;


val tptp_cnf_clasimp = tptp_cnf_clasimp_g tptp_cnf_rules;
val tptp_cnf_clasimpH = tptp_cnf_clasimp_g tptp_cnf_rulesH;


fun tptp_types_sorts thy = 
    let val classrel_clauses = ResClause.classrel_clauses_thy thy
	val arity_clauses = ResClause.arity_clause_thy thy
	val classrel_cls = map ResClause.tptp_classrelClause classrel_clauses
	val arity_cls = map ResClause.tptp_arity_clause arity_clauses
	fun write_ts () =
	    let val tsfile = File.platform_path types_sorts_file
		val out = TextIO.openOut(tsfile)
	    in
		ResAtp.writeln_strs out (classrel_cls @ arity_cls);
		TextIO.closeOut out;
		[tsfile]
	    end
    in
	if (List.null arity_cls andalso List.null classrel_cls) then []
	else
	    write_ts ()
    end;



(*FIXME: a function that does not perform any filtering now *)
fun find_relevant_ax ctxt = tptp_cnf_clasimp ctxt (true,true);


(***************************************************************)
(* setup ATPs as Isabelle methods                               *)
(***************************************************************)
fun atp_meth_g tptp_hyps tptp_cnf_clasimp tac prems ctxt = 
    let val rules = if !filter_ax then find_relevant_ax ctxt 
		    else tptp_cnf_clasimp ctxt (!include_claset, !include_simpset) 
	val (hyps,tfrees) = tptp_hyps (ProofContext.prems_of ctxt)
	val thy = ProofContext.theory_of ctxt
	val tsfile = tptp_types_sorts thy
	val files = hyps @ rules @ tsfile
    in
	Method.METHOD (fn facts =>
			  if !debug then (warning_thms_n (length facts) facts "facts";HEADGOAL (tac ctxt files tfrees)) 
			  else HEADGOAL (tac ctxt files tfrees))
    end;

fun atp_meth_f tac = atp_meth_g tptp_hyps tptp_cnf_clasimp tac;

fun atp_meth_h tac = atp_meth_g tptp_hypsH tptp_cnf_clasimpH tac;

fun atp_meth_G atp_meth tac prems ctxt =
    let val _ = ResClause.init (ProofContext.theory_of ctxt)
    in    
	if not(List.null prems) then (warning_thms_n (length prems) prems "prems!!!"; atp_meth tac prems ctxt)
	else (atp_meth tac prems ctxt)
    end;
	

fun atp_meth_H tac = atp_meth_G atp_meth_h tac;

fun atp_meth_F tac = atp_meth_G atp_meth_f tac;


val atp_method_H = Method.bang_sectioned_args rules_modifiers o atp_meth_H;

val atp_method_F = Method.bang_sectioned_args rules_modifiers o atp_meth_F;



(*************Remove tmp files********************************)
fun rm_tmp_files1 [] = ()
  | rm_tmp_files1 (f::fs) =
    (OS.FileSys.remove f; rm_tmp_files1 fs);

fun cond_rm_tmp files = 
    if !keep_atp_input then warning "ATP input kept..." 
    else (warning "deleting ATP inputs..."; rm_tmp_files1 files);


end
