(* ID: $Id$ 
   Author: Jia Meng, NICTA

*)
structure ResAtpSetup =

struct

val keep_atp_input = ref false;
val debug = ref true;

val fol_keep_types = ResClause.keep_types;

(* use them to set and find type levels of HOL clauses *)
val hol_full_types = ResHolClause.full_types;
val hol_partial_types = ResHolClause.partial_types;
val hol_const_types_only = ResHolClause.const_types_only;
val hol_no_types = ResHolClause.no_types;
fun hol_typ_level () = ResHolClause.find_typ_level ();

fun is_typed_hol () = 
    let val tp_level = hol_typ_level()
    in
	not (tp_level = ResHolClause.T_NONE)
    end;

val include_combS = ResHolClause.include_combS;
val include_min_comb = ResHolClause.include_min_comb;



(*******************************************************)
(* set up the output paths                             *)
(*******************************************************)
fun full_typed_comb () =
    if !ResHolClause.include_combS then 
	(ResAtp.helper_path "E_HOME" "additionals/full_comb_inclS"
	 handle _ => ResAtp.helper_path "VAMPIRE_HOME" "additionals/full_comb_inclS")
    else 
	(ResAtp.helper_path "E_HOME" "additionals/full_comb_noS"
	 handle _ => ResAtp.helper_path "VAMPIRE_HOME" "additionals/full_comb_noS");

fun partial_typed_comb () = 
    if !ResHolClause.include_combS then 
	(ResAtp.helper_path "E_HOME" "additionals/par_comb_inclS"
	 handle _ => ResAtp.helper_path "VAMPIRE_HOME" "additionals/par_comb_inclS")
    else 
	(ResAtp.helper_path "E_HOME" "additionals/par_comb_noS"
	 handle _ => ResAtp.helper_path "VAMPIRE_HOME" "additionals/par_comb_noS");

fun const_typed_comb () =
    if !ResHolClause.include_combS then 
	(ResAtp.helper_path "E_HOME" "additionals/const_comb_inclS"
	 handle _ => ResAtp.helper_path "VAMPIRE_HOME" "additionals/const_comb_inclS")
    else 
	(ResAtp.helper_path "E_HOME" "additionals/const_comb_noS"
	 handle _ => ResAtp.helper_path "VAMPIRE_HOME" "additionals/const_comb_noS");
	
fun untyped_comb () = 
    if !ResHolClause.include_combS then 
	(ResAtp.helper_path "E_HOME" "additionals/u_comb_inclS"
	 handle _ => ResAtp.helper_path "VAMPIRE_HOME" "additionals/u_comb_inclS")
    else
	(ResAtp.helper_path "E_HOME" "additionals/u_comb_noS"
	 handle _ => ResAtp.helper_path "VAMPIRE_HOME" "additionals/u_comb_noS");


fun full_typed_HOL_helper1 () =
    ResAtp.helper_path "E_HOME" "additionals/full_helper1"
    handle _ => ResAtp.helper_path "VAMPIRE_HOME" "additionals/full_helper1";

fun partial_typed_HOL_helper1 () = 
    ResAtp.helper_path "E_HOME" "additionals/par_helper1"
    handle _ => ResAtp.helper_path "VAMPIRE_HOME" "additionals/par_helper1";

fun const_typed_HOL_helper1 () = 
    ResAtp.helper_path "E_HOME" "additionals/const_helper1"
    handle _ => ResAtp.helper_path "VAMPIRE_HOME" "additionals/const_helper1";


fun untyped_HOL_helper1 () = 
    ResAtp.helper_path "E_HOME" "additionals/u_helper1"
    handle _ => ResAtp.helper_path "VAMPIRE_HOME" "additionals/u_helper1";


fun HOL_helper1 () =
    let val tp_level = !ResHolClause.typ_level
    in
	case tp_level of ResHolClause.T_PARTIAL => (warning "Partial type helper"; partial_typed_HOL_helper1 ())
		       | ResHolClause.T_FULL => (warning "Full type helper"; full_typed_HOL_helper1 ())
		       | ResHolClause.T_CONST => (warning "Const type helper"; const_typed_HOL_helper1 ())
		       | ResHolClause.T_NONE => (warning "Untyped helper"; untyped_HOL_helper1 ())
    end;


fun HOL_comb () =
    let val tp_level = !ResHolClause.typ_level
    in
	case tp_level of ResHolClause.T_FULL => (warning "Full type comb"; full_typed_comb ())
		       | ResHolClause.T_PARTIAL => (warning "Partial type comb"; partial_typed_comb ())
		       | ResHolClause.T_CONST => (warning "Const type comb"; const_typed_comb ())
		       | ResHolClause.T_NONE => (warning "Untyped comb"; untyped_comb ())
    end;


fun atp_input_file file =
    let val file' = !ResAtp.problem_name ^ "_" ^ file
    in
	if !ResAtp.destdir = "" then File.platform_path (File.tmp_path (Path.basic file'))
	else if File.exists (File.unpack_platform_path (!ResAtp.destdir))
	then !ResAtp.destdir ^ "/" ^ file'
	else error ("No such directory: " ^ !ResAtp.destdir)
    end;

fun claset_file () = atp_input_file "claset";
fun simpset_file () = atp_input_file "simp";
fun local_lemma_file () = atp_input_file "locallemmas";
fun hyps_file () = atp_input_file "hyps";
fun prob_file _ = atp_input_file "";

fun types_sorts_file () = atp_input_file "typesorts";



(*******************************************************)
(* operations on Isabelle theorems:                    *)
(* retrieving from ProofContext,                       *)
(* modifying local theorems,                           *)
(* CNF                                                 *)
(*******************************************************)

val include_simpset = ref false;
val include_claset = ref false; 

val add_simpset = (fn () => include_simpset:=true);
val add_claset = (fn () => include_claset:=true);
val add_clasimp = (fn () => include_simpset:=true;include_claset:=true);
val rm_simpset = (fn () => include_simpset:=false);
val rm_claset = (fn () => include_claset:=false);
val rm_clasimp = (fn () => include_simpset:=false;include_claset:=false);


(******************************************************************)
(* detect whether a given problem (clauses) is FOL/HOL/HOLC/HOLCS *)
(******************************************************************)

datatype logic = FOL | HOL | HOLC | HOLCS;

fun string_of_logic FOL = "FOL"
  | string_of_logic HOL = "HOL"
  | string_of_logic HOLC = "HOLC"
  | string_of_logic HOLCS = "HOLCS";

(*HOLCS will not occur here*)
fun upgrade_lg HOLC _ = HOLC
  | upgrade_lg HOL HOLC = HOLC
  | upgrade_lg HOL _ = HOL
  | upgrade_lg FOL lg = lg; 

(* check types *)
fun has_bool (Type("bool",_)) = true
  | has_bool (Type(_, Ts)) = exists has_bool Ts
  | has_bool _ = false;

fun has_bool_arg tp = 
    let val (targs,tr) = strip_type tp
    in
	exists has_bool targs
    end;

fun is_fn_tp (Type("fun",_)) = true
  | is_fn_tp _ = false;


exception FN_LG of term;

fun fn_lg (t as Const(f,tp)) (lg,seen) = 
    if has_bool tp then (upgrade_lg HOL lg, t ins seen) else (lg, t ins seen) 
  | fn_lg (t as Free(f,tp)) (lg,seen) = 
    if has_bool tp then (upgrade_lg HOL lg, t ins seen) else (lg, t ins seen) 
  | fn_lg (t as Var(f,tp)) (lg,seen) =
    if is_fn_tp tp orelse has_bool tp then (upgrade_lg HOL lg,t ins seen)
    else (lg,t ins seen)
  | fn_lg (t as Abs(_,_,_)) (lg,seen) = (upgrade_lg HOLC lg,t ins seen)
  | fn_lg f _ = raise FN_LG(f); 


fun term_lg [] (lg,seen) = (lg,seen)
  | term_lg (tm::tms) (FOL,seen) =
    let val (f,args) = strip_comb tm
	val (lg',seen') = if f mem seen then (FOL,seen) 
			  else fn_lg f (FOL,seen)

	 in
	     term_lg (args@tms) (lg',seen')
    end
  | term_lg _ (lg,seen) = (lg,seen)

exception PRED_LG of term;

fun pred_lg (t as Const(P,tp)) (lg,seen)= 
    if has_bool_arg tp then (upgrade_lg HOL lg, t ins seen) else (lg,t ins seen) 
  | pred_lg (t as Free(P,tp)) (lg,seen) =
    if has_bool_arg tp then (upgrade_lg HOL lg, t ins seen) else (lg,t ins seen)
  | pred_lg (t as Var(_,_)) (lg,seen) = (upgrade_lg HOL lg, t ins seen)
  | pred_lg P _ = raise PRED_LG(P);


fun lit_lg (Const("Not",_) $ P) (lg,seen) = lit_lg P (lg,seen)
  | lit_lg P (lg,seen) =
    let val (pred,args) = strip_comb P
	val (lg',seen') = if pred mem seen then (lg,seen) 
			  else pred_lg pred (lg,seen)
    in
	term_lg args (lg',seen')
    end;

fun lits_lg [] (lg,seen) = (lg,seen)
  | lits_lg (lit::lits) (FOL,seen) =
    lits_lg lits (lit_lg lit (FOL,seen))
  | lits_lg lits (lg,seen) = (lg,seen);


fun logic_of_clause tm (lg,seen) =
    let val tm' = HOLogic.dest_Trueprop tm
	val disjs = HOLogic.dest_disj tm'
    in
	lits_lg disjs (lg,seen)
    end;

fun lits_lg [] (lg,seen) = (lg,seen)
  | lits_lg (lit::lits) (FOL,seen) =
    lits_lg lits (lit_lg lit (FOL,seen))
  | lits_lg lits (lg,seen) = (lg,seen);


fun logic_of_clause tm (lg,seen) =
    let val tm' = HOLogic.dest_Trueprop tm
	val disjs = HOLogic.dest_disj tm'
    in
	lits_lg disjs (lg,seen)
    end;

fun logic_of_clauses [] (lg,seen) = (lg,seen)
  | logic_of_clauses (cls::clss) (FOL,seen) =
    logic_of_clauses clss (logic_of_clause cls (FOL,seen))
  | logic_of_clauses (cls::clss) (lg,seen) = (lg,seen);

fun logic_of_nclauses [] (lg,seen) = (lg,seen)
  | logic_of_nclauses (cls::clss) (FOL,seen) =
    logic_of_nclauses clss (logic_of_clauses (snd cls) (FOL,seen))
  | logic_of_nclauses clss (lg,seen) = (lg,seen);



fun problem_logic (conj_cls,hyp_cls,userR,claR,simpR) =
    let val (lg1,seen1) = logic_of_clauses conj_cls (FOL,[])
	val (lg2,seen2) = logic_of_clauses hyp_cls (lg1,seen1)
	val (lg3,seen3) = logic_of_nclauses userR (lg2,seen2)
	val (lg4,seen4) = logic_of_nclauses claR (lg3,seen3)
	val (lg5,seen5) = logic_of_nclauses simpR (lg4,seen4)
    in
	lg5
    end;



(***************************************************************)
(* prover-specific output format:                              *)
(* TPTP                                                        *)
(***************************************************************)

(**** CNF rules and hypothesis ****)
fun cnf_rules_tms ctxt ths (include_claset,include_simpset) =
    let val local_claR = if include_claset then ResAxioms.claset_rules_of_ctxt ctxt else []
	val (local_claR_cls,err1) = ResAxioms.cnf_rules2 local_claR []
	val local_simpR = if include_simpset then ResAxioms.simpset_rules_of_ctxt ctxt else []
	val (local_simpR_cls,err2) = ResAxioms.cnf_rules2 local_simpR []
	val (user_ths_cls,err3) = ResAxioms.cnf_rules2 (map ResAxioms.pairname ths) []
	val errs = err3 @ err2 @ err1
    in
	(user_ths_cls,local_simpR_cls,local_claR_cls,errs)
    end;

fun cnf_hyps_thms ctxt = 
    let val ths = ProofContext.prems_of ctxt
    in
	ResClause.union_all (map ResAxioms.skolem_thm ths)
    end;

(**** clausification ****)
fun cls_axiom_fol _ _ [] = []
  | cls_axiom_fol name i (tm::tms) =
      case ResClause.make_axiom_clause tm (name,i) of 
          SOME cls => cls :: cls_axiom_fol name (i+1) tms
        | NONE => cls_axiom_fol name i tms;

fun cls_axiom_hol  _ _ [] = []
  | cls_axiom_hol name i (tm::tms) =
   (ResHolClause.make_axiom_clause tm (name,i)) :: (cls_axiom_hol name (i+1) tms);


fun filtered_tptp_axiom_fol name clss =
    (fst(ListPair.unzip (map ResClause.clause2tptp (filter (fn c => not (ResClause.isTaut c)) (cls_axiom_fol name 0 clss)))),[])
    handle _ => ([],[name]);

fun filtered_tptp_axiom_hol name clss =
    (fst(ListPair.unzip (map ResHolClause.clause2tptp (filter (fn c => not (ResHolClause.isTaut c)) (cls_axiom_hol name 0 clss)))),[])
    handle _ => ([],[name]);

fun tptp_axioms_g filt_ax_fn [] err = ([],err)
  | tptp_axioms_g filt_ax_fn ((name,clss)::nclss) err =
    let val (nclss1,err1) = tptp_axioms_g filt_ax_fn nclss err
	val (clsstrs,err_name_list) = filt_ax_fn name clss
    in
	case clsstrs of [] => (nclss1,err_name_list @ err1) 
		      | _ => (clsstrs::nclss1,err1)
    end;
		
fun tptp_axioms_fol rules = tptp_axioms_g filtered_tptp_axiom_fol rules [];

fun tptp_axioms_hol rules = tptp_axioms_g filtered_tptp_axiom_hol rules [];


fun atp_axioms_g tptp_ax_fn rules file =
    let val out = TextIO.openOut file
	val (clss,errs) = tptp_ax_fn rules
	val clss' = ResClause.union_all clss
    in
	ResClause.writeln_strs out clss';
	TextIO.closeOut out;
	([file],errs)
    end;


fun atp_axioms_fol rules file = atp_axioms_g tptp_axioms_fol rules file;

fun atp_axioms_hol rules file = atp_axioms_g tptp_axioms_hol rules file;


fun filtered_tptp_conjectures_fol terms =
    let val clss = ResClause.make_conjecture_clauses terms
	val clss' = filter (fn c => not (ResClause.isTaut c)) clss
    in
	ListPair.unzip (map ResClause.clause2tptp clss')
    end;

fun filtered_tptp_conjectures_hol terms =
    let val clss = ResHolClause.make_conjecture_clauses terms
	val clss' = filter (fn c => not (ResHolClause.isTaut c)) clss
    in
	ListPair.unzip (map ResHolClause.clause2tptp clss')
    end;

fun atp_conjectures_h_g filt_conj_fn hyp_cls =
    let val (tptp_h_clss,tfree_litss) = filt_conj_fn hyp_cls
	val tfree_lits = ResClause.union_all tfree_litss
	val tfree_clss = map ResClause.tptp_tfree_clause tfree_lits 
	val hypsfile = hyps_file ()
        val out = TextIO.openOut(hypsfile)
    in
        ResClause.writeln_strs out (tfree_clss @ tptp_h_clss);
        TextIO.closeOut out; warning hypsfile;
        ([hypsfile],tfree_lits)
    end;

fun atp_conjectures_h_fol hyp_cls = atp_conjectures_h_g filtered_tptp_conjectures_fol hyp_cls;

fun atp_conjectures_h_hol hyp_cls = atp_conjectures_h_g filtered_tptp_conjectures_hol hyp_cls;

fun atp_conjectures_c_g filt_conj_fn conj_cls n tfrees =
    let val (tptp_c_clss,tfree_litss) = filt_conj_fn conj_cls
	val tfree_clss = map ResClause.tptp_tfree_clause ((ResClause.union_all tfree_litss) \\ tfrees)
	val probfile = prob_file n
	val out = TextIO.openOut(probfile)		 	
    in
	ResClause.writeln_strs out (tfree_clss @ tptp_c_clss);
	TextIO.closeOut out;
	warning probfile; 
	probfile 
    end;

fun atp_conjectures_c_fol conj_cls n tfrees = atp_conjectures_c_g filtered_tptp_conjectures_fol conj_cls n tfrees;

fun atp_conjectures_c_hol conj_cls n tfrees = atp_conjectures_c_g filtered_tptp_conjectures_hol conj_cls n tfrees;


fun atp_conjectures_g atp_conj_h_fn atp_conj_c_fn [] conj_cls n =
    let val probfile = atp_conj_c_fn conj_cls n []
    in
	[probfile]
    end
  | atp_conjectures_g atp_conj_h_fn atp_conj_c_fn hyp_cls conj_cls n =
    let val (hypsfile,tfree_lits) = atp_conj_h_fn hyp_cls
	val probfile = atp_conj_c_fn conj_cls n tfree_lits
    in
	(probfile::hypsfile)
    end;

fun atp_conjectures_fol hyp_cls conj_cls n = atp_conjectures_g atp_conjectures_h_fol atp_conjectures_c_fol hyp_cls conj_cls n;

fun atp_conjectures_hol hyp_cls conj_cls n = atp_conjectures_g atp_conjectures_h_hol atp_conjectures_c_hol hyp_cls conj_cls n;


(**** types and sorts ****)
fun tptp_types_sorts thy = 
    let val classrel_clauses = ResClause.classrel_clauses_thy thy
	val arity_clauses = ResClause.arity_clause_thy thy
	val classrel_cls = map ResClause.tptp_classrelClause classrel_clauses
	val arity_cls = map ResClause.tptp_arity_clause arity_clauses
	fun write_ts () =
	    let val tsfile = types_sorts_file ()
		val out = TextIO.openOut(tsfile)
	    in
		ResClause.writeln_strs out (classrel_cls @ arity_cls);
		TextIO.closeOut out;
		[tsfile]
	    end
    in
	if (List.null arity_cls andalso List.null classrel_cls) then []
	else
	    write_ts ()
    end;


(******* write to files ******)

datatype mode = Auto | Fol | Hol;

fun write_out_g logic atp_ax_fn atp_conj_fn (claR,simpR,userR,hyp_cls,conj_cls,n,err) =
    let val (files1,err1) = if (null claR) then ([],[]) else (atp_ax_fn claR (claset_file()))
	val (files2,err2) = if (null simpR) then ([],[]) else (atp_ax_fn simpR (simpset_file ()))
	val (files3,err3) = if (null userR) then ([],[]) else (atp_ax_fn userR (local_lemma_file ()))
	val files4 = atp_conj_fn hyp_cls conj_cls n
	val errs = err1 @ err2 @ err3 @ err
	val logic' = if !include_combS then HOLCS 
		     else 
			 if !include_min_comb then HOLC else logic
	val _ = warning ("Problems are " ^ (string_of_logic logic'))
	val _ = if (null errs) then () else warning ("Can't clausify thms: " ^ (ResClause.paren_pack errs))
	val helpers = case logic' of FOL => []
				   | HOL => [HOL_helper1 ()]
				   | _ => [HOL_helper1(),HOL_comb()] (*HOLC or HOLCS*)
    in
	(helpers,files4 @ files1 @ files2 @ files3)
    end;

fun write_out_fol (claR,simpR,userR,hyp_cls,conj_cls,n,err) = write_out_g FOL atp_axioms_fol atp_conjectures_fol (claR,simpR,userR,hyp_cls,conj_cls,n,err);

fun write_out_hol (claR,simpR,userR,hyp_cls,conj_cls,n,err) = write_out_g HOL atp_axioms_hol atp_conjectures_hol (claR,simpR,userR,hyp_cls,conj_cls,n,err);

fun write_out_fol_ts ctxt (claR,simpR,userR,hyp_cls,conj_cls,n,err) =  
    let val ts_file = if (!fol_keep_types) then tptp_types_sorts (ProofContext.theory_of ctxt) else []
	val (helpers,files) = write_out_fol (claR,simpR,userR,hyp_cls,conj_cls,n,err) 
    in
	(helpers,files@ts_file)
    end;

fun write_out_hol_ts ctxt (claR,simpR,userR,hyp_cls,conj_cls,n,err) =  
    let val ts_file = if (is_typed_hol()) then tptp_types_sorts (ProofContext.theory_of ctxt) else []
	val (helpers,files) = write_out_hol (claR,simpR,userR,hyp_cls,conj_cls,n,err)
    in
	(helpers,files@ts_file)
    end;


fun prep_atp_input mode ctxt conjectures user_thms n =
    let val conj_cls = map prop_of (make_clauses conjectures) 
	val (userR,simpR,claR,errs) = cnf_rules_tms ctxt user_thms (!include_claset,!include_simpset) 
	val hyp_cls = map prop_of (cnf_hyps_thms ctxt) 
	val logic = case mode of Auto => problem_logic (conj_cls,hyp_cls,userR,claR,simpR)
			       | Fol => FOL
			       | Hol => HOL
    in
	case logic of FOL => write_out_fol_ts ctxt (claR,simpR,userR,hyp_cls,conj_cls,n,errs)
		    | _ => write_out_hol_ts ctxt (claR,simpR,userR,hyp_cls,conj_cls,n,errs)
			   
    end;


(***************************************************************)
(* setup ATPs as Isabelle methods                              *)
(***************************************************************)


fun atp_meth' tac ths ctxt = 
    Method.SIMPLE_METHOD' HEADGOAL
    (tac ctxt ths);

fun atp_meth tac ths ctxt = 
    let val thy = ProofContext.theory_of ctxt
	val _ = ResClause.init thy
	val _ = ResHolClause.init thy
    in
	atp_meth' tac ths ctxt
    end;


fun atp_method tac = Method.thms_ctxt_args (atp_meth tac);


(*************Remove tmp files********************************)
fun rm_tmp_files1 [] = ()
  | rm_tmp_files1 (f::fs) =
    (OS.FileSys.remove f; rm_tmp_files1 fs);

fun cond_rm_tmp files = 
    if !keep_atp_input then warning "ATP input kept..." 
    else if !ResAtp.destdir <> "" then warning ("ATP input kept in directory " ^ (!ResAtp.destdir))
    else (warning "deleting ATP inputs..."; rm_tmp_files1 files);

end
