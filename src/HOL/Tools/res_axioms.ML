(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

Transformation of axiom rules (elim/intro/etc) into CNF forms.    
*)



signature RES_ELIM_RULE =
sig

exception ELIMR2FOL of string
val elimRule_tac : Thm.thm -> Tactical.tactic
val elimR2Fol : Thm.thm -> Term.term
val transform_elim : Thm.thm -> Thm.thm

end;

structure ResElimRule: RES_ELIM_RULE =

struct


fun elimRule_tac thm =
    ((rtac impI 1) ORELSE (rtac notI 1)) THEN (etac thm 1) THEN
    REPEAT(Blast_tac 1);


(* This following version fails sometimes, need to investigate, do not use it now. *)
fun elimRule_tac' thm =
   ((rtac impI 1) ORELSE (rtac notI 1)) THEN (etac thm 1) THEN
   REPEAT(SOLVE((etac exI 1) ORELSE (rtac conjI 1) ORELSE (rtac disjI1 1) ORELSE (rtac disjI2 1))); 


exception ELIMR2FOL of string;

fun make_imp (prem,concl) = Const("op -->", Type("fun",[Type("bool",[]),Type("fun",[Type("bool",[]),Type("bool",[])])])) $ prem $ concl;


fun make_disjs [x] = x
  | make_disjs (x :: xs) = Const("op |",Type("fun",[Type("bool",[]),Type("fun",[Type("bool",[]),Type("bool",[])])])) $ x $ (make_disjs xs)


fun make_conjs [x] = x
  | make_conjs (x :: xs) = Const("op &", Type("fun",[Type("bool",[]),Type("fun",[Type("bool",[]),Type("bool",[])])])) $ x $ (make_conjs xs)


fun add_EX term [] = term
  | add_EX term ((x,xtp)::xs) = add_EX (Const ("Ex",Type("fun",[Type("fun",[xtp,Type("bool",[])]),Type("bool",[])])) $ Abs (x,xtp,term)) xs;


exception TRUEPROP of string; 

fun strip_trueprop (Const ("Trueprop", Type("fun",[Type("bool",[]),Type("prop",[])])) $ P) = P
  | strip_trueprop _ = raise TRUEPROP("not a prop!");



exception STRIP_CONCL;


fun strip_concl prems bvs (Const ("all", _) $ Abs (x,xtp,body))  = strip_concl prems ((x,xtp)::bvs) body
  | strip_concl prems bvs (Const ("==>",_) $ P $ Q) =
    let val P' = strip_trueprop P
	val prems' = P'::prems
    in
	strip_concl prems' bvs  Q
    end
  | strip_concl prems bvs _ = add_EX (make_conjs prems) bvs;
 


fun trans_elim (main,others) =
    let val others' = map (strip_concl [] []) others
	val disjs = make_disjs others'
    in
	make_imp(strip_trueprop main,disjs)
    end;


fun neg P = Const ("Not", Type("fun",[Type("bool",[]),Type("bool",[])])) $ P;


fun elimR2Fol_aux prems = 
    let val nprems = length prems
	val main = hd prems
    in
	if (nprems = 1) then neg (strip_trueprop main)
        else trans_elim (main, tl prems)
    end;


fun trueprop term = Const ("Trueprop", Type("fun",[Type("bool",[]),Type("prop",[])])) $ term; 
	    

fun elimR2Fol elimR = 
    let val elimR' = Drule.freeze_all elimR
	val (prems,concl) = (prems_of elimR', concl_of elimR')
    in
	case concl of Const("Trueprop",_) $ Free(_,Type("bool",[])) 
		      => trueprop (elimR2Fol_aux prems)
                    | Free(x,Type("prop",[])) => trueprop(elimR2Fol_aux prems) 
		    | _ => raise ELIMR2FOL("Not an elimination rule!")
    end;




(**** use prove_goalw_cterm to prove ****)

fun transform_elim thm =
    let val tm = elimR2Fol thm
	val ctm = cterm_of (sign_of_thm thm) tm	
    in
	prove_goalw_cterm [] ctm (fn prems => [elimRule_tac thm])
    end;	


end;


(* some lemmas *)

Goal "(P==True) ==> P";
by(Blast_tac 1);
qed "Eq_TrueD1";

Goal "(P=True) ==> P";
by(Blast_tac 1);
qed "Eq_TrueD2";

Goal "(P==False) ==> ~P";
by(Blast_tac 1);
qed "Eq_FalseD1";

Goal "(P=False) ==> ~P";
by(Blast_tac 1);
qed "Eq_FalseD2";

local 

    fun prove s = prove_goal (the_context()) s (fn _ => [Simp_tac 1]);

val small_simps = 
  map prove 
   ["(P | True) == True", "(True | P) == True",
    "(P & True) == P", "(True & P) == P",
    "(False | P) == P", "(P | False) == P",
    "(False & P) == False", "(P & False) == False",
    "~True == False", "~False == True"];
in

val small_simpset = empty_ss addsimps small_simps

end;


signature RES_AXIOMS =
sig

val clausify_axiom : Thm.thm -> ResClause.clause list
val cnf_axiom : Thm.thm -> Thm.thm list
val cnf_elim : Thm.thm -> Thm.thm list
val cnf_intro : Thm.thm -> Thm.thm list
val cnf_rule : Thm.thm -> Thm.thm list
val cnf_classical_rules_thy : Theory.theory -> Thm.thm list list * Thm.thm list
val clausify_classical_rules_thy 
: Theory.theory -> ResClause.clause list list * Thm.thm list
val cnf_simpset_rules_thy 
: Theory.theory -> Thm.thm list list * Thm.thm list
val clausify_simpset_rules_thy 
: Theory.theory -> ResClause.clause list list * Thm.thm list
val rm_Eps 
: (Term.term * Term.term) list -> Thm.thm list -> Term.term list
end;

structure ResAxioms : RES_AXIOMS =
 
struct

open ResElimRule;

(* to be fixed: cnf_intro, cnf_rule, is_introR *)

fun is_elimR thm = 
    case (concl_of thm) of (Const ("Trueprop", _) $ Var (idx,_)) => true
			 | Var(indx,Type("prop",[])) => true
			 | _ => false;



fun repeat_RS thm1 thm2 =
    let val thm1' =  thm1 RS thm2 handle THM _ => thm1
    in
	if eq_thm(thm1,thm1') then thm1' else (repeat_RS thm1' thm2)
    end;



(* added this function to remove True/False in a theorem that is in NNF form. *)
fun rm_TF_nnf thm = simplify small_simpset thm;

fun skolem_axiom thm = 
    let val thm' = (skolemize o rm_TF_nnf o  make_nnf o ObjectLogic.atomize_thm o Drule.freeze_all) thm
    in 
	repeat_RS thm' someI_ex
    end;


fun isa_cls thm = 
    let val thm' = skolem_axiom thm 
    in
	map standard (make_clauses [thm'])
    end;


fun cnf_elim thm = 
    let val thm' = transform_elim thm;
    in
	isa_cls thm'
    end;


val cnf_intro = isa_cls;
val cnf_rule = isa_cls;	


fun is_introR thm = true;



(*Transfer a theorem in to theory Hilbert_Choice.thy if it is not already
  inside that theory -- because it's needed for Skolemization *)

val hc_thy = ThyInfo.get_theory"Hilbert_Choice";

fun transfer_to_Hilbert_Choice thm =
    transfer hc_thy thm handle THM _ => thm;

(* remove "True" clause *)
fun rm_redundant_cls [] = []
  | rm_redundant_cls (thm::thms) =
    let val t = prop_of thm
    in
	case t of (Const ("Trueprop", _) $ Const ("True", _)) => rm_redundant_cls thms
		| _ => thm::(rm_redundant_cls thms)
    end;

(* transform an Isabelle thm into CNF *)
fun cnf_axiom thm =
    let val thm' = transfer_to_Hilbert_Choice thm
	val thm'' = if (is_elimR thm') then (cnf_elim thm')
		    else (if (is_introR thm') then cnf_intro thm' else cnf_rule thm')
    in
	rm_redundant_cls thm''
    end;


(* changed: with one extra case added *)
fun univ_vars_of_aux (Const ("Hilbert_Choice.Eps",_) $ Abs(_,_,body)) vars = univ_vars_of_aux body vars
  | univ_vars_of_aux (Const ("Ex",_) $ Abs(_,_,body)) vars = univ_vars_of_aux body vars (* EX x. body *)
  | univ_vars_of_aux (P $ Q) vars =
    let val vars' = univ_vars_of_aux P vars
    in
	univ_vars_of_aux Q vars'
    end
  | univ_vars_of_aux (t as Var(_,_)) vars = 
    if (t mem vars) then vars else (t::vars)
  | univ_vars_of_aux _ vars = vars;
  

fun univ_vars_of t = univ_vars_of_aux t [];


fun get_new_skolem epss (t as (Const ("Hilbert_Choice.Eps",_) $ Abs(_,tp,_)))  = 
    let val all_vars = univ_vars_of t
	val sk_term = ResSkolemFunction.gen_skolem all_vars tp
    in
	(sk_term,(t,sk_term)::epss)
    end;


fun sk_lookup [] t = None
  | sk_lookup ((tm,sk_tm)::tms) t = if (t = tm) then Some (sk_tm) else (sk_lookup tms t);


fun get_skolem epss t = 
    let val sk_fun = sk_lookup epss t
    in
	case sk_fun of None => get_new_skolem epss t
		     | Some sk => (sk,epss)
    end;


fun rm_Eps_cls_aux epss (t as (Const ("Hilbert_Choice.Eps",_) $ Abs(_,_,_))) = get_skolem epss t
  | rm_Eps_cls_aux epss (P $ Q) =
    let val (P',epss') = rm_Eps_cls_aux epss P
	val (Q',epss'') = rm_Eps_cls_aux epss' Q
    in
	(P' $ Q',epss'')
    end
  | rm_Eps_cls_aux epss t = (t,epss);


fun rm_Eps_cls epss thm =
    let val tm = prop_of thm
    in
	rm_Eps_cls_aux epss tm
    end;



fun rm_Eps _ [] = []
  | rm_Eps epss (thm::thms) = 
    let val (thm',epss') = rm_Eps_cls epss thm
    in
	thm' :: (rm_Eps epss' thms)
    end;



(* changed, now it also finds out the name of the theorem. *)
fun clausify_axiom thm =
    let val isa_clauses = cnf_axiom thm (*"isa_clauses" are already "standard"ed. *)
        val isa_clauses' = rm_Eps [] isa_clauses
        val thm_name = Thm.name_of_thm thm
	val clauses_n = length isa_clauses
	fun make_axiom_clauses _ [] = []
	  | make_axiom_clauses i (cls::clss) = (ResClause.make_axiom_clause cls (thm_name,i)) :: make_axiom_clauses (i+1) clss 
    in
	make_axiom_clauses 0 isa_clauses'
		
    end;
  

(******** Extracting and CNF/Clausify theorems from a classical reasoner and simpset of a given theory ******)


local

fun retr_thms ([]:MetaSimplifier.rrule list) = []
	  | retr_thms (r::rs) = (#thm r)::(retr_thms rs);


fun snds [] = []
  |   snds ((x,y)::l) = y::(snds l);

in


fun claset_rules_of_thy thy =
    let val clsset = rep_cs (claset_of thy)
	val safeEs = #safeEs clsset
	val safeIs = #safeIs clsset
	val hazEs = #hazEs clsset
	val hazIs = #hazIs clsset
    in
	safeEs @ safeIs @ hazEs @ hazIs
    end;

fun simpset_rules_of_thy thy =
    let val simpset = simpset_of thy
	val rules = #rules(fst (rep_ss simpset))
	val thms = retr_thms (snds(Net.dest rules))
    in
	thms
    end;

end;


(**** Translate a set of classical rules or simplifier rules into CNF (still as type "thm") from a given theory ****)

(* classical rules *)
fun cnf_classical_rules [] err_list = ([],err_list)
  | cnf_classical_rules (thm::thms) err_list = 
    let val (ts,es) = cnf_classical_rules thms err_list
    in
	((cnf_axiom thm)::ts,es) handle  _ => (ts,(thm::es))
    end;


(* CNF all rules from a given theory's classical reasoner *)
fun cnf_classical_rules_thy thy = 
    let val rules = claset_rules_of_thy thy
    in
        cnf_classical_rules rules []
    end;


(* simplifier rules *)
fun cnf_simpset_rules [] err_list = ([],err_list)
  | cnf_simpset_rules (thm::thms) err_list =
    let val (ts,es) = cnf_simpset_rules thms err_list
    in
	((cnf_axiom thm)::ts,es) handle _ => (ts,(thm::es))
    end;


(* CNF all simplifier rules from a given theory's simpset *)
fun cnf_simpset_rules_thy thy =
    let val thms = simpset_rules_of_thy thy
    in
	cnf_simpset_rules thms []
    end;



(**** Convert all theorems of a classical reason/simpset into clauses (ResClause.clause) ****)

(* classical rules *)
fun clausify_classical_rules [] err_list = ([],err_list)
  | clausify_classical_rules (thm::thms) err_list =
    let val (ts,es) = clausify_classical_rules thms err_list
    in
	((clausify_axiom thm)::ts,es) handle  _ => (ts,(thm::es))
    end;

fun clausify_classical_rules_thy thy =
    let val rules = claset_rules_of_thy thy
    in
	clausify_classical_rules rules []
    end;


(* simplifier rules *)
fun clausify_simpset_rules [] err_list = ([],err_list)
  | clausify_simpset_rules (thm::thms) err_list =
    let val (ts,es) = clausify_simpset_rules thms err_list
    in
	((clausify_axiom thm)::ts,es) handle _ => (ts,(thm::es))
    end;


fun clausify_simpset_rules_thy thy =
    let val thms = simpset_rules_of_thy thy
    in
	clausify_simpset_rules thms []
    end;




end; 
