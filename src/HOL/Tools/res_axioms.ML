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

(* a tactic used to prove an elim-rule. *)
fun elimRule_tac thm =
    ((rtac impI 1) ORELSE (rtac notI 1)) THEN (etac thm 1) THEN
    REPEAT(Fast_tac 1);


(* This following version fails sometimes, need to investigate, do not use it now. *)
fun elimRule_tac' thm =
   ((rtac impI 1) ORELSE (rtac notI 1)) THEN (etac thm 1) THEN
   REPEAT(SOLVE((etac exI 1) ORELSE (rtac conjI 1) ORELSE (rtac disjI1 1) ORELSE (rtac disjI2 1))); 


exception ELIMR2FOL of string;

(* functions used to construct a formula *)

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


fun neg P = Const ("Not", Type("fun",[Type("bool",[]),Type("bool",[])])) $ P;


fun is_neg (Const("Trueprop",_) $ (Const("Not",_) $ Free(p,_))) (Const("Trueprop",_) $ Free(q,_))= (p = q)
  | is_neg _ _ = false;


exception STRIP_CONCL;


fun strip_concl' prems bvs (Const ("==>",_) $ P $ Q) =
    let val P' = strip_trueprop P
	val prems' = P'::prems
    in
	strip_concl' prems' bvs  Q
    end
  | strip_concl' prems bvs P = 
    let val P' = neg (strip_trueprop P)
    in
	add_EX (make_conjs (P'::prems)) bvs
    end;


fun strip_concl prems bvs concl (Const ("all", _) $ Abs (x,xtp,body))  = strip_concl prems ((x,xtp)::bvs) concl body
  | strip_concl prems bvs concl (Const ("==>",_) $ P $ Q) =
    if (is_neg P concl) then (strip_concl' prems bvs Q)
    else
	(let val P' = strip_trueprop P
	     val prems' = P'::prems
	 in
	     strip_concl prems' bvs  concl Q
	 end)
  | strip_concl prems bvs concl _ = add_EX (make_conjs prems) bvs;
 


fun trans_elim (main,others,concl) =
    let val others' = map (strip_concl [] [] concl) others
	val disjs = make_disjs others'
    in
	make_imp(strip_trueprop main,disjs)
    end;


(* aux function of elim2Fol, take away predicate variable. *)
fun elimR2Fol_aux prems concl = 
    let val nprems = length prems
	val main = hd prems
    in
	if (nprems = 1) then neg (strip_trueprop main)
        else trans_elim (main, tl prems, concl)
    end;


fun trueprop term = Const ("Trueprop", Type("fun",[Type("bool",[]),Type("prop",[])])) $ term; 
	    
(* convert an elim rule into an equivalent formula, of type Term.term. *)
fun elimR2Fol elimR = 
    let val elimR' = Drule.freeze_all elimR
	val (prems,concl) = (prems_of elimR', concl_of elimR')
    in
	case concl of Const("Trueprop",_) $ Free(_,Type("bool",[])) 
		      => trueprop (elimR2Fol_aux prems concl)
                    | Free(x,Type("prop",[])) => trueprop(elimR2Fol_aux prems concl) 
		    | _ => raise ELIMR2FOL("Not an elimination rule!")
    end;



(**** use prove_goalw_cterm to prove ****)

(* convert an elim-rule into an equivalent theorem that does not have the predicate variable. *) 
fun transform_elim thm =
    let val tm = elimR2Fol thm
	val ctm = cterm_of (sign_of_thm thm) tm	
    in
	prove_goalw_cterm [] ctm (fn prems => [elimRule_tac thm])
    end;	


end;



signature RES_AXIOMS =
sig

val clausify_axiom : Thm.thm -> ResClause.clause list
val cnf_axiom : Thm.thm -> Thm.thm list
val meta_cnf_axiom : Thm.thm -> Thm.thm list
val cnf_elim : Thm.thm -> Thm.thm list
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
val claset_rules_of_thy : Theory.theory -> Thm.thm list
val simpset_rules_of_thy : Theory.theory -> (string * Thm.thm) list
val clausify_rules : Thm.thm list -> Thm.thm list -> ResClause.clause list list * Thm.thm list

end;

structure ResAxioms : RES_AXIOMS =
 
struct

open ResElimRule;

(* to be fixed: cnf_intro, cnf_rule, is_introR *)

(* check if a rule is an elim rule *)
fun is_elimR thm = 
    case (concl_of thm) of (Const ("Trueprop", _) $ Var (idx,_)) => true
			 | Var(indx,Type("prop",[])) => true
			 | _ => false;


(* repeated resolution *)
fun repeat_RS thm1 thm2 =
    let val thm1' =  thm1 RS thm2 handle THM _ => thm1
    in
	if eq_thm(thm1,thm1') then thm1' else (repeat_RS thm1' thm2)
    end;


(* convert a theorem into NNF and also skolemize it. *)
fun skolem_axiom thm = 
  if Term.is_first_order (prop_of thm) then
    let val thm' = (skolemize o make_nnf o ObjectLogic.atomize_thm o Drule.freeze_all) thm
    in 
	repeat_RS thm' someI_ex
    end
  else raise THM ("skolem_axiom: not first-order", 0, [thm]);


fun cnf_rule thm = make_clauses [skolem_axiom thm]

fun cnf_elim thm = cnf_rule (transform_elim thm);


(*Transfer a theorem in to theory Reconstruction.thy if it is not already
  inside that theory -- because it's needed for Skolemization *)

val recon_thy = ThyInfo.get_theory"Reconstruction";

fun transfer_to_Reconstruction thm =
    transfer recon_thy thm handle THM _ => thm;

fun is_taut th =
      case (prop_of th) of
           (Const ("Trueprop", _) $ Const ("True", _)) => true
         | _ => false;

(* remove tautologous clauses *)
val rm_redundant_cls = List.filter (not o is_taut);

(* transform an Isabelle thm into CNF *)
fun cnf_axiom_aux thm =
    let val thm' = transfer_to_Reconstruction thm
	val thm'' = if (is_elimR thm') then (cnf_elim thm')  else cnf_rule thm'
    in
	map (zero_var_indexes o Thm.varifyT) (rm_redundant_cls thm'')
    end;
    
(*Cache for clauses: could be a hash table if we provided them.*)
val clause_cache = ref (Symtab.empty : (thm * thm list) Symtab.table)

fun cnf_axiom th =
    case Thm.name_of_thm th of
	  "" => cnf_axiom_aux th (*no name, so can't cache*)
	| s  => case Symtab.lookup (!clause_cache,s) of
	  	  NONE => 
		    let val cls = cnf_axiom_aux th
		    in  clause_cache := Symtab.update ((s, (th,cls)), !clause_cache); cls
		    end
	        | SOME(th',cls) =>
		    if eq_thm(th,th') then cls
		    else (*New theorem stored under the same name? Possible??*)
		      let val cls = cnf_axiom_aux th
		      in  clause_cache := Symtab.update ((s, (th,cls)), !clause_cache); cls
		      end;

fun meta_cnf_axiom thm = 
    map Meson.make_meta_clause (cnf_axiom thm);


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


fun sk_lookup [] t = NONE
  | sk_lookup ((tm,sk_tm)::tms) t = if (t = tm) then SOME (sk_tm) else (sk_lookup tms t);



(* get the proper skolem term to replace epsilon term *)
fun get_skolem epss t = 
    let val sk_fun = sk_lookup epss t
    in
	case sk_fun of NONE => get_new_skolem epss t
		     | SOME sk => (sk,epss)
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


(* remove the epsilon terms in a formula, by skolem terms. *)
fun rm_Eps _ [] = []
  | rm_Eps epss (thm::thms) = 
    let val (thm',epss') = rm_Eps_cls epss thm
    in
	thm' :: (rm_Eps epss' thms)
    end;



(* changed, now it also finds out the name of the theorem. *)
(* convert a theorem into CNF and then into Clause.clause format. *)
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
  

(**** Extract and Clausify theorems from a theory's claset and simpset ****)

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
    let val rules = #rules(fst (rep_ss (simpset_of thy)))
    in
	map (fn (_,r) => (#name r, #thm r)) (Net.dest rules)
    end;


(**** Translate a set of classical/simplifier rules into CNF (still as type "thm")  ****)

(* classical rules *)
fun cnf_rules [] err_list = ([],err_list)
  | cnf_rules (thm::thms) err_list = 
      let val (ts,es) = cnf_rules thms err_list
      in  (cnf_axiom thm :: ts,es) handle  _ => (ts,(thm::es))  end;


(* CNF all rules from a given theory's classical reasoner *)
fun cnf_classical_rules_thy thy = 
    cnf_rules (claset_rules_of_thy thy) [];

(* CNF all simplifier rules from a given theory's simpset *)
fun cnf_simpset_rules_thy thy =
    cnf_rules (map #2 (simpset_rules_of_thy thy)) [];


(**** Convert all theorems of a claset/simpset into clauses (ResClause.clause) ****)

(* classical rules *)
fun clausify_rules [] err_list = ([],err_list)
  | clausify_rules (thm::thms) err_list =
    let val (ts,es) = clausify_rules thms err_list
    in
	((clausify_axiom thm)::ts,es) handle  _ => (ts,(thm::es))
    end;


(* convert all classical rules from a given theory into Clause.clause format. *)
fun clausify_classical_rules_thy thy =
    clausify_rules (claset_rules_of_thy thy) [];

(* convert all simplifier rules from a given theory into Clause.clause format. *)
fun clausify_simpset_rules_thy thy =
    clausify_rules (map #2 (simpset_rules_of_thy thy)) [];


end; 
