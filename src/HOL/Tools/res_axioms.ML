(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

Transformation of axiom rules (elim/intro/etc) into CNF forms.    
*)

signature RES_AXIOMS =
  sig
  exception ELIMR2FOL of string
  val elimRule_tac : thm -> Tactical.tactic
  val elimR2Fol : thm -> term
  val transform_elim : thm -> thm
  val clausify_axiom_pairs : (string*thm) -> (ResClause.clause*thm) list
  val cnf_axiom : (string * thm) -> thm list
  val meta_cnf_axiom : thm -> thm list
  val cnf_rule : thm -> thm list
  val cnf_rules : (string*thm) list -> thm list -> thm list list * thm list
  val rm_Eps : (term * term) list -> thm list -> term list
  val claset_rules_of_thy : theory -> (string * thm) list
  val simpset_rules_of_thy : theory -> (string * thm) list
  val clausify_rules_pairs : (string * thm) list -> thm list -> (ResClause.clause * thm) list list * thm list
  val clause_setup : (theory -> theory) list
  val meson_method_setup : (theory -> theory) list
  end;

structure ResAxioms : RES_AXIOMS =
 
struct

(**** Transformation of Elimination Rules into First-Order Formulas****)

(* a tactic used to prove an elim-rule. *)
fun elimRule_tac th =
    ((rtac impI 1) ORELSE (rtac notI 1)) THEN (etac th 1) THEN
    REPEAT(fast_tac HOL_cs 1);

exception ELIMR2FOL of string;

(* functions used to construct a formula *)

fun make_disjs [x] = x
  | make_disjs (x :: xs) = HOLogic.mk_disj(x, make_disjs xs)

fun make_conjs [x] = x
  | make_conjs (x :: xs) =  HOLogic.mk_conj(x, make_conjs xs)

fun add_EX tm [] = tm
  | add_EX tm ((x,xtp)::xs) = add_EX (HOLogic.exists_const xtp $ Abs(x,xtp,tm)) xs;



fun is_neg (Const("Trueprop",_) $ (Const("Not",_) $ Free(p,_))) (Const("Trueprop",_) $ Free(q,_)) = (p = q)
  | is_neg _ _ = false;


exception STRIP_CONCL;


fun strip_concl' prems bvs (Const ("==>",_) $ P $ Q) =
      let val P' = HOLogic.dest_Trueprop P
  	  val prems' = P'::prems
      in
	strip_concl' prems' bvs  Q
      end
  | strip_concl' prems bvs P = 
      let val P' = HOLogic.Not $ (HOLogic.dest_Trueprop P)
      in
	add_EX (make_conjs (P'::prems)) bvs
      end;


fun strip_concl prems bvs concl (Const ("all", _) $ Abs (x,xtp,body))  = strip_concl prems ((x,xtp)::bvs) concl body
  | strip_concl prems bvs concl (Const ("==>",_) $ P $ Q) =
    if (is_neg P concl) then (strip_concl' prems bvs Q)
    else
	(let val P' = HOLogic.dest_Trueprop P
	     val prems' = P'::prems
	 in
	     strip_concl prems' bvs  concl Q
	 end)
  | strip_concl prems bvs concl _ = add_EX (make_conjs prems) bvs;
 


fun trans_elim (main,others,concl) =
    let val others' = map (strip_concl [] [] concl) others
	val disjs = make_disjs others'
    in
	HOLogic.mk_imp (HOLogic.dest_Trueprop main, disjs)
    end;


(* aux function of elim2Fol, take away predicate variable. *)
fun elimR2Fol_aux prems concl = 
    let val nprems = length prems
	val main = hd prems
    in
	if (nprems = 1) then HOLogic.Not $ (HOLogic.dest_Trueprop main)
        else trans_elim (main, tl prems, concl)
    end;

    
(* convert an elim rule into an equivalent formula, of type term. *)
fun elimR2Fol elimR = 
    let val elimR' = Drule.freeze_all elimR
	val (prems,concl) = (prems_of elimR', concl_of elimR')
    in
	case concl of Const("Trueprop",_) $ Free(_,Type("bool",[])) 
		      => HOLogic.mk_Trueprop (elimR2Fol_aux prems concl)
                    | Free(x,Type("prop",[])) => HOLogic.mk_Trueprop(elimR2Fol_aux prems concl) 
		    | _ => raise ELIMR2FOL("Not an elimination rule!")
    end;


(* check if a rule is an elim rule *)
fun is_elimR th = 
    case (concl_of th) of (Const ("Trueprop", _) $ Var (idx,_)) => true
			 | Var(indx,Type("prop",[])) => true
			 | _ => false;

(* convert an elim-rule into an equivalent theorem that does not have the 
   predicate variable.  Leave other theorems unchanged.*) 
fun transform_elim th =
  if is_elimR th then
    let val tm = elimR2Fol th
	val ctm = cterm_of (sign_of_thm th) tm	
    in
	prove_goalw_cterm [] ctm (fn prems => [elimRule_tac th])
    end
 else th;


(**** Transformation of Clasets and Simpsets into First-Order Axioms ****)

(* to be fixed: cnf_intro, cnf_rule, is_introR *)

(* repeated resolution *)
fun repeat_RS thm1 thm2 =
    let val thm1' =  thm1 RS thm2 handle THM _ => thm1
    in
	if eq_thm(thm1,thm1') then thm1' else (repeat_RS thm1' thm2)
    end;


(*Convert a theorem into NNF and also skolemize it. Original version, using
  Hilbert's epsilon in the resulting clauses.*)
fun skolem_axiom th = 
  let val th' = (skolemize o make_nnf o ObjectLogic.atomize_thm o Drule.freeze_all) th
  in  repeat_RS th' someI_ex
  end;


fun cnf_rule th = make_clauses [skolem_axiom (transform_elim th)];

(*Transfer a theorem into theory Reconstruction.thy if it is not already
  inside that theory -- because it's needed for Skolemization *)

(*This will refer to the final version of theory Reconstruction.*)
val recon_thy_ref = Theory.self_ref (the_context ());  

(*If called while Reconstruction is being created, it will transfer to the
  current version. If called afterward, it will transfer to the final version.*)
fun transfer_to_Reconstruction th =
    transfer (Theory.deref recon_thy_ref) th handle THM _ => th;

fun is_taut th =
      case (prop_of th) of
           (Const ("Trueprop", _) $ Const ("True", _)) => true
         | _ => false;

(* remove tautologous clauses *)
val rm_redundant_cls = List.filter (not o is_taut);

(* transform an Isabelle thm into CNF *)
fun cnf_axiom_aux th =
    map zero_var_indexes
        (rm_redundant_cls (cnf_rule (transfer_to_Reconstruction th)));
       
       
(**** SKOLEMIZATION BY INFERENCE (lcp) ****)

(*Traverse a term, accumulating Skolem function definitions.*)
fun declare_skofuns s t thy =
  let fun dec_sko (Const ("Ex",_) $ (xtp as Abs(_,T,p))) (n, thy) =
	    (*Existential: declare a Skolem function, then insert into body and continue*)
	    let val cname = s ^ "_" ^ Int.toString n
		val args = term_frees xtp  (*get the formal parameter list*)
		val Ts = map type_of args
		val cT = Ts ---> T
		val c = Const (Sign.full_name (Theory.sign_of thy) cname, cT)
		val rhs = list_abs_free (map dest_Free args, HOLogic.choice_const T $ xtp)
		        (*Forms a lambda-abstraction over the formal parameters*)
		val def = equals cT $ c $ rhs
		val thy' = Theory.add_consts_i [(cname, cT, NoSyn)] thy
		           (*Theory is augmented with the constant, then its def*)
		val thy'' = Theory.add_defs_i false [(cname ^ "_def", def)] thy'
	    in dec_sko (subst_bound (list_comb(c,args), p)) (n+1, thy'') end
	| dec_sko (Const ("All",_) $ (xtp as Abs(a,T,p))) (n, thy) =
	    (*Universal quant: insert a free variable into body and continue*)
	    let val fname = variant (add_term_names (p,[])) a
	    in dec_sko (subst_bound (Free(fname,T), p)) (n, thy) end
	| dec_sko (Const ("op &", _) $ p $ q) nthy = 
	    dec_sko q (dec_sko p nthy)
	| dec_sko (Const ("op |", _) $ p $ q) nthy = 
	    dec_sko q (dec_sko p nthy)
	| dec_sko (Const ("Trueprop", _) $ p) nthy = 
	    dec_sko p nthy
	| dec_sko t (n,thy) = (n,thy) (*Do nothing otherwise*)
  in  #2 (dec_sko t (1,thy))  end;

(*cterms are used throughout for efficiency*)
val cTrueprop = Thm.cterm_of (Theory.sign_of HOL.thy) HOLogic.Trueprop;

(*cterm version of mk_cTrueprop*)
fun c_mkTrueprop A = Thm.capply cTrueprop A;

(*Given an abstraction over n variables, replace the bound variables by free
  ones. Return the body, along with the list of free variables.*)
fun c_variant_abs_multi (ct0, vars) = 
      let val (cv,ct) = Thm.dest_abs NONE ct0
      in  c_variant_abs_multi (ct, cv::vars)  end
      handle CTERM _ => (ct0, rev vars);

(*Given the definition of a Skolem function, return a theorem to replace 
  an existential formula by a use of that function.*)
fun skolem_of_def def =  
  let val (c,rhs) = Drule.dest_equals (cprop_of (Drule.freeze_all def))
      val (ch, frees) = c_variant_abs_multi (rhs, [])
      val (chil,cabs) = Thm.dest_comb ch
      val {sign,t, ...} = rep_cterm chil
      val (Const ("Hilbert_Choice.Eps", Type("fun",[_,T]))) = t
      val cex = Thm.cterm_of sign (HOLogic.exists_const T)
      val ex_tm = c_mkTrueprop (Thm.capply cex cabs)
      and conc =  c_mkTrueprop (Drule.beta_conv cabs (Drule.list_comb(c,frees)));
  in  prove_goalw_cterm [def] (Drule.mk_implies (ex_tm, conc))
	    (fn [prem] => [ rtac (prem RS someI_ex) 1 ])
  end;	 


(*Converts an Isabelle theorem (intro, elim or simp format) into nnf.*)
fun to_nnf thy th = 
    th |> Thm.transfer thy
       |> transform_elim |> Drule.freeze_all
       |> ObjectLogic.atomize_thm |> make_nnf;

(*The cache prevents repeated clausification of a theorem, 
  and also repeated declaration of Skolem functions*)  (* FIXME better use Termtab!? *)
val clause_cache = ref (Symtab.empty : (thm * thm list) Symtab.table)

(*Declare Skolem functions for a theorem, supplied in nnf and with its name*)
fun skolem thy (name,th) =
  let val cname = (case name of "" => gensym "sko" | s => Sign.base_name s)
      val thy' = declare_skofuns cname (#prop (rep_thm th)) thy
  in (map (skolem_of_def o #2) (axioms_of thy'), thy') end;

(*Populate the clause cache using the supplied theorems*)
fun skolemlist [] thy = thy
  | skolemlist ((name,th)::nths) thy = 
      (case Symtab.lookup (!clause_cache,name) of
	  NONE => 
	    let val (nnfth,ok) = (to_nnf thy th, true)  
	                 handle THM _ => (asm_rl, false)
            in
                if ok then
                    let val (skoths,thy') = skolem thy (name, nnfth)
			val cls = Meson.make_cnf skoths nnfth
		    in  clause_cache := 
		     	  Symtab.update ((name, (th,cls)), !clause_cache);
			skolemlist nths thy'
		    end
		else skolemlist nths thy
            end
	| SOME _ => skolemlist nths thy) (*FIXME: check for duplicate names?*)

(*Exported function to convert Isabelle theorems into axiom clauses*) 
fun cnf_axiom (name,th) =
    case name of
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

fun pairname th = (Thm.name_of_thm th, th);

fun meta_cnf_axiom th = 
    map Meson.make_meta_clause (cnf_axiom (pairname th));


(* changed: with one extra case added *)
fun univ_vars_of_aux (Const ("Hilbert_Choice.Eps",_) $ Abs(_,_,body)) vars =    
      univ_vars_of_aux body vars
  | univ_vars_of_aux (Const ("Ex",_) $ Abs(_,_,body)) vars = 
      univ_vars_of_aux body vars (* EX x. body *)
  | univ_vars_of_aux (P $ Q) vars =
      univ_vars_of_aux Q (univ_vars_of_aux P vars)
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
    case (sk_lookup epss t) of NONE => get_new_skolem epss t
		             | SOME sk => (sk,epss);


fun rm_Eps_cls_aux epss (t as (Const ("Hilbert_Choice.Eps",_) $ Abs(_,_,_))) = 
       get_skolem epss t
  | rm_Eps_cls_aux epss (P $ Q) =
       let val (P',epss') = rm_Eps_cls_aux epss P
	   val (Q',epss'') = rm_Eps_cls_aux epss' Q
       in (P' $ Q',epss'') end
  | rm_Eps_cls_aux epss t = (t,epss);


fun rm_Eps_cls epss th = rm_Eps_cls_aux epss (prop_of th);


(* remove the epsilon terms in a formula, by skolem terms. *)
fun rm_Eps _ [] = []
  | rm_Eps epss (th::thms) = 
      let val (th',epss') = rm_Eps_cls epss th
      in th' :: (rm_Eps epss' thms) end;



(**** Extract and Clausify theorems from a theory's claset and simpset ****)

fun claset_rules_of_thy thy =
    let val clsset = rep_cs (claset_of thy)
	val safeEs = #safeEs clsset
	val safeIs = #safeIs clsset
	val hazEs = #hazEs clsset
	val hazIs = #hazIs clsset
    in
	map pairname (safeEs @ safeIs @ hazEs @ hazIs)
    end;

fun simpset_rules_of_thy thy =
    let val rules = #rules (fst (rep_ss (simpset_of thy)))
    in map (fn r => (#name r, #thm r)) (Net.entries rules) end;


(**** Translate a set of classical/simplifier rules into CNF (still as type "thm")  ****)

(* classical rules *)
fun cnf_rules [] err_list = ([],err_list)
  | cnf_rules ((name,th) :: thms) err_list = 
      let val (ts,es) = cnf_rules thms err_list
      in  (cnf_axiom (name,th) :: ts,es) handle  _ => (ts, (th::es))  end;


(**** Convert all theorems of a claset/simpset into clauses (ResClause.clause) ****)

(* outputs a list of (clause,thm) pairs *)
fun clausify_axiom_pairs (thm_name,thm) =
    let val isa_clauses = cnf_axiom (thm_name,thm) (*"isa_clauses" are already "standard"ed. *)
        val isa_clauses' = rm_Eps [] isa_clauses
        val clauses_n = length isa_clauses
        val thy = theory_of_thm thm
	fun make_axiom_clauses _ [] []= []
	  | make_axiom_clauses i (cls::clss) (cls'::clss') =
	      (ResClause.make_axiom_clause cls (thm_name,i), cls') :: 
	      make_axiom_clauses (i+1) clss clss'
    in
	make_axiom_clauses 0 isa_clauses' isa_clauses		
    end;

fun clausify_rules_pairs [] err_list = ([],err_list)
  | clausify_rules_pairs ((name,thm)::thms) err_list =
      let val (ts,es) = clausify_rules_pairs thms err_list
      in
	  ((clausify_axiom_pairs (name,thm))::ts, es) 
	  handle  _ => (ts, (thm::es))
      end;


(*Setup function: takes a theory and installs ALL simprules and claset rules 
  into the clause cache*)
fun clause_cache_setup thy =
  let val simps = simpset_rules_of_thy thy
      and clas  = claset_rules_of_thy thy
  in skolemlist clas (skolemlist simps thy) end;
  
val clause_setup = [clause_cache_setup];  


(*** meson proof methods ***)

fun cnf_rules_of_ths ths = List.concat (#1 (cnf_rules (map pairname ths) []));

fun meson_meth ths ctxt =
  Method.SIMPLE_METHOD' HEADGOAL
    (CHANGED_PROP o Meson.meson_claset_tac (cnf_rules_of_ths ths) (local_claset_of ctxt));

val meson_method_setup =
 [Method.add_methods
  [("meson", Method.thms_ctxt_args meson_meth, 
    "The MESON resolution proof procedure")]];

end; 
