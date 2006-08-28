(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

Transformation of axiom rules (elim/intro/etc) into CNF forms.    
*)

signature RES_AXIOMS =
  sig
  val elimRule_tac : thm -> Tactical.tactic
  val elimR2Fol : thm -> term
  val transform_elim : thm -> thm
  val cnf_axiom : (string * thm) -> thm list
  val meta_cnf_axiom : thm -> thm list
  val claset_rules_of_thy : theory -> (string * thm) list
  val simpset_rules_of_thy : theory -> (string * thm) list
  val claset_rules_of_ctxt: Proof.context -> (string * thm) list
  val simpset_rules_of_ctxt : Proof.context -> (string * thm) list
  val pairname : thm -> (string * thm)
  val skolem_thm : thm -> thm list
  val to_nnf : thm -> thm
  val cnf_rules_pairs : (string * Thm.thm) list -> (Thm.thm * (string * int)) list list;
  val meson_method_setup : theory -> theory
  val setup : theory -> theory

  val atpset_rules_of_thy : theory -> (string * thm) list
  val atpset_rules_of_ctxt : Proof.context -> (string * thm) list
  end;
 
structure ResAxioms =
 
struct

(*FIXME DELETE: For running the comparison between combinators and abstractions.
  CANNOT be a ref, as the setting is used while Isabelle is built.*)
val abstract_lambdas = true;

val trace_abs = ref false;

(**** Transformation of Elimination Rules into First-Order Formulas****)

(* a tactic used to prove an elim-rule. *)
fun elimRule_tac th =
    (resolve_tac [impI,notI] 1) THEN (etac th 1) THEN REPEAT(fast_tac HOL_cs 1);

fun add_EX tm [] = tm
  | add_EX tm ((x,xtp)::xs) = add_EX (HOLogic.exists_const xtp $ Abs(x,xtp,tm)) xs;

(*Checks for the premise ~P when the conclusion is P.*)
fun is_neg (Const("Trueprop",_) $ (Const("Not",_) $ Free(p,_))) 
           (Const("Trueprop",_) $ Free(q,_)) = (p = q)
  | is_neg _ _ = false;

exception ELIMR2FOL;

(*Handles the case where the dummy "conclusion" variable appears negated in the
  premises, so the final consequent must be kept.*)
fun strip_concl' prems bvs (Const ("==>",_) $ P $ Q) =
      strip_concl' (HOLogic.dest_Trueprop P :: prems) bvs  Q
  | strip_concl' prems bvs P = 
      let val P' = HOLogic.Not $ (HOLogic.dest_Trueprop P)
      in add_EX (foldr1 HOLogic.mk_conj (P'::prems)) bvs end;

(*Recurrsion over the minor premise of an elimination rule. Final consequent
  is ignored, as it is the dummy "conclusion" variable.*)
fun strip_concl prems bvs concl (Const ("all", _) $ Abs (x,xtp,body)) = 
      strip_concl prems ((x,xtp)::bvs) concl body
  | strip_concl prems bvs concl (Const ("==>",_) $ P $ Q) =
      if (is_neg P concl) then (strip_concl' prems bvs Q)
      else strip_concl (HOLogic.dest_Trueprop P::prems) bvs  concl Q
  | strip_concl prems bvs concl Q = 
      if concl aconv Q then add_EX (foldr1 HOLogic.mk_conj prems) bvs
      else raise ELIMR2FOL (*expected conclusion not found!*)
 
fun trans_elim (major,[],_) = HOLogic.Not $ major
  | trans_elim (major,minors,concl) =
      let val disjs = foldr1 HOLogic.mk_disj (map (strip_concl [] [] concl) minors)
      in  HOLogic.mk_imp (major, disjs)  end;

(* convert an elim rule into an equivalent formula, of type term. *)
fun elimR2Fol elimR = 
  let val elimR' = #1 (Drule.freeze_thaw elimR)
      val (prems,concl) = (prems_of elimR', concl_of elimR')
      val cv = case concl of    (*conclusion variable*)
		  Const("Trueprop",_) $ (v as Free(_,Type("bool",[]))) => v
		| v as Free(_, Type("prop",[])) => v
		| _ => raise ELIMR2FOL
  in case prems of
      [] => raise ELIMR2FOL
    | (Const("Trueprop",_) $ major) :: minors => 
        if member (op aconv) (term_frees major) cv then raise ELIMR2FOL
        else (trans_elim (major, minors, concl) handle TERM _ => raise ELIMR2FOL)
    | _ => raise ELIMR2FOL
  end;

(* convert an elim-rule into an equivalent theorem that does not have the 
   predicate variable.  Leave other theorems unchanged.*) 
fun transform_elim th =
    let val ctm = cterm_of (sign_of_thm th) (HOLogic.mk_Trueprop (elimR2Fol th))
    in Goal.prove_raw [] ctm (fn _ => elimRule_tac th) end
    handle ELIMR2FOL => th (*not an elimination rule*)
         | exn => (warning ("transform_elim failed: " ^ Toplevel.exn_message exn ^ 
                            " for theorem " ^ string_of_thm th); th) 


(**** Transformation of Clasets and Simpsets into First-Order Axioms ****)

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
     
       
(**** SKOLEMIZATION BY INFERENCE (lcp) ****)

(*Traverse a theorem, declaring Skolem function definitions. String s is the suggested
  prefix for the Skolem constant. Result is a new theory*)
fun declare_skofuns s th thy =
  let fun dec_sko (Const ("Ex",_) $ (xtp as Abs(_,T,p))) (thy, axs) =
	    (*Existential: declare a Skolem function, then insert into body and continue*)
	    let val cname = gensym ("sko_" ^ s ^ "_")
		val args = term_frees xtp  (*get the formal parameter list*)
		val Ts = map type_of args
		val cT = Ts ---> T
		val c = Const (Sign.full_name thy cname, cT)
		val rhs = list_abs_free (map dest_Free args, HOLogic.choice_const T $ xtp)
		        (*Forms a lambda-abstraction over the formal parameters*)
		val thy' = Theory.add_consts_i [(cname, cT, NoSyn)] thy
		           (*Theory is augmented with the constant, then its def*)
		val cdef = cname ^ "_def"
		val thy'' = Theory.add_defs_i false false [(cdef, equals cT $ c $ rhs)] thy'
	    in dec_sko (subst_bound (list_comb(c,args), p)) 
	               (thy'', get_axiom thy'' cdef :: axs)
	    end
	| dec_sko (Const ("All",_) $ (xtp as Abs(a,T,p))) thx =
	    (*Universal quant: insert a free variable into body and continue*)
	    let val fname = Name.variant (add_term_names (p,[])) a
	    in dec_sko (subst_bound (Free(fname,T), p)) thx end
	| dec_sko (Const ("op &", _) $ p $ q) thx = dec_sko q (dec_sko p thx)
	| dec_sko (Const ("op |", _) $ p $ q) thx = dec_sko q (dec_sko p thx)
	| dec_sko (Const ("Trueprop", _) $ p) thx = dec_sko p thx
	| dec_sko t thx = thx (*Do nothing otherwise*)
  in  dec_sko (prop_of th) (thy,[])  end;

(*Traverse a theorem, accumulating Skolem function definitions.*)
fun assume_skofuns th =
  let fun dec_sko (Const ("Ex",_) $ (xtp as Abs(_,T,p))) defs =
	    (*Existential: declare a Skolem function, then insert into body and continue*)
	    let val skos = map (#1 o Logic.dest_equals) defs  (*existing sko fns*)
		val args = term_frees xtp \\ skos  (*the formal parameters*)
		val Ts = map type_of args
		val cT = Ts ---> T
		val c = Free (gensym "sko_", cT)
		val rhs = list_abs_free (map dest_Free args,        
		                         HOLogic.choice_const T $ xtp)
		      (*Forms a lambda-abstraction over the formal parameters*)
		val def = equals cT $ c $ rhs
	    in dec_sko (subst_bound (list_comb(c,args), p)) 
	               (def :: defs)
	    end
	| dec_sko (Const ("All",_) $ (xtp as Abs(a,T,p))) defs =
	    (*Universal quant: insert a free variable into body and continue*)
	    let val fname = Name.variant (add_term_names (p,[])) a
	    in dec_sko (subst_bound (Free(fname,T), p)) defs end
	| dec_sko (Const ("op &", _) $ p $ q) defs = dec_sko q (dec_sko p defs)
	| dec_sko (Const ("op |", _) $ p $ q) defs = dec_sko q (dec_sko p defs)
	| dec_sko (Const ("Trueprop", _) $ p) defs = dec_sko p defs
	| dec_sko t defs = defs (*Do nothing otherwise*)
  in  dec_sko (prop_of th) []  end;


(**** REPLACING ABSTRACTIONS BY FUNCTION DEFINITIONS ****)

(*Returns the vars of a theorem*)
fun vars_of_thm th =
  map (Thm.cterm_of (Thm.theory_of_thm th) o Var) (Drule.fold_terms Term.add_vars th []);

(*Make a version of fun_cong with a given variable name*)
local
    val fun_cong' = fun_cong RS asm_rl; (*renumber f, g to prevent clashes with (a,0)*)
    val cx = hd (vars_of_thm fun_cong');
    val ty = typ_of (ctyp_of_term cx);
    val thy = Thm.theory_of_thm fun_cong;
    fun mkvar a = cterm_of thy (Var((a,0),ty));
in
fun xfun_cong x = Thm.instantiate ([], [(cx, mkvar x)]) fun_cong'
end;

(*Removes the lambdas from an equation of the form t = (%x. u)*)
fun strip_lambdas th = 
  case prop_of th of
      _ $ (Const ("op =", _) $ _ $ Abs (x,_,_)) => 
          strip_lambdas (#1 (Drule.freeze_thaw (th RS xfun_cong x)))
    | _ => th;

(*Convert meta- to object-equality. Fails for theorems like split_comp_eq, 
  where some types have the empty sort.*)
fun object_eq th = th RS def_imp_eq 
    handle THM _ => error ("Theorem contains empty sort: " ^ string_of_thm th);
  
fun valid_name vs (Free(x,T)) = x mem_string vs
  | valid_name vs _ = false;

(*Contract all eta-redexes in the theorem, lest they give rise to needless abstractions*)
fun eta_conversion_rule th =
  equal_elim (eta_conversion (cprop_of th)) th;
  
fun crhs th =
  case Drule.strip_comb (cprop_of th) of
      (f, [_, rhs]) => 
          (case term_of f of
               Const ("==", _) => rhs
             | _ => raise THM ("crhs", 0, [th]))
    | _ => raise THM ("crhs", 1, [th]);

(*Apply a function definition to an argument, beta-reducing the result.*)
fun beta_comb cf x =
  let val th1 = combination cf (reflexive x)
      val th2 = beta_conversion false (crhs th1)
  in  transitive th1 th2  end;

(*Apply a function definition to arguments, beta-reducing along the way.*)
fun list_combination cf [] = cf
  | list_combination cf (x::xs) = list_combination (beta_comb cf x) xs;

fun list_cabs ([] ,     t) = t
  | list_cabs (v::vars, t) = Thm.cabs v (list_cabs(vars,t));

fun assert_eta_free ct = 
  let val t = term_of ct 
  in if (t aconv Envir.eta_contract t) then ()  
     else error ("Eta redex in term: " ^ string_of_cterm ct)
  end;

(*Traverse a theorem, declaring abstraction function definitions. String s is the suggested
  prefix for the constants. Resulting theory is returned in the first theorem. *)
fun declare_absfuns th =
  let fun abstract thy ct = case term_of ct of
          Abs (_,T,u) =>
	    let val cname = gensym "abs_"
	        val _ = assert_eta_free ct;
		val (cv,cta) = Thm.dest_abs NONE ct
		val v = (#1 o dest_Free o term_of) cv
		val (u'_th,defs) = abstract thy cta
                val cu' = crhs u'_th
		val abs_v_u = lambda (term_of cv) (term_of cu')
		(*get the formal parameters: ALL variables free in the term*)
		val args = term_frees abs_v_u
		val Ts = map type_of args
		val cT = Ts ---> (T --> typ_of (ctyp_of_term cu'))
		val thy = theory_of_thm u'_th
		val c = Const (Sign.full_name thy cname, cT)
		val thy = Theory.add_consts_i [(cname, cT, NoSyn)] thy
		           (*Theory is augmented with the constant, then its def*)
		val rhs = list_abs_free (map dest_Free args, abs_v_u)
		      (*Forms a lambda-abstraction over the formal parameters*)
		val cdef = cname ^ "_def"
		val thy = Theory.add_defs_i false false [(cdef, equals cT $ c $ rhs)] thy		      
		val def = #1 (Drule.freeze_thaw (get_axiom thy cdef))
		val def_args = list_combination def (map (cterm_of thy) args)
	    in (transitive (abstract_rule v cv u'_th) (symmetric def_args), 
	        def :: defs) end
	| (t1$t2) =>
	    let val (ct1,ct2) = Thm.dest_comb ct
	        val (th1,defs1) = abstract thy ct1
		val (th2,defs2) = abstract (theory_of_thm th1) ct2
	    in  (combination th1 th2, defs1@defs2)  end
	| _ => (transfer thy (reflexive ct), [])
      val _ = if !trace_abs then warning (string_of_thm th) else ();
      val (eqth,defs) = abstract (theory_of_thm th) (cprop_of th)
      val ths = equal_elim eqth th ::
                map (forall_intr_vars o strip_lambdas o object_eq) defs
  in  (theory_of_thm eqth, ths)  end;

fun assume_absfuns th =
  let val cterm = cterm_of (Thm.theory_of_thm th)
      fun abstract vs ct = case term_of ct of
          Abs (_,T,u) =>
	    let val (cv,cta) = Thm.dest_abs NONE ct
	        val _ = assert_eta_free ct;
		val v = (#1 o dest_Free o term_of) cv
		val (u'_th,defs) = abstract (v::vs) cta
                val cu' = crhs u'_th
		val abs_v_u = Thm.cabs cv cu'
		(*get the formal parameters: bound variables also present in the term*)
		val args = filter (valid_name vs) (term_frees (term_of abs_v_u))
		val Ts = map type_of args
		val const_ty = Ts ---> (T --> typ_of (ctyp_of_term cu'))
		val c = Free (gensym "abs_", const_ty)
		val rhs = list_cabs (map cterm args, abs_v_u)
		      (*Forms a lambda-abstraction over the formal parameters*)
		val def = assume (Thm.capply (cterm (equals const_ty $ c)) rhs)
		val def_args = list_combination def (map cterm args)
	    in (transitive (abstract_rule v cv u'_th) (symmetric def_args), 
	        def :: defs) end
	| (t1$t2) =>
	    let val (ct1,ct2) = Thm.dest_comb ct
	        val (t1',defs1) = abstract vs ct1
		val (t2',defs2) = abstract vs ct2
	    in  (combination t1' t2', defs1@defs2)  end
	| _ => (reflexive ct, [])
      val (eqth,defs) = abstract [] (cprop_of th)
  in  equal_elim eqth th ::
      map (forall_intr_vars o strip_lambdas o object_eq) defs
  end;


(*cterms are used throughout for efficiency*)
val cTrueprop = Thm.cterm_of HOL.thy HOLogic.Trueprop;

(*cterm version of mk_cTrueprop*)
fun c_mkTrueprop A = Thm.capply cTrueprop A;

(*Given an abstraction over n variables, replace the bound variables by free
  ones. Return the body, along with the list of free variables.*)
fun c_variant_abs_multi (ct0, vars) = 
      let val (cv,ct) = Thm.dest_abs NONE ct0
      in  c_variant_abs_multi (ct, cv::vars)  end
      handle CTERM _ => (ct0, rev vars);

(*Given the definition of a Skolem function, return a theorem to replace 
  an existential formula by a use of that function. 
   Example: "EX x. x : A & x ~: B ==> sko A B : A & sko A B ~: B"  [.] *)
fun skolem_of_def def =  
  let val (c,rhs) = Drule.dest_equals (cprop_of (#1 (Drule.freeze_thaw def)))
      val (ch, frees) = c_variant_abs_multi (rhs, [])
      val (chilbert,cabs) = Thm.dest_comb ch
      val {sign,t, ...} = rep_cterm chilbert
      val T = case t of Const ("Hilbert_Choice.Eps", Type("fun",[_,T])) => T
                      | _ => raise THM ("skolem_of_def: expected Eps", 0, [def])
      val cex = Thm.cterm_of sign (HOLogic.exists_const T)
      val ex_tm = c_mkTrueprop (Thm.capply cex cabs)
      and conc =  c_mkTrueprop (Drule.beta_conv cabs (Drule.list_comb(c,frees)));
      fun tacf [prem] = rewrite_goals_tac [def] THEN rtac (prem RS someI_ex) 1
  in  Goal.prove_raw [ex_tm] conc tacf 
       |> forall_intr_list frees
       |> forall_elim_vars 0  (*Introduce Vars, but don't discharge defs.*)
       |> Thm.varifyT
  end;

(*Converts an Isabelle theorem (intro, elim or simp format) into nnf.*)
(*It now works for HOL too. *)
fun to_nnf th = 
    th |> transfer_to_Reconstruction
       |> transform_elim |> zero_var_indexes |> Drule.freeze_thaw |> #1
       |> ObjectLogic.atomize_thm |> make_nnf;

(*The cache prevents repeated clausification of a theorem, 
  and also repeated declaration of Skolem functions*)  
  (* FIXME better use Termtab!? No, we MUST use theory data!!*)
val clause_cache = ref (Symtab.empty : (thm * thm list) Symtab.table)


(*Generate Skolem functions for a theorem supplied in nnf*)
fun skolem_of_nnf th =
  map (skolem_of_def o assume o (cterm_of (theory_of_thm th))) (assume_skofuns th);

(*Replace lambdas by assumed function definitions in the theorems*)
fun assume_abstract ths =
  if abstract_lambdas then List.concat (map (assume_absfuns o eta_conversion_rule) ths)
  else map eta_conversion_rule ths;

(*Replace lambdas by declared function definitions in the theorems*)
fun declare_abstract' (thy, []) = (thy, [])
  | declare_abstract' (thy, th::ths) =
      let val (thy', th_defs) = 
            th |> zero_var_indexes |> Drule.freeze_thaw |> #1
               |> eta_conversion_rule |> transfer thy |> declare_absfuns
	  val (thy'', ths') = declare_abstract' (thy', ths)
      in  (thy'', th_defs @ ths')  end;

(*FIXME DELETE if we decide to switch to abstractions*)
fun declare_abstract (thy, ths) =
  if abstract_lambdas then declare_abstract' (thy, ths)
  else (thy, map eta_conversion_rule ths);

(*Skolemize a named theorem, with Skolem functions as additional premises.*)
(*also works for HOL*) 
fun skolem_thm th = 
  let val nnfth = to_nnf th
  in  Meson.make_cnf (skolem_of_nnf nnfth) nnfth
      |> assume_abstract |> Meson.finish_cnf |> rm_redundant_cls
  end
  handle THM _ => [];

(*Declare Skolem functions for a theorem, supplied in nnf and with its name.
  It returns a modified theory, unless skolemization fails.*)
fun skolem thy (name,th) =
  let val cname = (case name of "" => gensym "" | s => Sign.base_name s)
      val _ = Output.debug ("skolemizing " ^ name ^ ": ")
  in Option.map 
        (fn nnfth => 
          let val (thy',defs) = declare_skofuns cname nnfth thy
              val cnfs = Meson.make_cnf (map skolem_of_def defs) nnfth
              val (thy'',cnfs') = declare_abstract (thy',cnfs)
          in (thy'', rm_redundant_cls (Meson.finish_cnf cnfs'))
          end)
      (SOME (to_nnf th)  handle THM _ => NONE) 
  end;

(*Populate the clause cache using the supplied theorem. Return the clausal form
  and modified theory.*)
fun skolem_cache_thm ((name,th), thy) = 
  case Symtab.lookup (!clause_cache) name of
      NONE => 
	(case skolem thy (name, Thm.transfer thy th) of
	     NONE => ([th],thy)
	   | SOME (thy',cls) => 
	       (change clause_cache (Symtab.update (name, (th, cls))); (cls,thy')))
    | SOME (th',cls) =>
        if eq_thm(th,th') then (cls,thy)
	else (Output.debug ("skolem_cache: Ignoring variant of theorem " ^ name); 
	      Output.debug (string_of_thm th);
	      Output.debug (string_of_thm th');
	      ([th],thy));
	      
fun skolem_cache ((name,th), thy) = #2 (skolem_cache_thm ((name,th), thy));


(*Exported function to convert Isabelle theorems into axiom clauses*) 
fun cnf_axiom (name,th) =
  case name of
	"" => skolem_thm th (*no name, so can't cache*)
      | s  => case Symtab.lookup (!clause_cache) s of
		NONE => 
		  let val cls = skolem_thm th
		  in change clause_cache (Symtab.update (s, (th, cls))); cls end
	      | SOME(th',cls) =>
		  if eq_thm(th,th') then cls
		  else (Output.debug ("cnf_axiom: duplicate or variant of theorem " ^ name); 
		        Output.debug (string_of_thm th);
		        Output.debug (string_of_thm th');
		        cls);

fun pairname th = (Thm.name_of_thm th, th);

fun meta_cnf_axiom th = 
    map Meson.make_meta_clause (cnf_axiom (pairname th));


(**** Extract and Clausify theorems from a theory's claset and simpset ****)

(*Preserve the name of "th" after the transformation "f"*)
fun preserve_name f th = Thm.name_thm (Thm.name_of_thm th, f th);

fun rules_of_claset cs =
  let val {safeIs,safeEs,hazIs,hazEs,...} = rep_cs cs
      val intros = safeIs @ hazIs
      val elims  = map Classical.classical_rule (safeEs @ hazEs)
  in
     Output.debug ("rules_of_claset intros: " ^ Int.toString(length intros) ^ 
            " elims: " ^ Int.toString(length elims));
     map pairname (intros @ elims)
  end;

fun rules_of_simpset ss =
  let val ({rules,...}, _) = rep_ss ss
      val simps = Net.entries rules
  in 
      Output.debug ("rules_of_simpset: " ^ Int.toString(length simps));
      map (fn r => (#name r, #thm r)) simps
  end;

fun claset_rules_of_thy thy = rules_of_claset (claset_of thy);
fun simpset_rules_of_thy thy = rules_of_simpset (simpset_of thy);

fun atpset_rules_of_thy thy = map pairname (ResAtpSet.atp_rules_of_thy thy);


fun claset_rules_of_ctxt ctxt = rules_of_claset (local_claset_of ctxt);
fun simpset_rules_of_ctxt ctxt = rules_of_simpset (local_simpset_of ctxt);

fun atpset_rules_of_ctxt ctxt = map pairname (ResAtpSet.atp_rules_of_ctxt ctxt);

(**** Translate a set of classical/simplifier rules into CNF (still as type "thm")  ****)

(* classical rules: works for both FOL and HOL *)
fun cnf_rules [] err_list = ([],err_list)
  | cnf_rules ((name,th) :: ths) err_list = 
      let val (ts,es) = cnf_rules ths err_list
      in  (cnf_axiom (name,th) :: ts,es) handle  _ => (ts, (th::es))  end;  

fun pair_name_cls k (n, []) = []
  | pair_name_cls k (n, cls::clss) = (cls, (n,k)) :: pair_name_cls (k+1) (n, clss)
 	    
fun cnf_rules_pairs_aux pairs [] = pairs
  | cnf_rules_pairs_aux pairs ((name,th)::ths) =
      let val pairs' = (pair_name_cls 0 (name, cnf_axiom(name,th))) :: pairs
		       handle THM _ => pairs | ResClause.CLAUSE _ => pairs
			    | ResHolClause.LAM2COMB _ => pairs
      in  cnf_rules_pairs_aux pairs' ths  end;
    
val cnf_rules_pairs = cnf_rules_pairs_aux [];


(**** Convert all theorems of a claset/simpset into clauses (ResClause.clause, or ResHolClause.clause) ****)

(*Setup function: takes a theory and installs ALL known theorems into the clause cache*)
fun clause_cache_setup thy = List.foldl skolem_cache thy (PureThy.all_thms_of thy);
  

(*** meson proof methods ***)

fun cnf_rules_of_ths ths = List.concat (#1 (cnf_rules (map pairname ths) []));

fun meson_meth ths ctxt =
  Method.SIMPLE_METHOD' HEADGOAL
    (CHANGED_PROP o Meson.meson_claset_tac (cnf_rules_of_ths ths) (local_claset_of ctxt));

val meson_method_setup =
  Method.add_methods
    [("meson", Method.thms_ctxt_args meson_meth, 
      "MESON resolution proof procedure")];



(*** The Skolemization attribute ***)

fun conj2_rule (th1,th2) = conjI OF [th1,th2];

(*Conjoin a list of clauses to recreate a single theorem*)
val conj_rule = foldr1 conj2_rule;

fun skolem_attr (Context.Theory thy, th) =
      let val name = Thm.name_of_thm th
          val (cls, thy') = skolem_cache_thm ((name, th), thy)
      in (Context.Theory thy', conj_rule cls) end
  | skolem_attr (context, th) = (context, conj_rule (skolem_thm th));

val setup_attrs = Attrib.add_attributes
  [("skolem", Attrib.no_args skolem_attr, "skolemization of a theorem")];

val setup = clause_cache_setup #> setup_attrs;

end; 
