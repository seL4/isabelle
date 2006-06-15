(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

Transformation of axiom rules (elim/intro/etc) into CNF forms.    
*)

signature RES_AXIOMS =
  sig
  exception ELIMR2FOL of string
  val tagging_enabled : bool
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
  val cnf_rules_pairs : (string * Thm.thm) list -> (Thm.thm * (string * int)) list list;
  val meson_method_setup : theory -> theory
  val setup : theory -> theory

  val atpset_rules_of_thy : theory -> (string * thm) list
  val atpset_rules_of_ctxt : Proof.context -> (string * thm) list
  end;

structure ResAxioms : RES_AXIOMS =
 
struct


val tagging_enabled = false (*compile_time option*)

(**** Transformation of Elimination Rules into First-Order Formulas****)

(* a tactic used to prove an elim-rule. *)
fun elimRule_tac th =
    ((rtac impI 1) ORELSE (rtac notI 1)) THEN (etac th 1) THEN
    REPEAT(fast_tac HOL_cs 1);

exception ELIMR2FOL of string;

fun add_EX tm [] = tm
  | add_EX tm ((x,xtp)::xs) = add_EX (HOLogic.exists_const xtp $ Abs(x,xtp,tm)) xs;

(*Checks for the premise ~P when the conclusion is P.*)
fun is_neg (Const("Trueprop",_) $ (Const("Not",_) $ Free(p,_))) 
           (Const("Trueprop",_) $ Free(q,_)) = (p = q)
  | is_neg _ _ = false;

(*FIXME: What if dest_Trueprop fails?*)
fun strip_concl' prems bvs (Const ("==>",_) $ P $ Q) =
      strip_concl' (HOLogic.dest_Trueprop P :: prems) bvs  Q
  | strip_concl' prems bvs P = 
      let val P' = HOLogic.Not $ (HOLogic.dest_Trueprop P)
      in add_EX (foldr1 HOLogic.mk_conj (P'::prems)) bvs end;

fun strip_concl prems bvs concl (Const ("all", _) $ Abs (x,xtp,body)) = 
      strip_concl prems ((x,xtp)::bvs) concl body
  | strip_concl prems bvs concl (Const ("==>",_) $ P $ Q) =
      if (is_neg P concl) then (strip_concl' prems bvs Q)
      else strip_concl (HOLogic.dest_Trueprop P::prems) bvs  concl Q
  | strip_concl prems bvs concl _ = add_EX (foldr1 HOLogic.mk_conj prems) bvs;
 
fun trans_elim (major,minors,concl) =
    let val disjs = foldr1 HOLogic.mk_disj (map (strip_concl [] [] concl) minors)
    in
	HOLogic.mk_imp (HOLogic.dest_Trueprop major, disjs)
    end;

(* convert an elim rule into an equivalent formula, of type term. *)
fun elimR2Fol elimR = 
  let val elimR' = Drule.freeze_all elimR
      val (prems,concl) = (prems_of elimR', concl_of elimR')
      val _ = case concl of 
		  Const("Trueprop",_) $ Free(_,Type("bool",[])) => ()
		| Free(_, Type("prop",[])) => ()
		| _ => raise ELIMR2FOL "elimR2Fol: Not an elimination rule!"
      val th = case prems of
      		  [] => raise ELIMR2FOL "elimR2Fol: No premises!"
      		| [major] => HOLogic.Not $ (HOLogic.dest_Trueprop major)
      		| major::minors => trans_elim (major, minors, concl)
  in HOLogic.mk_Trueprop th end
  handle exn => 
    (warning ("elimR2Fol raised exception " ^ Toplevel.exn_message exn);
     concl_of elimR);

(* check if a rule is an elim rule *)
fun is_elimR th = 
    case concl_of th of Const ("Trueprop", _) $ Var _ => true
		      | Var(_,Type("prop",[])) => true
		      | _ => false;

(* convert an elim-rule into an equivalent theorem that does not have the 
   predicate variable.  Leave other theorems unchanged.*) 
fun transform_elim th =
  if is_elimR th then
    let val ctm = cterm_of (sign_of_thm th) (elimR2Fol th)
    in Goal.prove_raw [] ctm (fn _ => elimRule_tac th) end
    handle exn => (warning ("transform_elim failed: " ^ Toplevel.exn_message exn ^ 
                            " for theorem " ^ string_of_thm th); th)
 else th;


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
  let fun dec_sko (Const ("Ex",_) $ (xtp as Abs(_,T,p))) (n, (thy, axs)) =
	    (*Existential: declare a Skolem function, then insert into body and continue*)
	    let val cname = s ^ "_" ^ Int.toString n
		val args = term_frees xtp  (*get the formal parameter list*)
		val Ts = map type_of args
		val cT = Ts ---> T
		val c = Const (Sign.full_name thy cname, cT)
		val rhs = list_abs_free (map dest_Free args, HOLogic.choice_const T $ xtp)
		        (*Forms a lambda-abstraction over the formal parameters*)
		val def = equals cT $ c $ rhs
		val thy' = Theory.add_consts_i [(cname, cT, NoSyn)] thy
		           (*Theory is augmented with the constant, then its def*)
		val cdef = cname ^ "_def"
		val thy'' = Theory.add_defs_i false false [(cdef, def)] thy'
	    in dec_sko (subst_bound (list_comb(c,args), p)) 
	               (n+1, (thy'', get_axiom thy'' cdef :: axs)) 
	    end
	| dec_sko (Const ("All",_) $ (xtp as Abs(a,T,p))) (n, thx) =
	    (*Universal quant: insert a free variable into body and continue*)
	    let val fname = variant (add_term_names (p,[])) a
	    in dec_sko (subst_bound (Free(fname,T), p)) (n, thx) end
	| dec_sko (Const ("op &", _) $ p $ q) nthy = dec_sko q (dec_sko p nthy)
	| dec_sko (Const ("op |", _) $ p $ q) nthy = dec_sko q (dec_sko p nthy)
	| dec_sko (Const ("HOL.tag", _) $ p) nthy = dec_sko p nthy
	| dec_sko (Const ("Trueprop", _) $ p) nthy = dec_sko p nthy
	| dec_sko t nthx = nthx (*Do nothing otherwise*)
  in  #2 (dec_sko (#prop (rep_thm th)) (1, (thy,[])))  end;

(*Traverse a theorem, accumulating Skolem function definitions.*)
fun assume_skofuns th =
  let fun dec_sko (Const ("Ex",_) $ (xtp as Abs(_,T,p))) defs =
	    (*Existential: declare a Skolem function, then insert into body and continue*)
	    let val name = variant (add_term_names (p,[])) (gensym "sko_")
                val skos = map (#1 o Logic.dest_equals) defs  (*existing sko fns*)
		val args = term_frees xtp \\ skos  (*the formal parameters*)
		val Ts = map type_of args
		val cT = Ts ---> T
		val c = Free (name, cT)
		val rhs = list_abs_free (map dest_Free args,        
		                         HOLogic.choice_const T $ xtp)
		      (*Forms a lambda-abstraction over the formal parameters*)
		val def = equals cT $ c $ rhs
	    in dec_sko (subst_bound (list_comb(c,args), p)) 
	               (def :: defs)
	    end
	| dec_sko (Const ("All",_) $ (xtp as Abs(a,T,p))) defs =
	    (*Universal quant: insert a free variable into body and continue*)
	    let val fname = variant (add_term_names (p,[])) a
	    in dec_sko (subst_bound (Free(fname,T), p)) defs end
	| dec_sko (Const ("op &", _) $ p $ q) defs = dec_sko q (dec_sko p defs)
	| dec_sko (Const ("op |", _) $ p $ q) defs = dec_sko q (dec_sko p defs)
	| dec_sko (Const ("HOL.tag", _) $ p) defs = dec_sko p defs
	| dec_sko (Const ("Trueprop", _) $ p) defs = dec_sko p defs
	| dec_sko t defs = defs (*Do nothing otherwise*)
  in  dec_sko (#prop (rep_thm th)) []  end;

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
  let val (c,rhs) = Drule.dest_equals (cprop_of (Drule.freeze_all def))
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
       |> transform_elim |> Drule.freeze_all
       |> ObjectLogic.atomize_thm |> make_nnf;

(*The cache prevents repeated clausification of a theorem, 
  and also repeated declaration of Skolem functions*)  
  (* FIXME better use Termtab!? No, we MUST use theory data!!*)
val clause_cache = ref (Symtab.empty : (thm * thm list) Symtab.table)


(*Generate Skolem functions for a theorem supplied in nnf*)
fun skolem_of_nnf th =
  map (skolem_of_def o assume o (cterm_of (theory_of_thm th))) (assume_skofuns th);

(*Skolemize a named theorem, with Skolem functions as additional premises.*)
(*also works for HOL*) 
fun skolem_thm th = 
  let val nnfth = to_nnf th
  in  rm_redundant_cls (Meson.make_cnf (skolem_of_nnf nnfth) nnfth)
  end
  handle THM _ => [];

(*Declare Skolem functions for a theorem, supplied in nnf and with its name.
  It returns a modified theory, unless skolemization fails.*)
fun skolem thy (name,th) =
  let val cname = (case name of "" => gensym "sko" | s => Sign.base_name s)
  in Option.map 
        (fn nnfth => 
          let val (thy',defs) = declare_skofuns cname nnfth thy
              val skoths = map skolem_of_def defs
          in (thy', rm_redundant_cls (Meson.make_cnf skoths nnfth)) end)
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

(*Tags identify the major premise or conclusion, as hints to resolution provers.
  However, they don't appear to help in recent tests, and they complicate the code.*)
val tagI = thm "tagI";
val tagD = thm "tagD";

val tag_intro = preserve_name (fn th => th RS tagI);
val tag_elim  = preserve_name (fn th => tagD RS th);

fun rules_of_claset cs =
  let val {safeIs,safeEs,hazIs,hazEs,...} = rep_cs cs
      val intros = safeIs @ hazIs
      val elims  = map Classical.classical_rule (safeEs @ hazEs)
  in
     Output.debug ("rules_of_claset intros: " ^ Int.toString(length intros) ^ 
            " elims: " ^ Int.toString(length elims));
     if tagging_enabled 
     then map pairname (map tag_intro intros @ map tag_elim elims)
     else map pairname (intros @ elims)
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

(*These should include any plausibly-useful theorems, especially if they need
  Skolem functions. FIXME: this list is VERY INCOMPLETE*)
val default_initial_thms = map pairname
  [refl_def, antisym_def, sym_def, trans_def, single_valued_def,
   subset_refl, Union_least, Inter_greatest];

(*Setup function: takes a theory and installs ALL simprules and claset rules 
  into the clause cache*)
fun clause_cache_setup thy =
  let val simps = simpset_rules_of_thy thy
      and clas  = claset_rules_of_thy thy
      and thy0  = List.foldl skolem_cache thy default_initial_thms
      val thy1  = List.foldl skolem_cache thy0 clas
  in List.foldl skolem_cache thy1 simps end;
(*Could be duplicate theorem names, due to multiple attributes*)
  

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

fun skolem (Context.Theory thy, th) =
      let
        val name = Thm.name_of_thm th
        val (cls, thy') = skolem_cache_thm ((name, th), thy)
      in (Context.Theory thy', conj_rule cls) end
  | skolem (context, th) = (context, conj_rule (skolem_thm th));

val setup_attrs = Attrib.add_attributes
  [("skolem", Attrib.no_args skolem, "skolemization of a theorem")];

val setup = clause_cache_setup #> setup_attrs;

end; 
