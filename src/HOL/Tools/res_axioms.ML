(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

Transformation of axiom rules (elim/intro/etc) into CNF forms.
*)

signature RES_AXIOMS =
sig
  val trace_abs: bool ref
  val cnf_axiom : string * thm -> thm list
  val cnf_name : string -> thm list
  val meta_cnf_axiom : thm -> thm list
  val pairname : thm -> string * thm
  val skolem_thm : thm -> thm list
  val to_nnf : thm -> thm
  val cnf_rules_pairs : (string * thm) list -> (thm * (string * int)) list
  val meson_method_setup : theory -> theory
  val setup : theory -> theory
  val assume_abstract_list: thm list -> thm list
  val neg_conjecture_clauses: thm -> int -> thm list * (string * typ) list
  val claset_rules_of: Proof.context -> (string * thm) list   (*FIXME DELETE*)
  val simpset_rules_of: Proof.context -> (string * thm) list  (*FIXME DELETE*)
  val atpset_rules_of: Proof.context -> (string * thm) list
end;

structure ResAxioms =
struct

(*For running the comparison between combinators and abstractions.
  CANNOT be a ref, as the setting is used while Isabelle is built.
  Currently FALSE, i.e. all the "abstraction" code below is unused, but so far
  it seems to be inferior to combinators...*)
val abstract_lambdas = true;

val trace_abs = ref false;

(* FIXME legacy *)
fun freeze_thm th = #1 (Drule.freeze_thaw th);

val lhs_of = #1 o Logic.dest_equals o Thm.prop_of;
val rhs_of = #2 o Logic.dest_equals o Thm.prop_of;


(*Store definitions of abstraction functions, ensuring that identical right-hand
  sides are denoted by the same functions and thereby reducing the need for
  extensionality in proofs.
  FIXME!  Store in theory data!!*)

(*Populate the abstraction cache with common combinators.*)
fun seed th net =
  let val (_,ct) = Thm.dest_abs NONE (Drule.rhs_of th)
      val t = Logic.legacy_varify (term_of ct)
  in  Net.insert_term eq_thm (t, th) net end;
  
val abstraction_cache = ref 
      (seed (thm"ATP_Linkup.I_simp") 
       (seed (thm"ATP_Linkup.B_simp") 
	(seed (thm"ATP_Linkup.K_simp") Net.empty)));


(**** Transformation of Elimination Rules into First-Order Formulas****)

val cfalse = cterm_of HOL.thy HOLogic.false_const;
val ctp_false = cterm_of HOL.thy (HOLogic.mk_Trueprop HOLogic.false_const);

(*Converts an elim-rule into an equivalent theorem that does not have the
  predicate variable.  Leaves other theorems unchanged.  We simply instantiate the
  conclusion variable to False.*)
fun transform_elim th =
  case concl_of th of    (*conclusion variable*)
       Const("Trueprop",_) $ (v as Var(_,Type("bool",[]))) => 
           Thm.instantiate ([], [(cterm_of HOL.thy v, cfalse)]) th
    | v as Var(_, Type("prop",[])) => 
           Thm.instantiate ([], [(cterm_of HOL.thy v, ctp_false)]) th
    | _ => th;

(**** Transformation of Clasets and Simpsets into First-Order Axioms ****)

(*Transfer a theorem into theory ATP_Linkup.thy if it is not already
  inside that theory -- because it's needed for Skolemization *)

(*This will refer to the final version of theory ATP_Linkup.*)
val recon_thy_ref = Theory.self_ref (the_context ());

(*If called while ATP_Linkup is being created, it will transfer to the
  current version. If called afterward, it will transfer to the final version.*)
fun transfer_to_ATP_Linkup th =
    transfer (Theory.deref recon_thy_ref) th handle THM _ => th;


(**** SKOLEMIZATION BY INFERENCE (lcp) ****)

(*Traverse a theorem, declaring Skolem function definitions. String s is the suggested
  prefix for the Skolem constant. Result is a new theory*)
fun declare_skofuns s th thy =
  let val nref = ref 0
      fun dec_sko (Const ("Ex",_) $ (xtp as Abs(_,T,p))) (thy, axs) =
            (*Existential: declare a Skolem function, then insert into body and continue*)
            let val cname = Name.internal (s ^ "_sko" ^ Int.toString (inc nref))
                val args = term_frees xtp  (*get the formal parameter list*)
                val Ts = map type_of args
                val cT = Ts ---> T
                val c = Const (Sign.full_name thy cname, cT)
                val rhs = list_abs_free (map dest_Free args, HOLogic.choice_const T $ xtp)
                        (*Forms a lambda-abstraction over the formal parameters*)
                val thy' = Sign.add_consts_authentic [(cname, cT, NoSyn)] thy
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
  map (Thm.cterm_of (theory_of_thm th) o Var) (Drule.fold_terms Term.add_vars th []);

(*Make a version of fun_cong with a given variable name*)
local
    val fun_cong' = fun_cong RS asm_rl; (*renumber f, g to prevent clashes with (a,0)*)
    val cx = hd (vars_of_thm fun_cong');
    val ty = typ_of (ctyp_of_term cx);
    val thy = theory_of_thm fun_cong;
    fun mkvar a = cterm_of thy (Var((a,0),ty));
in
fun xfun_cong x = Thm.instantiate ([], [(cx, mkvar x)]) fun_cong'
end;

(*Removes the lambdas from an equation of the form t = (%x. u).  A non-negative n,
  serves as an upper bound on how many to remove.*)
fun strip_lambdas 0 th = th
  | strip_lambdas n th = 
      case prop_of th of
	  _ $ (Const ("op =", _) $ _ $ Abs (x,_,_)) =>
	      strip_lambdas (n-1) (freeze_thm (th RS xfun_cong x))
	| _ => th;

(*Convert meta- to object-equality. Fails for theorems like split_comp_eq,
  where some types have the empty sort.*)
val meta_eq_to_obj_eq = thm "meta_eq_to_obj_eq";
fun mk_object_eq th = th RS meta_eq_to_obj_eq
    handle THM _ => error ("Theorem contains empty sort: " ^ string_of_thm th);

(*Apply a function definition to an argument, beta-reducing the result.*)
fun beta_comb cf x =
  let val th1 = combination cf (reflexive x)
      val th2 = beta_conversion false (Drule.rhs_of th1)
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

fun eq_absdef (th1, th2) =
    Context.joinable (theory_of_thm th1, theory_of_thm th2)  andalso
    rhs_of th1 aconv rhs_of th2;

fun lambda_free (Abs _) = false
  | lambda_free (t $ u) = lambda_free t andalso lambda_free u
  | lambda_free _ = true;

fun monomorphic t =
  Term.fold_types (Term.fold_atyps (fn TVar _ => K false | _ => I)) t true;

fun dest_abs_list ct =
  let val (cv,ct') = Thm.dest_abs NONE ct
      val (cvs,cu) = dest_abs_list ct'
  in (cv::cvs, cu) end
  handle CTERM _ => ([],ct);

fun lambda_list [] u = u
  | lambda_list (v::vs) u = lambda v (lambda_list vs u);

fun abstract_rule_list [] [] th = th
  | abstract_rule_list (v::vs) (ct::cts) th = abstract_rule v ct (abstract_rule_list vs cts th)
  | abstract_rule_list _ _ th = raise THM ("abstract_rule_list", 0, [th]);


val Envir.Envir {asol = tenv0, iTs = tyenv0, ...} = Envir.empty 0

(*Does an existing abstraction definition have an RHS that matches the one we need now?
  thy is the current theory, which must extend that of theorem th.*)
fun match_rhs thy t th =
  let val _ = if !trace_abs then warning ("match_rhs: " ^ string_of_cterm (cterm_of thy t) ^ 
                                          " against\n" ^ string_of_thm th) else ();
      val (tyenv,tenv) = Pattern.first_order_match thy (rhs_of th, t) (tyenv0,tenv0)
      val term_insts = map Meson.term_pair_of (Vartab.dest tenv)
      val ct_pairs = if subthy (theory_of_thm th, thy) andalso 
                        forall lambda_free (map #2 term_insts) 
                     then map (pairself (cterm_of thy)) term_insts
                     else raise Pattern.MATCH (*Cannot allow lambdas in the instantiation*)
      fun ctyp2 (ixn, (S, T)) = (ctyp_of thy (TVar (ixn, S)), ctyp_of thy T)
      val th' = cterm_instantiate ct_pairs th
  in  SOME (th, instantiate (map ctyp2 (Vartab.dest tyenv), []) th')  end
  handle _ => NONE;

(*Traverse a theorem, declaring abstraction function definitions. String s is the suggested
  prefix for the constants. Resulting theory is returned in the first theorem. *)
fun declare_absfuns th =
  let fun abstract thy ct =
        if lambda_free (term_of ct) then (transfer thy (reflexive ct), [])
        else
        case term_of ct of
          Abs _ =>
            let val cname = Name.internal (gensym "abs_");
                val _ = assert_eta_free ct;
                val (cvs,cta) = dest_abs_list ct
                val (vs,Tvs) = ListPair.unzip (map (dest_Free o term_of) cvs)
                val _ = if !trace_abs then warning ("Nested lambda: " ^ string_of_cterm cta) else ();
                val (u'_th,defs) = abstract thy cta
                val _ = if !trace_abs then warning ("Returned " ^ string_of_thm u'_th) else ();
                val cu' = Drule.rhs_of u'_th
                val u' = term_of cu'
                val abs_v_u = lambda_list (map term_of cvs) u'
                (*get the formal parameters: ALL variables free in the term*)
                val args = term_frees abs_v_u
                val _ = if !trace_abs then warning (Int.toString (length args) ^ " arguments") else ();
                val rhs = list_abs_free (map dest_Free args, abs_v_u)
                      (*Forms a lambda-abstraction over the formal parameters*)
                val _ = if !trace_abs then warning ("Looking up " ^ string_of_cterm cu') else ();
                val thy = theory_of_thm u'_th
                val (ax,ax',thy) =
                 case List.mapPartial (match_rhs thy abs_v_u) 
                         (Net.match_term (!abstraction_cache) u') of
                     (ax,ax')::_ => 
                       (if !trace_abs then warning ("Re-using axiom " ^ string_of_thm ax) else ();
                        (ax,ax',thy))
                   | [] =>
                      let val _ = if !trace_abs then warning "Lookup was empty" else ();
                          val Ts = map type_of args
                          val cT = Ts ---> (Tvs ---> typ_of (ctyp_of_term cu'))
                          val c = Const (Sign.full_name thy cname, cT)
                          val thy = Sign.add_consts_authentic [(cname, cT, NoSyn)] thy
                                     (*Theory is augmented with the constant,
                                       then its definition*)
                          val cdef = cname ^ "_def"
                          val thy = Theory.add_defs_i false false
                                       [(cdef, equals cT $ c $ rhs)] thy
                          val _ = if !trace_abs then (warning ("Definition is " ^ 
                                                      string_of_thm (get_axiom thy cdef))) 
                                  else ();
                          val ax = get_axiom thy cdef |> freeze_thm
                                     |> mk_object_eq |> strip_lambdas (length args)
                                     |> mk_meta_eq |> Meson.generalize
                          val (_,ax') = Option.valOf (match_rhs thy abs_v_u ax)
                          val _ = if !trace_abs then 
                                    (warning ("Declaring: " ^ string_of_thm ax);
                                     warning ("Instance: " ^ string_of_thm ax')) 
                                  else ();
                          val _ = abstraction_cache := Net.insert_term eq_absdef 
                                            ((Logic.varify u'), ax) (!abstraction_cache)
                            handle Net.INSERT =>
                              raise THM ("declare_absfuns: INSERT", 0, [th,u'_th,ax])
                       in  (ax,ax',thy)  end
            in if !trace_abs then warning ("Lookup result: " ^ string_of_thm ax') else ();
               (transitive (abstract_rule_list vs cvs u'_th) (symmetric ax'), ax::defs) end
        | (t1$t2) =>
            let val (ct1,ct2) = Thm.dest_comb ct
                val (th1,defs1) = abstract thy ct1
                val (th2,defs2) = abstract (theory_of_thm th1) ct2
            in  (combination th1 th2, defs1@defs2)  end
      val _ = if !trace_abs then warning ("declare_absfuns, Abstracting: " ^ string_of_thm th) else ();
      val (eqth,defs) = abstract (theory_of_thm th) (cprop_of th)
      val ths = equal_elim eqth th :: map (strip_lambdas ~1 o mk_object_eq o freeze_thm) defs
      val _ = if !trace_abs then warning ("declare_absfuns, Result: " ^ string_of_thm (hd ths)) else ();
  in  (theory_of_thm eqth, map Drule.eta_contraction_rule ths)  end;

fun name_of def = try (#1 o dest_Free o lhs_of) def;

(*A name is valid provided it isn't the name of a defined abstraction.*)
fun valid_name defs (Free(x,T)) = not (x mem_string (List.mapPartial name_of defs))
  | valid_name defs _ = false;

fun assume_absfuns th =
  let val thy = theory_of_thm th
      val cterm = cterm_of thy
      fun abstract ct =
        if lambda_free (term_of ct) then (reflexive ct, [])
        else
        case term_of ct of
          Abs (_,T,u) =>
            let val _ = assert_eta_free ct;
                val (cvs,cta) = dest_abs_list ct
                val (vs,Tvs) = ListPair.unzip (map (dest_Free o term_of) cvs)
                val (u'_th,defs) = abstract cta
                val cu' = Drule.rhs_of u'_th
                val u' = term_of cu'
                (*Could use Thm.cabs instead of lambda to work at level of cterms*)
                val abs_v_u = lambda_list (map term_of cvs) (term_of cu')
                (*get the formal parameters: free variables not present in the defs
                  (to avoid taking abstraction function names as parameters) *)
                val args = filter (valid_name defs) (term_frees abs_v_u)
                val crhs = list_cabs (map cterm args, cterm abs_v_u)
                      (*Forms a lambda-abstraction over the formal parameters*)
                val rhs = term_of crhs
                val (ax,ax') =
                 case List.mapPartial (match_rhs thy abs_v_u) 
                        (Net.match_term (!abstraction_cache) u') of
                     (ax,ax')::_ => 
                       (if !trace_abs then warning ("Re-using axiom " ^ string_of_thm ax) else ();
                        (ax,ax'))
                   | [] =>
                      let val Ts = map type_of args
                          val const_ty = Ts ---> (Tvs ---> typ_of (ctyp_of_term cu'))
                          val c = Free (gensym "abs_", const_ty)
                          val ax = assume (Thm.capply (cterm (equals const_ty $ c)) crhs)
                                     |> mk_object_eq |> strip_lambdas (length args)
                                     |> mk_meta_eq |> Meson.generalize
                          val (_,ax') = Option.valOf (match_rhs thy abs_v_u ax)
                          val _ = abstraction_cache := Net.insert_term eq_absdef (rhs,ax)
                                    (!abstraction_cache)
                            handle Net.INSERT =>
                              raise THM ("assume_absfuns: INSERT", 0, [th,u'_th,ax])
                      in (ax,ax') end
            in if !trace_abs then warning ("Lookup result: " ^ string_of_thm ax') else ();
               (transitive (abstract_rule_list vs cvs u'_th) (symmetric ax'), ax::defs) end
        | (t1$t2) =>
            let val (ct1,ct2) = Thm.dest_comb ct
                val (t1',defs1) = abstract ct1
                val (t2',defs2) = abstract ct2
            in  (combination t1' t2', defs1@defs2)  end
      val _ = if !trace_abs then warning ("assume_absfuns, Abstracting: " ^ string_of_thm th) else ();
      val (eqth,defs) = abstract (cprop_of th)
      val ths = equal_elim eqth th :: map (strip_lambdas ~1 o mk_object_eq o freeze_thm) defs
      val _ = if !trace_abs then warning ("assume_absfuns, Result: " ^ string_of_thm (hd ths)) else ();
  in  map Drule.eta_contraction_rule ths  end;


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
  let val (c,rhs) = Drule.dest_equals (cprop_of (freeze_thm def))
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

(*Converts an Isabelle theorem (intro, elim or simp format, even higher-order) into NNF.*)
fun to_nnf th =
    th |> transfer_to_ATP_Linkup
       |> transform_elim |> zero_var_indexes |> freeze_thm
       |> ObjectLogic.atomize_thm |> make_nnf |> strip_lambdas ~1;

(*The cache prevents repeated clausification of a theorem,
  and also repeated declaration of Skolem functions*)
  (* FIXME better use Termtab!? No, we MUST use theory data!!*)
val clause_cache = ref (Symtab.empty : (thm * thm list) Symtab.table)


(*Generate Skolem functions for a theorem supplied in nnf*)
fun skolem_of_nnf th =
  map (skolem_of_def o assume o (cterm_of (theory_of_thm th))) (assume_skofuns th);

fun assert_lambda_free ths msg = 
  case filter (not o lambda_free o prop_of) ths of
      [] => ()
     | ths' => error (msg ^ "\n" ^ space_implode "\n" (map string_of_thm ths'));

fun assume_abstract th =
  if lambda_free (prop_of th) then [th]
  else th |> Drule.eta_contraction_rule |> assume_absfuns
          |> tap (fn ths => assert_lambda_free ths "assume_abstract: lambdas")

(*Replace lambdas by assumed function definitions in the theorems*)
fun assume_abstract_list ths =
  if abstract_lambdas then List.concat (map assume_abstract ths)
  else map Drule.eta_contraction_rule ths;

(*Replace lambdas by declared function definitions in the theorems*)
fun declare_abstract' (thy, []) = (thy, [])
  | declare_abstract' (thy, th::ths) =
      let val (thy', th_defs) =
            if lambda_free (prop_of th) then (thy, [th])
            else
                th |> zero_var_indexes |> freeze_thm
                   |> Drule.eta_contraction_rule |> transfer thy |> declare_absfuns
          val _ = assert_lambda_free th_defs "declare_abstract: lambdas"
          val (thy'', ths') = declare_abstract' (thy', ths)
      in  (thy'', th_defs @ ths')  end;

fun declare_abstract (thy, ths) =
  if abstract_lambdas then declare_abstract' (thy, ths)
  else (thy, map Drule.eta_contraction_rule ths);

(*Skolemize a named theorem, with Skolem functions as additional premises.*)
fun skolem_thm th =
  let val nnfth = to_nnf th
  in  Meson.make_cnf (skolem_of_nnf nnfth) nnfth |> assume_abstract_list |> Meson.finish_cnf
  end
  handle THM _ => [];

(*Keep the full complexity of the original name*)
fun flatten_name s = space_implode "_X" (NameSpace.explode s);

(*Declare Skolem functions for a theorem, supplied in nnf and with its name.
  It returns a modified theory, unless skolemization fails.*)
fun skolem thy (name,th) =
  let val cname = (case name of "" => gensym "" | s => flatten_name s)
      val _ = Output.debug (fn () => "skolemizing " ^ name ^ ": ")
  in Option.map
        (fn nnfth =>
          let val (thy',defs) = declare_skofuns cname nnfth thy
              val cnfs = Meson.make_cnf (map skolem_of_def defs) nnfth
              val (thy'',cnfs') = declare_abstract (thy',cnfs)
          in (map Goal.close_result (Meson.finish_cnf cnfs'), thy'')
          end)
      (SOME (to_nnf th)  handle THM _ => NONE)
  end;

(*Populate the clause cache using the supplied theorem. Return the clausal form
  and modified theory.*)
fun skolem_cache_thm (name,th) thy =
  case Symtab.lookup (!clause_cache) name of
      NONE =>
        (case skolem thy (name, Thm.transfer thy th) of
             NONE => ([th],thy)
           | SOME (cls,thy') => 
                 (if null cls then warning ("skolem_cache: empty clause set for " ^ name)
                  else ();
                  change clause_cache (Symtab.update (name, (th, cls))); 
                  (cls,thy')))
    | SOME (th',cls) =>
        if eq_thm(th,th') then (cls,thy)
        else (Output.debug (fn () => "skolem_cache: Ignoring variant of theorem " ^ name);
              Output.debug (fn () => string_of_thm th);
              Output.debug (fn () => string_of_thm th');
              getOpt (skolem thy (name, Thm.transfer thy th), ([th],thy)));

(*Exported function to convert Isabelle theorems into axiom clauses*)
fun cnf_axiom (name,th) =
 (Output.debug (fn () => "cnf_axiom called, theorem name = " ^ name);
  case name of
        "" => skolem_thm th (*no name, so can't cache*)
      | s  => case Symtab.lookup (!clause_cache) s of
                NONE => 
                  let val cls = map Goal.close_result (skolem_thm th)
                  in Output.debug (fn () => "inserted into cache");
                     change clause_cache (Symtab.update (s, (th, cls))); cls 
                  end
              | SOME(th',cls) =>
                  if eq_thm(th,th') then cls
                  else
                    (Output.debug (fn () => "cnf_axiom: duplicate or variant of theorem " ^ name);
                     Output.debug (fn () => string_of_thm th);
                     Output.debug (fn () => string_of_thm th');
                     skolem_thm th)
 );

fun pairname th = (PureThy.get_name_hint th, th);

(*Principally for debugging*)
fun cnf_name s = 
  let val th = thm s
  in cnf_axiom (PureThy.get_name_hint th, th) end;

(**** Extract and Clausify theorems from a theory's claset and simpset ****)

fun rules_of_claset cs =
  let val {safeIs,safeEs,hazIs,hazEs,...} = rep_cs cs
      val intros = safeIs @ hazIs
      val elims  = map Classical.classical_rule (safeEs @ hazEs)
  in
     Output.debug (fn () => "rules_of_claset intros: " ^ Int.toString(length intros) ^
            " elims: " ^ Int.toString(length elims));
     map pairname (intros @ elims)
  end;

fun rules_of_simpset ss =
  let val ({rules,...}, _) = rep_ss ss
      val simps = Net.entries rules
  in
    Output.debug (fn () => "rules_of_simpset: " ^ Int.toString(length simps));
    map (fn r => (#name r, #thm r)) simps
  end;

fun claset_rules_of ctxt = rules_of_claset (local_claset_of ctxt);
fun simpset_rules_of ctxt = rules_of_simpset (local_simpset_of ctxt);

fun atpset_rules_of ctxt = map pairname (ResAtpset.get_atpset ctxt);


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
      let val pairs' = (pair_name_cls 0 (name, cnf_axiom(name,th))) @ pairs
                       handle THM _ => pairs | ResClause.CLAUSE _ => pairs
      in  cnf_rules_pairs_aux pairs' ths  end;

(*The combination of rev and tail recursion preserves the original order*)
fun cnf_rules_pairs l = cnf_rules_pairs_aux [] (rev l);


(**** Convert all theorems of a claset/simpset into clauses (ResClause.clause, or ResHolClause.clause) ****)

(*Setup function: takes a theory and installs ALL known theorems into the clause cache*)

fun skolem_cache (name,th) thy =
  let val prop = Thm.prop_of th
  in
      if lambda_free prop 
         (*Monomorphic theorems can be Skolemized on demand,
           but there are problems with re-use of abstraction functions if we don't
           do them now, even for monomorphic theorems.*)
      then thy  
      else #2 (skolem_cache_thm (name,th) thy)
  end;

(*The cache can be kept smaller by augmenting the condition above with 
    orelse (not abstract_lambdas andalso monomorphic prop).
  However, while this step does not reduce the time needed to build HOL, 
  it doubles the time taken by the first call to the ATP link-up.*)

fun clause_cache_setup thy = fold skolem_cache (PureThy.all_thms_of thy) thy;


(*** meson proof methods ***)

fun skolem_use_cache_thm th =
  case Symtab.lookup (!clause_cache) (PureThy.get_name_hint th) of
      NONE => skolem_thm th
    | SOME (th',cls) =>
        if eq_thm(th,th') then cls else skolem_thm th;

fun cnf_rules_of_ths ths = List.concat (map skolem_use_cache_thm ths);

val meson_method_setup = Method.add_methods
  [("meson", Method.thms_args (fn ths =>
      Method.SIMPLE_METHOD' (CHANGED_PROP o Meson.meson_claset_tac (cnf_rules_of_ths ths) HOL_cs)),
    "MESON resolution proof procedure")];

(** Attribute for converting a theorem into clauses **)

fun meta_cnf_axiom th = map Meson.make_meta_clause (cnf_axiom (pairname th));

fun clausify_rule (th,i) = List.nth (meta_cnf_axiom th, i)

val clausify = Attrib.syntax (Scan.lift Args.nat
  >> (fn i => Thm.rule_attribute (fn _ => fn th => clausify_rule (th, i))));


(*** Converting a subgoal into negated conjecture clauses. ***)

val neg_skolemize_tac = EVERY' [rtac ccontr, ObjectLogic.atomize_tac, skolemize_tac];
val neg_clausify = Meson.finish_cnf o assume_abstract_list o make_clauses;

fun neg_conjecture_clauses st0 n =
  let val st = Seq.hd (neg_skolemize_tac n st0)
      val (params,_,_) = strip_context (Logic.nth_prem (n, Thm.prop_of st))
  in (neg_clausify (Option.valOf (metahyps_thms n st)), params) end;

(*Conversion of a subgoal to conjecture clauses. Each clause has  
  leading !!-bound universal variables, to express generality. *)
val neg_clausify_tac = 
  neg_skolemize_tac THEN' 
  SUBGOAL
    (fn (prop,_) =>
     let val ts = Logic.strip_assums_hyp prop
     in EVERY1 
	 [METAHYPS
	    (fn hyps => 
              (Method.insert_tac
                (map forall_intr_vars (neg_clausify hyps)) 1)),
	  REPEAT_DETERM_N (length ts) o (etac thin_rl)]
     end);

(** The Skolemization attribute **)

fun conj2_rule (th1,th2) = conjI OF [th1,th2];

(*Conjoin a list of theorems to form a single theorem*)
fun conj_rule []  = TrueI
  | conj_rule ths = foldr1 conj2_rule ths;

fun skolem_attr (Context.Theory thy, th) =
      let val name = PureThy.get_name_hint th
          val (cls, thy') = skolem_cache_thm (name, th) thy
      in (Context.Theory thy', conj_rule cls) end
  | skolem_attr (context, th) = (context, conj_rule (skolem_use_cache_thm th));

val setup_attrs = Attrib.add_attributes
  [("skolem", Attrib.no_args skolem_attr, "skolemization of a theorem"),
   ("clausify", clausify, "conversion of theorem to clauses")];

val setup_methods = Method.add_methods
  [("neg_clausify", Method.no_args (Method.SIMPLE_METHOD' neg_clausify_tac), 
    "conversion of goal to conjecture clauses")];
     
val setup = clause_cache_setup #> setup_attrs #> setup_methods;

end;
