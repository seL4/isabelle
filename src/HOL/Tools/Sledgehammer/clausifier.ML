(*  Title:      HOL/Tools/Sledgehammer/clausifier.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen

Transformation of axiom rules (elim/intro/etc) into CNF forms.
*)

signature CLAUSIFIER =
sig
  val extensionalize_theorem : thm -> thm
  val introduce_combinators_in_cterm : cterm -> thm
  val introduce_combinators_in_theorem : thm -> thm
  val to_definitional_cnf_with_quantifiers : theory -> thm -> thm
  val cnf_axiom : theory -> thm -> thm list
end;

structure Clausifier : CLAUSIFIER =
struct

(**** Transformation of Elimination Rules into First-Order Formulas****)

val cfalse = cterm_of @{theory HOL} HOLogic.false_const;
val ctp_false = cterm_of @{theory HOL} (HOLogic.mk_Trueprop HOLogic.false_const);

(* Converts an elim-rule into an equivalent theorem that does not have the
   predicate variable. Leaves other theorems unchanged. We simply instantiate
   the conclusion variable to False. (Cf. "transform_elim_term" in
   "Sledgehammer_Util".) *)
fun transform_elim_theorem th =
  case concl_of th of    (*conclusion variable*)
       @{const Trueprop} $ (v as Var (_, @{typ bool})) =>
           Thm.instantiate ([], [(cterm_of @{theory HOL} v, cfalse)]) th
    | v as Var(_, @{typ prop}) =>
           Thm.instantiate ([], [(cterm_of @{theory HOL} v, ctp_false)]) th
    | _ => th


(**** SKOLEMIZATION BY INFERENCE (lcp) ****)

fun mk_skolem t =
  let val T = fastype_of t in
    Const (@{const_name skolem}, T --> T) $ t
  end

fun beta_eta_under_lambdas (Abs (s, T, t')) =
    Abs (s, T, beta_eta_under_lambdas t')
  | beta_eta_under_lambdas t = Envir.beta_eta_contract t

(*Traverse a theorem, accumulating Skolem function definitions.*)
fun assume_skolem_funs th =
  let
    fun dec_sko (Const (@{const_name Ex}, _) $ (body as Abs (_, T, p))) rhss =
        (*Existential: declare a Skolem function, then insert into body and continue*)
        let
          val args = OldTerm.term_frees body
          (* Forms a lambda-abstraction over the formal parameters *)
          val rhs =
            list_abs_free (map dest_Free args,
                           HOLogic.choice_const T $ beta_eta_under_lambdas body)
            |> mk_skolem
          val comb = list_comb (rhs, args)
        in dec_sko (subst_bound (comb, p)) (rhs :: rhss) end
      | dec_sko (Const (@{const_name All},_) $ Abs (a, T, p)) rhss =
        (*Universal quant: insert a free variable into body and continue*)
        let val fname = Name.variant (OldTerm.add_term_names (p,[])) a
        in dec_sko (subst_bound (Free(fname,T), p)) rhss end
      | dec_sko (@{const HOL.conj} $ p $ q) rhss = rhss |> dec_sko p |> dec_sko q
      | dec_sko (@{const HOL.disj} $ p $ q) rhss = rhss |> dec_sko p |> dec_sko q
      | dec_sko (@{const Trueprop} $ p) rhss = dec_sko p rhss
      | dec_sko _ rhss = rhss
  in  dec_sko (prop_of th) []  end;


(**** REPLACING ABSTRACTIONS BY COMBINATORS ****)

val fun_cong_all = @{thm fun_eq_iff [THEN iffD1]}

(* Removes the lambdas from an equation of the form "t = (%x. u)".
   (Cf. "extensionalize_term" in "Sledgehammer_Translate".) *)
fun extensionalize_theorem th =
  case prop_of th of
    _ $ (Const (@{const_name HOL.eq}, Type (_, [Type (@{type_name fun}, _), _]))
         $ _ $ Abs _) => extensionalize_theorem (th RS fun_cong_all)
  | _ => th

fun is_quasi_lambda_free (Const (@{const_name skolem}, _) $ _) = true
  | is_quasi_lambda_free (t1 $ t2) =
    is_quasi_lambda_free t1 andalso is_quasi_lambda_free t2
  | is_quasi_lambda_free (Abs _) = false
  | is_quasi_lambda_free _ = true

val [f_B,g_B] = map (cterm_of @{theory}) (OldTerm.term_vars (prop_of @{thm abs_B}));
val [g_C,f_C] = map (cterm_of @{theory}) (OldTerm.term_vars (prop_of @{thm abs_C}));
val [f_S,g_S] = map (cterm_of @{theory}) (OldTerm.term_vars (prop_of @{thm abs_S}));

(* FIXME: Requires more use of cterm constructors. *)
fun abstract ct =
  let
      val thy = theory_of_cterm ct
      val Abs(x,_,body) = term_of ct
      val Type(@{type_name fun}, [xT,bodyT]) = typ_of (ctyp_of_term ct)
      val cxT = ctyp_of thy xT
      val cbodyT = ctyp_of thy bodyT
      fun makeK () =
        instantiate' [SOME cxT, SOME cbodyT] [SOME (cterm_of thy body)]
                     @{thm abs_K}
  in
      case body of
          Const _ => makeK()
        | Free _ => makeK()
        | Var _ => makeK()  (*though Var isn't expected*)
        | Bound 0 => instantiate' [SOME cxT] [] @{thm abs_I} (*identity: I*)
        | rator$rand =>
            if loose_bvar1 (rator,0) then (*C or S*)
               if loose_bvar1 (rand,0) then (*S*)
                 let val crator = cterm_of thy (Abs(x,xT,rator))
                     val crand = cterm_of thy (Abs(x,xT,rand))
                     val abs_S' = cterm_instantiate [(f_S,crator),(g_S,crand)] @{thm abs_S}
                     val (_,rhs) = Thm.dest_equals (cprop_of abs_S')
                 in
                   Thm.transitive abs_S' (Conv.binop_conv abstract rhs)
                 end
               else (*C*)
                 let val crator = cterm_of thy (Abs(x,xT,rator))
                     val abs_C' = cterm_instantiate [(f_C,crator),(g_C,cterm_of thy rand)] @{thm abs_C}
                     val (_,rhs) = Thm.dest_equals (cprop_of abs_C')
                 in
                   Thm.transitive abs_C' (Conv.fun_conv (Conv.arg_conv abstract) rhs)
                 end
            else if loose_bvar1 (rand,0) then (*B or eta*)
               if rand = Bound 0 then Thm.eta_conversion ct
               else (*B*)
                 let val crand = cterm_of thy (Abs(x,xT,rand))
                     val crator = cterm_of thy rator
                     val abs_B' = cterm_instantiate [(f_B,crator),(g_B,crand)] @{thm abs_B}
                     val (_,rhs) = Thm.dest_equals (cprop_of abs_B')
                 in Thm.transitive abs_B' (Conv.arg_conv abstract rhs) end
            else makeK()
        | _ => raise Fail "abstract: Bad term"
  end;

(* Traverse a theorem, remplacing lambda-abstractions with combinators. *)
fun introduce_combinators_in_cterm ct =
  if is_quasi_lambda_free (term_of ct) then
    Thm.reflexive ct
  else case term_of ct of
    Abs _ =>
    let
      val (cv, cta) = Thm.dest_abs NONE ct
      val (v, _) = dest_Free (term_of cv)
      val u_th = introduce_combinators_in_cterm cta
      val cu = Thm.rhs_of u_th
      val comb_eq = abstract (Thm.cabs cv cu)
    in Thm.transitive (Thm.abstract_rule v cv u_th) comb_eq end
  | _ $ _ =>
    let val (ct1, ct2) = Thm.dest_comb ct in
        Thm.combination (introduce_combinators_in_cterm ct1)
                        (introduce_combinators_in_cterm ct2)
    end

fun introduce_combinators_in_theorem th =
  if is_quasi_lambda_free (prop_of th) then
    th
  else
    let
      val th = Drule.eta_contraction_rule th
      val eqth = introduce_combinators_in_cterm (cprop_of th)
    in Thm.equal_elim eqth th end
    handle THM (msg, _, _) =>
           (warning ("Error in the combinator translation of " ^
                     Display.string_of_thm_without_context th ^
                     "\nException message: " ^ msg ^ ".");
            (* A type variable of sort "{}" will make abstraction fail. *)
            TrueI)

(*cterms are used throughout for efficiency*)
val cTrueprop = cterm_of @{theory HOL} HOLogic.Trueprop;

(*Given an abstraction over n variables, replace the bound variables by free
  ones. Return the body, along with the list of free variables.*)
fun c_variant_abs_multi (ct0, vars) =
      let val (cv,ct) = Thm.dest_abs NONE ct0
      in  c_variant_abs_multi (ct, cv::vars)  end
      handle CTERM _ => (ct0, rev vars);

val skolem_def_raw = @{thms skolem_def_raw}

(* Given the definition of a Skolem function, return a theorem to replace
   an existential formula by a use of that function.
   Example: "EX x. x : A & x ~: B ==> sko A B : A & sko A B ~: B"  [.] *)
fun skolem_theorem_of_def thy rhs0 =
  let
    val rhs = rhs0 |> Type.legacy_freeze_thaw |> #1 |> cterm_of thy
    val rhs' = rhs |> Thm.dest_comb |> snd
    val (ch, frees) = c_variant_abs_multi (rhs', [])
    val (hilbert, cabs) = ch |> Thm.dest_comb |>> term_of
    val T =
      case hilbert of
        Const (@{const_name Eps}, Type (@{type_name fun}, [_, T])) => T
      | _ => raise TERM ("skolem_theorem_of_def: expected \"Eps\"", [hilbert])
    val cex = cterm_of thy (HOLogic.exists_const T)
    val ex_tm = Thm.capply cTrueprop (Thm.capply cex cabs)
    val conc =
      Drule.list_comb (rhs, frees)
      |> Drule.beta_conv cabs |> Thm.capply cTrueprop
    fun tacf [prem] =
      rewrite_goals_tac skolem_def_raw
      THEN rtac ((prem |> rewrite_rule skolem_def_raw) RS @{thm someI_ex}) 1
  in
    Goal.prove_internal [ex_tm] conc tacf
    |> forall_intr_list frees
    |> Thm.forall_elim_vars 0  (*Introduce Vars, but don't discharge defs.*)
    |> Thm.varifyT_global
  end

(* Converts an Isabelle theorem (intro, elim or simp format, even higher-order)
   into NNF. *)
fun to_nnf th ctxt0 =
  let
    val th1 = th |> transform_elim_theorem |> zero_var_indexes
    val ((_, [th2]), ctxt) = Variable.import true [th1] ctxt0
    val th3 = th2 |> Conv.fconv_rule Object_Logic.atomize
                  |> extensionalize_theorem
                  |> Meson.make_nnf ctxt
  in (th3, ctxt) end

fun to_definitional_cnf_with_quantifiers thy th =
  let
    val eqth = cnf.make_cnfx_thm thy (HOLogic.dest_Trueprop (prop_of th))
    val eqth = eqth RS @{thm eq_reflection}
    val eqth = eqth RS @{thm TruepropI}
  in Thm.equal_elim eqth th end

(* Convert a theorem to CNF, with Skolem functions as additional premises. *)
fun cnf_axiom thy th =
  let
    val ctxt0 = Variable.global_thm_context th
    val (nnf_th, ctxt) = to_nnf th ctxt0
    fun aux th =
      Meson.make_cnf (map (skolem_theorem_of_def thy) (assume_skolem_funs th))
                     th ctxt
    val (cnf_ths, ctxt) =
      aux nnf_th
      |> (fn ([], _) => aux (to_definitional_cnf_with_quantifiers thy nnf_th)
           | p => p)
  in
    cnf_ths |> map introduce_combinators_in_theorem
            |> Variable.export ctxt ctxt0
            |> Meson.finish_cnf
            |> map Thm.close_derivation
  end
  handle THM _ => []

end;
