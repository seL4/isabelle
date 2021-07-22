(*  Title:      HOL/Tools/Meson/meson_clausify.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen

Transformation of HOL theorems into CNF forms.
*)

signature MESON_CLAUSIFY =
sig
  val new_skolem_var_prefix : string
  val new_nonskolem_var_prefix : string
  val is_zapped_var_name : string -> bool
  val is_quasi_lambda_free : term -> bool
  val introduce_combinators_in_cterm : Proof.context -> cterm -> thm
  val introduce_combinators_in_theorem : Proof.context -> thm -> thm
  val cluster_of_zapped_var_name : string -> (int * (int * int)) * bool
  val ss_only : thm list -> Proof.context -> Proof.context
  val cnf_axiom : Meson.simp_options -> Proof.context -> bool -> bool -> int -> thm
    -> (thm * term) option * thm list
end;

structure Meson_Clausify : MESON_CLAUSIFY =
struct

(* the extra "Meson" helps prevent clashes (FIXME) *)
val new_skolem_var_prefix = "MesonSK"
val new_nonskolem_var_prefix = "MesonV"

fun is_zapped_var_name s =
  exists (fn prefix => String.isPrefix prefix s)
         [new_skolem_var_prefix, new_nonskolem_var_prefix]

(**** Transformation of Elimination Rules into First-Order Formulas****)

val cfalse = Thm.cterm_of \<^theory_context>\<open>HOL\<close> \<^term>\<open>False\<close>;
val ctp_false = Thm.cterm_of \<^theory_context>\<open>HOL\<close> (HOLogic.mk_Trueprop \<^term>\<open>False\<close>);

(* Converts an elim-rule into an equivalent theorem that does not have the
   predicate variable. Leaves other theorems unchanged. We simply instantiate
   the conclusion variable to False. (Cf. "transform_elim_prop" in
   "Sledgehammer_Util".) *)
fun transform_elim_theorem th =
  (case Thm.concl_of th of    (*conclusion variable*)
    \<^const>\<open>Trueprop\<close> $ (Var (v as (_, \<^typ>\<open>bool\<close>))) =>
      Thm.instantiate ([], [(v, cfalse)]) th
  | Var (v as (_, \<^typ>\<open>prop\<close>)) =>
      Thm.instantiate ([], [(v, ctp_false)]) th
  | _ => th)


(**** SKOLEMIZATION BY INFERENCE (lcp) ****)

fun mk_old_skolem_term_wrapper t =
  let val T = fastype_of t in
    Const (\<^const_name>\<open>Meson.skolem\<close>, T --> T) $ t
  end

fun beta_eta_in_abs_body (Abs (s, T, t')) = Abs (s, T, beta_eta_in_abs_body t')
  | beta_eta_in_abs_body t = Envir.beta_eta_contract t

(*Traverse a theorem, accumulating Skolem function definitions.*)
fun old_skolem_defs th =
  let
    fun dec_sko (Const (\<^const_name>\<open>Ex\<close>, _) $ (body as Abs (_, T, p))) rhss =
        (*Existential: declare a Skolem function, then insert into body and continue*)
        let
          val args = Misc_Legacy.term_frees body
          (* Forms a lambda-abstraction over the formal parameters *)
          val rhs =
            fold_rev (absfree o dest_Free) args
              (HOLogic.choice_const T $ beta_eta_in_abs_body body)
            |> mk_old_skolem_term_wrapper
          val comb = list_comb (rhs, args)
        in dec_sko (subst_bound (comb, p)) (rhs :: rhss) end
      | dec_sko (Const (\<^const_name>\<open>All\<close>,_) $ Abs (a, T, p)) rhss =
        (*Universal quant: insert a free variable into body and continue*)
        let val fname = singleton (Name.variant_list (Misc_Legacy.add_term_names (p, []))) a
        in dec_sko (subst_bound (Free(fname,T), p)) rhss end
      | dec_sko (\<^const>\<open>conj\<close> $ p $ q) rhss = rhss |> dec_sko p |> dec_sko q
      | dec_sko (\<^const>\<open>disj\<close> $ p $ q) rhss = rhss |> dec_sko p |> dec_sko q
      | dec_sko (\<^const>\<open>Trueprop\<close> $ p) rhss = dec_sko p rhss
      | dec_sko _ rhss = rhss
  in  dec_sko (Thm.prop_of th) []  end;


(**** REPLACING ABSTRACTIONS BY COMBINATORS ****)

fun is_quasi_lambda_free (Const (\<^const_name>\<open>Meson.skolem\<close>, _) $ _) = true
  | is_quasi_lambda_free (t1 $ t2) =
    is_quasi_lambda_free t1 andalso is_quasi_lambda_free t2
  | is_quasi_lambda_free (Abs _) = false
  | is_quasi_lambda_free _ = true

fun abstract ctxt ct =
  let
      val Abs (_, _, body) = Thm.term_of ct
      val (x, cbody) = Thm.dest_abs NONE ct
      val (A, cbodyT) = Thm.dest_funT (Thm.ctyp_of_cterm ct)
      fun makeK () = Thm.instantiate' [SOME A, SOME cbodyT] [SOME cbody] @{thm abs_K}
  in
      case body of
          Const _ => makeK()
        | Free _ => makeK()
        | Var _ => makeK()  (*though Var isn't expected*)
        | Bound 0 => Thm.instantiate' [SOME A] [] @{thm abs_I} (*identity: I*)
        | rator$rand =>
            if Term.is_dependent rator then (*C or S*)
               if Term.is_dependent rand then (*S*)
                 let val crator = Thm.lambda x (Thm.dest_fun cbody)
                     val crand = Thm.lambda x (Thm.dest_arg cbody)
                     val (C, B) = Thm.dest_funT (Thm.dest_ctyp1 (Thm.ctyp_of_cterm crator))
                     val abs_S' = @{thm abs_S}
                       |> instantiate'_normalize [SOME A, SOME B, SOME C] [SOME crator, SOME crand]
                     val (_,rhs) = Thm.dest_equals (Thm.cprop_of abs_S')
                 in
                   Thm.transitive abs_S' (Conv.binop_conv (abstract ctxt) rhs)
                 end
               else (*C*)
                 let val crator = Thm.lambda x (Thm.dest_fun cbody)
                     val crand = Thm.dest_arg cbody
                     val (C, B) = Thm.dest_funT (Thm.dest_ctyp1 (Thm.ctyp_of_cterm crator))
                     val abs_C' = @{thm abs_C}
                       |> instantiate'_normalize [SOME A, SOME B, SOME C] [SOME crator, SOME crand]
                     val (_,rhs) = Thm.dest_equals (Thm.cprop_of abs_C')
                 in
                   Thm.transitive abs_C' (Conv.fun_conv (Conv.arg_conv (abstract ctxt)) rhs)
                 end
            else if Term.is_dependent rand then (*B or eta*)
               if rand = Bound 0 then Thm.eta_conversion ct
               else (*B*)
                 let val crator = Thm.dest_fun cbody
                     val crand = Thm.lambda x (Thm.dest_arg cbody)
                     val (C, B) = Thm.dest_funT (Thm.ctyp_of_cterm crator)
                     val abs_B' = @{thm abs_B}
                      |> instantiate'_normalize [SOME A, SOME B, SOME C] [SOME crator, SOME crand]
                     val (_,rhs) = Thm.dest_equals (Thm.cprop_of abs_B')
                 in Thm.transitive abs_B' (Conv.arg_conv (abstract ctxt) rhs) end
            else makeK ()
        | _ => raise Fail "abstract: Bad term"
  end;

(* Traverse a theorem, remplacing lambda-abstractions with combinators. *)
fun introduce_combinators_in_cterm ctxt ct =
  if is_quasi_lambda_free (Thm.term_of ct) then
    Thm.reflexive ct
  else case Thm.term_of ct of
    Abs _ =>
    let
      val (cv, cta) = Thm.dest_abs NONE ct
      val (v, _) = dest_Free (Thm.term_of cv)
      val u_th = introduce_combinators_in_cterm ctxt cta
      val cu = Thm.rhs_of u_th
      val comb_eq = abstract ctxt (Thm.lambda cv cu)
    in Thm.transitive (Thm.abstract_rule v cv u_th) comb_eq end
  | _ $ _ =>
    let val (ct1, ct2) = Thm.dest_comb ct in
        Thm.combination (introduce_combinators_in_cterm ctxt ct1)
                        (introduce_combinators_in_cterm ctxt ct2)
    end

fun introduce_combinators_in_theorem ctxt th =
  if is_quasi_lambda_free (Thm.prop_of th) then
    th
  else
    let
      val th = Drule.eta_contraction_rule th
      val eqth = introduce_combinators_in_cterm ctxt (Thm.cprop_of th)
    in Thm.equal_elim eqth th end
    handle THM (msg, _, _) =>
           (warning ("Error in the combinator translation of " ^ Thm.string_of_thm ctxt th ^
              "\nException message: " ^ msg);
            (* A type variable of sort "{}" will make "abstraction" fail. *)
            TrueI)

(*cterms are used throughout for efficiency*)
val cTrueprop = Thm.cterm_of \<^theory_context>\<open>HOL\<close> HOLogic.Trueprop;

(*Given an abstraction over n variables, replace the bound variables by free
  ones. Return the body, along with the list of free variables.*)
fun c_variant_abs_multi (ct0, vars) =
      let val (cv,ct) = Thm.dest_abs NONE ct0
      in  c_variant_abs_multi (ct, cv::vars)  end
      handle CTERM _ => (ct0, rev vars);

(* Given the definition of a Skolem function, return a theorem to replace
   an existential formula by a use of that function.
   Example: "EX x. x : A & x ~: B ==> sko A B : A & sko A B ~: B"  [.] *)
fun old_skolem_theorem_of_def ctxt rhs0 =
  let
    val rhs = rhs0 |> Type.legacy_freeze_thaw |> #1 |> Thm.cterm_of ctxt
    val rhs' = rhs |> Thm.dest_comb |> snd
    val (ch, frees) = c_variant_abs_multi (rhs', [])
    val (hilbert, cabs) = ch |> Thm.dest_comb |>> Thm.term_of
    val T =
      case hilbert of
        Const (_, Type (\<^type_name>\<open>fun\<close>, [_, T])) => T
      | _ => raise TERM ("old_skolem_theorem_of_def: expected \"Eps\"", [hilbert])
    val cex = Thm.cterm_of ctxt (HOLogic.exists_const T)
    val ex_tm = Thm.apply cTrueprop (Thm.apply cex cabs)
    val conc =
      Drule.list_comb (rhs, frees)
      |> Drule.beta_conv cabs |> Thm.apply cTrueprop
    fun tacf [prem] =
      rewrite_goals_tac ctxt @{thms skolem_def [abs_def]}
      THEN resolve_tac ctxt
        [(prem |> rewrite_rule ctxt @{thms skolem_def [abs_def]})
          RS Global_Theory.get_thm (Proof_Context.theory_of ctxt) "Hilbert_Choice.someI_ex"] 1
  in
    Goal.prove_internal ctxt [ex_tm] conc tacf
    |> forall_intr_list frees
    |> Thm.forall_elim_vars 0  (*Introduce Vars, but don't discharge defs.*)
    |> Thm.varifyT_global
  end

fun to_definitional_cnf_with_quantifiers ctxt th =
  let
    val eqth = CNF.make_cnfx_thm ctxt (HOLogic.dest_Trueprop (Thm.prop_of th))
    val eqth = eqth RS @{thm eq_reflection}
    val eqth = eqth RS @{thm TruepropI}
  in Thm.equal_elim eqth th end

fun zapped_var_name ((ax_no, cluster_no), skolem) index_no s =
  (if skolem then new_skolem_var_prefix else new_nonskolem_var_prefix) ^
  "_" ^ string_of_int ax_no ^ "_" ^ string_of_int cluster_no ^ "_" ^
  string_of_int index_no ^ "_" ^ Name.desymbolize (SOME false) s

fun cluster_of_zapped_var_name s =
  let val get_int = the o Int.fromString o nth (space_explode "_" s) in
    ((get_int 1, (get_int 2, get_int 3)),
     String.isPrefix new_skolem_var_prefix s)
  end

fun rename_bound_vars_to_be_zapped ax_no =
  let
    fun aux (cluster as (cluster_no, cluster_skolem)) index_no pos t =
      case t of
        (t1 as Const (s, _)) $ Abs (s', T, t') =>
        if s = \<^const_name>\<open>Pure.all\<close> orelse s = \<^const_name>\<open>All\<close> orelse
           s = \<^const_name>\<open>Ex\<close> then
          let
            val skolem = (pos = (s = \<^const_name>\<open>Ex\<close>))
            val (cluster, index_no) =
              if skolem = cluster_skolem then (cluster, index_no)
              else ((cluster_no ||> cluster_skolem ? Integer.add 1, skolem), 0)
            val s' = zapped_var_name cluster index_no s'
          in t1 $ Abs (s', T, aux cluster (index_no + 1) pos t') end
        else
          t
      | (t1 as Const (s, _)) $ t2 $ t3 =>
        if s = \<^const_name>\<open>Pure.imp\<close> orelse s = \<^const_name>\<open>HOL.implies\<close> then
          t1 $ aux cluster index_no (not pos) t2 $ aux cluster index_no pos t3
        else if s = \<^const_name>\<open>HOL.conj\<close> orelse
                s = \<^const_name>\<open>HOL.disj\<close> then
          t1 $ aux cluster index_no pos t2 $ aux cluster index_no pos t3
        else
          t
      | (t1 as Const (s, _)) $ t2 =>
        if s = \<^const_name>\<open>Trueprop\<close> then
          t1 $ aux cluster index_no pos t2
        else if s = \<^const_name>\<open>Not\<close> then
          t1 $ aux cluster index_no (not pos) t2
        else
          t
      | _ => t
  in aux ((ax_no, 0), true) 0 true end

fun zap pos ct =
  ct
  |> (case Thm.term_of ct of
        Const (s, _) $ Abs (s', _, _) =>
        if s = \<^const_name>\<open>Pure.all\<close> orelse s = \<^const_name>\<open>All\<close> orelse
           s = \<^const_name>\<open>Ex\<close> then
          Thm.dest_comb #> snd #> Thm.dest_abs (SOME s') #> snd #> zap pos
        else
          Conv.all_conv
      | Const (s, _) $ _ $ _ =>
        if s = \<^const_name>\<open>Pure.imp\<close> orelse s = \<^const_name>\<open>implies\<close> then
          Conv.combination_conv (Conv.arg_conv (zap (not pos))) (zap pos)
        else if s = \<^const_name>\<open>conj\<close> orelse s = \<^const_name>\<open>disj\<close> then
          Conv.combination_conv (Conv.arg_conv (zap pos)) (zap pos)
        else
          Conv.all_conv
      | Const (s, _) $ _ =>
        if s = \<^const_name>\<open>Trueprop\<close> then Conv.arg_conv (zap pos)
        else if s = \<^const_name>\<open>Not\<close> then Conv.arg_conv (zap (not pos))
        else Conv.all_conv
      | _ => Conv.all_conv)

fun ss_only ths ctxt = clear_simpset (put_simpset HOL_basic_ss ctxt) addsimps ths

val cheat_choice =
  \<^prop>\<open>\<forall>x. \<exists>y. Q x y \<Longrightarrow> \<exists>f. \<forall>x. Q x (f x)\<close>
  |> Logic.varify_global
  |> Skip_Proof.make_thm \<^theory>

(* Converts an Isabelle theorem into NNF. *)
fun nnf_axiom simp_options choice_ths new_skolem ax_no th ctxt =
  let
    val thy = Proof_Context.theory_of ctxt
    val th =
      th |> transform_elim_theorem
         |> zero_var_indexes
         |> new_skolem ? forall_intr_vars
    val (th, ctxt) = Variable.import true [th] ctxt |>> snd |>> the_single
    val th = th |> Conv.fconv_rule (Object_Logic.atomize ctxt)
                |> Meson.cong_extensionalize_thm ctxt
                |> Meson.abs_extensionalize_thm ctxt
                |> Meson.make_nnf simp_options ctxt
  in
    if new_skolem then
      let
        fun skolemize choice_ths =
          Meson.skolemize_with_choice_theorems simp_options ctxt choice_ths
          #> simplify (ss_only @{thms all_simps[symmetric]} ctxt)
        val no_choice = null choice_ths
        val pull_out =
          if no_choice then
            simplify (ss_only @{thms all_simps[symmetric] ex_simps[symmetric]} ctxt)
          else
            skolemize choice_ths
        val discharger_th = th |> pull_out
        val discharger_th =
          discharger_th |> Meson.has_too_many_clauses ctxt (Thm.concl_of discharger_th)
                           ? (to_definitional_cnf_with_quantifiers ctxt
                              #> pull_out)
        val zapped_th =
          discharger_th |> Thm.prop_of |> rename_bound_vars_to_be_zapped ax_no
          |> (if no_choice then
                Skip_Proof.make_thm thy #> skolemize [cheat_choice] #> Thm.cprop_of
              else
                Thm.cterm_of ctxt)
          |> zap true
        val fixes =
          [] |> Term.add_free_names (Thm.prop_of zapped_th)
             |> filter is_zapped_var_name
        val ctxt' = ctxt |> Variable.add_fixes_direct fixes
        val fully_skolemized_t =
          zapped_th |> singleton (Variable.export ctxt' ctxt)
                    |> Thm.cprop_of |> Thm.dest_equals |> snd |> Thm.term_of
      in
        if exists_subterm (fn Var ((s, _), _) =>
                              String.isPrefix new_skolem_var_prefix s
                            | _ => false) fully_skolemized_t then
          let
            val (fully_skolemized_ct, ctxt) =
              yield_singleton (Variable.import_terms true) fully_skolemized_t ctxt
              |>> Thm.cterm_of ctxt
          in
            (SOME (discharger_th, fully_skolemized_ct),
             (Thm.assume fully_skolemized_ct, ctxt))
          end
       else
         (NONE, (th, ctxt))
      end
    else
      (NONE, (th |> Meson.has_too_many_clauses ctxt (Thm.concl_of th)
                    ? to_definitional_cnf_with_quantifiers ctxt, ctxt))
  end

(* Convert a theorem to CNF, with additional premises due to skolemization. *)
fun cnf_axiom simp_options ctxt0 new_skolem combinators ax_no th =
  let
    val choice_ths = Meson.choice_theorems (Proof_Context.theory_of ctxt0)
    val (opt, (nnf_th, ctxt1)) =
      nnf_axiom simp_options choice_ths new_skolem ax_no th ctxt0
    fun clausify th =
      Meson.make_cnf
       (if new_skolem orelse null choice_ths then []
        else map (old_skolem_theorem_of_def ctxt1) (old_skolem_defs th))
       th ctxt1
    val (cnf_ths, ctxt2) = clausify nnf_th
    fun intr_imp ct th =
      Thm.instantiate ([], [((("i", 0), \<^typ>\<open>nat\<close>), Thm.cterm_of ctxt2 (HOLogic.mk_nat ax_no))])
                      (zero_var_indexes @{thm skolem_COMBK_D})
      RS Thm.implies_intr ct th
  in
    (opt |> Option.map (I #>> singleton (Variable.export ctxt2 ctxt0)
                        ##> (Thm.term_of #> HOLogic.dest_Trueprop
                             #> singleton (Variable.export_terms ctxt2 ctxt0))),
     cnf_ths |> map (combinators ? introduce_combinators_in_theorem ctxt2
                     #> (case opt of SOME (_, ct) => intr_imp ct | NONE => I))
             |> Variable.export ctxt2 ctxt0
             |> Meson.finish_cnf
             |> map (Thm.close_derivation \<^here>))
  end
  handle THM _ => (NONE, [])

end;
