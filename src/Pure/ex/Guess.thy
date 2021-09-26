(*  Title:      Pure/ex/Guess.thy
    Author:     Makarius

Improper proof command 'guess': variant of 'obtain' based on tactical result.

  <chain_facts>
  guess x <proof body> <proof end> \<equiv>

  {
    fix thesis
    <chain_facts> have "PROP ?guess"
      apply magic      \<comment> \<open>turn goal into \<open>thesis \<Longrightarrow> #thesis\<close>\<close>
      <proof body>
      apply_end magic  \<comment> \<open>turn final \<open>(\<And>x. P x \<Longrightarrow> thesis) \<Longrightarrow> #thesis\<close> into\<close>
        \<comment> \<open>\<open>#((\<And>x. A x \<Longrightarrow> thesis) \<Longrightarrow> thesis)\<close> which is a finished goal state\<close>
      <proof end>
  }
  fix x assm <<obtain_export>> "A x"
*)

section \<open>Improper proof command 'guess'\<close>

theory Guess
  imports Pure
  keywords "guess" :: prf_script_asm_goal % "proof"
begin

text \<open>
  The @{command guess} is similar to @{command obtain}, but it derives the
  obtained context elements from the course of tactical reasoning in the
  proof. Thus it can considerably obscure the proof: it is provided here as
  \<^emph>\<open>improper\<close> and experimental feature.

  A proof with @{command guess} starts with a fixed goal \<open>thesis\<close>. The
  subsequent refinement steps may turn this to anything of the form
  \<open>\<And>\<^vec>x. \<^vec>A \<^vec>x \<Longrightarrow> thesis\<close>, but without splitting into new
  subgoals. The final goal state is then used as reduction rule for the obtain
  pattern described above. Obtained parameters \<open>\<^vec>x\<close> are marked as
  internal by default, and thus inaccessible in the proof text. The variable
  names and type constraints given as arguments for @{command "guess"} specify
  a prefix of accessible parameters.

  Some examples are in \<^file>\<open>Guess_Examples.thy\<close>.
\<close>

ML \<open>
signature GUESS =
sig
  val guess: (binding * typ option * mixfix) list -> bool -> Proof.state -> Proof.state
  val guess_cmd: (binding * string option * mixfix) list -> bool -> Proof.state -> Proof.state
end;

structure Guess: GUESS =
struct

local

fun unify_params vars thesis_var raw_rule ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val string_of_term = Syntax.string_of_term (Config.put show_types true ctxt);

    fun err msg th = error (msg ^ ":\n" ^ Thm.string_of_thm ctxt th);

    val maxidx = fold (Term.maxidx_typ o snd o fst) vars ~1;
    val rule = Thm.incr_indexes (maxidx + 1) raw_rule;

    val params = Rule_Cases.strip_params (Logic.nth_prem (1, Thm.prop_of rule));
    val m = length vars;
    val n = length params;
    val _ = m <= n orelse err "More variables than parameters in obtained rule" rule;

    fun unify ((x, T), (y, U)) (tyenv, max) = Sign.typ_unify thy (T, U) (tyenv, max)
      handle Type.TUNIFY =>
        err ("Failed to unify variable " ^
          string_of_term (Free (x, Envir.norm_type tyenv T)) ^ " against parameter " ^
          string_of_term (Syntax_Trans.mark_bound_abs (y, Envir.norm_type tyenv U)) ^ " in") rule;
    val (tyenv, _) = fold unify (map #1 vars ~~ take m params)
      (Vartab.empty, Int.max (maxidx, Thm.maxidx_of rule));
    val norm_type = Envir.norm_type tyenv;

    val xs = map (apsnd norm_type o fst) vars;
    val ys = map (apsnd norm_type) (drop m params);
    val ys' = map Name.internal (Name.variant_list (map fst xs) (map fst ys)) ~~ map #2 ys;
    val terms = map (Drule.mk_term o Thm.cterm_of ctxt o Free) (xs @ ys');

    val instT =
      TVars.build
        (params |> fold (#2 #> Term.fold_atyps (fn T => fn instT =>
          (case T of
            TVar v =>
              if TVars.defined instT v then instT
              else TVars.add (v, Thm.ctyp_of ctxt (norm_type T)) instT
          | _ => instT))));
    val closed_rule = rule
      |> Thm.forall_intr (Thm.cterm_of ctxt (Free thesis_var))
      |> Thm.instantiate (instT, Vars.empty);

    val ((_, rule' :: terms'), ctxt') = Variable.import false (closed_rule :: terms) ctxt;
    val vars' =
      map (dest_Free o Thm.term_of o Drule.dest_term) terms' ~~
      (map snd vars @ replicate (length ys) NoSyn);
    val rule'' = Thm.forall_elim (Thm.cterm_of ctxt' (Logic.varify_global (Free thesis_var))) rule';
  in ((vars', rule''), ctxt') end;

fun inferred_type (binding, _, mx) ctxt =
  let
    val x = Variable.check_name binding;
    val ((_, T), ctxt') = Proof_Context.inferred_param x ctxt
  in ((x, T, mx), ctxt') end;

fun polymorphic ctxt vars =
  let val Ts = map Logic.dest_type (Variable.polymorphic ctxt (map (Logic.mk_type o #2) vars))
  in map2 (fn (x, _, mx) => fn T => ((x, T), mx)) vars Ts end;

fun gen_guess prep_var raw_vars int state =
  let
    val _ = Proof.assert_forward_or_chain state;
    val ctxt = Proof.context_of state;
    val chain_facts = if can Proof.assert_chain state then Proof.the_facts state else [];

    val (thesis_var, thesis) = #1 (Obtain.obtain_thesis ctxt);
    val vars = ctxt
      |> fold_map prep_var raw_vars |-> fold_map inferred_type
      |> fst |> polymorphic ctxt;

    fun guess_context raw_rule state' =
      let
        val ((parms, rule), ctxt') =
          unify_params vars thesis_var raw_rule (Proof.context_of state');
        val (xs, _) = Variable.add_fixes (map (#1 o #1) parms) ctxt';
        val ps = xs ~~ map (#2 o #1) parms;
        val ts = map Free ps;
        val asms =
          Logic.strip_assums_hyp (Logic.nth_prem (1, Thm.prop_of rule))
          |> map (fn asm => (Term.betapplys (fold_rev Term.abs ps asm, ts), []));
        val _ = not (null asms) orelse error "Trivial result -- nothing guessed";
      in
        state'
        |> Proof.map_context (K ctxt')
        |> Proof.fix (map (fn ((x, T), mx) => (Binding.name x, SOME T, mx)) parms)
        |> `Proof.context_of |-> (fn fix_ctxt => Proof.assm
          (Obtain.obtain_export fix_ctxt rule (map (Thm.cterm_of ctxt) ts))
            [] [] [(Binding.empty_atts, asms)])
        |> Proof.map_context (fold Variable.unbind_term Auto_Bind.no_facts)
      end;

    val goal = Var (("guess", 0), propT);
    val pos = Position.thread_data ();
    fun print_result ctxt' (k, [(s, [_, th])]) =
      Proof_Display.print_results int pos ctxt' (k, [(s, [th])]);
    val before_qed =
      Method.primitive_text (fn ctxt =>
        Goal.conclude #> Raw_Simplifier.norm_hhf ctxt #>
          (fn th => Goal.protect 0 (Conjunction.intr (Drule.mk_term (Thm.cprop_of th)) th)));
    fun after_qed (result_ctxt, results) state' =
      let val [_, res] = Proof_Context.export result_ctxt (Proof.context_of state') (flat results)
      in
        state'
        |> Proof.end_block
        |> guess_context (Obtain.check_result ctxt thesis res)
      end;
  in
    state
    |> Proof.enter_forward
    |> Proof.begin_block
    |> Proof.fix [(Binding.name Auto_Bind.thesisN, NONE, NoSyn)]
    |> Proof.chain_facts chain_facts
    |> Proof.internal_goal print_result Proof_Context.mode_schematic true "guess"
      (SOME before_qed) after_qed
      [] [] [(Binding.empty_atts, [(Logic.mk_term goal, []), (goal, [])])]
    |> snd
    |> Proof.refine_singleton
        (Method.primitive_text (fn _ => fn _ => Goal.init (Thm.cterm_of ctxt thesis)))
  end;

in

val guess = gen_guess Proof_Context.cert_var;
val guess_cmd = gen_guess Proof_Context.read_var;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>guess\<close> "wild guessing (unstructured)"
    (Scan.optional Parse.vars [] >> (Toplevel.proof' o guess_cmd));

end;

end;
\<close>

end
