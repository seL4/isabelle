(*  Title:      HOL/Tools/SMT/smt_replay_methods.ML
    Author:     Sascha Boehme, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Mathias Fleury, MPII

Proof methods for replaying SMT proofs.
*)

signature SMT_REPLAY_METHODS =
sig
  (*Printing*)
  val pretty_goal: Proof.context -> string -> string -> thm list -> term -> Pretty.T
  val trace_goal: Proof.context -> string -> thm list -> term -> unit
  val trace: Proof.context -> (unit -> string) -> unit

  (*Replaying*)
  val replay_error: Proof.context -> string -> string -> thm list -> term -> 'a
  val replay_rule_error: string -> Proof.context -> string -> thm list -> term -> 'a

  (*theory lemma methods*)
  type th_lemma_method = Proof.context -> thm list -> term -> thm
  val add_th_lemma_method: string * th_lemma_method -> Context.generic ->
    Context.generic
  val get_th_lemma_method: Proof.context -> th_lemma_method Symtab.table
  val discharge: int -> thm list -> thm -> thm
  val match_instantiate: Proof.context -> term -> thm -> thm
  val prove: Proof.context -> term -> (Proof.context -> int -> tactic) -> thm

  val prove_arith_rewrite: ((term -> int * term Termtab.table ->
    term * (int * term Termtab.table)) -> term -> int * term Termtab.table ->
    term * (int * term Termtab.table)) -> Proof.context -> term -> thm

  (*abstraction*)
  type abs_context = int * term Termtab.table
  type 'a abstracter = term -> abs_context -> 'a * abs_context
  val add_arith_abstracter: (term abstracter -> term option abstracter) ->
    Context.generic -> Context.generic

  val abstract_lit: term -> abs_context -> term * abs_context
  val abstract_conj: term -> abs_context -> term * abs_context
  val abstract_disj: term -> abs_context -> term * abs_context
  val abstract_not:  (term -> abs_context -> term * abs_context) ->
    term -> abs_context -> term * abs_context
  val abstract_unit:  term -> abs_context -> term * abs_context
  val abstract_bool:  term -> abs_context -> term * abs_context
  (* also abstracts over equivalences and conjunction and implication*)
  val abstract_bool_shallow:  term -> abs_context -> term * abs_context
  (* abstracts down to equivalence symbols *)
  val abstract_bool_shallow_equivalence: term -> abs_context -> term * abs_context
  val abstract_prop: term -> abs_context -> term * abs_context
  val abstract_term:  term -> abs_context -> term * abs_context
  val abstract_eq: (term -> int * term Termtab.table ->  term * (int * term Termtab.table)) ->
        term -> int * term Termtab.table -> term * (int * term Termtab.table)
  val abstract_neq: (term -> int * term Termtab.table ->  term * (int * term Termtab.table)) ->
        term -> int * term Termtab.table -> term * (int * term Termtab.table)
  val abstract_arith: Proof.context -> term -> abs_context -> term * abs_context
  (* also abstracts over if-then-else *)
  val abstract_arith_shallow: Proof.context -> term -> abs_context -> term * abs_context

  val prove_abstract:  Proof.context -> thm list -> term ->
    (Proof.context -> thm list -> int -> tactic) ->
    (abs_context -> (term list * term) * abs_context) -> thm
  val prove_abstract': Proof.context -> term -> (Proof.context -> thm list -> int -> tactic) ->
    (abs_context -> term * abs_context) -> thm
  val try_provers:  string -> Proof.context -> string -> (string * (term -> 'a)) list -> thm list ->
    term -> 'a

  (*shared tactics*)
  val cong_unfolding_trivial: Proof.context -> thm list -> term -> thm
  val cong_basic: Proof.context -> thm list -> term -> thm
  val cong_full: Proof.context -> thm list -> term -> thm
  val cong_unfolding_first: Proof.context -> thm list -> term -> thm
  val arith_th_lemma: Proof.context -> thm list -> term -> thm
  val arith_th_lemma_wo: Proof.context -> thm list -> term -> thm
  val arith_th_lemma_wo_shallow: Proof.context -> thm list -> term -> thm
  val arith_th_lemma_tac_with_wo: Proof.context -> thm list -> int -> tactic

  val dest_thm: thm -> term
  val prop_tac: Proof.context -> thm list -> int -> tactic

  val certify_prop: Proof.context -> term -> cterm
  val dest_prop: term -> term

end;

structure SMT_Replay_Methods: SMT_REPLAY_METHODS =
struct

(* utility functions *)

fun trace ctxt f = SMT_Config.trace_msg ctxt f ()

fun pretty_thm ctxt thm = Syntax.pretty_term ctxt (Thm.concl_of thm)

fun pretty_goal ctxt msg rule thms t =
  let
    val full_msg = msg ^ ": " ^ quote rule
    val assms =
      if null thms then []
      else [Pretty.big_list "assumptions:" (map (pretty_thm ctxt) thms)]
    val concl = Pretty.big_list "proposition:" [Syntax.pretty_term ctxt t]
  in Pretty.big_list full_msg (assms @ [concl]) end

fun replay_error ctxt msg rule thms t = error (Pretty.string_of (pretty_goal ctxt msg rule thms t))

fun replay_rule_error name ctxt = replay_error ctxt ("Failed to replay" ^ name ^ " proof step")

fun trace_goal ctxt rule thms t =
  trace ctxt (fn () => Pretty.string_of (pretty_goal ctxt "Goal" rule thms t))

fun as_prop (t as Const (\<^const_name>\<open>Trueprop\<close>, _) $ _) = t
  | as_prop t = HOLogic.mk_Trueprop t

fun dest_prop (Const (\<^const_name>\<open>Trueprop\<close>, _) $ t) = t
  | dest_prop t = t

fun dest_thm thm = dest_prop (Thm.concl_of thm)


(* plug-ins *)

type abs_context = int * term Termtab.table

type 'a abstracter = term -> abs_context -> 'a * abs_context

type th_lemma_method = Proof.context -> thm list -> term -> thm

fun id_ord ((id1, _), (id2, _)) = int_ord (id1, id2)

structure Plugins = Generic_Data
(
  type T =
    (int * (term abstracter -> term option abstracter)) list *
    th_lemma_method Symtab.table
  val empty = ([], Symtab.empty)
  val extend = I
  fun merge ((abss1, ths1), (abss2, ths2)) = (
    Ord_List.merge id_ord (abss1, abss2),
    Symtab.merge (K true) (ths1, ths2))
)

fun add_arith_abstracter abs = Plugins.map (apfst (Ord_List.insert id_ord (serial (), abs)))
fun get_arith_abstracters ctxt = map snd (fst (Plugins.get (Context.Proof ctxt)))

fun add_th_lemma_method method = Plugins.map (apsnd (Symtab.update_new method))
fun get_th_lemma_method ctxt = snd (Plugins.get (Context.Proof ctxt))

fun match ctxt pat t =
  (Vartab.empty, Vartab.empty)
  |> Pattern.first_order_match (Proof_Context.theory_of ctxt) (pat, t)

fun gen_certify_inst sel cert ctxt thm t =
  let
    val inst = match ctxt (dest_thm thm) (dest_prop t)
    fun cert_inst (ix, (a, b)) = ((ix, a), cert b)
  in Vartab.fold (cons o cert_inst) (sel inst) [] end

fun match_instantiateT ctxt t thm =
  if Term.exists_type (Term.exists_subtype Term.is_TVar) (dest_thm thm) then
    Thm.instantiate (gen_certify_inst fst (Thm.ctyp_of ctxt) ctxt thm t, []) thm
  else thm

fun match_instantiate ctxt t thm =
  let val thm' = match_instantiateT ctxt t thm in
    Thm.instantiate ([], gen_certify_inst snd (Thm.cterm_of ctxt) ctxt thm' t) thm'
  end

fun discharge _ [] thm = thm
  | discharge i (rule :: rules) thm = discharge (i + Thm.nprems_of rule) rules (rule RSN (i, thm))

fun by_tac ctxt thms ns ts t tac =
  Goal.prove ctxt [] (map as_prop ts) (as_prop t)
    (fn {context, prems} => HEADGOAL (tac context prems))
  |> Drule.generalize (Names.empty, Names.make_set ns)
  |> discharge 1 thms

fun prove ctxt t tac = by_tac ctxt [] [] [] t (K o tac)


(* abstraction *)

fun prove_abstract ctxt thms t tac f =
  let
    val ((prems, concl), (_, ts)) = f (1, Termtab.empty)
    val ns = Termtab.fold (fn (_, v) => cons (fst (Term.dest_Free v))) ts []
  in
    by_tac ctxt [] ns prems concl tac
    |> match_instantiate ctxt t
    |> discharge 1 thms
  end

fun prove_abstract' ctxt t tac f =
  prove_abstract ctxt [] t tac (f #>> pair [])

fun lookup_term (_, terms) t = Termtab.lookup terms t

fun abstract_sub t f cx =
  (case lookup_term cx t of
    SOME v => (v, cx)
  | NONE => f cx)

fun mk_fresh_free t (i, terms) =
  let val v = Free ("t" ^ string_of_int i, fastype_of t)
  in (v, (i + 1, Termtab.update (t, v) terms)) end

fun apply_abstracters _ [] _ cx = (NONE, cx)
  | apply_abstracters abs (abstracter :: abstracters) t cx =
      (case abstracter abs t cx of
        (NONE, _) => apply_abstracters abs abstracters t cx
      | x as (SOME _, _) => x)

fun abstract_term (t as _ $ _) = abstract_sub t (mk_fresh_free t)
  | abstract_term (t as Abs _) = abstract_sub t (mk_fresh_free t)
  | abstract_term t = pair t

fun abstract_bin abs f t t1 t2 = abstract_sub t (abs t1 ##>> abs t2 #>> f)

fun abstract_ter abs f t t1 t2 t3 =
  abstract_sub t (abs t1 ##>> abs t2 ##>> abs t3 #>> (Scan.triple1 #> f))

fun abstract_lit (\<^const>\<open>HOL.Not\<close> $ t) = abstract_term t #>> HOLogic.mk_not
  | abstract_lit t = abstract_term t

fun abstract_not abs (t as \<^const>\<open>HOL.Not\<close> $ t1) =
      abstract_sub t (abs t1 #>> HOLogic.mk_not)
  | abstract_not _ t = abstract_lit t

fun abstract_conj (t as \<^const>\<open>HOL.conj\<close> $ t1 $ t2) =
      abstract_bin abstract_conj HOLogic.mk_conj t t1 t2
  | abstract_conj t = abstract_lit t

fun abstract_disj (t as \<^const>\<open>HOL.disj\<close> $ t1 $ t2) =
      abstract_bin abstract_disj HOLogic.mk_disj t t1 t2
  | abstract_disj t = abstract_lit t

fun abstract_prop (t as (c as @{const If (bool)}) $ t1 $ t2 $ t3) =
      abstract_ter abstract_prop (fn (t1, t2, t3) => c $ t1 $ t2 $ t3) t t1 t2 t3
  | abstract_prop (t as \<^const>\<open>HOL.disj\<close> $ t1 $ t2) =
      abstract_bin abstract_prop HOLogic.mk_disj t t1 t2
  | abstract_prop (t as \<^const>\<open>HOL.conj\<close> $ t1 $ t2) =
      abstract_bin abstract_prop HOLogic.mk_conj t t1 t2
  | abstract_prop (t as \<^const>\<open>HOL.implies\<close> $ t1 $ t2) =
      abstract_bin abstract_prop HOLogic.mk_imp t t1 t2
  | abstract_prop (t as \<^term>\<open>HOL.eq :: bool => _\<close> $ t1 $ t2) =
      abstract_bin abstract_prop HOLogic.mk_eq t t1 t2
  | abstract_prop t = abstract_not abstract_prop t

fun abstract_arith ctxt u =
  let
    fun abs (t as (Const (\<^const_name>\<open>HOL.The\<close>, _) $ Abs (_, _, _))) =
          abstract_sub t (abstract_term t)
      | abs (t as (c as Const _) $ Abs (s, T, t')) =
          abstract_sub t (abs t' #>> (fn u' => c $ Abs (s, T, u')))
      | abs (t as (c as Const (\<^const_name>\<open>If\<close>, _)) $ t1 $ t2 $ t3) =
          abstract_ter abs (fn (t1, t2, t3) => c $ t1 $ t2 $ t3) t t1 t2 t3
      | abs (t as \<^const>\<open>HOL.Not\<close> $ t1) = abstract_sub t (abs t1 #>> HOLogic.mk_not)
      | abs (t as \<^const>\<open>HOL.disj\<close> $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> HOLogic.mk_disj)
      | abs (t as (c as Const (\<^const_name>\<open>uminus_class.uminus\<close>, _)) $ t1) =
          abstract_sub t (abs t1 #>> (fn u => c $ u))
      | abs (t as (c as Const (\<^const_name>\<open>plus_class.plus\<close>, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (\<^const_name>\<open>minus_class.minus\<close>, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (\<^const_name>\<open>times_class.times\<close>, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (\<^const_name>\<open>z3div\<close>, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (\<^const_name>\<open>z3mod\<close>, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (\<^const_name>\<open>HOL.eq\<close>, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (\<^const_name>\<open>ord_class.less\<close>, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (\<^const_name>\<open>ord_class.less_eq\<close>, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs t = abstract_sub t (fn cx =>
          if can HOLogic.dest_number t then (t, cx)
          else
            (case apply_abstracters abs (get_arith_abstracters ctxt) t cx of
              (SOME u, cx') => (u, cx')
            | (NONE, _) => abstract_term t cx))
  in abs u end

fun abstract_unit (t as (\<^const>\<open>HOL.Not\<close> $ (\<^const>\<open>HOL.disj\<close> $ t1 $ t2))) =
      abstract_sub t (abstract_unit t1 ##>> abstract_unit t2 #>>
        HOLogic.mk_not o HOLogic.mk_disj)
  | abstract_unit (t as (\<^const>\<open>HOL.disj\<close> $ t1 $ t2)) =
      abstract_sub t (abstract_unit t1 ##>> abstract_unit t2 #>>
        HOLogic.mk_disj)
  | abstract_unit (t as (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ t1 $ t2)) =
      if fastype_of t1 = \<^typ>\<open>bool\<close> then
        abstract_sub t (abstract_unit t1 ##>> abstract_unit t2 #>>
          HOLogic.mk_eq)
      else abstract_lit t
  | abstract_unit (t as (\<^const>\<open>HOL.Not\<close> $ (Const(\<^const_name>\<open>HOL.eq\<close>, _) $ t1 $ t2))) =
      if fastype_of t1 = \<^typ>\<open>bool\<close> then
        abstract_sub t (abstract_unit t1 ##>> abstract_unit t2 #>>
          HOLogic.mk_eq #>> HOLogic.mk_not)
      else abstract_lit t
  | abstract_unit (t as (\<^const>\<open>HOL.Not\<close> $ t1)) =
      abstract_sub t (abstract_unit t1 #>> HOLogic.mk_not)
  | abstract_unit t = abstract_lit t

fun abstract_bool (t as (@{const HOL.disj} $ t1 $ t2)) =
      abstract_sub t (abstract_bool t1 ##>> abstract_bool t2 #>>
        HOLogic.mk_disj)
  | abstract_bool (t as (@{const HOL.conj} $ t1 $ t2)) =
      abstract_sub t (abstract_bool t1 ##>> abstract_bool t2 #>>
        HOLogic.mk_conj)
  | abstract_bool (t as (Const(@{const_name HOL.eq}, _) $ t1 $ t2)) =
      if fastype_of t1 = @{typ bool} then
        abstract_sub t (abstract_bool t1 ##>> abstract_bool t2 #>>
          HOLogic.mk_eq)
      else abstract_lit t
  | abstract_bool (t as (@{const HOL.Not} $ t1)) =
      abstract_sub t (abstract_bool t1 #>> HOLogic.mk_not)
  | abstract_bool (t as (@{const HOL.implies} $ t1 $ t2)) =
      abstract_sub t (abstract_bool t1 ##>> abstract_bool t2 #>>
        HOLogic.mk_imp)
  | abstract_bool t = abstract_lit t

fun abstract_bool_shallow (t as (@{const HOL.disj} $ t1 $ t2)) =
      abstract_sub t (abstract_bool_shallow t1 ##>> abstract_bool_shallow t2 #>>
        HOLogic.mk_disj)
  | abstract_bool_shallow (t as (@{const HOL.Not} $ t1)) =
      abstract_sub t (abstract_bool_shallow t1 #>> HOLogic.mk_not)
  | abstract_bool_shallow t = abstract_term t

fun abstract_bool_shallow_equivalence (t as (@{const HOL.disj} $ t1 $ t2)) =
      abstract_sub t (abstract_bool_shallow_equivalence t1 ##>> abstract_bool_shallow_equivalence t2 #>>
        HOLogic.mk_disj)
  | abstract_bool_shallow_equivalence (t as (Const(@{const_name HOL.eq}, _) $ t1 $ t2)) =
      if fastype_of t1 = @{typ bool} then
        abstract_sub t (abstract_lit t1 ##>> abstract_lit t2 #>>
          HOLogic.mk_eq)
      else abstract_lit t
  | abstract_bool_shallow_equivalence (t as (@{const HOL.Not} $ t1)) =
      abstract_sub t (abstract_bool_shallow_equivalence t1 #>> HOLogic.mk_not)
  | abstract_bool_shallow_equivalence t = abstract_lit t

fun abstract_arith_shallow ctxt u =
  let
    fun abs (t as (Const (\<^const_name>\<open>HOL.The\<close>, _) $ Abs (_, _, _))) =
          abstract_sub t (abstract_term t)
      | abs (t as (c as Const _) $ Abs (s, T, t')) =
          abstract_sub t (abs t' #>> (fn u' => c $ Abs (s, T, u')))
      | abs (t as (Const (\<^const_name>\<open>If\<close>, _)) $ _ $ _ $ _) =
          abstract_sub t (abstract_term t)
      | abs (t as \<^const>\<open>HOL.Not\<close> $ t1) = abstract_sub t (abs t1 #>> HOLogic.mk_not)
      | abs (t as \<^const>\<open>HOL.disj\<close> $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> HOLogic.mk_disj)
      | abs (t as (c as Const (\<^const_name>\<open>uminus_class.uminus\<close>, _)) $ t1) =
          abstract_sub t (abs t1 #>> (fn u => c $ u))
      | abs (t as (c as Const (\<^const_name>\<open>plus_class.plus\<close>, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (\<^const_name>\<open>minus_class.minus\<close>, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (\<^const_name>\<open>times_class.times\<close>, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (Const (\<^const_name>\<open>z3div\<close>, _)) $ _ $ _) =
         abstract_sub t (abstract_term t)
      | abs (t as (Const (\<^const_name>\<open>z3mod\<close>, _)) $ _ $ _) =
          abstract_sub t (abstract_term t)
      | abs (t as (c as Const (\<^const_name>\<open>HOL.eq\<close>, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (\<^const_name>\<open>ord_class.less\<close>, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs (t as (c as Const (\<^const_name>\<open>ord_class.less_eq\<close>, _)) $ t1 $ t2) =
          abstract_sub t (abs t1 ##>> abs t2 #>> (fn (u1, u2) => c $ u1 $ u2))
      | abs t = abstract_sub t (fn cx =>
          if can HOLogic.dest_number t then (t, cx)
          else
            (case apply_abstracters abs (get_arith_abstracters ctxt) t cx of
              (SOME u, cx') => (u, cx')
            | (NONE, _) => abstract_term t cx))
  in abs u end

(* theory lemmas *)

fun try_provers prover_name ctxt rule [] thms t = replay_rule_error prover_name ctxt rule thms t
  | try_provers prover_name ctxt rule ((name, prover) :: named_provers) thms t =
      (case (trace ctxt (K ("Trying prover " ^ quote name)); try prover t) of
        SOME thm => thm
      | NONE => try_provers prover_name ctxt rule named_provers thms t)

(*theory-lemma*)

fun arith_th_lemma_tac ctxt prems =
  Method.insert_tac ctxt prems
  THEN' SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms z3div_def z3mod_def})
  THEN' Arith_Data.arith_tac ctxt

fun arith_th_lemma ctxt thms t =
  prove_abstract ctxt thms t arith_th_lemma_tac (
    fold_map (abstract_arith ctxt o dest_thm) thms ##>>
      abstract_arith ctxt (dest_prop t))

fun arith_th_lemma_tac_with_wo ctxt prems =
  Method.insert_tac ctxt prems
  THEN' SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms z3div_def z3mod_def int_distrib})
  THEN' Simplifier.asm_full_simp_tac
     (empty_simpset ctxt addsimprocs [(*@{simproc linordered_ring_strict_eq_cancel_factor_poly},
      @{simproc linordered_ring_strict_le_cancel_factor_poly},
      @{simproc linordered_ring_strict_less_cancel_factor_poly},
      @{simproc nat_eq_cancel_factor_poly},
      @{simproc nat_le_cancel_factor_poly},
      @{simproc nat_less_cancel_factor_poly}*)])
  THEN' (fn i => TRY (Arith_Data.arith_tac ctxt i))

fun arith_th_lemma_wo ctxt thms t =
  prove_abstract ctxt thms t arith_th_lemma_tac_with_wo (
    fold_map (abstract_arith ctxt o dest_thm) thms ##>>
      abstract_arith ctxt (dest_prop t))

fun arith_th_lemma_wo_shallow ctxt thms t =
  prove_abstract ctxt thms t arith_th_lemma_tac_with_wo (
    fold_map (abstract_arith_shallow ctxt o dest_thm) thms ##>>
      abstract_arith_shallow ctxt (dest_prop t))

val _ = Theory.setup (Context.theory_map (add_th_lemma_method ("arith", arith_th_lemma)))


(* congruence *)

fun certify_prop ctxt t = Thm.cterm_of ctxt (as_prop t)

fun ctac ctxt prems i st = st |> (
  resolve_tac ctxt (@{thm refl} :: prems) i
  ORELSE (cong_tac ctxt i THEN ctac ctxt prems (i + 1) THEN ctac ctxt prems i))

fun cong_basic ctxt thms t =
  let val st = Thm.trivial (certify_prop ctxt t)
  in
    (case Seq.pull (ctac ctxt thms 1 st) of
      SOME (thm, _) => thm
    | NONE => raise THM ("cong", 0, thms @ [st]))
  end

val cong_dest_rules = @{lemma
  "(\<not> P \<or> Q) \<and> (P \<or> \<not> Q) \<Longrightarrow> P = Q"
  "(P \<or> \<not> Q) \<and> (\<not> P \<or> Q) \<Longrightarrow> P = Q"
  by fast+}

fun cong_full_core_tac ctxt =
  eresolve_tac ctxt @{thms subst}
  THEN' resolve_tac ctxt @{thms refl}
  ORELSE' Classical.fast_tac ctxt

fun cong_full ctxt thms t = prove ctxt t (fn ctxt' =>
  Method.insert_tac ctxt thms
  THEN' (cong_full_core_tac ctxt'
    ORELSE' dresolve_tac ctxt cong_dest_rules
    THEN' cong_full_core_tac ctxt'))

local
  val reorder_for_simp = try (fn thm =>
       let val t = Thm.prop_of (@{thm eq_reflection} OF [thm])
           val thm =
             (case Logic.dest_equals t of
               (t1, t2) =>
                 if t1 aconv t2 then raise TERM("identical terms", [t1, t2])
                 else if Term.size_of_term t1 > Term.size_of_term t2 then @{thm eq_reflection} OF [thm]
                 else @{thm eq_reflection} OF [@{thm sym} OF [thm]])
                  handle TERM("dest_equals", _) => @{thm eq_reflection} OF [thm]
       in thm end)
in  
fun cong_unfolding_trivial ctxt thms t =
   prove ctxt t (fn _ =>
      EVERY' (map (fn thm => K (unfold_tac ctxt [thm])) ((map_filter reorder_for_simp thms)))
      THEN' (fn i => TRY (resolve_tac ctxt @{thms refl} i)))

fun cong_unfolding_first ctxt thms t =
  let val ctxt =
        ctxt
        |> empty_simpset
        |> put_simpset HOL_basic_ss
        |> (fn ctxt => ctxt addsimps @{thms not_not eq_commute})
  in
    prove ctxt t (fn _ =>
      EVERY' (map (fn thm => K (unfold_tac ctxt [thm])) ((map_filter reorder_for_simp thms)))
      THEN' Method.insert_tac ctxt thms
      THEN' (full_simp_tac ctxt)
      THEN' K (ALLGOALS (K (Clasimp.auto_tac ctxt))))
  end

end


fun arith_rewrite_tac ctxt _ =
  let val backup_tac = Arith_Data.arith_tac ctxt ORELSE' Clasimp.force_tac ctxt in
    (TRY o Simplifier.simp_tac ctxt) THEN_ALL_NEW backup_tac
    ORELSE' backup_tac
  end

fun abstract_eq f (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t1 $ t2) =
      f t1 ##>> f t2 #>> HOLogic.mk_eq
  | abstract_eq _ t = abstract_term t

fun abstract_neq f (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t1 $ t2) =
      f t1 ##>> f t2 #>> HOLogic.mk_eq
  | abstract_neq f (Const (\<^const_name>\<open>HOL.Not\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ t1 $ t2)) =
       f t1 ##>> f t2 #>> HOLogic.mk_eq #>> curry (op $) HOLogic.Not
  |  abstract_neq f (Const (\<^const_name>\<open>HOL.disj\<close>, _) $ t1 $ t2) =
      f t1 ##>> f t2 #>> HOLogic.mk_disj
  | abstract_neq _ t = abstract_term t

fun prove_arith_rewrite abstracter ctxt t =
  prove_abstract' ctxt t arith_rewrite_tac (
    abstracter (abstract_arith ctxt) (dest_prop t))

fun prop_tac ctxt prems =
  Method.insert_tac ctxt prems
  THEN' SUBGOAL (fn (prop, i) =>
    if Term.size_of_term prop > 100 then SAT.satx_tac ctxt i
    else (Classical.fast_tac ctxt ORELSE' Clasimp.force_tac ctxt) i)

end;
