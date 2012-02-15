(*  Title:      HOL/Tools/SMT/z3_proof_tools.ML
    Author:     Sascha Boehme, TU Muenchen

Helper functions required for Z3 proof reconstruction.
*)

signature Z3_PROOF_TOOLS =
sig
  (*modifying terms*)
  val as_meta_eq: cterm -> cterm

  (*theorem nets*)
  val thm_net_of: ('a -> thm) -> 'a list -> 'a Net.net
  val net_instances: (int * thm) Net.net -> cterm -> (int * thm) list
  val net_instance: thm Net.net -> cterm -> thm option

  (*proof combinators*)
  val under_assumption: (thm -> thm) -> cterm -> thm
  val with_conv: conv -> (cterm -> thm) -> cterm -> thm
  val discharge: thm -> thm -> thm
  val varify: string list -> thm -> thm
  val unfold_eqs: Proof.context -> thm list -> conv
  val match_instantiate: (cterm -> cterm) -> cterm -> thm -> thm
  val by_tac: (int -> tactic) -> cterm -> thm
  val make_hyp_def: thm -> Proof.context -> thm * Proof.context
  val by_abstraction: int -> bool * bool -> Proof.context -> thm list ->
    (Proof.context -> cterm -> thm) -> cterm -> thm

  (*a faster COMP*)
  type compose_data
  val precompose: (cterm -> cterm list) -> thm -> compose_data
  val precompose2: (cterm -> cterm * cterm) -> thm -> compose_data
  val compose: compose_data -> thm -> thm

  (*unfolding of 'distinct'*)
  val unfold_distinct_conv: conv

  (*simpset*)
  val add_simproc: Simplifier.simproc -> Context.generic -> Context.generic
  val make_simpset: Proof.context -> thm list -> simpset
end

structure Z3_Proof_Tools: Z3_PROOF_TOOLS =
struct



(* modifying terms *)

fun as_meta_eq ct =
  uncurry SMT_Utils.mk_cequals (Thm.dest_binop (SMT_Utils.dest_cprop ct))



(* theorem nets *)

fun thm_net_of f xthms =
  let fun insert xthm = Net.insert_term (K false) (Thm.prop_of (f xthm), xthm)
  in fold insert xthms Net.empty end

fun maybe_instantiate ct thm =
  try Thm.first_order_match (Thm.cprop_of thm, ct)
  |> Option.map (fn inst => Thm.instantiate inst thm)

local
  fun instances_from_net match f net ct =
    let
      val lookup = if match then Net.match_term else Net.unify_term
      val xthms = lookup net (Thm.term_of ct)
      fun select ct = map_filter (f (maybe_instantiate ct)) xthms 
      fun select' ct =
        let val thm = Thm.trivial ct
        in map_filter (f (try (fn rule => rule COMP thm))) xthms end
    in (case select ct of [] => select' ct | xthms' => xthms') end
in

fun net_instances net =
  instances_from_net false (fn f => fn (i, thm) => Option.map (pair i) (f thm))
    net

fun net_instance net = try hd o instances_from_net true I net

end



(* proof combinators *)

fun under_assumption f ct =
  let val ct' = SMT_Utils.mk_cprop ct
  in Thm.implies_intr ct' (f (Thm.assume ct')) end

fun with_conv conv prove ct =
  let val eq = Thm.symmetric (conv ct)
  in Thm.equal_elim eq (prove (Thm.lhs_of eq)) end

fun discharge p pq = Thm.implies_elim pq p

fun varify vars = Drule.generalize ([], vars)

fun unfold_eqs _ [] = Conv.all_conv
  | unfold_eqs ctxt eqs =
      Conv.top_sweep_conv (K (Conv.rewrs_conv eqs)) ctxt

fun match_instantiate f ct thm =
  Thm.instantiate (Thm.match (f (Thm.cprop_of thm), ct)) thm

fun by_tac tac ct = Goal.norm_result (Goal.prove_internal [] ct (K (tac 1)))

(*
   |- c x == t x ==> P (c x)
  ---------------------------
      c == t |- P (c x)
*) 
fun make_hyp_def thm ctxt =
  let
    val (lhs, rhs) = Thm.dest_binop (Thm.cprem_of thm 1)
    val (cf, cvs) = Drule.strip_comb lhs
    val eq = SMT_Utils.mk_cequals cf (fold_rev Thm.lambda cvs rhs)
    fun apply cv th =
      Thm.combination th (Thm.reflexive cv)
      |> Conv.fconv_rule (Conv.arg_conv (Thm.beta_conversion false))
  in
    yield_singleton Assumption.add_assumes eq ctxt
    |>> Thm.implies_elim thm o fold apply cvs
  end



(* abstraction *)

local

fun abs_context ctxt = (ctxt, Termtab.empty, 1, false)

fun context_of (ctxt, _, _, _) = ctxt

fun replace (_, (cv, ct)) = Thm.forall_elim ct o Thm.forall_intr cv

fun abs_instantiate (_, tab, _, beta_norm) =
  fold replace (Termtab.dest tab) #>
  beta_norm ? Conv.fconv_rule (Thm.beta_conversion true)

fun lambda_abstract cvs t =
  let
    val frees = map Free (Term.add_frees t [])
    val cvs' = filter (fn cv => member (op aconv) frees (Thm.term_of cv)) cvs
    val vs = map (Term.dest_Free o Thm.term_of) cvs'
  in (fold_rev absfree vs t, cvs') end

fun fresh_abstraction (_, cvs) ct (cx as (ctxt, tab, idx, beta_norm)) =
  let val (t, cvs') = lambda_abstract cvs (Thm.term_of ct)
  in
    (case Termtab.lookup tab t of
      SOME (cv, _) => (Drule.list_comb (cv, cvs'), cx)
    | NONE =>
        let
          val (n, ctxt') = yield_singleton Variable.variant_fixes "x" ctxt
          val cv = SMT_Utils.certify ctxt'
            (Free (n, map SMT_Utils.typ_of cvs' ---> SMT_Utils.typ_of ct))
          val cu = Drule.list_comb (cv, cvs')
          val e = (t, (cv, fold_rev Thm.lambda cvs' ct))
          val beta_norm' = beta_norm orelse not (null cvs')
        in (cu, (ctxt', Termtab.update e tab, idx + 1, beta_norm')) end)
  end

fun abs_comb f g dcvs ct =
  let val (cf, cu) = Thm.dest_comb ct
  in f dcvs cf ##>> g dcvs cu #>> uncurry Thm.apply end

fun abs_arg f = abs_comb (K pair) f

fun abs_args f dcvs ct =
  (case Thm.term_of ct of
    _ $ _ => abs_comb (abs_args f) f dcvs ct
  | _ => pair ct)

fun abs_list f g dcvs ct =
  (case Thm.term_of ct of
    Const (@{const_name Nil}, _) => pair ct
  | Const (@{const_name Cons}, _) $ _ $ _ =>
      abs_comb (abs_arg f) (abs_list f g) dcvs ct
  | _ => g dcvs ct)

fun abs_abs f (depth, cvs) ct =
  let val (cv, cu) = Thm.dest_abs NONE ct
  in f (depth, cv :: cvs) cu #>> Thm.lambda cv end

val is_atomic =
  (fn Free _ => true | Var _ => true | Bound _ => true | _ => false)

fun abstract depth (ext_logic, with_theories) =
  let
    fun abstr1 cvs ct = abs_arg abstr cvs ct
    and abstr2 cvs ct = abs_comb abstr1 abstr cvs ct
    and abstr3 cvs ct = abs_comb abstr2 abstr cvs ct
    and abstr_abs cvs ct = abs_arg (abs_abs abstr) cvs ct

    and abstr (dcvs as (d, cvs)) ct =
      (case Thm.term_of ct of
        @{const Trueprop} $ _ => abstr1 dcvs ct
      | @{const "==>"} $ _ $ _ => abstr2 dcvs ct
      | @{const True} => pair ct
      | @{const False} => pair ct
      | @{const Not} $ _ => abstr1 dcvs ct
      | @{const HOL.conj} $ _ $ _ => abstr2 dcvs ct
      | @{const HOL.disj} $ _ $ _ => abstr2 dcvs ct
      | @{const HOL.implies} $ _ $ _ => abstr2 dcvs ct
      | Const (@{const_name HOL.eq}, _) $ _ $ _ => abstr2 dcvs ct
      | Const (@{const_name distinct}, _) $ _ =>
          if ext_logic then abs_arg (abs_list abstr fresh_abstraction) dcvs ct
          else fresh_abstraction dcvs ct
      | Const (@{const_name If}, _) $ _ $ _ $ _ =>
          if ext_logic then abstr3 dcvs ct else fresh_abstraction dcvs ct
      | Const (@{const_name All}, _) $ _ =>
          if ext_logic then abstr_abs dcvs ct else fresh_abstraction dcvs ct
      | Const (@{const_name Ex}, _) $ _ =>
          if ext_logic then abstr_abs dcvs ct else fresh_abstraction dcvs ct
      | t => (fn cx =>
          if is_atomic t orelse can HOLogic.dest_number t then (ct, cx)
          else if with_theories andalso
            Z3_Interface.is_builtin_theory_term (context_of cx) t
          then abs_args abstr dcvs ct cx
          else if d = 0 then fresh_abstraction dcvs ct cx
          else
            (case Term.strip_comb t of
              (Const _, _) => abs_args abstr (d-1, cvs) ct cx
            | (Free _, _) => abs_args abstr (d-1, cvs) ct cx
            | _ => fresh_abstraction dcvs ct cx)))
  in abstr (depth, []) end

val cimp = Thm.cterm_of @{theory} @{const "==>"}

fun deepen depth f x =
  if depth = 0 then f depth x
  else (case try (f depth) x of SOME y => y | NONE => deepen (depth - 1) f x)

fun with_prems depth thms f ct =
  fold_rev (Thm.mk_binop cimp o Thm.cprop_of) thms ct
  |> deepen depth f
  |> fold (fn prem => fn th => Thm.implies_elim th prem) thms

in

fun by_abstraction depth mode ctxt thms prove =
  with_prems depth thms (fn d => fn ct =>
    let val (cu, cx) = abstract d mode ct (abs_context ctxt)
    in abs_instantiate cx (prove (context_of cx) cu) end)

end



(* a faster COMP *)

type compose_data = cterm list * (cterm -> cterm list) * thm

fun list2 (x, y) = [x, y]

fun precompose f rule = (f (Thm.cprem_of rule 1), f, rule)
fun precompose2 f rule = precompose (list2 o f) rule

fun compose (cvs, f, rule) thm =
  discharge thm (Thm.instantiate ([], cvs ~~ f (Thm.cprop_of thm)) rule)



(* unfolding of 'distinct' *)

local
  val set1 = @{lemma "x ~: set [] == ~False" by simp}
  val set2 = @{lemma "x ~: set [x] == False" by simp}
  val set3 = @{lemma "x ~: set [y] == x ~= y" by simp}
  val set4 = @{lemma "x ~: set (x # ys) == False" by simp}
  val set5 = @{lemma "x ~: set (y # ys) == x ~= y & x ~: set ys" by simp}

  fun set_conv ct =
    (Conv.rewrs_conv [set1, set2, set3, set4] else_conv
    (Conv.rewr_conv set5 then_conv Conv.arg_conv set_conv)) ct

  val dist1 = @{lemma "distinct [] == ~False" by (simp add: distinct_def)}
  val dist2 = @{lemma "distinct [x] == ~False" by (simp add: distinct_def)}
  val dist3 = @{lemma "distinct (x # xs) == x ~: set xs & distinct xs"
    by (simp add: distinct_def)}

  fun binop_conv cv1 cv2 = Conv.combination_conv (Conv.arg_conv cv1) cv2
in
fun unfold_distinct_conv ct =
  (Conv.rewrs_conv [dist1, dist2] else_conv
  (Conv.rewr_conv dist3 then_conv binop_conv set_conv unfold_distinct_conv)) ct
end



(* simpset *)

local
  val antisym_le1 = mk_meta_eq @{thm order_class.antisym_conv}
  val antisym_le2 = mk_meta_eq @{thm linorder_class.antisym_conv2}
  val antisym_less1 = mk_meta_eq @{thm linorder_class.antisym_conv1}
  val antisym_less2 = mk_meta_eq @{thm linorder_class.antisym_conv3}

  fun eq_prop t thm = HOLogic.mk_Trueprop t aconv Thm.prop_of thm
  fun dest_binop ((c as Const _) $ t $ u) = (c, t, u)
    | dest_binop t = raise TERM ("dest_binop", [t])

  fun prove_antisym_le ss t =
    let
      val (le, r, s) = dest_binop t
      val less = Const (@{const_name less}, Term.fastype_of le)
      val prems = Simplifier.prems_of ss
    in
      (case find_first (eq_prop (le $ s $ r)) prems of
        NONE =>
          find_first (eq_prop (HOLogic.mk_not (less $ r $ s))) prems
          |> Option.map (fn thm => thm RS antisym_less1)
      | SOME thm => SOME (thm RS antisym_le1))
    end
    handle THM _ => NONE

  fun prove_antisym_less ss t =
    let
      val (less, r, s) = dest_binop (HOLogic.dest_not t)
      val le = Const (@{const_name less_eq}, Term.fastype_of less)
      val prems = Simplifier.prems_of ss
    in
      (case find_first (eq_prop (le $ r $ s)) prems of
        NONE =>
          find_first (eq_prop (HOLogic.mk_not (less $ s $ r))) prems
          |> Option.map (fn thm => thm RS antisym_less2)
      | SOME thm => SOME (thm RS antisym_le2))
  end
  handle THM _ => NONE

  val basic_simpset = HOL_ss addsimps @{thms field_simps}
    addsimps [@{thm times_divide_eq_right}, @{thm times_divide_eq_left}]
    addsimps @{thms arith_special} addsimps @{thms less_bin_simps}
    addsimps @{thms le_bin_simps} addsimps @{thms eq_bin_simps}
    addsimps @{thms add_bin_simps} addsimps @{thms succ_bin_simps}
    addsimps @{thms minus_bin_simps} addsimps @{thms pred_bin_simps}
    addsimps @{thms mult_bin_simps} addsimps @{thms iszero_simps}
    addsimps @{thms array_rules}
    addsimps @{thms term_true_def} addsimps @{thms term_false_def}
    addsimps @{thms z3div_def} addsimps @{thms z3mod_def}
    addsimprocs [
      Simplifier.simproc_global @{theory} "fast_int_arith" [
        "(m::int) < n", "(m::int) <= n", "(m::int) = n"] (K Lin_Arith.simproc),
      Simplifier.simproc_global @{theory} "antisym_le" ["(x::'a::order) <= y"]
        (K prove_antisym_le),
      Simplifier.simproc_global @{theory} "antisym_less" ["~ (x::'a::linorder) < y"]
        (K prove_antisym_less)]

  structure Simpset = Generic_Data
  (
    type T = simpset
    val empty = basic_simpset
    val extend = I
    val merge = Simplifier.merge_ss
  )
in

fun add_simproc simproc = Simpset.map (fn ss => ss addsimprocs [simproc])

fun make_simpset ctxt rules =
  Simplifier.context ctxt (Simpset.get (Context.Proof ctxt)) addsimps rules

end

end
