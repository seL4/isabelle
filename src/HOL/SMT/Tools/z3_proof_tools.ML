(*  Title:      HOL/SMT/Tools/z3_proof_tools.ML
    Author:     Sascha Boehme, TU Muenchen

Helper functions required for Z3 proof reconstruction.
*)

signature Z3_PROOF_TOOLS =
sig
  (* accessing and modifying terms *)
  val term_of: cterm -> term
  val prop_of: thm -> term
  val mk_prop: cterm -> cterm
  val as_meta_eq: cterm -> cterm

  (* theorem nets *)
  val thm_net_of: thm list -> thm Net.net
  val net_instance: thm Net.net -> cterm -> thm option

  (* proof combinators *)
  val under_assumption: (thm -> thm) -> cterm -> thm
  val with_conv: conv -> (cterm -> thm) -> cterm -> thm
  val discharge: thm -> thm -> thm
  val varify: string list -> thm -> thm
  val unfold_eqs: Proof.context -> thm list -> conv
  val match_instantiate: (cterm -> cterm) -> cterm -> thm -> thm
  val by_tac: (int -> tactic) -> cterm -> thm
  val make_hyp_def: thm -> cterm list * thm
  val by_abstraction: Proof.context -> thm list -> (Proof.context -> cterm ->
    thm) -> cterm -> thm

  (* a faster COMP *)
  type compose_data
  val precompose: (cterm -> cterm list) -> thm -> compose_data
  val precompose2: (cterm -> cterm * cterm) -> thm -> compose_data
  val compose: compose_data -> thm -> thm

  (* unfolding of 'distinct' *)
  val unfold_distinct_conv: conv

  (* simpset *)
  val make_simpset: Proof.context -> thm list -> simpset
end

structure Z3_Proof_Tools: Z3_PROOF_TOOLS =
struct



(* accessing terms *)

val dest_prop = (fn @{term Trueprop} $ t => t | t => t)

fun term_of ct = dest_prop (Thm.term_of ct)
fun prop_of thm = dest_prop (Thm.prop_of thm)

val mk_prop = Thm.capply @{cterm Trueprop}

val (eqT, eq) = `(hd o Thm.dest_ctyp o Thm.ctyp_of_term) @{cpat "op =="}
fun mk_meta_eq_cterm ct cu =
  let val inst = ([(eqT, Thm.ctyp_of_term ct)], [])
  in Thm.mk_binop (Thm.instantiate_cterm inst eq) ct cu end

fun as_meta_eq ct = uncurry mk_meta_eq_cterm (Thm.dest_binop (Thm.dest_arg ct))



(* theorem nets *)

fun thm_net_of thms =
  let fun insert thm = Net.insert_term (K false) (Thm.prop_of thm, thm)
  in fold insert thms Net.empty end

fun maybe_instantiate ct thm =
  try Thm.first_order_match (Thm.cprop_of thm, ct)
  |> Option.map (fn inst => Thm.instantiate inst thm)

fun first_of thms ct = get_first (maybe_instantiate ct) thms
fun net_instance net ct = first_of (Net.match_term net (Thm.term_of ct)) ct



(* proof combinators *)

fun under_assumption f ct =
  let val ct' = mk_prop ct
  in Thm.implies_intr ct' (f (Thm.assume ct')) end

fun with_conv conv prove ct =
  let val eq = Thm.symmetric (conv ct)
  in Thm.equal_elim eq (prove (Thm.lhs_of eq)) end

fun discharge p pq = Thm.implies_elim pq p

fun varify vars = Drule.generalize ([], vars)

fun unfold_eqs _ [] = Conv.all_conv
  | unfold_eqs ctxt eqs =
      More_Conv.top_sweep_conv (K (More_Conv.rewrs_conv eqs)) ctxt

fun match_instantiate f ct thm =
  Thm.instantiate (Thm.match (f (Thm.cprop_of thm), ct)) thm

fun by_tac tac ct = Goal.norm_result (Goal.prove_internal [] ct (K (tac 1)))

(* |- c x == t x ==> P (c x)  ~~>  c == t |- P (c x) *) 
fun make_hyp_def thm =
  let
    val (lhs, rhs) = Thm.dest_binop (Thm.cprem_of thm 1)
    val (cf, cvs) = Drule.strip_comb lhs
    val eq = mk_meta_eq_cterm cf (fold_rev Thm.cabs cvs rhs)
    fun apply cv th =
      Thm.combination th (Thm.reflexive cv)
      |> Conv.fconv_rule (Conv.arg_conv (Thm.beta_conversion false))
  in ([eq], Thm.implies_elim thm (fold apply cvs (Thm.assume eq))) end



(* abstraction *)

local

fun typ_of ct = #T (Thm.rep_cterm ct)
fun certify ctxt = Thm.cterm_of (ProofContext.theory_of ctxt)

fun abs_context ctxt = (ctxt, Termtab.empty, 1, false)

fun context_of (ctxt, _, _, _) = ctxt

fun replace (cv, ct) = Thm.forall_elim ct o Thm.forall_intr cv

fun abs_instantiate (_, tab, _, beta_norm) =
  fold replace (map snd (Termtab.dest tab)) #>
  beta_norm ? Conv.fconv_rule (Thm.beta_conversion true)

fun generalize cvs =
  let
    val no_name = ""

    fun dest (Free (n, _)) = n
      | dest _ = no_name

    fun gen vs (t as Free (n, _)) =
          let val i = find_index (equal n) vs
          in
            if i >= 0 then insert (op aconvc) (nth cvs i) #> pair (Bound i)
            else pair t
          end
      | gen vs (t $ u) = gen vs t ##>> gen vs u #>> (op $)
      | gen vs (Abs (n, T, t)) =
          gen (no_name :: vs) t #>> (fn u => Abs (n, T, u))
      | gen _ t = pair t

  in (fn ct => gen (map (dest o Thm.term_of) cvs) (Thm.term_of ct) []) end

fun fresh_abstraction cvs ct (cx as (ctxt, tab, idx, beta_norm)) =
  let val (t, cvs') = generalize cvs ct
  in
    (case Termtab.lookup tab t of
      SOME (cv, _) => (cv, cx)
    | NONE =>
        let
          val (n, ctxt') = yield_singleton Variable.variant_fixes "x" ctxt
          val cv = certify ctxt (Free (n, map typ_of cvs' ---> typ_of ct))
          val cv' = Drule.list_comb (cv, cvs')
          val e = (t, (cv, fold_rev Thm.cabs cvs' ct))
          val beta_norm' = beta_norm orelse not (null cvs')
        in (cv', (ctxt', Termtab.update e tab, idx + 1, beta_norm')) end)
  end

fun abs_arg f cvs ct =
  let val (cf, cu) = Thm.dest_comb ct
  in f cvs cu #>> Thm.capply cf end

fun abs_comb f g cvs ct =
  let val (cf, cu) = Thm.dest_comb ct
  in f cvs cf ##>> g cvs cu #>> uncurry Thm.capply end

fun abs_list f g cvs ct =
  (case Thm.term_of ct of
    Const (@{const_name Nil}, _) => pair ct
  | Const (@{const_name Cons}, _) $ _ $ _ =>
      abs_comb (abs_arg f) (abs_list f g) cvs ct
  | _ => g cvs ct)

fun abs_abs f cvs ct =
  let val (cv, cu) = Thm.dest_abs NONE ct
  in f (cv :: cvs) cu #>> Thm.cabs cv end

val is_atomic = (fn _ $ _ => false | Abs _ => false | _ => true)
val is_arithT = (fn @{typ int} => true | @{typ real} => true | _ => false)
fun is_number t =
  (case try HOLogic.dest_number t of
    SOME (T, _) => is_arithT T
  | NONE => false)

val abstract =
  let (* FIXME: provide an option to avoid abstraction of If/distinct/All/Ex *)
    fun abstr1 cvs ct = abs_arg abstr cvs ct
    and abstr2 cvs ct = abs_comb abstr1 abstr cvs ct
    and abstr3 cvs ct = abs_comb abstr2 abstr cvs ct
    and abstr_abs cvs ct = abs_arg (abs_abs abstr) cvs ct

    and abstr cvs ct =
      (case Thm.term_of ct of
        @{term Trueprop} $ _ => abstr1 cvs ct
      | @{term "op ==>"} $ _ $ _ => abstr2 cvs ct
      | @{term True} => pair ct
      | @{term False} => pair ct
      | @{term Not} $ _ => abstr1 cvs ct
      | @{term "op &"} $ _ $ _ => abstr2 cvs ct
      | @{term "op |"} $ _ $ _ => abstr2 cvs ct
      | @{term "op -->"} $ _ $ _ => abstr2 cvs ct
      | Const (@{const_name "op ="}, _) $ _ $ _ => abstr2 cvs ct
      | Const (@{const_name distinct}, _) $ _ =>
          abs_arg (abs_list abstr fresh_abstraction) cvs ct
      | Const (@{const_name If}, _) $ _ $ _ $ _ => abstr3 cvs ct
      | Const (@{const_name All}, _) $ _ => abstr_abs cvs ct
      | Const (@{const_name Ex}, _) $ _ => abstr_abs cvs ct
      | @{term "uminus :: int => _"} $ _ => abstr1 cvs ct
      | @{term "uminus :: real => _"} $ _ => abstr1 cvs ct
      | @{term "op + :: int => _"} $ _ $ _ => abstr2 cvs ct
      | @{term "op + :: real => _"} $ _ $ _ => abstr2 cvs ct
      | @{term "op - :: int => _"} $ _ $ _ => abstr2 cvs ct
      | @{term "op - :: real => _"} $ _ $ _ => abstr2 cvs ct
      | @{term "op * :: int => _"} $ _ $ _ => abstr2 cvs ct
      | @{term "op * :: real => _"} $ _ $ _ => abstr2 cvs ct
      | @{term "op div :: int => _"} $ _ $ _ => abstr2 cvs ct
      | @{term "op mod :: int => _"} $ _ $ _ => abstr2 cvs ct
      | @{term "op / :: real => _"} $ _ $ _ => abstr2 cvs ct
      | @{term "op < :: int => _"} $ _ $ _ => abstr2 cvs ct
      | @{term "op < :: real => _"} $ _ $ _ => abstr2 cvs ct
      | @{term "op <= :: int => _"} $ _ $ _ => abstr2 cvs ct
      | @{term "op <= :: real => _"} $ _ $ _ => abstr2 cvs ct
      | Const (@{const_name apply}, _) $ _ $ _ => abstr2 cvs ct
      | Const (@{const_name fun_upd}, _) $ _ $ _ $ _ => abstr3 cvs ct
      | t =>
          if is_atomic t orelse is_number t then pair ct
          else fresh_abstraction cvs ct)
  in abstr [] end

fun with_prems thms f ct =
  fold_rev (Thm.mk_binop @{cterm "op ==>"} o Thm.cprop_of) thms ct
  |> f
  |> fold (fn prem => fn th => Thm.implies_elim th prem) thms

in

fun by_abstraction ctxt thms prove = with_prems thms (fn ct =>
  let val (cu, cx) = abstract ct (abs_context ctxt)
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
    (More_Conv.rewrs_conv [set1, set2, set3, set4] else_conv
    (Conv.rewr_conv set5 then_conv Conv.arg_conv set_conv)) ct

  val dist1 = @{lemma "distinct [] == ~False" by simp}
  val dist2 = @{lemma "distinct [x] == ~False" by simp}
  val dist3 = @{lemma "distinct (x # xs) == x ~: set xs & distinct xs"
    by simp}

  fun binop_conv cv1 cv2 = Conv.combination_conv (Conv.arg_conv cv1) cv2
in
fun unfold_distinct_conv ct =
  (More_Conv.rewrs_conv [dist1, dist2] else_conv
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
      val prems = Simplifier.prems_of_ss ss
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
      val prems = prems_of_ss ss
    in
      (case find_first (eq_prop (le $ r $ s)) prems of
        NONE =>
          find_first (eq_prop (HOLogic.mk_not (less $ s $ r))) prems
          |> Option.map (fn thm => thm RS antisym_less2)
      | SOME thm => SOME (thm RS antisym_le2))
  end
  handle THM _ => NONE
in

fun make_simpset ctxt rules = Simplifier.context ctxt (HOL_ss
  addsimps @{thms ring_distribs} addsimps @{thms field_simps}
  addsimps [@{thm times_divide_eq_right}, @{thm times_divide_eq_left}]
  addsimps @{thms arith_special} addsimps @{thms less_bin_simps}
  addsimps @{thms le_bin_simps} addsimps @{thms eq_bin_simps}
  addsimps @{thms add_bin_simps} addsimps @{thms succ_bin_simps}
  addsimps @{thms minus_bin_simps} addsimps @{thms pred_bin_simps}
  addsimps @{thms mult_bin_simps} addsimps @{thms iszero_simps}
  addsimps @{thms array_rules}
  addsimprocs [
    Simplifier.simproc @{theory} "fast_int_arith" [
      "(m::int) < n", "(m::int) <= n", "(m::int) = n"] (K Lin_Arith.simproc),
    Simplifier.simproc @{theory} "fast_real_arith" [
      "(m::real) < n", "(m::real) <= n", "(m::real) = n"]
      (K Lin_Arith.simproc),
    Simplifier.simproc @{theory} "antisym_le" ["(x::'a::order) <= y"]
      (K prove_antisym_le),
    Simplifier.simproc @{theory} "antisym_less" ["~ (x::'a::linorder) < y"]
      (K prove_antisym_less)]
  addsimps rules)

end

end
