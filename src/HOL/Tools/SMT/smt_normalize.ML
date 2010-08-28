(*  Title:      HOL/Tools/SMT/smt_normalize.ML
    Author:     Sascha Boehme, TU Muenchen

Normalization steps on theorems required by SMT solvers:
  * simplify trivial distincts (those with less than three elements),
  * rewrite bool case expressions as if expressions,
  * normalize numerals (e.g. replace negative numerals by negated positive
    numerals),
  * embed natural numbers into integers,
  * add extra rules specifying types and constants which occur frequently,
  * fully translate into object logic, add universal closure,
  * lift lambda terms,
  * make applications explicit for functions with varying number of arguments.
*)

signature SMT_NORMALIZE =
sig
  type extra_norm = thm list -> Proof.context -> thm list * Proof.context
  val normalize: extra_norm -> thm list -> Proof.context ->
    thm list * Proof.context
  val atomize_conv: Proof.context -> conv
  val eta_expand_conv: (Proof.context -> conv) -> Proof.context -> conv
end

structure SMT_Normalize: SMT_NORMALIZE =
struct

infix 2 ??
fun (test ?? f) x = if test x then f x else x

fun if_conv c cv1 cv2 ct = (if c (Thm.term_of ct) then cv1 else cv2) ct
fun if_true_conv c cv = if_conv c cv Conv.all_conv



(* simplification of trivial distincts (distinct should have at least
   three elements in the argument list) *)

local
  fun is_trivial_distinct (Const (@{const_name distinct}, _) $ t) =
        length (HOLogic.dest_list t) <= 2
    | is_trivial_distinct _ = false

  val thms = map mk_meta_eq @{lemma
    "distinct [] = True"
    "distinct [x] = True"
    "distinct [x, y] = (x ~= y)"
    by simp_all}
  fun distinct_conv _ =
    if_true_conv is_trivial_distinct (Conv.rewrs_conv thms)
in
fun trivial_distinct ctxt =
  map ((Term.exists_subterm is_trivial_distinct o Thm.prop_of) ??
    Conv.fconv_rule (Conv.top_conv distinct_conv ctxt))
end



(* rewrite bool case expressions as if expressions *)

local
  val is_bool_case = (fn
      Const (@{const_name "bool.bool_case"}, _) $ _ $ _ $ _ => true
    | _ => false)

  val thms = map mk_meta_eq @{lemma
    "(case P of True => x | False => y) = (if P then x else y)"
    "(case P of False => y | True => x) = (if P then x else y)"
    by simp_all}
  val unfold_conv = if_true_conv is_bool_case (Conv.rewrs_conv thms)
in
fun rewrite_bool_cases ctxt =
  map ((Term.exists_subterm is_bool_case o Thm.prop_of) ??
    Conv.fconv_rule (Conv.top_conv (K unfold_conv) ctxt))
end



(* normalization of numerals: rewriting of negative integer numerals into
   positive numerals, Numeral0 into 0, Numeral1 into 1 *)

local
  fun is_number_sort ctxt T =
    Sign.of_sort (ProofContext.theory_of ctxt) (T, @{sort number_ring})

  fun is_strange_number ctxt (t as Const (@{const_name number_of}, _) $ _) =
        (case try HOLogic.dest_number t of
          SOME (T, i) => is_number_sort ctxt T andalso i < 2
        | NONE => false)
    | is_strange_number _ _ = false

  val pos_numeral_ss = HOL_ss
    addsimps [@{thm Int.number_of_minus}, @{thm Int.number_of_Min}]
    addsimps [@{thm Int.number_of_Pls}, @{thm Int.numeral_1_eq_1}]
    addsimps @{thms Int.pred_bin_simps}
    addsimps @{thms Int.normalize_bin_simps}
    addsimps @{lemma
      "Int.Min = - Int.Bit1 Int.Pls"
      "Int.Bit0 (- Int.Pls) = - Int.Pls"
      "Int.Bit0 (- k) = - Int.Bit0 k"
      "Int.Bit1 (- k) = - Int.Bit1 (Int.pred k)"
      by simp_all (simp add: pred_def)}

  fun pos_conv ctxt = if_conv (is_strange_number ctxt)
    (Simplifier.rewrite (Simplifier.context ctxt pos_numeral_ss))
    Conv.no_conv
in
fun normalize_numerals ctxt =
  map ((Term.exists_subterm (is_strange_number ctxt) o Thm.prop_of) ??
    Conv.fconv_rule (Conv.top_sweep_conv pos_conv ctxt))
end



(* embedding of standard natural number operations into integer operations *)

local
  val nat_embedding = @{lemma
    "nat (int n) = n"
    "i >= 0 --> int (nat i) = i"
    "i < 0 --> int (nat i) = 0"
    by simp_all}

  val nat_rewriting = @{lemma
    "0 = nat 0"
    "1 = nat 1"
    "number_of i = nat (number_of i)"
    "int (nat 0) = 0"
    "int (nat 1) = 1"
    "a < b = (int a < int b)"
    "a <= b = (int a <= int b)"
    "Suc a = nat (int a + 1)"
    "a + b = nat (int a + int b)"
    "a - b = nat (int a - int b)"
    "a * b = nat (int a * int b)"
    "a div b = nat (int a div int b)"
    "a mod b = nat (int a mod int b)"
    "min a b = nat (min (int a) (int b))"
    "max a b = nat (max (int a) (int b))"
    "int (nat (int a + int b)) = int a + int b"
    "int (nat (int a * int b)) = int a * int b"
    "int (nat (int a div int b)) = int a div int b"
    "int (nat (int a mod int b)) = int a mod int b"
    "int (nat (min (int a) (int b))) = min (int a) (int b)"
    "int (nat (max (int a) (int b))) = max (int a) (int b)"
    by (simp_all add: nat_mult_distrib nat_div_distrib nat_mod_distrib
      int_mult[symmetric] zdiv_int[symmetric] zmod_int[symmetric])}

  fun on_positive num f x = 
    (case try HOLogic.dest_number (Thm.term_of num) of
      SOME (_, i) => if i >= 0 then SOME (f x) else NONE
    | NONE => NONE)

  val cancel_int_nat_ss = HOL_ss
    addsimps [@{thm Nat_Numeral.nat_number_of}]
    addsimps [@{thm Nat_Numeral.int_nat_number_of}]
    addsimps @{thms neg_simps}

  fun cancel_int_nat_simproc _ ss ct = 
    let
      val num = Thm.dest_arg (Thm.dest_arg ct)
      val goal = Thm.mk_binop @{cterm "op == :: int => _"} ct num
      val simpset = Simplifier.inherit_context ss cancel_int_nat_ss
      fun tac _ = Simplifier.simp_tac simpset 1
    in on_positive num (Goal.prove_internal [] goal) tac end

  val nat_ss = HOL_ss
    addsimps nat_rewriting
    addsimprocs [Simplifier.make_simproc {
      name = "cancel_int_nat_num", lhss = [@{cpat "int (nat _)"}],
      proc = cancel_int_nat_simproc, identifier = [] }]

  fun conv ctxt = Simplifier.rewrite (Simplifier.context ctxt nat_ss)

  val uses_nat_type = Term.exists_type (Term.exists_subtype (equal @{typ nat}))
  val uses_nat_int =
    Term.exists_subterm (member (op aconv) [@{term int}, @{term nat}])
in
fun nat_as_int ctxt =
  map ((uses_nat_type o Thm.prop_of) ?? Conv.fconv_rule (conv ctxt)) #>
  exists (uses_nat_int o Thm.prop_of) ?? append nat_embedding
end



(* further normalizations: beta/eta, universal closure, atomize *)

val eta_expand_eq = @{lemma "f == (%x. f x)" by (rule reflexive)}

fun eta_expand_conv cv ctxt =
  Conv.rewr_conv eta_expand_eq then_conv Conv.abs_conv (cv o snd) ctxt

local
  val eta_conv = eta_expand_conv

  fun keep_conv ctxt = Conv.binder_conv (norm_conv o snd) ctxt
  and eta_binder_conv ctxt = Conv.arg_conv (eta_conv norm_conv ctxt)
  and keep_let_conv ctxt = Conv.combination_conv
    (Conv.arg_conv (norm_conv ctxt)) (Conv.abs_conv (norm_conv o snd) ctxt)
  and unfold_let_conv ctxt = Conv.combination_conv
    (Conv.arg_conv (norm_conv ctxt)) (eta_conv norm_conv ctxt)
  and unfold_conv thm ctxt = Conv.rewr_conv thm then_conv keep_conv ctxt
  and unfold_ex1_conv ctxt = unfold_conv @{thm Ex1_def} ctxt
  and unfold_ball_conv ctxt = unfold_conv (mk_meta_eq @{thm Ball_def}) ctxt
  and unfold_bex_conv ctxt = unfold_conv (mk_meta_eq @{thm Bex_def}) ctxt
  and norm_conv ctxt ct =
    (case Thm.term_of ct of
      Const (@{const_name All}, _) $ Abs _ => keep_conv
    | Const (@{const_name All}, _) $ _ => eta_binder_conv
    | Const (@{const_name All}, _) => eta_conv eta_binder_conv
    | Const (@{const_name Ex}, _) $ Abs _ => keep_conv
    | Const (@{const_name Ex}, _) $ _ => eta_binder_conv
    | Const (@{const_name Ex}, _) => eta_conv eta_binder_conv
    | Const (@{const_name Let}, _) $ _ $ Abs _ => keep_let_conv
    | Const (@{const_name Let}, _) $ _ $ _ => unfold_let_conv
    | Const (@{const_name Let}, _) $ _ => eta_conv unfold_let_conv
    | Const (@{const_name Let}, _) => eta_conv (eta_conv unfold_let_conv)
    | Const (@{const_name Ex1}, _) $ _ => unfold_ex1_conv
    | Const (@{const_name Ex1}, _) => eta_conv unfold_ex1_conv 
    | Const (@{const_name Ball}, _) $ _ $ _ => unfold_ball_conv
    | Const (@{const_name Ball}, _) $ _ => eta_conv unfold_ball_conv
    | Const (@{const_name Ball}, _) => eta_conv (eta_conv unfold_ball_conv)
    | Const (@{const_name Bex}, _) $ _ $ _ => unfold_bex_conv
    | Const (@{const_name Bex}, _) $ _ => eta_conv unfold_bex_conv
    | Const (@{const_name Bex}, _) => eta_conv (eta_conv unfold_bex_conv)
    | Abs _ => Conv.abs_conv (norm_conv o snd)
    | _ $ _ => Conv.comb_conv o norm_conv
    | _ => K Conv.all_conv) ctxt ct

  fun is_normed t =
    (case t of
      Const (@{const_name All}, _) $ Abs (_, _, u) => is_normed u
    | Const (@{const_name All}, _) $ _ => false
    | Const (@{const_name All}, _) => false
    | Const (@{const_name Ex}, _) $ Abs (_, _, u) => is_normed u
    | Const (@{const_name Ex}, _) $ _ => false
    | Const (@{const_name Ex}, _) => false
    | Const (@{const_name Let}, _) $ u1 $ Abs (_, _, u2) =>
        is_normed u1 andalso is_normed u2
    | Const (@{const_name Let}, _) $ _ $ _ => false
    | Const (@{const_name Let}, _) $ _ => false
    | Const (@{const_name Let}, _) => false
    | Const (@{const_name Ex1}, _) => false
    | Const (@{const_name Ball}, _) => false
    | Const (@{const_name Bex}, _) => false
    | Abs (_, _, u) => is_normed u
    | u1 $ u2 => is_normed u1 andalso is_normed u2
    | _ => true)
in
fun norm_binder_conv ctxt = if_conv is_normed Conv.all_conv (norm_conv ctxt)
end

fun norm_def ctxt thm =
  (case Thm.prop_of thm of
    @{term Trueprop} $ (Const (@{const_name HOL.eq}, _) $ _ $ Abs _) =>
      norm_def ctxt (thm RS @{thm fun_cong})
  | Const (@{const_name "=="}, _) $ _ $ Abs _ =>
      norm_def ctxt (thm RS @{thm meta_eq_to_obj_eq})
  | _ => thm)

fun atomize_conv ctxt ct =
  (case Thm.term_of ct of
    @{term "op ==>"} $ _ $ _ =>
      Conv.binop_conv (atomize_conv ctxt) then_conv
      Conv.rewr_conv @{thm atomize_imp}
  | Const (@{const_name "=="}, _) $ _ $ _ =>
      Conv.binop_conv (atomize_conv ctxt) then_conv
      Conv.rewr_conv @{thm atomize_eq}
  | Const (@{const_name all}, _) $ Abs _ =>
      Conv.binder_conv (atomize_conv o snd) ctxt then_conv
      Conv.rewr_conv @{thm atomize_all}
  | _ => Conv.all_conv) ct

fun normalize_rule ctxt =
  Conv.fconv_rule (
    (* reduce lambda abstractions, except at known binders: *)
    Thm.beta_conversion true then_conv
    Thm.eta_conversion then_conv
    norm_binder_conv ctxt) #>
  norm_def ctxt #>
  Drule.forall_intr_vars #>
  Conv.fconv_rule (atomize_conv ctxt)



(* lift lambda terms into additional rules *)

local
  val meta_eq = @{cpat "op =="}
  val meta_eqT = hd (Thm.dest_ctyp (Thm.ctyp_of_term meta_eq))
  fun inst_meta cT = Thm.instantiate_cterm ([(meta_eqT, cT)], []) meta_eq
  fun mk_meta_eq ct cu = Thm.mk_binop (inst_meta (Thm.ctyp_of_term ct)) ct cu

  fun cert ctxt = Thm.cterm_of (ProofContext.theory_of ctxt)

  fun used_vars cvs ct =
    let
      val lookup = AList.lookup (op aconv) (map (` Thm.term_of) cvs)
      val add = (fn SOME ct => insert (op aconvc) ct | _ => I)
    in Term.fold_aterms (add o lookup) (Thm.term_of ct) [] end

  fun apply cv thm = 
    let val thm' = Thm.combination thm (Thm.reflexive cv)
    in Thm.transitive thm' (Thm.beta_conversion false (Thm.rhs_of thm')) end
  fun apply_def cvs eq = Thm.symmetric (fold apply cvs eq)

  fun replace_lambda cvs ct (cx as (ctxt, defs)) =
    let
      val cvs' = used_vars cvs ct
      val ct' = fold_rev Thm.cabs cvs' ct
    in
      (case Termtab.lookup defs (Thm.term_of ct') of
        SOME eq => (apply_def cvs' eq, cx)
      | NONE =>
          let
            val {T, ...} = Thm.rep_cterm ct' and n = Name.uu
            val (n', ctxt') = yield_singleton Variable.variant_fixes n ctxt
            val cu = mk_meta_eq (cert ctxt (Free (n', T))) ct'
            val (eq, ctxt'') = yield_singleton Assumption.add_assumes cu ctxt'
            val defs' = Termtab.update (Thm.term_of ct', eq) defs
          in (apply_def cvs' eq, (ctxt'', defs')) end)
    end

  fun none ct cx = (Thm.reflexive ct, cx)
  fun in_comb f g ct cx =
    let val (cu1, cu2) = Thm.dest_comb ct
    in cx |> f cu1 ||>> g cu2 |>> uncurry Thm.combination end
  fun in_arg f = in_comb none f
  fun in_abs f cvs ct (ctxt, defs) =
    let
      val (n, ctxt') = yield_singleton Variable.variant_fixes Name.uu ctxt
      val (cv, cu) = Thm.dest_abs (SOME n) ct
    in  (ctxt', defs) |> f (cv :: cvs) cu |>> Thm.abstract_rule n cv end

  fun traverse cvs ct =
    (case Thm.term_of ct of
      Const (@{const_name All}, _) $ Abs _ => in_arg (in_abs traverse cvs)
    | Const (@{const_name Ex}, _) $ Abs _ => in_arg (in_abs traverse cvs)
    | Const (@{const_name Let}, _) $ _ $ Abs _ =>
        in_comb (in_arg (traverse cvs)) (in_abs traverse cvs)
    | Abs _ => at_lambda cvs
    | _ $ _ => in_comb (traverse cvs) (traverse cvs)
    | _ => none) ct

  and at_lambda cvs ct =
    in_abs traverse cvs ct #-> (fn thm =>
    replace_lambda cvs (Thm.rhs_of thm) #>> Thm.transitive thm)

  fun has_free_lambdas t =
    (case t of
      Const (@{const_name All}, _) $ Abs (_, _, u) => has_free_lambdas u
    | Const (@{const_name Ex}, _) $ Abs (_, _, u) => has_free_lambdas u
    | Const (@{const_name Let}, _) $ u1 $ Abs (_, _, u2) =>
        has_free_lambdas u1 orelse has_free_lambdas u2
    | Abs _ => true
    | u1 $ u2 => has_free_lambdas u1 orelse has_free_lambdas u2
    | _ => false)

  fun lift_lm f thm cx =
    if not (has_free_lambdas (Thm.prop_of thm)) then (thm, cx)
    else cx |> f (Thm.cprop_of thm) |>> (fn thm' => Thm.equal_elim thm' thm)
in
fun lift_lambdas thms ctxt =
  let
    val cx = (ctxt, Termtab.empty)
    val (thms', (ctxt', defs)) = fold_map (lift_lm (traverse [])) thms cx
    val eqs = Termtab.fold (cons o normalize_rule ctxt' o snd) defs []
  in (eqs @ thms', ctxt') end
end



(* make application explicit for functions with varying number of arguments *)

local
  val const = prefix "c" and free = prefix "f"
  fun min i (e as (_, j)) = if i <> j then (true, Int.min (i, j)) else e
  fun add t i = Symtab.map_default (t, (false, i)) (min i)
  fun traverse t =
    (case Term.strip_comb t of
      (Const (n, _), ts) => add (const n) (length ts) #> fold traverse ts 
    | (Free (n, _), ts) => add (free n) (length ts) #> fold traverse ts
    | (Abs (_, _, u), ts) => fold traverse (u :: ts)
    | (_, ts) => fold traverse ts)
  val prune = (fn (n, (true, i)) => Symtab.update (n, i) | _ => I)
  fun prune_tab tab = Symtab.fold prune tab Symtab.empty

  fun binop_conv cv1 cv2 = Conv.combination_conv (Conv.arg_conv cv1) cv2
  fun nary_conv conv1 conv2 ct =
    (Conv.combination_conv (nary_conv conv1 conv2) conv2 else_conv conv1) ct
  fun abs_conv conv tb = Conv.abs_conv (fn (cv, cx) =>
    let val n = fst (Term.dest_Free (Thm.term_of cv))
    in conv (Symtab.update (free n, 0) tb) cx end)
  val fun_app_rule = @{lemma "f x == fun_app f x" by (simp add: fun_app_def)}
in
fun explicit_application ctxt thms =
  let
    fun sub_conv tb ctxt ct =
      (case Term.strip_comb (Thm.term_of ct) of
        (Const (n, _), ts) => app_conv tb (const n) (length ts) ctxt
      | (Free (n, _), ts) => app_conv tb (free n) (length ts) ctxt
      | (Abs _, _) => nary_conv (abs_conv sub_conv tb ctxt) (sub_conv tb ctxt)
      | (_, _) => nary_conv Conv.all_conv (sub_conv tb ctxt)) ct
    and app_conv tb n i ctxt =
      (case Symtab.lookup tb n of
        NONE => nary_conv Conv.all_conv (sub_conv tb ctxt)
      | SOME j => fun_app_conv tb ctxt (i - j))
    and fun_app_conv tb ctxt i ct = (
      if i = 0 then nary_conv Conv.all_conv (sub_conv tb ctxt)
      else
        Conv.rewr_conv fun_app_rule then_conv
        binop_conv (fun_app_conv tb ctxt (i-1)) (sub_conv tb ctxt)) ct

    fun needs_exp_app tab = Term.exists_subterm (fn
        Bound _ $ _ => true
      | Const (n, _) => Symtab.defined tab (const n)
      | Free (n, _) => Symtab.defined tab (free n)
      | _ => false)

    fun rewrite tab ctxt thm =
      if not (needs_exp_app tab (Thm.prop_of thm)) then thm
      else Conv.fconv_rule (sub_conv tab ctxt) thm

    val tab = prune_tab (fold (traverse o Thm.prop_of) thms Symtab.empty)
  in map (rewrite tab ctxt) thms end
end



(* combined normalization *)

type extra_norm = thm list -> Proof.context -> thm list * Proof.context

fun with_context f thms ctxt = (f ctxt thms, ctxt)

fun normalize extra_norm thms ctxt =
  thms
  |> trivial_distinct ctxt
  |> rewrite_bool_cases ctxt
  |> normalize_numerals ctxt
  |> nat_as_int ctxt
  |> rpair ctxt
  |-> extra_norm
  |-> with_context (fn cx => map (normalize_rule cx))
  |-> SMT_Monomorph.monomorph
  |-> lift_lambdas
  |-> with_context explicit_application

end
