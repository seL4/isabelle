(*  Title:      HOL/SMT/Tools/smt_normalize.ML
    Author:     Sascha Boehme, TU Muenchen

Normalization steps on theorems required by SMT solvers:
  * unfold trivial let expressions,
  * simplify trivial distincts (those with less than three elements),
  * rewrite bool case expressions as if expressions,
  * replace negative numerals by negated positive numerals,
  * embed natural numbers into integers,
  * add extra rules specifying types and constants which occur frequently,
  * lift lambda terms,
  * make applications explicit for functions with varying number of arguments,
  * fully translate into object logic, add universal closure. 
*)

signature SMT_NORMALIZE =
sig
  val instantiate_free: cterm * cterm -> thm -> thm
  val discharge_definition: cterm -> thm -> thm

  val normalize: Proof.context -> thm list -> cterm list * thm list
end

structure SMT_Normalize: SMT_NORMALIZE =
struct

infix 2 ??
fun (test ?? f) x = if test x then f x else x

fun if_conv c cv1 cv2 ct = (if c (Thm.term_of ct) then cv1 else cv2) ct
fun if_true_conv c cv = if_conv c cv Conv.all_conv

fun instantiate_free (cv, ct) =
  (Term.exists_subterm (equal (Thm.term_of cv)) o Thm.prop_of) ??
  (Thm.forall_elim ct o Thm.forall_intr cv)

fun discharge_definition ct thm =
  let val (cv, cu) = Thm.dest_equals ct
  in
    Thm.implies_intr ct thm
    |> instantiate_free (cv, cu)
    |> (fn thm => Thm.implies_elim thm (Thm.reflexive cu))
  end



(* simplification of trivial let expressions (whose bound variables occur at
   most once) *)

local
  fun count i (Bound j) = if j = i then 1 else 0
    | count i (t $ u) = count i t + count i u
    | count i (Abs (_, _, t)) = count (i + 1) t
    | count _ _ = 0

  fun is_trivial_let (Const (@{const_name Let}, _) $ _ $ Abs (_, _, t)) =
        (count 0 t <= 1)
    | is_trivial_let _ = false

  fun let_conv _ = if_true_conv is_trivial_let (Conv.rewr_conv @{thm Let_def})
in
fun trivial_let ctxt =
  map ((Term.exists_subterm is_trivial_let o Thm.prop_of) ??
    Conv.fconv_rule (More_Conv.top_conv let_conv ctxt))
end



(* simplification of trivial distincts (distinct should have at least
   three elements in the argument list) *)

local
  fun is_trivial_distinct (Const (@{const_name distinct}, _) $ t) =
        length (HOLogic.dest_list t) <= 2
    | is_trivial_distinct _ = false

  val thms = @{lemma
    "distinct [] == True"
    "distinct [x] == True"
    "distinct [x, y] == (x ~= y)"
    by simp_all}
  fun distinct_conv _ =
    if_true_conv is_trivial_distinct (More_Conv.rewrs_conv thms)
in
fun trivial_distinct ctxt =
  map ((Term.exists_subterm is_trivial_distinct o Thm.prop_of) ??
    Conv.fconv_rule (More_Conv.top_conv distinct_conv ctxt))
end



(* rewrite bool case expressions as if expressions *)

local
  val is_bool_case = (fn
      Const (@{const_name "bool.bool_case"}, _) $ _ $ _ $ _ => true
    | _ => false)

  val thms = @{lemma
    "(case P of True => x | False => y) == (if P then x else y)"
    "(case P of False => y | True => x) == (if P then x else y)"
    by (rule eq_reflection, simp)+}
  val unfold_conv = if_true_conv is_bool_case (More_Conv.rewrs_conv thms)
in
fun rewrite_bool_cases ctxt =
  map ((Term.exists_subterm is_bool_case o Thm.prop_of) ??
    Conv.fconv_rule (More_Conv.top_conv (K unfold_conv) ctxt))
end



(* rewriting of negative integer numerals into positive numerals *)

local
  fun neg_numeral @{term Int.Min} = true
    | neg_numeral _ = false
  fun is_number_sort thy T = Sign.of_sort thy (T, @{sort number_ring})
  fun is_neg_number ctxt (Const (@{const_name number_of}, T) $ t) =
        Term.exists_subterm neg_numeral t andalso
        is_number_sort (ProofContext.theory_of ctxt) (Term.body_type T)
    | is_neg_number _ _ = false

  val pos_numeral_ss = HOL_ss
    addsimps [@{thm Int.number_of_minus}, @{thm Int.number_of_Min}]
    addsimps [@{thm Int.numeral_1_eq_1}]
    addsimps @{thms Int.pred_bin_simps}
    addsimps @{thms Int.normalize_bin_simps}
    addsimps @{lemma
      "Int.Min = - Int.Bit1 Int.Pls"
      "Int.Bit0 (- Int.Pls) = - Int.Pls"
      "Int.Bit0 (- k) = - Int.Bit0 k"
      "Int.Bit1 (- k) = - Int.Bit1 (Int.pred k)"
      by simp_all (simp add: pred_def)}

  fun pos_conv ctxt = if_conv (is_neg_number ctxt)
    (Simplifier.rewrite (Simplifier.context ctxt pos_numeral_ss))
    Conv.no_conv
in
fun positive_numerals ctxt =
  map ((Term.exists_subterm (is_neg_number ctxt) o Thm.prop_of) ??
    Conv.fconv_rule (More_Conv.top_sweep_conv pos_conv ctxt))
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
    by (simp add: nat_mult_distrib nat_div_distrib nat_mod_distrib
      int_mult[symmetric] zdiv_int[symmetric] zmod_int[symmetric])+}

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



(* include additional rules *)

local
  val pair_rules = [@{thm fst_conv}, @{thm snd_conv}, @{thm pair_collapse}]

  val pair_type = (fn Type (@{type_name "*"}, _) => true | _ => false)
  val exists_pair_type = Term.exists_type (Term.exists_subtype pair_type)

  val add_pair_rules =
    exists (exists_pair_type o Thm.prop_of) ?? append pair_rules


  val fun_upd_rules = [@{thm fun_upd_same}, @{thm fun_upd_apply}]

  val is_fun_upd = (fn Const (@{const_name fun_upd}, _) => true | _ => false)
  val exists_fun_upd = Term.exists_subterm is_fun_upd

  val add_fun_upd_rules =
    exists (exists_fun_upd o Thm.prop_of) ?? append fun_upd_rules
in
val add_rules = add_pair_rules #> add_fun_upd_rules
end



(* unfold definitions of specific constants *)

local
  fun mk_entry (t as Const (n, _)) thm = ((n, t), thm)
    | mk_entry t _ = raise TERM ("mk_entry", [t])
  fun prepare_def thm =
    (case Thm.prop_of thm of
      Const (@{const_name "=="}, _) $ t $ _ => mk_entry (Term.head_of t) thm
    | t => raise TERM ("prepare_def", [t]))

  val defs = map prepare_def [
    @{thm abs_if[where 'a = int, THEN eq_reflection]},
    @{thm abs_if[where 'a = real, THEN eq_reflection]},
    @{thm min_def[where 'a = int, THEN eq_reflection]},
    @{thm min_def[where 'a = real, THEN eq_reflection]},
    @{thm max_def[where 'a = int, THEN eq_reflection]},
    @{thm max_def[where 'a = real, THEN eq_reflection]},
    @{thm Ex1_def}, @{thm Ball_def}, @{thm Bex_def}]

  fun matches thy ((t as Const (n, _)), (m, p)) =
        n = m andalso Pattern.matches thy (p, t)
    | matches _ _ = false

  fun lookup_def thy = AList.lookup (matches thy) defs
  fun lookup_def_head thy = lookup_def thy o Term.head_of

  fun occurs_def thy = Term.exists_subterm (is_some o lookup_def thy)

  fun unfold_def_conv ctxt ct =
    (case lookup_def_head (ProofContext.theory_of ctxt) (Thm.term_of ct) of
      SOME thm => Conv.rewr_conv thm
    | NONE => Conv.all_conv) ct
in
fun unfold_defs ctxt =
  (occurs_def (ProofContext.theory_of ctxt) o Thm.prop_of) ??
  Conv.fconv_rule (More_Conv.top_conv unfold_def_conv ctxt)
end



(* further normalizations: beta/eta, universal closure, atomize *)

local
  val all1 = @{lemma "All P == ALL x. P x" by (rule reflexive)}
  val all2 = @{lemma "All == (%P. ALL x. P x)" by (rule reflexive)}
  val ex1 = @{lemma "Ex P == EX x. P x" by (rule reflexive)}
  val ex2 = @{lemma "Ex == (%P. EX x. P x)" by (rule reflexive)}
  val let1 = @{lemma "Let c P == let x = c in P x" by (rule reflexive)}
  val let2 = @{lemma "Let c == (%P. let x = c in P x)" by (rule reflexive)}
  val let3 = @{lemma "Let == (%c P. let x = c in P x)" by (rule reflexive)}

  fun all_abs_conv cv ctxt =
    Conv.abs_conv (all_abs_conv cv o snd) ctxt else_conv cv ctxt
  fun keep_conv ctxt = More_Conv.binder_conv norm_conv ctxt
  and unfold_conv rule ctxt =
    Conv.rewr_conv rule then_conv all_abs_conv keep_conv ctxt
  and unfold_let_conv rule ctxt =
    Conv.rewr_conv rule then_conv
    all_abs_conv (fn cx => Conv.combination_conv
      (Conv.arg_conv (norm_conv cx)) (Conv.abs_conv (norm_conv o snd) cx)) ctxt
  and norm_conv ctxt ct =
    (case Thm.term_of ct of
      Const (@{const_name All}, _) $ Abs _ => keep_conv
    | Const (@{const_name All}, _) $ _ => unfold_conv all1
    | Const (@{const_name All}, _) => unfold_conv all2
    | Const (@{const_name Ex}, _) $ Abs _ => keep_conv
    | Const (@{const_name Ex}, _) $ _ => unfold_conv ex1
    | Const (@{const_name Ex}, _) => unfold_conv ex2
    | Const (@{const_name Let}, _) $ _ $ Abs _ => keep_conv
    | Const (@{const_name Let}, _) $ _ $ _ => unfold_let_conv let1
    | Const (@{const_name Let}, _) $ _ => unfold_let_conv let2
    | Const (@{const_name Let}, _) => unfold_let_conv let3
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
    | Abs (_, _, u) => is_normed u
    | u1 $ u2 => is_normed u1 andalso is_normed u2
    | _ => true)
in
fun norm_binder_conv ctxt = if_conv is_normed Conv.all_conv (norm_conv ctxt)
end

fun norm_def ctxt thm =
  (case Thm.prop_of thm of
    @{term Trueprop} $ (Const (@{const_name "op ="}, _) $ _ $ Abs _) =>
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
      More_Conv.binder_conv atomize_conv ctxt then_conv
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

  fun norm_meta_def cv thm = 
    let val thm' = Thm.combination thm (Thm.reflexive cv)
    in Thm.transitive thm' (Thm.beta_conversion false (Thm.rhs_of thm')) end

  fun cert ctxt = Thm.cterm_of (ProofContext.theory_of ctxt)

  val fresh_name = yield_singleton Name.variants

  fun used_vars cvs ct =
    let
      val lookup = AList.lookup (op aconv) (map (` Thm.term_of) cvs)
      val add = (fn (SOME ct) => insert (op aconvc) ct | _ => I)
    in Term.fold_aterms (add o lookup) (Thm.term_of ct) [] end
  fun make_def cvs eq = Thm.symmetric (fold norm_meta_def cvs eq)
  fun add_def ct thm = Termtab.update (Thm.term_of ct, (serial (), thm))

  fun replace ctxt cvs ct (cx as (nctxt, defs)) =
    let
      val cvs' = used_vars cvs ct
      val ct' = fold_rev Thm.cabs cvs' ct
    in
      (case Termtab.lookup defs (Thm.term_of ct') of
        SOME (_, eq) => (make_def cvs' eq, cx)
      | NONE =>
          let
            val {T, ...} = Thm.rep_cterm ct'
            val (n, nctxt') = fresh_name "" nctxt
            val eq = Thm.assume (mk_meta_eq (cert ctxt (Free (n, T))) ct')
          in (make_def cvs' eq, (nctxt', add_def ct' eq defs)) end)
    end

  fun none ct cx = (Thm.reflexive ct, cx)
  fun in_comb f g ct cx =
    let val (cu1, cu2) = Thm.dest_comb ct
    in cx |> f cu1 ||>> g cu2 |>> uncurry Thm.combination end
  fun in_arg f = in_comb none f
  fun in_abs f cvs ct (nctxt, defs) =
    let
      val (n, nctxt') = fresh_name Name.uu nctxt
      val (cv, cu) = Thm.dest_abs (SOME n) ct
    in f (cv :: cvs) cu (nctxt', defs) |>> Thm.abstract_rule n cv end

  fun replace_lambdas ctxt =
    let
      fun repl cvs ct =
        (case Thm.term_of ct of
          Const (@{const_name All}, _) $ Abs _ => in_arg (in_abs repl cvs)
        | Const (@{const_name Ex}, _) $ Abs _ => in_arg (in_abs repl cvs)
        | Const _ $ Abs _ => in_arg (at_lambda cvs)
        | Const (@{const_name Let}, _) $ _ $ Abs _ =>
            in_comb (in_arg (repl cvs)) (in_abs repl cvs)
        | Abs _ => at_lambda cvs
        | _ $ _ => in_comb (repl cvs) (repl cvs)
        | _ => none) ct
      and at_lambda cvs ct =
        in_abs repl cvs ct #-> (fn thm =>
        replace ctxt cvs (Thm.rhs_of thm) #>> Thm.transitive thm)
    in repl [] end

  fun has_free_lambdas t =
    (case t of
      Const (@{const_name All}, _) $ Abs (_, _, u) => has_free_lambdas u
    | Const (@{const_name Ex}, _) $ Abs (_, _, u) => has_free_lambdas u
    | Const (@{const_name Let}, _) $ u1 $ Abs (_, _, u2) =>
        has_free_lambdas u1 orelse has_free_lambdas u2
    | Abs _ => true
    | u1 $ u2 => has_free_lambdas u1 orelse has_free_lambdas u2
    | _ => false)
in
fun lift_lambdas ctxt thms =
  let
    val declare_frees = fold (Thm.fold_terms Term.declare_term_frees)
    fun rewrite f thm cx =
      if not (has_free_lambdas (Thm.prop_of thm)) then (thm, cx)
      else f (Thm.cprop_of thm) cx |>> (fn thm' => Thm.equal_elim thm' thm)

    val rev_int_fst_ord = rev_order o int_ord o pairself fst
    fun ordered_values tab =
      Termtab.fold (fn (_, x) => OrdList.insert rev_int_fst_ord x) tab []
      |> map snd

    val (thms', (_, defs)) =
      (declare_frees thms (Name.make_context []), Termtab.empty)
      |> fold_map (rewrite (replace_lambdas ctxt)) thms
    val eqs = ordered_values defs
  in
    (maps (#hyps o Thm.crep_thm) eqs, map (normalize_rule ctxt) eqs @ thms')
  end
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
  val apply_rule = @{lemma "f x == apply f x" by (simp add: apply_def)}
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
      | SOME j => apply_conv tb ctxt (i - j))
    and apply_conv tb ctxt i ct = (
      if i = 0 then nary_conv Conv.all_conv (sub_conv tb ctxt)
      else
        Conv.rewr_conv apply_rule then_conv
        binop_conv (apply_conv tb ctxt (i-1)) (sub_conv tb ctxt)) ct

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

fun normalize ctxt thms =
  thms
  |> trivial_let ctxt
  |> trivial_distinct ctxt
  |> rewrite_bool_cases ctxt
  |> positive_numerals ctxt
  |> nat_as_int ctxt
  |> add_rules
  |> map (unfold_defs ctxt #> normalize_rule ctxt)
  |> lift_lambdas ctxt
  |> apsnd (explicit_application ctxt)

end
