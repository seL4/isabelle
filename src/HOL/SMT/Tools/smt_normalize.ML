(*  Title:      HOL/SMT/Tools/smt_normalize.ML
    Author:     Sascha Boehme, TU Muenchen

Normalization steps on theorems required by SMT solvers:
  * unfold trivial let expressions,
  * replace negative numerals by negated positive numerals,
  * embed natural numbers into integers,
  * add extra rules specifying types and constants which occur frequently,
  * lift lambda terms,
  * make applications explicit for functions with varying number of arguments,
  * fully translate into object logic, add universal closure. 
*)

signature SMT_NORMALIZE =
sig
  val normalize_rule: Proof.context -> thm -> thm
  val instantiate_free: cterm * cterm -> thm -> thm
  val discharge_definition: cterm -> thm -> thm

  val trivial_let: Proof.context -> thm list -> thm list
  val positive_numerals: Proof.context -> thm list -> thm list
  val nat_as_int: Proof.context -> thm list -> thm list
  val unfold_defs: bool Config.T
  val add_pair_rules: Proof.context -> thm list -> thm list
  val add_fun_upd_rules: Proof.context -> thm list -> thm list
  val add_abs_min_max_rules: Proof.context -> thm list -> thm list

  datatype config =
    RewriteTrivialLets |
    RewriteNegativeNumerals |
    RewriteNaturalNumbers |
    AddPairRules |
    AddFunUpdRules |
    AddAbsMinMaxRules

  val normalize: config list -> Proof.context -> thm list ->
    cterm list * thm list

  val setup: theory -> theory
end

structure SMT_Normalize: SMT_NORMALIZE =
struct

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
in
val norm_binder_conv = norm_conv
end

fun cert ctxt = Thm.cterm_of (ProofContext.theory_of ctxt)

fun norm_meta_def cv thm = 
  let val thm' = Thm.combination thm (Thm.reflexive cv)
  in Thm.transitive thm' (Thm.beta_conversion false (Thm.rhs_of thm')) end

fun norm_def ctxt thm =
  (case Thm.prop_of thm of
    Const (@{const_name "=="}, _) $ _ $ Abs (_, T, _) =>
      let val v = Var ((Name.uu, #maxidx (Thm.rep_thm thm) + 1), T)
      in norm_def ctxt (norm_meta_def (cert ctxt v) thm) end
  | @{term Trueprop} $ (Const (@{const_name "op ="}, _) $ _ $ Abs _) =>
      norm_def ctxt (thm RS @{thm fun_cong})
  | _ => thm)

fun normalize_rule ctxt =
  Conv.fconv_rule (
    Thm.beta_conversion true then_conv
    Thm.eta_conversion then_conv
    norm_binder_conv ctxt) #>
  norm_def ctxt #>
  Drule.forall_intr_vars #>
  Conv.fconv_rule (ObjectLogic.atomize then_conv norm_binder_conv ctxt)

fun instantiate_free (cv, ct) thm =
  if Term.exists_subterm (equal (Thm.term_of cv)) (Thm.prop_of thm)
  then Thm.forall_elim ct (Thm.forall_intr cv thm)
  else thm

fun discharge_definition ct thm =
  let val (cv, cu) = Thm.dest_equals ct
  in
    Thm.implies_intr ct thm
    |> instantiate_free (cv, cu)
    |> (fn thm => Thm.implies_elim thm (Thm.reflexive cu))
  end

fun if_conv c cv1 cv2 ct = (if c (Thm.term_of ct) then cv1 else cv2) ct
fun if_true_conv c cv = if_conv c cv Conv.all_conv


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

  fun cond_let_conv ctxt = if_true_conv (Term.exists_subterm is_trivial_let)
    (More_Conv.top_conv let_conv ctxt)
in
fun trivial_let ctxt = map (Conv.fconv_rule (cond_let_conv ctxt))
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
  fun has_neg_number ctxt = Term.exists_subterm (is_neg_number ctxt)

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

  fun cond_pos_conv ctxt = if_true_conv (has_neg_number ctxt)
    (More_Conv.top_sweep_conv pos_conv ctxt)
in
fun positive_numerals ctxt = map (Conv.fconv_rule (cond_pos_conv ctxt))
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
    "int (nat (int a + int b)) = int a + int b"
    "int (nat (int a * int b)) = int a * int b"
    "int (nat (int a div int b)) = int a div int b"
    "int (nat (int a mod int b)) = int a mod int b"
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
fun nat_as_int ctxt thms =
  let
    fun norm thm = thm
      |> uses_nat_type (Thm.prop_of thm) ? Conv.fconv_rule (conv ctxt)
    val thms' = map norm thms
  in
    if exists (uses_nat_int o Thm.prop_of) thms' then nat_embedding @ thms'
    else thms'
  end
end


(* include additional rules *)

val (unfold_defs, unfold_defs_setup) =
  Attrib.config_bool "smt_unfold_defs" true

local
  val pair_rules = [@{thm fst_conv}, @{thm snd_conv}, @{thm pair_collapse}]

  val pair_type = (fn Type (@{type_name "*"}, _) => true | _ => false)
  val exists_pair_type = Term.exists_type (Term.exists_subtype pair_type)

  val fun_upd_rules = [@{thm fun_upd_same}, @{thm fun_upd_apply}]
  val is_fun_upd = (fn Const (@{const_name fun_upd}, _) => true | _ => false)
  val exists_fun_upd = Term.exists_subterm is_fun_upd
in
fun add_pair_rules _ thms =
  thms
  |> exists (exists_pair_type o Thm.prop_of) thms ? append pair_rules

fun add_fun_upd_rules _ thms =
  thms
  |> exists (exists_fun_upd o Thm.prop_of) thms ? append fun_upd_rules
end


local
  fun mk_entry t thm = (Term.head_of t, (thm, thm RS @{thm eq_reflection}))
  fun prepare_def thm =
    (case HOLogic.dest_Trueprop (Thm.prop_of thm) of
      Const (@{const_name "op ="}, _) $ t $ _ => mk_entry t thm
    | t => raise TERM ("prepare_def", [t]))

  val defs = map prepare_def [
    @{thm abs_if[where 'a = int]}, @{thm abs_if[where 'a = real]},
    @{thm min_def[where 'a = int]}, @{thm min_def[where 'a = real]},
    @{thm max_def[where 'a = int]}, @{thm max_def[where 'a = real]}]

  fun add_sym t = if AList.defined (op =) defs t then insert (op =) t else I
  fun add_syms thms = fold (Term.fold_aterms add_sym o Thm.prop_of) thms []

  fun unfold_conv ct =
    (case AList.lookup (op =) defs (Term.head_of (Thm.term_of ct)) of
      SOME (_, eq) => Conv.rewr_conv eq
    | NONE => Conv.all_conv) ct
in
fun add_abs_min_max_rules ctxt thms =
  if Config.get ctxt unfold_defs
  then map (Conv.fconv_rule (More_Conv.bottom_conv (K unfold_conv) ctxt)) thms
  else map fst (map_filter (AList.lookup (op =) defs) (add_syms thms)) @ thms
end


(* lift lambda terms into additional rules *)

local
  val meta_eq = @{cpat "op =="}
  val meta_eqT = hd (Thm.dest_ctyp (Thm.ctyp_of_term meta_eq))
  fun inst_meta cT = Thm.instantiate_cterm ([(meta_eqT, cT)], []) meta_eq
  fun mk_meta_eq ct cu = Thm.mk_binop (inst_meta (Thm.ctyp_of_term ct)) ct cu

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
in
fun lift_lambdas ctxt thms =
  let
    val declare_frees = fold (Thm.fold_terms Term.declare_term_frees)
    fun rewrite f thm cx =
      let val (thm', cx') = f (Thm.cprop_of thm) cx
      in (Thm.equal_elim thm' thm, cx') end

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

    val tab = prune_tab (fold (traverse o Thm.prop_of) thms Symtab.empty)
  in map (Conv.fconv_rule (sub_conv tab ctxt)) thms end
end


(* combined normalization *)

datatype config =
  RewriteTrivialLets |
  RewriteNegativeNumerals |
  RewriteNaturalNumbers |
  AddPairRules |
  AddFunUpdRules |
  AddAbsMinMaxRules

fun normalize config ctxt thms =
  let fun if_enabled c f = member (op =) config c ? f ctxt
  in
    thms
    |> if_enabled RewriteTrivialLets trivial_let
    |> if_enabled RewriteNegativeNumerals positive_numerals
    |> if_enabled RewriteNaturalNumbers nat_as_int
    |> if_enabled AddPairRules add_pair_rules
    |> if_enabled AddFunUpdRules add_fun_upd_rules
    |> if_enabled AddAbsMinMaxRules add_abs_min_max_rules
    |> map (normalize_rule ctxt)
    |> lift_lambdas ctxt
    |> apsnd (explicit_application ctxt)
  end

val setup = unfold_defs_setup

end
