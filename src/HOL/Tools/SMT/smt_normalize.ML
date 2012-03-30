(*  Title:      HOL/Tools/SMT/smt_normalize.ML
    Author:     Sascha Boehme, TU Muenchen

Normalization steps on theorems required by SMT solvers.
*)

signature SMT_NORMALIZE =
sig
  val atomize_conv: Proof.context -> conv
  type extra_norm = Proof.context -> thm list * thm list -> thm list * thm list
  val add_extra_norm: SMT_Utils.class * extra_norm -> Context.generic ->
    Context.generic
  val normalize: (int * (int option * thm)) list -> Proof.context ->
    (int * thm) list * Proof.context
  val setup: theory -> theory
end

structure SMT_Normalize: SMT_NORMALIZE =
struct


(* general theorem normalizations *)

(** instantiate elimination rules **)
 
local
  val (cpfalse, cfalse) =
    `SMT_Utils.mk_cprop (Thm.cterm_of @{theory} @{const False})

  fun inst f ct thm =
    let val cv = f (Drule.strip_imp_concl (Thm.cprop_of thm))
    in Thm.instantiate ([], [(cv, ct)]) thm end
in

fun instantiate_elim thm =
  (case Thm.concl_of thm of
    @{const Trueprop} $ Var (_, @{typ bool}) => inst Thm.dest_arg cfalse thm
  | Var _ => inst I cpfalse thm
  | _ => thm)

end


(** normalize definitions **)

fun norm_def thm =
  (case Thm.prop_of thm of
    @{const Trueprop} $ (Const (@{const_name HOL.eq}, _) $ _ $ Abs _) =>
      norm_def (thm RS @{thm fun_cong})
  | Const (@{const_name "=="}, _) $ _ $ Abs _ =>
      norm_def (thm RS @{thm meta_eq_to_obj_eq})
  | _ => thm)


(** atomization **)

fun atomize_conv ctxt ct =
  (case Thm.term_of ct of
    @{const "==>"} $ _ $ _ =>
      Conv.binop_conv (atomize_conv ctxt) then_conv
      Conv.rewr_conv @{thm atomize_imp}
  | Const (@{const_name "=="}, _) $ _ $ _ =>
      Conv.binop_conv (atomize_conv ctxt) then_conv
      Conv.rewr_conv @{thm atomize_eq}
  | Const (@{const_name all}, _) $ Abs _ =>
      Conv.binder_conv (atomize_conv o snd) ctxt then_conv
      Conv.rewr_conv @{thm atomize_all}
  | _ => Conv.all_conv) ct

val setup_atomize =
  fold SMT_Builtin.add_builtin_fun_ext'' [@{const_name "==>"},
    @{const_name "=="}, @{const_name all}, @{const_name Trueprop}]


(** unfold special quantifiers **)

local
  val ex1_def = mk_meta_eq @{lemma
    "Ex1 = (%P. EX x. P x & (ALL y. P y --> y = x))"
    by (rule ext) (simp only: Ex1_def)}

  val ball_def = mk_meta_eq @{lemma "Ball = (%A P. ALL x. x : A --> P x)"
    by (rule ext)+ (rule Ball_def)}

  val bex_def = mk_meta_eq @{lemma "Bex = (%A P. EX x. x : A & P x)"
    by (rule ext)+ (rule Bex_def)}

  val special_quants = [(@{const_name Ex1}, ex1_def),
    (@{const_name Ball}, ball_def), (@{const_name Bex}, bex_def)]
  
  fun special_quant (Const (n, _)) = AList.lookup (op =) special_quants n
    | special_quant _ = NONE

  fun special_quant_conv _ ct =
    (case special_quant (Thm.term_of ct) of
      SOME thm => Conv.rewr_conv thm
    | NONE => Conv.all_conv) ct
in

fun unfold_special_quants_conv ctxt =
  SMT_Utils.if_exists_conv (is_some o special_quant)
    (Conv.top_conv special_quant_conv ctxt)

val setup_unfolded_quants =
  fold (SMT_Builtin.add_builtin_fun_ext'' o fst) special_quants

end


(** trigger inference **)

local
  (*** check trigger syntax ***)

  fun dest_trigger (Const (@{const_name pat}, _) $ _) = SOME true
    | dest_trigger (Const (@{const_name nopat}, _) $ _) = SOME false
    | dest_trigger _ = NONE

  fun eq_list [] = false
    | eq_list (b :: bs) = forall (equal b) bs

  fun proper_trigger t =
    t
    |> these o try HOLogic.dest_list
    |> map (map_filter dest_trigger o these o try HOLogic.dest_list)
    |> (fn [] => false | bss => forall eq_list bss)

  fun proper_quant inside f t =
    (case t of
      Const (@{const_name All}, _) $ Abs (_, _, u) => proper_quant true f u
    | Const (@{const_name Ex}, _) $ Abs (_, _, u) => proper_quant true f u
    | @{const trigger} $ p $ u =>
        (if inside then f p else false) andalso proper_quant false f u
    | Abs (_, _, u) => proper_quant false f u
    | u1 $ u2 => proper_quant false f u1 andalso proper_quant false f u2
    | _ => true)

  fun check_trigger_error ctxt t =
    error ("SMT triggers must only occur under quantifier and multipatterns " ^
      "must have the same kind: " ^ Syntax.string_of_term ctxt t)

  fun check_trigger_conv ctxt ct =
    if proper_quant false proper_trigger (SMT_Utils.term_of ct) then
      Conv.all_conv ct
    else check_trigger_error ctxt (Thm.term_of ct)


  (*** infer simple triggers ***)

  fun dest_cond_eq ct =
    (case Thm.term_of ct of
      Const (@{const_name HOL.eq}, _) $ _ $ _ => Thm.dest_binop ct
    | @{const HOL.implies} $ _ $ _ => dest_cond_eq (Thm.dest_arg ct)
    | _ => raise CTERM ("no equation", [ct]))

  fun get_constrs thy (Type (n, _)) = these (Datatype.get_constrs thy n)
    | get_constrs _ _ = []

  fun is_constr thy (n, T) =
    let fun match (m, U) = m = n andalso Sign.typ_instance thy (T, U)
    in can (the o find_first match o get_constrs thy o Term.body_type) T end

  fun is_constr_pat thy t =
    (case Term.strip_comb t of
      (Free _, []) => true
    | (Const c, ts) => is_constr thy c andalso forall (is_constr_pat thy) ts
    | _ => false)

  fun is_simp_lhs ctxt t =
    (case Term.strip_comb t of
      (Const c, ts as _ :: _) =>
        not (SMT_Builtin.is_builtin_fun_ext ctxt c ts) andalso
        forall (is_constr_pat (Proof_Context.theory_of ctxt)) ts
    | _ => false)

  fun has_all_vars vs t =
    subset (op aconv) (vs, map Free (Term.add_frees t []))

  fun minimal_pats vs ct =
    if has_all_vars vs (Thm.term_of ct) then
      (case Thm.term_of ct of
        _ $ _ =>
          (case pairself (minimal_pats vs) (Thm.dest_comb ct) of
            ([], []) => [[ct]]
          | (ctss, ctss') => union (eq_set (op aconvc)) ctss ctss')
      | _ => [])
    else []

  fun proper_mpat _ _ _ [] = false
    | proper_mpat thy gen u cts =
        let
          val tps = (op ~~) (`gen (map Thm.term_of cts))
          fun some_match u = tps |> exists (fn (t', t) =>
            Pattern.matches thy (t', u) andalso not (t aconv u))
        in not (Term.exists_subterm some_match u) end

  val pat =
    SMT_Utils.mk_const_pat @{theory} @{const_name SMT.pat} SMT_Utils.destT1
  fun mk_pat ct = Thm.apply (SMT_Utils.instT' ct pat) ct

  fun mk_clist T = pairself (Thm.cterm_of @{theory})
    (HOLogic.cons_const T, HOLogic.nil_const T)
  fun mk_list (ccons, cnil) f cts = fold_rev (Thm.mk_binop ccons o f) cts cnil
  val mk_pat_list = mk_list (mk_clist @{typ SMT.pattern})
  val mk_mpat_list = mk_list (mk_clist @{typ "SMT.pattern list"})  
  fun mk_trigger ctss = mk_mpat_list (mk_pat_list mk_pat) ctss

  val trigger_eq =
    mk_meta_eq @{lemma "p = SMT.trigger t p" by (simp add: trigger_def)}

  fun insert_trigger_conv [] ct = Conv.all_conv ct
    | insert_trigger_conv ctss ct =
        let val (ctr, cp) = Thm.dest_binop (Thm.rhs_of trigger_eq) ||> rpair ct
        in Thm.instantiate ([], [cp, (ctr, mk_trigger ctss)]) trigger_eq end

  fun infer_trigger_eq_conv outer_ctxt (ctxt, cvs) ct =
    let
      val (lhs, rhs) = dest_cond_eq ct

      val vs = map Thm.term_of cvs
      val thy = Proof_Context.theory_of ctxt

      fun get_mpats ct =
        if is_simp_lhs ctxt (Thm.term_of ct) then minimal_pats vs ct
        else []
      val gen = Variable.export_terms ctxt outer_ctxt
      val filter_mpats = filter (proper_mpat thy gen (Thm.term_of rhs))

    in insert_trigger_conv (filter_mpats (get_mpats lhs)) ct end

  fun has_trigger (@{const SMT.trigger} $ _ $ _) = true
    | has_trigger _ = false

  fun try_trigger_conv cv ct =
    if SMT_Utils.under_quant has_trigger (SMT_Utils.term_of ct) then
      Conv.all_conv ct
    else Conv.try_conv cv ct

  fun infer_trigger_conv ctxt =
    if Config.get ctxt SMT_Config.infer_triggers then
      try_trigger_conv
        (SMT_Utils.under_quant_conv (infer_trigger_eq_conv ctxt) ctxt)
    else Conv.all_conv
in

fun trigger_conv ctxt =
  SMT_Utils.prop_conv
    (check_trigger_conv ctxt then_conv infer_trigger_conv ctxt)

val setup_trigger =
  fold SMT_Builtin.add_builtin_fun_ext''
    [@{const_name SMT.pat}, @{const_name SMT.nopat}, @{const_name SMT.trigger}]

end


(** adding quantifier weights **)

local
  (*** check weight syntax ***)

  val has_no_weight =
    not o Term.exists_subterm (fn @{const SMT.weight} => true | _ => false)

  fun is_weight (@{const SMT.weight} $ w $ t) =
        (case try HOLogic.dest_number w of
          SOME (_, i) => i >= 0 andalso has_no_weight t
        | _ => false)
    | is_weight t = has_no_weight t

  fun proper_trigger (@{const SMT.trigger} $ _ $ t) = is_weight t
    | proper_trigger t = is_weight t 

  fun check_weight_error ctxt t =
    error ("SMT weight must be a non-negative number and must only occur " ^
      "under the top-most quantifier and an optional trigger: " ^
      Syntax.string_of_term ctxt t)

  fun check_weight_conv ctxt ct =
    if SMT_Utils.under_quant proper_trigger (SMT_Utils.term_of ct) then
      Conv.all_conv ct
    else check_weight_error ctxt (Thm.term_of ct)


  (*** insertion of weights ***)

  fun under_trigger_conv cv ct =
    (case Thm.term_of ct of
      @{const SMT.trigger} $ _ $ _ => Conv.arg_conv cv
    | _ => cv) ct

  val weight_eq =
    mk_meta_eq @{lemma "p = SMT.weight i p" by (simp add: weight_def)}
  fun mk_weight_eq w =
    let val cv = Thm.dest_arg1 (Thm.rhs_of weight_eq)
    in
      Thm.instantiate ([], [(cv, Numeral.mk_cnumber @{ctyp int} w)]) weight_eq
    end

  fun add_weight_conv NONE _ = Conv.all_conv
    | add_weight_conv (SOME weight) ctxt =
        let val cv = Conv.rewr_conv (mk_weight_eq weight)
        in SMT_Utils.under_quant_conv (K (under_trigger_conv cv)) ctxt end
in

fun weight_conv weight ctxt = 
  SMT_Utils.prop_conv
    (check_weight_conv ctxt then_conv add_weight_conv weight ctxt)

val setup_weight = SMT_Builtin.add_builtin_fun_ext'' @{const_name SMT.weight}

end


(** combined general normalizations **)

fun gen_normalize1_conv ctxt weight =
  atomize_conv ctxt then_conv
  unfold_special_quants_conv ctxt then_conv
  Thm.beta_conversion true then_conv
  trigger_conv ctxt then_conv
  weight_conv weight ctxt

fun gen_normalize1 ctxt weight thm =
  thm
  |> instantiate_elim
  |> norm_def
  |> Conv.fconv_rule (Thm.beta_conversion true then_conv Thm.eta_conversion)
  |> Drule.forall_intr_vars
  |> Conv.fconv_rule (gen_normalize1_conv ctxt weight)

fun drop_fact_warning ctxt =
  let val pre = prefix "Warning: dropping assumption: "
  in SMT_Config.verbose_msg ctxt (pre o Display.string_of_thm ctxt) end

fun gen_norm1_safe ctxt (i, (weight, thm)) =
  if Config.get ctxt SMT_Config.drop_bad_facts then
    (case try (gen_normalize1 ctxt weight) thm of
      SOME thm' => SOME (i, thm')
    | NONE => (drop_fact_warning ctxt thm; NONE))
  else SOME (i, gen_normalize1 ctxt weight thm)

fun gen_normalize ctxt iwthms = map_filter (gen_norm1_safe ctxt) iwthms



(* unfolding of definitions and theory-specific rewritings *)

(** rewrite bool case expressions as if expressions **)

local
  fun is_bool_case (Const (@{const_name "bool.bool_case"}, _)) = true
    | is_bool_case _ = false

  val thm = mk_meta_eq @{lemma
    "bool_case = (%x y P. if P then x else y)" by (rule ext)+ simp}

  fun unfold_conv _ = SMT_Utils.if_true_conv is_bool_case (Conv.rewr_conv thm)
in

fun rewrite_bool_case_conv ctxt =
  SMT_Utils.if_exists_conv is_bool_case (Conv.top_conv unfold_conv ctxt)

val setup_bool_case =
  SMT_Builtin.add_builtin_fun_ext'' @{const_name "bool.bool_case"}

end


(** unfold abs, min and max **)

local
  val abs_def = mk_meta_eq @{lemma
    "abs = (%a::'a::abs_if. if a < 0 then - a else a)"
    by (rule ext) (rule abs_if)}

  val min_def = mk_meta_eq @{lemma "min = (%a b. if a <= b then a else b)"
    by (rule ext)+ (rule min_def)}

  val max_def = mk_meta_eq  @{lemma "max = (%a b. if a <= b then b else a)"
    by (rule ext)+ (rule max_def)}

  val defs = [(@{const_name min}, min_def), (@{const_name max}, max_def),
    (@{const_name abs}, abs_def)]

  fun is_builtinT ctxt T =
    SMT_Builtin.is_builtin_typ_ext ctxt (Term.domain_type T)

  fun abs_min_max ctxt (Const (n, T)) =
        (case AList.lookup (op =) defs n of
          NONE => NONE
        | SOME thm => if is_builtinT ctxt T then SOME thm else NONE)
    | abs_min_max _ _ = NONE

  fun unfold_amm_conv ctxt ct =
    (case abs_min_max ctxt (Thm.term_of ct) of
      SOME thm => Conv.rewr_conv thm
    | NONE => Conv.all_conv) ct
in

fun unfold_abs_min_max_conv ctxt =
  SMT_Utils.if_exists_conv (is_some o abs_min_max ctxt)
    (Conv.top_conv unfold_amm_conv ctxt)
  
val setup_abs_min_max = fold (SMT_Builtin.add_builtin_fun_ext'' o fst) defs

end


(** embedding of standard natural number operations into integer operations **)

local
  val nat_embedding = @{lemma
    "ALL n. nat (int n) = n"
    "ALL i. i >= 0 --> int (nat i) = i"
    "ALL i. i < 0 --> int (nat i) = 0"
    by simp_all}

  val simple_nat_ops = [
    @{const less (nat)}, @{const less_eq (nat)},
    @{const Suc}, @{const plus (nat)}, @{const minus (nat)}]

  val mult_nat_ops =
    [@{const times (nat)}, @{const div (nat)}, @{const mod (nat)}]

  val nat_ops = simple_nat_ops @ mult_nat_ops

  val nat_consts = nat_ops @ [@{const numeral (nat)},
    @{const zero_class.zero (nat)}, @{const one_class.one (nat)}]

  val nat_int_coercions = [@{const of_nat (int)}, @{const nat}]

  val builtin_nat_ops = nat_int_coercions @ simple_nat_ops

  val is_nat_const = member (op aconv) nat_consts

  fun is_nat_const' @{const of_nat (int)} = true
    | is_nat_const' t = is_nat_const t

  val expands = map mk_meta_eq @{lemma
    "0 = nat 0"
    "1 = nat 1"
    "(numeral :: num => nat) = (%i. nat (numeral i))"
    "op < = (%a b. int a < int b)"
    "op <= = (%a b. int a <= int b)"
    "Suc = (%a. nat (int a + 1))"
    "op + = (%a b. nat (int a + int b))"
    "op - = (%a b. nat (int a - int b))"
    "op * = (%a b. nat (int a * int b))"
    "op div = (%a b. nat (int a div int b))"
    "op mod = (%a b. nat (int a mod int b))"
    by (fastforce simp add: nat_mult_distrib nat_div_distrib nat_mod_distrib)+}

  val ints = map mk_meta_eq @{lemma
    "int 0 = 0"
    "int 1 = 1"
    "int (Suc n) = int n + 1"
    "int (n + m) = int n + int m"
    "int (n - m) = int (nat (int n - int m))"
    "int (n * m) = int n * int m"
    "int (n div m) = int n div int m"
    "int (n mod m) = int n mod int m"
    "int (if P then n else m) = (if P then int n else int m)"
    by (auto simp add: int_mult zdiv_int zmod_int)}

  fun mk_number_eq ctxt i lhs =
    let
      val eq = SMT_Utils.mk_cequals lhs (Numeral.mk_cnumber @{ctyp int} i)
      val ss = HOL_ss
        addsimps [@{thm Int.int_numeral}]
      fun tac _ = Simplifier.simp_tac (Simplifier.context ctxt ss) 1       
    in Goal.norm_result (Goal.prove_internal [] eq tac) end

  fun expand_head_conv cv ct =
    (case Thm.term_of ct of
      _ $ _ =>
        Conv.fun_conv (expand_head_conv cv) then_conv
        Thm.beta_conversion false
    | _ => cv) ct

  fun int_conv ctxt ct =
    (case Thm.term_of ct of
      @{const of_nat (int)} $ (n as (@{const numeral (nat)} $ _)) =>
        Conv.rewr_conv (mk_number_eq ctxt (snd (HOLogic.dest_number n)) ct)
    | @{const of_nat (int)} $ _ =>
        (Conv.rewrs_conv ints then_conv Conv.sub_conv ints_conv ctxt) else_conv
        Conv.sub_conv (Conv.top_sweep_conv nat_conv) ctxt        
    | _ => Conv.no_conv) ct

  and ints_conv ctxt = Conv.top_sweep_conv int_conv ctxt

  and expand_conv ctxt =
    SMT_Utils.if_conv (is_nat_const o Term.head_of)
      (expand_head_conv (Conv.rewrs_conv expands) then_conv ints_conv ctxt)
      (int_conv ctxt)

  and nat_conv ctxt = SMT_Utils.if_exists_conv is_nat_const'
    (Conv.top_sweep_conv expand_conv ctxt)

  val uses_nat_int = Term.exists_subterm (member (op aconv) nat_int_coercions)
in

val nat_as_int_conv = nat_conv

fun add_nat_embedding thms =
  if exists (uses_nat_int o Thm.prop_of) thms then (thms, nat_embedding)
  else (thms, [])

val setup_nat_as_int =
  SMT_Builtin.add_builtin_typ_ext (@{typ nat}, K true) #>
  fold (SMT_Builtin.add_builtin_fun_ext' o Term.dest_Const) builtin_nat_ops

end


(** normalize numerals **)

local
  (*
    rewrite negative numerals into positive numerals,
    rewrite Numeral0 into 0
    rewrite Numeral1 into 1
  *)

  fun is_strange_number ctxt (t as Const (@{const_name neg_numeral}, _) $ _) =
        (case try HOLogic.dest_number t of
          SOME (_, i) => SMT_Builtin.is_builtin_num ctxt t andalso i < 2
        | NONE => false)
    | is_strange_number _ _ = false

  val pos_num_ss = HOL_ss
    addsimps [@{thm Num.numeral_One}]
    addsimps [@{thm Num.neg_numeral_def}]

  fun norm_num_conv ctxt =
    SMT_Utils.if_conv (is_strange_number ctxt)
      (Simplifier.rewrite (Simplifier.context ctxt pos_num_ss)) Conv.no_conv
in

fun normalize_numerals_conv ctxt =
  SMT_Utils.if_exists_conv (is_strange_number ctxt)
    (Conv.top_sweep_conv norm_num_conv ctxt)

end


(** combined unfoldings and rewritings **)

fun unfold_conv ctxt =
  rewrite_bool_case_conv ctxt then_conv
  unfold_abs_min_max_conv ctxt then_conv
  nat_as_int_conv ctxt then_conv
  Thm.beta_conversion true

fun unfold1 ctxt = map (apsnd (Conv.fconv_rule (unfold_conv ctxt)))

fun burrow_ids f ithms =
  let
    val (is, thms) = split_list ithms
    val (thms', extra_thms) = f thms
  in (is ~~ thms') @ map (pair ~1) extra_thms end

fun unfold2 ithms ctxt =
  ithms
  |> map (apsnd (Conv.fconv_rule (normalize_numerals_conv ctxt)))
  |> burrow_ids add_nat_embedding
  |> rpair ctxt



(* overall normalization *)

type extra_norm = Proof.context -> thm list * thm list -> thm list * thm list

structure Extra_Norms = Generic_Data
(
  type T = extra_norm SMT_Utils.dict
  val empty = []
  val extend = I
  fun merge data = SMT_Utils.dict_merge fst data
)

fun add_extra_norm (cs, norm) =
  Extra_Norms.map (SMT_Utils.dict_update (cs, norm))

fun apply_extra_norms ithms ctxt =
  let
    val cs = SMT_Config.solver_class_of ctxt
    val es = SMT_Utils.dict_lookup (Extra_Norms.get (Context.Proof ctxt)) cs
  in (burrow_ids (fold (fn e => e ctxt) es o rpair []) ithms, ctxt) end

local
  val ignored = member (op =) [@{const_name All}, @{const_name Ex},
    @{const_name Let}, @{const_name If}, @{const_name HOL.eq}]

  val schematic_consts_of =
    let
      fun collect (@{const SMT.trigger} $ p $ t) =
            collect_trigger p #> collect t
        | collect (t $ u) = collect t #> collect u
        | collect (Abs (_, _, t)) = collect t
        | collect (t as Const (n, _)) = 
            if not (ignored n) then Monomorph.add_schematic_consts_of t else I
        | collect _ = I
      and collect_trigger t =
        let val dest = these o try HOLogic.dest_list 
        in fold (fold collect_pat o dest) (dest t) end
      and collect_pat (Const (@{const_name SMT.pat}, _) $ t) = collect t
        | collect_pat (Const (@{const_name SMT.nopat}, _) $ t) = collect t
        | collect_pat _ = I
    in (fn t => collect t Symtab.empty) end
in

fun monomorph xthms ctxt =
  let val (xs, thms) = split_list xthms
  in
    (map (pair 1) thms, ctxt)
    |-> Monomorph.monomorph schematic_consts_of
    |>> maps (uncurry (map o pair)) o map2 pair xs o map (map snd)
  end

end

fun normalize iwthms ctxt =
  iwthms
  |> gen_normalize ctxt
  |> unfold1 ctxt
  |> rpair ctxt
  |-> monomorph
  |-> unfold2
  |-> apply_extra_norms

val setup = Context.theory_map (
  setup_atomize #>
  setup_unfolded_quants #>
  setup_trigger #>
  setup_weight #>
  setup_bool_case #>
  setup_abs_min_max #>
  setup_nat_as_int)

end
