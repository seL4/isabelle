(*  Title:      HOL/SMT/Tools/z3_proof_rules.ML
    Author:     Sascha Boehme, TU Muenchen

Z3 proof rules and their reconstruction.
*)

signature Z3_PROOF_RULES =
sig
  (*proof rule names*)
  type rule  
  val rule_of_string: string -> rule option
  val string_of_rule: rule -> string

  (*proof reconstruction*)
  type proof
  val make_proof: rule -> int list -> cterm * cterm list -> proof
  val prove: Proof.context -> thm list option -> proof Inttab.table -> int ->
    thm

  (*setup*)
  val setup: theory -> theory
end

structure Z3_Proof_Rules: Z3_PROOF_RULES =
struct

structure T = Z3_Proof_Terms

fun z3_exn msg = raise SMT_Solver.SMT ("Z3 proof reconstruction: " ^ msg)


(* proof rule names *)

datatype rule = TrueAxiom | Asserted | Goal | ModusPonens | Reflexivity |
  Symmetry | Transitivity | TransitivityStar | Monotonicity | QuantIntro |
  Distributivity | AndElim | NotOrElim | Rewrite | RewriteStar | PullQuant |
  PullQuantStar | PushQuant | ElimUnusedVars | DestEqRes | QuantInst |
  Hypothesis | Lemma | UnitResolution | IffTrue | IffFalse | Commutativity |
  DefAxiom | IntroDef | ApplyDef | IffOeq | NnfPos | NnfNeg | NnfStar |
  CnfStar | Skolemize | ModusPonensOeq | ThLemma

val rule_names = Symtab.make [
  ("true-axiom", TrueAxiom),
  ("asserted", Asserted),
  ("goal", Goal),
  ("mp", ModusPonens),
  ("refl", Reflexivity),
  ("symm", Symmetry),
  ("trans", Transitivity),
  ("trans*", TransitivityStar),
  ("monotonicity", Monotonicity),
  ("quant-intro", QuantIntro),
  ("distributivity", Distributivity),
  ("and-elim", AndElim),
  ("not-or-elim", NotOrElim),
  ("rewrite", Rewrite),
  ("rewrite*", RewriteStar),
  ("pull-quant", PullQuant),
  ("pull-quant*", PullQuantStar),
  ("push-quant", PushQuant),
  ("elim-unused", ElimUnusedVars),
  ("der", DestEqRes),
  ("quant-inst", QuantInst),
  ("hypothesis", Hypothesis),
  ("lemma", Lemma),
  ("unit-resolution", UnitResolution),
  ("iff-true", IffTrue),
  ("iff-false", IffFalse),
  ("commutativity", Commutativity),
  ("def-axiom", DefAxiom),
  ("intro-def", IntroDef),
  ("apply-def", ApplyDef),
  ("iff~", IffOeq),
  ("nnf-pos", NnfPos),
  ("nnf-neg", NnfNeg),
  ("nnf*", NnfStar),
  ("cnf*", CnfStar),
  ("sk", Skolemize),
  ("mp~", ModusPonensOeq),
  ("th-lemma", ThLemma)]

val rule_of_string = Symtab.lookup rule_names
fun string_of_rule r =
  let fun fit (s, r') = if r = r' then SOME s else NONE 
  in the (Symtab.get_first NONE fit rule_names) end


(* proof representation *)

datatype theorem =
  Thm of thm |
  MetaEq of thm |
  Literals of thm * thm Termtab.table

fun thm_of (Thm thm) = thm
  | thm_of (MetaEq thm) = thm COMP @{thm meta_eq_to_obj_eq}
  | thm_of (Literals (thm, _)) = thm

fun meta_eq_of (MetaEq thm) = thm
  | meta_eq_of p = mk_meta_eq (thm_of p)

datatype proof =
  Unproved of {
    rule: rule,
    subs: int list,
    prop: cterm,
    vars: cterm list } |
  Sequent of {
    hyps: cterm list,
    vars: cterm list,
    thm: theorem }

fun make_proof r ps (ct, cvs) = Unproved {rule=r, subs=ps, prop=ct, vars=cvs}


(* proof reconstruction utilities *)

fun try_apply ctxt name nfs ct =
  let
    val trace = SMT_Solver.trace_msg ctxt I

    fun first [] = z3_exn (name ^ " failed")
      | first ((n, f) :: nfs) =
          (case try f ct of
            SOME thm => (trace (n ^ " succeeded"); thm)
          | NONE => (trace (n ^ " failed"); first nfs))
  in first nfs end

fun prop_of thm = (case Thm.prop_of thm of @{term Trueprop} $ t => t | t => t)

fun as_meta_eq ct = uncurry T.mk_meta_eq (Thm.dest_binop ct)

fun by_tac' tac ct = Goal.norm_result (Goal.prove_internal [] ct (K (tac 1)))
fun by_tac tac ct = by_tac' tac (T.mk_prop ct)

fun match_instantiate' f ct thm =
  Thm.instantiate (Thm.match (f (Thm.cprop_of thm), ct)) thm
val match_instantiate = match_instantiate' I

local
  fun maybe_instantiate ct thm =
    try Thm.first_order_match (Thm.cprop_of thm, ct)
    |> Option.map (fn inst => Thm.instantiate inst thm)
in
fun thm_net_of thms =
  let fun insert thm = Net.insert_term (K false) (Thm.prop_of thm, thm)
  in fold insert thms Net.empty end

fun first_of thms ct = get_first (maybe_instantiate ct) thms
fun net_instance net ct = first_of (Net.match_term net (Thm.term_of ct)) ct
end

fun certify ctxt = Thm.cterm_of (ProofContext.theory_of ctxt)
fun certify_var ctxt idx T = certify ctxt (Var (("x", idx), T))
fun certify_free ctxt idx T = certify ctxt (Free ("x" ^ string_of_int idx, T))

fun varify ctxt =
  let
    fun varify1 cv thm =
      let
        val T = Thm.typ_of (Thm.ctyp_of_term cv)
        val v = certify_var ctxt (Thm.maxidx_of thm + 1) T
       in SMT_Normalize.instantiate_free (cv, v) thm end
  in fold varify1 end

fun under_assumption f ct =
  let val ct' = T.mk_prop ct
  in Thm.implies_intr ct' (f (Thm.assume ct')) end

fun with_conv conv prove ct =
  let val eq = Thm.symmetric (conv ct)
  in Thm.equal_elim eq (prove (Thm.lhs_of eq)) end

fun list2 (x, y) = [x, y]

fun precompose f rule = (f (Thm.cprem_of rule 1), f, rule)

fun discharge p pq = Thm.implies_elim pq p

fun compose (cvs, f, rule) thm =
  let fun inst thm = Thm.instantiate ([], cvs ~~ f (Thm.cprop_of thm))
  in discharge thm (inst thm rule) end

fun make_hyp_def thm = (* |- c x == t x ==> P (c x)  ~~>  c == t |- P (c x) *) 
  let
    val (lhs, rhs) = Thm.dest_binop (Thm.cprem_of thm 1)
    val (cf, cvs) = Drule.strip_comb lhs
    val eq = T.mk_meta_eq cf (fold_rev Thm.cabs cvs rhs)
    fun apply cv th =
      Thm.combination th (Thm.reflexive cv)
      |> Conv.fconv_rule (Conv.arg_conv (Thm.beta_conversion false))
  in ([eq], Thm.implies_elim thm (fold apply cvs (Thm.assume eq))) end

val true_thm = @{lemma "~False" by simp}

val is_neg = (fn @{term Not} $ _ => true | _ => false)
fun is_neg' f = (fn @{term Not} $ t => f t | _ => false)
val is_conj = (fn @{term "op &"} $ _ $ _ => true | _ => false)
val is_disj = (fn @{term "op |"} $ _ $ _ => true | _ => false)

(** explosion of conjunctions and disjunctions **)

local
  val dest_conj_term = (fn @{term "op &"} $ t $ u => SOME (t, u) | _ => NONE)

  val negate_term = (fn @{term Not} $ t => t | t => @{term Not} $ t)
  fun dest_disj_term' f = (fn
      @{term Not} $ (@{term "op |"} $ t $ u) => SOME (f t, f u)
    | _ => NONE)
  val dest_disj_term = dest_disj_term' negate_term

  fun destc ct = list2 (Thm.dest_binop (Thm.dest_arg ct))
  val dest_conj1 = precompose destc @{thm conjunct1}
  val dest_conj2 = precompose destc @{thm conjunct2}
  fun dest_conj_rules t =
    dest_conj_term t |> Option.map (K (dest_conj1, dest_conj2))
    
  fun destd f ct = list2 (f (Thm.dest_binop (Thm.dest_arg (Thm.dest_arg ct))))
  val dn1 = apfst Thm.dest_arg and dn2 = apsnd Thm.dest_arg
  val dest_disj1 = precompose (destd I) @{lemma "~(P | Q) ==> ~P" by fast}
  and dest_disj2 = precompose (destd dn1) @{lemma "~(~P | Q) ==> P" by fast}
  and dest_disj3 = precompose (destd I) @{lemma "~(P | Q) ==> ~Q" by fast}
  and dest_disj4 = precompose (destd dn2) @{lemma "~(P | ~Q) ==> Q" by fast}

  val is_neg = (fn @{term Not} $ _ => true | _ => false)
  fun dest_disj_rules t =
    (case dest_disj_term' is_neg t of
      SOME (true, true) => SOME (dest_disj2, dest_disj4)
    | SOME (true, false) => SOME (dest_disj2, dest_disj3)
    | SOME (false, true) => SOME (dest_disj1, dest_disj4)
    | SOME (false, false) => SOME (dest_disj1, dest_disj3)
    | NONE => NONE)

  val is_dneg = is_neg' is_neg
  fun destn ct = [Thm.dest_arg (Thm.dest_arg (Thm.dest_arg ct))]
  val dneg_rule = precompose destn @{thm notnotD}
in
fun exists_lit is_conj P =
  let
    val dest = if is_conj then dest_conj_term else dest_disj_term
    fun exists t = P t orelse
      (case dest t of
        SOME (t1, t2) => exists t1 orelse exists t2
      | NONE => false)
  in exists end

fun explode_term is_conj keep_intermediate =
  let
    val dest = if is_conj then dest_conj_term else dest_disj_term
    val dest_rules = if is_conj then dest_conj_rules else dest_disj_rules
    fun explode1 rules t =
      (case dest t of
        SOME (t1, t2) =>
          let val (rule1, rule2) = the (dest_rules t)
          in
            explode1 (rule1 :: rules) t1 #>
            explode1 (rule2 :: rules) t2 #>
            keep_intermediate ? cons (t, rev rules)
          end
      | NONE => cons (t, rev rules))
    fun explode0 (@{term Not} $ (@{term Not} $ t)) = [(t, [dneg_rule])]
      | explode0 t = explode1 [] t []
  in explode0 end

fun extract_lit thm rules = fold compose rules thm

fun explode_thm is_conj full keep_intermediate stop_lits =
  let
    val dest_rules = if is_conj then dest_conj_rules else dest_disj_rules
    val tab = fold (Termtab.update o rpair ()) stop_lits Termtab.empty

    fun explode1 thm =
      if Termtab.defined tab (prop_of thm) then cons thm
      else
        (case dest_rules (prop_of thm) of
          SOME (rule1, rule2) => explode2 rule1 thm #> explode2 rule2 thm #>
            keep_intermediate ? cons thm
        | NONE => cons thm)
    and explode2 dest_rule thm =
      if full orelse exists_lit is_conj (Termtab.defined tab) (prop_of thm)
      then explode1 (compose dest_rule thm)
      else cons (compose dest_rule thm)
    fun explode0 thm =
      if not is_conj andalso is_dneg (prop_of thm) then [compose dneg_rule thm]
      else explode1 thm []
  in explode0 end
end

(** joining of literals to conjunctions or disjunctions **)

local
  fun precomp2 f g thm =
    (f (Thm.cprem_of thm 1), g (Thm.cprem_of thm 2), f, g, thm)
  fun comp2 (cv1, cv2, f, g, rule) thm1 thm2 =
    let val inst = [(cv1, f (Thm.cprop_of thm1)), (cv2, g (Thm.cprop_of thm2))]
    in Thm.instantiate ([], inst) rule |> discharge thm1 |> discharge thm2 end

  fun d1 ct = Thm.dest_arg ct and d2 ct = Thm.dest_arg (Thm.dest_arg ct)

  val conj_rule = precomp2 d1 d1 @{thm conjI}
  fun comp_conj ((_, thm1), (_, thm2)) = comp2 conj_rule thm1 thm2

  val disj1 = precomp2 d2 d2 @{lemma "~P ==> ~Q ==> ~(P | Q)" by fast}
  val disj2 = precomp2 d2 d1 @{lemma "~P ==> Q ==> ~(P | ~Q)" by fast}
  val disj3 = precomp2 d1 d2 @{lemma "P ==> ~Q ==> ~(~P | Q)" by fast}
  val disj4 = precomp2 d1 d1 @{lemma "P ==> Q ==> ~(~P | ~Q)" by fast}

  fun comp_disj ((false, thm1), (false, thm2)) = comp2 disj1 thm1 thm2
    | comp_disj ((false, thm1), (true, thm2)) = comp2 disj2 thm1 thm2
    | comp_disj ((true, thm1), (false, thm2)) = comp2 disj3 thm1 thm2
    | comp_disj ((true, thm1), (true, thm2)) = comp2 disj4 thm1 thm2

  fun dest_conj (@{term "op &"} $ t $ u) = ((false, t), (false, u))
    | dest_conj t = raise TERM ("dest_conj", [t])

  val neg = (fn @{term Not} $ t => (true, t) | t => (false, @{term Not} $ t))
  fun dest_disj (@{term Not} $ (@{term "op |"} $ t $ u)) = (neg t, neg u)
    | dest_disj t = raise TERM ("dest_disj", [t])

  val dnegE = precompose (single o d2 o d1) @{thm notnotD}
  val dnegI = precompose (single o d1) @{lemma "P ==> ~~P" by fast}
  fun as_dneg f t = f (@{term Not} $ (@{term Not} $ t))

  fun dni f = list2 o apsnd f o Thm.dest_binop o f o d1
  val negIffE = precompose (dni d1) @{lemma "~(P = (~Q)) ==> Q = P" by fast}
  val negIffI = precompose (dni I) @{lemma "P = Q ==> ~(Q = (~P))" by fast}
  val iff_const = @{term "op = :: bool => _"}
  fun as_negIff f (@{term "op = :: bool => _"} $ t $ u) =
        f (@{term Not} $ (iff_const $ u $ (@{term Not} $ t)))
    | as_negIff _ _ = NONE
in
fun make_lit_tab thms = fold (Termtab.update o ` prop_of) thms Termtab.empty

fun join is_conj tab t =
  let
    val comp = if is_conj then comp_conj else comp_disj
    val dest = if is_conj then dest_conj else dest_disj

    val lookup_lit = Termtab.lookup tab
    fun lookup_lit' t =
      (case t of
        @{term Not} $ (@{term Not} $ t) => (compose dnegI, lookup_lit t)
      | @{term Not} $ (@{term "op = :: bool => _"} $ t $ (@{term Not} $ u)) =>
          (compose negIffI, lookup_lit (iff_const $ u $ t))
      | @{term Not} $ ((eq as Const (@{const_name "op ="}, _)) $ t $ u) =>
          let fun rewr lit = lit COMP @{thm not_sym}
          in (rewr, lookup_lit (@{term Not} $ (eq $ u $ t))) end
      | _ =>
          (case as_dneg lookup_lit t of
            NONE => (compose negIffE, as_negIff lookup_lit t)
          | x => (compose dnegE, x)))
    fun join1 (s, t) =
      (case lookup_lit t of
        SOME lit => (s, lit)
      | NONE => 
          (case lookup_lit' t of
            (rewrite, SOME lit) => (s, rewrite lit)
          | (_, NONE) => (s, comp (pairself join1 (dest t)))))
  in snd (join1 (if is_conj then (false, t) else (true, t))) end
end

(** proving equality of conjunctions or disjunctions **)

fun iff_intro thm1 thm2 = thm2 COMP (thm1 COMP @{thm iffI})

local
  val cp1 = @{lemma "(~P) = (~Q) ==> P = Q" by simp}
  val cp2 = @{lemma "(~P) = Q ==> P = (~Q)" by fastsimp}
  val cp3 = @{lemma "P = (~Q) ==> (~P) = Q" by simp}
  val neg = Thm.capply @{cterm Not}
in
fun contrapos1 prove (ct, cu) = prove (neg ct, neg cu) COMP cp1
fun contrapos2 prove (ct, cu) = prove (neg ct, Thm.dest_arg cu) COMP cp2
fun contrapos3 prove (ct, cu) = prove (Thm.dest_arg ct, neg cu) COMP cp3
end

local
  fun prove_eq l r (cl, cr) =
    let
      fun explode is_conj = explode_thm is_conj true (l <> r) []
      fun make_tab is_conj thm = make_lit_tab (true_thm :: explode is_conj thm)
      fun prove is_conj ct tab = join is_conj tab (Thm.term_of ct)

      val thm1 = under_assumption (prove r cr o make_tab l) cl
      val thm2 = under_assumption (prove l cl o make_tab r) cr
    in iff_intro thm1 thm2 end

  datatype conj_disj = CONJ | DISJ | NCON | NDIS
  fun kind_of t =
    if is_conj t then SOME CONJ
    else if is_disj t then SOME DISJ
    else if is_neg' is_conj t then SOME NCON
    else if is_neg' is_disj t then SOME NDIS
    else NONE
in
fun prove_conj_disj_eq ct =
  let val cp = Thm.dest_binop ct
  in
    (case pairself (kind_of o Thm.term_of) cp of
      (SOME CONJ, SOME CONJ) => prove_eq true true cp
    | (SOME CONJ, SOME NDIS) => prove_eq true false cp
    | (SOME CONJ, NONE) => prove_eq true true cp
    | (SOME DISJ, SOME DISJ) => contrapos1 (prove_eq false false) cp
    | (SOME DISJ, SOME NCON) => contrapos2 (prove_eq false true) cp
    | (SOME DISJ, NONE) => contrapos1 (prove_eq false false) cp
    | (SOME NCON, SOME NCON) => contrapos1 (prove_eq true true) cp
    | (SOME NCON, SOME DISJ) => contrapos3 (prove_eq true false) cp
    | (SOME NCON, NONE) => contrapos3 (prove_eq true false) cp
    | (SOME NDIS, SOME NDIS) => prove_eq false false cp
    | (SOME NDIS, SOME CONJ) => prove_eq false true cp
    | (SOME NDIS, NONE) => prove_eq false true cp
    | _ => raise CTERM ("prove_conj_disj_eq", [ct]))
  end
end

(** unfolding of distinct **)

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

(** proving abstractions **)

fun fold_map_op f ct =
  let val (cf, cu) = Thm.dest_comb ct
  in f cu #>> Thm.capply cf end

fun fold_map_binop f1 f2 ct =
  let val ((cf, cu1), cu2) = apfst Thm.dest_comb (Thm.dest_comb ct)
  in f1 cu1 ##>> f2 cu2 #>> uncurry (Thm.mk_binop cf) end

fun abstraction_context ctxt = (ctxt, certify_var, 1, false, Ctermtab.empty)
fun abstraction_context' ctxt = (ctxt, certify_free, 1, true, Ctermtab.empty)

fun fresh_abstraction ct (cx as (ctxt, mk_var, idx, gen, tab)) =
  (case Ctermtab.lookup tab ct of
    SOME cv => (cv, cx)
  | NONE =>
      let val cv = mk_var ctxt idx (#T (Thm.rep_cterm ct))
      in (cv, (ctxt, mk_var, idx + 1, gen, Ctermtab.update (ct, cv) tab)) end)

fun prove_abstraction tac ct (ctxt, _, _, gen, tab) =
  let
    val insts = map swap (Ctermtab.dest tab)
    val thm = Goal.prove_internal [] ct (fn _ => tac 1)
  in
    if gen
    then fold SMT_Normalize.instantiate_free insts thm
    else Thm.instantiate ([], insts) thm
  end


(* core proof rules *)

datatype assms = Some of thm list | Many of thm Net.net

val true_false = @{lemma "True == ~ False" by simp}

local
  val TT_eq = @{lemma "(P = (~False)) == P" by simp}
  val remove_trigger = @{lemma "trigger t p == p"
    by (rule eq_reflection, rule trigger_def)}
  val remove_iff = @{lemma "p iff q == p = q"
    by (rule eq_reflection, rule iff_def)}

  fun with_context simpset ctxt = Simplifier.context ctxt simpset

  val prep_ss = with_context (Simplifier.empty_ss addsimps
    [@{thm Let_def}, remove_trigger, remove_iff, true_false, TT_eq])

  val TT_eq_conv = Conv.rewr_conv TT_eq
  val norm_conv = More_Conv.bottom_conv (K (Conv.try_conv TT_eq_conv))

  val threshold = 10
  
  val lookup = (fn Some thms => first_of thms | Many net => net_instance net)
  fun lookup_assm ctxt assms ct =
    (case lookup assms ct of
      SOME thm => thm
    | _ => z3_exn ("not asserted: " ^
        quote (Syntax.string_of_term ctxt (Thm.term_of ct))))
in
fun prepare_assms ctxt assms =
  let
    val rewrite = Conv.fconv_rule (Simplifier.rewrite (prep_ss ctxt))
    val thms = map rewrite assms
  in if length assms < threshold then Some thms else Many (thm_net_of thms) end

fun asserted _ NONE ct = Thm (Thm.assume (T.mk_prop ct))
  | asserted ctxt (SOME assms) ct =
      Thm (with_conv (norm_conv ctxt) (lookup_assm ctxt assms) (T.mk_prop ct))
end


(** P ==> P = Q ==> Q   or   P ==> P --> Q ==> Q **)
local
  val meta_iffD1 = @{lemma "P == Q ==> P ==> (Q::bool)" by simp}
  val meta_iffD1_c = precompose (list2 o Thm.dest_binop) meta_iffD1

  val iffD1_c = precompose (list2 o Thm.dest_binop o Thm.dest_arg) @{thm iffD1}
  val mp_c = precompose (list2 o Thm.dest_binop o Thm.dest_arg) @{thm mp}
in
fun mp (MetaEq thm) p = Thm (Thm.implies_elim (compose meta_iffD1_c thm) p)
  | mp p_q p = 
      let
        val pq = thm_of p_q
        val thm = compose iffD1_c pq handle THM _ => compose mp_c pq
      in Thm (Thm.implies_elim thm p) end
end


(** and_elim:     P1 & ... & Pn ==> Pi **)
(** not_or_elim:  ~(P1 | ... | Pn) ==> ~Pi **)
local
  fun get_lit conj t (l, thm) =
    let val is_sublit_of = exists_lit conj (fn u => u aconv t)
    in if is_sublit_of (prop_of thm) then SOME (l, thm) else NONE end

  fun derive conj t lits idx ptab =
    let
      val (l, lit) = the (Termtab.get_first NONE (get_lit conj t) lits)
      val ls = explode_thm conj false false [t] lit
      val lits' = fold (Termtab.update o ` prop_of) ls (Termtab.delete l lits)
      fun upd (Sequent {hyps, vars, thm}) =
            Sequent {hyps=hyps, vars=vars, thm = Literals (thm_of thm, lits')}
        | upd p = p
    in (the (Termtab.lookup lits' t), Inttab.map_entry idx upd ptab) end

  val mk_tab = make_lit_tab o single
  val literals_of = (fn Literals (_, lits) => lits | p => mk_tab (thm_of p))
  fun lit_elim conj (p, idx) ct ptab =
    let val lits = literals_of p
    in
      (case Termtab.lookup lits (Thm.term_of ct) of
        SOME lit => (Thm lit, ptab)
      | NONE => apfst Thm (derive conj (Thm.term_of ct) lits idx ptab))
    end
in
val and_elim = lit_elim true
val not_or_elim = lit_elim false
end


(** P1 ... Pn |- False ==> |- ~P1 | ... | ~Pn **)
local
  fun step lit thm =
    Thm.implies_elim (Thm.implies_intr (Thm.cprop_of lit) thm) lit
  val explode_disj = explode_thm false false false
  fun intro hyps thm th = fold step (explode_disj hyps th) thm

  fun dest_ccontr ct = [Thm.dest_arg (Thm.dest_arg (Thm.dest_arg1 ct))]
  val ccontr = precompose dest_ccontr @{thm ccontr}
in
fun lemma thm ct =
  let
    val cu = Thm.capply @{cterm Not} ct
    val hyps = map_filter (try HOLogic.dest_Trueprop) (#hyps (Thm.rep_thm thm))
  in Thm (compose ccontr (under_assumption (intro hyps thm) cu)) end
end


(** \/{P1, ..., Pn, Q1, ..., Qn} & ~P1 & ... & ~Pn ==> \/{Q1, ..., Qn} **)
local
  val explode_disj = explode_thm false true false and join_disj = join false
  fun unit thm thms th =
    let val t = @{term Not} $ prop_of thm and ts = map prop_of thms
    in join_disj (make_lit_tab (thms @ explode_disj ts th)) t end

  fun dest_arg2 ct = Thm.dest_arg (Thm.dest_arg ct)
  fun dest ct = list2 (pairself dest_arg2 (Thm.dest_binop ct))
  val contrapos = precompose dest @{lemma "(~P ==> ~Q) ==> Q ==> P" by fast}
in
fun unit_resolution thm thms ct =
  under_assumption (unit thm thms) (Thm.capply @{cterm Not} ct)
  |> Thm o discharge thm o compose contrapos
end


local
  val iff1 = @{lemma "P ==> P == (~ False)" by simp}
  val iff2 = @{lemma "~P ==> P == False" by simp}
in
fun iff_true thm = MetaEq (thm COMP iff1)
fun iff_false thm = MetaEq (thm COMP iff2)
end


(** distributivity of | over & **)
val distributivity = Thm o by_tac (Classical.fast_tac HOL_cs)


(** Tseitin-like axioms **)
local
  val disjI1 = @{lemma "(P ==> Q) ==> ~P | Q" by fast}
  val disjI2 = @{lemma "(~P ==> Q) ==> P | Q" by fast}
  val disjI3 = @{lemma "(~Q ==> P) ==> P | Q" by fast}
  val disjI4 = @{lemma "(Q ==> P) ==> P | ~Q" by fast}

  fun prove' conj1 conj2 ct2 thm =
    let val tab =
      make_lit_tab (true_thm :: explode_thm conj1 true (conj1 <> conj2) [] thm)
    in join conj2 tab (Thm.term_of ct2) end

  fun prove rule (ct1, conj1) (ct2, conj2) =
    under_assumption (prove' conj1 conj2 ct2) ct1 COMP rule

  fun prove_def_axiom ct =
    let val (ct1, ct2) = Thm.dest_binop ct
    in
      (case Thm.term_of ct1 of
        @{term Not} $ (@{term "op &"} $ _ $ _) =>
          prove disjI1 (Thm.dest_arg ct1, true) (ct2, true)
      | @{term "op &"} $ _ $ _ =>
          prove disjI3 (Thm.capply @{cterm Not} ct2, false) (ct1, true)
      | @{term Not} $ (@{term "op |"} $ _ $ _) =>
          prove disjI3 (Thm.capply @{cterm Not} ct2, false) (ct1, false)
      | @{term "op |"} $ _ $ _ =>
          prove disjI2 (Thm.capply @{cterm Not} ct1, false) (ct2, true)
      | Const (@{const_name distinct}, _) $ _ =>
          let
            fun dis_conv cv = Conv.arg_conv (Conv.arg1_conv cv)
            fun prv cu =
              let val (cu1, cu2) = Thm.dest_binop (Thm.dest_arg cu)
              in prove disjI4 (Thm.dest_arg cu2, true) (cu1, true) end
          in with_conv (dis_conv unfold_distinct_conv) prv (T.mk_prop ct) end
      | @{term Not} $ (Const (@{const_name distinct}, _) $ _) =>
          let
            fun dis_conv cv = Conv.arg_conv (Conv.arg1_conv (Conv.arg_conv cv))
            fun prv cu =
              let val (cu1, cu2) = Thm.dest_binop (Thm.dest_arg cu)
              in prove disjI1 (Thm.dest_arg cu1, true) (cu2, true) end
          in with_conv (dis_conv unfold_distinct_conv) prv (T.mk_prop ct) end
      | _ => raise CTERM ("prove_def_axiom", [ct]))
    end

  val ifI = @{lemma "(P ==> Q1) ==> (~P ==> Q2) ==> if P then Q1 else Q2"
    by simp}
  val ifE = @{lemma
    "(if P then Q1 else Q2) ==> (P --> Q1 ==> ~P --> Q2 ==> R) ==> R" by simp}
  val claset = HOL_cs addIs [ifI] addEs [ifE]
in
fun def_axiom ctxt ct =
  Thm (try_apply ctxt "def_axiom" [
    ("conj/disj", prove_def_axiom),
    ("fast", by_tac (Classical.fast_tac claset)),
    ("simp+fast", by_tac (Simplifier.simp_tac HOL_ss THEN_ALL_NEW
      Classical.fast_tac claset))] ct)
end


(** local definitions **)
local
  val intro_rules = [
    @{lemma "n == P ==> (~n | P) & (n | ~P)" by simp},
    @{lemma "n == (if P then s else t) ==> (~P | n = s) & (P | n = t)"
      by simp},
    @{lemma "n == P ==> n = P" by (rule meta_eq_to_obj_eq)} ]

  val apply_rules = [
    @{lemma "(~n | P) & (n | ~P) ==> P == n" by (atomize(full)) fast},
    @{lemma "(~P | n = s) & (P | n = t) ==> (if P then s else t) == n"
      by (atomize(full)) fastsimp} ]

  val inst_rule = match_instantiate' Thm.dest_arg

  fun apply_rule ct =
    (case get_first (try (inst_rule (T.mk_prop ct))) intro_rules of
      SOME thm => thm
    | NONE => raise CTERM ("intro_def", [ct]))
in
fun intro_def ct = apsnd Thm (make_hyp_def (apply_rule ct))

fun apply_def thm =
  get_first (try (fn rule => MetaEq (thm COMP rule))) apply_rules
  |> the_default (Thm thm)
end


local
  val quant_rules1 = ([
    @{lemma "(!!x. P x == Q) ==> ALL x. P x == Q" by simp},
    @{lemma "(!!x. P x == Q) ==> EX x. P x == Q" by simp}], [
    @{lemma "(!!x. P x == Q x) ==> ALL x. P x == ALL x. Q x" by simp},
    @{lemma "(!!x. P x == Q x) ==> EX x. P x == EX x. Q x" by simp}])

  val quant_rules2 = ([
    @{lemma "(!!x. ~P x == Q) ==> ~(ALL x. P x) == Q" by simp},
    @{lemma "(!!x. ~P x == Q) ==> ~(EX x. P x) == Q" by simp}], [
    @{lemma "(!!x. ~P x == Q x) ==> ~(ALL x. P x) == EX x. Q x" by simp},
    @{lemma "(!!x. ~P x == Q x) ==> ~(EX x. P x) == ALL x. Q x" by simp}])

  fun nnf_quant_tac thm (qs as (qs1, qs2)) i st = (
    Tactic.rtac thm ORELSE'
    (Tactic.match_tac qs1 THEN' nnf_quant_tac thm qs) ORELSE'
    (Tactic.match_tac qs2 THEN' nnf_quant_tac thm qs)) i st

  fun nnf_quant ctxt qs (p, (vars, _)) ct =
    as_meta_eq ct
    |> by_tac' (nnf_quant_tac (varify ctxt vars (meta_eq_of p)) qs)

  val nnf_rules = thm_net_of [@{thm not_not}]

  fun abstract ct =
    (case Thm.term_of ct of
      @{term False} => pair
    | @{term Not} $ _ => fold_map_op abstract
    | @{term "op &"} $ _ $ _ => fold_map_binop abstract abstract
    | @{term "op |"} $ _ $ _ => fold_map_binop abstract abstract
    | @{term "op -->"} $ _ $ _ => fold_map_binop abstract abstract
    | @{term "op = :: bool => _"} $ _ $ _ => fold_map_binop abstract abstract
    | _ => fresh_abstraction) ct

  fun abstracted ctxt ct =
    abstraction_context' ctxt
    |> abstract (Thm.dest_arg ct)
    |>> T.mk_prop
    |-> prove_abstraction (Classical.best_tac HOL_cs)

  fun prove_nnf ctxt =
    try_apply ctxt "nnf" [
      ("conj/disj", prove_conj_disj_eq o Thm.dest_arg),
      ("rule", the o net_instance nnf_rules),
      ("abstract", abstracted ctxt),
      ("tactic", by_tac' (Classical.best_tac HOL_cs))]
in
fun nnf ctxt ps ct =
  (case Thm.term_of ct of
    _ $ (l as Const _ $ Abs _) $ (r as Const _ $ Abs _) =>
      if l aconv r then MetaEq (Thm.reflexive (Thm.dest_arg ct))
      else MetaEq (nnf_quant ctxt quant_rules1 (hd ps) ct)
  | _ $ (@{term Not} $ (Const _ $ Abs _)) $ (Const _ $ Abs _) =>
      MetaEq (nnf_quant ctxt quant_rules2 (hd ps) ct)
  | _ =>
      let
        val eqs = map (Thm.symmetric o meta_eq_of o fst) ps
        val nnf_rewr_conv = Conv.arg_conv (Conv.arg_conv
          (More_Conv.top_sweep_conv (K (More_Conv.rewrs_conv eqs)) ctxt))
      in Thm (with_conv nnf_rewr_conv (prove_nnf ctxt) (T.mk_prop ct)) end)
end


(* equality proof rules *)

(** t = t **)
fun refl ct = MetaEq (Thm.reflexive (Thm.dest_arg ct))


(** s = t ==> t = s **)
local
  val symm_rule = @{lemma "s = t ==> t == s" by simp}
in
fun symm (MetaEq thm) = MetaEq (Thm.symmetric thm)
  | symm p = MetaEq (thm_of p COMP symm_rule)
end


(** s = t ==> t = u ==> s = u **)
local
  val trans_rule = @{lemma "s = t ==> t = u ==> s == u" by simp}
in
fun trans (MetaEq thm) q = MetaEq (Thm.transitive thm (meta_eq_of q))
  | trans p (MetaEq thm) = MetaEq (Thm.transitive (meta_eq_of p) thm)
  | trans p q = MetaEq (thm_of q COMP (thm_of p COMP trans_rule))
end


(** t1 = s1 & ... & tn = sn ==> f t1 ... tn = f s1 .. sn
    (reflexive antecendents are droppped) **)
local
  exception MONO

  fun prove_refl (ct, _) = Thm.reflexive ct
  fun prove_comb f g cp =
    let val ((ct1, ct2), (cu1, cu2)) = pairself Thm.dest_comb cp
    in Thm.combination (f (ct1, cu1)) (g (ct2, cu2)) end
  fun prove_arg f = prove_comb prove_refl f

  fun prove f cp = prove_comb (prove f) f cp handle CTERM _ => prove_refl cp

  fun prove_nary is_comb f =
    let
      fun prove (cp as (ct, _)) = f cp handle MONO =>
        if is_comb (Thm.term_of ct)
        then prove_comb (prove_arg prove) prove cp
        else prove_refl cp
    in prove end

  fun prove_list f n cp =
    if n = 0 then prove_refl cp
    else prove_comb (prove_arg f) (prove_list f (n-1)) cp

  fun with_length f (cp as (cl, _)) =
    f (length (HOLogic.dest_list (Thm.term_of cl))) cp

  fun prove_distinct f = prove_arg (with_length (prove_list f))

  fun prove_eq exn lookup cp =
    (case lookup (Logic.mk_equals (pairself Thm.term_of cp)) of
      SOME eq => eq
    | NONE => if exn then raise MONO else prove_refl cp)
  val prove_eq_exn = prove_eq true and prove_eq_safe = prove_eq false

  fun mono f (cp as (cl, _)) =
    (case Term.head_of (Thm.term_of cl) of
      @{term "op &"} => prove_nary is_conj (prove_eq_exn f)
    | @{term "op |"} => prove_nary is_disj (prove_eq_exn f)
    | Const (@{const_name distinct}, _) => prove_distinct (prove_eq_safe f)
    | _ => prove (prove_eq_safe f)) cp
in
fun monotonicity eqs ct =
  let
    val tab = map (` Thm.prop_of o meta_eq_of) eqs
    val lookup = AList.lookup (op aconv) tab
    val cp = Thm.dest_binop ct
  in MetaEq (prove_eq_exn lookup cp handle MONO => mono lookup cp) end
end


(** f a b = f b a **)
local
  val rule = @{lemma "a = b == b = a" by (atomize(full)) (rule eq_commute)}
in
fun commutativity ct = MetaEq (match_instantiate (as_meta_eq ct) rule)
end


(* quantifier proof rules *)

(** P ?x = Q ?x ==> (ALL x. P x) = (ALL x. Q x)
    P ?x = Q ?x ==> (EX x. P x) = (EX x. Q x)   **)
local
  val rules = [
    @{lemma "(!!x. P x == Q x) ==> (EX x. P x) == (EX x. Q x)" by simp},
    @{lemma "(!!x. P x == Q x) ==> (ALL x. P x) == (ALL x. Q x)" by simp}]
in
fun quant_intro ctxt (p, (vars, _)) ct =
  let
    val rules' = varify ctxt vars (meta_eq_of p) :: rules
    val cu = as_meta_eq ct
  in MetaEq (by_tac' (REPEAT_ALL_NEW (Tactic.match_tac rules')) cu) end
end


(** |- ((ALL x. P x) | Q) = (ALL x. P x | Q) **)
val pull_quant =
  Thm o by_tac (Tactic.rtac @{thm refl} ORELSE' Classical.best_tac HOL_cs)


(** |- (ALL x. P x & Q x) = ((ALL x. P x) & (ALL x. Q x)) **)
val push_quant =
  Thm o by_tac (Tactic.rtac @{thm refl} ORELSE' Classical.best_tac HOL_cs)


(**
  |- (ALL x1 ... xn y1 ... yn. P x1 ... xn) = (ALL x1 ... xn. P x1 ... xn)
**)
local
  val elim_all = @{lemma "ALL x. P == P" by simp}
  val elim_ex = @{lemma "EX x. P == P" by simp}

  val rule = (fn @{const_name All} => elim_all | _ => elim_ex)

  fun collect xs tp =
    if (op aconv) tp then rev xs
    else
      (case tp of
        (Const (q, _) $ Abs (_, _, l), r' as Const _ $ Abs (_, _, r)) =>
          if l aconv r then rev xs
          else if Term.loose_bvar1 (l, 0) then collect (NONE :: xs) (l, r)
          else collect (SOME (rule q) :: xs) (Term.incr_bv (~1, 0, l), r')
      | (Const (q, _) $ Abs (_, _, l), r) =>
          collect (SOME (rule q) :: xs) (Term.incr_bv (~1, 0, l), r)
      | (l, r) => raise TERM ("elim_unused", [l, r]))

  fun elim _ [] ct = Conv.all_conv ct
    | elim ctxt (x::xs) ct =
        (case x of
          SOME rule => Conv.rewr_conv rule then_conv elim ctxt xs
        | _ => Conv.arg_conv (Conv.abs_conv (fn (_,cx) => elim cx xs) ctxt)) ct
in
fun elim_unused_vars ctxt ct =
  let val (lhs, rhs) = Thm.dest_binop ct
  in MetaEq (elim ctxt (collect [] (Thm.term_of lhs, Thm.term_of rhs)) lhs) end
end


(** 
  |- (ALL x1 ... xn. ~(x1 = t1 & ... xn = tn) | P x1 ... xn) = P t1 ... tn
**)
val dest_eq_res = Thm o by_tac (Simplifier.simp_tac HOL_ss)


(** |- ~(ALL x1...xn. P x1...xn) | P a1...an **)
local
  val rule = @{lemma "~ P x | Q ==> ~(ALL x. P x) | Q" by fast}
in
val quant_inst = Thm o by_tac (
  REPEAT_ALL_NEW (Tactic.match_tac [rule])
  THEN' Tactic.rtac @{thm excluded_middle})
end


(** c = SOME x. P x |- (EX x. P x) = P c
    c = SOME x. ~ P x |- ~(ALL x. P x) = ~ P c **)
local
  val elim_ex = @{lemma "EX x. P == P" by simp}
  val elim_all = @{lemma "~ (ALL x. P) == ~P" by simp}
  val sk_ex = @{lemma "c == SOME x. P x ==> EX x. P x == P c"
    by simp (intro eq_reflection some_eq_ex[symmetric])}
  val sk_all = @{lemma "c == SOME x. ~ P x ==> ~(ALL x. P x) == ~ P c"
    by (simp only: not_all) (intro eq_reflection some_eq_ex[symmetric])}
  val sk_ex_rule = ((sk_ex, I), elim_ex)
  and sk_all_rule = ((sk_all, Thm.dest_arg), elim_all)

  fun dest f sk_rule = 
    Thm.dest_comb (f (Thm.dest_arg (Thm.dest_arg (Thm.cprop_of sk_rule))))
  fun type_of f sk_rule = Thm.ctyp_of_term (snd (dest f sk_rule))
  fun inst_sk (sk_rule, f) p c =
    Thm.instantiate ([(type_of f sk_rule, Thm.ctyp_of_term c)], []) sk_rule
    |> (fn sk' => Thm.instantiate ([], (list2 (dest f sk') ~~ [p, c])) sk')
    |> Conv.fconv_rule (Thm.beta_conversion true)

  fun kind (Const (q as @{const_name Ex}, _) $ _) = (sk_ex_rule, q, I, I)
    | kind (@{term Not} $ (Const (q as @{const_name All}, _) $ _)) =
        (sk_all_rule, q, Thm.dest_arg, Thm.capply @{cterm Not})
    | kind _ = z3_exn "skolemize: no quantifier"

  fun bodies_of ctxt ct =
    let
      val (rule, q, dest, make) = kind (Thm.term_of ct)

      fun inst_abs idx T cbs ct =
        let
          val cv = certify_var ctxt idx T
          val cu = Drule.beta_conv (Thm.dest_arg ct) cv
        in dest_body (idx + 1) ((cv, Thm.dest_arg ct) :: cbs) cu end
      and dest_body idx cbs ct =
        (case Thm.term_of ct of
          Const (qname, _) $ Abs (_, T, _) =>
            if q = qname then inst_abs idx T cbs ct else (make ct, rev cbs)
        | _ => (make ct, rev cbs))
    in (rule, dest_body (#maxidx (Thm.rep_cterm ct) + 1) [] (dest ct)) end

  fun transitive f thm = Thm.transitive thm (f (Thm.rhs_of thm))

  fun sk_step (rule, elim) (cv, mct, cb) (is, thm) =
    (case mct of
      SOME ct =>
        make_hyp_def (inst_sk rule (Thm.instantiate_cterm ([], is) cb) ct)
        |> apsnd (pair ((cv, ct) :: is) o Thm.transitive thm)
    | NONE => ([], (is, transitive (Conv.rewr_conv elim) thm)))
in
fun skolemize ctxt ct =
  let
    val (lhs, rhs) = Thm.dest_binop ct
    val (rule, (cu, cbs)) = bodies_of ctxt lhs
    val ctab = snd (Thm.first_order_match (cu, rhs))
    fun lookup_var (cv, cb) = (cv, AList.lookup (op aconvc) ctab cv, cb)
  in
    ([], Thm.reflexive lhs)
    |> fold_map (sk_step rule) (map lookup_var cbs)
    |> apfst (rev o flat) o apsnd (MetaEq o snd)
  end
end


(* theory proof rules *)

(** prove linear arithmetic problems via generalization **)
local
  val is_numeral = can HOLogic.dest_number
  fun is_number (Const (@{const_name uminus}, _) $ t) = is_numeral t
    | is_number t = is_numeral t

  local
    val int_distrib = @{lemma "n * (x + y) == n * x + n * (y::int)"
      by (simp add: int_distrib)}
    val real_distrib = @{lemma "n * (x + y) == n * x + n * (y::real)"
      by (simp add: mult.add_right)}
    val int_assoc = @{lemma "n * (m * x) == (n * m) * (x::int)" by linarith}
    val real_assoc = @{lemma "n * (m * x) == (n * m) * (x::real)" by linarith}

    val number_of_cong = @{lemma 
      "number_of x * number_of y == (number_of (x * y) :: int)"
      "number_of x * number_of y == (number_of (x * y) :: real)"
      by simp_all}
    val reduce_ss = HOL_ss addsimps @{thms mult_bin_simps}
      addsimps @{thms add_bin_simps} addsimps @{thms succ_bin_simps}
      addsimps @{thms minus_bin_simps} addsimps @{thms pred_bin_simps}
      addsimps number_of_cong
    val reduce_conv = Simplifier.rewrite reduce_ss

    fun apply_conv distrib assoc u ct =
     ((case u of
        Const (@{const_name times}, _) $ n $ _ =>
          if is_number n
          then Conv.rewr_conv assoc then_conv Conv.arg1_conv reduce_conv 
          else Conv.rewr_conv distrib
      | _ => Conv.rewr_conv distrib)
      then_conv Conv.binop_conv (Conv.try_conv distrib_conv)) ct

    and distrib_conv ct = 
      (case Thm.term_of ct of
        @{term "op * :: int => _"} $ n $ u =>
          if is_number n then apply_conv int_distrib int_assoc u
          else Conv.no_conv
      | @{term "op * :: real => _"} $ n $ u =>
          if is_number n then apply_conv real_distrib real_assoc u
          else Conv.no_conv
      | _ => Conv.no_conv) ct
  in
  val all_distrib_conv = More_Conv.top_sweep_conv (K distrib_conv)
  end

  local
    fun fresh ct = fresh_abstraction ct

    fun mult f1 f2 ct t u =
      if is_number t 
      then if is_number u then pair ct else fold_map_binop f1 f2 ct
      else fresh ct

    fun poly ct =
      (case Thm.term_of ct of
        Const (@{const_name plus}, _) $ _ $ _ => fold_map_binop poly poly ct
      | Const (@{const_name minus}, _) $ _ $ _ => fold_map_binop poly poly ct
      | Const (@{const_name times}, _) $ t $ u => mult pair fresh ct t u
      | Const (@{const_name div}, _) $ t $ u => mult fresh pair ct t u
      | Const (@{const_name mod}, _) $ t $ u => mult fresh pair ct t u
      | t => if is_number t then pair ct else fresh ct)

    val ineq_ops = [@{term "op = :: int => _"}, @{term "op < :: int => _"},
      @{term "op <= :: int => _"}, @{term "op = :: real => _"},
      @{term "op < :: real => _"}, @{term "op <= :: real => _"}]
    fun ineq ct =
      (case Thm.term_of ct of
        t $ _ $ _ =>
          if member (op =) ineq_ops t then fold_map_binop poly poly ct
          else raise CTERM ("arith_lemma", [ct])
      | @{term Not} $ (t $ _ $ _) =>
          if member (op =) ineq_ops t
          then fold_map_op (fold_map_binop poly poly) ct
          else raise CTERM ("arith_lemma", [ct])
      | _ => raise CTERM ("arith_lemma", [ct]))

    fun conj ct =
      (case Thm.term_of ct of
        @{term "op &"} $ _ $ _ => fold_map_binop conj conj ct
      | @{term "~False"} => pair ct
      | _ => ineq ct)

    fun disj ct =
      (case Thm.term_of ct of
        @{term "op |"} $ _ $ _ => fold_map_binop disj disj ct
      | @{term False} => pair ct
      | _ => conj ct)
  in
  fun prove_arith ctxt thms ct =
    abstraction_context ctxt
    |> fold_map (fold_map_op ineq o Thm.cprop_of) thms
    ||>> fold_map_op disj ct
    |>> uncurry (fold_rev (Thm.mk_binop @{cterm "op ==>"}))
    |-> prove_abstraction (Arith_Data.arith_tac ctxt)
    |> fold (fn th1 => fn th2 => Thm.implies_elim th2 th1) thms
  end
in
fun arith_lemma ctxt thms ct =
  let val thms' = map (Conv.fconv_rule (all_distrib_conv ctxt)) thms
  in with_conv (all_distrib_conv ctxt) (prove_arith ctxt thms') ct end
end

(** theory simpset **)
local
  val antisym_le1 = mk_meta_eq @{thm order_class.antisym_conv}
  val antisym_le2 = mk_meta_eq @{thm linorder_class.antisym_conv2}
  val antisym_less1 = mk_meta_eq @{thm linorder_class.antisym_conv1}
  val antisym_less2 = mk_meta_eq @{thm linorder_class.antisym_conv3}

  fun eq_prop t thm = HOLogic.mk_Trueprop t aconv Thm.prop_of thm

  fun prove_antisym_le ss ((le as Const(_, T)) $ r $ s) =
    let
      val prems = Simplifier.prems_of_ss ss
      val less = Const (@{const_name less}, T)
    in
      (case find_first (eq_prop (le $ s $ r)) prems of
        NONE =>
          find_first (eq_prop (HOLogic.mk_not (less $ r $ s))) prems
          |> Option.map (fn thm => thm RS antisym_less1)
      | SOME thm => SOME (thm RS antisym_le1))
    end
    handle THM _ => NONE

  fun prove_antisym_less ss (_ $ ((less as Const(_,T)) $ r $ s)) =
    let
      val prems = prems_of_ss ss
      val le = Const (@{const_name less_eq}, T)
    in
      (case find_first (eq_prop (le $ r $ s)) prems of
        NONE =>
          find_first (eq_prop (HOLogic.mk_not (less $ s $ r))) prems
          |> Option.map (fn thm => thm RS antisym_less2)
    | SOME thm => SOME (thm RS antisym_le2))
  end
  handle THM _ => NONE
in
val z3_simpset = HOL_ss addsimps @{thms array_rules}
  addsimps @{thms ring_distribs} addsimps @{thms field_eq_simps}
  addsimps @{thms arith_special} addsimps @{thms less_bin_simps}
  addsimps @{thms le_bin_simps} addsimps @{thms eq_bin_simps}
  addsimps @{thms add_bin_simps} addsimps @{thms succ_bin_simps}
  addsimps @{thms minus_bin_simps} addsimps @{thms pred_bin_simps}
  addsimps @{thms mult_bin_simps} addsimps @{thms iszero_simps}
  addsimprocs [
    Simplifier.simproc @{theory} "fast_int_arith" [
      "(m::int) < n", "(m::int) <= n", "(m::int) = n"] (K Lin_Arith.simproc),
    Simplifier.simproc @{theory} "fast_real_arith" [
      "(m::real) < n", "(m::real) <= n", "(m::real) = n"]
      (K Lin_Arith.simproc),
    Simplifier.simproc @{theory} "antisym le" ["(x::'a::order) <= y"]
      (K prove_antisym_le),
    Simplifier.simproc @{theory} "antisym less" ["~ (x::'a::linorder) < y"]
      (K prove_antisym_less)]
end

(** theory lemmas: linear arithmetic, arrays **)
local
  val array_ss = HOL_ss addsimps @{thms array_rules}
  fun array_tac thms =
    Tactic.cut_facts_tac thms
    THEN' Simplifier.asm_full_simp_tac array_ss

  fun full_arith_tac ctxt thms =
    Tactic.cut_facts_tac thms
    THEN' Arith_Data.arith_tac ctxt

  fun simp_arith_tac ctxt thms =
    Tactic.cut_facts_tac thms
    THEN' Simplifier.asm_full_simp_tac z3_simpset
    THEN' Arith_Data.arith_tac ctxt
in
fun th_lemma ctxt thms ct =
  Thm (try_apply ctxt "th-lemma" [
    ("abstract arith", arith_lemma ctxt thms),
    ("array", by_tac' (array_tac thms)),
    ("full arith", by_tac' (full_arith_tac ctxt thms)),
    ("simp arith", by_tac' (simp_arith_tac ctxt thms))] (T.mk_prop ct))
end

(** rewriting: prove equalities:
      * ACI of conjunction/disjunction
      * contradiction, excluded middle
      * logical rewriting rules (for negation, implication, equivalence,
          distinct)
      * normal forms for polynoms (integer/real arithmetic)
      * quantifier elimination over linear arithmetic
      * ... ? **)
structure Z3_Rewrite_Rules =
struct
  val name = "z3_rewrite"
  val descr = "Z3 rewrite rules used in proof reconstruction"

  structure Data = Generic_Data
  (
    type T = thm Net.net
    val empty = Net.empty
    val extend = I
    val merge = Net.merge Thm.eq_thm_prop
  )
  val get = Data.get o Context.Proof

  val entry = ` Thm.prop_of o Simplifier.rewrite_rule [true_false]
  val eq = Thm.eq_thm_prop
  val ins = Net.insert_term eq o entry and del = Net.delete_term eq o entry
  fun insert thm net = ins thm net handle Net.INSERT => net
  fun delete thm net = del thm net handle Net.DELETE => net

  val add = Thm.declaration_attribute (Data.map o insert)
  val del = Thm.declaration_attribute (Data.map o delete)
  val setup = Attrib.setup (Binding.name name) (Attrib.add_del add del) descr
end

local
  val contra_rule = @{lemma "P ==> ~P ==> False" by (rule notE)}
  fun contra_left conj thm =
    let
      fun make_tab xs = fold Termtab.update xs Termtab.empty
      val tab = make_tab (explode_term conj true (prop_of thm))
      fun pnlits (t, nrs) =
        (case t of
          @{term Not} $ u => Termtab.lookup tab u |> Option.map (pair nrs)
        | _ => NONE)
    in
      (case Termtab.lookup tab @{term False} of
        SOME rs => extract_lit thm rs
      | NONE =>
          pairself (extract_lit thm) (the (Termtab.get_first NONE pnlits tab))
          |> (fn (nlit, plit) => nlit COMP (plit COMP contra_rule)))
    end
  val falseE_v = Thm.dest_arg (Thm.dest_arg (Thm.cprop_of @{thm FalseE}))
  fun contra_right ct = Thm.instantiate ([], [(falseE_v, ct)]) @{thm FalseE}
  fun contradiction conj ct =
    iff_intro (under_assumption (contra_left conj) ct) (contra_right ct)

  fun conj_disj ct =
    let val cp as (cl, cr) = Thm.dest_binop (Thm.dest_arg ct)
    in
      (case Thm.term_of cr of
        @{term False} => contradiction true cl
      | @{term "~False"} => contrapos2 (contradiction false o fst) cp
      | _ => prove_conj_disj_eq (Thm.dest_arg ct))
    end

  val distinct =
    let val try_unfold = Conv.try_conv unfold_distinct_conv
    in with_conv (Conv.arg_conv (Conv.binop_conv try_unfold)) conj_disj end

  val nnf_neg_rule = @{lemma "~~P == P" by fastsimp}
  val nnf_cd_rules = @{lemma "~(P | Q) == ~P & ~Q" "~(P & Q) == ~P | ~Q"
    by fastsimp+}

  fun nnf_conv ct = Conv.try_conv (
    (Conv.rewr_conv nnf_neg_rule then_conv nnf_conv) else_conv
    (More_Conv.rewrs_conv nnf_cd_rules then_conv Conv.binop_conv nnf_conv)) ct
  val iffI_rule = @{lemma "~P | Q ==> ~Q | P ==> P = Q" by fast}
  fun arith_tac ctxt = CSUBGOAL (fn (goal, i) =>
    let val prep_then = with_conv (Conv.arg_conv (Conv.binop_conv nnf_conv))
    in Tactic.rtac (prep_then (arith_lemma ctxt []) goal) i end)
  fun arith_eq_tac ctxt =
    Tactic.rtac iffI_rule THEN_ALL_NEW arith_tac ctxt
    ORELSE' arith_tac ctxt

  val simp_tac = CHANGED o Simplifier.simp_tac z3_simpset
    ORELSE' Classical.best_tac HOL_cs
in
fun rewrite ctxt thms ct =
  let val rules_net = Z3_Rewrite_Rules.get ctxt
  in
    Thm (try_apply ctxt "rewrite" [
      ("schematic rule", the o net_instance rules_net),
      ("conj/disj", conj_disj),
      ("distinct", distinct),
      ("arith", by_tac' (arith_eq_tac ctxt)),
      ("classical", by_tac' (Classical.best_tac HOL_cs)),
      ("simp", by_tac' simp_tac),
      ("full arith", by_tac' (Arith_Data.arith_tac ctxt))] (T.mk_prop ct))
  end
end


(* tracing and debugging *)

fun check idx r ct ((_, p), _) =
  let val thm = thm_of p |> tap (Thm.join_proofs o single)
  in
    if (Thm.cprop_of thm) aconvc (T.mk_prop ct) then ()
    else z3_exn ("proof step failed: " ^ quote (string_of_rule r) ^
      " (#" ^ string_of_int idx ^ ")")
  end

local
  fun trace_before ctxt idx (r, ps, ct) =
    Pretty.string_of (
      Pretty.big_list ("#" ^ string_of_int idx ^ ": " ^ string_of_rule r) [
        Pretty.big_list "assumptions:"
          (map (Display.pretty_thm ctxt o thm_of o fst) ps),
        Pretty.block [Pretty.str "goal: ",
          Syntax.pretty_term ctxt (Thm.term_of ct)]])

  fun trace_after ctxt ((_, p), _) = Pretty.string_of (Pretty.block
    [Pretty.str "result: ", Display.pretty_thm ctxt (thm_of p)])
in
fun trace_rule ctxt idx prove r ps ct ptab =
  let
    val _ = SMT_Solver.trace_msg ctxt (trace_before ctxt idx) (r, ps, ct)
    val result = prove r ps ct ptab
    val _ = SMT_Solver.trace_msg ctxt (trace_after ctxt) result
  in result end
end


(* overall reconstruction procedure *)

fun not_supported r =
  z3_exn ("proof rule not implemented: " ^ quote (string_of_rule r))

fun prove ctxt assms =
  let
    val prems = Option.map (prepare_assms ctxt) assms

    fun step r ps ct ptab =
      (case (r, ps) of
        (* core rules *)
        (TrueAxiom, _) => (([], Thm true_thm), ptab)
      | (Asserted, _) => (([], asserted ctxt prems ct), ptab)
      | (Goal, _) => (([], asserted ctxt prems ct), ptab)
      | (ModusPonens, [(p, _), (q, _)]) => (([], mp q (thm_of p)), ptab)
      | (ModusPonensOeq, [(p, _), (q, _)]) => (([], mp q (thm_of p)), ptab)
      | (AndElim, [(p, (_, i))]) => apfst (pair []) (and_elim (p, i) ct ptab)
      | (NotOrElim, [(p, (_, i))]) =>
          apfst (pair []) (not_or_elim (p, i) ct ptab)
      | (Hypothesis, _) => (([], Thm (Thm.assume (T.mk_prop ct))), ptab)
      | (Lemma, [(p, _)]) => (([], lemma (thm_of p) ct), ptab)
      | (UnitResolution, (p, _) :: ps) =>
          (([], unit_resolution (thm_of p) (map (thm_of o fst) ps) ct), ptab)
      | (IffTrue, [(p, _)]) => (([], iff_true (thm_of p)), ptab)
      | (IffFalse, [(p, _)]) => (([], iff_false (thm_of p)), ptab)
      | (Distributivity, _) => (([], distributivity ct), ptab)
      | (DefAxiom, _) => (([], def_axiom ctxt ct), ptab)
      | (IntroDef, _) => (intro_def ct, ptab)
      | (ApplyDef, [(p, _)]) => (([], apply_def (thm_of p)), ptab)
      | (IffOeq, [(p, _)]) => (([], p), ptab)
      | (NnfPos, _) => (([], nnf ctxt ps ct), ptab)
      | (NnfNeg, _) => (([], nnf ctxt ps ct), ptab)

        (* equality rules *)
      | (Reflexivity, _) => (([], refl ct), ptab)
      | (Symmetry, [(p, _)]) => (([], symm p), ptab)
      | (Transitivity, [(p, _), (q, _)]) => (([], trans p q), ptab)
      | (Monotonicity, _) => (([], monotonicity (map fst ps) ct), ptab)
      | (Commutativity, _) => (([], commutativity ct), ptab)

        (* quantifier rules *)
      | (QuantIntro, [p]) => (([], quant_intro ctxt p ct), ptab)
      | (PullQuant, _) => (([], pull_quant ct), ptab)
      | (PushQuant, _) => (([], push_quant ct), ptab)
      | (ElimUnusedVars, _) => (([], elim_unused_vars ctxt ct), ptab)
      | (DestEqRes, _) => (([], dest_eq_res ct), ptab)
      | (QuantInst, _) => (([], quant_inst ct), ptab)
      | (Skolemize, _) => (skolemize ctxt ct, ptab)

        (* theory rules *)
      | (ThLemma, _) => (([], th_lemma ctxt (map (thm_of o fst) ps) ct), ptab)
      | (Rewrite, _) => (([], rewrite ctxt [] ct), ptab)
      | (RewriteStar, ps) =>
          (([], rewrite ctxt (map (thm_of o fst) ps) ct), ptab)

      | (NnfStar, _) => not_supported r
      | (CnfStar, _) => not_supported r
      | (TransitivityStar, _) => not_supported r
      | (PullQuantStar, _) => not_supported r

      | _ => z3_exn ("Proof rule " ^ quote (string_of_rule r) ^
         " has an unexpected number of arguments."))

    fun eq_hyp (ct, cu) = Thm.dest_arg1 ct aconvc Thm.dest_arg1 cu

    fun conclude idx rule prop ((hypss, ps), ptab) =
      trace_rule ctxt idx step rule ps prop ptab
      |> Config.get ctxt SMT_Solver.trace ? tap (check idx rule prop)
      |>> apfst (distinct eq_hyp o fold append hypss)

    fun add_sequent idx vars (hyps, thm) ptab =
      let val s = Sequent {hyps=hyps, vars=vars, thm=thm}
      in ((hyps, (thm, vars)), Inttab.update (idx, s) ptab) end

    fun lookup idx ptab =
      (case Inttab.lookup ptab idx of
        SOME (Unproved {rule, subs, vars, prop}) =>
          fold_map lookup subs ptab
          |>> split_list
          |>> apsnd (map2 (fn idx => fn (p, vs) => (p, (vs, idx))) subs)
          |> conclude idx rule prop
          |-> add_sequent idx vars
      | SOME (Sequent {hyps, vars, thm}) => ((hyps, (thm, vars)), ptab)
      | NONE => z3_exn ("unknown proof id: " ^ quote (string_of_int idx)))

    fun result (hyps, (thm, _)) =
      fold SMT_Normalize.discharge_definition hyps (thm_of thm)

  in (fn ptab => fn idx => result (fst (lookup idx ptab))) end

val setup = Z3_Rewrite_Rules.setup

end
