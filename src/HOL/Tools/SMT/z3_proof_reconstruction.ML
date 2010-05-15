(*  Title:      HOL/Tools/SMT/z3_proof_reconstruction.ML
    Author:     Sascha Boehme, TU Muenchen

Proof reconstruction for proofs found by Z3.
*)

signature Z3_PROOF_RECONSTRUCTION =
sig
  val add_z3_rule: thm -> Context.generic -> Context.generic
  val trace_assms: bool Config.T
  val reconstruct: string list * SMT_Translate.recon -> Proof.context ->
    thm * Proof.context
  val setup: theory -> theory
end

structure Z3_Proof_Reconstruction: Z3_PROOF_RECONSTRUCTION =
struct

structure P = Z3_Proof_Parser
structure T = Z3_Proof_Tools
structure L = Z3_Proof_Literals

fun z3_exn msg = raise SMT_Solver.SMT ("Z3 proof reconstruction: " ^ msg)



(** net of schematic rules **)

val z3_ruleN = "z3_rule"

local
  val description = "declaration of Z3 proof rules"

  val eq = Thm.eq_thm

  structure Z3_Rules = Generic_Data
  (
    type T = thm Net.net
    val empty = Net.empty
    val extend = I
    val merge = Net.merge eq
  )

  val prep = `Thm.prop_of o Simplifier.rewrite_rule [L.rewrite_true]

  fun ins thm net = Net.insert_term eq (prep thm) net handle Net.INSERT => net
  fun del thm net = Net.delete_term eq (prep thm) net handle Net.DELETE => net

  val add = Thm.declaration_attribute (Z3_Rules.map o ins)
  val del = Thm.declaration_attribute (Z3_Rules.map o del)
in

val add_z3_rule = Z3_Rules.map o ins

fun by_schematic_rule ctxt ct =
  the (T.net_instance (Z3_Rules.get (Context.Proof ctxt)) ct)

val z3_rules_setup =
  Attrib.setup (Binding.name z3_ruleN) (Attrib.add_del add del) description #>
  PureThy.add_thms_dynamic (Binding.name z3_ruleN, Net.content o Z3_Rules.get)

end



(** proof tools **)

fun named ctxt name prover ct =
  let val _ = SMT_Solver.trace_msg ctxt I ("Z3: trying " ^ name ^ " ...")
  in prover ct end

fun NAMED ctxt name tac i st =
  let val _ = SMT_Solver.trace_msg ctxt I ("Z3: trying " ^ name ^ " ...")
  in tac i st end

fun pretty_goal ctxt thms t =
  [Pretty.block [Pretty.str "proposition: ", Syntax.pretty_term ctxt t]]
  |> not (null thms) ? cons (Pretty.big_list "assumptions:"
       (map (Display.pretty_thm ctxt) thms))

fun try_apply ctxt thms =
  let
    fun try_apply_err ct = Pretty.string_of (Pretty.chunks [
      Pretty.big_list ("Z3 found a proof," ^
        " but proof reconstruction failed at the following subgoal:")
        (pretty_goal ctxt thms (Thm.term_of ct)),
      Pretty.str ("Adding a rule to the lemma group " ^ quote z3_ruleN ^
        " might solve this problem.")])

    fun apply [] ct = error (try_apply_err ct)
      | apply (prover :: provers) ct =
          (case try prover ct of
            SOME thm => (SMT_Solver.trace_msg ctxt I "Z3: succeeded"; thm)
          | NONE => apply provers ct)

  in apply o cons (named ctxt "schematic rules" (by_schematic_rule ctxt)) end

local
  val rewr_if =
    @{lemma "(if P then Q1 else Q2) = ((P --> Q1) & (~P --> Q2))" by simp}
in
val simp_fast_tac =
  Simplifier.simp_tac (HOL_ss addsimps [rewr_if])
  THEN_ALL_NEW Classical.fast_tac HOL_cs
end



(** theorems and proofs **)

(* theorem incarnations *)

datatype theorem =
  Thm of thm | (* theorem without special features *)
  MetaEq of thm | (* meta equality "t == s" *)
  Literals of thm * L.littab
    (* "P1 & ... & Pn" and table of all literals P1, ..., Pn *)

fun thm_of (Thm thm) = thm
  | thm_of (MetaEq thm) = thm COMP @{thm meta_eq_to_obj_eq}
  | thm_of (Literals (thm, _)) = thm

fun meta_eq_of (MetaEq thm) = thm
  | meta_eq_of p = mk_meta_eq (thm_of p)

fun literals_of (Literals (_, lits)) = lits
  | literals_of p = L.make_littab [thm_of p]


(* proof representation *)

datatype proof = Unproved of P.proof_step | Proved of theorem



(** core proof rules **)

(* assumption *)

val (trace_assms, trace_assms_setup) =
  Attrib.config_bool "z3_trace_assms" (K false)

local
  val remove_trigger = @{lemma "trigger t p == p"
    by (rule eq_reflection, rule trigger_def)}

  val prep_rules = [@{thm Let_def}, remove_trigger, L.rewrite_true]

  fun rewrite_conv ctxt eqs = Simplifier.full_rewrite
    (Simplifier.context ctxt Simplifier.empty_ss addsimps eqs)

  fun rewrites ctxt eqs = map (Conv.fconv_rule (rewrite_conv ctxt eqs))

  fun trace ctxt thm =
    if Config.get ctxt trace_assms
    then tracing (Display.string_of_thm ctxt thm)
    else ()

  fun lookup_assm ctxt assms ct =
    (case T.net_instance assms ct of
      SOME thm => (trace ctxt thm; thm)
    | _ => z3_exn ("not asserted: " ^
        quote (Syntax.string_of_term ctxt (Thm.term_of ct))))
in
fun prepare_assms ctxt unfolds assms =
  let
    val unfolds' = rewrites ctxt [L.rewrite_true] unfolds
    val assms' = rewrites ctxt (union Thm.eq_thm unfolds' prep_rules) assms
  in (unfolds', T.thm_net_of assms') end

fun asserted ctxt (unfolds, assms) ct =
  let val revert_conv = rewrite_conv ctxt unfolds
  in Thm (T.with_conv revert_conv (lookup_assm ctxt assms) ct) end
end



(* P = Q ==> P ==> Q   or   P --> Q ==> P ==> Q *)
local
  val meta_iffD1 = @{lemma "P == Q ==> P ==> (Q::bool)" by simp}
  val meta_iffD1_c = T.precompose2 Thm.dest_binop meta_iffD1

  val iffD1_c = T.precompose2 (Thm.dest_binop o Thm.dest_arg) @{thm iffD1}
  val mp_c = T.precompose2 (Thm.dest_binop o Thm.dest_arg) @{thm mp}
in
fun mp (MetaEq thm) p = Thm (Thm.implies_elim (T.compose meta_iffD1_c thm) p)
  | mp p_q p = 
      let
        val pq = thm_of p_q
        val thm = T.compose iffD1_c pq handle THM _ => T.compose mp_c pq
      in Thm (Thm.implies_elim thm p) end
end



(* and_elim:     P1 & ... & Pn ==> Pi *)
(* not_or_elim:  ~(P1 | ... | Pn) ==> ~Pi *)
local
  fun is_sublit conj t = L.exists_lit conj (fn u => u aconv t)

  fun derive conj t lits idx ptab =
    let
      val lit = the (L.get_first_lit (is_sublit conj t) lits)
      val ls = L.explode conj false false [t] lit
      val lits' = fold L.insert_lit ls (L.delete_lit lit lits)

      fun upd (Proved thm) = Proved (Literals (thm_of thm, lits'))
        | upd p = p
    in (the (L.lookup_lit lits' t), Inttab.map_entry idx upd ptab) end

  fun lit_elim conj (p, idx) ct ptab =
    let val lits = literals_of p
    in
      (case L.lookup_lit lits (T.term_of ct) of
        SOME lit => (Thm lit, ptab)
      | NONE => apfst Thm (derive conj (T.term_of ct) lits idx ptab))
    end
in
val and_elim = lit_elim true
val not_or_elim = lit_elim false
end



(* P1, ..., Pn |- False ==> |- ~P1 | ... | ~Pn *)
local
  fun step lit thm =
    Thm.implies_elim (Thm.implies_intr (Thm.cprop_of lit) thm) lit
  val explode_disj = L.explode false false false
  fun intro hyps thm th = fold step (explode_disj hyps th) thm

  fun dest_ccontr ct = [Thm.dest_arg (Thm.dest_arg (Thm.dest_arg1 ct))]
  val ccontr = T.precompose dest_ccontr @{thm ccontr}
in
fun lemma thm ct =
  let
    val cu = Thm.capply @{cterm Not} (Thm.dest_arg ct)
    val hyps = map_filter (try HOLogic.dest_Trueprop) (#hyps (Thm.rep_thm thm))
  in Thm (T.compose ccontr (T.under_assumption (intro hyps thm) cu)) end
end



(* \/{P1, ..., Pn, Q1, ..., Qn}, ~P1, ..., ~Pn ==> \/{Q1, ..., Qn} *)
local
  val explode_disj = L.explode false true false
  val join_disj = L.join false
  fun unit thm thms th =
    let val t = @{term Not} $ T.prop_of thm and ts = map T.prop_of thms
    in join_disj (L.make_littab (thms @ explode_disj ts th)) t end

  fun dest_arg2 ct = Thm.dest_arg (Thm.dest_arg ct)
  fun dest ct = pairself dest_arg2 (Thm.dest_binop ct)
  val contrapos = T.precompose2 dest @{lemma "(~P ==> ~Q) ==> Q ==> P" by fast}
in
fun unit_resolution thm thms ct =
  Thm.capply @{cterm Not} (Thm.dest_arg ct)
  |> T.under_assumption (unit thm thms)
  |> Thm o T.discharge thm o T.compose contrapos
end



(* P ==> P == True   or   P ==> P == False *)
local
  val iff1 = @{lemma "P ==> P == (~ False)" by simp}
  val iff2 = @{lemma "~P ==> P == False" by simp}
in
fun iff_true thm = MetaEq (thm COMP iff1)
fun iff_false thm = MetaEq (thm COMP iff2)
end



(* distributivity of | over & *)
fun distributivity ctxt = Thm o try_apply ctxt [] [
  named ctxt "fast" (T.by_tac (Classical.fast_tac HOL_cs))]
    (* FIXME: not very well tested *)



(* Tseitin-like axioms *)

local
  val disjI1 = @{lemma "(P ==> Q) ==> ~P | Q" by fast}
  val disjI2 = @{lemma "(~P ==> Q) ==> P | Q" by fast}
  val disjI3 = @{lemma "(~Q ==> P) ==> P | Q" by fast}
  val disjI4 = @{lemma "(Q ==> P) ==> P | ~Q" by fast}

  fun prove' conj1 conj2 ct2 thm =
    let val lits = L.true_thm :: L.explode conj1 true (conj1 <> conj2) [] thm
    in L.join conj2 (L.make_littab lits) (Thm.term_of ct2) end

  fun prove rule (ct1, conj1) (ct2, conj2) =
    T.under_assumption (prove' conj1 conj2 ct2) ct1 COMP rule

  fun prove_def_axiom ct =
    let val (ct1, ct2) = Thm.dest_binop (Thm.dest_arg ct)
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
          in T.with_conv (dis_conv T.unfold_distinct_conv) prv ct end
      | @{term Not} $ (Const (@{const_name distinct}, _) $ _) =>
          let
            fun dis_conv cv = Conv.arg_conv (Conv.arg1_conv (Conv.arg_conv cv))
            fun prv cu =
              let val (cu1, cu2) = Thm.dest_binop (Thm.dest_arg cu)
              in prove disjI1 (Thm.dest_arg cu1, true) (cu2, true) end
          in T.with_conv (dis_conv T.unfold_distinct_conv) prv ct end
      | _ => raise CTERM ("prove_def_axiom", [ct]))
    end
in
fun def_axiom ctxt = Thm o try_apply ctxt [] [
  named ctxt "conj/disj/distinct" prove_def_axiom,
  T.by_abstraction (true, false) ctxt [] (fn ctxt' =>
    named ctxt' "simp+fast" (T.by_tac simp_fast_tac))]
end



(* local definitions *)
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

  val inst_rule = T.match_instantiate Thm.dest_arg

  fun apply_rule ct =
    (case get_first (try (inst_rule ct)) intro_rules of
      SOME thm => thm
    | NONE => raise CTERM ("intro_def", [ct]))
in
fun intro_def ct = T.make_hyp_def (apply_rule ct) #>> Thm

fun apply_def thm =
  get_first (try (fn rule => MetaEq (thm COMP rule))) apply_rules
  |> the_default (Thm thm)
end



(* negation normal form *)

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

  fun nnf_quant vars qs p ct =
    T.as_meta_eq ct
    |> T.by_tac (nnf_quant_tac (T.varify vars (meta_eq_of p)) qs)

  fun prove_nnf ctxt = try_apply ctxt [] [
    named ctxt "conj/disj" L.prove_conj_disj_eq,
    T.by_abstraction (true, false) ctxt [] (fn ctxt' =>
      named ctxt' "simp+fast" (T.by_tac simp_fast_tac))]
in
fun nnf ctxt vars ps ct =
  (case T.term_of ct of
    _ $ (l as Const _ $ Abs _) $ (r as Const _ $ Abs _) =>
      if l aconv r
      then MetaEq (Thm.reflexive (Thm.dest_arg (Thm.dest_arg ct)))
      else MetaEq (nnf_quant vars quant_rules1 (hd ps) ct)
  | _ $ (@{term Not} $ (Const _ $ Abs _)) $ (Const _ $ Abs _) =>
      MetaEq (nnf_quant vars quant_rules2 (hd ps) ct)
  | _ =>
      let
        val nnf_rewr_conv = Conv.arg_conv (Conv.arg_conv
          (T.unfold_eqs ctxt (map (Thm.symmetric o meta_eq_of) ps)))
      in Thm (T.with_conv nnf_rewr_conv (prove_nnf ctxt) ct) end)
end



(** equality proof rules **)

(* |- t = t *)
fun refl ct = MetaEq (Thm.reflexive (Thm.dest_arg (Thm.dest_arg ct)))



(* s = t ==> t = s *)
local
  val symm_rule = @{lemma "s = t ==> t == s" by simp}
in
fun symm (MetaEq thm) = MetaEq (Thm.symmetric thm)
  | symm p = MetaEq (thm_of p COMP symm_rule)
end



(* s = t ==> t = u ==> s = u *)
local
  val trans1 = @{lemma "s == t ==> t =  u ==> s == u" by simp}
  val trans2 = @{lemma "s =  t ==> t == u ==> s == u" by simp}
  val trans3 = @{lemma "s =  t ==> t =  u ==> s == u" by simp}
in
fun trans (MetaEq thm1) (MetaEq thm2) = MetaEq (Thm.transitive thm1 thm2)
  | trans (MetaEq thm) q = MetaEq (thm_of q COMP (thm COMP trans1))
  | trans p (MetaEq thm) = MetaEq (thm COMP (thm_of p COMP trans2))
  | trans p q = MetaEq (thm_of q COMP (thm_of p COMP trans3))
end



(* t1 = s1 ==> ... ==> tn = sn ==> f t1 ... tn = f s1 .. sn
   (reflexive antecendents are droppped) *)
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
  
  val prove_eq_exn = prove_eq true
  and prove_eq_safe = prove_eq false

  fun mono f (cp as (cl, _)) =
    (case Term.head_of (Thm.term_of cl) of
      @{term "op &"} => prove_nary L.is_conj (prove_eq_exn f)
    | @{term "op |"} => prove_nary L.is_disj (prove_eq_exn f)
    | Const (@{const_name distinct}, _) => prove_distinct (prove_eq_safe f)
    | _ => prove (prove_eq_safe f)) cp
in
fun monotonicity eqs ct =
  let
    val lookup = AList.lookup (op aconv) (map (`Thm.prop_of o meta_eq_of) eqs)
    val cp = Thm.dest_binop (Thm.dest_arg ct)
  in MetaEq (prove_eq_exn lookup cp handle MONO => mono lookup cp) end
end



(* |- f a b = f b a (where f is equality) *)
local
  val rule = @{lemma "a = b == b = a" by (atomize(full)) (rule eq_commute)}
in
fun commutativity ct = MetaEq (T.match_instantiate I (T.as_meta_eq ct) rule)
end



(** quantifier proof rules **)

(* P ?x = Q ?x ==> (ALL x. P x) = (ALL x. Q x)
   P ?x = Q ?x ==> (EX x. P x) = (EX x. Q x)    *)
local
  val rules = [
    @{lemma "(!!x. P x == Q x) ==> (ALL x. P x) == (ALL x. Q x)" by simp},
    @{lemma "(!!x. P x == Q x) ==> (EX x. P x) == (EX x. Q x)" by simp}]
in
fun quant_intro vars p ct =
  let
    val thm = meta_eq_of p
    val rules' = T.varify vars thm :: rules
    val cu = T.as_meta_eq ct
  in MetaEq (T.by_tac (REPEAT_ALL_NEW (Tactic.match_tac rules')) cu) end
end



(* |- ((ALL x. P x) | Q) = (ALL x. P x | Q) *)
fun pull_quant ctxt = Thm o try_apply ctxt [] [
  named ctxt "fast" (T.by_tac (Classical.fast_tac HOL_cs))]
    (* FIXME: not very well tested *)



(* |- (ALL x. P x & Q x) = ((ALL x. P x) & (ALL x. Q x)) *)
fun push_quant ctxt = Thm o try_apply ctxt [] [
  named ctxt "fast" (T.by_tac (Classical.fast_tac HOL_cs))]
    (* FIXME: not very well tested *)



(* |- (ALL x1 ... xn y1 ... yn. P x1 ... xn) = (ALL x1 ... xn. P x1 ... xn) *)
local
  val elim_all = @{lemma "(ALL x. P) == P" by simp}
  val elim_ex = @{lemma "(EX x. P) == P" by simp}

  fun elim_unused_conv ctxt =
    Conv.params_conv ~1 (K (Conv.arg_conv (Conv.arg1_conv
      (Conv.rewrs_conv [elim_all, elim_ex])))) ctxt

  fun elim_unused_tac ctxt =
    REPEAT_ALL_NEW (
      Tactic.match_tac [@{thm refl}, @{thm iff_allI}, @{thm iff_exI}]
      ORELSE' CONVERSION (elim_unused_conv ctxt))
in
fun elim_unused_vars ctxt = Thm o T.by_tac (elim_unused_tac ctxt)
end



(* |- (ALL x1 ... xn. ~(x1 = t1 & ... xn = tn) | P x1 ... xn) = P t1 ... tn *)
fun dest_eq_res ctxt = Thm o try_apply ctxt [] [
  named ctxt "fast" (T.by_tac (Classical.fast_tac HOL_cs))]
    (* FIXME: not very well tested *)



(* |- ~(ALL x1...xn. P x1...xn) | P a1...an *)
local
  val rule = @{lemma "~ P x | Q ==> ~(ALL x. P x) | Q" by fast}
in
val quant_inst = Thm o T.by_tac (
  REPEAT_ALL_NEW (Tactic.match_tac [rule])
  THEN' Tactic.rtac @{thm excluded_middle})
end



(* c = SOME x. P x |- (EX x. P x) = P c
   c = SOME x. ~ P x |- ~(ALL x. P x) = ~ P c *)
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
  fun pair2 (a, b) (c, d) = [(a, c), (b, d)]
  fun inst_sk (sk_rule, f) p c =
    Thm.instantiate ([(type_of f sk_rule, Thm.ctyp_of_term c)], []) sk_rule
    |> (fn sk' => Thm.instantiate ([], (pair2 (dest f sk') (p, c))) sk')
    |> Conv.fconv_rule (Thm.beta_conversion true)

  fun kind (Const (@{const_name Ex}, _) $ _) = (sk_ex_rule, I, I)
    | kind (@{term Not} $ (Const (@{const_name All}, _) $ _)) =
        (sk_all_rule, Thm.dest_arg, Thm.capply @{cterm Not})
    | kind t = raise TERM ("skolemize", [t])

  fun dest_abs_type (Abs (_, T, _)) = T
    | dest_abs_type t = raise TERM ("dest_abs_type", [t])

  fun bodies_of thy lhs rhs =
    let
      val (rule, dest, make) = kind (Thm.term_of lhs)

      fun dest_body idx cbs ct =
        let
          val cb = Thm.dest_arg (dest ct)
          val T = dest_abs_type (Thm.term_of cb)
          val cv = Thm.cterm_of thy (Var (("x", idx), T))
          val cu = make (Drule.beta_conv cb cv)
          val cbs' = (cv, cb) :: cbs
        in
          (snd (Thm.first_order_match (cu, rhs)), rev cbs')
          handle Pattern.MATCH => dest_body (idx+1) cbs' cu
        end
    in (rule, dest_body 1 [] lhs) end

  fun transitive f thm = Thm.transitive thm (f (Thm.rhs_of thm))

  fun sk_step (rule, elim) (cv, mct, cb) ((is, thm), ctxt) =
    (case mct of
      SOME ct =>
        ctxt
        |> T.make_hyp_def (inst_sk rule (Thm.instantiate_cterm ([], is) cb) ct)
        |>> pair ((cv, ct) :: is) o Thm.transitive thm
    | NONE => ((is, transitive (Conv.rewr_conv elim) thm), ctxt))
in
fun skolemize ct ctxt =
  let
    val (lhs, rhs) = Thm.dest_binop (Thm.dest_arg ct)
    val (rule, (ctab, cbs)) = bodies_of (ProofContext.theory_of ctxt) lhs rhs
    fun lookup_var (cv, cb) = (cv, AList.lookup (op aconvc) ctab cv, cb)
  in
    (([], Thm.reflexive lhs), ctxt)
    |> fold (sk_step rule) (map lookup_var cbs)
    |>> MetaEq o snd
  end
end



(** theory proof rules **)

(* theory lemmas: linear arithmetic, arrays *)

fun th_lemma ctxt simpset thms = Thm o try_apply ctxt thms [
  T.by_abstraction (false, true) ctxt thms (fn ctxt' => T.by_tac (
    NAMED ctxt' "arith" (Arith_Data.arith_tac ctxt')
    ORELSE' NAMED ctxt' "simp+arith" (Simplifier.simp_tac simpset THEN_ALL_NEW
      Arith_Data.arith_tac ctxt')))]



(* rewriting: prove equalities:
     * ACI of conjunction/disjunction
     * contradiction, excluded middle
     * logical rewriting rules (for negation, implication, equivalence,
         distinct)
     * normal forms for polynoms (integer/real arithmetic)
     * quantifier elimination over linear arithmetic
     * ... ? **)
structure Z3_Simps = Named_Thms
(
  val name = "z3_simp"
  val description = "simplification rules for Z3 proof reconstruction"
)

local
  fun spec_meta_eq_of thm =
    (case try (fn th => th RS @{thm spec}) thm of
      SOME thm' => spec_meta_eq_of thm'
    | NONE => mk_meta_eq thm)

  fun prep (Thm thm) = spec_meta_eq_of thm
    | prep (MetaEq thm) = thm
    | prep (Literals (thm, _)) = spec_meta_eq_of thm

  fun unfold_conv ctxt ths =
    Conv.arg_conv (Conv.binop_conv (T.unfold_eqs ctxt (map prep ths)))

  fun with_conv _ [] prv = prv
    | with_conv ctxt ths prv = T.with_conv (unfold_conv ctxt ths) prv

  val unfold_conv =
    Conv.arg_conv (Conv.binop_conv (Conv.try_conv T.unfold_distinct_conv))
  val prove_conj_disj_eq = T.with_conv unfold_conv L.prove_conj_disj_eq
in

fun rewrite ctxt simpset ths = Thm o with_conv ctxt ths (try_apply ctxt [] [
  named ctxt "conj/disj/distinct" prove_conj_disj_eq,
  T.by_abstraction (true, true) ctxt [] (fn ctxt' => T.by_tac (
    NAMED ctxt' "simp" (Simplifier.simp_tac simpset)
    THEN_ALL_NEW (
      NAMED ctxt' "fast" (Classical.fast_tac HOL_cs)
      ORELSE' NAMED ctxt' "arith" (Arith_Data.arith_tac ctxt'))))])

end



(** proof reconstruction **)

(* tracing and checking *)

local
  fun count_rules ptab =
    let
      fun count (_, Unproved _) (solved, total) = (solved, total + 1)
        | count (_, Proved _) (solved, total) = (solved + 1, total + 1)
    in Inttab.fold count ptab (0, 0) end

  fun header idx r (solved, total) = 
    "Z3: #" ^ string_of_int idx ^ ": " ^ P.string_of_rule r ^ " (goal " ^
    string_of_int (solved + 1) ^ " of " ^ string_of_int total ^ ")"

  fun check ctxt idx r ps ct p =
    let val thm = thm_of p |> tap (Thm.join_proofs o single)
    in
      if (Thm.cprop_of thm) aconvc ct then ()
      else z3_exn (Pretty.string_of (Pretty.big_list ("proof step failed: " ^
        quote (P.string_of_rule r) ^ " (#" ^ string_of_int idx ^ ")")
          (pretty_goal ctxt (map (thm_of o fst) ps) (Thm.prop_of thm) @
           [Pretty.block [Pretty.str "expected: ",
            Syntax.pretty_term ctxt (Thm.term_of ct)]])))
    end
in
fun trace_rule idx prove r ps ct (cxp as (ctxt, ptab)) =
  let
    val _ = SMT_Solver.trace_msg ctxt (header idx r o count_rules) ptab
    val result as (p, (ctxt', _)) = prove r ps ct cxp
    val _ = if not (Config.get ctxt' SMT_Solver.trace) then ()
      else check ctxt' idx r ps ct p
  in result end
end


(* overall reconstruction procedure *)

fun not_supported r =
  raise Fail ("Z3: proof rule not implemented: " ^ quote (P.string_of_rule r))

fun prove ctxt unfolds assms vars =
  let
    val assms' = prepare_assms ctxt unfolds assms
    val simpset = T.make_simpset ctxt (Z3_Simps.get ctxt)

    fun step r ps ct (cxp as (cx, ptab)) =
      (case (r, ps) of
        (* core rules *)
        (P.TrueAxiom, _) => (Thm L.true_thm, cxp)
      | (P.Asserted, _) => (asserted cx assms' ct, cxp)
      | (P.Goal, _) => (asserted cx assms' ct, cxp)
      | (P.ModusPonens, [(p, _), (q, _)]) => (mp q (thm_of p), cxp)
      | (P.ModusPonensOeq, [(p, _), (q, _)]) => (mp q (thm_of p), cxp)
      | (P.AndElim, [(p, i)]) => and_elim (p, i) ct ptab ||> pair cx
      | (P.NotOrElim, [(p, i)]) => not_or_elim (p, i) ct ptab ||> pair cx
      | (P.Hypothesis, _) => (Thm (Thm.assume ct), cxp)
      | (P.Lemma, [(p, _)]) => (lemma (thm_of p) ct, cxp)
      | (P.UnitResolution, (p, _) :: ps) =>
          (unit_resolution (thm_of p) (map (thm_of o fst) ps) ct, cxp)
      | (P.IffTrue, [(p, _)]) => (iff_true (thm_of p), cxp)
      | (P.IffFalse, [(p, _)]) => (iff_false (thm_of p), cxp)
      | (P.Distributivity, _) => (distributivity cx ct, cxp)
      | (P.DefAxiom, _) => (def_axiom cx ct, cxp)
      | (P.IntroDef, _) => intro_def ct cx ||> rpair ptab
      | (P.ApplyDef, [(p, _)]) => (apply_def (thm_of p), cxp)
      | (P.IffOeq, [(p, _)]) => (p, cxp)
      | (P.NnfPos, _) => (nnf cx vars (map fst ps) ct, cxp)
      | (P.NnfNeg, _) => (nnf cx vars (map fst ps) ct, cxp)

        (* equality rules *)
      | (P.Reflexivity, _) => (refl ct, cxp)
      | (P.Symmetry, [(p, _)]) => (symm p, cxp)
      | (P.Transitivity, [(p, _), (q, _)]) => (trans p q, cxp)
      | (P.Monotonicity, _) => (monotonicity (map fst ps) ct, cxp)
      | (P.Commutativity, _) => (commutativity ct, cxp)

        (* quantifier rules *)
      | (P.QuantIntro, [(p, _)]) => (quant_intro vars p ct, cxp)
      | (P.PullQuant, _) => (pull_quant cx ct, cxp)
      | (P.PushQuant, _) => (push_quant cx ct, cxp)
      | (P.ElimUnusedVars, _) => (elim_unused_vars cx ct, cxp)
      | (P.DestEqRes, _) => (dest_eq_res cx ct, cxp)
      | (P.QuantInst, _) => (quant_inst ct, cxp)
      | (P.Skolemize, _) => skolemize ct cx ||> rpair ptab

        (* theory rules *)
      | (P.ThLemma, _) =>
          (th_lemma cx simpset (map (thm_of o fst) ps) ct, cxp)
      | (P.Rewrite, _) => (rewrite cx simpset [] ct, cxp)
      | (P.RewriteStar, ps) =>
          (rewrite cx simpset (map fst ps) ct, cxp)

      | (P.NnfStar, _) => not_supported r
      | (P.CnfStar, _) => not_supported r
      | (P.TransitivityStar, _) => not_supported r
      | (P.PullQuantStar, _) => not_supported r

      | _ => raise Fail ("Z3: proof rule " ^ quote (P.string_of_rule r) ^
         " has an unexpected number of arguments."))

    fun conclude idx rule prop (ps, cxp) =
      trace_rule idx step rule ps prop cxp
      |-> (fn p => apsnd (Inttab.update (idx, Proved p)) #> pair p)

    fun lookup idx (cxp as (_, ptab)) =
      (case Inttab.lookup ptab idx of
        SOME (Unproved (P.Proof_Step {rule, prems, prop})) =>
          fold_map lookup prems cxp
          |>> map2 rpair prems
          |> conclude idx rule prop
      | SOME (Proved p) => (p, cxp)
      | NONE => z3_exn ("unknown proof id: " ^ quote (string_of_int idx)))

    fun result (p, (cx, _)) = (thm_of p, cx)
  in
    (fn (idx, ptab) => result (lookup idx (ctxt, Inttab.map Unproved ptab)))
  end

fun reconstruct (output, {typs, terms, unfolds, assms}) ctxt =
  P.parse ctxt typs terms output
  |> (fn (idx, (ptab, vars, cx)) => prove cx unfolds assms vars (idx, ptab))

val setup = trace_assms_setup #> z3_rules_setup #> Z3_Simps.setup

end
