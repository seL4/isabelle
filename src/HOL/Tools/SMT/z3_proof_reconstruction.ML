(*  Title:      HOL/Tools/SMT/z3_proof_reconstruction.ML
    Author:     Sascha Boehme, TU Muenchen

Proof reconstruction for proofs found by Z3.
*)

signature Z3_PROOF_RECONSTRUCTION =
sig
  val add_z3_rule: thm -> Context.generic -> Context.generic
  val reconstruct: Proof.context -> SMT_Translate.recon -> string list ->
    int list * thm
  val setup: theory -> theory
end

structure Z3_Proof_Reconstruction: Z3_PROOF_RECONSTRUCTION =
struct


fun z3_exn msg = raise SMT_Failure.SMT (SMT_Failure.Other_Failure
  ("Z3 proof reconstruction: " ^ msg))



(* net of schematic rules *)

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

  val prep =
    `Thm.prop_of o Simplifier.rewrite_rule [Z3_Proof_Literals.rewrite_true]

  fun ins thm net = Net.insert_term eq (prep thm) net handle Net.INSERT => net
  fun del thm net = Net.delete_term eq (prep thm) net handle Net.DELETE => net

  val add = Thm.declaration_attribute (Z3_Rules.map o ins)
  val del = Thm.declaration_attribute (Z3_Rules.map o del)
in

val add_z3_rule = Z3_Rules.map o ins

fun by_schematic_rule ctxt ct =
  the (Z3_Proof_Tools.net_instance (Z3_Rules.get (Context.Proof ctxt)) ct)

val z3_rules_setup =
  Attrib.setup (Binding.name z3_ruleN) (Attrib.add_del add del) description #>
  Global_Theory.add_thms_dynamic (Binding.name z3_ruleN, Net.content o Z3_Rules.get)

end



(* proof tools *)

fun named ctxt name prover ct =
  let val _ = SMT_Config.trace_msg ctxt I ("Z3: trying " ^ name ^ " ...")
  in prover ct end

fun NAMED ctxt name tac i st =
  let val _ = SMT_Config.trace_msg ctxt I ("Z3: trying " ^ name ^ " ...")
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
            SOME thm => (SMT_Config.trace_msg ctxt I "Z3: succeeded"; thm)
          | NONE => apply provers ct)

    fun schematic_label full = "schematic rules" |> full ? suffix " (full)"
    fun schematic ctxt full ct =
      ct
      |> full ? fold_rev (curry Drule.mk_implies o Thm.cprop_of) thms
      |> named ctxt (schematic_label full) (by_schematic_rule ctxt)
      |> fold Thm.elim_implies thms

  in apply o cons (schematic ctxt false) o cons (schematic ctxt true) end

local
  val rewr_if =
    @{lemma "(if P then Q1 else Q2) = ((P --> Q1) & (~P --> Q2))" by simp}
in

fun HOL_fast_tac ctxt =
  Classical.fast_tac (put_claset HOL_cs ctxt)

fun simp_fast_tac ctxt =
  Simplifier.simp_tac (HOL_ss addsimps [rewr_if])
  THEN_ALL_NEW HOL_fast_tac ctxt

end



(* theorems and proofs *)

(** theorem incarnations **)

datatype theorem =
  Thm of thm | (* theorem without special features *)
  MetaEq of thm | (* meta equality "t == s" *)
  Literals of thm * Z3_Proof_Literals.littab
    (* "P1 & ... & Pn" and table of all literals P1, ..., Pn *)

fun thm_of (Thm thm) = thm
  | thm_of (MetaEq thm) = thm COMP @{thm meta_eq_to_obj_eq}
  | thm_of (Literals (thm, _)) = thm

fun meta_eq_of (MetaEq thm) = thm
  | meta_eq_of p = mk_meta_eq (thm_of p)

fun literals_of (Literals (_, lits)) = lits
  | literals_of p = Z3_Proof_Literals.make_littab [thm_of p]



(** core proof rules **)

(* assumption *)

local
  val remove_trigger = mk_meta_eq @{thm SMT.trigger_def}
  val remove_weight = mk_meta_eq @{thm SMT.weight_def}
  val remove_fun_app = mk_meta_eq @{thm SMT.fun_app_def}

  fun rewrite_conv _ [] = Conv.all_conv
    | rewrite_conv ctxt eqs = Simplifier.full_rewrite
        (Simplifier.context ctxt Simplifier.empty_ss addsimps eqs)

  val prep_rules = [@{thm Let_def}, remove_trigger, remove_weight,
    remove_fun_app, Z3_Proof_Literals.rewrite_true]

  fun rewrite _ [] = I
    | rewrite ctxt eqs = Conv.fconv_rule (rewrite_conv ctxt eqs)

  fun lookup_assm assms_net ct =
    Z3_Proof_Tools.net_instances assms_net ct
    |> map (fn ithm as (_, thm) => (ithm, Thm.cprop_of thm aconvc ct))
in

fun add_asserted outer_ctxt rewrite_rules assms asserted ctxt =
  let
    val eqs = map (rewrite ctxt [Z3_Proof_Literals.rewrite_true]) rewrite_rules
    val eqs' = union Thm.eq_thm eqs prep_rules

    val assms_net =
      assms
      |> map (apsnd (rewrite ctxt eqs'))
      |> map (apsnd (Conv.fconv_rule Thm.eta_conversion))
      |> Z3_Proof_Tools.thm_net_of snd 

    fun revert_conv ctxt = rewrite_conv ctxt eqs' then_conv Thm.eta_conversion

    fun assume thm ctxt =
      let
        val ct = Thm.cprem_of thm 1
        val (thm', ctxt') = yield_singleton Assumption.add_assumes ct ctxt
      in (Thm.implies_elim thm thm', ctxt') end

    fun add1 idx thm1 ((i, th), exact) ((is, thms), (ctxt, ptab)) =
      let
        val (thm, ctxt') =
          if exact then (Thm.implies_elim thm1 th, ctxt)
          else assume thm1 ctxt
        val thms' = if exact then thms else th :: thms
      in 
        ((insert (op =) i is, thms'),
          (ctxt', Inttab.update (idx, Thm thm) ptab))
      end

    fun add (idx, ct) (cx as ((is, thms), (ctxt, ptab))) =
      let
        val thm1 = 
          Thm.trivial ct
          |> Conv.fconv_rule (Conv.arg1_conv (revert_conv outer_ctxt))
        val thm2 = singleton (Variable.export ctxt outer_ctxt) thm1
      in
        (case lookup_assm assms_net (Thm.cprem_of thm2 1) of
          [] =>
            let val (thm, ctxt') = assume thm1 ctxt
            in ((is, thms), (ctxt', Inttab.update (idx, Thm thm) ptab)) end
        | ithms => fold (add1 idx thm1) ithms cx)
      end
  in fold add asserted (([], []), (ctxt, Inttab.empty)) end

end


(* P = Q ==> P ==> Q   or   P --> Q ==> P ==> Q *)
local
  val precomp = Z3_Proof_Tools.precompose2
  val comp = Z3_Proof_Tools.compose

  val meta_iffD1 = @{lemma "P == Q ==> P ==> (Q::bool)" by simp}
  val meta_iffD1_c = precomp Thm.dest_binop meta_iffD1

  val iffD1_c = precomp (Thm.dest_binop o Thm.dest_arg) @{thm iffD1}
  val mp_c = precomp (Thm.dest_binop o Thm.dest_arg) @{thm mp}
in
fun mp (MetaEq thm) p = Thm (Thm.implies_elim (comp meta_iffD1_c thm) p)
  | mp p_q p = 
      let
        val pq = thm_of p_q
        val thm = comp iffD1_c pq handle THM _ => comp mp_c pq
      in Thm (Thm.implies_elim thm p) end
end


(* and_elim:     P1 & ... & Pn ==> Pi *)
(* not_or_elim:  ~(P1 | ... | Pn) ==> ~Pi *)
local
  fun is_sublit conj t = Z3_Proof_Literals.exists_lit conj (fn u => u aconv t)

  fun derive conj t lits idx ptab =
    let
      val lit = the (Z3_Proof_Literals.get_first_lit (is_sublit conj t) lits)
      val ls = Z3_Proof_Literals.explode conj false false [t] lit
      val lits' = fold Z3_Proof_Literals.insert_lit ls
        (Z3_Proof_Literals.delete_lit lit lits)

      fun upd thm = Literals (thm_of thm, lits')
      val ptab' = Inttab.map_entry idx upd ptab
    in (the (Z3_Proof_Literals.lookup_lit lits' t), ptab') end

  fun lit_elim conj (p, idx) ct ptab =
    let val lits = literals_of p
    in
      (case Z3_Proof_Literals.lookup_lit lits (SMT_Utils.term_of ct) of
        SOME lit => (Thm lit, ptab)
      | NONE => apfst Thm (derive conj (SMT_Utils.term_of ct) lits idx ptab))
    end
in
val and_elim = lit_elim true
val not_or_elim = lit_elim false
end


(* P1, ..., Pn |- False ==> |- ~P1 | ... | ~Pn *)
local
  fun step lit thm =
    Thm.implies_elim (Thm.implies_intr (Thm.cprop_of lit) thm) lit
  val explode_disj = Z3_Proof_Literals.explode false false false
  fun intro hyps thm th = fold step (explode_disj hyps th) thm

  fun dest_ccontr ct = [Thm.dest_arg (Thm.dest_arg (Thm.dest_arg1 ct))]
  val ccontr = Z3_Proof_Tools.precompose dest_ccontr @{thm ccontr}
in
fun lemma thm ct =
  let
    val cu = Z3_Proof_Literals.negate (Thm.dest_arg ct)
    val hyps = map_filter (try HOLogic.dest_Trueprop) (Thm.hyps_of thm)
    val th = Z3_Proof_Tools.under_assumption (intro hyps thm) cu
  in Thm (Z3_Proof_Tools.compose ccontr th) end
end


(* \/{P1, ..., Pn, Q1, ..., Qn}, ~P1, ..., ~Pn ==> \/{Q1, ..., Qn} *)
local
  val explode_disj = Z3_Proof_Literals.explode false true false
  val join_disj = Z3_Proof_Literals.join false
  fun unit thm thms th =
    let
      val t = @{const Not} $ SMT_Utils.prop_of thm
      val ts = map SMT_Utils.prop_of thms
    in
      join_disj (Z3_Proof_Literals.make_littab (thms @ explode_disj ts th)) t
    end

  fun dest_arg2 ct = Thm.dest_arg (Thm.dest_arg ct)
  fun dest ct = pairself dest_arg2 (Thm.dest_binop ct)
  val contrapos =
    Z3_Proof_Tools.precompose2 dest @{lemma "(~P ==> ~Q) ==> Q ==> P" by fast}
in
fun unit_resolution thm thms ct =
  Z3_Proof_Literals.negate (Thm.dest_arg ct)
  |> Z3_Proof_Tools.under_assumption (unit thm thms)
  |> Thm o Z3_Proof_Tools.discharge thm o Z3_Proof_Tools.compose contrapos
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
  named ctxt "fast" (Z3_Proof_Tools.by_tac (HOL_fast_tac ctxt))]
    (* FIXME: not very well tested *)


(* Tseitin-like axioms *)
local
  val disjI1 = @{lemma "(P ==> Q) ==> ~P | Q" by fast}
  val disjI2 = @{lemma "(~P ==> Q) ==> P | Q" by fast}
  val disjI3 = @{lemma "(~Q ==> P) ==> P | Q" by fast}
  val disjI4 = @{lemma "(Q ==> P) ==> P | ~Q" by fast}

  fun prove' conj1 conj2 ct2 thm =
    let
      val littab =
        Z3_Proof_Literals.explode conj1 true (conj1 <> conj2) [] thm
        |> cons Z3_Proof_Literals.true_thm
        |> Z3_Proof_Literals.make_littab
    in Z3_Proof_Literals.join conj2 littab (Thm.term_of ct2) end

  fun prove rule (ct1, conj1) (ct2, conj2) =
    Z3_Proof_Tools.under_assumption (prove' conj1 conj2 ct2) ct1 COMP rule

  fun prove_def_axiom ct =
    let val (ct1, ct2) = Thm.dest_binop (Thm.dest_arg ct)
    in
      (case Thm.term_of ct1 of
        @{const Not} $ (@{const HOL.conj} $ _ $ _) =>
          prove disjI1 (Thm.dest_arg ct1, true) (ct2, true)
      | @{const HOL.conj} $ _ $ _ =>
          prove disjI3 (Z3_Proof_Literals.negate ct2, false) (ct1, true)
      | @{const Not} $ (@{const HOL.disj} $ _ $ _) =>
          prove disjI3 (Z3_Proof_Literals.negate ct2, false) (ct1, false)
      | @{const HOL.disj} $ _ $ _ =>
          prove disjI2 (Z3_Proof_Literals.negate ct1, false) (ct2, true)
      | Const (@{const_name distinct}, _) $ _ =>
          let
            fun dis_conv cv = Conv.arg_conv (Conv.arg1_conv cv)
            val unfold_dis_conv = dis_conv Z3_Proof_Tools.unfold_distinct_conv
            fun prv cu =
              let val (cu1, cu2) = Thm.dest_binop (Thm.dest_arg cu)
              in prove disjI4 (Thm.dest_arg cu2, true) (cu1, true) end
          in Z3_Proof_Tools.with_conv unfold_dis_conv prv ct end
      | @{const Not} $ (Const (@{const_name distinct}, _) $ _) =>
          let
            fun dis_conv cv = Conv.arg_conv (Conv.arg1_conv (Conv.arg_conv cv))
            val unfold_dis_conv = dis_conv Z3_Proof_Tools.unfold_distinct_conv
            fun prv cu =
              let val (cu1, cu2) = Thm.dest_binop (Thm.dest_arg cu)
              in prove disjI1 (Thm.dest_arg cu1, true) (cu2, true) end
          in Z3_Proof_Tools.with_conv unfold_dis_conv prv ct end
      | _ => raise CTERM ("prove_def_axiom", [ct]))
    end
in
fun def_axiom ctxt = Thm o try_apply ctxt [] [
  named ctxt "conj/disj/distinct" prove_def_axiom,
  Z3_Proof_Tools.by_abstraction 0 (true, false) ctxt [] (fn ctxt' =>
    named ctxt' "simp+fast" (Z3_Proof_Tools.by_tac (simp_fast_tac ctxt')))]
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
      by (atomize(full)) fastforce} ]

  val inst_rule = Z3_Proof_Tools.match_instantiate Thm.dest_arg

  fun apply_rule ct =
    (case get_first (try (inst_rule ct)) intro_rules of
      SOME thm => thm
    | NONE => raise CTERM ("intro_def", [ct]))
in
fun intro_def ct = Z3_Proof_Tools.make_hyp_def (apply_rule ct) #>> Thm

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

  fun nnf_quant_tac_varified vars eq =
    nnf_quant_tac (Z3_Proof_Tools.varify vars eq)

  fun nnf_quant vars qs p ct =
    Z3_Proof_Tools.as_meta_eq ct
    |> Z3_Proof_Tools.by_tac (nnf_quant_tac_varified vars (meta_eq_of p) qs)

  fun prove_nnf ctxt = try_apply ctxt [] [
    named ctxt "conj/disj" Z3_Proof_Literals.prove_conj_disj_eq,
    Z3_Proof_Tools.by_abstraction 0 (true, false) ctxt [] (fn ctxt' =>
      named ctxt' "simp+fast" (Z3_Proof_Tools.by_tac (simp_fast_tac ctxt')))]
in
fun nnf ctxt vars ps ct =
  (case SMT_Utils.term_of ct of
    _ $ (l as Const _ $ Abs _) $ (r as Const _ $ Abs _) =>
      if l aconv r
      then MetaEq (Thm.reflexive (Thm.dest_arg (Thm.dest_arg ct)))
      else MetaEq (nnf_quant vars quant_rules1 (hd ps) ct)
  | _ $ (@{const Not} $ (Const _ $ Abs _)) $ (Const _ $ Abs _) =>
      MetaEq (nnf_quant vars quant_rules2 (hd ps) ct)
  | _ =>
      let
        val nnf_rewr_conv = Conv.arg_conv (Conv.arg_conv
          (Z3_Proof_Tools.unfold_eqs ctxt
            (map (Thm.symmetric o meta_eq_of) ps)))
      in Thm (Z3_Proof_Tools.with_conv nnf_rewr_conv (prove_nnf ctxt) ct) end)
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
  
  val prove_exn = prove_eq true
  and prove_safe = prove_eq false

  fun mono f (cp as (cl, _)) =
    (case Term.head_of (Thm.term_of cl) of
      @{const HOL.conj} => prove_nary Z3_Proof_Literals.is_conj (prove_exn f)
    | @{const HOL.disj} => prove_nary Z3_Proof_Literals.is_disj (prove_exn f)
    | Const (@{const_name distinct}, _) => prove_distinct (prove_safe f)
    | _ => prove (prove_safe f)) cp
in
fun monotonicity eqs ct =
  let
    fun and_symmetric (t, thm) = [(t, thm), (t, Thm.symmetric thm)]
    val teqs = maps (and_symmetric o `Thm.prop_of o meta_eq_of) eqs
    val lookup = AList.lookup (op aconv) teqs
    val cp = Thm.dest_binop (Thm.dest_arg ct)
  in MetaEq (prove_exn lookup cp handle MONO => mono lookup cp) end
end


(* |- f a b = f b a (where f is equality) *)
local
  val rule = @{lemma "a = b == b = a" by (atomize(full)) (rule eq_commute)}
in
fun commutativity ct =
  MetaEq (Z3_Proof_Tools.match_instantiate I
    (Z3_Proof_Tools.as_meta_eq ct) rule)
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
    val rules' = Z3_Proof_Tools.varify vars thm :: rules
    val cu = Z3_Proof_Tools.as_meta_eq ct
    val tac = REPEAT_ALL_NEW (Tactic.match_tac rules')
  in MetaEq (Z3_Proof_Tools.by_tac tac cu) end
end


(* |- ((ALL x. P x) | Q) = (ALL x. P x | Q) *)
fun pull_quant ctxt = Thm o try_apply ctxt [] [
  named ctxt "fast" (Z3_Proof_Tools.by_tac (HOL_fast_tac ctxt))]
    (* FIXME: not very well tested *)


(* |- (ALL x. P x & Q x) = ((ALL x. P x) & (ALL x. Q x)) *)
fun push_quant ctxt = Thm o try_apply ctxt [] [
  named ctxt "fast" (Z3_Proof_Tools.by_tac (HOL_fast_tac ctxt))]
    (* FIXME: not very well tested *)


(* |- (ALL x1 ... xn y1 ... yn. P x1 ... xn) = (ALL x1 ... xn. P x1 ... xn) *)
local
  val elim_all = @{lemma "P = Q ==> (ALL x. P) = Q" by fast}
  val elim_ex = @{lemma "P = Q ==> (EX x. P) = Q" by fast}

  fun elim_unused_tac i st = (
    Tactic.match_tac [@{thm refl}]
    ORELSE' (Tactic.match_tac [elim_all, elim_ex] THEN' elim_unused_tac)
    ORELSE' (
      Tactic.match_tac [@{thm iff_allI}, @{thm iff_exI}]
      THEN' elim_unused_tac)) i st
in

val elim_unused_vars = Thm o Z3_Proof_Tools.by_tac elim_unused_tac

end


(* |- (ALL x1 ... xn. ~(x1 = t1 & ... xn = tn) | P x1 ... xn) = P t1 ... tn *)
fun dest_eq_res ctxt = Thm o try_apply ctxt [] [
  named ctxt "fast" (Z3_Proof_Tools.by_tac (HOL_fast_tac ctxt))]
    (* FIXME: not very well tested *)


(* |- ~(ALL x1...xn. P x1...xn) | P a1...an *)
local
  val rule = @{lemma "~ P x | Q ==> ~(ALL x. P x) | Q" by fast}
in
val quant_inst = Thm o Z3_Proof_Tools.by_tac (
  REPEAT_ALL_NEW (Tactic.match_tac [rule])
  THEN' Tactic.rtac @{thm excluded_middle})
end


(* |- (EX x. P x) = P c     |- ~(ALL x. P x) = ~ P c *)
local
  val forall =
    SMT_Utils.mk_const_pat @{theory} @{const_name all}
      (SMT_Utils.destT1 o SMT_Utils.destT1)
  fun mk_forall cv ct =
    Thm.apply (SMT_Utils.instT' cv forall) (Thm.lambda cv ct)

  fun get_vars f mk pred ctxt t =
    Term.fold_aterms f t []
    |> map_filter (fn v =>
         if pred v then SOME (SMT_Utils.certify ctxt (mk v)) else NONE)

  fun close vars f ct ctxt =
    let
      val frees_of = get_vars Term.add_frees Free (member (op =) vars o fst)
      val vs = frees_of ctxt (Thm.term_of ct)
      val (thm, ctxt') = f (fold_rev mk_forall vs ct) ctxt
      val vars_of = get_vars Term.add_vars Var (K true) ctxt'
    in (Thm.instantiate ([], vars_of (Thm.prop_of thm) ~~ vs) thm, ctxt') end

  val sk_rules = @{lemma
    "c = (SOME x. P x) ==> (EX x. P x) = P c"
    "c = (SOME x. ~P x) ==> (~(ALL x. P x)) = (~P c)"
    by (metis someI_ex)+}
in

fun skolemize vars =
  apfst Thm oo close vars (yield_singleton Assumption.add_assumes)

fun discharge_sk_tac i st = (
  Tactic.rtac @{thm trans} i
  THEN Tactic.resolve_tac sk_rules i
  THEN (Tactic.rtac @{thm refl} ORELSE' discharge_sk_tac) (i+1)
  THEN Tactic.rtac @{thm refl} i) st

end



(** theory proof rules **)

(* theory lemmas: linear arithmetic, arrays *)
fun th_lemma ctxt simpset thms = Thm o try_apply ctxt thms [
  Z3_Proof_Tools.by_abstraction 0 (false, true) ctxt thms (fn ctxt' =>
    Z3_Proof_Tools.by_tac (
      NAMED ctxt' "arith" (Arith_Data.arith_tac ctxt')
      ORELSE' NAMED ctxt' "simp+arith" (
        Simplifier.asm_full_simp_tac simpset
        THEN_ALL_NEW Arith_Data.arith_tac ctxt')))]


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
  val name = @{binding z3_simp}
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
    Conv.arg_conv (Conv.binop_conv (Z3_Proof_Tools.unfold_eqs ctxt
      (map prep ths)))

  fun with_conv _ [] prv = prv
    | with_conv ctxt ths prv =
        Z3_Proof_Tools.with_conv (unfold_conv ctxt ths) prv

  val unfold_conv =
    Conv.arg_conv (Conv.binop_conv
      (Conv.try_conv Z3_Proof_Tools.unfold_distinct_conv))
  val prove_conj_disj_eq =
    Z3_Proof_Tools.with_conv unfold_conv Z3_Proof_Literals.prove_conj_disj_eq

  fun declare_hyps ctxt thm =
    (thm, snd (Assumption.add_assumes (#hyps (Thm.crep_thm thm)) ctxt))
in

val abstraction_depth = 3
  (*
    This value was chosen large enough to potentially catch exceptions,
    yet small enough to not cause too much harm.  The value might be
    increased in the future, if reconstructing 'rewrite' fails on problems
    that get too much abstracted to be reconstructable.
  *)

fun rewrite simpset ths ct ctxt =
  apfst Thm (declare_hyps ctxt (with_conv ctxt ths (try_apply ctxt [] [
    named ctxt "conj/disj/distinct" prove_conj_disj_eq,
    named ctxt "pull-ite" Z3_Proof_Methods.prove_ite,
    Z3_Proof_Tools.by_abstraction 0 (true, false) ctxt [] (fn ctxt' =>
      Z3_Proof_Tools.by_tac (
        NAMED ctxt' "simp (logic)" (Simplifier.simp_tac simpset)
        THEN_ALL_NEW NAMED ctxt' "fast (logic)" (fast_tac ctxt'))),
    Z3_Proof_Tools.by_abstraction 0 (false, true) ctxt [] (fn ctxt' =>
      Z3_Proof_Tools.by_tac (
        (Tactic.rtac @{thm iff_allI} ORELSE' K all_tac)
        THEN' NAMED ctxt' "simp (theory)" (Simplifier.simp_tac simpset)
        THEN_ALL_NEW (
          NAMED ctxt' "fast (theory)" (HOL_fast_tac ctxt')
          ORELSE' NAMED ctxt' "arith (theory)" (Arith_Data.arith_tac ctxt')))),
    Z3_Proof_Tools.by_abstraction 0 (true, true) ctxt [] (fn ctxt' =>
      Z3_Proof_Tools.by_tac (
        (Tactic.rtac @{thm iff_allI} ORELSE' K all_tac)
        THEN' NAMED ctxt' "simp (full)" (Simplifier.simp_tac simpset)
        THEN_ALL_NEW (
          NAMED ctxt' "fast (full)" (HOL_fast_tac ctxt')
          ORELSE' NAMED ctxt' "arith (full)" (Arith_Data.arith_tac ctxt')))),
    named ctxt "injectivity" (Z3_Proof_Methods.prove_injectivity ctxt),
    Z3_Proof_Tools.by_abstraction abstraction_depth (true, true) ctxt []
      (fn ctxt' =>
        Z3_Proof_Tools.by_tac (
          (Tactic.rtac @{thm iff_allI} ORELSE' K all_tac)
          THEN' NAMED ctxt' "simp (deepen)" (Simplifier.simp_tac simpset)
          THEN_ALL_NEW (
            NAMED ctxt' "fast (deepen)" (HOL_fast_tac ctxt')
            ORELSE' NAMED ctxt' "arith (deepen)" (Arith_Data.arith_tac
              ctxt'))))]) ct))

end



(* proof reconstruction *)

(** tracing and checking **)

fun trace_before ctxt idx = SMT_Config.trace_msg ctxt (fn r =>
  "Z3: #" ^ string_of_int idx ^ ": " ^ Z3_Proof_Parser.string_of_rule r)

fun check_after idx r ps ct (p, (ctxt, _)) =
  if not (Config.get ctxt SMT_Config.trace) then ()
  else
    let val thm = thm_of p |> tap (Thm.join_proofs o single)
    in
      if (Thm.cprop_of thm) aconvc ct then ()
      else
        z3_exn (Pretty.string_of (Pretty.big_list
          ("proof step failed: " ^ quote (Z3_Proof_Parser.string_of_rule r) ^
            " (#" ^ string_of_int idx ^ ")")
          (pretty_goal ctxt (map (thm_of o fst) ps) (Thm.prop_of thm) @
            [Pretty.block [Pretty.str "expected: ",
              Syntax.pretty_term ctxt (Thm.term_of ct)]])))
    end


(** overall reconstruction procedure **)

local
  fun not_supported r = raise Fail ("Z3: proof rule not implemented: " ^
    quote (Z3_Proof_Parser.string_of_rule r))

  fun prove_step simpset vars r ps ct (cxp as (cx, ptab)) =
    (case (r, ps) of
      (* core rules *)
      (Z3_Proof_Parser.True_Axiom, _) => (Thm Z3_Proof_Literals.true_thm, cxp)
    | (Z3_Proof_Parser.Asserted, _) => raise Fail "bad assertion"
    | (Z3_Proof_Parser.Goal, _) => raise Fail "bad assertion"
    | (Z3_Proof_Parser.Modus_Ponens, [(p, _), (q, _)]) =>
        (mp q (thm_of p), cxp)
    | (Z3_Proof_Parser.Modus_Ponens_Oeq, [(p, _), (q, _)]) =>
        (mp q (thm_of p), cxp)
    | (Z3_Proof_Parser.And_Elim, [(p, i)]) =>
        and_elim (p, i) ct ptab ||> pair cx
    | (Z3_Proof_Parser.Not_Or_Elim, [(p, i)]) =>
        not_or_elim (p, i) ct ptab ||> pair cx
    | (Z3_Proof_Parser.Hypothesis, _) => (Thm (Thm.assume ct), cxp)
    | (Z3_Proof_Parser.Lemma, [(p, _)]) => (lemma (thm_of p) ct, cxp)
    | (Z3_Proof_Parser.Unit_Resolution, (p, _) :: ps) =>
        (unit_resolution (thm_of p) (map (thm_of o fst) ps) ct, cxp)
    | (Z3_Proof_Parser.Iff_True, [(p, _)]) => (iff_true (thm_of p), cxp)
    | (Z3_Proof_Parser.Iff_False, [(p, _)]) => (iff_false (thm_of p), cxp)
    | (Z3_Proof_Parser.Distributivity, _) => (distributivity cx ct, cxp)
    | (Z3_Proof_Parser.Def_Axiom, _) => (def_axiom cx ct, cxp)
    | (Z3_Proof_Parser.Intro_Def, _) => intro_def ct cx ||> rpair ptab
    | (Z3_Proof_Parser.Apply_Def, [(p, _)]) => (apply_def (thm_of p), cxp)
    | (Z3_Proof_Parser.Iff_Oeq, [(p, _)]) => (p, cxp)
    | (Z3_Proof_Parser.Nnf_Pos, _) => (nnf cx vars (map fst ps) ct, cxp)
    | (Z3_Proof_Parser.Nnf_Neg, _) => (nnf cx vars (map fst ps) ct, cxp)

      (* equality rules *)
    | (Z3_Proof_Parser.Reflexivity, _) => (refl ct, cxp)
    | (Z3_Proof_Parser.Symmetry, [(p, _)]) => (symm p, cxp)
    | (Z3_Proof_Parser.Transitivity, [(p, _), (q, _)]) => (trans p q, cxp)
    | (Z3_Proof_Parser.Monotonicity, _) => (monotonicity (map fst ps) ct, cxp)
    | (Z3_Proof_Parser.Commutativity, _) => (commutativity ct, cxp)

      (* quantifier rules *)
    | (Z3_Proof_Parser.Quant_Intro, [(p, _)]) => (quant_intro vars p ct, cxp)
    | (Z3_Proof_Parser.Pull_Quant, _) => (pull_quant cx ct, cxp)
    | (Z3_Proof_Parser.Push_Quant, _) => (push_quant cx ct, cxp)
    | (Z3_Proof_Parser.Elim_Unused_Vars, _) => (elim_unused_vars ct, cxp)
    | (Z3_Proof_Parser.Dest_Eq_Res, _) => (dest_eq_res cx ct, cxp)
    | (Z3_Proof_Parser.Quant_Inst, _) => (quant_inst ct, cxp)
    | (Z3_Proof_Parser.Skolemize, _) => skolemize vars ct cx ||> rpair ptab

      (* theory rules *)
    | (Z3_Proof_Parser.Th_Lemma _, _) =>  (* FIXME: use arguments *)
        (th_lemma cx simpset (map (thm_of o fst) ps) ct, cxp)
    | (Z3_Proof_Parser.Rewrite, _) => rewrite simpset [] ct cx ||> rpair ptab
    | (Z3_Proof_Parser.Rewrite_Star, ps) =>
        rewrite simpset (map fst ps) ct cx ||> rpair ptab

    | (Z3_Proof_Parser.Nnf_Star, _) => not_supported r
    | (Z3_Proof_Parser.Cnf_Star, _) => not_supported r
    | (Z3_Proof_Parser.Transitivity_Star, _) => not_supported r
    | (Z3_Proof_Parser.Pull_Quant_Star, _) => not_supported r

    | _ => raise Fail ("Z3: proof rule " ^
        quote (Z3_Proof_Parser.string_of_rule r) ^
        " has an unexpected number of arguments."))

  fun lookup_proof ptab idx =
    (case Inttab.lookup ptab idx of
      SOME p => (p, idx)
    | NONE => z3_exn ("unknown proof id: " ^ quote (string_of_int idx)))

  fun prove simpset vars (idx, step) (_, cxp as (ctxt, ptab)) =
    let
      val Z3_Proof_Parser.Proof_Step {rule=r, prems, prop, ...} = step
      val ps = map (lookup_proof ptab) prems
      val _ = trace_before ctxt idx r
      val (thm, (ctxt', ptab')) =
        cxp
        |> prove_step simpset vars r ps prop
        |> tap (check_after idx r ps prop)
    in (thm, (ctxt', Inttab.update (idx, thm) ptab')) end

  fun make_discharge_rules rules = rules @ [@{thm allI}, @{thm refl},
    @{thm reflexive}, Z3_Proof_Literals.true_thm]

  fun discharge_assms_tac rules =
    REPEAT (HEADGOAL (
      Tactic.resolve_tac rules ORELSE' SOLVED' discharge_sk_tac))
    
  fun discharge_assms rules thm =
    if Thm.nprems_of thm = 0 then Goal.norm_result thm
    else
      (case Seq.pull (discharge_assms_tac rules thm) of
        SOME (thm', _) => Goal.norm_result thm'
      | NONE => raise THM ("failed to discharge premise", 1, [thm]))

  fun discharge rules outer_ctxt (p, (inner_ctxt, _)) =
    thm_of p
    |> singleton (Proof_Context.export inner_ctxt outer_ctxt)
    |> discharge_assms (make_discharge_rules rules)
in

fun reconstruct outer_ctxt recon output =
  let
    val {context=ctxt, typs, terms, rewrite_rules, assms} = recon
    val (asserted, steps, vars, ctxt1) =
      Z3_Proof_Parser.parse ctxt typs terms output

    val simpset = Z3_Proof_Tools.make_simpset ctxt1 (Z3_Simps.get ctxt1)

    val ((is, rules), cxp as (ctxt2, _)) =
      add_asserted outer_ctxt rewrite_rules assms asserted ctxt1
  in
    if Config.get ctxt2 SMT_Config.filter_only_facts then (is, @{thm TrueI})
    else
      (Thm @{thm TrueI}, cxp)
      |> fold (prove simpset vars) steps 
      |> discharge rules outer_ctxt
      |> pair []
  end

end

val setup = z3_rules_setup #> Z3_Simps.setup

end
