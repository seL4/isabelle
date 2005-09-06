(*  Title       : HOL/Hyperreal/Transfer.thy
    ID          : $Id$
    Author      : Brian Huffman
*)

header {* Transfer Principle *}

theory Transfer
imports StarType
begin

subsection {* Preliminaries *}

text {* These transform expressions like @{term "{n. f (P n)} \<in> \<U>"} *}

lemma fuf_ex:
  "({n. \<exists>x. P n x} \<in> \<U>) = (\<exists>X. {n. P n (X n)} \<in> \<U>)"
proof
  assume "{n. \<exists>x. P n x} \<in> \<U>"
  hence "{n. P n (SOME x. P n x)} \<in> \<U>"
    by (auto elim: someI filter.subset [OF filter_FUFNat])
  thus "\<exists>X. {n. P n (X n)} \<in> \<U>" by fast
next
  show "\<exists>X. {n. P n (X n)} \<in> \<U> \<Longrightarrow> {n. \<exists>x. P n x} \<in> \<U>"
    by (auto elim: filter.subset [OF filter_FUFNat])
qed

lemma fuf_not: "({n. \<not> P n} \<in> \<U>) = ({n. P n} \<notin> \<U>)"
 apply (subst Collect_neg_eq)
 apply (rule ultrafilter.Compl_iff [OF ultrafilter_FUFNat])
done

lemma fuf_conj:
  "({n. P n \<and> Q n} \<in> \<U>) = ({n. P n} \<in> \<U> \<and> {n. Q n} \<in> \<U>)"
 apply (subst Collect_conj_eq)
 apply (rule filter.Int_iff [OF filter_FUFNat])
done

lemma fuf_disj:
  "({n. P n \<or> Q n} \<in> \<U>) = ({n. P n} \<in> \<U> \<or> {n. Q n} \<in> \<U>)"
 apply (subst Collect_disj_eq)
 apply (rule ultrafilter.Un_iff [OF ultrafilter_FUFNat])
done

lemma fuf_imp:
  "({n. P n \<longrightarrow> Q n} \<in> \<U>) = ({n. P n} \<in> \<U> \<longrightarrow> {n. Q n} \<in> \<U>)"
by (simp only: imp_conv_disj fuf_disj fuf_not)

lemma fuf_iff:
  "({n. P n = Q n} \<in> \<U>) = (({n. P n} \<in> \<U>) = ({n. Q n} \<in> \<U>))"
by (simp add: iff_conv_conj_imp fuf_conj fuf_imp)

lemma fuf_all:
  "({n. \<forall>x. P n x} \<in> \<U>) = (\<forall>X. {n. P n (X n)} \<in> \<U>)"
 apply (rule Not_eq_iff [THEN iffD1])
 apply (simp add: fuf_not [symmetric])
 apply (rule fuf_ex)
done

lemma fuf_if_bool:
  "({n. if P n then Q n else R n} \<in> \<U>) =
    (if {n. P n} \<in> \<U> then {n. Q n} \<in> \<U> else {n. R n} \<in> \<U>)"
by (simp add: if_bool_eq_conj fuf_conj fuf_imp fuf_not)

lemma fuf_eq:
  "({n. X n = Y n} \<in> \<U>) = (star_n X = star_n Y)"
by (rule star_n_eq_iff [symmetric])

lemma fuf_if:
  "star_n (\<lambda>n. if P n then X n else Y n) =
    (if {n. P n} \<in> \<U> then star_n X else star_n Y)"
by (auto simp add: star_n_eq_iff fuf_not [symmetric] elim: ultra)

subsection {* Starting the transfer proof *}

text {*
  A transfer theorem asserts an equivalence @{prop "P \<equiv> P'"}
  between two related propositions. Proposition @{term P} may
  refer to constants having star types, like @{typ "'a star"}.
  Proposition @{term P'} is syntactically similar, but only
  refers to ordinary types (i.e. @{term P'} is the un-starred
  version of @{term P}).
*}

text {* This introduction rule starts each transfer proof. *}

lemma transfer_start:
  "P \<equiv> {n. Q} \<in> \<U> \<Longrightarrow> Trueprop P \<equiv> Trueprop Q"
by (subgoal_tac "P \<equiv> Q", simp, simp add: atomize_eq)

subsection {* Transfer introduction rules *}

text {*
  The proof of a transfer theorem is completely syntax-directed.
  At each step in the proof, the top-level connective determines
  which introduction rule to apply. Each argument to the top-level
  connective generates a new subgoal.
*}

text {*
  Subgoals in a transfer proof always have the form of an equivalence.
  The left side can be any term, and may contain references to star
  types. The form of the right side depends on its type. At type
  @{typ bool} it takes the form @{term "{n. P n} \<in> \<U>"}. At type
  @{typ "'a star"} it takes the form @{term "star_n (\<lambda>n. X n)"}. At type
  @{typ "'a star set"} it looks like @{term "Iset (star_n (\<lambda>n. A n))"}.
  And at type @{typ "'a star \<Rightarrow> 'b star"} it has the form
  @{term "Ifun (star_n (\<lambda>n. F n))"}.
*}

subsubsection {* Boolean operators *}

lemma transfer_not:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>\<rbrakk> \<Longrightarrow> \<not> p \<equiv> {n. \<not> P n} \<in> \<U>"
by (simp only: fuf_not)

lemma transfer_conj:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; q \<equiv> {n. Q n} \<in> \<U>\<rbrakk>
    \<Longrightarrow> p \<and> q \<equiv> {n. P n \<and> Q n} \<in> \<U>"
by (simp only: fuf_conj)

lemma transfer_disj:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; q \<equiv> {n. Q n} \<in> \<U>\<rbrakk>
    \<Longrightarrow> p \<or> q \<equiv> {n. P n \<or> Q n} \<in> \<U>"
by (simp only: fuf_disj)

lemma transfer_imp:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; q \<equiv> {n. Q n} \<in> \<U>\<rbrakk>
    \<Longrightarrow> p \<longrightarrow> q \<equiv> {n. P n \<longrightarrow> Q n} \<in> \<U>"
by (simp only: fuf_imp)

lemma transfer_iff:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; q \<equiv> {n. Q n} \<in> \<U>\<rbrakk>
    \<Longrightarrow> p = q \<equiv> {n. P n = Q n} \<in> \<U>"
by (simp only: fuf_iff)

lemma transfer_if_bool:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; x \<equiv> {n. X n} \<in> \<U>; y \<equiv> {n. Y n} \<in> \<U>\<rbrakk>
    \<Longrightarrow> (if p then x else y) \<equiv> {n. if P n then X n else Y n} \<in> \<U>"
by (simp only: fuf_if_bool)

lemma transfer_all_bool:
  "\<lbrakk>\<And>x. p x \<equiv> {n. P n x} \<in> \<U>\<rbrakk> \<Longrightarrow> \<forall>x::bool. p x \<equiv> {n. \<forall>x. P n x} \<in> \<U>"
by (simp only: all_bool_eq fuf_conj)

lemma transfer_ex_bool:
  "\<lbrakk>\<And>x. p x \<equiv> {n. P n x} \<in> \<U>\<rbrakk> \<Longrightarrow> \<exists>x::bool. p x \<equiv> {n. \<exists>x. P n x} \<in> \<U>"
by (simp only: ex_bool_eq fuf_disj)

subsubsection {* Equals, If *}

lemma transfer_eq:
  "\<lbrakk>x \<equiv> star_n X; y \<equiv> star_n Y\<rbrakk> \<Longrightarrow> x = y \<equiv> {n. X n = Y n} \<in> \<U>"
by (simp only: fuf_eq)

lemma transfer_if:
  "\<lbrakk>p \<equiv> {n. P n} \<in> \<U>; x \<equiv> star_n X; y \<equiv> star_n Y\<rbrakk>
    \<Longrightarrow> (if p then x else y) \<equiv> star_n (\<lambda>n. if P n then X n else Y n)"
by (simp only: fuf_if)

subsubsection {* Quantifiers *}

lemma transfer_all:
  "\<lbrakk>\<And>X. p (star_n X) \<equiv> {n. P n (X n)} \<in> \<U>\<rbrakk>
    \<Longrightarrow> \<forall>x::'a star. p x \<equiv> {n. \<forall>x. P n x} \<in> \<U>"
by (simp only: all_star_eq fuf_all)

lemma transfer_ex:
  "\<lbrakk>\<And>X. p (star_n X) \<equiv> {n. P n (X n)} \<in> \<U>\<rbrakk>
    \<Longrightarrow> \<exists>x::'a star. p x \<equiv> {n. \<exists>x. P n x} \<in> \<U>"
by (simp only: ex_star_eq fuf_ex)

lemma transfer_ex1:
  "\<lbrakk>\<And>X. p (star_n X) \<equiv> {n. P n (X n)} \<in> \<U>\<rbrakk>
    \<Longrightarrow> \<exists>!x. p x \<equiv> {n. \<exists>!x. P n x} \<in> \<U>"
by (simp only: Ex1_def transfer_ex transfer_conj
   transfer_all transfer_imp transfer_eq)

subsubsection {* Functions *}

lemma transfer_Ifun:
  "\<lbrakk>f \<equiv> star_n F; x \<equiv> star_n X\<rbrakk>
    \<Longrightarrow> f \<star> x \<equiv> star_n (\<lambda>n. F n (X n))"
by (simp only: Ifun_star_n)

lemma transfer_fun_eq:
  "\<lbrakk>\<And>X. f (star_n X) = g (star_n X) 
    \<equiv> {n. F n (X n) = G n (X n)} \<in> \<U>\<rbrakk>
      \<Longrightarrow> f = g \<equiv> {n. F n = G n} \<in> \<U>"
by (simp only: expand_fun_eq transfer_all)

subsubsection {* Sets *}

lemma transfer_Iset:
  "\<lbrakk>a \<equiv> star_n A\<rbrakk> \<Longrightarrow> Iset a \<equiv> Iset (star_n (\<lambda>n. A n))"
by simp

lemma transfer_Collect:
  "\<lbrakk>\<And>X. p (star_n X) \<equiv> {n. P n (X n)} \<in> \<U>\<rbrakk>
    \<Longrightarrow> Collect p \<equiv> Iset (star_n (\<lambda>n. Collect (P n)))"
by (simp add: atomize_eq expand_set_eq all_star_eq Iset_star_n)

lemma transfer_mem:
  "\<lbrakk>x \<equiv> star_n X; a \<equiv> Iset (star_n A)\<rbrakk>
    \<Longrightarrow> x \<in> a \<equiv> {n. X n \<in> A n} \<in> \<U>"
by (simp only: Iset_star_n)

lemma transfer_set_eq:
  "\<lbrakk>a \<equiv> Iset (star_n A); b \<equiv> Iset (star_n B)\<rbrakk>
    \<Longrightarrow> a = b \<equiv> {n. A n = B n} \<in> \<U>"
by (simp only: expand_set_eq transfer_all transfer_iff transfer_mem)

lemma transfer_ball:
  "\<lbrakk>a \<equiv> Iset (star_n A); \<And>X. p (star_n X) \<equiv> {n. P n (X n)} \<in> \<U>\<rbrakk>
    \<Longrightarrow> \<forall>x\<in>a. p x \<equiv> {n. \<forall>x\<in>A n. P n x} \<in> \<U>"
by (simp only: Ball_def transfer_all transfer_imp transfer_mem)

lemma transfer_bex:
  "\<lbrakk>a \<equiv> Iset (star_n A); \<And>X. p (star_n X) \<equiv> {n. P n (X n)} \<in> \<U>\<rbrakk>
    \<Longrightarrow> \<exists>x\<in>a. p x \<equiv> {n. \<exists>x\<in>A n. P n x} \<in> \<U>"
by (simp only: Bex_def transfer_ex transfer_conj transfer_mem)

subsubsection {* Miscellaneous *}

lemma transfer_unstar:
  "p \<equiv> star_n P \<Longrightarrow> unstar p \<equiv> {n. P n} \<in> \<U>"
by (simp only: unstar_star_n)

lemma transfer_star_n: "star_n X \<equiv> star_n (\<lambda>n. X n)"
by (rule reflexive)

lemma transfer_bool: "p \<equiv> {n. p} \<in> \<U>"
by (simp add: atomize_eq)

lemmas transfer_intros =
  transfer_star_n
  transfer_Ifun
  transfer_fun_eq

  transfer_not
  transfer_conj
  transfer_disj
  transfer_imp
  transfer_iff
  transfer_if_bool
  transfer_all_bool
  transfer_ex_bool

  transfer_all
  transfer_ex

  transfer_unstar
  transfer_bool
  transfer_eq
  transfer_if

  transfer_set_eq
  transfer_Iset
  transfer_Collect
  transfer_mem
  transfer_ball
  transfer_bex

subsection {* Transfer tactic *}

text {*
  We start by giving ML bindings for the theorems that
  will used by the transfer tactic. Ideally, some of the
  lists of theorems should be expandable.
  To @{text star_class_defs} we would like to add theorems
  about @{term nat_of}, @{term int_of}, @{term meet},
  @{term join}, etc.
  Also, we would like to create introduction rules for new
  constants.
*}

ML_setup {*
val atomizers = map thm ["atomize_all", "atomize_imp", "atomize_eq"]
val Ifun_defs = thms "Ifun_defs" @ [thm "Iset_of_def"]
val star_class_defs = thms "star_class_defs"
val transfer_defs = atomizers @ Ifun_defs @ star_class_defs

val transfer_start = thm "transfer_start"
val transfer_intros = thms "transfer_intros"
val transfer_Ifun = thm "transfer_Ifun"
*}

text {*
  Next we define the ML function @{text unstar_term}.
  This function takes a term, and gives back an equivalent
  term that does not contain any references to the @{text star}
  type constructor. Hopefully the resulting term will still be
  type-correct: Any constant whose type contains @{text star}
  should either be polymorphic (so that it will still work at
  the un-starred instance) or listed in @{text star_consts}
  (so it can be removed).
  Maybe @{text star_consts} should be extensible?
*}

ML_setup {*
local
  fun unstar_typ (Type ("StarType.star",[t])) = unstar_typ t
    | unstar_typ (Type (a, Ts)) = Type (a, map unstar_typ Ts)
    | unstar_typ T = T

  val star_consts =
    [ "StarType.star_of", "StarType.Ifun"
    , "StarType.Ifun_of", "StarType.Ifun2"
    , "StarType.Ifun2_of", "StarType.Ipred"
    , "StarType.Ipred_of", "StarType.Ipred2"
    , "StarType.Ipred2_of", "StarType.Iset"
    , "StarType.Iset_of", "StarType.unstar" ]

  fun is_star_const a = exists (fn x => x = a) star_consts
in
  fun unstar_term (Const(a,T) $ x) = if (is_star_const a)
                     then (unstar_term x)
                     else (Const(a,unstar_typ T) $ unstar_term x)
    | unstar_term (f $ t) = unstar_term f $ unstar_term t
    | unstar_term (Const(a,T)) = Const(a,unstar_typ T)
    | unstar_term (Abs(a,T,t)) = Abs(a,unstar_typ T,unstar_term t) 
    | unstar_term t = t
end
*}

text {*
  The @{text transfer_thm_of} function takes a term that
  represents a proposition, and proves that it is logically
  equivalent to the un-starred version. Assuming all goes
  well, it returns a theorem asserting the equivalence.
*}

text {*
  TODO: We need some error messages for when things go
  wrong. Errors may be caused by constants that don't have
  matching introduction rules, or quantifiers over wrong types.
*}

ML_setup {*
local
  val tacs =
    [ match_tac [transitive_thm] 1
    , resolve_tac [transfer_start] 1
    , REPEAT_ALL_NEW (resolve_tac transfer_intros) 1
    , match_tac [reflexive_thm] 1 ]
in
  fun transfer_thm_of sg ths t =
      let val u = unstar_term t
          val e = Const("==", propT --> propT --> propT)
          val c = cterm_of sg (e $ t $ u)
      in prove_goalw_cterm (transfer_defs @ ths) c (fn _ => tacs)
      end
end
*}

text {*
  Instead of applying the @{thm [source] transfer_start} rule
  right away, the proof of each transfer theorem starts with the
  transitivity rule @{text "\<lbrakk>P \<equiv> ?Q; ?Q \<equiv> P'\<rbrakk> \<Longrightarrow> P \<equiv> P'"}, which
  introduces a new unbound schematic variable @{text ?Q}. The first
  premise @{text "P \<equiv> ?Q"} is solved by recursively using 
  @{thm [source] transfer_start} and @{thm [source] transfer_intros}.
  Each rule application adds constraints to the form of @{text ?Q};
  by the time the first premise is proved, @{text ?Q} is completely
  bound to the value of @{term P'}. Finally, the second premise is
  resolved with the reflexivity rule @{text "P' \<equiv> P'"}.
*}

text {*
  The delayed binding is necessary for the correct operation of the
  introduction rule @{thm [source] transfer_Ifun}:
  @{thm transfer_Ifun[of f _ x]}. With a subgoal of the form
  @{term "f \<star> x \<equiv> star_n (\<lambda>n. F n (X n))"}, we would like to bind @{text ?F}
  to @{text F} and @{text ?X} to @{term X}. Unfortunately, higher-order
  unification finds more than one possible match, and binds @{text ?F}
  to @{term "\<lambda>x. x"} by default. If the right-hand side of the subgoal
  contains an unbound schematic variable instead of the explicit
  application @{term "F n (X n)"}, then we can ensure that there is
  only one possible way to match the rule.
*}

ML_setup {*
fun transfer_tac ths =
    SUBGOAL (fn (t,i) =>
        (fn th =>
            let val tr = transfer_thm_of (sign_of_thm th) ths t
            in rewrite_goals_tac [tr] th
            end
        )
    )
*}

text {*
  Finally we set up the @{text transfer} method. It takes
  an optional list of definitions as arguments; they are
  passed along to @{text transfer_thm_of}, which expands
  the definitions before attempting to prove the transfer
  theorem.
*}

method_setup transfer = {*
  Method.thms_args
    (fn ths => Method.SIMPLE_METHOD' HEADGOAL (transfer_tac ths))
*} "transfer principle"

text {* Sample theorems *}

lemma Ifun_inject: "\<And>f g. (Ifun f = Ifun g) = (f = g)"
by transfer (rule refl)

lemma unstar_inject: "\<And>x y. (unstar x = unstar y) = (x = y)"
by transfer (rule refl)

lemma Iset_inject: "\<And>A B. (Iset A = Iset B) = (A = B)"
by transfer (rule refl)

end
