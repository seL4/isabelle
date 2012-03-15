(*  Title:      HOL/Hilbert_Choice.thy
    Author:     Lawrence C Paulson, Tobias Nipkow
    Copyright   2001  University of Cambridge
*)

header {* Hilbert's Epsilon-Operator and the Axiom of Choice *}

theory Hilbert_Choice
imports Nat Wellfounded Plain
keywords "specification" "ax_specification" :: thy_goal
uses ("Tools/choice_specification.ML")
begin

subsection {* Hilbert's epsilon *}

axiomatization Eps :: "('a => bool) => 'a" where
  someI: "P x ==> P (Eps P)"

syntax (epsilon)
  "_Eps"        :: "[pttrn, bool] => 'a"    ("(3\<some>_./ _)" [0, 10] 10)
syntax (HOL)
  "_Eps"        :: "[pttrn, bool] => 'a"    ("(3@ _./ _)" [0, 10] 10)
syntax
  "_Eps"        :: "[pttrn, bool] => 'a"    ("(3SOME _./ _)" [0, 10] 10)
translations
  "SOME x. P" == "CONST Eps (%x. P)"

print_translation {*
  [(@{const_syntax Eps}, fn [Abs abs] =>
      let val (x, t) = Syntax_Trans.atomic_abs_tr' abs
      in Syntax.const @{syntax_const "_Eps"} $ x $ t end)]
*} -- {* to avoid eta-contraction of body *}

definition inv_into :: "'a set => ('a => 'b) => ('b => 'a)" where
"inv_into A f == %x. SOME y. y : A & f y = x"

abbreviation inv :: "('a => 'b) => ('b => 'a)" where
"inv == inv_into UNIV"


subsection {*Hilbert's Epsilon-operator*}

text{*Easier to apply than @{text someI} if the witness comes from an
existential formula*}
lemma someI_ex [elim?]: "\<exists>x. P x ==> P (SOME x. P x)"
apply (erule exE)
apply (erule someI)
done

text{*Easier to apply than @{text someI} because the conclusion has only one
occurrence of @{term P}.*}
lemma someI2: "[| P a;  !!x. P x ==> Q x |] ==> Q (SOME x. P x)"
by (blast intro: someI)

text{*Easier to apply than @{text someI2} if the witness comes from an
existential formula*}
lemma someI2_ex: "[| \<exists>a. P a; !!x. P x ==> Q x |] ==> Q (SOME x. P x)"
by (blast intro: someI2)

lemma some_equality [intro]:
     "[| P a;  !!x. P x ==> x=a |] ==> (SOME x. P x) = a"
by (blast intro: someI2)

lemma some1_equality: "[| EX!x. P x; P a |] ==> (SOME x. P x) = a"
by blast

lemma some_eq_ex: "P (SOME x. P x) =  (\<exists>x. P x)"
by (blast intro: someI)

lemma some_eq_trivial [simp]: "(SOME y. y=x) = x"
apply (rule some_equality)
apply (rule refl, assumption)
done

lemma some_sym_eq_trivial [simp]: "(SOME y. x=y) = x"
apply (rule some_equality)
apply (rule refl)
apply (erule sym)
done


subsection{*Axiom of Choice, Proved Using the Description Operator*}

lemma choice: "\<forall>x. \<exists>y. Q x y ==> \<exists>f. \<forall>x. Q x (f x)"
by (fast elim: someI)

lemma bchoice: "\<forall>x\<in>S. \<exists>y. Q x y ==> \<exists>f. \<forall>x\<in>S. Q x (f x)"
by (fast elim: someI)


subsection {*Function Inverse*}

lemma inv_def: "inv f = (%y. SOME x. f x = y)"
by(simp add: inv_into_def)

lemma inv_into_into: "x : f ` A ==> inv_into A f x : A"
apply (simp add: inv_into_def)
apply (fast intro: someI2)
done

lemma inv_id [simp]: "inv id = id"
by (simp add: inv_into_def id_def)

lemma inv_into_f_f [simp]:
  "[| inj_on f A;  x : A |] ==> inv_into A f (f x) = x"
apply (simp add: inv_into_def inj_on_def)
apply (blast intro: someI2)
done

lemma inv_f_f: "inj f ==> inv f (f x) = x"
by simp

lemma f_inv_into_f: "y : f`A  ==> f (inv_into A f y) = y"
apply (simp add: inv_into_def)
apply (fast intro: someI2)
done

lemma inv_into_f_eq: "[| inj_on f A; x : A; f x = y |] ==> inv_into A f y = x"
apply (erule subst)
apply (fast intro: inv_into_f_f)
done

lemma inv_f_eq: "[| inj f; f x = y |] ==> inv f y = x"
by (simp add:inv_into_f_eq)

lemma inj_imp_inv_eq: "[| inj f; ALL x. f(g x) = x |] ==> inv f = g"
  by (blast intro: inv_into_f_eq)

text{*But is it useful?*}
lemma inj_transfer:
  assumes injf: "inj f" and minor: "!!y. y \<in> range(f) ==> P(inv f y)"
  shows "P x"
proof -
  have "f x \<in> range f" by auto
  hence "P(inv f (f x))" by (rule minor)
  thus "P x" by (simp add: inv_into_f_f [OF injf])
qed

lemma inj_iff: "(inj f) = (inv f o f = id)"
apply (simp add: o_def fun_eq_iff)
apply (blast intro: inj_on_inverseI inv_into_f_f)
done

lemma inv_o_cancel[simp]: "inj f ==> inv f o f = id"
by (simp add: inj_iff)

lemma o_inv_o_cancel[simp]: "inj f ==> g o inv f o f = g"
by (simp add: o_assoc[symmetric])

lemma inv_into_image_cancel[simp]:
  "inj_on f A ==> S <= A ==> inv_into A f ` f ` S = S"
by(fastforce simp: image_def)

lemma inj_imp_surj_inv: "inj f ==> surj (inv f)"
by (blast intro!: surjI inv_into_f_f)

lemma surj_f_inv_f: "surj f ==> f(inv f y) = y"
by (simp add: f_inv_into_f)

lemma inv_into_injective:
  assumes eq: "inv_into A f x = inv_into A f y"
      and x: "x: f`A"
      and y: "y: f`A"
  shows "x=y"
proof -
  have "f (inv_into A f x) = f (inv_into A f y)" using eq by simp
  thus ?thesis by (simp add: f_inv_into_f x y)
qed

lemma inj_on_inv_into: "B <= f`A ==> inj_on (inv_into A f) B"
by (blast intro: inj_onI dest: inv_into_injective injD)

lemma bij_betw_inv_into: "bij_betw f A B ==> bij_betw (inv_into A f) B A"
by (auto simp add: bij_betw_def inj_on_inv_into)

lemma surj_imp_inj_inv: "surj f ==> inj (inv f)"
by (simp add: inj_on_inv_into)

lemma surj_iff: "(surj f) = (f o inv f = id)"
by (auto intro!: surjI simp: surj_f_inv_f fun_eq_iff[where 'b='a])

lemma surj_iff_all: "surj f \<longleftrightarrow> (\<forall>x. f (inv f x) = x)"
  unfolding surj_iff by (simp add: o_def fun_eq_iff)

lemma surj_imp_inv_eq: "[| surj f; \<forall>x. g(f x) = x |] ==> inv f = g"
apply (rule ext)
apply (drule_tac x = "inv f x" in spec)
apply (simp add: surj_f_inv_f)
done

lemma bij_imp_bij_inv: "bij f ==> bij (inv f)"
by (simp add: bij_def inj_imp_surj_inv surj_imp_inj_inv)

lemma inv_equality: "[| !!x. g (f x) = x;  !!y. f (g y) = y |] ==> inv f = g"
apply (rule ext)
apply (auto simp add: inv_into_def)
done

lemma inv_inv_eq: "bij f ==> inv (inv f) = f"
apply (rule inv_equality)
apply (auto simp add: bij_def surj_f_inv_f)
done

(** bij(inv f) implies little about f.  Consider f::bool=>bool such that
    f(True)=f(False)=True.  Then it's consistent with axiom someI that
    inv f could be any function at all, including the identity function.
    If inv f=id then inv f is a bijection, but inj f, surj(f) and
    inv(inv f)=f all fail.
**)

lemma inv_into_comp:
  "[| inj_on f (g ` A); inj_on g A; x : f ` g ` A |] ==>
  inv_into A (f o g) x = (inv_into A g o inv_into (g ` A) f) x"
apply (rule inv_into_f_eq)
  apply (fast intro: comp_inj_on)
 apply (simp add: inv_into_into)
apply (simp add: f_inv_into_f inv_into_into)
done

lemma o_inv_distrib: "[| bij f; bij g |] ==> inv (f o g) = inv g o inv f"
apply (rule inv_equality)
apply (auto simp add: bij_def surj_f_inv_f)
done

lemma image_surj_f_inv_f: "surj f ==> f ` (inv f ` A) = A"
by (simp add: image_eq_UN surj_f_inv_f)

lemma image_inv_f_f: "inj f ==> (inv f) ` (f ` A) = A"
by (simp add: image_eq_UN)

lemma inv_image_comp: "inj f ==> inv f ` (f`X) = X"
by (auto simp add: image_def)

lemma bij_image_Collect_eq: "bij f ==> f ` Collect P = {y. P (inv f y)}"
apply auto
apply (force simp add: bij_is_inj)
apply (blast intro: bij_is_surj [THEN surj_f_inv_f, symmetric])
done

lemma bij_vimage_eq_inv_image: "bij f ==> f -` A = inv f ` A" 
apply (auto simp add: bij_is_surj [THEN surj_f_inv_f])
apply (blast intro: bij_is_inj [THEN inv_into_f_f, symmetric])
done

lemma finite_fun_UNIVD1:
  assumes fin: "finite (UNIV :: ('a \<Rightarrow> 'b) set)"
  and card: "card (UNIV :: 'b set) \<noteq> Suc 0"
  shows "finite (UNIV :: 'a set)"
proof -
  from fin have finb: "finite (UNIV :: 'b set)" by (rule finite_fun_UNIVD2)
  with card have "card (UNIV :: 'b set) \<ge> Suc (Suc 0)"
    by (cases "card (UNIV :: 'b set)") (auto simp add: card_eq_0_iff)
  then obtain n where "card (UNIV :: 'b set) = Suc (Suc n)" "n = card (UNIV :: 'b set) - Suc (Suc 0)" by auto
  then obtain b1 b2 where b1b2: "(b1 :: 'b) \<noteq> (b2 :: 'b)" by (auto simp add: card_Suc_eq)
  from fin have "finite (range (\<lambda>f :: 'a \<Rightarrow> 'b. inv f b1))" by (rule finite_imageI)
  moreover have "UNIV = range (\<lambda>f :: 'a \<Rightarrow> 'b. inv f b1)"
  proof (rule UNIV_eq_I)
    fix x :: 'a
    from b1b2 have "x = inv (\<lambda>y. if y = x then b1 else b2) b1" by (simp add: inv_into_def)
    thus "x \<in> range (\<lambda>f\<Colon>'a \<Rightarrow> 'b. inv f b1)" by blast
  qed
  ultimately show "finite (UNIV :: 'a set)" by simp
qed

lemma image_inv_into_cancel:
  assumes SURJ: "f`A=A'" and SUB: "B' \<le> A'"
  shows "f `((inv_into A f)`B') = B'"
  using assms
proof (auto simp add: f_inv_into_f)
  let ?f' = "(inv_into A f)"
  fix a' assume *: "a' \<in> B'"
  then have "a' \<in> A'" using SUB by auto
  then have "a' = f (?f' a')"
    using SURJ by (auto simp add: f_inv_into_f)
  then show "a' \<in> f ` (?f' ` B')" using * by blast
qed

lemma inv_into_inv_into_eq:
  assumes "bij_betw f A A'" "a \<in> A"
  shows "inv_into A' (inv_into A f) a = f a"
proof -
  let ?f' = "inv_into A f"   let ?f'' = "inv_into A' ?f'"
  have 1: "bij_betw ?f' A' A" using assms
  by (auto simp add: bij_betw_inv_into)
  obtain a' where 2: "a' \<in> A'" and 3: "?f' a' = a"
    using 1 `a \<in> A` unfolding bij_betw_def by force
  hence "?f'' a = a'"
    using `a \<in> A` 1 3 by (auto simp add: f_inv_into_f bij_betw_def)
  moreover have "f a = a'" using assms 2 3
    by (auto simp add: bij_betw_def)
  ultimately show "?f'' a = f a" by simp
qed

lemma inj_on_iff_surj:
  assumes "A \<noteq> {}"
  shows "(\<exists>f. inj_on f A \<and> f ` A \<le> A') \<longleftrightarrow> (\<exists>g. g ` A' = A)"
proof safe
  fix f assume INJ: "inj_on f A" and INCL: "f ` A \<le> A'"
  let ?phi = "\<lambda>a' a. a \<in> A \<and> f a = a'"  let ?csi = "\<lambda>a. a \<in> A"
  let ?g = "\<lambda>a'. if a' \<in> f ` A then (SOME a. ?phi a' a) else (SOME a. ?csi a)"
  have "?g ` A' = A"
  proof
    show "?g ` A' \<le> A"
    proof clarify
      fix a' assume *: "a' \<in> A'"
      show "?g a' \<in> A"
      proof cases
        assume Case1: "a' \<in> f ` A"
        then obtain a where "?phi a' a" by blast
        hence "?phi a' (SOME a. ?phi a' a)" using someI[of "?phi a'" a] by blast
        with Case1 show ?thesis by auto
      next
        assume Case2: "a' \<notin> f ` A"
        hence "?csi (SOME a. ?csi a)" using assms someI_ex[of ?csi] by blast
        with Case2 show ?thesis by auto
      qed
    qed
  next
    show "A \<le> ?g ` A'"
    proof-
      {fix a assume *: "a \<in> A"
       let ?b = "SOME aa. ?phi (f a) aa"
       have "?phi (f a) a" using * by auto
       hence 1: "?phi (f a) ?b" using someI[of "?phi(f a)" a] by blast
       hence "?g(f a) = ?b" using * by auto
       moreover have "a = ?b" using 1 INJ * by (auto simp add: inj_on_def)
       ultimately have "?g(f a) = a" by simp
       with INCL * have "?g(f a) = a \<and> f a \<in> A'" by auto
      }
      thus ?thesis by force
    qed
  qed
  thus "\<exists>g. g ` A' = A" by blast
next
  fix g  let ?f = "inv_into A' g"
  have "inj_on ?f (g ` A')"
    by (auto simp add: inj_on_inv_into)
  moreover
  {fix a' assume *: "a' \<in> A'"
   let ?phi = "\<lambda> b'. b' \<in> A' \<and> g b' = g a'"
   have "?phi a'" using * by auto
   hence "?phi(SOME b'. ?phi b')" using someI[of ?phi] by blast
   hence "?f(g a') \<in> A'" unfolding inv_into_def by auto
  }
  ultimately show "\<exists>f. inj_on f (g ` A') \<and> f ` g ` A' \<subseteq> A'" by auto
qed

lemma Ex_inj_on_UNION_Sigma:
  "\<exists>f. (inj_on f (\<Union> i \<in> I. A i) \<and> f ` (\<Union> i \<in> I. A i) \<le> (SIGMA i : I. A i))"
proof
  let ?phi = "\<lambda> a i. i \<in> I \<and> a \<in> A i"
  let ?sm = "\<lambda> a. SOME i. ?phi a i"
  let ?f = "\<lambda>a. (?sm a, a)"
  have "inj_on ?f (\<Union> i \<in> I. A i)" unfolding inj_on_def by auto
  moreover
  { { fix i a assume "i \<in> I" and "a \<in> A i"
      hence "?sm a \<in> I \<and> a \<in> A(?sm a)" using someI[of "?phi a" i] by auto
    }
    hence "?f ` (\<Union> i \<in> I. A i) \<le> (SIGMA i : I. A i)" by auto
  }
  ultimately
  show "inj_on ?f (\<Union> i \<in> I. A i) \<and> ?f ` (\<Union> i \<in> I. A i) \<le> (SIGMA i : I. A i)"
  by auto
qed

subsection {* The Cantor-Bernstein Theorem *}

lemma Cantor_Bernstein_aux:
  shows "\<exists>A' h. A' \<le> A \<and>
                (\<forall>a \<in> A'. a \<notin> g`(B - f ` A')) \<and>
                (\<forall>a \<in> A'. h a = f a) \<and>
                (\<forall>a \<in> A - A'. h a \<in> B - (f ` A') \<and> a = g(h a))"
proof-
  obtain H where H_def: "H = (\<lambda> A'. A - (g`(B - (f ` A'))))" by blast
  have 0: "mono H" unfolding mono_def H_def by blast
  then obtain A' where 1: "H A' = A'" using lfp_unfold by blast
  hence 2: "A' = A - (g`(B - (f ` A')))" unfolding H_def by simp
  hence 3: "A' \<le> A" by blast
  have 4: "\<forall>a \<in> A'.  a \<notin> g`(B - f ` A')"
  using 2 by blast
  have 5: "\<forall>a \<in> A - A'. \<exists>b \<in> B - (f ` A'). a = g b"
  using 2 by blast
  (*  *)
  obtain h where h_def:
  "h = (\<lambda> a. if a \<in> A' then f a else (SOME b. b \<in> B - (f ` A') \<and> a = g b))" by blast
  hence "\<forall>a \<in> A'. h a = f a" by auto
  moreover
  have "\<forall>a \<in> A - A'. h a \<in> B - (f ` A') \<and> a = g(h a)"
  proof
    fix a assume *: "a \<in> A - A'"
    let ?phi = "\<lambda> b. b \<in> B - (f ` A') \<and> a = g b"
    have "h a = (SOME b. ?phi b)" using h_def * by auto
    moreover have "\<exists>b. ?phi b" using 5 *  by auto
    ultimately show  "?phi (h a)" using someI_ex[of ?phi] by auto
  qed
  ultimately show ?thesis using 3 4 by blast
qed

theorem Cantor_Bernstein:
  assumes INJ1: "inj_on f A" and SUB1: "f ` A \<le> B" and
          INJ2: "inj_on g B" and SUB2: "g ` B \<le> A"
  shows "\<exists>h. bij_betw h A B"
proof-
  obtain A' and h where 0: "A' \<le> A" and
  1: "\<forall>a \<in> A'. a \<notin> g`(B - f ` A')" and
  2: "\<forall>a \<in> A'. h a = f a" and
  3: "\<forall>a \<in> A - A'. h a \<in> B - (f ` A') \<and> a = g(h a)"
  using Cantor_Bernstein_aux[of A g B f] by blast
  have "inj_on h A"
  proof (intro inj_onI)
    fix a1 a2
    assume 4: "a1 \<in> A" and 5: "a2 \<in> A" and 6: "h a1 = h a2"
    show "a1 = a2"
    proof(cases "a1 \<in> A'")
      assume Case1: "a1 \<in> A'"
      show ?thesis
      proof(cases "a2 \<in> A'")
        assume Case11: "a2 \<in> A'"
        hence "f a1 = f a2" using Case1 2 6 by auto
        thus ?thesis using INJ1 Case1 Case11 0
        unfolding inj_on_def by blast
      next
        assume Case12: "a2 \<notin> A'"
        hence False using 3 5 2 6 Case1 by force
        thus ?thesis by simp
      qed
    next
    assume Case2: "a1 \<notin> A'"
      show ?thesis
      proof(cases "a2 \<in> A'")
        assume Case21: "a2 \<in> A'"
        hence False using 3 4 2 6 Case2 by auto
        thus ?thesis by simp
      next
        assume Case22: "a2 \<notin> A'"
        hence "a1 = g(h a1) \<and> a2 = g(h a2)" using Case2 4 5 3 by auto
        thus ?thesis using 6 by simp
      qed
    qed
  qed
  (*  *)
  moreover
  have "h ` A = B"
  proof safe
    fix a assume "a \<in> A"
    thus "h a \<in> B" using SUB1 2 3 by (case_tac "a \<in> A'", auto)
  next
    fix b assume *: "b \<in> B"
    show "b \<in> h ` A"
    proof(cases "b \<in> f ` A'")
      assume Case1: "b \<in> f ` A'"
      then obtain a where "a \<in> A' \<and> b = f a" by blast
      thus ?thesis using 2 0 by force
    next
      assume Case2: "b \<notin> f ` A'"
      hence "g b \<notin> A'" using 1 * by auto
      hence 4: "g b \<in> A - A'" using * SUB2 by auto
      hence "h(g b) \<in> B \<and> g(h(g b)) = g b"
      using 3 by auto
      hence "h(g b) = b" using * INJ2 unfolding inj_on_def by auto
      thus ?thesis using 4 by force
    qed
  qed
  (*  *)
  ultimately show ?thesis unfolding bij_betw_def by auto
qed

subsection {*Other Consequences of Hilbert's Epsilon*}

text {*Hilbert's Epsilon and the @{term split} Operator*}

text{*Looping simprule*}
lemma split_paired_Eps: "(SOME x. P x) = (SOME (a,b). P(a,b))"
  by simp

lemma Eps_split: "Eps (split P) = (SOME xy. P (fst xy) (snd xy))"
  by (simp add: split_def)

lemma Eps_split_eq [simp]: "(@(x',y'). x = x' & y = y') = (x,y)"
  by blast


text{*A relation is wellfounded iff it has no infinite descending chain*}
lemma wf_iff_no_infinite_down_chain:
  "wf r = (~(\<exists>f. \<forall>i. (f(Suc i),f i) \<in> r))"
apply (simp only: wf_eq_minimal)
apply (rule iffI)
 apply (rule notI)
 apply (erule exE)
 apply (erule_tac x = "{w. \<exists>i. w=f i}" in allE, blast)
apply (erule contrapos_np, simp, clarify)
apply (subgoal_tac "\<forall>n. nat_rec x (%i y. @z. z:Q & (z,y) :r) n \<in> Q")
 apply (rule_tac x = "nat_rec x (%i y. @z. z:Q & (z,y) :r)" in exI)
 apply (rule allI, simp)
 apply (rule someI2_ex, blast, blast)
apply (rule allI)
apply (induct_tac "n", simp_all)
apply (rule someI2_ex, blast+)
done

lemma wf_no_infinite_down_chainE:
  assumes "wf r" obtains k where "(f (Suc k), f k) \<notin> r"
using `wf r` wf_iff_no_infinite_down_chain[of r] by blast


text{*A dynamically-scoped fact for TFL *}
lemma tfl_some: "\<forall>P x. P x --> P (Eps P)"
  by (blast intro: someI)


subsection {* Least value operator *}

definition
  LeastM :: "['a => 'b::ord, 'a => bool] => 'a" where
  "LeastM m P == SOME x. P x & (\<forall>y. P y --> m x <= m y)"

syntax
  "_LeastM" :: "[pttrn, 'a => 'b::ord, bool] => 'a"    ("LEAST _ WRT _. _" [0, 4, 10] 10)
translations
  "LEAST x WRT m. P" == "CONST LeastM m (%x. P)"

lemma LeastMI2:
  "P x ==> (!!y. P y ==> m x <= m y)
    ==> (!!x. P x ==> \<forall>y. P y --> m x \<le> m y ==> Q x)
    ==> Q (LeastM m P)"
  apply (simp add: LeastM_def)
  apply (rule someI2_ex, blast, blast)
  done

lemma LeastM_equality:
  "P k ==> (!!x. P x ==> m k <= m x)
    ==> m (LEAST x WRT m. P x) = (m k::'a::order)"
  apply (rule LeastMI2, assumption, blast)
  apply (blast intro!: order_antisym)
  done

lemma wf_linord_ex_has_least:
  "wf r ==> \<forall>x y. ((x,y):r^+) = ((y,x)~:r^*) ==> P k
    ==> \<exists>x. P x & (!y. P y --> (m x,m y):r^*)"
  apply (drule wf_trancl [THEN wf_eq_minimal [THEN iffD1]])
  apply (drule_tac x = "m`Collect P" in spec, force)
  done

lemma ex_has_least_nat:
    "P k ==> \<exists>x. P x & (\<forall>y. P y --> m x <= (m y::nat))"
  apply (simp only: pred_nat_trancl_eq_le [symmetric])
  apply (rule wf_pred_nat [THEN wf_linord_ex_has_least])
   apply (simp add: less_eq linorder_not_le pred_nat_trancl_eq_le, assumption)
  done

lemma LeastM_nat_lemma:
    "P k ==> P (LeastM m P) & (\<forall>y. P y --> m (LeastM m P) <= (m y::nat))"
  apply (simp add: LeastM_def)
  apply (rule someI_ex)
  apply (erule ex_has_least_nat)
  done

lemmas LeastM_natI = LeastM_nat_lemma [THEN conjunct1]

lemma LeastM_nat_le: "P x ==> m (LeastM m P) <= (m x::nat)"
by (rule LeastM_nat_lemma [THEN conjunct2, THEN spec, THEN mp], assumption, assumption)


subsection {* Greatest value operator *}

definition
  GreatestM :: "['a => 'b::ord, 'a => bool] => 'a" where
  "GreatestM m P == SOME x. P x & (\<forall>y. P y --> m y <= m x)"

definition
  Greatest :: "('a::ord => bool) => 'a" (binder "GREATEST " 10) where
  "Greatest == GreatestM (%x. x)"

syntax
  "_GreatestM" :: "[pttrn, 'a => 'b::ord, bool] => 'a"
      ("GREATEST _ WRT _. _" [0, 4, 10] 10)
translations
  "GREATEST x WRT m. P" == "CONST GreatestM m (%x. P)"

lemma GreatestMI2:
  "P x ==> (!!y. P y ==> m y <= m x)
    ==> (!!x. P x ==> \<forall>y. P y --> m y \<le> m x ==> Q x)
    ==> Q (GreatestM m P)"
  apply (simp add: GreatestM_def)
  apply (rule someI2_ex, blast, blast)
  done

lemma GreatestM_equality:
 "P k ==> (!!x. P x ==> m x <= m k)
    ==> m (GREATEST x WRT m. P x) = (m k::'a::order)"
  apply (rule_tac m = m in GreatestMI2, assumption, blast)
  apply (blast intro!: order_antisym)
  done

lemma Greatest_equality:
  "P (k::'a::order) ==> (!!x. P x ==> x <= k) ==> (GREATEST x. P x) = k"
  apply (simp add: Greatest_def)
  apply (erule GreatestM_equality, blast)
  done

lemma ex_has_greatest_nat_lemma:
  "P k ==> \<forall>x. P x --> (\<exists>y. P y & ~ ((m y::nat) <= m x))
    ==> \<exists>y. P y & ~ (m y < m k + n)"
  apply (induct n, force)
  apply (force simp add: le_Suc_eq)
  done

lemma ex_has_greatest_nat:
  "P k ==> \<forall>y. P y --> m y < b
    ==> \<exists>x. P x & (\<forall>y. P y --> (m y::nat) <= m x)"
  apply (rule ccontr)
  apply (cut_tac P = P and n = "b - m k" in ex_has_greatest_nat_lemma)
    apply (subgoal_tac [3] "m k <= b", auto)
  done

lemma GreatestM_nat_lemma:
  "P k ==> \<forall>y. P y --> m y < b
    ==> P (GreatestM m P) & (\<forall>y. P y --> (m y::nat) <= m (GreatestM m P))"
  apply (simp add: GreatestM_def)
  apply (rule someI_ex)
  apply (erule ex_has_greatest_nat, assumption)
  done

lemmas GreatestM_natI = GreatestM_nat_lemma [THEN conjunct1]

lemma GreatestM_nat_le:
  "P x ==> \<forall>y. P y --> m y < b
    ==> (m x::nat) <= m (GreatestM m P)"
  apply (blast dest: GreatestM_nat_lemma [THEN conjunct2, THEN spec, of P])
  done


text {* \medskip Specialization to @{text GREATEST}. *}

lemma GreatestI: "P (k::nat) ==> \<forall>y. P y --> y < b ==> P (GREATEST x. P x)"
  apply (simp add: Greatest_def)
  apply (rule GreatestM_natI, auto)
  done

lemma Greatest_le:
    "P x ==> \<forall>y. P y --> y < b ==> (x::nat) <= (GREATEST x. P x)"
  apply (simp add: Greatest_def)
  apply (rule GreatestM_nat_le, auto)
  done


subsection {* Specification package -- Hilbertized version *}

lemma exE_some: "[| Ex P ; c == Eps P |] ==> P c"
  by (simp only: someI_ex)

use "Tools/choice_specification.ML"

end
