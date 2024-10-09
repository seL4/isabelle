(*  Title:      HOL/Nonstandard_Analysis/StarDef.thy
    Author:     Jacques D. Fleuriot and Brian Huffman
*)

section \<open>Construction of Star Types Using Ultrafilters\<close>

theory StarDef
  imports Free_Ultrafilter
begin

subsection \<open>A Free Ultrafilter over the Naturals\<close>

definition FreeUltrafilterNat :: "nat filter"  (\<open>\<U>\<close>)
  where "\<U> = (SOME U. freeultrafilter U)"

lemma freeultrafilter_FreeUltrafilterNat: "freeultrafilter \<U>"
  unfolding FreeUltrafilterNat_def
  by (simp add: freeultrafilter_Ex someI_ex)

interpretation FreeUltrafilterNat: freeultrafilter \<U>
  by (rule freeultrafilter_FreeUltrafilterNat)


subsection \<open>Definition of \<open>star\<close> type constructor\<close>

definition starrel :: "((nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)) set"
  where "starrel = {(X, Y). eventually (\<lambda>n. X n = Y n) \<U>}"

definition "star = (UNIV :: (nat \<Rightarrow> 'a) set) // starrel"

typedef 'a star = "star :: (nat \<Rightarrow> 'a) set set"
  by (auto simp: star_def intro: quotientI)

definition star_n :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a star"
  where "star_n X = Abs_star (starrel `` {X})"

theorem star_cases [case_names star_n, cases type: star]:
  obtains X where "x = star_n X"
  by (cases x) (auto simp: star_n_def star_def elim: quotientE)

lemma all_star_eq: "(\<forall>x. P x) \<longleftrightarrow> (\<forall>X. P (star_n X))"
  by (metis star_cases)

lemma ex_star_eq: "(\<exists>x. P x) \<longleftrightarrow> (\<exists>X. P (star_n X))"
  by (metis star_cases)

text \<open>Proving that \<^term>\<open>starrel\<close> is an equivalence relation.\<close>

lemma starrel_iff [iff]: "(X, Y) \<in> starrel \<longleftrightarrow> eventually (\<lambda>n. X n = Y n) \<U>"
  by (simp add: starrel_def)

lemma equiv_starrel: "equiv UNIV starrel"
proof (rule equivI)
  show "refl starrel" by (simp add: refl_on_def)
  show "sym starrel" by (simp add: sym_def eq_commute)
  show "trans starrel" by (intro transI) (auto elim: eventually_elim2)
qed

lemmas equiv_starrel_iff = eq_equiv_class_iff [OF equiv_starrel UNIV_I UNIV_I]

lemma starrel_in_star: "starrel``{x} \<in> star"
  by (simp add: star_def quotientI)

lemma star_n_eq_iff: "star_n X = star_n Y \<longleftrightarrow> eventually (\<lambda>n. X n = Y n) \<U>"
  by (simp add: star_n_def Abs_star_inject starrel_in_star equiv_starrel_iff)


subsection \<open>Transfer principle\<close>

text \<open>This introduction rule starts each transfer proof.\<close>
lemma transfer_start: "P \<equiv> eventually (\<lambda>n. Q) \<U> \<Longrightarrow> Trueprop P \<equiv> Trueprop Q"
  by (simp add: FreeUltrafilterNat.proper)

text \<open>Standard principles that play a central role in the transfer tactic.\<close>
definition Ifun :: "('a \<Rightarrow> 'b) star \<Rightarrow> 'a star \<Rightarrow> 'b star"
    (\<open>(\<open>notation=\<open>infix \<star>\<close>\<close>_ \<star>/ _)\<close> [300, 301] 300)
  where "Ifun f \<equiv>
    \<lambda>x. Abs_star (\<Union>F\<in>Rep_star f. \<Union>X\<in>Rep_star x. starrel``{\<lambda>n. F n (X n)})"

lemma Ifun_congruent2: "congruent2 starrel starrel (\<lambda>F X. starrel``{\<lambda>n. F n (X n)})"
  by (auto simp add: congruent2_def equiv_starrel_iff elim!: eventually_rev_mp)

lemma Ifun_star_n: "star_n F \<star> star_n X = star_n (\<lambda>n. F n (X n))"
  by (simp add: Ifun_def star_n_def Abs_star_inverse starrel_in_star
      UN_equiv_class2 [OF equiv_starrel equiv_starrel Ifun_congruent2])

lemma transfer_Ifun: "f \<equiv> star_n F \<Longrightarrow> x \<equiv> star_n X \<Longrightarrow> f \<star> x \<equiv> star_n (\<lambda>n. F n (X n))"
  by (simp only: Ifun_star_n)

definition star_of :: "'a \<Rightarrow> 'a star"
  where "star_of x \<equiv> star_n (\<lambda>n. x)"

text \<open>Initialize transfer tactic.\<close>
ML_file \<open>transfer_principle.ML\<close>

method_setup transfer =
  \<open>Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD' (Transfer_Principle.transfer_tac ctxt ths))\<close>
  "transfer principle"


text \<open>Transfer introduction rules.\<close>

lemma transfer_ex [transfer_intro]:
  "(\<And>X. p (star_n X) \<equiv> eventually (\<lambda>n. P n (X n)) \<U>) \<Longrightarrow>
    \<exists>x::'a star. p x \<equiv> eventually (\<lambda>n. \<exists>x. P n x) \<U>"
  by (simp only: ex_star_eq eventually_ex)

lemma transfer_all [transfer_intro]:
  "(\<And>X. p (star_n X) \<equiv> eventually (\<lambda>n. P n (X n)) \<U>) \<Longrightarrow>
    \<forall>x::'a star. p x \<equiv> eventually (\<lambda>n. \<forall>x. P n x) \<U>"
  by (simp only: all_star_eq FreeUltrafilterNat.eventually_all_iff)

lemma transfer_not [transfer_intro]: "p \<equiv> eventually P \<U> \<Longrightarrow> \<not> p \<equiv> eventually (\<lambda>n. \<not> P n) \<U>"
  by (simp only: FreeUltrafilterNat.eventually_not_iff)

lemma transfer_conj [transfer_intro]:
  "p \<equiv> eventually P \<U> \<Longrightarrow> q \<equiv> eventually Q \<U> \<Longrightarrow> p \<and> q \<equiv> eventually (\<lambda>n. P n \<and> Q n) \<U>"
  by (simp only: eventually_conj_iff)

lemma transfer_disj [transfer_intro]:
  "p \<equiv> eventually P \<U> \<Longrightarrow> q \<equiv> eventually Q \<U> \<Longrightarrow> p \<or> q \<equiv> eventually (\<lambda>n. P n \<or> Q n) \<U>"
  by (simp only: FreeUltrafilterNat.eventually_disj_iff)

lemma transfer_imp [transfer_intro]:
  "p \<equiv> eventually P \<U> \<Longrightarrow> q \<equiv> eventually Q \<U> \<Longrightarrow> p \<longrightarrow> q \<equiv> eventually (\<lambda>n. P n \<longrightarrow> Q n) \<U>"
  by (simp only: FreeUltrafilterNat.eventually_imp_iff)

lemma transfer_iff [transfer_intro]:
  "p \<equiv> eventually P \<U> \<Longrightarrow> q \<equiv> eventually Q \<U> \<Longrightarrow> p = q \<equiv> eventually (\<lambda>n. P n = Q n) \<U>"
  by (simp only: FreeUltrafilterNat.eventually_iff_iff)

lemma transfer_if_bool [transfer_intro]:
  "p \<equiv> eventually P \<U> \<Longrightarrow> x \<equiv> eventually X \<U> \<Longrightarrow> y \<equiv> eventually Y \<U> \<Longrightarrow>
    (if p then x else y) \<equiv> eventually (\<lambda>n. if P n then X n else Y n) \<U>"
  by (simp only: if_bool_eq_conj transfer_conj transfer_imp transfer_not)

lemma transfer_eq [transfer_intro]:
  "x \<equiv> star_n X \<Longrightarrow> y \<equiv> star_n Y \<Longrightarrow> x = y \<equiv> eventually (\<lambda>n. X n = Y n) \<U>"
  by (simp only: star_n_eq_iff)

lemma transfer_if [transfer_intro]:
  "p \<equiv> eventually (\<lambda>n. P n) \<U> \<Longrightarrow> x \<equiv> star_n X \<Longrightarrow> y \<equiv> star_n Y \<Longrightarrow>
    (if p then x else y) \<equiv> star_n (\<lambda>n. if P n then X n else Y n)"
  by (rule eq_reflection) (auto simp: star_n_eq_iff transfer_not elim!: eventually_mono)

lemma transfer_fun_eq [transfer_intro]:
  "(\<And>X. f (star_n X) = g (star_n X) \<equiv> eventually (\<lambda>n. F n (X n) = G n (X n)) \<U>) \<Longrightarrow>
    f = g \<equiv> eventually (\<lambda>n. F n = G n) \<U>"
  by (simp only: fun_eq_iff transfer_all)

lemma transfer_star_n [transfer_intro]: "star_n X \<equiv> star_n (\<lambda>n. X n)"
  by (rule reflexive)

lemma transfer_bool [transfer_intro]: "p \<equiv> eventually (\<lambda>n. p) \<U>"
  by (simp add: FreeUltrafilterNat.proper)


subsection \<open>Standard elements\<close>

definition Standard :: "'a star set"
  where "Standard = range star_of"

text \<open>Transfer tactic should remove occurrences of \<^term>\<open>star_of\<close>.\<close>
setup \<open>Transfer_Principle.add_const \<^const_name>\<open>star_of\<close>\<close>

lemma star_of_inject: "star_of x = star_of y \<longleftrightarrow> x = y"
  by transfer (rule refl)

lemma Standard_star_of [simp]: "star_of x \<in> Standard"
  by (simp add: Standard_def)


subsection \<open>Internal functions\<close>

text \<open>Transfer tactic should remove occurrences of \<^term>\<open>Ifun\<close>.\<close>
setup \<open>Transfer_Principle.add_const \<^const_name>\<open>Ifun\<close>\<close>

lemma Ifun_star_of [simp]: "star_of f \<star> star_of x = star_of (f x)"
  by transfer (rule refl)

lemma Standard_Ifun [simp]: "f \<in> Standard \<Longrightarrow> x \<in> Standard \<Longrightarrow> f \<star> x \<in> Standard"
  by (auto simp add: Standard_def)


text \<open>Nonstandard extensions of functions.\<close>

definition starfun :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a star \<Rightarrow> 'b star"
    (\<open>(\<open>open_block notation=\<open>prefix starfun\<close>\<close>*f* _)\<close> [80] 80)
  where "starfun f \<equiv> \<lambda>x. star_of f \<star> x"

definition starfun2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a star \<Rightarrow> 'b star \<Rightarrow> 'c star"
    (\<open>(\<open>open_block notation=\<open>prefix starfun2\<close>\<close>*f2* _)\<close> [80] 80)
  where "starfun2 f \<equiv> \<lambda>x y. star_of f \<star> x \<star> y"

declare starfun_def [transfer_unfold]
declare starfun2_def [transfer_unfold]

lemma starfun_star_n: "( *f* f) (star_n X) = star_n (\<lambda>n. f (X n))"
  by (simp only: starfun_def star_of_def Ifun_star_n)

lemma starfun2_star_n: "( *f2* f) (star_n X) (star_n Y) = star_n (\<lambda>n. f (X n) (Y n))"
  by (simp only: starfun2_def star_of_def Ifun_star_n)

lemma starfun_star_of [simp]: "( *f* f) (star_of x) = star_of (f x)"
  by transfer (rule refl)

lemma starfun2_star_of [simp]: "( *f2* f) (star_of x) = *f* f x"
  by transfer (rule refl)

lemma Standard_starfun [simp]: "x \<in> Standard \<Longrightarrow> starfun f x \<in> Standard"
  by (simp add: starfun_def)

lemma Standard_starfun2 [simp]: "x \<in> Standard \<Longrightarrow> y \<in> Standard \<Longrightarrow> starfun2 f x y \<in> Standard"
  by (simp add: starfun2_def)

lemma Standard_starfun_iff:
  assumes inj: "\<And>x y. f x = f y \<Longrightarrow> x = y"
  shows "starfun f x \<in> Standard \<longleftrightarrow> x \<in> Standard"
proof
  assume "x \<in> Standard"
  then show "starfun f x \<in> Standard" by simp
next
  from inj have inj': "\<And>x y. starfun f x = starfun f y \<Longrightarrow> x = y"
    by transfer
  assume "starfun f x \<in> Standard"
  then obtain b where b: "starfun f x = star_of b"
    unfolding Standard_def ..
  then have "\<exists>x. starfun f x = star_of b" ..
  then have "\<exists>a. f a = b" by transfer
  then obtain a where "f a = b" ..
  then have "starfun f (star_of a) = star_of b" by transfer
  with b have "starfun f x = starfun f (star_of a)" by simp
  then have "x = star_of a" by (rule inj')
  then show "x \<in> Standard" by (simp add: Standard_def)
qed

lemma Standard_starfun2_iff:
  assumes inj: "\<And>a b a' b'. f a b = f a' b' \<Longrightarrow> a = a' \<and> b = b'"
  shows "starfun2 f x y \<in> Standard \<longleftrightarrow> x \<in> Standard \<and> y \<in> Standard"
proof
  assume "x \<in> Standard \<and> y \<in> Standard"
  then show "starfun2 f x y \<in> Standard" by simp
next
  have inj': "\<And>x y z w. starfun2 f x y = starfun2 f z w \<Longrightarrow> x = z \<and> y = w"
    using inj by transfer
  assume "starfun2 f x y \<in> Standard"
  then obtain c where c: "starfun2 f x y = star_of c"
    unfolding Standard_def ..
  then have "\<exists>x y. starfun2 f x y = star_of c" by auto
  then have "\<exists>a b. f a b = c" by transfer
  then obtain a b where "f a b = c" by auto
  then have "starfun2 f (star_of a) (star_of b) = star_of c" by transfer
  with c have "starfun2 f x y = starfun2 f (star_of a) (star_of b)" by simp
  then have "x = star_of a \<and> y = star_of b" by (rule inj')
  then show "x \<in> Standard \<and> y \<in> Standard" by (simp add: Standard_def)
qed


subsection \<open>Internal predicates\<close>

definition unstar :: "bool star \<Rightarrow> bool"
  where "unstar b \<longleftrightarrow> b = star_of True"

lemma unstar_star_n: "unstar (star_n P) \<longleftrightarrow> eventually P \<U>"
  by (simp add: unstar_def star_of_def star_n_eq_iff)

lemma unstar_star_of [simp]: "unstar (star_of p) = p"
  by (simp add: unstar_def star_of_inject)

text \<open>Transfer tactic should remove occurrences of \<^term>\<open>unstar\<close>.\<close>
setup \<open>Transfer_Principle.add_const \<^const_name>\<open>unstar\<close>\<close>

lemma transfer_unstar [transfer_intro]: "p \<equiv> star_n P \<Longrightarrow> unstar p \<equiv> eventually P \<U>"
  by (simp only: unstar_star_n)

definition starP :: "('a \<Rightarrow> bool) \<Rightarrow> 'a star \<Rightarrow> bool"
    (\<open>(\<open>open_block notation=\<open>prefix starP\<close>\<close>*p* _)\<close> [80] 80)
  where "*p* P = (\<lambda>x. unstar (star_of P \<star> x))"

definition starP2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a star \<Rightarrow> 'b star \<Rightarrow> bool"
    (\<open>(\<open>open_block notation=\<open>prefix starP2\<close>\<close>*p2* _)\<close> [80] 80)
  where "*p2* P = (\<lambda>x y. unstar (star_of P \<star> x \<star> y))"

declare starP_def [transfer_unfold]
declare starP2_def [transfer_unfold]

lemma starP_star_n: "( *p* P) (star_n X) = eventually (\<lambda>n. P (X n)) \<U>"
  by (simp only: starP_def star_of_def Ifun_star_n unstar_star_n)

lemma starP2_star_n: "( *p2* P) (star_n X) (star_n Y) = (eventually (\<lambda>n. P (X n) (Y n)) \<U>)"
  by (simp only: starP2_def star_of_def Ifun_star_n unstar_star_n)

lemma starP_star_of [simp]: "( *p* P) (star_of x) = P x"
  by transfer (rule refl)

lemma starP2_star_of [simp]: "( *p2* P) (star_of x) = *p* P x"
  by transfer (rule refl)


subsection \<open>Internal sets\<close>

definition Iset :: "'a set star \<Rightarrow> 'a star set"
  where "Iset A = {x. ( *p2* (\<in>)) x A}"

lemma Iset_star_n: "(star_n X \<in> Iset (star_n A)) = (eventually (\<lambda>n. X n \<in> A n) \<U>)"
  by (simp add: Iset_def starP2_star_n)

text \<open>Transfer tactic should remove occurrences of \<^term>\<open>Iset\<close>.\<close>
setup \<open>Transfer_Principle.add_const \<^const_name>\<open>Iset\<close>\<close>

lemma transfer_mem [transfer_intro]:
  "x \<equiv> star_n X \<Longrightarrow> a \<equiv> Iset (star_n A) \<Longrightarrow> x \<in> a \<equiv> eventually (\<lambda>n. X n \<in> A n) \<U>"
  by (simp only: Iset_star_n)

lemma transfer_Collect [transfer_intro]:
  "(\<And>X. p (star_n X) \<equiv> eventually (\<lambda>n. P n (X n)) \<U>) \<Longrightarrow>
    Collect p \<equiv> Iset (star_n (\<lambda>n. Collect (P n)))"
  by (simp add: atomize_eq set_eq_iff all_star_eq Iset_star_n)

lemma transfer_set_eq [transfer_intro]:
  "a \<equiv> Iset (star_n A) \<Longrightarrow> b \<equiv> Iset (star_n B) \<Longrightarrow> a = b \<equiv> eventually (\<lambda>n. A n = B n) \<U>"
  by (simp only: set_eq_iff transfer_all transfer_iff transfer_mem)

lemma transfer_ball [transfer_intro]:
  "a \<equiv> Iset (star_n A) \<Longrightarrow> (\<And>X. p (star_n X) \<equiv> eventually (\<lambda>n. P n (X n)) \<U>) \<Longrightarrow>
    \<forall>x\<in>a. p x \<equiv> eventually (\<lambda>n. \<forall>x\<in>A n. P n x) \<U>"
  by (simp only: Ball_def transfer_all transfer_imp transfer_mem)

lemma transfer_bex [transfer_intro]:
  "a \<equiv> Iset (star_n A) \<Longrightarrow> (\<And>X. p (star_n X) \<equiv> eventually (\<lambda>n. P n (X n)) \<U>) \<Longrightarrow>
    \<exists>x\<in>a. p x \<equiv> eventually (\<lambda>n. \<exists>x\<in>A n. P n x) \<U>"
  by (simp only: Bex_def transfer_ex transfer_conj transfer_mem)

lemma transfer_Iset [transfer_intro]: "a \<equiv> star_n A \<Longrightarrow> Iset a \<equiv> Iset (star_n (\<lambda>n. A n))"
  by simp


text \<open>Nonstandard extensions of sets.\<close>

definition starset :: "'a set \<Rightarrow> 'a star set"
    (\<open>(\<open>open_block notation=\<open>prefix starset\<close>\<close>*s* _)\<close> [80] 80)
  where "starset A = Iset (star_of A)"

declare starset_def [transfer_unfold]

lemma starset_mem: "star_of x \<in> *s* A \<longleftrightarrow> x \<in> A"
  by transfer (rule refl)

lemma starset_UNIV: "*s* (UNIV::'a set) = (UNIV::'a star set)"
  by (transfer UNIV_def) (rule refl)

lemma starset_empty: "*s* {} = {}"
  by (transfer empty_def) (rule refl)

lemma starset_insert: "*s* (insert x A) = insert (star_of x) ( *s* A)"
  by (transfer insert_def Un_def) (rule refl)

lemma starset_Un: "*s* (A \<union> B) = *s* A \<union> *s* B"
  by (transfer Un_def) (rule refl)

lemma starset_Int: "*s* (A \<inter> B) = *s* A \<inter> *s* B"
  by (transfer Int_def) (rule refl)

lemma starset_Compl: "*s* -A = -( *s* A)"
  by (transfer Compl_eq) (rule refl)

lemma starset_diff: "*s* (A - B) = *s* A - *s* B"
  by (transfer set_diff_eq) (rule refl)

lemma starset_image: "*s* (f ` A) = ( *f* f) ` ( *s* A)"
  by (transfer image_def) (rule refl)

lemma starset_vimage: "*s* (f -` A) = ( *f* f) -` ( *s* A)"
  by (transfer vimage_def) (rule refl)

lemma starset_subset: "( *s* A \<subseteq> *s* B) \<longleftrightarrow> A \<subseteq> B"
  by (transfer subset_eq) (rule refl)

lemma starset_eq: "( *s* A = *s* B) \<longleftrightarrow> A = B"
  by transfer (rule refl)

lemmas starset_simps [simp] =
  starset_mem     starset_UNIV
  starset_empty   starset_insert
  starset_Un      starset_Int
  starset_Compl   starset_diff
  starset_image   starset_vimage
  starset_subset  starset_eq


subsection \<open>Syntactic classes\<close>

instantiation star :: (zero) zero
begin
  definition star_zero_def: "0 \<equiv> star_of 0"
  instance ..
end

instantiation star :: (one) one
begin
  definition star_one_def: "1 \<equiv> star_of 1"
  instance ..
end

instantiation star :: (plus) plus
begin
  definition star_add_def: "(+) \<equiv> *f2* (+)"
  instance ..
end

instantiation star :: (times) times
begin
  definition star_mult_def: "((*)) \<equiv> *f2* ((*))"
  instance ..
end

instantiation star :: (uminus) uminus
begin
  definition star_minus_def: "uminus \<equiv> *f* uminus"
  instance ..
end

instantiation star :: (minus) minus
begin
  definition star_diff_def: "(-) \<equiv> *f2* (-)"
  instance ..
end

instantiation star :: (abs) abs
begin
  definition star_abs_def: "abs \<equiv> *f* abs"
  instance ..
end

instantiation star :: (sgn) sgn
begin
  definition star_sgn_def: "sgn \<equiv> *f* sgn"
  instance ..
end

instantiation star :: (divide) divide
begin
  definition star_divide_def:  "divide \<equiv> *f2* divide"
  instance ..
end

instantiation star :: (inverse) inverse
begin
  definition star_inverse_def: "inverse \<equiv> *f* inverse"
  instance ..
end

instance star :: (Rings.dvd) Rings.dvd ..

instantiation star :: (modulo) modulo
begin
  definition star_mod_def: "(mod) \<equiv> *f2* (mod)"
  instance ..
end

instantiation star :: (ord) ord
begin
  definition star_le_def: "(\<le>) \<equiv> *p2* (\<le>)"
  definition star_less_def: "(<) \<equiv> *p2* (<)"
  instance ..
end

lemmas star_class_defs [transfer_unfold] =
  star_zero_def     star_one_def
  star_add_def      star_diff_def     star_minus_def
  star_mult_def     star_divide_def   star_inverse_def
  star_le_def       star_less_def     star_abs_def       star_sgn_def
  star_mod_def


text \<open>Class operations preserve standard elements.\<close>

lemma Standard_zero: "0 \<in> Standard"
  by (simp add: star_zero_def)

lemma Standard_one: "1 \<in> Standard"
  by (simp add: star_one_def)

lemma Standard_add: "x \<in> Standard \<Longrightarrow> y \<in> Standard \<Longrightarrow> x + y \<in> Standard"
  by (simp add: star_add_def)

lemma Standard_diff: "x \<in> Standard \<Longrightarrow> y \<in> Standard \<Longrightarrow> x - y \<in> Standard"
  by (simp add: star_diff_def)

lemma Standard_minus: "x \<in> Standard \<Longrightarrow> - x \<in> Standard"
  by (simp add: star_minus_def)

lemma Standard_mult: "x \<in> Standard \<Longrightarrow> y \<in> Standard \<Longrightarrow> x * y \<in> Standard"
  by (simp add: star_mult_def)

lemma Standard_divide: "x \<in> Standard \<Longrightarrow> y \<in> Standard \<Longrightarrow> x / y \<in> Standard"
  by (simp add: star_divide_def)

lemma Standard_inverse: "x \<in> Standard \<Longrightarrow> inverse x \<in> Standard"
  by (simp add: star_inverse_def)

lemma Standard_abs: "x \<in> Standard \<Longrightarrow> \<bar>x\<bar> \<in> Standard"
  by (simp add: star_abs_def)

lemma Standard_mod: "x \<in> Standard \<Longrightarrow> y \<in> Standard \<Longrightarrow> x mod y \<in> Standard"
  by (simp add: star_mod_def)

lemmas Standard_simps [simp] =
  Standard_zero  Standard_one
  Standard_add   Standard_diff    Standard_minus
  Standard_mult  Standard_divide  Standard_inverse
  Standard_abs   Standard_mod


text \<open>\<^term>\<open>star_of\<close> preserves class operations.\<close>

lemma star_of_add: "star_of (x + y) = star_of x + star_of y"
  by transfer (rule refl)

lemma star_of_diff: "star_of (x - y) = star_of x - star_of y"
  by transfer (rule refl)

lemma star_of_minus: "star_of (-x) = - star_of x"
  by transfer (rule refl)

lemma star_of_mult: "star_of (x * y) = star_of x * star_of y"
  by transfer (rule refl)

lemma star_of_divide: "star_of (x / y) = star_of x / star_of y"
  by transfer (rule refl)

lemma star_of_inverse: "star_of (inverse x) = inverse (star_of x)"
  by transfer (rule refl)

lemma star_of_mod: "star_of (x mod y) = star_of x mod star_of y"
  by transfer (rule refl)

lemma star_of_abs: "star_of \<bar>x\<bar> = \<bar>star_of x\<bar>"
  by transfer (rule refl)


text \<open>\<^term>\<open>star_of\<close> preserves numerals.\<close>

lemma star_of_zero: "star_of 0 = 0"
  by transfer (rule refl)

lemma star_of_one: "star_of 1 = 1"
  by transfer (rule refl)


text \<open>\<^term>\<open>star_of\<close> preserves orderings.\<close>

lemma star_of_less: "(star_of x < star_of y) = (x < y)"
by transfer (rule refl)

lemma star_of_le: "(star_of x \<le> star_of y) = (x \<le> y)"
by transfer (rule refl)

lemma star_of_eq: "(star_of x = star_of y) = (x = y)"
by transfer (rule refl)


text \<open>As above, for \<open>0\<close>.\<close>

lemmas star_of_0_less = star_of_less [of 0, simplified star_of_zero]
lemmas star_of_0_le   = star_of_le   [of 0, simplified star_of_zero]
lemmas star_of_0_eq   = star_of_eq   [of 0, simplified star_of_zero]

lemmas star_of_less_0 = star_of_less [of _ 0, simplified star_of_zero]
lemmas star_of_le_0   = star_of_le   [of _ 0, simplified star_of_zero]
lemmas star_of_eq_0   = star_of_eq   [of _ 0, simplified star_of_zero]


text \<open>As above, for \<open>1\<close>.\<close>

lemmas star_of_1_less = star_of_less [of 1, simplified star_of_one]
lemmas star_of_1_le   = star_of_le   [of 1, simplified star_of_one]
lemmas star_of_1_eq   = star_of_eq   [of 1, simplified star_of_one]

lemmas star_of_less_1 = star_of_less [of _ 1, simplified star_of_one]
lemmas star_of_le_1   = star_of_le   [of _ 1, simplified star_of_one]
lemmas star_of_eq_1   = star_of_eq   [of _ 1, simplified star_of_one]

lemmas star_of_simps [simp] =
  star_of_add     star_of_diff    star_of_minus
  star_of_mult    star_of_divide  star_of_inverse
  star_of_mod     star_of_abs
  star_of_zero    star_of_one
  star_of_less    star_of_le      star_of_eq
  star_of_0_less  star_of_0_le    star_of_0_eq
  star_of_less_0  star_of_le_0    star_of_eq_0
  star_of_1_less  star_of_1_le    star_of_1_eq
  star_of_less_1  star_of_le_1    star_of_eq_1


subsection \<open>Ordering and lattice classes\<close>

instance star :: (order) order
proof 
  show "\<And>x y::'a star. (x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by transfer (rule less_le_not_le)
  show "\<And>x::'a star. x \<le> x"
    by transfer (rule order_refl)
  show "\<And>x y z::'a star. \<lbrakk>x \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> x \<le> z"
    by transfer (rule order_trans)
  show "\<And>x y::'a star. \<lbrakk>x \<le> y; y \<le> x\<rbrakk> \<Longrightarrow> x = y"
    by transfer (rule order_antisym)
qed

instantiation star :: (semilattice_inf) semilattice_inf
begin
  definition star_inf_def [transfer_unfold]: "inf \<equiv> *f2* inf"
  instance by (standard; transfer) auto
end

instantiation star :: (semilattice_sup) semilattice_sup
begin
  definition star_sup_def [transfer_unfold]: "sup \<equiv> *f2* sup"
  instance by (standard; transfer) auto
end

instance star :: (lattice) lattice ..

instance star :: (distrib_lattice) distrib_lattice
  by (standard; transfer) (auto simp add: sup_inf_distrib1)

lemma Standard_inf [simp]: "x \<in> Standard \<Longrightarrow> y \<in> Standard \<Longrightarrow> inf x y \<in> Standard"
  by (simp add: star_inf_def)

lemma Standard_sup [simp]: "x \<in> Standard \<Longrightarrow> y \<in> Standard \<Longrightarrow> sup x y \<in> Standard"
  by (simp add: star_sup_def)

lemma star_of_inf [simp]: "star_of (inf x y) = inf (star_of x) (star_of y)"
  by transfer (rule refl)

lemma star_of_sup [simp]: "star_of (sup x y) = sup (star_of x) (star_of y)"
  by transfer (rule refl)

instance star :: (linorder) linorder
  by (intro_classes, transfer, rule linorder_linear)

lemma star_max_def [transfer_unfold]: "max = *f2* max"
  unfolding max_def
  by (intro ext, transfer, simp)

lemma star_min_def [transfer_unfold]: "min = *f2* min"
  unfolding min_def
  by (intro ext, transfer, simp)

lemma Standard_max [simp]: "x \<in> Standard \<Longrightarrow> y \<in> Standard \<Longrightarrow> max x y \<in> Standard"
  by (simp add: star_max_def)

lemma Standard_min [simp]: "x \<in> Standard \<Longrightarrow> y \<in> Standard \<Longrightarrow> min x y \<in> Standard"
  by (simp add: star_min_def)

lemma star_of_max [simp]: "star_of (max x y) = max (star_of x) (star_of y)"
  by transfer (rule refl)

lemma star_of_min [simp]: "star_of (min x y) = min (star_of x) (star_of y)"
  by transfer (rule refl)


subsection \<open>Ordered group classes\<close>

instance star :: (semigroup_add) semigroup_add
  by (intro_classes, transfer, rule add.assoc)

instance star :: (ab_semigroup_add) ab_semigroup_add
  by (intro_classes, transfer, rule add.commute)

instance star :: (semigroup_mult) semigroup_mult
  by (intro_classes, transfer, rule mult.assoc)

instance star :: (ab_semigroup_mult) ab_semigroup_mult
  by (intro_classes, transfer, rule mult.commute)

instance star :: (comm_monoid_add) comm_monoid_add
  by (intro_classes, transfer, rule comm_monoid_add_class.add_0)

instance star :: (monoid_mult) monoid_mult
  apply intro_classes
   apply (transfer, rule mult_1_left)
  apply (transfer, rule mult_1_right)
  done

instance star :: (power) power ..

instance star :: (comm_monoid_mult) comm_monoid_mult
  by (intro_classes, transfer, rule mult_1)

instance star :: (cancel_semigroup_add) cancel_semigroup_add
  apply intro_classes
   apply (transfer, erule add_left_imp_eq)
  apply (transfer, erule add_right_imp_eq)
  done

instance star :: (cancel_ab_semigroup_add) cancel_ab_semigroup_add
  by intro_classes (transfer, simp add: diff_diff_eq)+

instance star :: (cancel_comm_monoid_add) cancel_comm_monoid_add ..

instance star :: (ab_group_add) ab_group_add
  apply intro_classes
   apply (transfer, rule left_minus)
  apply (transfer, rule diff_conv_add_uminus)
  done

instance star :: (ordered_ab_semigroup_add) ordered_ab_semigroup_add
  by (intro_classes, transfer, rule add_left_mono)

instance star :: (ordered_cancel_ab_semigroup_add) ordered_cancel_ab_semigroup_add ..

instance star :: (ordered_ab_semigroup_add_imp_le) ordered_ab_semigroup_add_imp_le
  by (intro_classes, transfer, rule add_le_imp_le_left)

instance star :: (ordered_comm_monoid_add) ordered_comm_monoid_add ..
instance star :: (ordered_ab_semigroup_monoid_add_imp_le) ordered_ab_semigroup_monoid_add_imp_le ..
instance star :: (ordered_cancel_comm_monoid_add) ordered_cancel_comm_monoid_add ..
instance star :: (ordered_ab_group_add) ordered_ab_group_add ..

instance star :: (ordered_ab_group_add_abs) ordered_ab_group_add_abs
  by intro_classes (transfer, simp add: abs_ge_self abs_leI abs_triangle_ineq)+

instance star :: (linordered_cancel_ab_semigroup_add) linordered_cancel_ab_semigroup_add ..


subsection \<open>Ring and field classes\<close>

instance star :: (semiring) semiring
  by (intro_classes; transfer) (fact distrib_right distrib_left)+

instance star :: (semiring_0) semiring_0
  by (intro_classes; transfer) simp_all

instance star :: (semiring_0_cancel) semiring_0_cancel ..

instance star :: (comm_semiring) comm_semiring
  by (intro_classes; transfer) (fact distrib_right)

instance star :: (comm_semiring_0) comm_semiring_0 ..
instance star :: (comm_semiring_0_cancel) comm_semiring_0_cancel ..

instance star :: (zero_neq_one) zero_neq_one
  by (intro_classes; transfer) (fact zero_neq_one)

instance star :: (semiring_1) semiring_1 ..
instance star :: (comm_semiring_1) comm_semiring_1 ..

declare dvd_def [transfer_refold]

instance star :: (comm_semiring_1_cancel) comm_semiring_1_cancel
  by (intro_classes; transfer) (fact right_diff_distrib')

instance star :: (semiring_no_zero_divisors) semiring_no_zero_divisors
  by (intro_classes; transfer) (fact no_zero_divisors)

instance star :: (semiring_1_no_zero_divisors) semiring_1_no_zero_divisors ..

instance star :: (semiring_no_zero_divisors_cancel) semiring_no_zero_divisors_cancel
  by (intro_classes; transfer) simp_all

instance star :: (semiring_1_cancel) semiring_1_cancel ..
instance star :: (ring) ring ..
instance star :: (comm_ring) comm_ring ..
instance star :: (ring_1) ring_1 ..
instance star :: (comm_ring_1) comm_ring_1 ..
instance star :: (semidom) semidom ..

instance star :: (semidom_divide) semidom_divide
  by (intro_classes; transfer) simp_all

instance star :: (ring_no_zero_divisors) ring_no_zero_divisors ..
instance star :: (ring_1_no_zero_divisors) ring_1_no_zero_divisors ..
instance star :: (idom) idom ..
instance star :: (idom_divide) idom_divide ..

instance star :: (divide_trivial) divide_trivial
  by (intro_classes; transfer) simp_all

instance star :: (division_ring) division_ring
  by (intro_classes; transfer) (simp_all add: divide_inverse)

instance star :: (field) field
  by (intro_classes; transfer) (simp_all add: divide_inverse)

instance star :: (ordered_semiring) ordered_semiring
  by (intro_classes; transfer) (fact mult_left_mono mult_right_mono)+

instance star :: (ordered_cancel_semiring) ordered_cancel_semiring ..

instance star :: (linordered_semiring_strict) linordered_semiring_strict
  by (intro_classes; transfer) (fact mult_strict_left_mono mult_strict_right_mono)+

instance star :: (ordered_comm_semiring) ordered_comm_semiring
  by (intro_classes; transfer) (fact mult_left_mono)

instance star :: (ordered_cancel_comm_semiring) ordered_cancel_comm_semiring ..

instance star :: (linordered_comm_semiring_strict) linordered_comm_semiring_strict
  by (intro_classes; transfer) (fact mult_strict_left_mono)

instance star :: (ordered_ring) ordered_ring ..

instance star :: (ordered_ring_abs) ordered_ring_abs
  by (intro_classes; transfer) (fact abs_eq_mult)

instance star :: (abs_if) abs_if
  by (intro_classes; transfer) (fact abs_if)

instance star :: (linordered_ring_strict) linordered_ring_strict ..
instance star :: (ordered_comm_ring) ordered_comm_ring ..

instance star :: (linordered_semidom) linordered_semidom
  by (intro_classes; transfer) (fact zero_less_one le_add_diff_inverse2)+

instance star :: (linordered_idom) linordered_idom
  by (intro_classes; transfer) (fact sgn_if)

instance star :: (linordered_field) linordered_field ..

instance star :: (algebraic_semidom) algebraic_semidom ..

instantiation star :: (normalization_semidom) normalization_semidom
begin

definition unit_factor_star :: "'a star \<Rightarrow> 'a star"
  where [transfer_unfold]: "unit_factor_star = *f* unit_factor"

definition normalize_star :: "'a star \<Rightarrow> 'a star"
  where [transfer_unfold]: "normalize_star = *f* normalize"

instance
  by standard (transfer; simp add: is_unit_unit_factor unit_factor_mult)+

end

instance star :: (semidom_modulo) semidom_modulo
  by standard (transfer; simp)



subsection \<open>Power\<close>

lemma star_power_def [transfer_unfold]: "(^) \<equiv> \<lambda>x n. ( *f* (\<lambda>x. x ^ n)) x"
proof (rule eq_reflection, rule ext, rule ext)
  show "x ^ n = ( *f* (\<lambda>x. x ^ n)) x" for n :: nat and x :: "'a star"
  proof (induct n arbitrary: x)
    case 0
    have "\<And>x::'a star. ( *f* (\<lambda>x. 1)) x = 1"
      by transfer simp
    then show ?case by simp
  next
    case (Suc n)
    have "\<And>x::'a star. x * ( *f* (\<lambda>x::'a. x ^ n)) x = ( *f* (\<lambda>x::'a. x * x ^ n)) x"
      by transfer simp
    with Suc show ?case by simp
  qed
qed

lemma Standard_power [simp]: "x \<in> Standard \<Longrightarrow> x ^ n \<in> Standard"
  by (simp add: star_power_def)

lemma star_of_power [simp]: "star_of (x ^ n) = star_of x ^ n"
  by transfer (rule refl)


subsection \<open>Number classes\<close>

instance star :: (numeral) numeral ..

lemma star_numeral_def [transfer_unfold]: "numeral k = star_of (numeral k)"
  by (induct k) (simp_all only: numeral.simps star_of_one star_of_add)

lemma Standard_numeral [simp]: "numeral k \<in> Standard"
  by (simp add: star_numeral_def)

lemma star_of_numeral [simp]: "star_of (numeral k) = numeral k"
  by transfer (rule refl)

lemma star_of_nat_def [transfer_unfold]: "of_nat n = star_of (of_nat n)"
  by (induct n) simp_all

lemmas star_of_compare_numeral [simp] =
  star_of_less [of "numeral k", simplified star_of_numeral]
  star_of_le   [of "numeral k", simplified star_of_numeral]
  star_of_eq   [of "numeral k", simplified star_of_numeral]
  star_of_less [of _ "numeral k", simplified star_of_numeral]
  star_of_le   [of _ "numeral k", simplified star_of_numeral]
  star_of_eq   [of _ "numeral k", simplified star_of_numeral]
  star_of_less [of "- numeral k", simplified star_of_numeral]
  star_of_le   [of "- numeral k", simplified star_of_numeral]
  star_of_eq   [of "- numeral k", simplified star_of_numeral]
  star_of_less [of _ "- numeral k", simplified star_of_numeral]
  star_of_le   [of _ "- numeral k", simplified star_of_numeral]
  star_of_eq   [of _ "- numeral k", simplified star_of_numeral] for k

lemma Standard_of_nat [simp]: "of_nat n \<in> Standard"
  by (simp add: star_of_nat_def)

lemma star_of_of_nat [simp]: "star_of (of_nat n) = of_nat n"
  by transfer (rule refl)

lemma star_of_int_def [transfer_unfold]: "of_int z = star_of (of_int z)"
  by (rule int_diff_cases [of z]) simp

lemma Standard_of_int [simp]: "of_int z \<in> Standard"
  by (simp add: star_of_int_def)

lemma star_of_of_int [simp]: "star_of (of_int z) = of_int z"
  by transfer (rule refl)

instance star :: (semiring_char_0) semiring_char_0
proof
  have "inj (star_of :: 'a \<Rightarrow> 'a star)"
    by (rule injI) simp
  then have "inj (star_of \<circ> of_nat :: nat \<Rightarrow> 'a star)"
    using inj_of_nat by (rule inj_compose)
  then show "inj (of_nat :: nat \<Rightarrow> 'a star)"
    by (simp add: comp_def)
qed

instance star :: (ring_char_0) ring_char_0 ..


subsection \<open>Finite class\<close>

lemma starset_finite: "finite A \<Longrightarrow> *s* A = star_of ` A"
  by (erule finite_induct) simp_all

instance star :: (finite) finite
proof intro_classes
  show "finite (UNIV::'a star set)"
    by (metis starset_UNIV finite finite_imageI starset_finite)
qed

end
