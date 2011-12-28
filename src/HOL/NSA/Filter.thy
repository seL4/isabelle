(*  Title:      HOL/NSA/Filter.thy
    Author:     Jacques D. Fleuriot, University of Cambridge
    Author:     Lawrence C Paulson
    Author:     Brian Huffman
*) 

header {* Filters and Ultrafilters *}

theory Filter
imports "~~/src/HOL/Library/Zorn" "~~/src/HOL/Library/Infinite_Set"
begin

subsection {* Definitions and basic properties *}

subsubsection {* Filters *}

locale filter =
  fixes F :: "'a set set"
  assumes UNIV [iff]:  "UNIV \<in> F"
  assumes empty [iff]: "{} \<notin> F"
  assumes Int:         "\<lbrakk>u \<in> F; v \<in> F\<rbrakk> \<Longrightarrow> u \<inter> v \<in> F"
  assumes subset:      "\<lbrakk>u \<in> F; u \<subseteq> v\<rbrakk> \<Longrightarrow> v \<in> F"

lemma (in filter) memD: "A \<in> F \<Longrightarrow> - A \<notin> F"
proof
  assume "A \<in> F" and "- A \<in> F"
  hence "A \<inter> (- A) \<in> F" by (rule Int)
  thus "False" by simp
qed

lemma (in filter) not_memI: "- A \<in> F \<Longrightarrow> A \<notin> F"
by (drule memD, simp)

lemma (in filter) Int_iff: "(x \<inter> y \<in> F) = (x \<in> F \<and> y \<in> F)"
by (auto elim: subset intro: Int)

subsubsection {* Ultrafilters *}

locale ultrafilter = filter +
  assumes ultra: "A \<in> F \<or> - A \<in> F"

lemma (in ultrafilter) memI: "- A \<notin> F \<Longrightarrow> A \<in> F"
by (cut_tac ultra [of A], simp)

lemma (in ultrafilter) not_memD: "A \<notin> F \<Longrightarrow> - A \<in> F"
by (rule memI, simp)

lemma (in ultrafilter) not_mem_iff: "(A \<notin> F) = (- A \<in> F)"
by (rule iffI [OF not_memD not_memI])

lemma (in ultrafilter) Compl_iff: "(- A \<in> F) = (A \<notin> F)"
by (rule iffI [OF not_memI not_memD])

lemma (in ultrafilter) Un_iff: "(x \<union> y \<in> F) = (x \<in> F \<or> y \<in> F)"
 apply (rule iffI)
  apply (erule contrapos_pp)
  apply (simp add: Int_iff not_mem_iff)
 apply (auto elim: subset)
done

subsubsection {* Free Ultrafilters *}

locale freeultrafilter = ultrafilter +
  assumes infinite: "A \<in> F \<Longrightarrow> infinite A"

lemma (in freeultrafilter) finite: "finite A \<Longrightarrow> A \<notin> F"
by (erule contrapos_pn, erule infinite)

lemma (in freeultrafilter) singleton: "{x} \<notin> F"
by (rule finite, simp)

lemma (in freeultrafilter) insert_iff [simp]: "(insert x A \<in> F) = (A \<in> F)"
apply (subst insert_is_Un)
apply (subst Un_iff)
apply (simp add: singleton)
done

lemma (in freeultrafilter) filter: "filter F" ..

lemma (in freeultrafilter) ultrafilter: "ultrafilter F" ..


subsection {* Collect properties *}

lemma (in filter) Collect_ex:
  "({n. \<exists>x. P n x} \<in> F) = (\<exists>X. {n. P n (X n)} \<in> F)"
proof
  assume "{n. \<exists>x. P n x} \<in> F"
  hence "{n. P n (SOME x. P n x)} \<in> F"
    by (auto elim: someI subset)
  thus "\<exists>X. {n. P n (X n)} \<in> F" by fast
next
  show "\<exists>X. {n. P n (X n)} \<in> F \<Longrightarrow> {n. \<exists>x. P n x} \<in> F"
    by (auto elim: subset)
qed

lemma (in filter) Collect_conj:
  "({n. P n \<and> Q n} \<in> F) = ({n. P n} \<in> F \<and> {n. Q n} \<in> F)"
by (subst Collect_conj_eq, rule Int_iff)

lemma (in ultrafilter) Collect_not:
  "({n. \<not> P n} \<in> F) = ({n. P n} \<notin> F)"
by (subst Collect_neg_eq, rule Compl_iff)

lemma (in ultrafilter) Collect_disj:
  "({n. P n \<or> Q n} \<in> F) = ({n. P n} \<in> F \<or> {n. Q n} \<in> F)"
by (subst Collect_disj_eq, rule Un_iff)

lemma (in ultrafilter) Collect_all:
  "({n. \<forall>x. P n x} \<in> F) = (\<forall>X. {n. P n (X n)} \<in> F)"
apply (rule Not_eq_iff [THEN iffD1])
apply (simp add: Collect_not [symmetric])
apply (rule Collect_ex)
done

subsection {* Maximal filter = Ultrafilter *}

text {*
   A filter F is an ultrafilter iff it is a maximal filter,
   i.e. whenever G is a filter and @{term "F \<subseteq> G"} then @{term "F = G"}
*}
text {*
  Lemmas that shows existence of an extension to what was assumed to
  be a maximal filter. Will be used to derive contradiction in proof of
  property of ultrafilter.
*}

lemma extend_lemma1: "UNIV \<in> F \<Longrightarrow> A \<in> {X. \<exists>f\<in>F. A \<inter> f \<subseteq> X}"
by blast

lemma extend_lemma2: "F \<subseteq> {X. \<exists>f\<in>F. A \<inter> f \<subseteq> X}"
by blast

lemma (in filter) extend_filter:
assumes A: "- A \<notin> F"
shows "filter {X. \<exists>f\<in>F. A \<inter> f \<subseteq> X}" (is "filter ?X")
proof (rule filter.intro)
  show "UNIV \<in> ?X" by blast
next
  show "{} \<notin> ?X"
  proof (clarify)
    fix f assume f: "f \<in> F" and Af: "A \<inter> f \<subseteq> {}"
    from Af have fA: "f \<subseteq> - A" by blast
    from f fA have "- A \<in> F" by (rule subset)
    with A show "False" by simp
  qed
next
  fix u and v
  assume u: "u \<in> ?X" and v: "v \<in> ?X"
  from u obtain f where f: "f \<in> F" and Af: "A \<inter> f \<subseteq> u" by blast
  from v obtain g where g: "g \<in> F" and Ag: "A \<inter> g \<subseteq> v" by blast
  from f g have fg: "f \<inter> g \<in> F" by (rule Int)
  from Af Ag have Afg: "A \<inter> (f \<inter> g) \<subseteq> u \<inter> v" by blast
  from fg Afg show "u \<inter> v \<in> ?X" by blast
next
  fix u and v
  assume uv: "u \<subseteq> v" and u: "u \<in> ?X"
  from u obtain f where f: "f \<in> F" and Afu: "A \<inter> f \<subseteq> u" by blast
  from Afu uv have Afv: "A \<inter> f \<subseteq> v" by blast
  from f Afv have "\<exists>f\<in>F. A \<inter> f \<subseteq> v" by blast
  thus "v \<in> ?X" by simp
qed

lemma (in filter) max_filter_ultrafilter:
assumes max: "\<And>G. \<lbrakk>filter G; F \<subseteq> G\<rbrakk> \<Longrightarrow> F = G"
shows "ultrafilter_axioms F"
proof (rule ultrafilter_axioms.intro)
  fix A show "A \<in> F \<or> - A \<in> F"
  proof (rule disjCI)
    let ?X = "{X. \<exists>f\<in>F. A \<inter> f \<subseteq> X}"
    assume AF: "- A \<notin> F"
    from AF have X: "filter ?X" by (rule extend_filter)
    from UNIV have AX: "A \<in> ?X" by (rule extend_lemma1)
    have FX: "F \<subseteq> ?X" by (rule extend_lemma2)
    from X FX have "F = ?X" by (rule max)
    with AX show "A \<in> F" by simp
  qed
qed

lemma (in ultrafilter) max_filter:
assumes G: "filter G" and sub: "F \<subseteq> G" shows "F = G"
proof
  show "F \<subseteq> G" using sub .
  show "G \<subseteq> F"
  proof
    fix A assume A: "A \<in> G"
    from G A have "- A \<notin> G" by (rule filter.memD)
    with sub have B: "- A \<notin> F" by blast
    thus "A \<in> F" by (rule memI)
  qed
qed

subsection {* Ultrafilter Theorem *}

text "A locale makes proof of ultrafilter Theorem more modular"
locale UFT =
  fixes   frechet :: "'a set set"
  and     superfrechet :: "'a set set set"

  assumes infinite_UNIV: "infinite (UNIV :: 'a set)"

  defines frechet_def: "frechet \<equiv> {A. finite (- A)}"
  and     superfrechet_def: "superfrechet \<equiv> {G. filter G \<and> frechet \<subseteq> G}"

lemma (in UFT) superfrechetI:
  "\<lbrakk>filter G; frechet \<subseteq> G\<rbrakk> \<Longrightarrow> G \<in> superfrechet"
by (simp add: superfrechet_def)

lemma (in UFT) superfrechetD1:
  "G \<in> superfrechet \<Longrightarrow> filter G"
by (simp add: superfrechet_def)

lemma (in UFT) superfrechetD2:
  "G \<in> superfrechet \<Longrightarrow> frechet \<subseteq> G"
by (simp add: superfrechet_def)

text {* A few properties of free filters *}

lemma filter_cofinite:
assumes inf: "infinite (UNIV :: 'a set)"
shows "filter {A:: 'a set. finite (- A)}" (is "filter ?F")
proof (rule filter.intro)
  show "UNIV \<in> ?F" by simp
next
  show "{} \<notin> ?F" using inf by simp
next
  fix u v assume "u \<in> ?F" and "v \<in> ?F"
  thus "u \<inter> v \<in> ?F" by simp
next
  fix u v assume uv: "u \<subseteq> v" and u: "u \<in> ?F"
  from uv have vu: "- v \<subseteq> - u" by simp
  from u show "v \<in> ?F"
    by (simp add: finite_subset [OF vu])
qed

text {*
   We prove: 1. Existence of maximal filter i.e. ultrafilter;
             2. Freeness property i.e ultrafilter is free.
             Use a locale to prove various lemmas and then 
             export main result: The ultrafilter Theorem
*}

lemma (in UFT) filter_frechet: "filter frechet"
by (unfold frechet_def, rule filter_cofinite [OF infinite_UNIV])

lemma (in UFT) frechet_in_superfrechet: "frechet \<in> superfrechet"
by (rule superfrechetI [OF filter_frechet subset_refl])

lemma (in UFT) lemma_mem_chain_filter:
  "\<lbrakk>c \<in> chain superfrechet; x \<in> c\<rbrakk> \<Longrightarrow> filter x"
by (unfold chain_def superfrechet_def, blast)


subsubsection {* Unions of chains of superfrechets *}

text "In this section we prove that superfrechet is closed
with respect to unions of non-empty chains. We must show
  1) Union of a chain is a filter,
  2) Union of a chain contains frechet.

Number 2 is trivial, but 1 requires us to prove all the filter rules."

lemma (in UFT) Union_chain_UNIV:
"\<lbrakk>c \<in> chain superfrechet; c \<noteq> {}\<rbrakk> \<Longrightarrow> UNIV \<in> \<Union>c"
proof -
  assume 1: "c \<in> chain superfrechet" and 2: "c \<noteq> {}"
  from 2 obtain x where 3: "x \<in> c" by blast
  from 1 3 have "filter x" by (rule lemma_mem_chain_filter)
  hence "UNIV \<in> x" by (rule filter.UNIV)
  with 3 show "UNIV \<in> \<Union>c" by blast
qed

lemma (in UFT) Union_chain_empty:
"c \<in> chain superfrechet \<Longrightarrow> {} \<notin> \<Union>c"
proof
  assume 1: "c \<in> chain superfrechet" and 2: "{} \<in> \<Union>c"
  from 2 obtain x where 3: "x \<in> c" and 4: "{} \<in> x" ..
  from 1 3 have "filter x" by (rule lemma_mem_chain_filter)
  hence "{} \<notin> x" by (rule filter.empty)
  with 4 show "False" by simp
qed

lemma (in UFT) Union_chain_Int:
"\<lbrakk>c \<in> chain superfrechet; u \<in> \<Union>c; v \<in> \<Union>c\<rbrakk> \<Longrightarrow> u \<inter> v \<in> \<Union>c"
proof -
  assume c: "c \<in> chain superfrechet"
  assume "u \<in> \<Union>c"
    then obtain x where ux: "u \<in> x" and xc: "x \<in> c" ..
  assume "v \<in> \<Union>c"
    then obtain y where vy: "v \<in> y" and yc: "y \<in> c" ..
  from c xc yc have "x \<subseteq> y \<or> y \<subseteq> x" by (rule chainD)
  with xc yc have xyc: "x \<union> y \<in> c"
    by (auto simp add: Un_absorb1 Un_absorb2)
  with c have fxy: "filter (x \<union> y)" by (rule lemma_mem_chain_filter)
  from ux have uxy: "u \<in> x \<union> y" by simp
  from vy have vxy: "v \<in> x \<union> y" by simp
  from fxy uxy vxy have "u \<inter> v \<in> x \<union> y" by (rule filter.Int)
  with xyc show "u \<inter> v \<in> \<Union>c" ..
qed

lemma (in UFT) Union_chain_subset:
"\<lbrakk>c \<in> chain superfrechet; u \<in> \<Union>c; u \<subseteq> v\<rbrakk> \<Longrightarrow> v \<in> \<Union>c"
proof -
  assume c: "c \<in> chain superfrechet"
     and u: "u \<in> \<Union>c" and uv: "u \<subseteq> v"
  from u obtain x where ux: "u \<in> x" and xc: "x \<in> c" ..
  from c xc have fx: "filter x" by (rule lemma_mem_chain_filter)
  from fx ux uv have vx: "v \<in> x" by (rule filter.subset)
  with xc show "v \<in> \<Union>c" ..
qed

lemma (in UFT) Union_chain_filter:
assumes chain: "c \<in> chain superfrechet" and nonempty: "c \<noteq> {}"
shows "filter (\<Union>c)"
proof (rule filter.intro)
  show "UNIV \<in> \<Union>c" using chain nonempty by (rule Union_chain_UNIV)
next
  show "{} \<notin> \<Union>c" using chain by (rule Union_chain_empty)
next
  fix u v assume "u \<in> \<Union>c" and "v \<in> \<Union>c"
  with chain show "u \<inter> v \<in> \<Union>c" by (rule Union_chain_Int)
next
  fix u v assume "u \<in> \<Union>c" and "u \<subseteq> v"
  with chain show "v \<in> \<Union>c" by (rule Union_chain_subset)
qed

lemma (in UFT) lemma_mem_chain_frechet_subset:
  "\<lbrakk>c \<in> chain superfrechet; x \<in> c\<rbrakk> \<Longrightarrow> frechet \<subseteq> x"
by (unfold superfrechet_def chain_def, blast)

lemma (in UFT) Union_chain_superfrechet:
  "\<lbrakk>c \<noteq> {}; c \<in> chain superfrechet\<rbrakk> \<Longrightarrow> \<Union>c \<in> superfrechet"
proof (rule superfrechetI)
  assume 1: "c \<in> chain superfrechet" and 2: "c \<noteq> {}"
  thus "filter (\<Union>c)" by (rule Union_chain_filter)
  from 2 obtain x where 3: "x \<in> c" by blast
  from 1 3 have "frechet \<subseteq> x" by (rule lemma_mem_chain_frechet_subset)
  also from 3 have "x \<subseteq> \<Union>c" by blast
  finally show "frechet \<subseteq> \<Union>c" .
qed

subsubsection {* Existence of free ultrafilter *}

lemma (in UFT) max_cofinite_filter_Ex:
  "\<exists>U\<in>superfrechet. \<forall>G\<in>superfrechet. U \<subseteq> G \<longrightarrow> U = G"
proof (rule Zorn_Lemma2 [rule_format])
  fix c assume c: "c \<in> chain superfrechet"
  show "\<exists>U\<in>superfrechet. \<forall>G\<in>c. G \<subseteq> U" (is "?U")
  proof (cases)
    assume "c = {}"
    with frechet_in_superfrechet show "?U" by blast
  next
    assume A: "c \<noteq> {}"
    from A c have "\<Union>c \<in> superfrechet"
      by (rule Union_chain_superfrechet)
    thus "?U" by blast
  qed
qed

lemma (in UFT) mem_superfrechet_all_infinite:
  "\<lbrakk>U \<in> superfrechet; A \<in> U\<rbrakk> \<Longrightarrow> infinite A"
proof
  assume U: "U \<in> superfrechet" and A: "A \<in> U" and fin: "finite A"
  from U have fil: "filter U" and fre: "frechet \<subseteq> U"
    by (simp_all add: superfrechet_def)
  from fin have "- A \<in> frechet" by (simp add: frechet_def)
  with fre have cA: "- A \<in> U" by (rule subsetD)
  from fil A cA have "A \<inter> - A \<in> U" by (rule filter.Int)
  with fil show "False" by (simp add: filter.empty)
qed

text {* There exists a free ultrafilter on any infinite set *}

lemma (in UFT) freeultrafilter_ex:
  "\<exists>U::'a set set. freeultrafilter U"
proof -
  from max_cofinite_filter_Ex obtain U
    where U: "U \<in> superfrechet"
      and max [rule_format]: "\<forall>G\<in>superfrechet. U \<subseteq> G \<longrightarrow> U = G" ..
  from U have fil: "filter U" by (rule superfrechetD1)
  from U have fre: "frechet \<subseteq> U" by (rule superfrechetD2)
  have ultra: "ultrafilter_axioms U"
  proof (rule filter.max_filter_ultrafilter [OF fil])
    fix G assume G: "filter G" and UG: "U \<subseteq> G"
    from fre UG have "frechet \<subseteq> G" by simp
    with G have "G \<in> superfrechet" by (rule superfrechetI)
    from this UG show "U = G" by (rule max)
  qed
  have free: "freeultrafilter_axioms U"
  proof (rule freeultrafilter_axioms.intro)
    fix A assume "A \<in> U"
    with U show "infinite A" by (rule mem_superfrechet_all_infinite)
  qed
  from fil ultra free have "freeultrafilter U"
    by (rule freeultrafilter.intro [OF ultrafilter.intro])
    (* FIXME: unfold_locales should use chained facts *)
  then show ?thesis ..
qed

lemmas freeultrafilter_Ex = UFT.freeultrafilter_ex [OF UFT.intro]

hide_const (open) filter

end
