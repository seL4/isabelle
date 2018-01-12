theory Examples imports Complex_Main begin

declare [[eta_contract = false]]

text\<open>membership, intersection\<close>
text\<open>difference and empty set\<close>
text\<open>complement, union and universal set\<close>

lemma "(x \<in> A \<inter> B) = (x \<in> A \<and> x \<in> B)"
by blast

text\<open>
@{thm[display] IntI[no_vars]}
\rulename{IntI}

@{thm[display] IntD1[no_vars]}
\rulename{IntD1}

@{thm[display] IntD2[no_vars]}
\rulename{IntD2}
\<close>

lemma "(x \<in> -A) = (x \<notin> A)"
by blast

text\<open>
@{thm[display] Compl_iff[no_vars]}
\rulename{Compl_iff}
\<close>

lemma "- (A \<union> B) = -A \<inter> -B"
by blast

text\<open>
@{thm[display] Compl_Un[no_vars]}
\rulename{Compl_Un}
\<close>

lemma "A-A = {}"
by blast

text\<open>
@{thm[display] Diff_disjoint[no_vars]}
\rulename{Diff_disjoint}
\<close>



lemma "A \<union> -A = UNIV"
by blast

text\<open>
@{thm[display] Compl_partition[no_vars]}
\rulename{Compl_partition}
\<close>

text\<open>subset relation\<close>


text\<open>
@{thm[display] subsetI[no_vars]}
\rulename{subsetI}

@{thm[display] subsetD[no_vars]}
\rulename{subsetD}
\<close>

lemma "((A \<union> B) \<subseteq> C) = (A \<subseteq> C \<and> B \<subseteq> C)"
by blast

text\<open>
@{thm[display] Un_subset_iff[no_vars]}
\rulename{Un_subset_iff}
\<close>

lemma "(A \<subseteq> -B) = (B \<subseteq> -A)"
by blast

lemma "(A <= -B) = (B <= -A)"
  oops

text\<open>ASCII version: blast fails because of overloading because
 it doesn't have to be sets\<close>

lemma "((A:: 'a set) <= -B) = (B <= -A)"
by blast

text\<open>A type constraint lets it work\<close>

text\<open>An issue here: how do we discuss the distinction between ASCII and
symbol notation?  Here the latter disambiguates.\<close>


text\<open>
set extensionality

@{thm[display] set_eqI[no_vars]}
\rulename{set_eqI}

@{thm[display] equalityI[no_vars]}
\rulename{equalityI}

@{thm[display] equalityE[no_vars]}
\rulename{equalityE}
\<close>


text\<open>finite sets: insertion and membership relation\<close>
text\<open>finite set notation\<close>

lemma "insert x A = {x} \<union> A"
by blast

text\<open>
@{thm[display] insert_is_Un[no_vars]}
\rulename{insert_is_Un}
\<close>

lemma "{a,b} \<union> {c,d} = {a,b,c,d}"
by blast

lemma "{a,b} \<inter> {b,c} = {b}"
apply auto
oops
text\<open>fails because it isn't valid\<close>

lemma "{a,b} \<inter> {b,c} = (if a=c then {a,b} else {b})"
apply simp
by blast

text\<open>or just force or auto.  blast alone can't handle the if-then-else\<close>

text\<open>next: some comprehension examples\<close>

lemma "(a \<in> {z. P z}) = P a"
by blast

text\<open>
@{thm[display] mem_Collect_eq[no_vars]}
\rulename{mem_Collect_eq}
\<close>

lemma "{x. x \<in> A} = A"
by blast

text\<open>
@{thm[display] Collect_mem_eq[no_vars]}
\rulename{Collect_mem_eq}
\<close>

lemma "{x. P x \<or> x \<in> A} = {x. P x} \<union> A"
by blast

lemma "{x. P x \<longrightarrow> Q x} = -{x. P x} \<union> {x. Q x}"
by blast

definition prime :: "nat set" where
    "prime == {p. 1<p & (ALL m. m dvd p --> m=1 | m=p)}"

lemma "{p*q | p q. p\<in>prime \<and> q\<in>prime} =
       {z. \<exists>p q. z = p*q \<and> p\<in>prime \<and> q\<in>prime}"
by (rule refl)

text\<open>binders\<close>

text\<open>bounded quantifiers\<close>

lemma "(\<exists>x\<in>A. P x) = (\<exists>x. x\<in>A \<and> P x)"
by blast

text\<open>
@{thm[display] bexI[no_vars]}
\rulename{bexI}
\<close>

text\<open>
@{thm[display] bexE[no_vars]}
\rulename{bexE}
\<close>

lemma "(\<forall>x\<in>A. P x) = (\<forall>x. x\<in>A \<longrightarrow> P x)"
by blast

text\<open>
@{thm[display] ballI[no_vars]}
\rulename{ballI}
\<close>

text\<open>
@{thm[display] bspec[no_vars]}
\rulename{bspec}
\<close>

text\<open>indexed unions and variations\<close>

lemma "(\<Union>x. B x) = (\<Union>x\<in>UNIV. B x)"
by blast

text\<open>
@{thm[display] UN_iff[no_vars]}
\rulename{UN_iff}
\<close>

text\<open>
@{thm[display] Union_iff[no_vars]}
\rulename{Union_iff}
\<close>

lemma "(\<Union>x\<in>A. B x) = {y. \<exists>x\<in>A. y \<in> B x}"
by blast

lemma "\<Union>S = (\<Union>x\<in>S. x)"
by blast

text\<open>
@{thm[display] UN_I[no_vars]}
\rulename{UN_I}
\<close>

text\<open>
@{thm[display] UN_E[no_vars]}
\rulename{UN_E}
\<close>

text\<open>indexed intersections\<close>

lemma "(\<Inter>x. B x) = {y. \<forall>x. y \<in> B x}"
by blast

text\<open>
@{thm[display] INT_iff[no_vars]}
\rulename{INT_iff}
\<close>

text\<open>
@{thm[display] Inter_iff[no_vars]}
\rulename{Inter_iff}
\<close>

text\<open>mention also card, Pow, etc.\<close>


text\<open>
@{thm[display] card_Un_Int[no_vars]}
\rulename{card_Un_Int}

@{thm[display] card_Pow[no_vars]}
\rulename{card_Pow}

@{thm[display] n_subsets[no_vars]}
\rulename{n_subsets}
\<close>

end
