(* ID:         $Id$ *)
theory Examples = Main:

ML "reset eta_contract"
ML "Pretty.setmargin 64"

text{*membership, intersection *}
text{*difference and empty set*}
text{*complement, union and universal set*}

lemma "(x \<in> A \<inter> B) = (x \<in> A \<and> x \<in> B)"
by blast

text{*
@{thm[display] IntI[no_vars]}
\rulename{IntI}

@{thm[display] IntD1[no_vars]}
\rulename{IntD1}

@{thm[display] IntD2[no_vars]}
\rulename{IntD2}
*}

lemma "(x \<in> -A) = (x \<notin> A)"
by blast

text{*
@{thm[display] Compl_iff[no_vars]}
\rulename{Compl_iff}
*}

lemma "- (A \<union> B) = -A \<inter> -B"
by blast

text{*
@{thm[display] Compl_Un[no_vars]}
\rulename{Compl_Un}
*}

lemma "A-A = {}"
by blast

text{*
@{thm[display] Diff_disjoint[no_vars]}
\rulename{Diff_disjoint}
*}

  

lemma "A \<union> -A = UNIV"
by blast

text{*
@{thm[display] Compl_partition[no_vars]}
\rulename{Compl_partition}
*}

text{*subset relation*}


text{*
@{thm[display] subsetI[no_vars]}
\rulename{subsetI}

@{thm[display] subsetD[no_vars]}
\rulename{subsetD}
*}

lemma "((A \<union> B) \<subseteq> C) = (A \<subseteq> C \<and> B \<subseteq> C)"
by blast

text{*
@{thm[display] Un_subset_iff[no_vars]}
\rulename{Un_subset_iff}
*}

lemma "(A \<subseteq> -B) = (B \<subseteq> -A)"
by blast

lemma "(A <= -B) = (B <= -A)"
  oops

text{*ASCII version: blast fails because of overloading because
 it doesn't have to be sets*}

lemma "((A:: 'a set) <= -B) = (B <= -A)"
by blast

text{*A type constraint lets it work*}

text{*An issue here: how do we discuss the distinction between ASCII and
symbol notation?  Here the latter disambiguates.*}


text{*
set extensionality

@{thm[display] set_ext[no_vars]}
\rulename{set_ext}

@{thm[display] equalityI[no_vars]}
\rulename{equalityI}

@{thm[display] equalityE[no_vars]}
\rulename{equalityE}
*}


text{*finite sets: insertion and membership relation*}
text{*finite set notation*}

lemma "insert x A = {x} \<union> A"
by blast

text{*
@{thm[display] insert_is_Un[no_vars]}
\rulename{insert_is_Un}
*}

lemma "{a,b} \<union> {c,d} = {a,b,c,d}"
by blast

lemma "{a,b} \<inter> {b,c} = {b}"
apply auto
oops
text{*fails because it isn't valid*}

lemma "{a,b} \<inter> {b,c} = (if a=c then {a,b} else {b})"
apply simp
by blast

text{*or just force or auto.  blast alone can't handle the if-then-else*}

text{*next: some comprehension examples*}

lemma "(a \<in> {z. P z}) = P a"
by blast

text{*
@{thm[display] mem_Collect_eq[no_vars]}
\rulename{mem_Collect_eq}
*}

lemma "{x. x \<in> A} = A"
by blast
  
text{*
@{thm[display] Collect_mem_eq[no_vars]}
\rulename{Collect_mem_eq}
*}

lemma "{x. P x \<or> x \<in> A} = {x. P x} \<union> A"
by blast

lemma "{x. P x \<longrightarrow> Q x} = -{x. P x} \<union> {x. Q x}"
by blast

constdefs
  prime   :: "nat set"
    "prime == {p. 1<p & (ALL m. m dvd p --> m=1 | m=p)}"

lemma "{p*q | p q. p\<in>prime \<and> q\<in>prime} = 
       {z. \<exists>p q. z = p*q \<and> p\<in>prime \<and> q\<in>prime}"
by (rule refl)

text{*binders*}

text{*bounded quantifiers*}

lemma "(\<exists>x\<in>A. P x) = (\<exists>x. x\<in>A \<and> P x)"
by blast

text{*
@{thm[display] bexI[no_vars]}
\rulename{bexI}
*}

text{*
@{thm[display] bexE[no_vars]}
\rulename{bexE}
*}

lemma "(\<forall>x\<in>A. P x) = (\<forall>x. x\<in>A \<longrightarrow> P x)"
by blast

text{*
@{thm[display] ballI[no_vars]}
\rulename{ballI}
*}

text{*
@{thm[display] bspec[no_vars]}
\rulename{bspec}
*}

text{*indexed unions and variations*}

lemma "(\<Union>x. B x) = (\<Union>x\<in>UNIV. B x)"
by blast

text{*
@{thm[display] UN_iff[no_vars]}
\rulename{UN_iff}
*}

text{*
@{thm[display] Union_iff[no_vars]}
\rulename{Union_iff}
*}

lemma "(\<Union>x\<in>A. B x) = {y. \<exists>x\<in>A. y \<in> B x}"
by blast

lemma "\<Union>S = (\<Union>x\<in>S. x)"
by blast

text{*
@{thm[display] UN_I[no_vars]}
\rulename{UN_I}
*}

text{*
@{thm[display] UN_E[no_vars]}
\rulename{UN_E}
*}

text{*indexed intersections*}

lemma "(\<Inter>x. B x) = {y. \<forall>x. y \<in> B x}"
by blast

text{*
@{thm[display] INT_iff[no_vars]}
\rulename{INT_iff}
*}

text{*
@{thm[display] Inter_iff[no_vars]}
\rulename{Inter_iff}
*}

text{*mention also card, Pow, etc.*}


text{*
@{thm[display] card_Un_Int[no_vars]}
\rulename{card_Un_Int}

@{thm[display] card_Pow[no_vars]}
\rulename{card_Pow}

@{thm[display] n_subsets[no_vars]}
\rulename{n_subsets}
*}

end
