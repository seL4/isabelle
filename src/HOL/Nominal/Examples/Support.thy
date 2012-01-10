theory Support 
  imports "../Nominal" 
begin

text {* 
  An example showing that in general

  x\<sharp>(A \<union> B) does not imply  x\<sharp>A and  x\<sharp>B

  For this we set A to the set of even atoms and B to 
  the set of odd atoms. Then A \<union> B, that is the set of 
  all atoms, has empty support. The sets A, respectively B, 
  however have the set of all atoms as their support. 
*}

atom_decl atom

text {* The set of even atoms. *}
abbreviation
  EVEN :: "atom set"
where
  "EVEN \<equiv> {atom n | n. \<exists>i. n=2*i}"

text {* The set of odd atoms: *}
abbreviation  
  ODD :: "atom set"
where
  "ODD \<equiv> {atom n | n. \<exists>i. n=2*i+1}"

text {* An atom is either even or odd. *}
lemma even_or_odd:
  fixes n :: nat
  shows "\<exists>i. (n = 2*i) \<or> (n=2*i+1)"
  by (induct n) (presburger)+

text {* 
  The union of even and odd atoms is the set of all atoms. 
  (Unfortunately I do not know a simpler proof of this fact.) *}
lemma EVEN_union_ODD:
  shows "EVEN \<union> ODD = UNIV"
  using even_or_odd
proof -
  have "EVEN \<union> ODD = (\<lambda>n. atom n) ` {n. \<exists>i. n = 2*i} \<union> (\<lambda>n. atom n) ` {n. \<exists>i. n = 2*i+1}" by auto
  also have "\<dots> = (\<lambda>n. atom n) ` ({n. \<exists>i. n = 2*i} \<union> {n. \<exists>i. n = 2*i+1})" by auto
  also have "\<dots> = (\<lambda>n. atom n) ` ({n. \<exists>i. n = 2*i \<or> n = 2*i+1})" by auto
  also have "\<dots> = (\<lambda>n. atom n) ` (UNIV::nat set)" using even_or_odd by auto
  also have "\<dots> = (UNIV::atom set)" using atom.exhaust
    by (auto simp add: surj_def)
  finally show "EVEN \<union> ODD = UNIV" by simp
qed

text {* The sets of even and odd atoms are disjunct. *}
lemma EVEN_intersect_ODD:
  shows "EVEN \<inter> ODD = {}"
  using even_or_odd
  by (auto) (presburger)

text {* 
  The preceeding two lemmas help us to prove 
  the following two useful equalities: *}

lemma UNIV_subtract:
  shows "UNIV - EVEN = ODD"
  and   "UNIV - ODD  = EVEN"
  using EVEN_union_ODD EVEN_intersect_ODD
  by (blast)+

text {* The sets EVEN and ODD are infinite. *}
lemma EVEN_ODD_infinite:
  shows "infinite EVEN"
  and   "infinite ODD"
unfolding infinite_iff_countable_subset
proof -
  let ?f = "\<lambda>n. atom (2*n)"
  have "inj ?f \<and> range ?f \<subseteq> EVEN" by (auto simp add: inj_on_def)
  then show "\<exists>f::nat\<Rightarrow>atom. inj f \<and> range f \<subseteq> EVEN" by (rule_tac exI)
next
  let ?f = "\<lambda>n. atom (2*n+1)"
  have "inj ?f \<and> range ?f \<subseteq> ODD" by (auto simp add: inj_on_def)
  then show "\<exists>f::nat\<Rightarrow>atom. inj f \<and> range f \<subseteq> ODD" by (rule_tac exI)
qed

text {* 
  A general fact about a set S of atoms that is both infinite and 
  coinfinite. Then S has all atoms as its support. Steve Zdancewic 
  helped with proving this fact. *}

lemma supp_infinite_coinfinite:
  fixes S::"atom set"
  assumes asm1: "infinite S"
  and     asm2: "infinite (UNIV-S)"
  shows "(supp S) = (UNIV::atom set)"
proof -
  have "\<forall>(x::atom). x\<in>(supp S)"
  proof
    fix x::"atom"
    show "x\<in>(supp S)"
    proof (cases "x\<in>S")
      case True
      have "x\<in>S" by fact
      hence "\<forall>b\<in>(UNIV-S). [(x,b)]\<bullet>S\<noteq>S" by (auto simp add: perm_set_def calc_atm)
      with asm2 have "infinite {b\<in>(UNIV-S). [(x,b)]\<bullet>S\<noteq>S}" by (rule infinite_Collection)
      hence "infinite {b. [(x,b)]\<bullet>S\<noteq>S}" by (rule_tac infinite_super, auto)
      then show "x\<in>(supp S)" by (simp add: supp_def)
    next
      case False
      have "x\<notin>S" by fact
      hence "\<forall>b\<in>S. [(x,b)]\<bullet>S\<noteq>S" by (auto simp add: perm_set_def calc_atm)
      with asm1 have "infinite {b\<in>S. [(x,b)]\<bullet>S\<noteq>S}" by (rule infinite_Collection)
      hence "infinite {b. [(x,b)]\<bullet>S\<noteq>S}" by (rule_tac infinite_super, auto)
      then show "x\<in>(supp S)" by (simp add: supp_def)
    qed
  qed
  then show "(supp S) = (UNIV::atom set)" by auto
qed

text {* As a corollary we get that EVEN and ODD have infinite support. *}
lemma EVEN_ODD_supp:
  shows "supp EVEN = (UNIV::atom set)"
  and   "supp ODD  = (UNIV::atom set)"
  using supp_infinite_coinfinite UNIV_subtract EVEN_ODD_infinite
  by simp_all

text {* 
  The set of all atoms has empty support, since any swappings leaves 
  this set unchanged. *}

lemma UNIV_supp:
  shows "supp (UNIV::atom set) = ({}::atom set)"
proof -
  have "\<forall>(x::atom) (y::atom). [(x,y)]\<bullet>UNIV = (UNIV::atom set)"
    by (auto simp add: perm_set_def calc_atm)
  then show "supp (UNIV::atom set) = ({}::atom set)" by (simp add: supp_def)
qed

text {* Putting everything together. *}
theorem EVEN_ODD_freshness:
  fixes x::"atom"
  shows "x\<sharp>(EVEN \<union> ODD)"
  and   "\<not>x\<sharp>EVEN"
  and   "\<not>x\<sharp>ODD"
  by (auto simp only: fresh_def EVEN_union_ODD EVEN_ODD_supp UNIV_supp)

text {* Moral: support is a sublte notion. *}

end