(*  Title:   HOL/LOrder.thy
    ID:      $Id$
    Author:  Steven Obua, TU Muenchen

FIXME integrate properly with lattice locales
- get rid of the implicit there-is-a-meet/join but require explicit ops.
- abandone semilorder axclasses, instead turn lattice locales into classes
- rename meet/join to inf/sup in all theorems
*)

header "Lattice Orders"

theory LOrder
imports Lattices
begin

text {* The theory of lattices developed here is taken from
\cite{Birkhoff79}.  *}

constdefs
  is_meet :: "(('a::order) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool"
  "is_meet m == ! a b x. m a b \<le> a \<and> m a b \<le> b \<and> (x \<le> a \<and> x \<le> b \<longrightarrow> x \<le> m a b)"
  is_join :: "(('a::order) \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool"
  "is_join j == ! a b x. a \<le> j a b \<and> b \<le> j a b \<and> (a \<le> x \<and> b \<le> x \<longrightarrow> j a b \<le> x)"  

lemma is_meet_unique: 
  assumes "is_meet u" "is_meet v" shows "u = v"
proof -
  {
    fix a b :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    assume a: "is_meet a"
    assume b: "is_meet b"
    {
      fix x y 
      let ?za = "a x y"
      let ?zb = "b x y"
      from a have za_le: "?za <= x & ?za <= y" by (auto simp add: is_meet_def)
      with b have "?za <= ?zb" by (auto simp add: is_meet_def)
    }
  }
  note f_le = this
  show "u = v" by ((rule ext)+, simp_all add: order_antisym prems f_le) 
qed

lemma is_join_unique: 
  assumes "is_join u" "is_join v" shows "u = v"
proof -
  {
    fix a b :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    assume a: "is_join a"
    assume b: "is_join b"
    {
      fix x y 
      let ?za = "a x y"
      let ?zb = "b x y"
      from a have za_le: "x <= ?za & y <= ?za" by (auto simp add: is_join_def)
      with b have "?zb <= ?za" by (auto simp add: is_join_def)
    }
  }
  note f_le = this
  show "u = v" by ((rule ext)+, simp_all add: order_antisym prems f_le) 
qed

lemma is_meet_inf: "is_meet (inf \<Colon> 'a\<Colon>lower_semilattice \<Rightarrow> 'a \<Rightarrow> 'a)"
unfolding is_meet_def by auto

lemma is_join_sup: "is_join (sup \<Colon> 'a\<Colon>upper_semilattice \<Rightarrow> 'a \<Rightarrow> 'a)"
unfolding is_join_def by auto

axclass meet_semilorder < order
  meet_exists: "? m. is_meet m"

axclass join_semilorder < order
  join_exists: "? j. is_join j"

axclass lorder < meet_semilorder, join_semilorder

definition
  inf :: "('a::meet_semilorder) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "inf = (THE m. is_meet m)"

definition
  sup :: "('a::join_semilorder) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "sup = (THE j. is_join j)"

lemma is_meet_meet: "is_meet (inf::'a \<Rightarrow> 'a \<Rightarrow> ('a::meet_semilorder))"
proof -
  from meet_exists obtain k::"'a \<Rightarrow> 'a \<Rightarrow> 'a" where "is_meet k" ..
  with is_meet_unique[of _ k] show ?thesis
    by (simp add: inf_def theI [of is_meet])    
qed

lemma is_join_join: "is_join (sup::'a \<Rightarrow> 'a \<Rightarrow> ('a::join_semilorder))"
proof -
  from join_exists obtain k::"'a \<Rightarrow> 'a \<Rightarrow> 'a" where "is_join k" ..
  with is_join_unique[of _ k] show ?thesis
    by (simp add: sup_def theI[of is_join])    
qed

lemma meet_unique: "(is_meet m) = (m = inf)" 
by (insert is_meet_meet, auto simp add: is_meet_unique)

lemma join_unique: "(is_join j) = (j = sup)"
by (insert is_join_join, auto simp add: is_join_unique)

lemma inf_unique: "(is_meet m) = (m = (Lattices.inf \<Colon> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<Colon>lower_semilattice))" 
by (insert is_meet_inf, auto simp add: is_meet_unique)

lemma sup_unique: "(is_join j) = (j = (Lattices.sup \<Colon> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<Colon>upper_semilattice))"
by (insert is_join_sup, auto simp add: is_join_unique)

interpretation inf_semilat:
  lower_semilattice ["op \<le> \<Colon> 'a\<Colon>meet_semilorder \<Rightarrow> 'a \<Rightarrow> bool" "op <" inf]
proof unfold_locales
  fix x y z :: "'a\<Colon>meet_semilorder"
  from is_meet_meet have "is_meet inf" by blast
  note meet = this is_meet_def
  from meet show "inf x y \<le> x" by blast
  from meet show "inf x y \<le> y" by blast
  from meet show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z" by blast
qed

interpretation sup_semilat:
  upper_semilattice ["op \<le> \<Colon> 'a\<Colon>join_semilorder \<Rightarrow> 'a \<Rightarrow> bool" "op <" sup]
proof unfold_locales
  fix x y z :: "'a\<Colon>join_semilorder"
  from is_join_join have "is_join sup" by blast
  note join = this is_join_def
  from join show "x \<le> sup x y" by blast
  from join show "y \<le> sup x y" by blast
  from join show "x \<le> z \<Longrightarrow> y \<le> z \<Longrightarrow> sup x y \<le> z" by blast
qed

interpretation inf_sup_lat:
  lattice ["op \<le> \<Colon> 'a\<Colon>lorder \<Rightarrow> 'a \<Rightarrow> bool" "op <" inf sup]
  by unfold_locales

lemma is_meet_min: "is_meet (min::'a \<Rightarrow> 'a \<Rightarrow> ('a::linorder))"
  by (auto simp add: is_meet_def min_def)
 lemma is_join_max: "is_join (max::'a \<Rightarrow> 'a \<Rightarrow> ('a::linorder))"
  by (auto simp add: is_join_def max_def)

instance linorder \<subseteq> lorder
proof
  from is_meet_min show "? (m::'a\<Rightarrow>'a\<Rightarrow>('a::linorder)). is_meet m" by auto
  from is_join_max show "? (j::'a\<Rightarrow>'a\<Rightarrow>('a::linorder)). is_join j" by auto 
qed

lemma meet_min: "inf = (min \<Colon> 'a\<Colon>{linorder} \<Rightarrow> 'a \<Rightarrow> 'a)"
  by (simp add: is_meet_meet is_meet_min is_meet_unique)
lemma join_max: "sup = (max \<Colon> 'a\<Colon>{linorder} \<Rightarrow> 'a \<Rightarrow> 'a)"
  by (simp add: is_join_join is_join_max is_join_unique)

lemmas [rule del] = sup_semilat.antisym_intro inf_semilat.antisym_intro
  sup_semilat.le_supE inf_semilat.le_infE

lemmas inf_le1 = inf_semilat.inf_le1
lemmas inf_le2 = inf_semilat.inf_le2
lemmas le_infI [rule del] = inf_semilat.le_infI
  (*intro! breaks a proof in Hyperreal/SEQ and NumberTheory/IntPrimes*)
lemmas sup_ge1 = sup_semilat.sup_ge1
lemmas sup_ge2 = sup_semilat.sup_ge2
lemmas le_supI [rule del] = sup_semilat.le_supI
lemmas inf_sup_ord = inf_le1 inf_le2 sup_ge1 sup_ge2
lemmas le_inf_iff = inf_semilat.le_inf_iff
lemmas ge_sup_conv = sup_semilat.ge_sup_conv
lemmas inf_idem = inf_semilat.inf_idem
lemmas sup_idem = sup_semilat.sup_idem
lemmas inf_commute = inf_semilat.inf_commute
lemmas sup_commute = sup_semilat.sup_commute
lemmas le_infI1 [rule del] = inf_semilat.le_infI1
lemmas le_infI2 [rule del] = inf_semilat.le_infI2
lemmas le_supI1 [rule del] = sup_semilat.le_supI1
lemmas le_supI2 [rule del] = sup_semilat.le_supI2
lemmas inf_assoc = inf_semilat.inf_assoc
lemmas sup_assoc = sup_semilat.sup_assoc
lemmas inf_left_commute = inf_semilat.inf_left_commute
lemmas inf_left_idem = inf_semilat.inf_left_idem
lemmas sup_left_commute = sup_semilat.sup_left_commute
lemmas sup_left_idem= sup_semilat.sup_left_idem
lemmas inf_aci = inf_assoc inf_commute inf_left_commute inf_left_idem
lemmas sup_aci = sup_assoc sup_commute sup_left_commute sup_left_idem
lemmas le_iff_inf = inf_semilat.le_iff_inf
lemmas le_iff_sup = sup_semilat.le_iff_sup
lemmas sup_absorb2 = sup_semilat.sup_absorb2
lemmas sup_absorb1 = sup_semilat.sup_absorb1
lemmas inf_absorb1 = inf_semilat.inf_absorb1
lemmas inf_absorb2 = inf_semilat.inf_absorb2
lemmas inf_sup_absorb = inf_sup_lat.inf_sup_absorb
lemmas sup_inf_absorb = inf_sup_lat.sup_inf_absorb
lemmas distrib_sup_le = inf_sup_lat.distrib_sup_le
lemmas distrib_inf_le = inf_sup_lat.distrib_inf_le

end
