(*  Title:   HOL/LOrder.thy
    ID:      $Id$
    Author:  Steven Obua, TU Muenchen

FIXME integrate properly with lattice locales
- make it a class?
- get rid of the implicit there-is-a-meet/join but require eplicit ops.
Also rename meet/join to inf/sup. 
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

axclass join_semilorder < order
  join_exists: "? j. is_join j"

axclass meet_semilorder < order
  meet_exists: "? m. is_meet m"

axclass lorder < join_semilorder, meet_semilorder

constdefs
  meet :: "('a::meet_semilorder) \<Rightarrow> 'a \<Rightarrow> 'a"
  "meet == THE m. is_meet m"
  join :: "('a::join_semilorder) \<Rightarrow> 'a \<Rightarrow> 'a"
  "join ==  THE j. is_join j"

lemma is_meet_meet: "is_meet (meet::'a \<Rightarrow> 'a \<Rightarrow> ('a::meet_semilorder))"
proof -
  from meet_exists obtain k::"'a \<Rightarrow> 'a \<Rightarrow> 'a" where "is_meet k" ..
  with is_meet_unique[of _ k] show ?thesis
    by (simp add: meet_def theI[of is_meet])    
qed

lemma meet_unique: "(is_meet m) = (m = meet)" 
by (insert is_meet_meet, auto simp add: is_meet_unique)

lemma is_join_join: "is_join (join::'a \<Rightarrow> 'a \<Rightarrow> ('a::join_semilorder))"
proof -
  from join_exists obtain k::"'a \<Rightarrow> 'a \<Rightarrow> 'a" where "is_join k" ..
  with is_join_unique[of _ k] show ?thesis
    by (simp add: join_def theI[of is_join])    
qed

lemma join_unique: "(is_join j) = (j = join)"
by (insert is_join_join, auto simp add: is_join_unique)

interpretation meet_semilat:
  lower_semilattice ["op \<le> \<Colon> 'a\<Colon>meet_semilorder \<Rightarrow> 'a \<Rightarrow> bool" "op <" meet]
proof unfold_locales
  fix x y z :: "'a\<Colon>meet_semilorder"
  from is_meet_meet have "is_meet meet" by blast
  note meet = this is_meet_def
  from meet show "meet x y \<le> x" by blast
  from meet show "meet x y \<le> y" by blast
  from meet show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> meet y z" by blast
qed

interpretation join_semilat:
  upper_semilattice ["op \<le> \<Colon> 'a\<Colon>join_semilorder \<Rightarrow> 'a \<Rightarrow> bool" "op <" join]
proof unfold_locales
  fix x y z :: "'a\<Colon>join_semilorder"
  from is_join_join have "is_join join" by blast
  note join = this is_join_def
  from join show "x \<le> join x y" by blast
  from join show "y \<le> join x y" by blast
  from join show "x \<le> z \<Longrightarrow> y \<le> z \<Longrightarrow> join x y \<le> z" by blast
qed

declare
 join_semilat.antisym_intro[rule del] meet_semilat.antisym_intro[rule del]
 join_semilat.le_supE[rule del] meet_semilat.le_infE[rule del]

interpretation meet_join_lat:
  lattice ["op \<le> \<Colon> 'a\<Colon>lorder \<Rightarrow> 'a \<Rightarrow> bool" "op <" meet join]
by unfold_locales

lemmas meet_left_le = meet_semilat.inf_le1
lemmas meet_right_le = meet_semilat.inf_le2
lemmas le_meetI[rule del] = meet_semilat.le_infI
(* intro! breaks a proof in Hyperreal/SEQ and NumberTheory/IntPrimes *)
lemmas join_left_le = join_semilat.sup_ge1
lemmas join_right_le = join_semilat.sup_ge2
lemmas join_leI[rule del] = join_semilat.le_supI

lemmas meet_join_le = meet_left_le meet_right_le join_left_le join_right_le

lemmas le_meet = meet_semilat.le_inf_iff

lemmas le_join = join_semilat.ge_sup_conv

lemma is_meet_min: "is_meet (min::'a \<Rightarrow> 'a \<Rightarrow> ('a::linorder))"
by (auto simp add: is_meet_def min_def)

lemma is_join_max: "is_join (max::'a \<Rightarrow> 'a \<Rightarrow> ('a::linorder))"
by (auto simp add: is_join_def max_def)

instance linorder \<subseteq> meet_semilorder
proof
  from is_meet_min show "? (m::'a\<Rightarrow>'a\<Rightarrow>('a::linorder)). is_meet m" by auto
qed

instance linorder \<subseteq> join_semilorder
proof
  from is_join_max show "? (j::'a\<Rightarrow>'a\<Rightarrow>('a::linorder)). is_join j" by auto 
qed
    
instance linorder \<subseteq> lorder ..

lemma meet_min: "meet = (min :: 'a\<Rightarrow>'a\<Rightarrow>('a::linorder))" 
by (simp add: is_meet_meet is_meet_min is_meet_unique)

lemma join_max: "join = (max :: 'a\<Rightarrow>'a\<Rightarrow>('a::linorder))"
by (simp add: is_join_join is_join_max is_join_unique)

lemmas meet_idempotent = meet_semilat.inf_idem
lemmas join_idempotent = join_semilat.sup_idem
lemmas meet_comm = meet_semilat.inf_commute
lemmas join_comm = join_semilat.sup_commute
lemmas meet_leI1[rule del] = meet_semilat.le_infI1
lemmas meet_leI2[rule del] = meet_semilat.le_infI2
lemmas le_joinI1[rule del] = join_semilat.le_supI1
lemmas le_joinI2[rule del] = join_semilat.le_supI2
lemmas meet_assoc = meet_semilat.inf_assoc
lemmas join_assoc = join_semilat.sup_assoc
lemmas meet_left_comm = meet_semilat.inf_left_commute
lemmas meet_left_idempotent = meet_semilat.inf_left_idem
lemmas join_left_comm = join_semilat.sup_left_commute
lemmas join_left_idempotent= join_semilat.sup_left_idem
    
lemmas meet_aci = meet_assoc meet_comm meet_left_comm meet_left_idempotent
lemmas join_aci = join_assoc join_comm join_left_comm join_left_idempotent

lemmas le_def_meet = meet_semilat.le_iff_inf
lemmas le_def_join = join_semilat.le_iff_sup

lemmas join_absorp2 = join_semilat.sup_absorb2
lemmas join_absorp1 = join_semilat.sup_absorb1

lemmas meet_absorp1 = meet_semilat.inf_absorb1
lemmas meet_absorp2 = meet_semilat.inf_absorb2

interpretation meet_join_lat:
  lattice ["op \<le> \<Colon> 'a\<Colon>{meet_semilorder,join_semilorder} \<Rightarrow> 'a \<Rightarrow> bool" "op <" meet join]
by unfold_locales

lemmas meet_join_absorp = meet_join_lat.inf_sup_absorb
lemmas join_meet_absorp = meet_join_lat.sup_inf_absorb

lemmas distrib_join_le = meet_join_lat.distrib_sup_le
lemmas distrib_meet_le = meet_join_lat.distrib_inf_le

end
