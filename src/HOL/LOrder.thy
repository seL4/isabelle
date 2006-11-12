(*  Title:   HOL/LOrder.thy
    ID:      $Id$
    Author:  Steven Obua, TU Muenchen
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

lemma meet_left_le: "meet a b \<le> (a::'a::meet_semilorder)"
by (insert is_meet_meet, auto simp add: is_meet_def)

lemma meet_right_le: "meet a b \<le> (b::'a::meet_semilorder)"
by (insert is_meet_meet, auto simp add: is_meet_def)

(* intro! breaks a proof in Hyperreal/SEQ and NumberTheory/IntPrimes *)
lemma le_meetI:
 "x \<le> a \<Longrightarrow> x \<le> b \<Longrightarrow> x \<le> meet a (b::'a::meet_semilorder)"
by (insert is_meet_meet, auto simp add: is_meet_def)

lemma join_left_le: "a \<le> join a (b::'a::join_semilorder)"
by (insert is_join_join, auto simp add: is_join_def)

lemma join_right_le: "b \<le> join a (b::'a::join_semilorder)"
by (insert is_join_join, auto simp add: is_join_def)

lemma join_leI:
 "a \<le> x \<Longrightarrow> b \<le> x \<Longrightarrow> join a b \<le> (x::'a::join_semilorder)"
by (insert is_join_join, auto simp add: is_join_def)

lemmas meet_join_le[simp] = meet_left_le meet_right_le join_left_le join_right_le

lemma le_meet[simp]: "(x <= meet y z) = (x <= y & x <= z)" (is "?L = ?R")
proof
  assume ?L
  moreover have "meet y z \<le> y" "meet y z <= z" by(simp_all)
  ultimately show ?R by(blast intro:order_trans)
next
  assume ?R thus ?L by (blast intro!:le_meetI)
qed

lemma join_le[simp]: "(join x y <= z) = (x <= z & y <= z)" (is "?L = ?R")
proof
  assume ?L
  moreover have "x \<le> join x y" "y \<le> join x y" by(simp_all)
  ultimately show ?R by(blast intro:order_trans)
next
  assume ?R thus ?L by (blast intro:join_leI)
qed


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

lemma meet_idempotent[simp]: "meet x x = x"
by (rule order_antisym, simp_all add: le_meetI)

lemma join_idempotent[simp]: "join x x = x"
by (rule order_antisym, simp_all add: join_leI)

lemma meet_comm: "meet x y = meet y x" 
by (rule order_antisym, (simp add: le_meetI)+)

lemma join_comm: "join x y = join y x"
by (rule order_antisym, (simp add: join_leI)+)

lemma meet_leI1: "x \<le> z \<Longrightarrow> meet x y \<le> z"
apply(subgoal_tac "meet x y <= x")
 apply(blast intro:order_trans)
apply simp
done

lemma meet_leI2: "y \<le> z \<Longrightarrow> meet x y \<le> z"
apply(subgoal_tac "meet x y <= y")
 apply(blast intro:order_trans)
apply simp
done

lemma le_joinI1: "x \<le> y \<Longrightarrow> x \<le> join y z"
apply(subgoal_tac "y <= join y z")
 apply(blast intro:order_trans)
apply simp
done

lemma le_joinI2: "x \<le> z \<Longrightarrow> x \<le> join y z"
apply(subgoal_tac "z <= join y z")
 apply(blast intro:order_trans)
apply simp
done

lemma meet_assoc: "meet (meet x y) z = meet x (meet y z)"
apply(rule order_antisym)
apply (simp add:meet_leI1 meet_leI2)
apply (simp add:meet_leI1 meet_leI2)
done

lemma join_assoc: "join (join x y) z = join x (join y z)"
apply(rule order_antisym)
apply (simp add:le_joinI1 le_joinI2)
apply (simp add:le_joinI1 le_joinI2)
done

lemma meet_left_comm: "meet a (meet b c) = meet b (meet a c)"
by (simp add: meet_assoc[symmetric, of a b c], simp add: meet_comm[of a b], simp add: meet_assoc)

lemma meet_left_idempotent: "meet y (meet y x) = meet y x"
by (simp add: meet_assoc meet_comm meet_left_comm)

lemma join_left_comm: "join a (join b c) = join b (join a c)"
by (simp add: join_assoc[symmetric, of a b c], simp add: join_comm[of a b], simp add: join_assoc)

lemma join_left_idempotent: "join y (join y x) = join y x"
by (simp add: join_assoc join_comm join_left_comm)
    
lemmas meet_aci = meet_assoc meet_comm meet_left_comm meet_left_idempotent

lemmas join_aci = join_assoc join_comm join_left_comm join_left_idempotent

lemma le_def_meet: "(x <= y) = (meet x y = x)"
apply rule
apply(simp add: order_antisym)
apply(subgoal_tac "meet x y <= y")
apply(simp)
apply(simp (no_asm))
done

lemma le_def_join: "(x <= y) = (join x y = y)"
apply rule
apply(simp add: order_antisym)
apply(subgoal_tac "x <= join x y")
apply(simp)
apply(simp (no_asm))
done

lemma join_absorp2: "a \<le> b \<Longrightarrow> join a b = b" 
by (simp add: le_def_join)

lemma join_absorp1: "b \<le> a \<Longrightarrow> join a b = a"
by (simp add: le_def_join join_aci)

lemma meet_absorp1: "a \<le> b \<Longrightarrow> meet a b = a"
by (simp add: le_def_meet)

lemma meet_absorp2: "b \<le> a \<Longrightarrow> meet a b = b"
by (simp add: le_def_meet meet_aci)

lemma meet_join_absorp: "meet x (join x y) = x"
by(simp add:meet_absorp1)

lemma join_meet_absorp: "join x (meet x y) = x"
by(simp add:join_absorp1)

lemma meet_mono: "y \<le> z \<Longrightarrow> meet x y \<le> meet x z"
by(simp add:meet_leI2)

lemma join_mono: "y \<le> z \<Longrightarrow> join x y \<le> join x z"
by(simp add:le_joinI2)

lemma distrib_join_le: "join x (meet y z) \<le> meet (join x y) (join x z)" (is "_ <= ?r")
proof -
  have a: "x <= ?r" by (simp_all add:le_meetI)
  have b: "meet y z <= ?r" by (simp add:le_joinI2)
  from a b show ?thesis by (simp add: join_leI)
qed
  
lemma distrib_meet_le: "join (meet x y) (meet x z) \<le> meet x (join y z)" (is "?l <= _")
proof -
  have a: "?l <= x" by (simp_all add: join_leI)
  have b: "?l <= join y z" by (simp add:meet_leI2)
  from a b show ?thesis by (simp add: le_meetI)
qed

lemma meet_join_eq_imp_le: "a = c \<or> a = d \<or> b = c \<or> b = d \<Longrightarrow> meet a b \<le> join c d"
by (auto simp:meet_leI2 meet_leI1)

lemma modular_le: "x \<le> z \<Longrightarrow> join x (meet y z) \<le> meet (join x y) z" (is "_ \<Longrightarrow> ?t <= _")
proof -
  assume a: "x <= z"
  have b: "?t <= join x y" by (simp_all add: join_leI meet_join_eq_imp_le )
  have c: "?t <= z" by (simp_all add: a join_leI)
  from b c show ?thesis by (simp add: le_meetI)
qed

end
