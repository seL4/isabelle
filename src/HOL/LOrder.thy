(*  Title:   HOL/LOrder.thy
    ID:      $Id$
    Author:  Steven Obua, TU Muenchen
    License: GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Lattice Orders *}

theory LOrder = HOL:

text {*
  The theory of lattices developed here is taken from the book:
  \begin{itemize}
  \item \emph{Lattice Theory} by Garret Birkhoff, American Mathematical Society 1979. 
  \end{itemize}
*}

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

lemma meet_imp_le: "x \<le> a \<Longrightarrow> x \<le> b \<Longrightarrow> x \<le> meet a (b::'a::meet_semilorder)"
by (insert is_meet_meet, auto simp add: is_meet_def)

lemma join_left_le: "a \<le> join a (b::'a::join_semilorder)"
by (insert is_join_join, auto simp add: is_join_def)

lemma join_right_le: "b \<le> join a (b::'a::join_semilorder)"
by (insert is_join_join, auto simp add: is_join_def)

lemma join_imp_le: "a \<le> x \<Longrightarrow> b \<le> x \<Longrightarrow> join a b \<le> (x::'a::join_semilorder)"
by (insert is_join_join, auto simp add: is_join_def)

lemmas meet_join_le = meet_left_le meet_right_le join_left_le join_right_le

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
by (rule order_antisym, simp_all add: meet_left_le meet_imp_le)

lemma join_idempotent[simp]: "join x x = x"
by (rule order_antisym, simp_all add: join_left_le join_imp_le)

lemma meet_comm: "meet x y = meet y x" 
by (rule order_antisym, (simp add: meet_left_le meet_right_le meet_imp_le)+)

lemma join_comm: "join x y = join y x"
by (rule order_antisym, (simp add: join_right_le join_left_le join_imp_le)+)

lemma meet_assoc: "meet (meet x y) z = meet x (meet y z)" (is "?l=?r")
proof - 
  have "?l <= meet x y & meet x y <= x & ?l <= z & meet x y <= y" by (simp add: meet_left_le meet_right_le)
  hence "?l <= x & ?l <= y & ?l <= z" by auto
  hence "?l <= ?r" by (simp add: meet_imp_le)
  hence a:"?l <= meet x (meet y z)" by (simp add: meet_imp_le)
  have "?r <= meet y z & meet y z <= y & meet y z <= z & ?r <= x" by (simp add: meet_left_le meet_right_le)  
  hence "?r <= x & ?r <= y & ?r <= z" by (auto) 
  hence "?r <= meet x y & ?r <= z" by (simp add: meet_imp_le)
  hence b:"?r <= ?l" by (simp add: meet_imp_le)
  from a b show "?l = ?r" by auto
qed

lemma join_assoc: "join (join x y) z = join x (join y z)" (is "?l=?r")
proof -
  have "join x y <= ?l & x <= join x y & z <= ?l & y <= join x y" by (simp add: join_left_le join_right_le)
  hence "x <= ?l & y <= ?l & z <= ?l" by auto
  hence "join y z <= ?l & x <= ?l" by (simp add: join_imp_le)
  hence a:"?r <= ?l" by (simp add: join_imp_le)
  have "join y z <= ?r & y <= join y z & z <= join y z & x <= ?r" by (simp add: join_left_le join_right_le)
  hence "y <= ?r & z <= ?r & x <= ?r" by auto
  hence "join x y <= ?r & z <= ?r" by (simp add: join_imp_le)
  hence b:"?l <= ?r" by (simp add: join_imp_le)
  from a b show "?l = ?r" by auto
qed

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
proof -
  have u: "x <= y \<longrightarrow> meet x y = x"
  proof 
    assume "x <= y"
    hence "x <= meet x y & meet x y <= x" by (simp add: meet_imp_le meet_left_le)
    thus "meet x y = x" by auto
  qed
  have v:"meet x y = x \<longrightarrow> x <= y" 
  proof 
    have a:"meet x y <= y" by (simp add: meet_right_le)
    assume "meet x y = x"
    hence "x = meet x y" by auto
    with a show "x <= y" by (auto)
  qed
  from u v show ?thesis by blast
qed

lemma le_def_join: "(x <= y) = (join x y = y)" 
proof -
  have u: "x <= y \<longrightarrow> join x y = y"
  proof 
    assume "x <= y"
    hence "join x y <= y & y <= join x y" by (simp add: join_imp_le join_right_le)
    thus "join x y = y" by auto
  qed
  have v:"join x y = y \<longrightarrow> x <= y" 
  proof 
    have a:"x <= join x y" by (simp add: join_left_le)
    assume "join x y = y"
    hence "y = join x y" by auto
    with a show "x <= y" by (auto)
  qed
  from u v show ?thesis by blast
qed

lemma meet_join_absorp: "meet x (join x y) = x"
proof -
  have a:"meet x (join x y) <= x" by (simp add: meet_left_le)
  have b:"x <= meet x (join x y)" by (rule meet_imp_le, simp_all add: join_left_le)
  from a b show ?thesis by auto
qed

lemma join_meet_absorp: "join x (meet x y) = x"
proof - 
  have a:"x <= join x (meet x y)" by (simp add: join_left_le)
  have b:"join x (meet x y) <= x" by (rule join_imp_le, simp_all add: meet_left_le)
  from a b show ?thesis by auto
qed

lemma meet_mono: "y \<le> z \<Longrightarrow> meet x y \<le> meet x z"
proof -
  assume a: "y <= z"
  have "meet x y <= x & meet x y <= y" by (simp add: meet_left_le meet_right_le)
  with a have "meet x y <= x & meet x y <= z" by auto 
  thus "meet x y <= meet x z" by (simp add: meet_imp_le)
qed

lemma join_mono: "y \<le> z \<Longrightarrow> join x y \<le> join x z"
proof -
  assume a: "y \<le> z"
  have "x <= join x z & z <= join x z" by (simp add: join_left_le join_right_le)
  with a have "x <= join x z & y <= join x z" by auto
  thus "join x y <= join x z" by (simp add: join_imp_le)
qed

lemma distrib_join_le: "join x (meet y z) \<le> meet (join x y) (join x z)" (is "_ <= ?r")
proof -
  have a: "x <= ?r" by (rule meet_imp_le, simp_all add: join_left_le)
  from meet_join_le have b: "meet y z <= ?r" 
    by (rule_tac meet_imp_le, (blast intro: order_trans)+)
  from a b show ?thesis by (simp add: join_imp_le)
qed
  
lemma distrib_meet_le: "join (meet x y) (meet x z) \<le> meet x (join y z)" (is "?l <= _") 
proof -
  have a: "?l <= x" by (rule join_imp_le, simp_all add: meet_left_le)
  from meet_join_le have b: "?l <= join y z" 
    by (rule_tac join_imp_le, (blast intro: order_trans)+)
  from a b show ?thesis by (simp add: meet_imp_le)
qed

lemma meet_join_eq_imp_le: "a = c \<or> a = d \<or> b = c \<or> b = d \<Longrightarrow> meet a b \<le> join c d"
by (insert meet_join_le, blast intro: order_trans)

lemma modular_le: "x \<le> z \<Longrightarrow> join x (meet y z) \<le> meet (join x y) z" (is "_ \<Longrightarrow> ?t <= _")
proof -
  assume a: "x <= z"
  have b: "?t <= join x y" by (rule join_imp_le, simp_all add: meet_join_le meet_join_eq_imp_le)
  have c: "?t <= z" by (rule join_imp_le, simp_all add: meet_join_le a)
  from b c show ?thesis by (simp add: meet_imp_le)
qed

ML {*
val is_meet_unique = thm "is_meet_unique";
val is_join_unique = thm "is_join_unique";
val join_exists = thm "join_exists";
val meet_exists = thm "meet_exists";
val is_meet_meet = thm "is_meet_meet";
val meet_unique = thm "meet_unique";
val is_join_join = thm "is_join_join";
val join_unique = thm "join_unique";
val meet_left_le = thm "meet_left_le";
val meet_right_le = thm "meet_right_le";
val meet_imp_le = thm "meet_imp_le";
val join_left_le = thm "join_left_le";
val join_right_le = thm "join_right_le";
val join_imp_le = thm "join_imp_le";
val meet_join_le = thms "meet_join_le";
val is_meet_min = thm "is_meet_min";
val is_join_max = thm "is_join_max";
val meet_min = thm "meet_min";
val join_max = thm "join_max";
val meet_idempotent = thm "meet_idempotent";
val join_idempotent = thm "join_idempotent";
val meet_comm = thm "meet_comm";
val join_comm = thm "join_comm";
val meet_assoc = thm "meet_assoc";
val join_assoc = thm "join_assoc";
val meet_left_comm = thm "meet_left_comm";
val meet_left_idempotent = thm "meet_left_idempotent";
val join_left_comm = thm "join_left_comm";
val join_left_idempotent = thm "join_left_idempotent";
val meet_aci = thms "meet_aci";
val join_aci = thms "join_aci";
val le_def_meet = thm "le_def_meet";
val le_def_join = thm "le_def_join";
val meet_join_absorp = thm "meet_join_absorp";
val join_meet_absorp = thm "join_meet_absorp";
val meet_mono = thm "meet_mono";
val join_mono = thm "join_mono";
val distrib_join_le = thm "distrib_join_le";
val distrib_meet_le = thm "distrib_meet_le";
val meet_join_eq_imp_le = thm "meet_join_eq_imp_le";
val modular_le = thm "modular_le";
*}

end