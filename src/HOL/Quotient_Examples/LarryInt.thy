
header{*The Integers as Equivalence Classes over Pairs of Natural Numbers*}

theory LarryInt
imports Main Quotient_Product
begin

fun
  intrel :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool" 
where
  "intrel (x, y) (u, v) = (x + v = u + y)"

quotient_type int = "nat \<times> nat" / intrel
  by (auto simp add: equivp_def expand_fun_eq)

instantiation int :: "{zero, one, plus, uminus, minus, times, ord}"
begin

quotient_definition
  Zero_int_def: "0::int" is "(0::nat, 0::nat)"

quotient_definition
  One_int_def: "1::int" is "(1::nat, 0::nat)"

definition
  "add_raw \<equiv> \<lambda>(x, y) (u, v). (x + (u::nat), y + (v::nat))"

quotient_definition
  "(op +) :: int \<Rightarrow> int \<Rightarrow> int" 
is
  "add_raw"

definition
  "uminus_raw \<equiv> \<lambda>(x::nat, y::nat). (y, x)"

quotient_definition
  "uminus :: int \<Rightarrow> int" 
is
  "uminus_raw"

fun
  mult_raw::"nat \<times> nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<times> nat"
where
  "mult_raw (x, y) (u, v) = (x*u + y*v, x*v + y*u)"

quotient_definition
  "(op *) :: int \<Rightarrow> int \<Rightarrow> int" 
is
  "mult_raw"

definition
  "le_raw \<equiv> \<lambda>(x, y) (u, v). (x+v \<le> u+(y::nat))"

quotient_definition 
  le_int_def: "(op \<le>) :: int \<Rightarrow> int \<Rightarrow> bool" 
is
  "le_raw"

definition
  less_int_def: "z < (w::int) \<equiv> (z \<le> w & z \<noteq> w)"

definition
  diff_int_def:  "z - (w::int) \<equiv> z + (-w)"

instance ..

end

subsection{*Construction of the Integers*}

lemma zminus_zminus_raw:
  "uminus_raw (uminus_raw z) = z"
  by (cases z) (simp add: uminus_raw_def)

lemma [quot_respect]:
  shows "(intrel ===> intrel) uminus_raw uminus_raw"
  by (simp add: uminus_raw_def)
  
lemma zminus_zminus:
  fixes z::"int"
  shows "- (- z) = z"
  by(lifting zminus_zminus_raw)

lemma zminus_0_raw:
  shows "uminus_raw (0, 0) = (0, 0::nat)"
  by (simp add: uminus_raw_def)

lemma zminus_0: 
  shows "- 0 = (0::int)"
  by (lifting zminus_0_raw)

subsection{*Integer Addition*}

lemma zminus_zadd_distrib_raw:
  shows "uminus_raw (add_raw z w) = add_raw (uminus_raw z) (uminus_raw w)"
by (cases z, cases w)
   (auto simp add: add_raw_def uminus_raw_def)

lemma [quot_respect]:
  shows "(intrel ===> intrel ===> intrel) add_raw add_raw"
by (simp add: add_raw_def)

lemma zminus_zadd_distrib: 
  fixes z w::"int"
  shows "- (z + w) = (- z) + (- w)"
  by(lifting zminus_zadd_distrib_raw)

lemma zadd_commute_raw:
  shows "add_raw z w = add_raw w z"
by (cases z, cases w)
   (simp add: add_raw_def)

lemma zadd_commute:
  fixes z w::"int"
  shows "(z::int) + w = w + z"
  by (lifting zadd_commute_raw)

lemma zadd_assoc_raw:
  shows "add_raw (add_raw z1 z2) z3 = add_raw z1 (add_raw z2 z3)"
  by (cases z1, cases z2, cases z3) (simp add: add_raw_def)

lemma zadd_assoc: 
  fixes z1 z2 z3::"int"
  shows "(z1 + z2) + z3 = z1 + (z2 + z3)"
  by (lifting zadd_assoc_raw)

lemma zadd_0_raw:
  shows "add_raw (0, 0) z = z"
  by (simp add: add_raw_def)


text {*also for the instance declaration int :: plus_ac0*}
lemma zadd_0: 
  fixes z::"int"
  shows "0 + z = z"
  by (lifting zadd_0_raw)

lemma zadd_zminus_inverse_raw:
  shows "intrel (add_raw (uminus_raw z) z) (0, 0)"
  by (cases z) (simp add: add_raw_def uminus_raw_def)

lemma zadd_zminus_inverse2: 
  fixes z::"int"
  shows "(- z) + z = 0"
  by (lifting zadd_zminus_inverse_raw)

subsection{*Integer Multiplication*}

lemma zmult_zminus_raw:
  shows "mult_raw (uminus_raw z) w = uminus_raw (mult_raw z w)"
apply(cases z, cases w)
apply(simp add: uminus_raw_def)
done

lemma mult_raw_fst:
  assumes a: "intrel x z"
  shows "intrel (mult_raw x y) (mult_raw z y)"
using a
apply(cases x, cases y, cases z)
apply(auto simp add: mult_raw.simps intrel.simps)
apply(rename_tac u v w x y z)
apply(subgoal_tac "u*w + z*w = y*w + v*w  &  u*x + z*x = y*x + v*x")
apply(simp add: mult_ac)
apply(simp add: add_mult_distrib [symmetric])
done

lemma mult_raw_snd:
  assumes a: "intrel x z"
  shows "intrel (mult_raw y x) (mult_raw y z)"
using a
apply(cases x, cases y, cases z)
apply(auto simp add: mult_raw.simps intrel.simps)
apply(rename_tac u v w x y z)
apply(subgoal_tac "u*w + z*w = y*w + v*w  &  u*x + z*x = y*x + v*x")
apply(simp add: mult_ac)
apply(simp add: add_mult_distrib [symmetric])
done

lemma [quot_respect]:
  shows "(intrel ===> intrel ===> intrel) mult_raw mult_raw"
apply(simp only: fun_rel_def)
apply(rule allI | rule impI)+
apply(rule equivp_transp[OF int_equivp])
apply(rule mult_raw_fst)
apply(assumption)
apply(rule mult_raw_snd)
apply(assumption)
done

lemma zmult_zminus: 
  fixes z w::"int"
  shows "(- z) * w = - (z * w)"
  by (lifting zmult_zminus_raw)

lemma zmult_commute_raw: 
  shows "mult_raw z w = mult_raw w z"
apply(cases z, cases w)
apply(simp add: add_ac mult_ac)
done

lemma zmult_commute: 
  fixes z w::"int"
  shows "z * w = w * z"
  by (lifting zmult_commute_raw)

lemma zmult_assoc_raw:
  shows "mult_raw (mult_raw z1 z2) z3 = mult_raw z1 (mult_raw z2 z3)"
apply(cases z1, cases z2, cases z3)
apply(simp add: add_mult_distrib2 mult_ac)
done

lemma zmult_assoc: 
  fixes z1 z2 z3::"int"
  shows "(z1 * z2) * z3 = z1 * (z2 * z3)"
  by (lifting zmult_assoc_raw)

lemma zadd_mult_distrib_raw:
  shows "mult_raw (add_raw z1 z2) w = add_raw (mult_raw z1 w) (mult_raw z2 w)"
apply(cases z1, cases z2, cases w)
apply(simp add: add_mult_distrib2 mult_ac add_raw_def)
done

lemma zadd_zmult_distrib: 
  fixes z1 z2 w::"int"
  shows "(z1 + z2) * w = (z1 * w) + (z2 * w)"
  by(lifting zadd_mult_distrib_raw)

lemma zadd_zmult_distrib2: 
  fixes w z1 z2::"int"
  shows "w * (z1 + z2) = (w * z1) + (w * z2)"
  by (simp add: zmult_commute [of w] zadd_zmult_distrib)

lemma zdiff_zmult_distrib: 
  fixes w z1 z2::"int"
  shows "(z1 - z2) * w = (z1 * w) - (z2 * w)"
  by (simp add: diff_int_def zadd_zmult_distrib zmult_zminus)

lemma zdiff_zmult_distrib2: 
  fixes w z1 z2::"int"
  shows "w * (z1 - z2) = (w * z1) - (w * z2)"
  by (simp add: zmult_commute [of w] zdiff_zmult_distrib)

lemmas int_distrib =
  zadd_zmult_distrib zadd_zmult_distrib2
  zdiff_zmult_distrib zdiff_zmult_distrib2

lemma zmult_1_raw:
  shows "mult_raw (1, 0) z = z"
  by (cases z) (auto)

lemma zmult_1:
  fixes z::"int"
  shows "1 * z = z"
  by (lifting zmult_1_raw)

lemma zmult_1_right: 
  fixes z::"int"
  shows "z * 1 = z"
  by (rule trans [OF zmult_commute zmult_1])

lemma zero_not_one:
  shows "\<not>(intrel (0, 0) (1::nat, 0::nat))"
  by auto

text{*The Integers Form A Ring*}
instance int :: comm_ring_1
proof
  fix i j k :: int
  show "(i + j) + k = i + (j + k)" by (simp add: zadd_assoc)
  show "i + j = j + i" by (simp add: zadd_commute)
  show "0 + i = i" by (rule zadd_0)
  show "- i + i = 0" by (rule zadd_zminus_inverse2)
  show "i - j = i + (-j)" by (simp add: diff_int_def)
  show "(i * j) * k = i * (j * k)" by (rule zmult_assoc)
  show "i * j = j * i" by (rule zmult_commute)
  show "1 * i = i" by (rule zmult_1) 
  show "(i + j) * k = i * k + j * k" by (simp add: int_distrib)
  show "0 \<noteq> (1::int)" by (lifting zero_not_one)
qed


subsection{*The @{text "\<le>"} Ordering*}

lemma zle_refl_raw:
  shows "le_raw w w"
  by (cases w) (simp add: le_raw_def)

lemma [quot_respect]:
  shows "(intrel ===> intrel ===> op =) le_raw le_raw"
  by (auto) (simp_all add: le_raw_def)

lemma zle_refl: 
  fixes w::"int"
  shows "w \<le> w"
  by (lifting zle_refl_raw)


lemma zle_trans_raw:
  shows "\<lbrakk>le_raw i j; le_raw j k\<rbrakk> \<Longrightarrow> le_raw i k"
apply(cases i, cases j, cases k)
apply(auto simp add: le_raw_def)
done

lemma zle_trans: 
  fixes i j k::"int"
  shows "\<lbrakk>i \<le> j; j \<le> k\<rbrakk> \<Longrightarrow> i \<le> k"
  by (lifting zle_trans_raw)

lemma zle_anti_sym_raw:
  shows "\<lbrakk>le_raw z w; le_raw w z\<rbrakk> \<Longrightarrow> intrel z w"
apply(cases z, cases w)
apply(auto iff: le_raw_def)
done

lemma zle_anti_sym: 
  fixes z w::"int"
  shows "\<lbrakk>z \<le> w; w \<le> z\<rbrakk> \<Longrightarrow> z = w"
  by (lifting zle_anti_sym_raw)


(* Axiom 'order_less_le' of class 'order': *)
lemma zless_le: 
  fixes w z::"int"
  shows "(w < z) = (w \<le> z & w \<noteq> z)"
  by (simp add: less_int_def)

instance int :: order
apply (default)
apply(auto simp add: zless_le zle_anti_sym)[1]
apply(rule zle_refl)
apply(erule zle_trans, assumption)
apply(erule zle_anti_sym, assumption)
done

(* Axiom 'linorder_linear' of class 'linorder': *)

lemma zle_linear_raw:
  shows "le_raw z w \<or> le_raw w z"
apply(cases w, cases z)
apply(auto iff: le_raw_def)
done

lemma zle_linear: 
  fixes z w::"int"
  shows "z \<le> w \<or> w \<le> z"
  by (lifting zle_linear_raw)

instance int :: linorder
apply(default)
apply(rule zle_linear)
done

lemma zadd_left_mono_raw:
  shows "le_raw i j \<Longrightarrow> le_raw (add_raw k i) (add_raw k j)"
apply(cases k)
apply(auto simp add: add_raw_def le_raw_def)
done

lemma zadd_left_mono: 
  fixes i j::"int"
  shows "i \<le> j \<Longrightarrow> k + i \<le> k + j"
  by (lifting zadd_left_mono_raw)


subsection{*Magnitide of an Integer, as a Natural Number: @{term nat}*}

definition
  "nat_raw \<equiv> \<lambda>(x, y).x - (y::nat)"

quotient_definition
  "nat2::int \<Rightarrow> nat"
is
  "nat_raw"

abbreviation
  "less_raw x y \<equiv> (le_raw x y \<and> \<not>(intrel x y))"

lemma nat_le_eq_zle_raw:
  shows "less_raw (0, 0) w \<or> le_raw (0, 0) z \<Longrightarrow> (nat_raw w \<le> nat_raw z) = (le_raw w z)"
  apply (cases w)
  apply (cases z)
  apply (simp add: nat_raw_def le_raw_def)
  by auto

lemma [quot_respect]:
  shows "(intrel ===> op =) nat_raw nat_raw"
  by (auto iff: nat_raw_def)

lemma nat_le_eq_zle: 
  fixes w z::"int"
  shows "0 < w \<or> 0 \<le> z \<Longrightarrow> (nat2 w \<le> nat2 z) = (w\<le>z)"
  unfolding less_int_def
  by (lifting nat_le_eq_zle_raw)

end
