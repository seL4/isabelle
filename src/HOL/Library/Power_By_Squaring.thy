(*
  File:     Power_By_Squaring.thy
  Author:   Manuel Eberl, TU München
  
  Fast computing of funpow (applying some functon n times) for weakly associative binary
  functions using exponentiation by squaring. Yields efficient exponentiation algorithms on
  monoid_mult and for modular exponentiation "b ^ e mod m" (and thus also for "cong")
*)
section \<open>Exponentiation by Squaring\<close>
theory Power_By_Squaring
  imports Main
begin

context
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

function efficient_funpow :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "efficient_funpow y x 0 = y"
| "efficient_funpow y x (Suc 0) = f x y"
| "n \<noteq> 0 \<Longrightarrow> even n \<Longrightarrow> efficient_funpow y x n = efficient_funpow y (f x x) (n div 2)"
| "n \<noteq> 1 \<Longrightarrow> odd n \<Longrightarrow> efficient_funpow y x n = efficient_funpow (f x y) (f x x) (n div 2)"
  by force+
termination by (relation "measure (snd \<circ> snd)") (auto elim: oddE)

lemma efficient_funpow_code [code]:
  "efficient_funpow y x n =
     (if n = 0 then y
      else if n = 1 then f x y
      else if even n then efficient_funpow y (f x x) (n div 2)
      else efficient_funpow (f x y) (f x x) (n div 2))"
  by (induction y x n rule: efficient_funpow.induct) auto

end

lemma efficient_funpow_correct:
  assumes f_assoc: "\<And>x z. f x (f x z) = f (f x x) z"
  shows "efficient_funpow f y x n = (f x ^^ n) y"
proof -
  have [simp]: "f ^^ 2 = (\<lambda>x. f (f x))" for f :: "'a \<Rightarrow> 'a"
    by (simp add: eval_nat_numeral o_def)
  show ?thesis
    by (induction y x n rule: efficient_funpow.induct[of _ f])
       (auto elim!: evenE oddE simp: funpow_mult [symmetric] funpow_Suc_right f_assoc
             simp del: funpow.simps(2))
qed

(*
  TODO: This could be used as a code_unfold rule or something like that but the
  implications are not quite clear. Would this be a good default implementation
  for powers?
*)
context monoid_mult
begin

lemma power_by_squaring: "efficient_funpow (*) (1 :: 'a) = (^)"
proof (intro ext)
  fix x :: 'a and n
  have "efficient_funpow (*) 1 x n = ((*) x ^^ n) 1"
    by (subst efficient_funpow_correct) (simp_all add: mult.assoc)
  also have "\<dots> = x ^ n"
    by (induction n) simp_all
  finally show "efficient_funpow (*) 1 x n = x ^ n" .
qed

end

end
