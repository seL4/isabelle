(*  Title:      HOL/Library/DenumRat.thy
    ID:         $Id$
    Author:     Benjamin Porter, 2006
*)

header "Denumerability of the Rationals"

theory DenumRat
imports
  Complex_Main NatPair
begin

lemma nat_to_int_surj: "\<exists>f::nat\<Rightarrow>int. surj f"
proof
  let ?f = "\<lambda>n. if (n mod 2 = 0) then - int (n div 2) else int ((n - 1) div 2 + 1)"
  have "\<forall>y. \<exists>x. y = ?f x"
  proof
    fix y::int
    {
      assume yl0: "y \<le> 0"
      then obtain n where ndef: "n = nat (- y * 2)" by simp
      from yl0 have g0: "- y * 2 \<ge> 0" by simp
      hence "nat (- y * 2) mod (nat 2) = nat ((-y * 2) mod 2)" by (subst nat_mod_distrib, auto)
      moreover have "(-y * 2) mod 2 = 0" by arith
      ultimately have "nat (- y * 2) mod 2 = 0" by simp
      with ndef have "n mod 2 = 0" by simp
      hence "?f n = - int (n div 2)" by simp
      also with ndef have "\<dots> = - int (nat (-y * 2) div 2)" by simp
      also with g0 have "\<dots> = - int (nat (((-y) * 2) div 2))" using nat_div_distrib by auto
      also have "\<dots> = - int (nat (-y))" using zdiv_zmult_self1 [of "2" "- y"]
        by simp
      also from yl0 have "\<dots> = y" using nat_0_le by auto
      finally have "?f n = y" .
      hence "\<exists>x. y = ?f x" by blast
    }
    moreover
    {
      assume "\<not>(y \<le> 0)"
      hence yg0: "y > 0" by simp
      hence yn0: "y \<noteq> 0" by simp
      from yg0 have g0: "y*2 + -2 \<ge> 0" by arith
      from yg0 obtain n where ndef: "n = nat (y * 2 - 1)" by simp
      from yg0 have "nat (y*2 - 1) mod 2 = nat ((y*2 - 1) mod 2)" using nat_mod_distrib by auto
      also have "\<dots> = nat ((y*2 + - 1) mod 2)" by (auto simp add: diff_int_def)
      also have "\<dots> = nat (1)" by (auto simp add: zmod_zadd_left_eq)
      finally have "n mod 2 = 1" using ndef by auto
      hence "?f n = int ((n - 1) div 2 + 1)" by simp
      also with ndef have "\<dots> = int ((nat (y*2 - 1) - 1) div 2 + 1)" by simp
      also with yg0 have "\<dots> = int (nat (y*2 - 2) div 2 + 1)" by arith
      also have "\<dots> = int (nat (y*2 + -2) div 2 + 1)" by (simp add: diff_int_def)
      also have "\<dots> = int (nat (y*2 + -2) div (nat 2) + 1)" by auto
      also from g0 have "\<dots> = int (nat ((y*2 + -2) div 2) + 1)"
        using nat_div_distrib by auto
      also have "\<dots> = int (nat ((y*2) div 2 + (-2) div 2 + ((y*2) mod 2 + (-2) mod 2) div 2) + 1)"
        by (auto simp add: zdiv_zadd1_eq)
      also from yg0 g0 have "\<dots> = int (nat (y))"
        by (auto)
      finally have "?f n = y" using yg0 by auto
      hence "\<exists>x. y = ?f x" by blast
    }
    ultimately show "\<exists>x. y = ?f x" by (rule case_split)
  qed
  thus "surj ?f" by (fold surj_def)
qed

lemma nat2_to_int2_surj: "\<exists>f::(nat*nat)\<Rightarrow>(int*int). surj f"
proof -
  from nat_to_int_surj obtain g::"nat\<Rightarrow>int" where "surj g" ..
  hence aux: "\<forall>y. \<exists>x. y = g x" by (unfold surj_def)
  let ?f = "\<lambda>n. (g (fst n), g (snd n))"
  {
    fix y::"(int*int)"
    from aux have "\<exists>x1 x2. fst y = g x1 \<and> snd y = g x2" by auto
    hence "\<exists>x. fst y = g (fst x) \<and> snd y = g (snd x)" by auto
    hence "\<exists>x. (fst y, snd y) = (g (fst x), g (snd x))" by blast
    hence "\<exists>x. y = ?f x" by auto
  }
  hence "\<forall>y. \<exists>x. y = ?f x" by auto
  hence "surj ?f" by (fold surj_def)
  thus ?thesis by auto
qed

lemma rat_denum:
  "\<exists>f::nat\<Rightarrow>rat. surj f"
proof -
  have "inj nat2_to_nat" by (rule nat2_to_nat_inj)
  hence "surj (inv nat2_to_nat)" by (rule inj_imp_surj_inv)
  moreover from nat2_to_int2_surj obtain h::"(nat*nat)\<Rightarrow>(int*int)" where "surj h" ..
  ultimately have "surj (h o (inv nat2_to_nat))" by (rule comp_surj)
  hence "\<exists>f::nat\<Rightarrow>(int*int). surj f" by auto
  then obtain g::"nat\<Rightarrow>(int*int)" where "surj g" by auto  
  hence gdef: "\<forall>y. \<exists>x. y = g x" by (unfold surj_def)  
  {
    fix y
    obtain a b where y: "y = Fract a b" by (cases y)
    from gdef
    obtain x where "(a,b) = g x" by blast
    hence "g x = (a,b)" ..
    with y have "y = (split Fract o g) x" by simp 
    hence "\<exists>x. y = (split Fract o g) x" ..
  }
  hence "surj (split Fract o g)" 
    by (simp add: surj_def)
  thus ?thesis by blast
qed


end