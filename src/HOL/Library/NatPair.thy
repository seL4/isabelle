(*  Title:      HOL/Library/NatPair.thy
    ID:         $Id$
    Author:     Stefan Richter
    Copyright   2003 Technische Universitaet Muenchen
*)

header {*
  \title{Pairs of Natural Numbers}
  \author{Stefan Richter}
*}

theory NatPair = Main:

text{*An injective function from $\mathbf{N}^2$ to
  $\mathbf{N}$.  Definition and proofs are from 
  Arnold Oberschelp.  Rekursionstheorie.  BI-Wissenschafts-Verlag, 1993
  (page 85).  *}

constdefs 
  nat2_to_nat:: "(nat * nat) \<Rightarrow> nat"
  "nat2_to_nat pair \<equiv> let (n,m) = pair in (n+m) * Suc (n+m) div 2 + n"

lemma dvd2_a_x_suc_a: "2 dvd a * (Suc a)" 
proof (cases "2 dvd a") 
  case True
  thus ?thesis by (rule dvd_mult2)
next
  case False 
  hence "Suc (a mod 2) = 2" by (simp add: dvd_eq_mod_eq_0)
  hence "Suc a mod 2 = 0" by (simp add: mod_Suc) 
  hence "2 dvd Suc a" by (simp only:dvd_eq_mod_eq_0) 
  thus ?thesis by (rule dvd_mult)
qed

lemma assumes eq: "nat2_to_nat (u,v) = nat2_to_nat (x,y)" 
  shows nat2_to_nat_help: "u+v \<le> x+y"
proof (rule classical)
  assume "\<not> ?thesis"
  hence contrapos: "x+y < u+v" 
    by simp
  have "nat2_to_nat (x,y) < (x+y) * Suc (x+y) div 2 + Suc (x + y)" 
    by (unfold nat2_to_nat_def) (simp add: Let_def)
  also have "\<dots> = (x+y)*Suc(x+y) div 2 + 2 * Suc(x+y) div 2" 
    by (simp only: div_mult_self1_is_m) 
  also have "\<dots> = (x+y)*Suc(x+y) div 2 + 2 * Suc(x+y) div 2 
    + ((x+y)*Suc(x+y) mod 2 + 2 * Suc(x+y) mod 2) div 2" 
  proof -
    have "2 dvd (x+y)*Suc(x+y)" 
      by (rule dvd2_a_x_suc_a)
    hence "(x+y)*Suc(x+y) mod 2 = 0" 
      by (simp only: dvd_eq_mod_eq_0)
    also
    have "2 * Suc(x+y) mod 2 = 0" 
      by (rule mod_mult_self1_is_0)
    ultimately have 
      "((x+y)*Suc(x+y) mod 2 + 2 * Suc(x+y) mod 2) div 2 = 0" 
      by simp 
    thus ?thesis 
      by simp
  qed 
  also have "\<dots> = ((x+y)*Suc(x+y) + 2*Suc(x+y)) div 2" 
    by (rule div_add1_eq[THEN sym])
  also have "\<dots> = ((x+y+2)*Suc(x+y)) div 2" 
    by (simp only: add_mult_distrib[THEN sym])
  also from contrapos have "\<dots> \<le> ((Suc(u+v))*(u+v)) div 2" 
    by (simp only: mult_le_mono div_le_mono) 
  also have "\<dots> \<le> nat2_to_nat (u,v)" 
    by (unfold nat2_to_nat_def) (simp add: Let_def)
  finally show ?thesis 
    by (simp only: eq)
qed

lemma nat2_to_nat_inj: "inj nat2_to_nat"
proof -
  {fix u v x y assume "nat2_to_nat (u,v) = nat2_to_nat (x,y)"
    hence "u+v \<le> x+y" by (rule nat2_to_nat_help)
    also from prems[THEN sym] have "x+y \<le> u+v" 
      by (rule nat2_to_nat_help)
    finally have eq: "u+v = x+y" .
    with prems have ux: "u=x" 
      by (simp add: nat2_to_nat_def Let_def)
    with eq have vy: "v=y" 
      by simp
    with ux have "(u,v) = (x,y)" 
      by simp
  }
  hence "\<And>x y. nat2_to_nat x = nat2_to_nat y \<Longrightarrow> x=y" 
    by fast
  thus ?thesis 
    by (unfold inj_on_def) simp
qed

end
