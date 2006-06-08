(*  Title:      HOL/ex/PresburgerEx.thy
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen
*)

header {* Some examples for Presburger Arithmetic *}

theory PresburgerEx imports Main begin

theorem "(\<forall>(y::int). 3 dvd y) ==> \<forall>(x::int). b < x --> a \<le> x"
  by presburger

theorem "!! (y::int) (z::int) (n::int). 3 dvd z ==> 2 dvd (y::int) ==>
  (\<exists>(x::int).  2*x =  y) & (\<exists>(k::int). 3*k = z)"
  by presburger

theorem "!! (y::int) (z::int) n. Suc(n::nat) < 6 ==>  3 dvd z ==>
  2 dvd (y::int) ==> (\<exists>(x::int).  2*x =  y) & (\<exists>(k::int). 3*k = z)"
  by presburger

theorem "\<forall>(x::nat). \<exists>(y::nat). (0::nat) \<le> 5 --> y = 5 + x "
  by presburger

text{*Very slow: about 55 seconds on a 1.8GHz machine.*}
theorem "\<forall>(x::nat). \<exists>(y::nat). y = 5 + x | x div 6 + 1= 2"
  by presburger

theorem "\<exists>(x::int). 0 < x"
  by presburger

theorem "\<forall>(x::int) y. x < y --> 2 * x + 1 < 2 * y"
  by presburger
 
theorem "\<forall>(x::int) y. 2 * x + 1 \<noteq> 2 * y"
  by presburger
 
theorem "\<exists>(x::int) y. 0 < x  & 0 \<le> y  & 3 * x - 5 * y = 1"
  by presburger

theorem "~ (\<exists>(x::int) (y::int) (z::int). 4*x + (-6::int)*y = 1)"
  by presburger

theorem "\<forall>(x::int). b < x --> a \<le> x"
  apply (presburger (no_quantify))
  oops

theorem "~ (\<exists>(x::int). False)"
  by presburger

theorem "\<forall>(x::int). (a::int) < 3 * x --> b < 3 * x"
  apply (presburger (no_quantify))
  oops

theorem "\<forall>(x::int). (2 dvd x) --> (\<exists>(y::int). x = 2*y)"
  by presburger 

theorem "\<forall>(x::int). (2 dvd x) --> (\<exists>(y::int). x = 2*y)"
  by presburger 

theorem "\<forall>(x::int). (2 dvd x) = (\<exists>(y::int). x = 2*y)"
  by presburger 

theorem "\<forall>(x::int). ((2 dvd x) = (\<forall>(y::int). x \<noteq> 2*y + 1))"
  by presburger 

theorem "~ (\<forall>(x::int). 
            ((2 dvd x) = (\<forall>(y::int). x \<noteq> 2*y+1) | 
             (\<exists>(q::int) (u::int) i. 3*i + 2*q - u < 17)
             --> 0 < x | ((~ 3 dvd x) &(x + 8 = 0))))"
  by presburger
 
theorem "~ (\<forall>(i::int). 4 \<le> i --> (\<exists>x y. 0 \<le> x & 0 \<le> y & 3 * x + 5 * y = i))"
  by presburger

theorem "\<forall>(i::int). 8 \<le> i --> (\<exists>x y. 0 \<le> x & 0 \<le> y & 3 * x + 5 * y = i)"
  by presburger

theorem "\<exists>(j::int). \<forall>i. j \<le> i --> (\<exists>x y. 0 \<le> x & 0 \<le> y & 3 * x + 5 * y = i)"
  by presburger

theorem "~ (\<forall>j (i::int). j \<le> i --> (\<exists>x y. 0 \<le> x & 0 \<le> y & 3 * x + 5 * y = i))"
  by presburger

text{*Very slow: about 80 seconds on a 1.8GHz machine.*}
theorem "(\<exists>m::nat. n = 2 * m) --> (n + 1) div 2 = n div 2"
  by presburger

theorem "(\<exists>m::int. n = 2 * m) --> (n + 1) div 2 = n div 2"
  by presburger

text{* This following theorem proves that all solutions to the
recurrence relation $x_{i+2} = |x_{i+1}| - x_i$ are periodic with
period 9.  The example was brought to our attention by John
Harrison. It does does not require Presburger arithmetic but merely
quantifier-free linear arithmetic and holds for the rationals as well.

Warning: it takes (in 2006) over 5 minutes! *}

lemma "\<lbrakk> x3 = abs x2 - x1; x4 = abs x3 - x2; x5 = abs x4 - x3;
         x6 = abs x5 - x4; x7 = abs x6 - x5; x8 = abs x7 - x6;
         x9 = abs x8 - x7; x10 = abs x9 - x8; x11 = abs x10 - x9 \<rbrakk>
 \<Longrightarrow> x1 = x10 & x2 = (x11::int)"
by arith

end
