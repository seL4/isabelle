(*  Title:      HOL/Divides.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

The division operators div, mod and the divides relation "dvd"
*)

theory Divides = NatArith files("Divides_lemmas.ML"):

(*We use the same class for div and mod;
  moreover, dvd is defined whenever multiplication is*)
axclass
  div < type

instance  nat :: div ..
instance  nat :: plus_ac0
proof qed (rule add_commute add_assoc add_0)+

consts
  div  :: "'a::div \<Rightarrow> 'a \<Rightarrow> 'a"          (infixl 70)
  mod  :: "'a::div \<Rightarrow> 'a \<Rightarrow> 'a"          (infixl 70)
  dvd  :: "'a::times \<Rightarrow> 'a \<Rightarrow> bool"      (infixl 50)


defs

  mod_def:   "m mod n == wfrec (trancl pred_nat)
                          (%f j. if j<n | n=0 then j else f (j-n)) m"

  div_def:   "m div n == wfrec (trancl pred_nat) 
                          (%f j. if j<n | n=0 then 0 else Suc (f (j-n))) m"

(*The definition of dvd is polymorphic!*)
  dvd_def:   "m dvd n == EX k. n = m*k"

(*This definition helps prove the harder properties of div and mod.
  It is copied from IntDiv.thy; should it be overloaded?*)
constdefs
  quorem :: "(nat*nat) * (nat*nat) => bool"
    "quorem == %((a,b), (q,r)).
                      a = b*q + r &
                      (if 0<b then 0<=r & r<b else b<r & r <=0)"

use "Divides_lemmas.ML"

lemma mod_div_equality2: "n * (m div n) + m mod n = (m::nat)"
apply(insert mod_div_equality[of m n])
apply(simp only:mult_ac)
done

lemma split_div:
assumes m: "m \<noteq> 0"
shows "P(n div m :: nat) = (!i. !j<m. n = m*i + j \<longrightarrow> P i)"
       (is "?P = ?Q")
proof
  assume P: ?P
  show ?Q
  proof (intro allI impI)
    fix i j
    assume n: "n = m*i + j" and j: "j < m"
    show "P i"
    proof (cases)
      assume "i = 0"
      with n j P show "P i" by simp
    next
      assume "i \<noteq> 0"
      with n j P show "P i" by (simp add:add_ac div_mult_self1)
    qed
  qed
next
  assume Q: ?Q
  from m Q[THEN spec,of "n div m",THEN spec, of "n mod m"]
  show ?P by(simp add:mod_div_equality2)
qed

lemma split_mod:
assumes m: "m \<noteq> 0"
shows "P(n mod m :: nat) = (!i. !j<m. n = m*i + j \<longrightarrow> P j)"
       (is "?P = ?Q")
proof
  assume P: ?P
  show ?Q
  proof (intro allI impI)
    fix i j
    assume "n = m*i + j" "j < m"
    thus "P j" using m P by(simp add:add_ac mult_ac)
  qed
next
  assume Q: ?Q
  from m Q[THEN spec,of "n div m",THEN spec, of "n mod m"]
  show ?P by(simp add:mod_div_equality2)
qed

end
