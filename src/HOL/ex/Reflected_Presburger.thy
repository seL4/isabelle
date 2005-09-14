(*  Title:      HOL/ex/PresburgerEx.thy
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen

A formalization of quantifier elimination for Presburger arithmetic
based on a generic quantifier elimination algorithm and Cooper's
methos to eliminate on \<exists>. *)

header {* Quantifier elimination for Presburger arithmetic *}

theory Reflected_Presburger
imports Main
begin

(* Shadow syntax for integer terms *)
datatype intterm =
    Cst int
  | Var nat
  | Neg intterm
  | Add intterm intterm 
  | Sub intterm intterm
  | Mult intterm intterm

(* interpretatation of intterms , takes bound variables and free variables *)
consts I_intterm :: "int list \<Rightarrow> intterm \<Rightarrow> int"
primrec 
"I_intterm ats (Cst b) = b"
"I_intterm ats (Var n) = (ats!n)"
"I_intterm ats (Neg it) = -(I_intterm ats it)"
"I_intterm ats (Add it1 it2) = (I_intterm ats it1) + (I_intterm ats it2)" 
"I_intterm ats (Sub it1 it2) = (I_intterm ats it1) - (I_intterm ats it2)"
"I_intterm ats (Mult it1 it2) = (I_intterm ats it1) * (I_intterm ats it2)"

(*Shadow syntax for Presburger formulae *)
datatype QF = 
   Lt intterm intterm
  |Gt intterm intterm
  |Le intterm intterm
  |Ge intterm intterm
  |Eq intterm intterm
  |Divides intterm intterm
  |T
  |F
  |NOT QF
  |And QF QF
  |Or QF QF
  |Imp QF QF
  |Equ QF QF
  |QAll QF
  |QEx QF

(* Interpretation of Presburger  formulae *)
consts qinterp :: "int list \<Rightarrow> QF \<Rightarrow> bool"
primrec
"qinterp ats (Lt it1 it2) = (I_intterm ats it1 < I_intterm ats it2)"
"qinterp ats (Gt it1 it2) = (I_intterm ats it1 > I_intterm ats it2)"
"qinterp ats (Le it1 it2) = (I_intterm ats it1 \<le> I_intterm ats it2)"
"qinterp ats (Ge it1 it2) = (I_intterm ats it1 \<ge> I_intterm ats it2)"
"qinterp ats (Divides it1 it2) = (I_intterm ats it1 dvd I_intterm ats it2)"
"qinterp ats (Eq it1 it2) = (I_intterm ats it1 = I_intterm ats it2)"
"qinterp ats T = True"
"qinterp ats F = False"
"qinterp ats (NOT p) = (\<not>(qinterp ats p))"
"qinterp ats (And p q) = (qinterp ats p \<and> qinterp ats q)"
"qinterp ats (Or p q) = (qinterp ats p \<or> qinterp ats q)"
"qinterp ats (Imp p q) = (qinterp ats p \<longrightarrow> qinterp ats q)"
"qinterp ats (Equ p q) = (qinterp ats p = qinterp ats q)"
"qinterp ats (QAll p) = (\<forall>x. qinterp (x#ats) p)"
"qinterp ats (QEx p) = (\<exists>x. qinterp (x#ats) p)"

(* quantifier elimination based on qe, quantifier elimination for an
   existential formula, with quantifier free body 
   Since quantifier elimination for one formula is allowed to fail, 
   the reult is of type QF option *)

consts lift_bin:: "('a \<Rightarrow> 'a \<Rightarrow> 'b) \<times> 'a option \<times> 'a option \<Rightarrow> 'b option"
recdef lift_bin "measure (\<lambda>(c,a,b). size a)"
"lift_bin (c,Some a,Some b) = Some (c a b)"
"lift_bin (c,x, y)  = None"

lemma lift_bin_Some:
  assumes ls: "lift_bin (c,x,y) = Some t"
  shows "(\<exists>a. x = Some a) \<and> (\<exists>b. y = Some b)"
  using ls 
  by (cases "x", auto) (cases "y", auto)+

consts lift_un:: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option"
primrec
"lift_un c None = None"
"lift_un c (Some p) = Some (c p)"

consts lift_qe:: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a option \<Rightarrow> 'b option"
primrec
"lift_qe qe None = None"
"lift_qe qe (Some p) = qe p"

(* generic quantifier elimination *)
consts qelim :: "(QF \<Rightarrow> QF option) \<times> QF \<Rightarrow> QF option"
recdef qelim "measure (\<lambda>(qe,p). size p)"
"qelim (qe, (QAll p)) = lift_un NOT (lift_qe qe (lift_un NOT (qelim (qe ,p))))"
"qelim (qe, (QEx p)) = lift_qe qe (qelim (qe,p))"
"qelim (qe, (And p q)) = lift_bin (And, (qelim (qe, p)), (qelim (qe, q)))"
"qelim (qe, (Or p q)) = lift_bin (Or, (qelim (qe, p)), (qelim (qe, q)))"
"qelim (qe, (Imp p q)) = lift_bin (Imp, (qelim (qe, p)), (qelim (qe, q)))"
"qelim (qe, (Equ p q)) = lift_bin (Equ, (qelim (qe, p)), (qelim (qe, q)))"
"qelim (qe,NOT p) = lift_un NOT (qelim (qe,p))"
"qelim (qe, p) = Some p"

(* quantifier free-ness *)
consts isqfree :: "QF \<Rightarrow> bool"
recdef isqfree "measure size"
"isqfree (QAll p) = False"
"isqfree (QEx p) = False"
"isqfree (And p q) = (isqfree p \<and> isqfree q)"
"isqfree (Or p q) = (isqfree p \<and> isqfree q)"
"isqfree (Imp p q) = (isqfree p \<and> isqfree q)"
"isqfree (Equ p q) = (isqfree p \<and> isqfree q)"
"isqfree (NOT p) = isqfree p"
"isqfree p = True"

(* qelim lifts quantifierfreeness*)
lemma qelim_qfree: 
  assumes qeqf: "(\<And> q q'. \<lbrakk>isqfree q ; qe q = Some q'\<rbrakk> \<Longrightarrow>  isqfree q')"
  shows qff:"\<And> p'. qelim (qe, p) = Some p' \<Longrightarrow> isqfree p'"
  using qeqf
proof (induct p)
  case (Lt a b)
  have "qelim (qe, Lt a b) = Some (Lt a b)" by simp
  moreover have "qelim (qe,Lt a b) = Some p'" . 
  ultimately have "p' = Lt a b" by simp
  moreover have "isqfree (Lt a b)" by simp
  ultimately 
  show ?case  by simp
next  
  case (Gt a b)
  have "qelim (qe, Gt a b) = Some (Gt a b)" by simp
  moreover have "qelim (qe,Gt a b) = Some p'" . 
  ultimately have "p' = Gt a b" by simp
  moreover have "isqfree (Gt a b)" by simp
  ultimately 
  show ?case  by simp
next  
  case (Le a b)
  have "qelim (qe, Le a b) = Some (Le a b)" by simp
  moreover have "qelim (qe,Le a b) = Some p'" . 
  ultimately have "p' = Le a b" by simp
  moreover have "isqfree (Le a b)" by simp
  ultimately 
  show ?case  by simp
next  
  case (Ge a b)
  have "qelim (qe, Ge a b) = Some (Ge a b)" by simp
  moreover have "qelim (qe,Ge a b) = Some p'" . 
  ultimately have "p' = Ge a b" by simp
  moreover have "isqfree (Ge a b)" by simp
  ultimately 
  show ?case  by simp
next  
  case (Eq a b)
  have "qelim (qe, Eq a b) = Some (Eq a b)" by simp
  moreover have "qelim (qe,Eq a b) = Some p'" . 
  ultimately have "p' = Eq a b" by simp
  moreover have "isqfree (Eq a b)" by simp
  ultimately 
  show ?case  by simp
next  
  case (Divides a b)
  have "qelim (qe, Divides a b) = Some (Divides a b)" by simp
  moreover have "qelim (qe,Divides a b) = Some p'" . 
  ultimately have "p' = Divides a b" by simp
  moreover have "isqfree (Divides a b)" by simp
  ultimately 
  show ?case  by simp
next  
  case T 
  have "qelim(qe,T) = Some T" by simp
  moreover have "qelim(qe,T) = Some p'" .
  ultimately have "p' = T" by simp
  moreover have "isqfree T" by simp
  ultimately show ?case by simp
next  
  case F
  have "qelim(qe,F) = Some F" by simp
  moreover have "qelim(qe,F) = Some p'" .
  ultimately have "p' = F" by simp
  moreover have "isqfree F" by simp
  ultimately show ?case by simp
next  
  case (NOT p)
  from "NOT.prems" have "\<exists> p1. qelim(qe,p) = Some p1"
    by  (cases "qelim(qe,p)") simp_all
  then obtain "p1" where p1_def: "qelim(qe,p) = Some p1" by blast
  from "NOT.prems" have "\<And>q q'. \<lbrakk>isqfree q; qe q = Some q'\<rbrakk> \<Longrightarrow> isqfree q'" 
    by blast
  with "NOT.hyps" p1_def have p1qf: "isqfree p1" by blast
  then have "p' = NOT p1" using "NOT.prems" p1_def
    by (cases "qelim(qe,NOT p)") simp_all
  then show ?case using p1qf by simp
next  
  case (And p q) 
  from "And.prems" have p1q1: "(\<exists>p1. qelim(qe,p) = Some p1) \<and> 
    (\<exists>q1. qelim(qe,q) = Some q1)" using lift_bin_Some[where c="And"] by simp
  from p1q1 obtain "p1" and "q1" 
    where p1_def: "qelim(qe,p) = Some p1" 
    and q1_def: "qelim(qe,q) = Some q1" by blast
  from prems have qf1:"isqfree p1"
    using p1_def by blast
  from prems have qf2:"isqfree q1"
    using q1_def by blast
  from "And.prems" have "qelim(qe,And p q) = Some p'" by blast
  then have "p' = And p1 q1" using p1_def q1_def by simp
  then 
  show ?case using qf1 qf2 by simp
next  
  case (Or p q)
  from "Or.prems" have p1q1: "(\<exists>p1. qelim(qe,p) = Some p1) \<and> 
    (\<exists>q1. qelim(qe,q) = Some q1)" using lift_bin_Some[where c="Or"] by simp
  from p1q1 obtain "p1" and "q1" 
    where p1_def: "qelim(qe,p) = Some p1" 
    and q1_def: "qelim(qe,q) = Some q1" by blast
  from prems have qf1:"isqfree p1"
    using p1_def by blast
  from prems have qf2:"isqfree q1"
    using q1_def by blast
  from "Or.prems" have "qelim(qe,Or p q) = Some p'" by blast
  then have "p' = Or p1 q1" using p1_def q1_def by simp
  then 
  show ?case using qf1 qf2 by simp
next  
  case (Imp p q)
  from "Imp.prems" have p1q1: "(\<exists>p1. qelim(qe,p) = Some p1) \<and> 
    (\<exists>q1. qelim(qe,q) = Some q1)" using lift_bin_Some[where c="Imp"] by simp
  from p1q1 obtain "p1" and "q1" 
    where p1_def: "qelim(qe,p) = Some p1" 
    and q1_def: "qelim(qe,q) = Some q1" by blast
  from prems have qf1:"isqfree p1"
    using p1_def by blast
  from prems have qf2:"isqfree q1"
    using q1_def by blast
  from "Imp.prems" have "qelim(qe,Imp p q) = Some p'" by blast
  then have "p' = Imp p1 q1" using p1_def q1_def by simp
  then 
  show ?case using qf1 qf2 by simp
next  
  case (Equ p q)
  from "Equ.prems" have p1q1: "(\<exists>p1. qelim(qe,p) = Some p1) \<and> 
    (\<exists>q1. qelim(qe,q) = Some q1)" using lift_bin_Some[where c="Equ"] by simp
  from p1q1 obtain "p1" and "q1" 
    where p1_def: "qelim(qe,p) = Some p1" 
    and q1_def: "qelim(qe,q) = Some q1" by blast
  from prems have qf1:"isqfree p1"
    using p1_def by blast
  from prems have qf2:"isqfree q1"
    using q1_def by blast
  from "Equ.prems" have "qelim(qe,Equ p q) = Some p'" by blast
  then have "p' = Equ p1 q1" using p1_def q1_def by simp
  then 
  show ?case using qf1 qf2 by simp
next 
  case (QEx p)
  from "QEx.prems" have "\<exists> p1. qelim(qe,p) = Some p1"
    by  (cases "qelim(qe,p)") simp_all
  then obtain "p1" where p1_def: "qelim(qe,p) = Some p1" by blast
  from "QEx.prems" have "\<And>q q'. \<lbrakk>isqfree q; qe q = Some q'\<rbrakk> \<Longrightarrow> isqfree q'" 
    by blast
  with "QEx.hyps" p1_def have p1qf: "isqfree p1" by blast
  from "QEx.prems" have "qe p1 = Some p'" using p1_def by simp
  with "QEx.prems" show ?case  using p1qf 
    by simp
next 
  case (QAll p) 
  from "QAll.prems"
  have "\<exists> p1. lift_qe qe (lift_un NOT (qelim (qe ,p))) = Some p1" 
    by (cases "lift_qe qe (lift_un NOT (qelim (qe ,p)))") simp_all
  then obtain "p1" where 
    p1_def:"lift_qe qe (lift_un NOT (qelim (qe ,p))) = Some p1" by blast
  then have "\<exists> p2. lift_un NOT (qelim (qe ,p)) = Some p2"
    by (cases "qelim (qe ,p)") simp_all
  then obtain "p2" 
    where p2_def:"lift_un NOT (qelim (qe ,p)) = Some p2" by blast
  then have "\<exists> p3. qelim(qe,p) = Some p3" by (cases "qelim(qe,p)") simp_all
  then obtain "p3" where p3_def: "qelim(qe,p) = Some p3" by blast
  with prems have qf3: "isqfree p3" by blast
  have p2_def2: "p2 = NOT p3" using p2_def p3_def by simp
  then have qf2: "isqfree p2" using qf3 by simp
  have p1_edf2: "qe p2 = Some p1" using p1_def p2_def by simp
  with "QAll.prems" have qf1: "isqfree p1" using qf2 by blast
  from "QAll.prems" have "p' = NOT p1" using p1_def by simp
  with qf1 show ?case by simp
qed

(* qelim lifts semantical equivalence *)
lemma qelim_corr: 
  assumes qecorr: "(\<And> q q' ats. \<lbrakk>isqfree q ; qe q = Some q'\<rbrakk> \<Longrightarrow>  (qinterp ats (QEx q)) = (qinterp ats q'))"
  and qeqf: "(\<And> q q'. \<lbrakk>isqfree q ; qe q = Some q'\<rbrakk> \<Longrightarrow>  isqfree q')"
  shows qff:"\<And> p' ats. qelim (qe, p) = Some p' \<Longrightarrow> (qinterp ats p = qinterp ats p')" (is "\<And> p' ats. ?Qe p p' \<Longrightarrow> (?F ats p = ?F ats p')")
  using qeqf qecorr
proof (induct p)
  case (NOT f)  
  from "NOT.prems" have "\<exists>f'. ?Qe f f' " by (cases "qelim(qe,f)") simp_all
  then obtain "f'" where df': "?Qe f f'" by blast
  with prems have feqf': "?F ats f = ?F ats f'" by blast
  from "NOT.prems" df' have "p' = NOT f'" by simp
  with feqf' show ?case by simp

next
  case (And f g) 
  from "And.prems" have f1g1: "(\<exists>f1. qelim(qe,f) = Some f1) \<and> 
    (\<exists>g1. qelim(qe,g) = Some g1)" using lift_bin_Some[where c="And"] by simp
  from f1g1 obtain "f1" and "g1" 
    where f1_def: "qelim(qe, f) = Some f1" 
    and g1_def: "qelim(qe,g) = Some g1" by blast
  from prems f1_def have feqf1: "?F ats f = ?F ats f1" by blast
  from prems g1_def have geqg1: "?F ats g = ?F ats g1" by blast
  from "And.prems" f1_def g1_def have "p' = And f1 g1" by simp
  with feqf1 geqg1 show ?case by simp

next
  case (Or f g) 
  from "Or.prems" have f1g1: "(\<exists>f1. qelim(qe,f) = Some f1) \<and> 
    (\<exists>g1. qelim(qe,g) = Some g1)" using lift_bin_Some[where c="Or"] by simp
  from f1g1 obtain "f1" and "g1" 
    where f1_def: "qelim(qe, f) = Some f1" 
    and g1_def: "qelim(qe,g) = Some g1" by blast
  from prems f1_def have feqf1: "?F ats f = ?F ats  f1" by blast
  from prems g1_def have geqg1: "?F ats g = ?F ats g1" by blast
  from "Or.prems" f1_def g1_def have "p' = Or f1 g1" by simp
  with feqf1 geqg1 show ?case by simp
next
  case (Imp f g)
  from "Imp.prems" have f1g1: "(\<exists>f1. qelim(qe,f) = Some f1) \<and> 
    (\<exists>g1. qelim(qe,g) = Some g1)" using lift_bin_Some[where c="Imp"] by simp
  from f1g1 obtain "f1" and "g1" 
    where f1_def: "qelim(qe, f) = Some f1" 
    and g1_def: "qelim(qe,g) = Some g1" by blast
  from prems f1_def have feqf1: "?F ats f = ?F ats f1" by blast
  from prems g1_def have geqg1: "?F ats g = ?F ats g1" by blast
  from "Imp.prems" f1_def g1_def have "p' = Imp f1 g1" by simp
  with feqf1 geqg1 show ?case by simp
next
  case (Equ f g)
  from "Equ.prems" have f1g1: "(\<exists>f1. qelim(qe,f) = Some f1) \<and> 
    (\<exists>g1. qelim(qe,g) = Some g1)" using lift_bin_Some[where c="Equ"] by simp
  from f1g1 obtain "f1" and "g1" 
    where f1_def: "qelim(qe, f) = Some f1" 
    and g1_def: "qelim(qe,g) = Some g1" by blast
  from prems f1_def have feqf1: "?F ats f = ?F ats f1" by blast
  from prems g1_def have geqg1: "?F ats g = ?F ats g1" by blast
  from "Equ.prems" f1_def g1_def have "p' = Equ f1 g1" by simp
  with feqf1 geqg1 show ?case by simp
next
  case (QEx f) 
    from "QEx.prems" have "\<exists> f1. ?Qe f f1"
    by  (cases "qelim(qe,f)") simp_all
  then obtain "f1" where f1_def: "qelim(qe,f) = Some f1" by blast
  from prems have qf1:"isqfree f1" using qelim_qfree by blast
  from prems have feqf1: "\<forall> ats. qinterp ats f = qinterp ats f1"
    using f1_def qf1 by blast
  then  have "?F ats (QEx f) = ?F ats (QEx f1)" 
    by simp 
  from prems have "qelim (qe,QEx f) = Some p'" by blast
  then  have "\<exists> f'. qe f1 = Some f'" using f1_def by simp
  then obtain "f'" where fdef': "qe f1 = Some f'" by blast
  with prems have exf1: "?F ats (QEx f1) = ?F ats f'" using qf1 by blast
  have fp: "?Qe (QEx f) f'" using f1_def fdef' by simp
  from prems have "?Qe (QEx f) p'" by blast 
  then have "p' = f'" using fp by simp
  then show ?case using feqf1 exf1 by simp
next
  case (QAll f)
  from "QAll.prems"
  have "\<exists> f0. lift_un NOT (lift_qe qe (lift_un NOT (qelim (qe ,f)))) = 
    Some f0"
    by (cases "lift_un NOT (lift_qe qe (lift_un NOT (qelim (qe ,f))))") 
      simp_all
  then obtain "f0" 
    where f0_def: "lift_un NOT (lift_qe qe (lift_un NOT (qelim (qe ,f)))) = 
    Some f0" by blast
  then have "\<exists> f1. lift_qe qe (lift_un NOT (qelim (qe ,f))) = Some f1" 
    by (cases "lift_qe qe (lift_un NOT (qelim (qe ,f)))") simp_all
  then obtain "f1" where 
    f1_def:"lift_qe qe (lift_un NOT (qelim (qe ,f))) = Some f1" by blast
  then have "\<exists> f2. lift_un NOT (qelim (qe ,f)) = Some f2"
    by (cases "qelim (qe ,f)") simp_all
  then obtain "f2" 
    where f2_def:"lift_un NOT (qelim (qe ,f)) = Some f2" by blast
  then have "\<exists> f3. qelim(qe,f) = Some f3" by (cases "qelim(qe,f)") simp_all
  then obtain "f3" where f3_def: "qelim(qe,f) = Some f3" by blast
  from prems have qf3:"isqfree f3" using qelim_qfree by blast
  from prems have feqf3: "\<forall> ats. qinterp ats f = qinterp ats f3"
    using f3_def qf3 by blast
  have f23:"f2 = NOT f3" using f2_def f3_def by simp
  then have feqf2: "\<forall> ats. qinterp ats f = qinterp ats (NOT f2)"
    using feqf3 by simp
  have qf2: "isqfree f2" using f23 qf3 by simp
  have "qe f2 = Some f1" using f1_def f2_def f23 by simp
  with prems have exf2eqf1: "?F ats (QEx f2) = ?F ats f1" using qf2 by blast
  have "f0 = NOT f1" using f0_def f1_def by simp
  then have f0eqf1: "?F ats f0 = ?F ats (NOT f1)" by simp
  from prems have "qelim (qe, QAll f) = Some p'" by blast
  then have f0eqp': "p' = f0" using f0_def by simp
  have "?F ats (QAll f) = (\<forall>x. ?F (x#ats) f)" by simp
  also have "\<dots> = (\<not> (\<exists> x. ?F (x#ats) (NOT f)))" by simp
  also have "\<dots> = (\<not> (\<exists> x. ?F (x#ats) (NOT (NOT f2))))" using feqf2
    by auto
  also have "\<dots> = (\<not> (\<exists> x. ?F (x#ats) f2))" by simp
  also have "\<dots> = (\<not> (?F ats f1))" using exf2eqf1 by simp
  finally show ?case using f0eqp' f0eqf1 by simp
qed simp_all

(* Cooper's algorithm *)


(* Transform an intform into NNF *)
consts lgth :: "QF \<Rightarrow> nat"
       nnf :: "QF \<Rightarrow> QF"    
primrec
"lgth (Lt it1 it2) = 1"
"lgth (Gt it1 it2) = 1"
"lgth (Le it1 it2) = 1"
"lgth (Ge it1 it2) = 1"
"lgth (Eq it1 it2) = 1"
"lgth (Divides it1 it2) = 1"
"lgth T = 1"
"lgth F = 1"
"lgth (NOT p) = 1 + lgth p"
"lgth (And p q) = 1 + lgth p + lgth q"
"lgth (Or p q) = 1 + lgth p + lgth q"
"lgth (Imp p q) = 1 + lgth p + lgth q"
"lgth (Equ p q) = 1 + lgth p + lgth q" 
"lgth (QAll p) = 1 + lgth p" 
"lgth (QEx p) = 1 + lgth p" 

lemma [simp] :"0 < lgth q"
apply (induct_tac q)
apply(auto)
done

(* NNF *)
recdef nnf "measure (\<lambda>p. lgth p)"
  "nnf (Lt it1 it2) = Le (Sub it1 it2) (Cst (- 1))"
  "nnf (Gt it1 it2) = Le (Sub it2 it1) (Cst (- 1))"
  "nnf (Le it1 it2) = Le it1 it2 "
  "nnf (Ge it1 it2) = Le it2 it1"
  "nnf (Eq it1 it2) = Eq it2 it1"
  "nnf (Divides d t) = Divides d t"
  "nnf T = T"
  "nnf F = F"
  "nnf (And p q) = And (nnf p) (nnf q)"
  "nnf (Or p q) = Or (nnf p) (nnf q)"
  "nnf (Imp p q) = Or (nnf (NOT p)) (nnf q)"
  "nnf (Equ p q) = Or (And (nnf p) (nnf q)) 
  (And (nnf (NOT p)) (nnf (NOT q)))"
  "nnf (NOT (Lt it1 it2)) = (Le it2 it1)"
  "nnf (NOT (Gt it1 it2))  = (Le it1 it2)"
  "nnf (NOT (Le it1 it2)) = (Le (Sub it2 it1) (Cst (- 1)))"
  "nnf (NOT (Ge it1 it2)) = (Le (Sub it1 it2) (Cst (- 1)))"
  "nnf (NOT (Eq it1 it2)) = (NOT (Eq it1 it2))"
  "nnf (NOT (Divides d t)) = (NOT (Divides d t))"
  "nnf (NOT T) = F"
  "nnf (NOT F) = T"
  "nnf (NOT (NOT p)) = (nnf p)"
  "nnf (NOT (And p q)) = (Or (nnf (NOT p)) (nnf (NOT q)))"
  "nnf (NOT (Or p q)) = (And (nnf (NOT p)) (nnf (NOT q)))"
  "nnf (NOT (Imp p q)) = (And (nnf p) (nnf (NOT q)))"
  "nnf (NOT (Equ p q)) = (Or (And (nnf p) (nnf (NOT q))) (And (nnf (NOT p)) (nnf q)))"

consts isnnf :: "QF \<Rightarrow> bool"
recdef isnnf "measure (\<lambda>p. lgth p)"
  "isnnf (Le it1 it2) = True"
  "isnnf (Eq it1 it2) = True"
  "isnnf (Divides d t) = True"
  "isnnf T = True"
  "isnnf F = True"
  "isnnf (And p q) = (isnnf p \<and> isnnf q)"
  "isnnf (Or p q) = (isnnf p \<and> isnnf q)"
  "isnnf (NOT (Divides d t)) = True" 
  "isnnf (NOT (Eq it1 it2)) = True" 
  "isnnf p = False"

(* nnf preserves semantics *)
lemma nnf_corr: "isqfree p \<Longrightarrow> qinterp ats p = qinterp ats (nnf p)"
by (induct p rule: nnf.induct,simp_all) 
(arith, arith, arith, arith, arith, arith, arith, arith, arith, blast)


(* the result of nnf is in NNF *)
lemma nnf_isnnf : "isqfree p \<Longrightarrow> isnnf (nnf p)"
by (induct p rule: nnf.induct, auto)

lemma nnf_isqfree: "isnnf p \<Longrightarrow> isqfree p"
by (induct p rule: isnnf.induct) auto

(* nnf preserves quantifier freeness *)
lemma nnf_qfree: "isqfree p \<Longrightarrow> isqfree(nnf p)"
  using nnf_isqfree nnf_isnnf by simp

(* Linearization and normalization of formulae *)
(* Definition of linearity of an intterm *)

consts islinintterm :: "intterm \<Rightarrow> bool"
recdef islinintterm "measure size"
"islinintterm (Cst i) = True"
"islinintterm (Add (Mult (Cst i) (Var n)) (Cst i')) = (i \<noteq> 0)"
"islinintterm (Add (Mult (Cst i) (Var n)) (Add (Mult (Cst i') (Var n')) r)) = ( i \<noteq> 0 \<and> i' \<noteq> 0 \<and> n < n' \<and> islinintterm  (Add (Mult (Cst i') (Var n')) r))"
"islinintterm i = False"

(* subterms of linear terms are linear *)
lemma islinintterm_subt:
  assumes lr: "islinintterm (Add (Mult (Cst i) (Var n)) r)"
  shows "islinintterm r"
using lr
by (induct r rule: islinintterm.induct) auto

(* c \<noteq> 0 for linear term c.n + r*)
lemma islinintterm_cnz:
  assumes lr: "islinintterm (Add (Mult (Cst i) (Var n)) r)"
  shows "i \<noteq> 0"
using lr
by (induct r rule: islinintterm.induct) auto

lemma islininttermc0r: "islinintterm (Add (Mult (Cst c) (Var n)) r) \<Longrightarrow> (c \<noteq> 0 \<and> islinintterm r)"
by (induct r rule: islinintterm.induct, simp_all)

(* An alternative linearity definition *)
consts islintn :: "(nat \<times> intterm) \<Rightarrow> bool"
recdef islintn "measure (\<lambda> (n,t). (size t))"
"islintn (n0, Cst i) = True"
"islintn (n0, Add (Mult (Cst i) (Var n)) r) = (i \<noteq> 0 \<and> n0 \<le> n \<and> islintn (n+1,r))"
"islintn (n0, t) = False"

constdefs islint :: "intterm \<Rightarrow> bool"
  "islint t \<equiv> islintn(0,t)"

(* And the equivalence to the first definition *)
lemma islinintterm_eq_islint: "islinintterm t = islint t"
  using islint_def
by (induct t rule: islinintterm.induct) auto

(* monotony *)
lemma islintn_mon:
  assumes lin: "islintn (n,t)"
  and mgen: "m \<le> n"
  shows "islintn(m,t)"
  using lin mgen 
by (induct t rule: islintn.induct) auto

lemma islintn_subt:
  assumes lint: "islintn(n,Add (Mult (Cst i) (Var m)) r)"
  shows "islintn (m+1,r)"
using lint
by auto

(* List indexin for n > 0 *)
lemma nth_pos: "0 < n \<longrightarrow> (x#xs) ! n = (y#xs) ! n"
using Nat.gr0_conv_Suc 
by clarsimp 

lemma nth_pos2: "0 < n \<Longrightarrow> (x#xs) ! n = xs ! (n - 1)"
using Nat.gr0_conv_Suc
by clarsimp

lemma intterm_novar0: 
  assumes lin: "islinintterm (Add (Mult (Cst i) (Var n)) r)"
  shows "I_intterm (x#ats) r = I_intterm (y#ats) r"
using lin
by (induct r rule: islinintterm.induct) (simp_all add: nth_pos2)
(* a simple version of a general theorem: Interpretation doese not depend 
   on the first variable if it doese not occur in the term *)

lemma linterm_novar0:
  assumes lin: "islintn (n,t)"
  and npos: "0 < n"
  shows "I_intterm (x#ats) t = I_intterm (y#ats) t"
using lin npos
by (induct n t rule: islintn.induct) (simp_all add: nth_pos2)

(* Periodicity of dvd *)
lemma dvd_period:
  assumes advdd: "(a::int) dvd d"
  shows "(a dvd (x + t)) = (a dvd ((x+ c*d) + t))"
using advdd  
proof-
  from advdd  have "\<forall>x.\<forall>k. (((a::int) dvd (x + t)) = (a dvd
 (x+k*d + t)))" by (rule dvd_modd_pinf)
  then show ?thesis by simp
qed

(* lin_ad adds two linear terms*)
consts lin_add :: "intterm \<times> intterm \<Rightarrow> intterm"
recdef lin_add "measure (\<lambda>(x,y). ((size x) + (size y)))"
"lin_add (Add (Mult (Cst c1) (Var n1)) (r1),Add (Mult (Cst c2) (Var n2)) (r2)) =
  (if n1=n2 then 
  (let c = Cst (c1 + c2) 
   in (if c1+c2=0 then lin_add(r1,r2) else Add (Mult c (Var n1)) (lin_add (r1,r2))))
  else if n1 \<le> n2 then (Add (Mult (Cst c1) (Var n1)) (lin_add (r1,Add (Mult (Cst c2) (Var n2)) (r2)))) 
  else (Add (Mult (Cst c2) (Var n2)) (lin_add (Add (Mult (Cst c1) (Var n1)) r1,r2))))"
"lin_add (Add (Mult (Cst c1) (Var n1)) (r1),Cst b) = 
  (Add (Mult (Cst c1) (Var n1)) (lin_add (r1, Cst b)))"  
"lin_add (Cst x,Add (Mult (Cst c2) (Var n2)) (r2)) = 
  Add (Mult (Cst c2) (Var n2)) (lin_add (Cst x,r2))" 
"lin_add (Cst b1, Cst b2) = Cst (b1+b2)"

lemma lin_add_cst_corr: 
  assumes blin : "islintn(n0,b)"
  shows "I_intterm ats (lin_add (Cst a,b)) = (I_intterm ats (Add (Cst a) b))"
using blin
by (induct n0 b rule: islintn.induct) auto

lemma lin_add_cst_corr2: 
  assumes blin : "islintn(n0,b)"
  shows "I_intterm ats (lin_add (b,Cst a)) = (I_intterm ats (Add b (Cst a)))"
using blin
by (induct n0 b rule: islintn.induct) auto

lemma lin_add_corrh: "\<And> n01 n02. \<lbrakk> islintn (n01,a) ; islintn (n02,b)\<rbrakk> 
  \<Longrightarrow> I_intterm ats (lin_add(a,b)) = I_intterm ats (Add a b)"
proof(induct a b rule: lin_add.induct)
  case (58 i n r j m s) 
  have "(n = m \<and> i+j = 0) \<or> (n = m \<and> i+j \<noteq> 0) \<or> n < m \<or> m < n " by arith
  moreover
  {assume "n=m\<and>i+j=0" hence ?case using prems by (auto simp add: sym[OF zadd_zmult_distrib]) }
  moreover
  {assume "n=m\<and>i+j\<noteq>0" hence ?case using prems by (auto simp add: Let_def zadd_zmult_distrib)}
  moreover
  {assume "n < m" hence ?case using prems by auto }
  moreover
  {assume "n > m" hence ?case using prems by auto }
  ultimately show ?case by blast
qed (auto simp add: lin_add_cst_corr lin_add_cst_corr2 Let_def)

(* lin_add has the semantics of Add*)
lemma lin_add_corr:
  assumes lina: "islinintterm a"
  and linb: "islinintterm b"
  shows "I_intterm ats (lin_add (a,b)) = (I_intterm ats (Add a b))"
using lina linb islinintterm_eq_islint islint_def lin_add_corrh
by blast

lemma lin_add_cst_lint:
  assumes lin: "islintn (n0,b)"
  shows "islintn (n0, lin_add (Cst i, b))"
using lin
by (induct n0 b rule: islintn.induct) auto

lemma lin_add_cst_lint2:
  assumes lin: "islintn (n0,b)"
  shows "islintn (n0, lin_add (b,Cst i))"
using lin
by (induct n0 b rule: islintn.induct) auto

(* lin_add preserves linearity..*)
lemma lin_add_lint: "\<And> n0 n01 n02. \<lbrakk> islintn (n01,a) ; islintn (n02,b); n0 \<le>  min n01 n02 \<rbrakk> 
  \<Longrightarrow> islintn (n0, lin_add (a,b))"
proof (induct a b rule: lin_add.induct)
  case (58 i n r j m s)
  have "(n =m \<and> i + j = 0) \<or> (n = m \<and> i+j \<noteq> 0) \<or> n <m \<or> m < n" by arith
  moreover 
  { assume "n = m"
      and  "i+j = 0"
    hence ?case using "58" islintn_mon[where m = "n01" and n = "Suc m"]
      islintn_mon[where m = "n02" and n = "Suc m"] by auto }
  moreover 
  { assume  "n = m"
      and "i+j \<noteq> 0"
    hence ?case using "58" islintn_mon[where m = "n01" and n = "Suc m"]
      islintn_mon[where m = "n02" and n = "Suc m"] by (auto simp add: Let_def) }
  moreover
  { assume "n < m" hence ?case using 58 by force }
moreover
  { assume "m < n"
    hence ?case using 58 
      apply (auto simp add: Let_def) 
      apply (erule allE[where x = "Suc m" ] )
      by (erule allE[where x = "Suc m" ] ) simp }
  ultimately show ?case by blast
qed(simp_all add: Let_def lin_add_cst_lint lin_add_cst_lint2)

lemma lin_add_lin:
  assumes lina: "islinintterm a"
  and linb: "islinintterm b"
  shows "islinintterm (lin_add (a,b))"
using islinintterm_eq_islint islint_def lin_add_lint lina linb by auto

(* lin_mul multiplies a linear term by a constant *)
consts lin_mul :: "int \<times> intterm \<Rightarrow> intterm"
recdef lin_mul "measure (\<lambda>(c,t). size t)"
"lin_mul (c,Cst i) = (Cst (c*i))"
"lin_mul (c,Add (Mult (Cst c') (Var n)) r)  = 
  (if c = 0 then (Cst 0) else
  (Add (Mult (Cst (c*c')) (Var n)) (lin_mul (c,r))))"

lemma zmult_zadd_distrib[simp]: "(a::int) * (b+c) = a*b + a*c"
proof-
  have "a*(b+c) = (b+c)*a" by simp
  moreover have "(b+c)*a = b*a + c*a" by (simp add: zadd_zmult_distrib)
  ultimately show ?thesis by simp
qed

(* lin_mul has the semantics of Mult *)
lemma lin_mul_corr: 
  assumes lint: "islinintterm  t"
  shows "I_intterm ats (lin_mul (c,t)) = I_intterm ats (Mult (Cst c) t)"
using lint
proof (induct c t rule: lin_mul.induct)
  case (21 c c' n r)
  have "islinintterm (Add (Mult (Cst c') (Var n)) r)" .
  then have "islinintterm r" 
    by (rule islinintterm_subt[of "c'" "n" "r"])
  then show ?case  using "21.hyps" "21.prems" by simp
qed(auto)

(* lin_mul preserves linearity *)
lemma lin_mul_lin:
  assumes lint: "islinintterm t"
  shows "islinintterm (lin_mul(c,t))"
using lint
by (induct t rule: islinintterm.induct) auto

lemma lin_mul0:
  assumes lint: "islinintterm t"
  shows "lin_mul(0,t) = Cst 0"
  using lint
  by (induct t rule: islinintterm.induct) auto

lemma lin_mul_lintn:
  "\<And> m. islintn(m,t) \<Longrightarrow> islintn(m,lin_mul(l,t))"
  by (induct l t rule: lin_mul.induct) simp_all

(* lin_neg neagtes a linear term *)
constdefs lin_neg :: "intterm \<Rightarrow> intterm"
"lin_neg i == lin_mul ((-1::int),i)"

(* lin_neg has the semantics of Neg *)
lemma lin_neg_corr:
  assumes lint: "islinintterm  t"
  shows "I_intterm ats (lin_neg t) = I_intterm ats (Neg t)"
  using lint lin_mul_corr
  by (simp add: lin_neg_def lin_mul_corr)

(* lin_neg preserves linearity *)
lemma lin_neg_lin:
  assumes lint: "islinintterm  t"
  shows "islinintterm (lin_neg t)"
using lint
by (simp add: lin_mul_lin lin_neg_def)

(* Some properties about lin_add and lin-neg should be moved above *)

lemma lin_neg_idemp: 
  assumes lini: "islinintterm i"
  shows "lin_neg (lin_neg i) = i"
using lini
by (induct i rule: islinintterm.induct) (auto simp add: lin_neg_def)

lemma lin_neg_lin_add_distrib:
  assumes lina : "islinintterm a"
  and linb :"islinintterm b"
  shows "lin_neg (lin_add(a,b)) = lin_add (lin_neg a, lin_neg b)"
using lina linb
proof (induct a b rule: lin_add.induct)
  case (58 c1 n1 r1 c2 n2 r2)
  from prems have lincnr1:"islinintterm (Add (Mult (Cst c1) (Var n1)) r1)" by simp
  have linr1: "islinintterm r1" by (rule islinintterm_subt[OF lincnr1])
  from prems have lincnr2: "islinintterm (Add (Mult (Cst c2) (Var n2)) r2)" by simp
  have linr2: "islinintterm r2" by (rule islinintterm_subt[OF lincnr2])
  have "n1 = n2 \<or> n1 < n2 \<or> n1 > n2" by arith
  show ?case using prems linr1 linr2 by (simp_all add: lin_neg_def Let_def)
next
  case (59 c n r b) 
  from prems have lincnr: "islinintterm (Add (Mult (Cst c) (Var n)) r)" by simp
  have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
  show ?case using prems linr by (simp add: lin_neg_def Let_def)
next
  case (60 b c n r)
  from prems have lincnr: "islinintterm (Add (Mult (Cst c) (Var n)) r)" by simp
  have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
  show ?case  using prems linr by (simp add: lin_neg_def Let_def)
qed (simp_all add: lin_neg_def)

(* linearize tries to linearize a term *)
consts linearize :: "intterm \<Rightarrow> intterm option"
recdef linearize "measure (\<lambda>t. size t)"
"linearize (Cst b) = Some (Cst b)"
"linearize (Var n) = Some (Add (Mult (Cst 1) (Var n)) (Cst 0))"
"linearize (Neg i) = lift_un lin_neg (linearize i)"
 "linearize (Add i j) = lift_bin(\<lambda> x. \<lambda> y. lin_add(x,y), linearize i, linearize j)"
"linearize (Sub i j) = 
  lift_bin(\<lambda> x. \<lambda> y. lin_add(x,lin_neg y), linearize i, linearize j)"
"linearize (Mult i j) = 
  (case linearize i of
  None \<Rightarrow> None
  | Some li \<Rightarrow> (case li of 
     Cst b \<Rightarrow> (case linearize j of
      None \<Rightarrow> None
     | (Some lj) \<Rightarrow> Some (lin_mul(b,lj)))
  | _ \<Rightarrow> (case linearize j of
      None \<Rightarrow> None
    | (Some lj) \<Rightarrow> (case lj of 
        Cst b \<Rightarrow> Some (lin_mul (b,li))
      | _ \<Rightarrow> None))))"

lemma linearize_linear1:
  assumes lin: "linearize t \<noteq> None"
  shows "islinintterm (the (linearize t))"
using lin
proof (induct t rule: linearize.induct)
  case (1 b) show ?case by simp  
next 
  case (2 n) show ?case by simp 
next 
  case (3 i) show ?case 
    proof-
    have "(linearize i = None) \<or> (\<exists>li. linearize i = Some li)" by auto
    moreover 
    { assume "linearize i = None" with prems have ?thesis by auto}
    moreover 
    { assume lini: "\<exists>li. linearize i = Some li"
      from lini obtain "li" where  "linearize i = Some li" by blast
      have linli: "islinintterm li" by (simp!)
      moreover have "linearize (Neg i) = Some (lin_neg li)" using prems by simp
      moreover from linli have "islinintterm(lin_neg li)" by (simp add: lin_neg_lin)
      ultimately have ?thesis by simp
    }
    ultimately show ?thesis by blast
  qed
next 
  case (4 i j) show ?case 
    proof-
    have "(linearize i = None) \<or> ((\<exists> li. linearize i = Some li) \<and> linearize j = None) \<or> ((\<exists> li. linearize i = Some li) \<and> (\<exists> lj. linearize j = Some lj))" by auto 
    moreover 
    {
      assume nlini: "linearize i = None"
      from nlini have "linearize (Add i j) = None" 
	by (simp add: Let_def measure_def inv_image_def) then have ?thesis using prems by auto}
    moreover 
    { assume nlinj: "linearize j = None"
	and lini: "\<exists> li. linearize i = Some li"
      from nlinj lini have "linearize (Add i j) = None" 
	by (simp add: Let_def measure_def inv_image_def, auto) with prems  have ?thesis by auto}
    moreover 
    { assume lini: "\<exists>li. linearize i = Some li"
	and linj: "\<exists>lj. linearize j = Some lj"
      from lini obtain "li" where  "linearize i = Some li" by blast
      have linli: "islinintterm li" by (simp!)
      from linj obtain "lj" where  "linearize j = Some lj" by blast
      have linlj: "islinintterm lj" by (simp!)
      moreover from lini linj have "linearize (Add i j) = Some (lin_add (li,lj))" 
	by (simp add: measure_def inv_image_def, auto!)
      moreover from linli linlj have "islinintterm(lin_add (li,lj))" by (simp add: lin_add_lin)
      ultimately have ?thesis by simp  }
    ultimately show ?thesis by blast
  qed
next 
  case (5 i j)show ?case 
    proof-
    have "(linearize i = None) \<or> ((\<exists> li. linearize i = Some li) \<and> linearize j = None) \<or> ((\<exists> li. linearize i = Some li) \<and> (\<exists> lj. linearize j = Some lj))" by auto 
    moreover 
    {
      assume nlini: "linearize i = None"
      from nlini have "linearize (Sub i j) = None" by (simp add: Let_def measure_def inv_image_def) then have ?thesis by (auto!)
    }
    moreover 
    {
      assume lini: "\<exists> li. linearize i = Some li"
	and nlinj: "linearize j = None"
      from nlinj lini have "linearize (Sub i j) = None" 
	by (simp add: Let_def measure_def inv_image_def, auto) then have ?thesis by (auto!)
    }
    moreover 
    {
      assume lini: "\<exists>li. linearize i = Some li"
	and linj: "\<exists>lj. linearize j = Some lj"
      from lini obtain "li" where  "linearize i = Some li" by blast
      have linli: "islinintterm li" by (simp!)
      from linj obtain "lj" where  "linearize j = Some lj" by blast
      have linlj: "islinintterm lj" by (simp!)
      moreover from lini linj have "linearize (Sub i j) = Some (lin_add (li,lin_neg lj))" 
	by (simp add: measure_def inv_image_def, auto!)
      moreover from linli linlj have "islinintterm(lin_add (li,lin_neg lj))" by (simp add: lin_add_lin lin_neg_lin)
      ultimately have ?thesis by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (6 i j)show ?case 
    proof-
      have cses: "(linearize i = None) \<or> 
	((\<exists> li. linearize i = Some li) \<and> linearize j = None) \<or> 
	((\<exists> li. linearize i = Some li) \<and> (\<exists> bj. linearize j = Some (Cst bj)))
	\<or> ((\<exists> bi. linearize i = Some (Cst bi)) \<and> (\<exists> lj. linearize j = Some lj))
	\<or> ((\<exists> li. linearize i = Some li \<and> \<not> (\<exists> bi. li = Cst bi)) \<and> (\<exists> lj. linearize j = Some lj \<and> \<not> (\<exists> bj. lj = Cst bj)))" by auto 
    moreover 
    {
      assume nlini: "linearize i = None"
      from nlini have "linearize (Mult i j) = None" 
	by (simp add: Let_def measure_def inv_image_def)  
      with prems have ?thesis by auto }
    moreover 
    {  assume lini: "\<exists> li. linearize i = Some li"
	and nlinj: "linearize j = None"
      from lini obtain "li" where "linearize i = Some li" by blast 
      moreover from nlinj lini have "linearize (Mult i j) = None"
	using prems
	by (cases li ) (auto simp add: Let_def measure_def inv_image_def)
      with prems have ?thesis by auto}
    moreover 
    { assume lini: "\<exists>li. linearize i = Some li"
	and linj: "\<exists>bj. linearize j = Some (Cst bj)"
      from lini obtain "li" where  li_def: "linearize i = Some li" by blast
      from prems have linli: "islinintterm li" by simp
      moreover 
      from linj  obtain "bj" where  bj_def: "linearize j = Some (Cst bj)" by blast
      have linlj: "islinintterm (Cst bj)" by simp 
      moreover from lini linj prems 
      have "linearize (Mult i j) = Some (lin_mul (bj,li))"
	by (cases li) (auto simp add: measure_def inv_image_def)
      moreover from linli linlj have "islinintterm(lin_mul (bj,li))" by (simp add: lin_mul_lin)
      ultimately have ?thesis by simp  }
    moreover 
    { assume lini: "\<exists>bi. linearize i = Some (Cst bi)"
	and linj: "\<exists>lj. linearize j = Some lj"
      from lini obtain "bi" where  "linearize i = Some (Cst bi)" by blast
      from prems have linli: "islinintterm (Cst bi)" by simp
      moreover 
      from linj  obtain "lj" where  "linearize j = Some lj" by blast
      from prems have linlj: "islinintterm lj" by simp
      moreover from lini linj prems have "linearize (Mult i j) = Some (lin_mul (bi,lj))" 
	by (simp add: measure_def inv_image_def) 
      moreover from linli linlj have "islinintterm(lin_mul (bi,lj))" by (simp add: lin_mul_lin)
      ultimately have ?thesis by simp }
    moreover 
    { assume linc: "\<exists> li. linearize i = Some li \<and> \<not> (\<exists> bi. li = Cst bi)"
	and ljnc: "\<exists> lj. linearize j = Some lj \<and> \<not> (\<exists> bj. lj = Cst bj)"
      from linc obtain "li" where "linearize i = Some li \<and> \<not> (\<exists> bi. li = Cst bi)" by blast
      moreover 
      from ljnc obtain "lj" where "linearize j = Some lj \<and> \<not> (\<exists> bj. lj = Cst bj)" by blast
      ultimately have "linearize (Mult i j) = None"
	by (cases li, auto simp add: measure_def inv_image_def) (cases lj, auto)+
      with prems have ?thesis by simp }
    ultimately show ?thesis by blast
  qed
qed  

(* the result of linearize, when successful, is a linear term*)
lemma linearize_linear: "\<And> t'. linearize t = Some t' \<Longrightarrow> islinintterm t'"
proof-
  fix t'
  assume lint: "linearize t = Some t'"
  from lint have lt: "linearize t \<noteq> None" by auto
  then have "islinintterm (the (linearize t))" by (rule_tac  linearize_linear1[OF lt])
  with lint show "islinintterm t'" by simp
qed

lemma linearize_corr1: 
  assumes lin: "linearize t \<noteq> None"
  shows "I_intterm ats t = I_intterm ats (the (linearize t))"
using lin
proof (induct t rule: linearize.induct)
  case (3 i) show ?case 
    proof-
    have "(linearize i = None) \<or> (\<exists>li. linearize i = Some li)" by auto
    moreover 
    {
      assume "linearize i = None"
      have ?thesis using prems by simp
    }
    moreover 
    {
      assume lini: "\<exists>li. linearize i = Some li"
      from lini have lini2: "linearize i \<noteq> None" by simp
      from lini obtain "li" where  "linearize i = Some li" by blast
      from lini2 lini have "islinintterm (the (linearize i))"
	by (simp add: linearize_linear1[OF lini2])
      then have linli: "islinintterm li" using prems by simp
      have ieqli: "I_intterm ats i = I_intterm ats li" using prems by simp
      moreover have "linearize (Neg i) = Some (lin_neg li)" using prems by simp
      moreover from ieqli linli have "I_intterm ats (Neg i) = I_intterm ats (lin_neg li)" by (simp add: lin_neg_corr[OF linli])
      ultimately have ?thesis using prems by (simp add: lin_neg_corr)
    }
    ultimately show ?thesis by blast
  qed
next 
  case (4 i j) show ?case 
    proof-
    have "(linearize i = None) \<or> ((\<exists> li. linearize i = Some li) \<and> linearize j = None) \<or> ((\<exists> li. linearize i = Some li) \<and> (\<exists> lj. linearize j = Some lj))" by auto 
    moreover 
    {
      assume nlini: "linearize i = None"
      from nlini have "linearize (Add i j) = None" by (simp add: Let_def measure_def inv_image_def) then have ?thesis using prems by auto
    }
    moreover 
    {
      assume nlinj: "linearize j = None"
	and lini: "\<exists> li. linearize i = Some li"
      from nlinj lini have "linearize (Add i j) = None" 
	by (simp add: Let_def measure_def inv_image_def, auto) 
      then have ?thesis using prems by auto
    }
    moreover 
    {
      assume lini: "\<exists>li. linearize i = Some li"
	and linj: "\<exists>lj. linearize j = Some lj"
      from lini have lini2: "linearize i \<noteq> None" by simp
      from linj have linj2: "linearize j \<noteq> None" by simp
      from lini obtain "li" where  "linearize i = Some li" by blast
      from lini2 have "islinintterm (the (linearize i))" by (simp add: linearize_linear1)
      then have linli: "islinintterm li" using prems by simp
      from linj obtain "lj" where  "linearize j = Some lj" by blast
      from linj2 have "islinintterm (the (linearize j))" by (simp add: linearize_linear1)
      then have linlj: "islinintterm lj" using prems by simp
      moreover from lini linj have "linearize (Add i j) = Some (lin_add (li,lj))"
	using prems by (simp add: measure_def inv_image_def)
      moreover from linli linlj have "I_intterm ats (lin_add (li,lj)) = I_intterm ats (Add li lj)" by (simp add: lin_add_corr)
      ultimately have ?thesis using prems by simp
    }
    ultimately show ?thesis by blast
  qed
next 
  case (5 i j)show ?case 
    proof-
    have "(linearize i = None) \<or> ((\<exists> li. linearize i = Some li) \<and> linearize j = None) \<or> ((\<exists> li. linearize i = Some li) \<and> (\<exists> lj. linearize j = Some lj))" by auto 
    moreover 
    {
      assume nlini: "linearize i = None"
      from nlini have "linearize (Sub i j) = None" by (simp add: Let_def measure_def inv_image_def) then have ?thesis using prems by auto
    }
    moreover 
    {
      assume lini: "\<exists> li. linearize i = Some li"
	and nlinj: "linearize j = None"
      from nlinj lini have "linearize (Sub i j) = None" 
	by (simp add: Let_def measure_def inv_image_def, auto) with prems have ?thesis by auto
    }
    moreover 
    {
      assume lini: "\<exists>li. linearize i = Some li"
	and linj: "\<exists>lj. linearize j = Some lj"
      from lini have lini2: "linearize i \<noteq> None" by simp
      from linj have linj2: "linearize j \<noteq> None" by simp
      from lini obtain "li" where  "linearize i = Some li" by blast
      from lini2 have "islinintterm (the (linearize i))" by (simp add: linearize_linear1)
      with prems have linli: "islinintterm li" by simp
      from linj obtain "lj" where  "linearize j = Some lj" by blast
      from linj2 have "islinintterm (the (linearize j))" by (simp add: linearize_linear1)
      with prems have linlj: "islinintterm lj" by simp
      moreover from prems have "linearize (Sub i j) = Some (lin_add (li,lin_neg lj))" 
	by (simp add: measure_def inv_image_def)
      moreover from linlj have linnlj:"islinintterm (lin_neg lj)" by (simp add: lin_neg_lin)
      moreover from linli linnlj have "I_intterm ats (lin_add (li,lin_neg lj)) = I_intterm ats (Add li (lin_neg lj))" by (simp only: lin_add_corr[OF linli linnlj])
      moreover from linli linlj linnlj have "I_intterm ats (Add li (lin_neg lj)) = I_intterm ats (Sub li lj)" 
	by (simp add: lin_neg_corr)
      ultimately have ?thesis using prems by simp    
    }
    ultimately show ?thesis by blast
  qed
next
  case (6 i j)show ?case 
    proof-
      have cses: "(linearize i = None) \<or> 
	((\<exists> li. linearize i = Some li) \<and> linearize j = None) \<or> 
	((\<exists> li. linearize i = Some li) \<and> (\<exists> bj. linearize j = Some (Cst bj)))
	\<or> ((\<exists> bi. linearize i = Some (Cst bi)) \<and> (\<exists> lj. linearize j = Some lj))
	\<or> ((\<exists> li. linearize i = Some li \<and> \<not> (\<exists> bi. li = Cst bi)) \<and> (\<exists> lj. linearize j = Some lj \<and> \<not> (\<exists> bj. lj = Cst bj)))" by auto 
    moreover 
    {
      assume nlini: "linearize i = None"
      from nlini have "linearize (Mult i j) = None" by (simp add: Let_def measure_def inv_image_def) with prems  have ?thesis by auto
    }
    moreover 
    {
      assume lini: "\<exists> li. linearize i = Some li"
	and nlinj: "linearize j = None"

      from lini obtain "li" where "linearize i = Some li" by blast 
      moreover from prems have "linearize (Mult i j) = None" 
	by (cases li) (simp_all add: Let_def measure_def inv_image_def)
      with prems have ?thesis by auto
    }
    moreover 
    {
      assume lini: "\<exists>li. linearize i = Some li"
	and linj: "\<exists>bj. linearize j = Some (Cst bj)"
      from lini have lini2: "linearize i \<noteq> None" by simp
      from linj have linj2: "linearize j \<noteq> None" by auto
      from lini obtain "li" where  "linearize i = Some li" by blast
      from lini2 have "islinintterm (the (linearize i))" by (simp add: linearize_linear1)
      with prems  have linli: "islinintterm li" by simp
      moreover 
      from linj  obtain "bj" where  "linearize j = Some (Cst bj)" by blast
      have linlj: "islinintterm (Cst bj)" by simp
      moreover from prems have "linearize (Mult i j) = Some (lin_mul (bj,li))"
 	by (cases li) (auto simp add: measure_def inv_image_def) 
      then have lm1: "I_intterm ats (the(linearize (Mult i j))) = I_intterm ats (lin_mul (bj,li))" by simp
      moreover from linli linlj have "I_intterm ats (lin_mul(bj,li)) = I_intterm ats (Mult li (Cst bj))" by (simp add: lin_mul_corr)
      with prems 
      have "I_intterm ats (lin_mul(bj,li)) = I_intterm ats (Mult li (the (linearize j)))" 
	by auto
      moreover have "I_intterm ats (Mult li (the (linearize j))) = I_intterm ats (Mult i (the (linearize j)))" using prems  by simp
      moreover have "I_intterm ats i = I_intterm ats (the (linearize i))"  
	using lini2 lini "6.hyps" by simp
	moreover have "I_intterm ats j = I_intterm ats (the (linearize j))"
	  using prems by (cases li) (auto simp add: measure_def inv_image_def)
      ultimately have ?thesis by auto }
    moreover 
    { assume lini: "\<exists>bi. linearize i = Some (Cst bi)"
	and linj: "\<exists>lj. linearize j = Some lj"
      from lini have lini2 : "linearize i \<noteq> None" by auto
      from linj have linj2 : "linearize j \<noteq> None" by auto      
      from lini obtain "bi" where  "linearize i = Some (Cst bi)" by blast
      have linli: "islinintterm (Cst bi)" using prems by simp
      moreover 
      from linj  obtain "lj" where  "linearize j = Some lj" by blast
      from linj2 have "islinintterm (the (linearize j))" by (simp add: linearize_linear1) 
      then have linlj: "islinintterm lj" by (simp!)
      moreover from linli lini linj have "linearize (Mult i j) = Some (lin_mul (bi,lj))" 	apply (simp add: measure_def inv_image_def) 
	apply auto by (case_tac "li::intterm",auto!)
      then have lm1: "I_intterm ats (the(linearize (Mult i j))) = I_intterm ats (lin_mul (bi,lj))" by simp
      moreover from linli linlj have "I_intterm ats (lin_mul(bi,lj)) = I_intterm ats (Mult (Cst bi) lj)" by (simp add: lin_mul_corr)
      then have "I_intterm ats (lin_mul(bi,lj)) = I_intterm ats (Mult (the (linearize i)) lj)" by (auto!)
      moreover have "I_intterm ats (Mult (the (linearize i)) lj) = I_intterm ats (Mult (the (linearize i)) j)" using lini lini2  by (simp!)
      moreover have "I_intterm ats i = I_intterm ats (the (linearize i))"  
	using lini2 lini "6.hyps" by simp
	moreover have "I_intterm ats j = I_intterm ats (the (linearize j))"
	  using linj linj2 lini lini2 linli linlj "6.hyps" by (auto!)

      ultimately have ?thesis by auto }
    moreover 
    { assume linc: "\<exists> li. linearize i = Some li \<and> \<not> (\<exists> bi. li = Cst bi)"
	and ljnc: "\<exists> lj. linearize j = Some lj \<and> \<not> (\<exists> bj. lj = Cst bj)"
      from linc obtain "li" where "\<exists> li. linearize i = Some li \<and> \<not> (\<exists> bi. li = Cst bi)" by blast
      moreover 
      from ljnc obtain "lj" where "\<exists> lj. linearize j = Some lj \<and> \<not> (\<exists> bj. lj = Cst bj)" by blast
      ultimately have "linearize (Mult i j) = None"
	apply (simp add: measure_def inv_image_def)
	apply (case_tac "linearize i", auto)
	apply (case_tac a)
	apply (auto!)
	by (case_tac "lj",auto)+
      then have ?thesis by (simp!) }
    ultimately show ?thesis by blast
  qed
qed  simp_all


(* linearize, when successfull, preserves semantics *)
lemma linearize_corr: "\<And> t'. linearize t = Some t' \<Longrightarrow> I_intterm ats t = I_intterm ats t' "
proof-
  fix t'
  assume lint: "linearize t = Some t'"
  show  "I_intterm ats t = I_intterm ats t'"
  proof-
    from lint have lt: "linearize t \<noteq> None" by simp 
    then have "I_intterm ats t = I_intterm ats (the (linearize t))" 
      by (rule_tac linearize_corr1[OF lt])
    with lint show ?thesis by simp
  qed
qed

(* tries to linearize a formula *)
consts linform :: "QF \<Rightarrow> QF option"
primrec
"linform (Le it1 it2) =  
  lift_bin(\<lambda>x. \<lambda>y. Le (lin_add(x,lin_neg y)) (Cst 0),linearize it1, linearize it2)"
"linform (Eq it1 it2) =  
  lift_bin(\<lambda>x. \<lambda>y. Eq (lin_add(x,lin_neg y)) (Cst 0),linearize it1, linearize it2)"
"linform (Divides d t) =  
  (case linearize d of
    None \<Rightarrow> None
   | Some ld \<Rightarrow> (case ld of
          Cst b \<Rightarrow> 
               (if (b=0) then None
               else 
                (case linearize t of 
                 None \<Rightarrow> None
               | Some lt \<Rightarrow> Some (Divides ld lt)))
         | _ \<Rightarrow> None))"
"linform  T = Some T"
"linform  F = Some F"
"linform (NOT p) = lift_un NOT (linform p)"
"linform (And p q)= lift_bin(\<lambda>f. \<lambda>g. And f g, linform p, linform q)"
"linform (Or p q) = lift_bin(\<lambda>f. \<lambda>g. Or f g, linform p, linform q)"

(* linearity of formulae *)
consts islinform :: "QF \<Rightarrow> bool"
recdef islinform "measure size"
"islinform (Le it (Cst i)) = (i=0 \<and> islinintterm it )"
"islinform (Eq it (Cst i)) = (i=0 \<and> islinintterm it)"
"islinform (Divides (Cst d) t) = (d \<noteq> 0 \<and> islinintterm t)"
"islinform  T = True"
"islinform  F = True"
"islinform (NOT (Divides (Cst d) t)) = (d \<noteq> 0 \<and> islinintterm t)"
"islinform (NOT (Eq it (Cst i))) = (i=0 \<and> islinintterm it)"
"islinform (And p q)= ((islinform p) \<and> (islinform q))"
"islinform (Or p q) = ((islinform p) \<and> (islinform q))"
"islinform p = False"

(* linform preserves nnf, if successful *)
lemma linform_nnf: 
  assumes nnfp: "isnnf p" 
  shows "\<And> p'. \<lbrakk>linform p = Some p'\<rbrakk> \<Longrightarrow> isnnf p'"
using nnfp
proof (induct p rule: isnnf.induct, simp_all)
  case (goal1 a b p')
  show ?case 
    using prems 
    by (cases "linearize a", auto) (cases "linearize b", auto)
next 
  case (goal2 a b p')
  show ?case 
    using prems 
    by (cases "linearize a", auto) (cases "linearize b", auto)
next 
  case (goal3 d t p')
  show ?case 
    using prems
    apply (cases "linearize d", auto)
    apply (case_tac "a",auto)
    apply (case_tac "int=0",auto)
    by (cases "linearize t",auto)
next
  case (goal4 f g p') show ?case 
    using prems
    by (cases "linform f", auto) (cases "linform g", auto)
next
  case (goal5 f g p') show ?case 
    using prems
    by (cases "linform f", auto) (cases "linform g", auto)
next
  case (goal6 d t p') show ?case 
    using prems
    apply (cases "linearize d", auto)
    apply (case_tac "a", auto)
    apply (case_tac "int = 0",auto)
    by (cases "linearize t", auto)
next 
  case (goal7 a b p')
  show ?case 
    using prems 
    by (cases "linearize a", auto) (cases "linearize b", auto)


qed


lemma linform_corr: "\<And> lp. \<lbrakk> isnnf p ; linform p = Some lp \<rbrakk> \<Longrightarrow> 
                     (qinterp ats p = qinterp ats lp)"
proof (induct p rule: linform.induct)
  case (Le x y)
  show ?case
    using "Le.prems"
  proof-
    have "(\<exists> lx ly. linearize x = Some lx \<and> linearize y = Some ly) \<or> 
      (linearize x = None) \<or> (linearize y = None)"by auto
    moreover 
    {
      assume linxy: "\<exists> lx ly. linearize x = Some lx \<and> linearize y = Some ly"
      from linxy obtain "lx" "ly" 
	where lxly:"linearize x = Some lx \<and> linearize y = Some ly" by blast
      then 
      have lxeqx: "I_intterm ats x = I_intterm ats lx" 
	by (simp add: linearize_corr)
      from lxly have lxlin: "islinintterm lx" 
	by (auto simp add: linearize_linear)
      from lxly have lyeqy: "I_intterm ats y = I_intterm ats ly"
	by (simp add: linearize_corr)
      from lxly have lylin: "islinintterm ly" 
	by (auto simp add: linearize_linear)
      from "prems"
      have lpeqle: "lp =  (Le (lin_add(lx,lin_neg ly)) (Cst 0))"
	by auto
      moreover
      have lin1: "islinintterm (Cst 1)" by simp
      then
      have ?thesis  
	using lxlin lylin lin1 lin_add_lin lin_neg_lin "prems" lxly lpeqle
	by (simp add: lin_add_corr lin_neg_corr lxeqx lyeqy)
      
    }
    
    moreover
    {
      assume "linearize x = None"
      have ?thesis using "prems" by simp
    }
    
    moreover
    {
      assume "linearize y = None"
      then have ?thesis using "prems"
	by (case_tac "linearize x", auto)
    }
    ultimately show ?thesis by blast
  qed
  
next 
  case (Eq x y)
  show ?case
    using "Eq.prems"
  proof-
    have "(\<exists> lx ly. linearize x = Some lx \<and> linearize y = Some ly) \<or> 
      (linearize x = None) \<or> (linearize y = None)"by auto
    moreover 
    {
      assume linxy: "\<exists> lx ly. linearize x = Some lx \<and> linearize y = Some ly"
      from linxy obtain "lx" "ly" 
	where lxly:"linearize x = Some lx \<and> linearize y = Some ly" by blast
      then 
      have lxeqx: "I_intterm ats x = I_intterm ats lx" 
	by (simp add: linearize_corr)
      from lxly have lxlin: "islinintterm lx" 
	by (auto simp add: linearize_linear)
      from lxly have lyeqy: "I_intterm ats y = I_intterm ats ly"
	by (simp add: linearize_corr)
      from lxly have lylin: "islinintterm ly" 
	by (auto simp add: linearize_linear)
      from "prems"
      have lpeqle: "lp =  (Eq (lin_add(lx,lin_neg ly)) (Cst 0))"
	by auto
      moreover
      have lin1: "islinintterm (Cst 1)" by simp
      then
      have ?thesis  
	using lxlin lylin lin1 lin_add_lin lin_neg_lin "prems" lxly lpeqle
	by (simp add: lin_add_corr lin_neg_corr lxeqx lyeqy)
      
    }
    
    moreover
    {
      assume "linearize x = None"
      have ?thesis using "prems" by simp
    }
    
    moreover
    {
      assume "linearize y = None"
      then have ?thesis using "prems"
	by (case_tac "linearize x", auto)
    }
    ultimately show ?thesis by blast
  qed
  
next 
  case (Divides d t)
  show ?case
    using "Divides.prems"
    apply (case_tac "linearize d",auto)
    apply (case_tac a, auto)
    apply (case_tac "int = 0", auto)
    apply (case_tac "linearize t", auto)
    apply (simp add: linearize_corr)
    apply (case_tac a, auto)
    apply (case_tac "int = 0", auto)
    by (case_tac "linearize t", auto simp add: linearize_corr)
next
  case (NOT f) show ?case
    using "prems"
  proof-
    have "(\<exists> lf. linform f = Some lf) \<or> (linform f = None)" by auto
    moreover 
    {
      assume linf: "\<exists> lf. linform f = Some lf"
      from prems have "isnnf (NOT f)" by simp
      then have fnnf: "isnnf f" by (cases f) auto
      from linf obtain "lf" where lf: "linform f = Some lf" by blast
      then have "lp = NOT lf" using "prems" by auto
      with "NOT.prems" "NOT.hyps" lf fnnf
      have ?case by simp
    }
    moreover 
    {
      assume "linform f = None"
      then 
      have "linform (NOT f) = None" by simp
      then 
      have ?thesis  using "NOT.prems" by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (Or f g) 
  show ?case using "Or.hyps"
  proof -
    have "((\<exists> lf. linform f = Some lf ) \<and> (\<exists> lg. linform g = Some lg)) \<or> 
      (linform f = None) \<or> (linform g = None)" by auto
    moreover
    {
      assume linf: "\<exists> lf. linform f = Some lf"
	and ling: "\<exists> lg. linform g = Some lg"
      from linf obtain "lf" where lf: "linform f = Some lf" by blast
      from ling obtain "lg" where lg: "linform g = Some lg" by blast
      from lf lg have "linform (Or f g) = Some (Or lf lg)" by simp
      then have "lp = Or lf lg" using lf lg "prems"  by simp
      with lf lg "prems" have ?thesis by simp
    }
    moreover
    {
      assume "linform f = None"
      then have ?thesis using "Or.prems"  by auto
    }
    moreover
    {
      assume "linform g = None"
      then have ?thesis using "Or.prems"  by (case_tac "linform f", auto)
      
    }
    ultimately show ?thesis by blast
  qed
next
  case (And f g) 
  show ?case using "And.hyps"
  proof -
    have "((\<exists> lf. linform f = Some lf ) \<and> (\<exists> lg. linform g = Some lg)) \<or> 
      (linform f = None) \<or> (linform g = None)" by auto
    moreover
    {
      assume linf: "\<exists> lf. linform f = Some lf"
	and ling: "\<exists> lg. linform g = Some lg"
      from linf obtain "lf" where lf: "linform f = Some lf" by blast
      from ling obtain "lg" where lg: "linform g = Some lg" by blast
      from lf lg have "linform (And f g) = Some (And lf lg)" by simp
      then have "lp = And lf lg" using lf lg "prems"  by simp
      with lf lg "prems" have ?thesis by simp
    }
    moreover
    {
      assume "linform f = None"
      then have ?thesis using "And.prems"  by auto
    }
    moreover
    {
      assume "linform g = None"
      then have ?thesis using "And.prems"  by (case_tac "linform f", auto)
      
    }
    ultimately show ?thesis by blast
  qed

qed simp_all


(* the result of linform is a linear formula *)
lemma linform_lin: "\<And> lp. \<lbrakk> isnnf p ; linform p = Some lp\<rbrakk> \<Longrightarrow> islinform lp"
proof (induct p rule: linform.induct)
   case (Le x y)
  have "((\<exists> lx. linearize x = Some lx) \<and> (\<exists> ly. linearize y = Some ly)) \<or> 
    (linearize x = None) \<or> (linearize y = None) " by clarsimp
  moreover 
  {
    assume linx: "\<exists> lx. linearize x = Some lx"
      and liny: "\<exists> ly. linearize y = Some ly"
    from linx obtain "lx" where lx: "linearize x = Some lx" by blast
    from liny obtain "ly" where ly: "linearize y = Some ly" by blast
    from lx have lxlin: "islinintterm lx" by (simp add: linearize_linear)
    from ly have lylin: "islinintterm ly" by (simp add: linearize_linear)    
    have lin1:"islinintterm (Cst 1)" by simp
    have lin0: "islinintterm (Cst 0)" by simp
    from "prems"  have "lp = Le (lin_add(lx,lin_neg ly)) (Cst 0)"
      by auto
    with lin0 lin1 lxlin lylin "prems" 
    have ?case by (simp add: lin_add_lin lin_neg_lin)
    
  }

  moreover 
  {
    assume "linearize x = None"
    then have ?case using "prems" by simp
  }
  moreover 
  {
    assume "linearize y = None"
    then have ?case using "prems" by (case_tac "linearize x",simp_all)
  }
  ultimately show ?case by blast
next
   case (Eq x y)
  have "((\<exists> lx. linearize x = Some lx) \<and> (\<exists> ly. linearize y = Some ly)) \<or> 
    (linearize x = None) \<or> (linearize y = None) " by clarsimp
  moreover 
  {
    assume linx: "\<exists> lx. linearize x = Some lx"
      and liny: "\<exists> ly. linearize y = Some ly"
    from linx obtain "lx" where lx: "linearize x = Some lx" by blast
    from liny obtain "ly" where ly: "linearize y = Some ly" by blast
    from lx have lxlin: "islinintterm lx" by (simp add: linearize_linear)
    from ly have lylin: "islinintterm ly" by (simp add: linearize_linear)    
    have lin1:"islinintterm (Cst 1)" by simp
    have lin0: "islinintterm (Cst 0)" by simp
    from "prems"  have "lp = Eq (lin_add(lx,lin_neg ly)) (Cst 0)"
      by auto
    with lin0 lin1 lxlin lylin "prems" 
    have ?case by (simp add: lin_add_lin lin_neg_lin)
    
  }

  moreover 
  {
    assume "linearize x = None"
    then have ?case using "prems" by simp
  }
  moreover 
  {
    assume "linearize y = None"
    then have ?case using "prems" by (case_tac "linearize x",simp_all)
  }
  ultimately show ?case by blast
next
   case (Divides d t)
   show ?case 
     using prems
     apply (case_tac "linearize d", auto)
     apply (case_tac a, auto)
     apply (case_tac "int = 0", auto)

     by (case_tac "linearize t",auto simp add: linearize_linear)
next
  case (Or f g)
 show ?case using "Or.hyps"
  proof -
    have "((\<exists> lf. linform f = Some lf ) \<and> (\<exists> lg. linform g = Some lg)) \<or> 
      (linform f = None) \<or> (linform g = None)" by auto
    moreover
    {
      assume linf: "\<exists> lf. linform f = Some lf"
	and ling: "\<exists> lg. linform g = Some lg"
      from linf obtain "lf" where lf: "linform f = Some lf" by blast
      from ling obtain "lg" where lg: "linform g = Some lg" by blast
      from lf lg have "linform (Or f g) = Some (Or lf lg)" by simp
      then have "lp = Or lf lg" using lf lg "prems"  by simp
      with lf lg "prems" have ?thesis by simp
    }
    moreover
    {
      assume "linform f = None"
      then have ?thesis using "Or.prems"  by auto
    }
    moreover
    {
      assume "linform g = None"
      then have ?thesis using "Or.prems"  by (case_tac "linform f", auto)
      
    }
    ultimately show ?thesis by blast
  qed
next
  case (And f g) 
  show ?case using "And.hyps"
  proof -
    have "((\<exists> lf. linform f = Some lf ) \<and> (\<exists> lg. linform g = Some lg)) \<or> 
      (linform f = None) \<or> (linform g = None)" by auto
    moreover
    {
      assume linf: "\<exists> lf. linform f = Some lf"
	and ling: "\<exists> lg. linform g = Some lg"
      from linf obtain "lf" where lf: "linform f = Some lf" by blast
      from ling obtain "lg" where lg: "linform g = Some lg" by blast
      from lf lg have "linform (And f g) = Some (And lf lg)" by simp
      then have "lp = And lf lg" using lf lg "prems"  by simp
      with lf lg "prems" have ?thesis by simp
    }
    moreover
    {
      assume "linform f = None"
      then have ?thesis using "And.prems"  by auto
    }
    moreover
    {
      assume "linform g = None"
      then have ?thesis using "And.prems"  by (case_tac "linform f", auto)
      
    }
    ultimately show ?thesis by blast
  qed
next
  case (NOT f) show ?case
    using "prems"
  proof-
    have "(\<exists> lf. linform f = Some lf) \<or> (linform f = None)" by auto
    moreover 
    {
      assume linf: "\<exists> lf. linform f = Some lf"
      from prems have "isnnf (NOT f)" by simp
      then have fnnf: "isnnf f" by (cases f) auto
      from linf obtain "lf" where lf: "linform f = Some lf" by blast
      then have "lp = NOT lf" using "prems" by auto
      with "NOT.prems" "NOT.hyps" lf fnnf
      have ?thesis 
	using fnnf
	apply (cases f, auto) 
	prefer 2
	apply (case_tac "linearize intterm1",auto)
	apply (case_tac a, auto)
	apply (case_tac "int = 0", auto)
	apply (case_tac "linearize intterm2") 
	apply (auto simp add: linearize_linear)
	apply (case_tac "linearize intterm1",auto)
	by (case_tac "linearize intterm2") 
      (auto simp add: linearize_linear lin_add_lin lin_neg_lin)
    }
    moreover 
    {
      assume "linform f = None"
      then 
      have "linform (NOT f) = None" by simp
      then 
      have ?thesis  using "NOT.prems" by simp
    }
    ultimately show ?thesis by blast
  qed
qed (simp_all)


(* linform, if successfull, preserves quantifier freeness *)
lemma linform_isnnf: "islinform p \<Longrightarrow> isnnf p"
by (induct p rule: islinform.induct) auto

lemma linform_isqfree: "islinform p \<Longrightarrow> isqfree p"
using linform_isnnf nnf_isqfree by simp

lemma linform_qfree: "\<And> p'. \<lbrakk> isnnf p ; linform p = Some p'\<rbrakk> \<Longrightarrow> isqfree p'"
using linform_isqfree linform_lin 
by simp

(* Definitions and lemmas about gcd and lcm *)
constdefs lcm :: "nat \<times> nat \<Rightarrow> nat"
  "lcm \<equiv> (\<lambda>(m,n). m*n div gcd(m,n))"

constdefs ilcm :: "int \<Rightarrow> int \<Rightarrow> int"
  "ilcm \<equiv> \<lambda>i.\<lambda>j. int (lcm(nat(abs i),nat(abs j)))"

(* ilcm_dvd12 are needed later *)
lemma lcm_dvd1: 
  assumes mpos: " m >0"
  and npos: "n>0"
  shows "m dvd (lcm(m,n))"
proof-
  have "gcd(m,n) dvd n" by simp
  then obtain "k" where "n = gcd(m,n) * k" using dvd_def by auto
  then have "m*n div gcd(m,n) = m*(gcd(m,n)*k) div gcd(m,n)" by (simp add: mult_ac)
  also have "\<dots> = m*k" using mpos npos gcd_zero by simp
  finally show ?thesis by (simp add: lcm_def)
qed

lemma lcm_dvd2: 
  assumes mpos: " m >0"
  and npos: "n>0"
  shows "n dvd (lcm(m,n))"
proof-
  have "gcd(m,n) dvd m" by simp
  then obtain "k" where "m = gcd(m,n) * k" using dvd_def by auto
  then have "m*n div gcd(m,n) = (gcd(m,n)*k)*n div gcd(m,n)" by (simp add: mult_ac)
  also have "\<dots> = n*k" using mpos npos gcd_zero by simp
  finally show ?thesis by (simp add: lcm_def)
qed

lemma ilcm_dvd1: 
assumes anz: "a \<noteq> 0" 
  and bnz: "b \<noteq> 0"
  shows "a dvd (ilcm a b)"
proof-
  let ?na = "nat (abs a)"
  let ?nb = "nat (abs b)"
  have nap: "?na >0" using anz by simp
  have nbp: "?nb >0" using bnz by simp
  from nap nbp have "?na dvd lcm(?na,?nb)" using lcm_dvd1 by simp
  thus ?thesis by (simp add: ilcm_def dvd_int_iff)
qed


lemma ilcm_dvd2: 
assumes anz: "a \<noteq> 0" 
  and bnz: "b \<noteq> 0"
  shows "b dvd (ilcm a b)"
proof-
  let ?na = "nat (abs a)"
  let ?nb = "nat (abs b)"
  have nap: "?na >0" using anz by simp
  have nbp: "?nb >0" using bnz by simp
  from nap nbp have "?nb dvd lcm(?na,?nb)" using lcm_dvd2 by simp
  thus ?thesis by (simp add: ilcm_def dvd_int_iff)
qed

lemma zdvd_self_abs1: "(d::int) dvd (abs d)"
by (case_tac "d <0", simp_all)

lemma zdvd_self_abs2: "(abs (d::int)) dvd d"
by (case_tac "d<0", simp_all)

(* lcm a b is positive for positive a and b *)

lemma lcm_pos: 
  assumes mpos: "m > 0"
  and npos: "n>0"
  shows "lcm (m,n) > 0"

proof(rule ccontr, simp add: lcm_def gcd_zero)
assume h:"m*n div gcd(m,n) = 0"
from mpos npos have "gcd (m,n) \<noteq> 0" using gcd_zero by simp
hence gcdp: "gcd(m,n) > 0" by simp
with h
have "m*n < gcd(m,n)"
  by (cases "m * n < gcd (m, n)") (auto simp add: div_if[OF gcdp, where m="m*n"])
moreover 
have "gcd(m,n) dvd m" by simp
 with mpos dvd_imp_le have t1:"gcd(m,n) \<le> m" by simp
 with npos have t1:"gcd(m,n)*n \<le> m*n" by simp
 have "gcd(m,n) \<le> gcd(m,n)*n" using npos by simp
 with t1 have "gcd(m,n) \<le> m*n" by arith
ultimately show "False" by simp
qed

lemma ilcm_pos: 
  assumes apos: " 0 < a"
  and bpos: "0 < b" 
  shows "0 < ilcm  a b"
proof-
  let ?na = "nat (abs a)"
  let ?nb = "nat (abs b)"
  have nap: "?na >0" using apos by simp
  have nbp: "?nb >0" using bpos by simp
  have "0 < lcm (?na,?nb)" by (rule lcm_pos[OF nap nbp])
  thus ?thesis by (simp add: ilcm_def)
qed

(* fomlcm computes the lcm of all c, where c is the coeffitient of Var 0 *)
consts formlcm :: "QF \<Rightarrow> int"
recdef formlcm "measure size"
"formlcm (Le (Add (Mult (Cst c) (Var 0)) r) (Cst i)) = abs c "
"formlcm (Eq (Add (Mult (Cst c) (Var 0)) r) (Cst i)) = abs c "
"formlcm (Divides (Cst d) (Add (Mult (Cst c) (Var 0)) r)) = abs c"
"formlcm (NOT p) = formlcm p"
"formlcm (And p q)= ilcm (formlcm p) (formlcm q)"
"formlcm (Or p q) = ilcm (formlcm p) (formlcm q)"
"formlcm p = 1"

(* the property that formlcm should fullfill *)
consts divideallc:: "int \<times> QF \<Rightarrow> bool"
recdef divideallc "measure (\<lambda>(i,p). size p)"
"divideallc (l,Le (Add (Mult (Cst c) (Var 0)) r) (Cst i)) = (c dvd l)"
"divideallc (l,Eq (Add (Mult (Cst c) (Var 0)) r) (Cst i)) = (c dvd l)"
"divideallc(l,Divides (Cst d) (Add (Mult (Cst c) (Var 0)) r)) = (c dvd l)"
"divideallc (l,NOT p) = divideallc(l,p)"
"divideallc (l,And p q) = (divideallc (l,p) \<and> divideallc (l,q))"
"divideallc (l,Or p q) = (divideallc (l,p) \<and> divideallc (l,q))"
"divideallc p = True"

(* formlcm retuns a positive integer *)
lemma formlcm_pos: 
  assumes linp: "islinform p"
  shows "0 < formlcm p"
using linp
proof (induct p rule: formlcm.induct, simp_all add: ilcm_pos)
  case (goal1 c r i)
  have "i=0 \<or> i \<noteq> 0" by simp
  moreover
  {
    assume "i \<noteq> 0" then have ?case using prems by simp
  }
  moreover 
  {
    assume iz: "i = 0"
    then have "islinintterm (Add (Mult (Cst c) (Var 0)) r)" using prems by simp
    then have "c\<noteq>0" 
      using prems
      by (simp add: islininttermc0r[where c="c" and n="0" and r="r"])
    then have ?case by simp
  }
  ultimately 
  show ?case by blast
next 
  case (goal2 c r i)
  have "i=0 \<or> i \<noteq> 0" by simp
  moreover
  {
    assume "i \<noteq> 0" then have ?case using prems by simp
  }
  moreover 
  {
    assume iz: "i = 0"
    then have "islinintterm (Add (Mult (Cst c) (Var 0)) r)" using prems by simp
    then have "c\<noteq>0" 
      using prems
      by (simp add: islininttermc0r[where c="c" and n="0" and r="r"])
    then have ?case by simp
  }
  ultimately 
  show ?case by blast

next 
  case (goal3 d c r)
  show ?case using prems by (simp add: islininttermc0r[where c="c" and n="0" and r="r"])
next
  case (goal4 f)
  show ?case using prems 
    by (cases f,auto) (case_tac "intterm2", auto,case_tac "intterm1", auto)
qed

lemma divideallc_mono: "\<And> c. \<lbrakk> divideallc(c,p) ; c dvd d\<rbrakk> \<Longrightarrow> divideallc (d,p)"
proof (induct d p rule: divideallc.induct, simp_all)
  case (goal1 l a b) show ?case by ( rule zdvd_trans [where m="a" and n="b" and k="l"])
next
  case (goal2 l a b) show ?case by ( rule zdvd_trans [where m="a" and n="b" and k="l"])
next
 case (goal3 l a b) show ?case by ( rule zdvd_trans [where m="a" and n="b" and k="l"])
next
  case (goal4 l f g k)
  have  "divideallc (l,g)" using prems by clarsimp
  moreover have "divideallc (l,f)" using prems by clarsimp
  ultimately
  show ?case  by simp
next 
  case (goal5 l f g k)
  have  "divideallc (l,g)" using prems by clarsimp
  moreover have "divideallc (l,f)" using prems by clarsimp
  ultimately
  show ?case  by simp
  
qed

(* fomlcm retuns a number all coeffitients of Var 0 divide *)

lemma formlcm_divideallc: 
  assumes linp: "islinform p"
  shows "divideallc(formlcm p, p)"
using linp
proof (induct p rule: formlcm.induct, simp_all add: zdvd_self_abs1)
  case (goal1 f)
  show ?case using prems
    by (cases f,auto) (case_tac "intterm2", auto, case_tac "intterm1",auto)
next 
  case (goal2 f g)
  have "formlcm f >0" using formlcm_pos prems by simp 
    hence "formlcm f \<noteq> 0" by simp
  moreover have "formlcm g > 0" using formlcm_pos prems by simp
  hence "formlcm g \<noteq> 0" by simp
  ultimately
  show ?case using prems formlcm_pos
     by (simp add: ilcm_dvd1 ilcm_dvd2 
       divideallc_mono[where c="formlcm f" and d="ilcm (formlcm f) (formlcm g)"]  
       divideallc_mono[where c="formlcm g" and d="ilcm (formlcm f) (formlcm g)"])
next 
  case (goal3 f g)
  have "formlcm f >0" using formlcm_pos prems by simp 
    hence "formlcm f \<noteq> 0" by simp
  moreover have "formlcm g > 0" using formlcm_pos prems by simp
  hence "formlcm g \<noteq> 0" by simp
  ultimately
  show ?case using prems 
    by (simp add: ilcm_dvd1 ilcm_dvd2 
      divideallc_mono[where c="formlcm f" and d="ilcm (formlcm f) (formlcm g)"]  
      divideallc_mono[where c="formlcm g" and d="ilcm (formlcm f) (formlcm g)"])
qed

(* adjustcoeff transforms the formula given an l , look at correctness thm*)
consts adjustcoeff :: "int \<times> QF \<Rightarrow> QF"
recdef adjustcoeff "measure (\<lambda>(l,p). size p)"
"adjustcoeff (l,(Le (Add (Mult (Cst c) (Var 0)) r) (Cst i))) = 
  (if c\<le>0 then 
  Le (Add (Mult (Cst -1) (Var 0)) (lin_mul (- (l div c), r))) (Cst (0::int))
  else
  Le (Add (Mult (Cst 1) (Var 0)) (lin_mul (l div c, r))) (Cst (0::int)))"
"adjustcoeff (l,(Eq (Add (Mult (Cst c) (Var 0)) r) (Cst i))) = 
  (Eq (Add (Mult (Cst 1) (Var 0)) (lin_mul (l div c, r))) (Cst (0::int)))"
"adjustcoeff (l,Divides (Cst d) (Add (Mult (Cst c) (Var 0)) r)) = 
  Divides (Cst ((l div c) * d))
  (Add (Mult (Cst 1) (Var 0)) (lin_mul (l div c, r)))"
"adjustcoeff (l,NOT (Divides (Cst d) (Add (Mult (Cst c) (Var 0)) r))) = NOT (Divides (Cst ((l div c) * d))
  (Add (Mult (Cst 1) (Var 0)) (lin_mul (l div c, r))))"
"adjustcoeff (l,(NOT(Eq (Add (Mult (Cst c) (Var 0)) r) (Cst i)))) = 
  (NOT(Eq (Add (Mult (Cst 1) (Var 0)) (lin_mul (l div c, r))) (Cst (0::int))))"
"adjustcoeff (l,And p q) = And (adjustcoeff (l,p)) (adjustcoeff(l,q))"
"adjustcoeff (l,Or p q) = Or (adjustcoeff (l,p)) (adjustcoeff(l,q))"
"adjustcoeff (l,p) = p"


(* unitycoeff expects a quantifier free formula an transforms it to an equivalent formula where the bound variable occurs only with coeffitient 1  or -1 *)
constdefs unitycoeff :: "QF \<Rightarrow> QF"
  "unitycoeff p == 
  (let l = formlcm p;
       p' = adjustcoeff (l,p)
   in (if l=1 then p' else 
      (And (Divides (Cst l) (Add (Mult (Cst 1) (Var 0)) (Cst 0))) p')))"

(* what is a unified formula *)
consts isunified :: "QF \<Rightarrow> bool"
recdef isunified "measure size"
"isunified (Le (Add (Mult (Cst i) (Var 0)) r) (Cst z)) = 
  ((abs i) = 1  \<and> (islinform(Le (Add (Mult (Cst i) (Var 0)) r) (Cst z))))"
"isunified (Eq (Add (Mult (Cst i) (Var 0)) r) (Cst z)) = 
  ((abs i) = 1  \<and> (islinform(Le (Add (Mult (Cst i) (Var 0)) r) (Cst z))))"
"isunified (NOT(Eq (Add (Mult (Cst i) (Var 0)) r) (Cst z))) = 
  ((abs i) = 1  \<and> (islinform(Le (Add (Mult (Cst i) (Var 0)) r) (Cst z))))"
"isunified (Divides (Cst d) (Add (Mult (Cst i) (Var 0)) r)) = 
  ((abs i) = 1 \<and> (islinform(Divides (Cst d) (Add (Mult (Cst i) (Var 0)) r))))"
"isunified (NOT(Divides (Cst d) (Add (Mult (Cst i) (Var 0)) r))) = 
  ((abs i) = 1 \<and> (islinform(NOT(Divides (Cst d) (Add (Mult (Cst i) (Var 0)) r)))))"
"isunified (And p q) = (isunified p \<and> isunified q)"
"isunified (Or p q) = (isunified p \<and> isunified q)"
"isunified p = islinform p"

lemma unified_islinform: "isunified p \<Longrightarrow> islinform p"
by (induct p rule: isunified.induct) auto

lemma adjustcoeff_lenpos: 
  "0 < n \<Longrightarrow> adjustcoeff (l, Le (Add (Mult (Cst i) (Var n)) r) (Cst c)) =
    Le (Add (Mult (Cst i) (Var n)) r) (Cst c)"
by (cases n, auto)

lemma adjustcoeff_eqnpos: 
  "0 < n \<Longrightarrow> adjustcoeff (l, Eq (Add (Mult (Cst i) (Var n)) r) (Cst c)) =
    Eq (Add (Mult (Cst i) (Var n)) r) (Cst c)"
by (cases n, auto)


(* Properties of adjustcoeff and unitycoeff *)

(* Some simple lemmas used afterwards *)
lemma zmult_zle_mono: "(i::int) \<le> j \<Longrightarrow> 0 \<le> k \<Longrightarrow> k * i \<le> k * j"
  apply (erule order_le_less [THEN iffD1, THEN disjE, of "0::int"])
  apply (erule order_le_less [THEN iffD1, THEN disjE])
  apply (rule order_less_imp_le)
  apply (rule zmult_zless_mono2)
  apply simp_all
  done

lemma zmult_zle_mono_eq:
  assumes kpos: "0 < k"
  shows "((i::int) \<le> j) = (k*i \<le> k*j)" (is "?P = ?Q")
proof
  assume P: ?P
  from kpos have kge0: "0 \<le> k" by simp
  show ?Q
    by (rule zmult_zle_mono[OF P kge0])
next 
  assume ?Q
  then have "k*i - k*j \<le> 0" by simp
  then have le1: "k*(i-j) \<le> k*0"
    by (simp add: zdiff_zmult_distrib2)
  have "i -j \<le> 0" 
    by (rule mult_left_le_imp_le[OF le1 kpos])
  then 
  show ?P by simp
qed
  

lemma adjustcoeff_le_corr:
  assumes lpos: "0 < l"
  and ipos: "0 < (i::int)"
  and dvd: "i dvd l"
  shows "(i*x + r \<le> 0) = (l*x + ((l div i)*r) \<le> 0)"
proof-
  from lpos ipos have ilel: "i\<le>l" by (simp add: zdvd_imp_le [OF dvd lpos])
  from ipos have inz: "i \<noteq> 0" by simp
  have "i div i\<le> l div i"
    by (simp add: zdiv_mono1[OF ilel ipos])
  then have ldivipos:"0 < l div i" 
    by (simp add: zdiv_self[OF inz])
  
  from dvd have "\<exists>i'. i*i' = l" by (auto simp add: dvd_def)
  then obtain "i'" where ii'eql: "i*i' = l" by blast
  have "(i * x + r \<le> 0) = (l div i * (i * x + r) \<le> l div i * 0)"
    by (rule zmult_zle_mono_eq[OF ldivipos, where i="i*x + r" and j="0"])
  also
  have "(l div i * (i * x + r) \<le> l div i * 0) = ((l div i * i) * x + ((l div i)*r) \<le> 0)"
    by (simp add: mult_ac)
  also have "((l div i * i) * x + ((l div i)*r) \<le> 0) = (l*x + ((l div i)*r) \<le> 0)"
    using sym[OF ii'eql] inz
    by (simp add: zmult_ac)
  finally  
  show ?thesis
    by simp
qed

lemma adjustcoeff_le_corr2:
  assumes lpos: "0 < l"
  and ineg: "(i::int) < 0"
  and dvd: "i dvd l"
  shows "(i*x + r \<le> 0) = ((-l)*x + ((-(l div i))*r) \<le> 0)"
proof-
  from dvd have midvdl: "-i dvd l" by simp
  from ineg have mipos: "0 < -i" by simp
  from lpos ineg have milel: "-i\<le>l" by (simp add: zdvd_imp_le [OF midvdl lpos])
  from ineg have inz: "i \<noteq> 0" by simp
  have "l div i\<le> -i div i"
    by (simp add: zdiv_mono1_neg[OF milel ineg])
  then have "l div i \<le> -1" 
    apply (simp add: zdiv_zminus1_eq_if[OF inz, where a="i"])
    by (simp add: zdiv_self[OF inz])
  then have ldivineg: "l div i < 0" by simp
  then have mldivipos: "0 < - (l div i)" by simp
  
  from dvd have "\<exists>i'. i*i' = l" by (auto simp add: dvd_def)
  then obtain "i'" where ii'eql: "i*i' = l" by blast
  have "(i * x + r \<le> 0) = (- (l div i) * (i * x + r) \<le> - (l div i) * 0)"
    by (rule zmult_zle_mono_eq[OF mldivipos, where i="i*x + r" and j="0"])
  also
  have "(- (l div i) * (i * x + r) \<le> - (l div i) * 0) = (-((l div i) * i) * x \<le> (l div i)*r)"
    by (simp add: mult_ac)
  also have " (-((l div i) * i) * x \<le> (l div i)*r) = (- (l*x) \<le> (l div i)*r)"
    using sym[OF ii'eql] inz
    by (simp add: zmult_ac)
  finally  
  show ?thesis
    by simp
qed

(* FIXME : Move this theorem above, it simplifies the 2 theorems above : adjustcoeff_le_corr1,2 *)
lemma dvd_div_pos: 
  assumes bpos: "0 < (b::int)"
  and anz: "a\<noteq>0"
  and dvd: "a dvd b"
  shows "(b div a)*a = b"
proof-
  from anz have "0 < a \<or> a < 0" by arith
  moreover
  {
    assume apos: "0 < a" 
    from bpos apos have aleb: "a\<le>b" by (simp add: zdvd_imp_le [OF dvd bpos])
    have "a div a\<le> b div a"
      by (simp add: zdiv_mono1[OF aleb apos])
    then have bdivapos:"0 < b div a" 
      by (simp add: zdiv_self[OF anz])
    
    from dvd have "\<exists>a'. a*a' = b" by (auto simp add: dvd_def)
    then obtain "a'" where aa'eqb: "a*a' = b" by blast
    then have ?thesis  using anz sym[OF aa'eqb] by simp
    
  }
  moreover
  {
    assume aneg: "a < 0"
    from dvd have midvdb: "-a dvd b" by simp
    from aneg have mapos: "0 < -a" by simp
    from bpos aneg have maleb: "-a\<le>b" by (simp add: zdvd_imp_le [OF midvdb bpos])
    from aneg have anz: "a \<noteq> 0" by simp
    have "b div a\<le> -a div a"
      by (simp add: zdiv_mono1_neg[OF maleb aneg])
    then have "b div a \<le> -1" 
      apply (simp add: zdiv_zminus1_eq_if[OF anz, where a="a"])
      by (simp add: zdiv_self[OF anz])
    then have bdivaneg: "b div a < 0" by simp
    then have mbdivapos: "0 < - (b div a)" by simp
    
    from dvd have "\<exists>a'. a*a' = b" by (auto simp add: dvd_def)
    then obtain "a'" where aa'eqb: "a*a' = b" by blast
    then have ?thesis using anz sym[OF aa'eqb] by (simp)
  }
  ultimately show ?thesis by blast
qed

lemma adjustcoeff_eq_corr: 
  assumes lpos: "(0::int) < l"
  and inz: "i \<noteq> 0"
  and dvd: "i dvd l"
  shows "(i*x + r = 0) = (l*x + ((l div i)*r) = 0)"
proof-
  have ldvdii: "(l div i)*i = l" by (rule dvd_div_pos[OF lpos inz dvd])
  have ldivinz: "l div i \<noteq> 0" using inz ldvdii lpos by auto
  have "(i*x + r = 0) = ((l div i)*(i*x + r) = (l div i)*0)"
    using ldivinz by arith
  also have "\<dots> = (((l div i)*i)*x + (l div i)*r = 0)"
    by (simp add: zmult_ac)
  finally show ?thesis using ldvdii by simp
qed



(* Correctness theorem for adjustcoeff *)
lemma adjustcoeff_corr:
  assumes linp: "islinform p"
  and alldvd: "divideallc (l,p)"
  and lpos: "0 < l"
  shows "qinterp (a#ats) p = qinterp ((a*l)#ats) (adjustcoeff(l, p))"
using linp alldvd
proof (induct p rule: islinform.induct,simp_all)
  case (goal1 t c)
  from prems have cz: "c=0" by simp
    then have ?case
      using prems
    proof(induct t rule: islinintterm.induct)
      case (2 i n i') show ?case using prems
	proof-
	  from prems have "i\<noteq>0" by simp
	  then 
	  have "(n=0 \<and> i < 0) \<or> (n=0 \<and> i > 0) \<or> n\<noteq>0" by arith
	  moreover 
	  {
	    assume "n\<noteq>0" then have ?thesis 
	      by (simp add: nth_pos2 adjustcoeff_lenpos)
	  }
	  moreover
	  {
	    assume nz: "n=0"
	      and ipos: "0 < i"
	    from prems nz have idvdl: "i dvd l" by simp
	    have "(i*a + i' \<le> 0) = (l*a+ ((l div i)*i') \<le> 0)" 
	      by (rule adjustcoeff_le_corr[OF lpos ipos idvdl])
	    then 
	    have ?thesis using prems by (simp add: mult_ac)
	  }
	  moreover
	  {
	    assume nz: "n=0"
	      and ineg: "i < 0"
	    from prems nz have idvdl: "i dvd l" by simp
	    have "(i*a+i' \<le> 0) = (-l*a + (-(l div i) * i') \<le> 0)"
	      by (rule adjustcoeff_le_corr2[OF lpos ineg idvdl])
	    then 
	    have ?thesis using prems
	      by (simp add: zmult_ac)
	  }
	  ultimately show ?thesis by blast
	qed
      next
	case (3 i n i' n' r) show ?case  using prems
	proof-
	  from prems 
	  have lininrp: "islinintterm (Add (Mult (Cst i') (Var n')) r)" 
	    by simp
	  then
	  have "islint (Add (Mult (Cst i') (Var n')) (r))" 
	    by (simp add: islinintterm_eq_islint)
	  then have linr: "islintn(Suc n',r)"
	    by (simp add: islinintterm_subt[OF lininrp] islinintterm_eq_islint islint_def)
	  from lininrp have linr2: "islinintterm r"
	    by (simp add: islinintterm_subt[OF lininrp])
	  from prems have "n < n'" by simp
	  then have nppos: "0 < n'" by simp
	  from prems have "i\<noteq>0" by simp
	  then 
	  have "(n=0 \<and> i < 0) \<or> (n=0 \<and> i > 0) \<or> n\<noteq>0" by arith
	  moreover 
	  {
	    assume nnz: "n\<noteq>0"
	    from linr have ?thesis using nppos nnz intterm_novar0[OF lininrp] prems
	      apply (simp add: adjustcoeff_lenpos linterm_novar0[OF linr, where x="a" and y="a*l"])
	      by (simp add: nth_pos2)
	      
	  }
	  moreover
	  {
	    assume nz: "n=0"
	      and ipos: "0 < i"
	    from prems nz have idvdl: "i dvd l" by simp
	    have "(i * a + (i' * (a # ats) ! n' + I_intterm (a # ats) r) \<le> 0) =
	      (l * a + l div i * (i' * (a # ats) ! n' + I_intterm (a # ats) r) \<le> 0)"
	      by (rule adjustcoeff_le_corr[OF lpos ipos idvdl])
	    then 
	    have ?thesis using prems linr linr2
	      by (simp add: mult_ac nth_pos2 lin_mul_corr 
		linterm_novar0[OF linr, where x="a" and y="a*l"])
	  }
	  moreover
	  {
	    assume nz: "n=0"
	      and ineg: "i < 0"
	    from prems nz have idvdl: "i dvd l" by simp
	    have "(i * a + (i' * (a # ats) ! n' + I_intterm (a # ats) r) \<le> 0) =
	      (- l * a + - (l div i) * (i' * (a # ats) ! n' + I_intterm (a # ats) r) \<le> 0)"
	      by (rule adjustcoeff_le_corr2[OF lpos ineg idvdl, where  x="a" and r="(i'* (a#ats) ! n' + I_intterm (a#ats) r )"])
	    then 
	    have ?thesis using prems linr linr2
	      by (simp add: zmult_ac nth_pos2 lin_mul_corr 
		linterm_novar0[OF linr, where x="a" and y="a*l"] )
	  }
	  ultimately show ?thesis by blast
	qed	  
    qed simp_all
    then show ?case by simp 
  
next
  case (goal2 t c)
  from prems have cz: "c=0" by simp
    then have ?case
      using prems
    proof(induct t rule: islinintterm.induct)
      case (2 i n i') show ?case using prems
	proof-
	  from prems have inz: "i\<noteq>0" by simp
	  then 
	  have "n=0 \<or> n\<noteq>0" by arith
	  moreover 
	  {
	    assume "n\<noteq>0" then have ?thesis 
	      by (simp add: nth_pos2 adjustcoeff_eqnpos)
	  }
	  moreover
	  {
	    assume nz: "n=0"
	    from prems nz have idvdl: "i dvd l" by simp
	    have "(i*a + i' = 0) = (l*a+ ((l div i)*i') = 0)" 
	      by (rule adjustcoeff_eq_corr[OF lpos inz idvdl])
	    then 
	    have ?thesis using prems by (simp add: mult_ac)
	  }
	  ultimately show ?thesis by blast
	qed
      next
	case (3 i n i' n' r) show ?case  using prems
	proof-
	  from prems 
	  have lininrp: "islinintterm (Add (Mult (Cst i') (Var n')) r)" 
	    by simp
	  then
	  have "islint (Add (Mult (Cst i') (Var n')) (r))" 
	    by (simp add: islinintterm_eq_islint)
	  then have linr: "islintn(Suc n',r)"
	    by (simp add: islinintterm_subt[OF lininrp] islinintterm_eq_islint islint_def)
	  from lininrp have linr2: "islinintterm r"
	    by (simp add: islinintterm_subt[OF lininrp])
	  from prems have "n < n'" by simp
	  then have nppos: "0 < n'" by simp
	  from prems have "i\<noteq>0" by simp
	  then 
	  have "n=0 \<or> n\<noteq>0" by arith
	  moreover 
	  {
	    assume nnz: "n\<noteq>0"
	    from linr have ?thesis using nppos nnz intterm_novar0[OF lininrp] prems
	      apply (simp add: adjustcoeff_eqnpos linterm_novar0[OF linr, where x="a" and y="a*l"])
	      by (simp add: nth_pos2)
	      
	  }
	  moreover
	  {
	    assume nz: "n=0"
	    from prems have inz: "i \<noteq> 0" by auto
	    from prems nz have idvdl: "i dvd l" by simp
	    have "(i * a + (i' * (a # ats) ! n' + I_intterm (a # ats) r) = 0) =
	      (l * a + l div i * (i' * (a # ats) ! n' + I_intterm (a # ats) r) = 0)"
	      by (rule adjustcoeff_eq_corr[OF lpos inz idvdl])
	    then 
	    have ?thesis using prems linr linr2
	      by (simp add: mult_ac nth_pos2 lin_mul_corr 
		linterm_novar0[OF linr, where x="a" and y="a*l"])
	  }
	  ultimately show ?thesis by blast
	qed	  
    qed simp_all
    then show ?case by simp 
  
next
  case (goal3 d t) show ?case
    using prems
    proof (induct t rule: islinintterm.induct)
      case (2 i n i') 
      have "n=0 \<or> (\<exists>m. (n = Suc m))" by arith
      moreover
      {
	assume "\<exists>m. n = Suc m"
	then have ?case using prems  by auto
      }
      moreover 
      {
	assume nz: "n=0"
	from prems have inz: "i\<noteq>0" by simp
	from prems have idvdl: "i dvd l" by simp
	have ldiviieql: "l div i * i = l" by (rule dvd_div_pos[OF lpos inz idvdl])
	with lpos have ldivinz: "0 \<noteq> l div i" by auto
	  
	then have ?case using prems
	  apply simp
	  apply (simp add: 
	    ac_dvd_eq[OF ldivinz, where m="d" and c="i" and n="a" and t="i'"] 
	    ldiviieql)
	  by (simp add: zmult_commute)
      }
      ultimately show ?case by blast

    next 
      case (3 i n i' n' r)
      from prems 
      have lininrp: "islinintterm (Add (Mult (Cst i') (Var n')) r)" 
	by simp
      then
      have "islint (Add (Mult (Cst i') (Var n')) (r))" 
	by (simp add: islinintterm_eq_islint)
      then have linr: "islintn(Suc n',r)"
	by (simp add: islinintterm_subt[OF lininrp] islinintterm_eq_islint islint_def)
      from lininrp have linr2: "islinintterm r"
	by (simp add: islinintterm_subt[OF lininrp])
      from prems have "n < n'" by simp
      then have nppos: "0 < n'" by simp
      from prems have inz: "i\<noteq>0" by simp
      
      have "n=0 \<or> (\<exists>m. (n = Suc m))" by arith
      moreover
      {
	assume "\<exists>m. n = Suc m"
	then have npos: "0 < n" by arith
	have ?case using nppos intterm_novar0[OF lininrp] prems
	  apply (auto simp add: linterm_novar0[OF linr, where x="a" and y="a*l"])
	  by (simp_all add: nth_pos2)
      }
      moreover 
      {
	assume nz: "n=0"
	from prems have idvdl: "i dvd l" by simp
	have ldiviieql: "l div i * i = l" by (rule dvd_div_pos[OF lpos inz idvdl])
	with lpos have ldivinz: "0 \<noteq> l div i" by auto
	  
	then have ?case using prems linr2 linr
	  apply (simp add: nth_pos2 lin_mul_corr linterm_novar0)
	  
	  apply (simp add: ac_dvd_eq[OF ldivinz, where m="d" and c="i" and n="a" and t="(i' * ats ! (n' - Suc 0) + I_intterm (a # ats) r)"] ldiviieql)
	  by (simp add: zmult_ac linterm_novar0[OF linr, where x="a" and y="a*l"])
      }
      ultimately show ?case by blast
      
    qed simp_all
next
  case (goal4 d t) show ?case
    using prems
    proof (induct t rule: islinintterm.induct)
      case (2 i n i') 
      have "n=0 \<or> (\<exists>m. (n = Suc m))" by arith
      moreover
      {
	assume "\<exists>m. n = Suc m"
	then have ?case using prems  by auto
      }
      moreover 
      {
	assume nz: "n=0"
	from prems have inz: "i\<noteq>0" by simp
	from prems have idvdl: "i dvd l" by simp
	have ldiviieql: "l div i * i = l" by (rule dvd_div_pos[OF lpos inz idvdl])
	with lpos have ldivinz: "0 \<noteq> l div i" by auto
	  
	then have ?case using prems
	  apply simp
	  apply (simp add: 
	    ac_dvd_eq[OF ldivinz, where m="d" and c="i" and n="a" and t="i'"] 
	    ldiviieql)
	  by (simp add: zmult_commute)
      }
      ultimately show ?case by blast

    next 
      case (3 i n i' n' r)
      from prems 
      have lininrp: "islinintterm (Add (Mult (Cst i') (Var n')) r)" 
	by simp
      then
      have "islint (Add (Mult (Cst i') (Var n')) (r))" 
	by (simp add: islinintterm_eq_islint)
      then have linr: "islintn(Suc n',r)"
	by (simp add: islinintterm_subt[OF lininrp] islinintterm_eq_islint islint_def)
      from lininrp have linr2: "islinintterm r"
	by (simp add: islinintterm_subt[OF lininrp])
      from prems have "n < n'" by simp
      then have nppos: "0 < n'" by simp
      from prems have inz: "i\<noteq>0" by simp
      
      have "n=0 \<or> (\<exists>m. (n = Suc m))" by arith
      moreover
      {
	assume "\<exists>m. n = Suc m"
	then have npos: "0 < n" by arith
	have ?case using nppos intterm_novar0[OF lininrp] prems
	  apply (auto simp add: linterm_novar0[OF linr, where x="a" and y="a*l"])
	  by (simp_all add: nth_pos2)
      }
      moreover 
      {
	assume nz: "n=0"
	from prems have idvdl: "i dvd l" by simp
	have ldiviieql: "l div i * i = l" by (rule dvd_div_pos[OF lpos inz idvdl])
	with lpos have ldivinz: "0 \<noteq> l div i" by auto
	  
	then have ?case using prems linr2 linr
	  apply (simp add: nth_pos2 lin_mul_corr linterm_novar0)
	  
	  apply (simp add: ac_dvd_eq[OF ldivinz, where m="d" and c="i" and n="a" and t="(i' * ats ! (n' - Suc 0) + I_intterm (a # ats) r)"] ldiviieql)
	  by (simp add: zmult_ac linterm_novar0[OF linr, where x="a" and y="a*l"])
      }
      ultimately show ?case by blast
      
    qed simp_all
next
    case (goal5 t c)
  from prems have cz: "c=0" by simp
    then have ?case
      using prems
    proof(induct t rule: islinintterm.induct)
      case (2 i n i') show ?case using prems
	proof-
	  from prems have inz: "i\<noteq>0" by simp
	  then 
	  have "n=0 \<or> n\<noteq>0" by arith
	  moreover 
	  {
	    assume "n\<noteq>0" then have ?thesis
	      using prems
	      by (cases n, simp_all)
	  }
	  moreover
	  {
	    assume nz: "n=0"
	    from prems nz have idvdl: "i dvd l" by simp
	    have "(i*a + i' = 0) = (l*a+ ((l div i)*i') = 0)" 
	      by (rule adjustcoeff_eq_corr[OF lpos inz idvdl])
	    then 
	    have ?thesis using prems by (simp add: mult_ac)
	  }
	  ultimately show ?thesis by blast
	qed
      next
	case (3 i n i' n' r) show ?case  using prems
	proof-
	  from prems 
	  have lininrp: "islinintterm (Add (Mult (Cst i') (Var n')) r)" 
	    by simp
	  then
	  have "islint (Add (Mult (Cst i') (Var n')) (r))" 
	    by (simp add: islinintterm_eq_islint)
	  then have linr: "islintn(Suc n',r)"
	    by (simp add: islinintterm_subt[OF lininrp] islinintterm_eq_islint islint_def)
	  from lininrp have linr2: "islinintterm r"
	    by (simp add: islinintterm_subt[OF lininrp])
	  from prems have "n < n'" by simp
	  then have nppos: "0 < n'" by simp
	  from prems have "i\<noteq>0" by simp
	  then 
	  have "n=0 \<or> n\<noteq>0" by arith
	  moreover 
	  {
	    assume nnz: "n\<noteq>0"
	    then have ?thesis using prems linr nppos nnz intterm_novar0[OF lininrp]
	      by (cases n, simp_all)
	    (simp add: nth_pos2 linterm_novar0[OF linr, where x="a" and y="a*l"])
	  }
	  moreover
	  {
	    assume nz: "n=0"
	    from prems have inz: "i \<noteq> 0" by auto
	    from prems nz have idvdl: "i dvd l" by simp
	    have "(i * a + (i' * (a # ats) ! n' + I_intterm (a # ats) r) = 0) =
	      (l * a + l div i * (i' * (a # ats) ! n' + I_intterm (a # ats) r) = 0)"
	      by (rule adjustcoeff_eq_corr[OF lpos inz idvdl])
	    then 
	    have ?thesis using prems linr linr2
	      by (simp add: mult_ac nth_pos2 lin_mul_corr 
		linterm_novar0[OF linr, where x="a" and y="a*l"])
	  }
	  ultimately show ?thesis by blast
	qed	  
    qed simp_all
    then show ?case by simp 
  
qed

(* unitycoeff preserves semantics *)
lemma unitycoeff_corr:
  assumes linp: "islinform p"
  shows "qinterp ats (QEx p) = qinterp ats (QEx (unitycoeff p))"
proof-
  
  have lpos: "0 < formlcm p" by (rule formlcm_pos[OF linp])
  have dvd : "divideallc (formlcm p, p)" by (rule formlcm_divideallc[OF linp])
  show ?thesis  using prems lpos dvd 
  proof (simp add: unitycoeff_def Let_def,case_tac "formlcm p = 1",
      simp_all add: adjustcoeff_corr)
    show "(\<exists>x. qinterp (x * formlcm p # ats) (adjustcoeff (formlcm p, p))) =
      (\<exists>x. formlcm p dvd x \<and>
      qinterp (x # ats) (adjustcoeff (formlcm p, p)))"
      (is "(\<exists>x. ?P(x* (formlcm p))) = (\<exists>x. formlcm p dvd x \<and> ?P x)")
    proof-
      have "(\<exists>x. ?P(x* (formlcm p))) = (\<exists>x. ?P((formlcm p)*x))"
	by (simp add: mult_commute)
      also have "(\<exists>x. ?P((formlcm p)*x)) = (\<exists>x. (formlcm p dvd x) \<and> ?P x)"
	by (simp add: unity_coeff_ex[where P="?P"])
      finally show ?thesis by simp
    qed
  qed
qed

(* the resul of adjustcoeff is unified for all l with divideallc (l,p) *)
lemma adjustcoeff_unified: 
  assumes linp: "islinform p"
  and dvdc: "divideallc(l,p)"
  and lpos: "l > 0"
  shows "isunified (adjustcoeff(l, p))"
  using linp dvdc lpos
  proof(induct l p rule: adjustcoeff.induct,simp_all add: lin_mul_lintn islinintterm_eq_islint islint_def)
    case (goal1 l d c r)
    from prems have "c >0 \<or> c < 0" by auto
    moreover {
      assume cpos: "c > 0 "
      from prems have lp: "l > 0" by simp
      from prems have cdvdl: "c dvd l" by simp
      have clel: "c \<le> l" by (rule zdvd_imp_le[OF cdvdl lp])
      have "c div c \<le>  l div c" by (rule zdiv_mono1[OF clel cpos])
      then have ?case using cpos by (simp add: zdiv_self)      
    }
    moreover {
      assume cneg: "c < 0"
      
     have mcpos: "-c > 0" by simp
      then have mcnz: "-c \<noteq> 0" by simp
      from prems have mcdvdl: "-c dvd l" 
	by simp 
      then have l1:"l mod -c = 0" by (simp add: zdvd_iff_zmod_eq_0)
      from prems have lp: "l >0" by simp
      have mclel: "-c \<le> l" by (rule zdvd_imp_le[OF mcdvdl lp])
      have "l div c = (-l div -c)"  by simp
      also have "\<dots> = - (l div -c)" using l1
	by (simp only: zdiv_zminus1_eq_if[OF mcnz, where a="l"]) simp
      finally have diveq: "l div c = - (l div -c)" by simp
      
      have "-c div -c \<le> l div -c" by (rule zdiv_mono1[OF mclel mcpos])
      then have "0 < l div -c" using cneg
	by (simp add: zdiv_self)
      then have ?case using diveq by simp
    }
    ultimately  show ?case by blast
  next
    case (goal2 l p)    from prems have "c >0 \<or> c < 0" by auto
    moreover {
      assume cpos: "c > 0 "
      from prems have lp: "l > 0" by simp
      from prems have cdvdl: "c dvd l" by simp
      have clel: "c \<le> l" by (rule zdvd_imp_le[OF cdvdl lp])
      have "c div c \<le>  l div c" by (rule zdiv_mono1[OF clel cpos])
      then have ?case using cpos by (simp add: zdiv_self)      
    }
    moreover {
      assume cneg: "c < 0"
      
     have mcpos: "-c > 0" by simp
      then have mcnz: "-c \<noteq> 0" by simp
      from prems have mcdvdl: "-c dvd l" 
	by simp 
      then have l1:"l mod -c = 0" by (simp add: zdvd_iff_zmod_eq_0)
      from prems have lp: "l >0" by simp
      have mclel: "-c \<le> l" by (rule zdvd_imp_le[OF mcdvdl lp])
      have "l div c = (-l div -c)"  by simp
      also have "\<dots> = - (l div -c)" using l1
	by (simp only: zdiv_zminus1_eq_if[OF mcnz, where a="l"]) simp
      finally have diveq: "l div c = - (l div -c)" by simp
      
      have "-c div -c \<le> l div -c" by (rule zdiv_mono1[OF mclel mcpos])
      then have "0 < l div -c" using cneg
	by (simp add: zdiv_self)
      then have ?case using diveq by simp
    }
    ultimately  show ?case by blast
  qed

lemma adjustcoeff_lcm_unified:
  assumes linp: "islinform p"
  shows "isunified (adjustcoeff(formlcm p, p))"
using linp adjustcoeff_unified formlcm_pos formlcm_divideallc
by simp

(* the result of unitycoeff is unified *)
lemma unitycoeff_unified:
  assumes linp: "islinform p"
  shows "isunified (unitycoeff p)"
using linp formlcm_pos[OF linp]
proof (auto simp add: unitycoeff_def Let_def adjustcoeff_lcm_unified)
  assume f1: "formlcm p = 1"
  have "isunified (adjustcoeff(formlcm p, p))" 
    by (rule adjustcoeff_lcm_unified[OF linp])
  with f1 
  show "isunified (adjustcoeff(1,p))" by simp
qed

lemma unified_isnnf: 
  assumes unifp: "isunified p"
  shows "isnnf p"
  using unified_islinform[OF unifp] linform_isnnf
  by simp

lemma unified_isqfree: "isunified p\<Longrightarrow> isqfree p"
using unified_islinform linform_isqfree
by auto

(* Plus/Minus infinity , B and A set definitions *)

consts minusinf :: "QF \<Rightarrow> QF"
       plusinf  :: "QF \<Rightarrow> QF"
       aset     :: "QF \<Rightarrow> intterm list"
       bset     :: "QF \<Rightarrow> intterm list"

recdef minusinf "measure size"
"minusinf (Le (Add (Mult (Cst c) (Var 0)) r) z) =
  (if c < 0 then F else T)"
"minusinf (Eq (Add (Mult (Cst c) (Var 0)) r) z) = F"
"minusinf (NOT(Eq (Add (Mult (Cst c) (Var 0)) r) z)) = T"
"minusinf (And p q) = And (minusinf p) (minusinf q)"
"minusinf (Or p q) = Or (minusinf p) (minusinf q)"
"minusinf p = p"

recdef plusinf "measure size"
"plusinf (Le (Add (Mult (Cst c) (Var 0)) r) z) =
  (if c < 0 then T else F)"
"plusinf (Eq (Add (Mult (Cst c) (Var 0)) r) z) = F"
"plusinf (NOT (Eq (Add (Mult (Cst c) (Var 0)) r) z)) = T"
"plusinf (And p q) = And (plusinf p) (plusinf q)"
"plusinf (Or p q) = Or (plusinf p) (plusinf q)"
"plusinf p = p"

recdef bset "measure size"
"bset (Le (Add (Mult (Cst c) (Var 0)) r) z) = 
 (if c < 0 then [lin_add(r,(Cst -1)), r]
         else [lin_add(lin_neg r,(Cst -1))])"
"bset (Eq (Add (Mult (Cst c) (Var 0)) r) z) =  
  (if c < 0 then [lin_add(r,(Cst -1))]
         else [lin_add(lin_neg r,(Cst -1))])"
"bset (NOT(Eq (Add (Mult (Cst c) (Var 0)) r) z)) =  
  (if c < 0 then [r]
         else [lin_neg r])"
"bset (And p q) = (bset p) @ (bset q)"
"bset (Or p q) = (bset p) @ (bset q)"
"bset p = []"

recdef aset "measure size"
"aset (Le (Add (Mult (Cst c) (Var 0)) r) z) = 
  (if c < 0 then [lin_add (r, Cst 1)]
         else [lin_add (lin_neg r, Cst 1), lin_neg r])"
"aset (Eq (Add (Mult (Cst c) (Var 0)) r) z) = 
  (if c < 0 then [lin_add(r,(Cst 1))]
       else [lin_add(lin_neg r,(Cst 1))])"
"aset (NOT(Eq (Add (Mult (Cst c) (Var 0)) r) z)) = 
  (if c < 0 then [r] 
      else [lin_neg r])"
"aset (And p q) = (aset p) @ (aset q)"
"aset (Or p q) = (aset p) @ (aset q)"
"aset p = []"

(* divlcm computes \<delta> = lcm d , where d | x +t occurs in p *)
consts divlcm :: "QF \<Rightarrow> int"
recdef divlcm "measure size"
"divlcm (Divides (Cst d) (Add (Mult (Cst c) (Var 0)) r)) = (abs d)"
"divlcm (NOT p) = divlcm p"
"divlcm (And p q)= ilcm (divlcm p) (divlcm q)"
"divlcm (Or p q) = ilcm (divlcm p) (divlcm q)"
"divlcm p = 1"

(* the preoperty of \<delta> *)
consts alldivide :: "int \<times> QF \<Rightarrow> bool"
recdef alldivide "measure (%(d,p). size p)"
"alldivide (d,(Divides (Cst d') (Add (Mult (Cst c) (Var 0)) r))) = 
  (d' dvd d)"
"alldivide (d,(NOT p)) = alldivide (d,p)"
"alldivide (d,(And p q)) = (alldivide (d,p) \<and> alldivide (d,q))"
"alldivide (d,(Or p q)) = ((alldivide (d,p)) \<and> (alldivide (d,q)))"
"alldivide (d,p) = True"

(* alldivide is monotone *)
lemma alldivide_mono: "\<And> d'. \<lbrakk> alldivide (d,p) ; d dvd d'\<rbrakk> \<Longrightarrow> alldivide (d',p)"
proof(induct d p rule: alldivide.induct, simp_all add: ilcm_dvd1 ilcm_dvd2)
  fix "d1" "d2" "d3"
  assume th1:"d2 dvd (d1::int)"
    and th2: "d1 dvd d3"
  show "d2 dvd d3" by (rule zdvd_trans[OF th1 th2])
qed

(* Some simple lemmas *)
lemma zdvd_eq_zdvd_abs: " (d::int) dvd d' = (d dvd (abs d')) "
proof-
  have "d' < 0 \<or> d' \<ge> 0" by arith
  moreover
  {
    assume dn': "d' < 0"
    then have "abs d' = - d'" by simp
    then 
    have ?thesis by (simp)
  }
  moreover 
  {
    assume dp': "d' \<ge> 0"
    then have "abs d' = d'" by simp
    then have ?thesis  by simp
  }
    ultimately show ?thesis by blast
qed

lemma zdvd_refl_abs: "(d::int) dvd (abs d)"
proof-
  have "d dvd d" by simp
  then show ?thesis by (simp add: iffD1 [OF zdvd_eq_zdvd_abs [where d = "d" and d'="d"]])
qed

(* \<delta> > 0*)
lemma divlcm_pos: 
  assumes 
  linp: "islinform p"
  shows "0 < divlcm p"
using linp
proof (induct p rule: divlcm.induct,simp_all add: ilcm_pos)
  case (goal1 f) show ?case 
    using prems 
    by (cases f, auto) (case_tac "intterm1", auto)
qed

lemma nz_le: "(x::int) > 0 \<Longrightarrow> x \<noteq> 0" by auto
(* divlcm is correct *)
lemma divlcm_corr:
  assumes 
  linp: "islinform p"
  shows "alldivide (divlcm p,p)"
  using linp divlcm_pos
proof (induct p rule: divlcm.induct,simp_all add: zdvd_refl_abs,clarsimp simp add: Nat.gr0_conv_Suc)
  case (goal1 f)
  have "islinform f" using prems  
    by (cases f, auto) (case_tac "intterm2", auto,case_tac "intterm1", auto)
  then have "alldivide (divlcm f, f)"  using prems by simp
  moreover have "divlcm (NOT f) = divlcm f" by simp
  moreover have "alldivide (x,f) = alldivide (x,NOT f)" by simp
  ultimately show ?case by simp
next
  case (goal2 f g)
  have dvd1: "(divlcm f) dvd (ilcm (divlcm f) (divlcm g))" 
    using prems by(simp add: ilcm_dvd1 nz_le)
  have dvd2: "(divlcm g) dvd (ilcm (divlcm f) (divlcm g))" 
    using prems by (simp add: ilcm_dvd2 nz_le)
  from dvd1 prems 
  have "alldivide (ilcm (divlcm f) (divlcm g), f)" 
    by (simp add: alldivide_mono[where d= "divlcm f" and p="f" and d' ="ilcm (divlcm f) (divlcm g)"])
  moreover   from dvd2 prems 
   have "alldivide (ilcm (divlcm f) (divlcm g), g)" 
    by (simp add: alldivide_mono[where d= "divlcm g" and p="g" and d' ="ilcm (divlcm f) (divlcm g)"])
  ultimately show ?case by simp
next
  case (goal3 f g)
  have dvd1: "(divlcm f) dvd (ilcm (divlcm f) (divlcm g))" 
    using prems by (simp add: nz_le ilcm_dvd1)
  have dvd2: "(divlcm g) dvd (ilcm (divlcm f) (divlcm g))" 
    using prems by (simp add: nz_le ilcm_dvd2)
  from dvd1 prems 
  have "alldivide (ilcm (divlcm f) (divlcm g), f)" 
    by (simp add: alldivide_mono[where d= "divlcm f" and p="f" and d' ="ilcm (divlcm f) (divlcm g)"])
  moreover   from dvd2 prems 
   have "alldivide (ilcm (divlcm f) (divlcm g), g)" 
    by (simp add: alldivide_mono[where d= "divlcm g" and p="g" and d' ="ilcm (divlcm f) (divlcm g)"])
  ultimately show ?case by simp
qed


(* Properties of  minusinf and plusinf*)

(* minusinf p and p are the same for minusinfity \<dots> *)
lemma minusinf_eq: 
  assumes unifp: "isunified p" 
  shows "\<exists> z. \<forall> x. x < z \<longrightarrow> (qinterp (x#ats) p = qinterp (x#ats) (minusinf p))"
using unifp unified_islinform[OF unifp]
proof (induct p rule: minusinf.induct)
  case (1 c r z)
  have "c <0 \<or> 0 \<le> c" by arith
  moreover 
  {
    assume cneg: " c < 0"
    from prems have z0: "z= Cst 0" 
      by (cases z,auto)
    with prems have lincnr: "islinintterm (Add (Mult (Cst c) (Var 0)) r)" 
      by simp

    from prems z0 have ?case 
      proof-
	show ?thesis
	  using prems z0
      apply auto
      apply (rule exI[where x="I_intterm (a # ats) r"])
      apply (rule allI)
      proof-
	fix x
	show "x < I_intterm (a # ats) r \<longrightarrow> \<not> - x + I_intterm (x # ats) r \<le> 0"
	  by (simp add: intterm_novar0[OF lincnr, where x="a" and y="x"])
      qed
    qed
  }
  moreover
  {
    assume cpos: "0 \<le> c"
    from prems have z0: "z= Cst 0" 
      by (cases z) auto
    with prems have lincnr: "islinintterm (Add (Mult (Cst c) (Var 0)) r)" 
      by simp
    
    from prems z0 have ?case
      proof-
	show ?thesis
	  using prems z0
      apply auto
      apply (rule exI[where x="-(I_intterm (a # ats) r)"])
      apply (rule allI)
      proof-
	fix x
	show "x < - I_intterm (a # ats) r \<longrightarrow> x + I_intterm (x # ats) r \<le> 0"
	  by (simp add: intterm_novar0[OF lincnr, where x="a" and y="x"])
      qed
    qed
  }
    
    ultimately show ?case by blast
next
  case (2 c r z)
  from prems have z0: "z= Cst 0" 
    by (cases z,auto)
  with prems have lincnr: "islinintterm (Add (Mult (Cst c) (Var 0)) r)" 
    by simp
  have "c <0 \<or> 0 \<le> c" by arith
  moreover 
  {
    assume cneg: " c < 0"
    from prems z0 have ?case 
      proof-
	show ?thesis
	  using prems z0
      apply auto
      apply (rule exI[where x="I_intterm (a # ats) r"])
      apply (rule allI)
      proof-
	fix x
	show "x < I_intterm (a # ats) r \<longrightarrow> \<not> - x + I_intterm (x # ats) r = 0"
	  by (simp add: intterm_novar0[OF lincnr, where x="a" and y="x"])
      qed
    qed
  }
  moreover
  {
    assume cpos: "0 \<le> c"
    from prems z0 have ?case
      proof-
	show ?thesis
	  using prems z0
      apply auto
      apply (rule exI[where x="-(I_intterm (a # ats) r)"])
      apply (rule allI)
      proof-
	fix x
	show "x < - I_intterm (a # ats) r \<longrightarrow> x + I_intterm (x # ats) r \<noteq> 0"
	  by (simp add: intterm_novar0[OF lincnr, where x="a" and y="x"])
      qed
    qed
  }
    
    ultimately show ?case by blast
next
  case (3 c r z)
  from prems have z0: "z= Cst 0" 
    by (cases z,auto)
  with prems have lincnr: "islinintterm (Add (Mult (Cst c) (Var 0)) r)" 
    by simp
  have "c <0 \<or> 0 \<le> c" by arith
  moreover 
  {
    assume cneg: " c < 0"
    from prems z0 have ?case 
      proof-
	show ?thesis
	  using prems z0
      apply auto
      apply (rule exI[where x="I_intterm (a # ats) r"])
      apply (rule allI)
      proof-
	fix x
	show "x < I_intterm (a # ats) r \<longrightarrow> \<not> - x + I_intterm (x # ats) r = 0"
	  by (simp add: intterm_novar0[OF lincnr, where x="a" and y="x"])
      qed
    qed
  }
  moreover
  {
    assume cpos: "0 \<le> c"
    from prems z0 have ?case
      proof-
	show ?thesis
	  using prems z0
      apply auto
      apply (rule exI[where x="-(I_intterm (a # ats) r)"])
      apply (rule allI)
      proof-
	fix x
	show "x < - I_intterm (a # ats) r \<longrightarrow> x + I_intterm (x # ats) r \<noteq> 0"
	  by (simp add: intterm_novar0[OF lincnr, where x="a" and y="x"])
      qed
    qed
  }
    
    ultimately show ?case by blast
next
  
  case (4 f g) 
  from prems obtain "zf" where 
    zf:"\<forall>x<zf. qinterp (x # ats) f = qinterp (x # ats) (minusinf f)" by auto
  from prems obtain "zg" where 
    zg:"\<forall>x<zg. qinterp (x # ats) g = qinterp (x # ats) (minusinf g)" by auto
  from zf zg show ?case 
    apply auto
    apply (rule exI[where x="min zf zg"])
    by simp
  
next case (5 f g)  
  from prems obtain "zf" where 
    zf:"\<forall>x<zf. qinterp (x # ats) f = qinterp (x # ats) (minusinf f)" by auto
  from prems obtain "zg" where 
    zg:"\<forall>x<zg. qinterp (x # ats) g = qinterp (x # ats) (minusinf g)" by auto
  from zf zg show ?case 
    apply auto
    apply (rule exI[where x="min zf zg"])
    by simp
  
qed simp_all

(* miusinf p behaves periodically*)
lemma minusinf_repeats: 
  assumes alldvd: "alldivide (d,p)"
  and unity: "isunified p"
  shows "qinterp (x#ats) (minusinf p) = qinterp ((x + c*d)#ats) (minusinf p)"
  using alldvd unity unified_islinform[OF unity]
proof(induct p rule: islinform.induct, simp_all)
  case (goal1 t a)
  show ?case
    using prems
    apply (cases t, simp_all add: nth_pos2)
    apply (case_tac "intterm1", simp_all)
    apply (case_tac "intterm1a",simp_all)
    by (case_tac "intterm2a",simp_all)
  (case_tac "nat",simp_all add: nth_pos2 intterm_novar0[where x="x" and y="x+c*d"])
next 
  case (goal2 t a)
  show ?case
    using prems
    apply (cases t, simp_all add: nth_pos2)
    apply (case_tac "intterm1", simp_all)
    apply (case_tac "intterm1a",simp_all)
    by (case_tac "intterm2a",simp_all)
  (case_tac "nat",simp_all add: nth_pos2 intterm_novar0[where x="x" and y="x+c*d"])
next 
  case (goal3 a t)
  show ?case using prems

  proof(induct t rule: islinintterm.induct, simp_all add: nth_pos2)
    case (goal1 i n i')
    show ?case
      using prems
    proof(cases n, simp_all, case_tac "i=1", simp,
	simp add: dvd_period[where a="a" and d="d" and x="x" and c="c"])
      case goal1
      from prems have "(abs i = 1) \<and> i \<noteq> 1" by auto 
      then  have im1: "i=-1" by arith
      then have "(a dvd i*x + i') = (a dvd x + (-i'))" 
	by (simp add: uminus_dvd_conv'[where d="a" and t="-x +i'"])
      moreover 
      from im1 have "(a dvd i*x + (i*(c * d)) + i') = (a dvd (x + c*d - i'))"
	apply simp
	apply (simp add: uminus_dvd_conv'[where d="a" and t="-x - c * d + i'"])
	by (simp add: zadd_ac)
      ultimately 
      have eq1:"((a dvd i*x + i') = (a dvd i*x + (i*(c * d)) + i')) = 
	((a dvd x + (-i'))  = (a dvd (x + c*d - i')))" by simp
      moreover 
      have dvd2: "(a dvd x + (-i')) = (a dvd x + c * d + (-i'))"
	by (rule dvd_period[where a="a" and d="d" and x="x" and c="c"], assumption)
      ultimately show ?case by simp
    qed
  next
    case (goal2 i n i' n' r)
    have "n = 0 \<or> 0 < n" by arith
    moreover 
    {
      assume npos: "0 < n"
      from prems have "n < n'" by simp then have "0 < n'" by simp
      moreover from prems
      have linr: "islinintterm (Add (Mult (Cst i') (Var n')) r)" by simp
      ultimately have ?case 
	using prems npos
	by (simp add: nth_pos2 intterm_novar0[OF linr,where x="x" and y="x + c*d"])
    }
    moreover 
    {
      assume n0: "n=0"
      from prems have lin2: "islinintterm (Add (Mult (Cst i') (Var n')) r)" by simp
      from prems have "n < n'" by simp then have npos': "0 < n'" by simp
      with prems have ?case
      proof(simp add: intterm_novar0[OF lin2, where x="x" and y="x+c*d"] 
	  nth_pos2 dvd_period,case_tac "i=1",
	  simp add: dvd_period[where a="a" and d="d" and x="x" and c="c"], simp)
	case goal1
	from prems have "abs i = 1 \<and> i\<noteq>1" by auto
	then have mi: "i = -1" by arith
	have "(a dvd -x + (i' * ats ! (n' - Suc 0) + I_intterm ((x + c * d) # ats) r)) = 
	  (a dvd x + (-i' * ats ! (n' - Suc 0) - I_intterm ((x + c * d) # ats) r))" 
	  by (simp add: 
	    uminus_dvd_conv'[where d="a" and 
	    t="-x + (i' * ats ! (n' - Suc 0) + I_intterm ((x + c * d) # ats) r)"])
	also 
	have "(a dvd x + (-i' * ats ! (n' - Suc 0) - I_intterm ((x + c * d) # ats) r)) = 
	  (a dvd x +c*d + (-i' * ats ! (n' - Suc 0) - I_intterm ((x + c * d) # ats) r))"
	  by (rule dvd_period[where a="a" and d="d" and x="x" and c="c"], assumption)
	also 
	have "(a dvd x +c*d + 
	  (-i' * ats ! (n' - Suc 0) - I_intterm ((x + c * d) # ats) r)) = 
	  (a dvd -(x +c*d + 
	  (-i' * ats ! (n' - Suc 0) - I_intterm ((x + c * d) # ats) r)))"
	  by (rule uminus_dvd_conv'[where d="a" and 
	    t="x +c*d + (-i' * ats ! (n' - Suc 0) - I_intterm ((x + c * d) # ats) r)"])
	also
	have "(a dvd -(x +c*d + 
	  (-i' * ats ! (n' - Suc 0) - I_intterm ((x + c * d) # ats) r)))
	  = (a dvd
          - x - c * d + (i' * ats ! (n' - Suc 0) + I_intterm ((x + c * d) # ats) r))" 
	  by (auto,simp_all add: zadd_ac)
	finally show ?case using mi by auto
      qed
    }
    ultimately show ?case by blast
  qed
next 
  case (goal4 a t)
  show ?case using prems 
  proof(induct t rule: islinintterm.induct, simp_all,case_tac "n=0",
      simp_all add: nth_pos2)
    case (goal1 i n i')
    show ?case
      using prems
    proof(case_tac "i=1", simp,
	simp add: dvd_period[where a="a" and d="d" and x="x" and c="c"])
      case goal1
      from prems have "abs i = 1 \<and> i\<noteq>1" by auto 
      then have im1: "i=-1" by arith
      then have "(a dvd i*x + i') = (a dvd x + (-i'))" 
	by (simp add: uminus_dvd_conv'[where d="a" and t="-x +i'"])
      moreover 
      from im1 have "(a dvd i*x + (i*(c * d)) + i') = (a dvd (x + c*d - i'))"
	apply simp
	apply (simp add: uminus_dvd_conv'[where d="a" and t="-x - c * d + i'"])
	by (simp add: zadd_ac)
      ultimately 
      have eq1:"((a dvd i*x + i') = (a dvd i*x + (i*(c * d)) + i')) = 
	((a dvd x + (-i'))  = (a dvd (x + c*d - i')))" by simp
      moreover 
      have dvd2: "(a dvd x + (-i')) = (a dvd x + c * d + (-i'))"
	by (rule dvd_period[where a="a" and d="d" and x="x" and c="c"], assumption)
      ultimately show ?thesis by simp
    qed
  next
    case (goal2 i n i' n' r)
    have "n = 0 \<or> 0 < n" by arith
    moreover 
    {
      assume npos: "0 < n"
      from prems have "n < n'" by simp then have "0 < n'" by simp
      moreover from prems
      have linr: "islinintterm (Add (Mult (Cst i') (Var n')) r)" by simp
      ultimately have ?case 
	using prems npos
	by (simp add: nth_pos2 intterm_novar0[OF linr,where x="x" and y="x + c*d"])
    }
    moreover 
    {
      assume n0: "n=0"
      from prems have lin2: "islinintterm (Add (Mult (Cst i') (Var n')) r)" by simp
      from prems have "n < n'" by simp then have npos': "0 < n'" by simp
      with prems have ?case
      proof(simp add: intterm_novar0[OF lin2, where x="x" and y="x+c*d"] 
	  nth_pos2 dvd_period,case_tac "i=1",
	  simp add: dvd_period[where a="a" and d="d" and x="x" and c="c"], simp)
	case goal1
	from prems have "abs i = 1 \<and> i\<noteq>1" by auto
	then have mi: "i = -1" by arith
	have "(a dvd -x + (i' * ats ! (n' - Suc 0) + I_intterm ((x + c * d) # ats) r)) = 
	  (a dvd x + (-i' * ats ! (n' - Suc 0) - I_intterm ((x + c * d) # ats) r))" 
	  by (simp add: 
	    uminus_dvd_conv'[where d="a" and 
	    t="-x + (i' * ats ! (n' - Suc 0) + I_intterm ((x + c * d) # ats) r)"])
	also 
	have "(a dvd x + (-i' * ats ! (n' - Suc 0) - I_intterm ((x + c * d) # ats) r)) = 
	  (a dvd x +c*d + (-i' * ats ! (n' - Suc 0) - I_intterm ((x + c * d) # ats) r))"
	  by (rule dvd_period[where a="a" and d="d" and x="x" and c="c"], assumption)
	also 
	have "(a dvd x +c*d + 
	  (-i' * ats ! (n' - Suc 0) - I_intterm ((x + c * d) # ats) r)) = 
	  (a dvd -(x +c*d + 
	  (-i' * ats ! (n' - Suc 0) - I_intterm ((x + c * d) # ats) r)))"
	  by (rule uminus_dvd_conv'[where d="a" and 
	    t="x +c*d + (-i' * ats ! (n' - Suc 0) - I_intterm ((x + c * d) # ats) r)"])
	also
	have "(a dvd -(x +c*d + 
	  (-i' * ats ! (n' - Suc 0) - I_intterm ((x + c * d) # ats) r)))
	  = (a dvd
          - x - c * d + (i' * ats ! (n' - Suc 0) + I_intterm ((x + c * d) # ats) r))" 
	  by (auto,simp_all add: zadd_ac)
	finally show ?case using mi by auto
      qed
    }
    ultimately show ?case by blast
  qed
next 
  case (goal5 t a)
  show ?case
    using prems
    apply (cases t, simp_all add: nth_pos2)
    apply (case_tac "intterm1", simp_all)
    apply (case_tac "intterm1a",simp_all)
    by (case_tac "intterm2a",simp_all)
  (case_tac "nat",simp_all add: nth_pos2 intterm_novar0[where x="x" and y="x+c*d"])
qed

lemma minusinf_repeats2:
  assumes alldvd: "alldivide (d,p)"
  and unity: "isunified p"
  shows "\<forall> x k. (qinterp (x#ats) (minusinf p) = qinterp ((x - k*d)#ats) (minusinf p))" 
  (is "\<forall> x k. ?P x = ?P (x - k*d)")
proof(rule allI, rule allI)
  fix x k
  show "?P x = ?P (x - k*d)"
  proof-
    have "?P x = ?P (x + (-k)*d)" by (rule minusinf_repeats[OF alldvd unity])
    then have "?P x = ?P (x - (k*d))" by simp
    then show ?thesis by blast 
  qed
qed


(* existence for minusinf p is existence for p *)
lemma minusinf_lemma:
  assumes unifp: "isunified p"
  and exminf: "\<exists> j \<in> {1 ..d}. qinterp (j#ats) (minusinf p)" (is "\<exists> j \<in> {1 .. d}. ?P1 j")
  shows "\<exists> x. qinterp (x#ats) p" (is "\<exists> x. ?P x")
proof-
  from exminf obtain "j" where P1j: "?P1 j" by blast
  have ePeqP1: "\<exists>z. \<forall> x. x < z \<longrightarrow> (?P x = ?P1 x)"
    by (rule minusinf_eq[OF unifp])
  then obtain "z" where P1eqP : "\<forall> x. x < z \<longrightarrow> (?P x = ?P1 x)" by blast
  let ?d = "divlcm p"
  have alldvd: "alldivide (?d,p)" using unified_islinform[OF unifp] divlcm_corr
    by auto
  have dpos: "0 < ?d" using unified_islinform[OF unifp] divlcm_pos
    by simp
  have P1eqP1 : "\<forall> x k. ?P1 x = ?P1 (x - k*(?d))"
    by (rule minusinf_repeats2[OF alldvd unifp])
  let ?w = "j - (abs (j-z) +1)* ?d"
  show "\<exists> x. ?P x"
  proof
    have w: "?w < z" 
      by (rule decr_lemma[OF dpos])
    
    have "?P1 j = ?P1 ?w" using P1eqP1 by blast
    also have "\<dots> = ?P ?w"  using w P1eqP by blast
    finally show "?P ?w" using P1j by blast
  qed
qed

(* limited search for the withness for minusinf p, due to peridicity *)
lemma minusinf_disj:
  assumes unifp: "isunified p"
  shows "(\<exists> x. qinterp (x#ats) (minusinf p)) = 
  (\<exists> j \<in> { 1.. divlcm p}. qinterp (j#ats) (minusinf p))" 
  (is "(\<exists> x. ?P x) = (\<exists> j \<in> { 1.. ?d}. ?P j)")
proof
  have linp: "islinform p" by (rule unified_islinform[OF unifp])
  have dpos: "0 < ?d" by (rule divlcm_pos[OF linp])
  have alldvd: "alldivide(?d,p)" by (rule divlcm_corr[OF linp])
  {
    assume "\<exists> j\<in> {1 .. ?d}. ?P j"
    then show "\<exists> x. ?P x" using dpos  by auto
  next
    assume "\<exists> x. ?P x"
    then obtain "x" where P: "?P x" by blast
    have modd: "\<forall>x k. ?P x = ?P (x - k*?d)"
      by (rule minusinf_repeats2[OF alldvd unifp])
    
    have "x mod ?d = x - (x div ?d)*?d"
      by(simp add:zmod_zdiv_equality mult_ac eq_diff_eq)
    hence Pmod: "?P x = ?P (x mod ?d)" using modd by simp
    show "\<exists> j\<in> {1 .. ?d}. ?P j"
    proof (cases)
      assume "x mod ?d = 0"
      hence "?P 0" using P Pmod by simp
      moreover have "?P 0 = ?P (0 - (-1)*?d)" using modd by blast
      ultimately have "?P ?d" by simp
      moreover have "?d \<in> {1 .. ?d}" using dpos 
	by (simp add:atLeastAtMost_iff)
      ultimately show "\<exists> j\<in> {1 .. ?d}. ?P j" ..
    next 
      assume not0: "x mod ?d \<noteq> 0"
      have "?P(x mod ?d)" using dpos P Pmod by(simp add:pos_mod_sign pos_mod_bound)
      moreover have "x mod ?d : {1 .. ?d}"
      proof -
	have "0 \<le> x mod ?d" by(rule pos_mod_sign[OF dpos])
	moreover have "x mod ?d < ?d"  by(rule pos_mod_bound[OF dpos])
	ultimately show ?thesis using not0 by(simp add:atLeastAtMost_iff)
      qed
      ultimately show "\<exists> j\<in> {1 .. ?d}. ?P j" ..
    qed
  }
qed

lemma minusinf_qfree:
  assumes linp : "islinform p"
  shows "isqfree (minusinf p)"
  using linp
 by (induct p rule: minusinf.induct) auto 

(* Properties of bset and a set *)

(* The elements of a bset are linear *) 
lemma bset_lin:
  assumes unifp: "isunified p"
  shows "\<forall> b \<in> set (bset p). islinintterm b"
using unifp unified_islinform[OF unifp]
proof (induct p rule: bset.induct, auto)
  case (goal1 c r z)
  from prems have "z = Cst 0" by (cases z, simp_all)
  then have lincnr: "islinintterm (Add (Mult (Cst c) (Var 0)) r)" using prems by simp
  have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
  have "islinintterm (Cst -1)" by simp
  then show ?case using linr lin_add_lin by simp
next 
  case (goal2 c r z)
  from prems have "z = Cst 0" by (cases z, simp_all)
  then have lincnr: "islinintterm (Add (Mult (Cst c) (Var 0)) r)" using prems by simp
  have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
  show ?case by (rule linr)
next
  case (goal3 c r z)
  from prems have "z = Cst 0" by (cases z, simp_all) 
  then have lincnr: "islinintterm (Add (Mult (Cst c) (Var 0)) r)" using prems by simp
  have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
  have "islinintterm (Cst -1)" by simp
  then show ?case using linr lin_add_lin lin_neg_lin by simp
next
  case (goal4 c r z)
  from prems have "z = Cst 0" by (cases z, simp_all) 
  then have lincnr: "islinintterm (Add (Mult (Cst c) (Var 0)) r)" using prems by simp
  have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
  have "islinintterm (Cst -1)" by simp
  then show ?case using linr lin_add_lin lin_neg_lin by simp
next
  case (goal5 c r z)
  from prems have "z = Cst 0" by (cases z, simp_all) 
  then have lincnr: "islinintterm (Add (Mult (Cst c) (Var 0)) r)" using prems by simp
  have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
  have "islinintterm (Cst -1)" by simp
  then show ?case using linr lin_add_lin lin_neg_lin by simp
next
  case (goal6 c r z)
  from prems have "z = Cst 0" by (cases z, simp_all) 
  then have lincnr: "islinintterm (Add (Mult (Cst c) (Var 0)) r)" using prems by simp
  have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
  have "islinintterm (Cst -1)" by simp
  then show ?case using linr lin_add_lin lin_neg_lin by simp
next
  case (goal7 c r z)
  from prems have "z = Cst 0" by (cases z, simp_all) 
  then have lincnr: "islinintterm (Add (Mult (Cst c) (Var 0)) r)" using prems by simp
  have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
  have "islinintterm (Cst -1)" by simp
  then show ?case using linr lin_add_lin lin_neg_lin by simp
qed

(* The third lemma in Norrisch's Paper *)
lemma bset_disj_repeat:
  assumes unifp: "isunified p"
  and alldvd: "alldivide (d,p)"
  and dpos: "0 < d"
  and nob: "(qinterp (x#ats) q) \<and> \<not>(\<exists>j\<in> {1 .. d}. \<exists> b \<in> set (bset p). (qinterp (((I_intterm (a#ats) b) + j)#ats) q)) \<and>(qinterp (x#ats) p)" 
  (is "?Q x \<and> \<not>(\<exists> j\<in> {1.. d}. \<exists> b\<in> ?B. ?Q (?I a b + j)) \<and> ?P x") 
    shows "?P (x -d)"  
  using unifp nob alldvd unified_islinform[OF unifp]
proof (induct p rule: islinform.induct,auto)
  case (goal1 t)
  from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])
    have "n=0 \<or> n>0" by arith
    moreover {assume "n>0" then have ?case 
	using prems
	by (simp add: nth_pos2 
	  intterm_novar0[OF lininr, where x="x" and y="x-d"]) }
    moreover 
    {assume nz: "n = 0"
      from prems have "abs i = 1" by auto 
      then have "i = -1 \<or> i =1" by arith
      moreover
      {
	assume i1: "i=1"
	have ?case  using dpos prems  
	  by (auto simp add: intterm_novar0[OF lininr, where x="x" and y="x - d"])
      }
      moreover 
      {
	assume im1: "i = -1"
	have ?case 
	  using prems 
	proof(auto simp add: intterm_novar0[OF lininr, where x="x - d" and y="x"], cases)
	  assume "- x + d +  ?I x r \<le> 0"
	  then show "- x + d + ?I x r \<le> 0" .
	next 
	  assume np: "\<not> - x + d +  ?I x r \<le> 0"
	  then have ltd:"x - ?I x r \<le> d - 1" by simp 
	  from prems have "-x + ?I x r \<le> 0" by simp
	  then have ge0: "x - ?I x r \<ge> 0" 
	    by simp
	  from ltd ge0 have "x - ?I x r = 0 \<or> (1 \<le> x - ?I x r \<and> x - ?I x r \<le> d - 1) " by arith
	  moreover
	  {
	    assume "x - ?I x r = 0"
	    then have xeqr: "x = ?I x r" by simp
	    from prems have "?Q x" by simp
	    with xeqr have qr:"?Q (?I x r)" by simp
	    from prems have lininr: "islinintterm (Add (Mult (Cst i) (Var 0)) r)" by simp
	    have "islinintterm r" by (rule islinintterm_subt[OF lininr])
	    from prems 
	    have "\<forall>j\<in>{1..d}. \<not> ?Q (?I a r + -1 + j)"
	      using linr by (auto simp add: lin_add_corr)
	    moreover from dpos have "1 \<in> {1..d}" by simp
	    ultimately have " \<not> ?Q (?I a r + -1 + 1)" by blast
	    with dpos linr have "\<not> ?Q (?I x r)"
	      by (simp add: intterm_novar0[OF lininr, where x="x" and y="a"] lin_add_corr)
	    with qr have "- x + d + ?I x r \<le> 0" by simp
	  }
	  moreover
	  {
	    assume gt0: "1 \<le> x - ?I x r \<and> x - ?I x r \<le> d - 1"
	    then have "\<exists> j\<in> {1 .. d - 1}. x - ?I x r =  j" by simp
	    then have "\<exists> j\<in> {1 .. d}. x - ?I x r =  j" by auto
	    then obtain  "j" where con: "1\<le>j \<and> j \<le> d  \<and> x - ?I x r = j" by auto
	    then have xeqr: "x = ?I x r + j" by auto
	    with prems have "?Q (?I x r + j)" by simp
	    with con have qrpj: "\<exists> j\<in> {1 .. d}. ?Q (?I x r + j)" by auto
	    from prems have "\<forall>j\<in>{1..d}. \<not> ?Q (?I a r + j)" by auto
	    then have "\<not> (\<exists> j\<in>{1..d}. ?Q (?I x r + j))" 
	      by (simp add: intterm_novar0[OF lininr, where x="x" and y="a"])
	    with qrpj prems have "- x + d + ?I x r \<le> 0" by simp 
	    
	  }
	  ultimately show "- x + d + ?I x r \<le> 0" by blast
	qed
      }
      ultimately have ?case by blast
    }
    ultimately have ?case by blast
  }
  ultimately show ?case by blast
next  
  case (goal3 a t)
  from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])
    have "n=0 \<or> n>0" by arith
    moreover {assume "n>0" then have ?case using prems 
	by (simp add: nth_pos2 
	  intterm_novar0[OF lininr, where x="x" and y="x-d"]) }
    moreover {
      assume nz: "n=0"
      from prems have "abs i = 1" by auto
      then have ipm: "i=1 \<or> i = -1" by arith
      from nz prems have advdixr: "a dvd (i * x) + I_intterm (x # ats) r" 
	by simp
      from prems have "a dvd d" by simp
      then have advdid: "a dvd i*d" using ipm by auto  
      have ?case
      using prems ipm 
      by (auto simp add: intterm_novar0[OF lininr, where x="x-d" and y="x"] dvd_period[OF advdid, where x="i*x" and c="-1"])
  }
  ultimately have ?case by blast
  } ultimately show ?case by blast
next

  case (goal4 a t)
  from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])

    have "n=0 \<or> n>0" by arith
    moreover {assume "n>0" then have ?case using prems 
	by (simp add: nth_pos2 
	  intterm_novar0[OF lininr, where x="x" and y="x-d"]) }
    moreover {
      assume nz: "n=0"
      from prems have "abs i = 1" by auto
      then have ipm: "i =1 \<or> i = -1" by arith
      from nz prems have advdixr: "\<not> (a dvd (i * x) + I_intterm (x # ats) r)" 
	by simp
      from prems have "a dvd d" by simp
      then have advdid: "a dvd i*d" using ipm by auto
      have ?case
      using prems ipm 
      by (auto simp add: intterm_novar0[OF lininr, where x="x-d" and y="x"] dvd_period[OF advdid, where x="i*x" and c="-1"])
  }
  ultimately have ?case by blast
  } ultimately show ?case by blast
next 
  case (goal2 t)
  from prems
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])
    have "n=0 \<or> n>0" by arith
    moreover {assume "n>0" then have ?case 
	using prems
	by (simp add: nth_pos2 
	  intterm_novar0[OF lininr, where x="x" and y="x-d"]) }
    moreover 
    {assume nz: "n = 0"
      from prems have "abs i = 1" by auto 
      then have "i = -1 \<or> i =1" by arith
      moreover
      {
	assume i1: "i=1"
	with prems have px: "x + ?I x r = 0" by simp
	then have "x = (- ?I x r - 1) + 1" by simp
	hence q1: "?Q ((- ?I x r - 1) + 1)" by simp
	from prems have "\<not> (?Q ((?I a (lin_add(lin_neg r, Cst -1))) + 1))"
	  by auto
	hence "\<not> (?Q ((- ?I a r - 1) + 1))" 
	  using lin_add_corr lin_neg_corr linr lin_neg_lin
	  by simp
	hence "\<not> (?Q ((- ?I x r - 1) + 1))" 
	  using intterm_novar0[OF lininr, where x="x" and y="a"]
	  by simp
	with q1 have  ?case by simp
      }
      moreover 
      {
	assume im1: "i = -1"
	with prems have px: "-x + ?I x r = 0" by simp
	then have "x = ?I x r" by simp
	hence q1: "?Q (?I x r)" by simp
	from prems have "\<not> (?Q ((?I a (lin_add(r, Cst -1))) + 1))"
	  by auto
	hence "\<not> (?Q (?I a r))" 
	  using lin_add_corr lin_neg_corr linr lin_neg_lin
	  by simp
	hence "\<not> (?Q (?I x r ))" 
	  using intterm_novar0[OF lininr, where x="x" and y="a"]
	  by simp
	with q1 have  ?case by simp
      }
      ultimately have ?case by blast
    }
    ultimately have ?case by blast
  }
  ultimately show ?case by blast
next
  case (goal5 t)
  from prems
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])
    have "n=0 \<or> n>0" by arith
    moreover {assume "n>0" then have ?case 
	using prems
	by (simp add: nth_pos2 
	  intterm_novar0[OF lininr, where x="x" and y="x-d"]) }
    moreover 
    {assume nz: "n = 0"
      from prems have "abs i = 1" by auto 
      then have "i = -1 \<or> i =1" by arith
      moreover
      {
	assume i1: "i=1"
	with prems have px: "x -d + ?I (x-d) r = 0" by simp
	hence "x = (- ?I x r) + d" 
	  using intterm_novar0[OF lininr, where x="x" and y="x-d"]
	  by simp
	hence q1: "?Q (- ?I x r + d)" by simp
	from prems have "\<not> (?Q ((?I a (lin_neg r)) + d))"
	  by auto
	hence "\<not> (?Q (- ?I a r + d))" 
	  using lin_neg_corr linr by simp
	hence "\<not> (?Q ((- ?I x r + d)))" 
	  using intterm_novar0[OF lininr, where x="x" and y="a"]
	  by simp
	with q1 have  ?case by simp
      }
      moreover 
      {
	assume im1: "i = -1"
	with prems have px: "- (x -d) + ?I (x - d) r = 0" by simp
	then have "x = ?I x r + d "
 	  using intterm_novar0[OF lininr, where x="x" and y="x-d"]
	  by simp
	hence q1: "?Q (?I x r + d)" by simp
	from prems have "\<not> (?Q ((?I a r) + d))"
	  by auto
	hence "\<not> (?Q (?I x r + d))" 
	  using intterm_novar0[OF lininr, where x="x" and y="a"]
	  by simp
	with q1 have  ?case by simp
      }
      ultimately have ?case by blast
    }
    ultimately have ?case by blast
  }
  ultimately show ?case by blast
  
qed
  
lemma bset_disj_repeat2:
  assumes unifp: "isunified p"

  shows "\<forall> x. \<not>(\<exists>j\<in> {1 .. (divlcm p)}. \<exists> b \<in> set (bset p). 
  (qinterp (((I_intterm (a#ats) b) + j)#ats) p))  
  \<longrightarrow> (qinterp (x#ats) p) \<longrightarrow> (qinterp ((x - (divlcm p))#ats) p)" 
  (is "\<forall> x. \<not>(\<exists> j\<in> {1 .. ?d}. \<exists> b\<in> ?B. ?P (?I a b + j)) \<longrightarrow> ?P x \<longrightarrow> ?P (x - ?d)")
proof
  fix x
  have linp: "islinform p" by (rule unified_islinform[OF unifp])
  have dpos: "?d > 0" by (rule divlcm_pos[OF linp])
  have alldvd: "alldivide(?d,p)" by (rule divlcm_corr[OF linp])
    show "\<not>(\<exists> j\<in> {1 .. ?d}. \<exists> b\<in> ?B. ?P (?I a b + j)) \<longrightarrow> ?P x \<longrightarrow> ?P (x - ?d)"
    using prems bset_disj_repeat[OF unifp alldvd dpos]
    by blast
qed

(* Cooper's theorem in the minusinfinity version *)
lemma cooper_mi_eq: 
  assumes unifp : "isunified p"
  shows "(\<exists> x. qinterp (x#ats) p) = 
  ((\<exists> j \<in> {1 .. (divlcm p)}. qinterp (j#ats) (minusinf p)) \<or> 
  (\<exists> j \<in> {1 .. (divlcm p)}. \<exists> b \<in> set (bset p). 
  qinterp (((I_intterm (a#ats) b) + j)#ats) p))"
  (is "(\<exists> x. ?P x) = ((\<exists> j\<in> {1 .. ?d}. ?MP j) \<or> (\<exists> j \<in> ?D. \<exists> b\<in> ?B. ?P (?I a b + j)))")
proof-
  have linp :"islinform p" by (rule unified_islinform[OF unifp])
  have dpos: "?d > 0" by (rule divlcm_pos[OF linp])
  have alldvd: "alldivide(?d,p)" by (rule divlcm_corr[OF linp])
  have eMPimpeP: "(\<exists>j \<in> ?D. ?MP j) \<longrightarrow> (\<exists>x. ?P x)"
    by (simp add: minusinf_lemma[OF unifp, where d="?d" and ats="ats"])
  have ePimpeP: "(\<exists> j \<in> ?D. \<exists> b\<in> ?B. ?P (?I a b + j)) \<longrightarrow> (\<exists> x. ?P x)"
    by blast
  have bst_rep: "\<forall> x. \<not> (\<exists> j \<in> ?D. \<exists> b \<in> ?B. ?P (?I a b + j)) \<longrightarrow> ?P x \<longrightarrow> ?P (x - ?d)"
    by (rule bset_disj_repeat2[OF unifp])
  have MPrep: "\<forall> x k. ?MP x = ?MP (x- k*?d)"
    by (rule minusinf_repeats2[OF alldvd unifp])
  have MPeqP: "\<exists> z. \<forall>  x < z. ?P x = ?MP x"
    by (rule minusinf_eq[OF unifp])
  let ?B'= "{?I a b| b. b\<in> ?B}"
  from bst_rep have bst_rep2: "\<forall>x. \<not> (\<exists>j\<in>?D. \<exists>b\<in> ?B'. ?P (b+j)) \<longrightarrow> ?P x \<longrightarrow> ?P (x - ?d)"
    by auto
  show ?thesis 
  using cpmi_eq[OF dpos MPeqP bst_rep2 MPrep]
  by auto
qed

(* A formalized analogy between aset, bset, plusinfinity and minusinfinity *)

consts mirror:: "QF \<Rightarrow> QF"
recdef mirror "measure size"
"mirror (Le (Add (Mult (Cst c) (Var 0)) r) z) =
  (Le (Add (Mult (Cst (- c)) (Var 0)) r) z)"
"mirror (Eq (Add (Mult (Cst c) (Var 0)) r) z) =
  (Eq (Add (Mult (Cst (- c)) (Var 0)) r) z)"
"mirror (Divides (Cst d) (Add (Mult (Cst c) (Var 0)) r)) = 
  (Divides (Cst d) (Add (Mult (Cst (- c)) (Var 0)) r))"
"mirror (NOT(Divides (Cst d) (Add (Mult (Cst c) (Var 0)) r))) = 
  (NOT(Divides (Cst d) (Add (Mult (Cst (- c)) (Var 0)) r)))"
"mirror (NOT(Eq (Add (Mult (Cst c) (Var 0)) r) z)) =
  (NOT(Eq (Add (Mult (Cst (- c)) (Var 0)) r) z))"
"mirror (And p q) = And (mirror p) (mirror q)"
"mirror (Or p q) = Or (mirror p) (mirror q)"
"mirror p = p"
(* mirror preserves unifiedness *)

lemma[simp]: "(abs (i::int) = 1) = (i =1 \<or> i = -1)"  by arith
lemma mirror_unified:
  assumes unif: "isunified p"
  shows "isunified (mirror p)"
  using unif
proof (induct p rule: mirror.induct, simp_all)
  case (goal1 c r z)
  from prems have zz: "z = Cst 0" by (cases z, simp_all) 
  then show ?case using prems 
    by (auto simp add: islinintterm_eq_islint islint_def)
next 
  case (goal2 c r z)
  from prems have zz: "z = Cst 0" by (cases z, simp_all) 
  then show ?case using prems 
    by (auto simp add: islinintterm_eq_islint islint_def)
next
  case (goal3 d c r) show ?case using prems by (auto simp add: islinintterm_eq_islint islint_def) 
next 
  case (goal4 d c r) show ?case using prems  by (auto simp add: islinintterm_eq_islint islint_def)
next 
 case (goal5 c r z)
  from prems have zz: "z = Cst 0" by (cases z, simp_all) 
  then show ?case using prems 
    by (auto simp add: islinintterm_eq_islint islint_def)
qed

(* relationship between plusinf and minusinf *)
lemma plusinf_eq_minusinf_mirror:
  assumes unifp: "isunified p"
  shows "(qinterp (x#ats) (plusinf p)) = (qinterp ((- x)#ats) (minusinf (mirror p)))"
using unifp unified_islinform[OF unifp]
proof (induct p rule: islinform.induct, simp_all)
  case (goal1 t z)
  from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])
    have ?case using prems 
      by (cases n, auto simp add: nth_pos2 
	  intterm_novar0[OF lininr, where x="x" and y="-x"] )}
  ultimately show ?case by blast
    
next
  case (goal2 t z)
  from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])
    have ?case using prems 
      by (cases n, auto simp add: nth_pos2 
	  intterm_novar0[OF lininr, where x="x" and y="-x"] )}
  ultimately show ?case by blast
next
  case (goal3 d t)
  
 from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])

    have ?case using prems 
      by (cases n, simp_all add: nth_pos2 
	  intterm_novar0[OF lininr, where x="x" and y="-x"] )}
  ultimately show ?case by blast
next

  case (goal4 d t)
  
 from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])

    have ?case using prems 
      by (cases n, simp_all add: nth_pos2 
	  intterm_novar0[OF lininr, where x="x" and y="-x"] )}
  ultimately show ?case by blast
next
  case (goal5 t z)
  from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])
    have ?case using prems 
      by (cases n, auto simp add: nth_pos2 
	  intterm_novar0[OF lininr, where x="x" and y="-x"] )}
  ultimately show ?case by blast
qed

(* relationship between aset abd bset *)
lemma aset_eq_bset_mirror: 
  assumes unifp: "isunified p"
  shows "set (aset p) = set (map lin_neg (bset (mirror p)))"
using unifp
proof(induct p rule: mirror.induct)
  case (1 c r z) 
  from prems have zz: "z = Cst 0"
    by (cases z, auto)
  from prems zz have lincnr: "islinintterm (Add (Mult (Cst c) (Var 0)) r)" by simp
  have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
  have neg1eqm1: "Cst 1 = lin_neg (Cst -1)" by (simp add: lin_neg_def)
  have negm1eq1: "Cst -1 = lin_neg (Cst 1)" by (simp add: lin_neg_def)
  show ?case  using prems linr zz apply (auto simp add: lin_neg_lin_add_distrib lin_neg_idemp neg1eqm1)
    by (simp add: negm1eq1 lin_neg_idemp sym[OF lin_neg_lin_add_distrib] lin_add_lin)
next
  case (2 c r z)   from prems have zz: "z = Cst 0"
    by (cases z, auto)
  from prems zz have lincnr: "islinintterm (Add (Mult (Cst c) (Var 0)) r)" by simp
  have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
  have neg1eqm1: "Cst 1 = lin_neg (Cst -1)" by (simp add: lin_neg_def)
  have negm1eq1: "Cst -1 = lin_neg (Cst 1)" by (simp add: lin_neg_def)
  show ?case  using prems linr zz
    by (auto simp add: lin_neg_lin_add_distrib lin_neg_idemp neg1eqm1)
  (simp add: negm1eq1 lin_neg_idemp sym[OF lin_neg_lin_add_distrib] lin_add_lin lin_neg_lin)

next
  case (5 c r z)  from prems have zz: "z = Cst 0"
    by (cases z, auto)
  from prems zz have lincnr: "islinintterm (Add (Mult (Cst c) (Var 0)) r)" by simp
  have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
  have neg1eqm1: "Cst 1 = lin_neg (Cst -1)" by (simp add: lin_neg_def)
  have negm1eq1: "Cst -1 = lin_neg (Cst 1)" by (simp add: lin_neg_def)
  show ?case  using prems linr zz
    by(auto simp add: lin_neg_lin_add_distrib lin_neg_idemp neg1eqm1)
  
qed simp_all

(* relationship between aset abd bset 2*)
lemma aset_eq_bset_mirror2: 
  assumes unifp: "isunified p"
  shows "aset p = map lin_neg (bset (mirror p))"
using unifp
proof(induct p rule: mirror.induct)
  case (1 c r z) 
  from prems have zz: "z = Cst 0"
    by (cases z, auto)
  from prems zz have lincnr: "islinintterm (Add (Mult (Cst c) (Var 0)) r)" by simp
  have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
  have neg1eqm1: "Cst 1 = lin_neg (Cst -1)" by (simp add: lin_neg_def)
  have negm1eq1: "Cst -1 = lin_neg (Cst 1)" by (simp add: lin_neg_def)
  show ?case  using prems linr zz
    apply (simp add: lin_neg_lin_add_distrib lin_neg_idemp neg1eqm1)
    apply (simp add: negm1eq1 lin_neg_idemp sym[OF lin_neg_lin_add_distrib] lin_add_lin)
    by arith
next
  case (2 c r z)   from prems have zz: "z = Cst 0"
    by (cases z, auto)
  from prems zz have lincnr: "islinintterm (Add (Mult (Cst c) (Var 0)) r)" by simp
  have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
  have neg1eqm1: "Cst 1 = lin_neg (Cst -1)" by (simp add: lin_neg_def)
  have negm1eq1: "Cst -1 = lin_neg (Cst 1)" by (simp add: lin_neg_def)
  show ?case  using prems linr zz
    by(auto simp add: lin_neg_lin_add_distrib lin_neg_idemp neg1eqm1)
    (simp add: negm1eq1 lin_neg_idemp sym[OF lin_neg_lin_add_distrib] lin_add_lin lin_neg_lin)

next
  case (5 c r z)  from prems have zz: "z = Cst 0"
    by (cases z, auto)
  from prems zz have lincnr: "islinintterm (Add (Mult (Cst c) (Var 0)) r)" by simp
  have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
  have neg1eqm1: "Cst 1 = lin_neg (Cst -1)" by (simp add: lin_neg_def)
  have negm1eq1: "Cst -1 = lin_neg (Cst 1)" by (simp add: lin_neg_def)
  show ?case  using prems linr zz
    by(auto simp add: lin_neg_lin_add_distrib lin_neg_idemp neg1eqm1)
  
qed simp_all

(* mirror preserves divlcm *)
lemma divlcm_mirror_eq:
  assumes unifp: "isunified p"
  shows "divlcm p = divlcm (mirror p)"
  using unifp
by (induct p rule: mirror.induct) auto

(* mirror almost preserves semantics *)  
lemma mirror_interp: 
  assumes unifp: "isunified p"
  shows "(qinterp (x#ats) p) = (qinterp ((- x)#ats) (mirror p))" (is "?P x = ?MP (-x)")
using unifp unified_islinform[OF unifp]
proof (induct p rule: islinform.induct)
  case (1 t z)
  from prems have zz: "z = 0" by simp
  from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])
    have ?case using prems zz
      by (cases n) (simp_all add: nth_pos2 
	intterm_novar0[OF lininr, where x="x" and y="-x"])
  }
  ultimately show ?case by blast
next
  case (2 t z)
  from prems have zz: "z = 0" by simp
  from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])
    have ?case using prems zz
      by (cases n) (simp_all add: nth_pos2 
	intterm_novar0[OF lininr, where x="x" and y="-x"])
  }
  ultimately show ?case by blast
next
  case (3 d t) 
  from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])
    have ?case
      using prems linr 
      by (cases n) (simp_all add: nth_pos2
	intterm_novar0[OF lininr, where x="x" and y="-x"])
  }
  ultimately show ?case by blast
next

  case (6 d t) 
  from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])
    have ?case
      using prems linr 
      by (cases n) (simp_all add: nth_pos2
	intterm_novar0[OF lininr, where x="x" and y="-x"])
  }
  ultimately show ?case by blast
next 
  case (7 t z)
  from prems have zz: "z = 0" by simp
  from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])
    have ?case using prems zz
      by (cases n) (simp_all add: nth_pos2 
	intterm_novar0[OF lininr, where x="x" and y="-x"])
  }
  ultimately show ?case by blast 
qed simp_all


lemma mirror_interp2: 
  assumes unifp: "islinform p"
  shows "(qinterp (x#ats) p) = (qinterp ((- x)#ats) (mirror p))" (is "?P x = ?MP (-x)")
using unifp 
proof (induct p rule: islinform.induct)
  case (1 t z)
  from prems have zz: "z = 0" by simp
  from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])
    have ?case using prems zz
      by (cases n) (simp_all add: nth_pos2 
	intterm_novar0[OF lininr, where x="x" and y="-x"])
  }
  ultimately show ?case by blast
next
  case (2 t z)
  from prems have zz: "z = 0" by simp
  from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])
    have ?case using prems zz
      by (cases n) (simp_all add: nth_pos2 
	intterm_novar0[OF lininr, where x="x" and y="-x"])
  }
  ultimately show ?case by blast
next
  case (3 d t) 
  from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])
    have ?case
      using prems linr 
      by (cases n) (simp_all add: nth_pos2
	intterm_novar0[OF lininr, where x="x" and y="-x"])
  }
  ultimately show ?case by blast
next

  case (6 d t) 
  from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])
    have ?case
      using prems linr 
      by (cases n) (simp_all add: nth_pos2
	intterm_novar0[OF lininr, where x="x" and y="-x"])
  }
  ultimately show ?case by blast
next 
  case (7 t z)
  from prems have zz: "z = 0" by simp
  from prems 
  have lint: "islinintterm t" by simp
  then have "(\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r) \<or> (\<exists> i. t = Cst i)"
    by (induct t rule: islinintterm.induct) auto
  moreover{ assume "\<exists> i. t = Cst i" then have ?case using prems by auto }
  moreover
  { assume "\<exists> i n r. t = Add (Mult (Cst i) (Var n) ) r"
    then obtain "i" "n" "r" where 
      inr_def: "t = Add (Mult (Cst i) (Var n) ) r" 
      by blast
    with lint have lininr: "islinintterm (Add (Mult (Cst i) (Var n) ) r)" 
      by simp
    have linr: "islinintterm r" 
      by (rule islinintterm_subt[OF lininr])
    have ?case using prems zz
      by (cases n) (simp_all add: nth_pos2 
	intterm_novar0[OF lininr, where x="x" and y="-x"])
  }
  ultimately show ?case by blast 
qed simp_all

(* mirror preserves existence *)
lemma mirror_ex: 
  assumes unifp: "isunified p"
  shows "(\<exists> x. (qinterp (x#ats) p)) = (\<exists> y. (qinterp (y#ats) (mirror p)))" 
  (is "(\<exists> x. ?P x) = (\<exists> y. ?MP y)")
proof
  assume "\<exists> x. ?P x"
  then obtain "x" where px:"?P x" by blast
  have "?MP (-x)" 
    using px
    by(simp add: mirror_interp[OF unifp, where x="x"])
  then show "\<exists> y. ?MP y" by blast
next 
  assume "\<exists> y. ?MP y"
  then obtain "y" where mpy: "?MP y" by blast
  have "?P (-y)"
    using mpy
    by (simp add: mirror_interp[OF unifp, where x="-y"])
  then show "\<exists> x. ?P x" by blast
qed

lemma mirror_ex2: 
  assumes unifp: "isunified p"
  shows "qinterp ats (QEx p) = qinterp ats (QEx (mirror p))"
using mirror_ex[OF unifp] by simp

  
(* Cooper's theorem in its plusinfinity version *)
lemma cooper_pi_eq:
  assumes unifp : "isunified p"
  shows "(\<exists> x. qinterp (x#ats) p) = 
  ((\<exists> j \<in> {1 .. (divlcm p)}. qinterp (-j#ats) (plusinf p)) \<or> 
  (\<exists> j \<in> {1 .. (divlcm p)}. \<exists> b \<in> set (aset p). 
  qinterp (((I_intterm (a#ats) b) - j)#ats) p))"
  (is "(\<exists> x. ?P x) = ((\<exists> j\<in> {1 .. ?d}. ?PP (-j)) \<or> (\<exists> j \<in> ?D. \<exists> b\<in> ?A. ?P (?I a b - j)))")
proof-
  have unifmp: "isunified (mirror p)" by (rule mirror_unified[OF unifp])
  have th1: 
    "(\<exists> j\<in> {1 .. ?d}. ?PP (-j)) = (\<exists> j\<in> {1..?d}.  qinterp (j # ats) (minusinf (mirror p)))"
    by (simp add: plusinf_eq_minusinf_mirror[OF unifp])
  have dth: "?d = divlcm (mirror p)"
    by (rule divlcm_mirror_eq[OF unifp])
  have "(\<exists> j \<in> ?D. \<exists> b\<in> ?A. ?P (?I a b - j)) = 
    (\<exists> j\<in> ?D. \<exists> b \<in> set (map lin_neg (bset (mirror p))). ?P (?I a b - j))"
    by (simp only: aset_eq_bset_mirror[OF unifp])
  also have "\<dots> = (\<exists> j\<in> ?D. \<exists> b \<in> set (bset (mirror p)). ?P (?I a (lin_neg b) - j))"
    by simp
  also have "\<dots> = (\<exists> j\<in> ?D. \<exists> b \<in> set (bset (mirror p)). ?P (-(?I a b + j)))"
  proof
    assume "\<exists>j\<in>{1..divlcm p}.
      \<exists>b\<in>set (bset (mirror p)). qinterp ((I_intterm (a # ats) (lin_neg b) - j) # ats) p"
    then
    obtain "j" and "b" where 
      pbmj: "j\<in> ?D \<and> b\<in> set (bset (mirror p)) \<and> ?P (?I a (lin_neg b) - j)" by blast
    then have linb: "islinintterm b" 
      by (auto simp add:bset_lin[OF unifmp])
    from linb pbmj have "?P (-(?I a b + j))" by (simp add: lin_neg_corr)
    then show "\<exists> j\<in> ?D. \<exists> b \<in> set (bset (mirror p)). ?P (-(?I a b + j))"
      using pbmj
      by auto
  next 
    assume "\<exists> j\<in> ?D. \<exists> b \<in> set (bset (mirror p)). ?P (-(?I a b + j))"
    then obtain "j" and "b" where 
      pbmj: "j\<in> ?D \<and> b\<in> set (bset (mirror p)) \<and> ?P (-(?I a b + j))"
      by blast
    then have linb: "islinintterm b" 
      by (auto simp add:bset_lin[OF unifmp])
    from linb pbmj have "?P (?I a (lin_neg b) - j)"  
      by (simp add: lin_neg_corr)
    then show "\<exists> j\<in> ?D. \<exists> b \<in> set (bset (mirror p)). ?P (?I a (lin_neg b) - j)"
      using pbmj by auto
  qed
  finally 
  have bth: "(\<exists> j\<in> ?D. \<exists> b\<in> ?A. ?P (?I a b - j)) =
    (\<exists>j\<in> ?D. \<exists> b\<in>set (bset (mirror p)). 
    qinterp ((I_intterm (a # ats) b + j) # ats) (mirror p))"
    by (simp add: mirror_interp[OF unifp] zadd_ac)
  from bth dth th1
  have "(\<exists> x. ?P x) = (\<exists> x. qinterp (x#ats) (mirror p))"
    by (simp add: mirror_ex[OF unifp])
  also have "\<dots> = ((\<exists>j\<in>{1..divlcm (mirror p)}. qinterp (j # ats) (minusinf (mirror p))) \<or>
    (\<exists>j\<in>{1..divlcm (mirror p)}.
    \<exists>b\<in>set (bset (mirror p)). qinterp ((I_intterm (a # ats) b + j) # ats) (mirror p)))"
    (is "(\<exists> x. ?MP x) = ((\<exists> j\<in> ?DM. ?MPM j) \<or> (\<exists> j \<in> ?DM. \<exists> b\<in> ?BM. ?MP (?I a b + j)))")
    by (rule cooper_mi_eq[OF unifmp])
  also 
  have "\<dots> = ((\<exists> j\<in> ?D. ?PP (-j)) \<or> (\<exists> j \<in> ?D. \<exists> b\<in> ?BM. ?MP (?I a b + j)))"
    using bth th1 dth by simp
  finally  show ?thesis using sym[OF bth] by simp
qed
   

(* substitution of a term into a Qfree formula, substitution of Bound 0 by i*)

consts subst_it:: "intterm \<Rightarrow> intterm \<Rightarrow> intterm"
primrec
"subst_it i (Cst b) = Cst b"
"subst_it i (Var n) = (if n = 0 then i else Var n)"
"subst_it i (Neg it) = Neg (subst_it i it)"
"subst_it i (Add it1 it2) = Add (subst_it i it1) (subst_it i it2)" 
"subst_it i (Sub it1 it2) = Sub (subst_it i it1) (subst_it i it2)"
"subst_it i (Mult it1 it2) = Mult (subst_it i it1) (subst_it i it2)"


(* subst_it preserves semantics *)
lemma subst_it_corr: 
"I_intterm (a#ats) (subst_it i t) = I_intterm ((I_intterm (a#ats) i)#ats) t"
by (induct t rule: subst_it.induct, simp_all add: nth_pos2)

consts subst_p:: "intterm \<Rightarrow> QF \<Rightarrow> QF"
primrec
"subst_p i (Le it1 it2) = Le (subst_it i it1) (subst_it i it2)"
"subst_p i (Lt it1 it2) = Lt (subst_it i it1) (subst_it i it2)"
"subst_p i (Ge it1 it2) = Ge (subst_it i it1) (subst_it i it2)"
"subst_p i (Gt it1 it2) = Gt (subst_it i it1) (subst_it i it2)"
"subst_p i (Eq it1 it2) = Eq (subst_it i it1) (subst_it i it2)"
"subst_p i (Divides d t) = Divides (subst_it i d) (subst_it i t)"
"subst_p i T = T"
"subst_p i F = F"
"subst_p i (And p q) = And (subst_p i p) (subst_p i q)"
"subst_p i (Or p q) = Or (subst_p i p) (subst_p i q)"
"subst_p i (Imp p q) = Imp (subst_p i p) (subst_p i q)"
"subst_p i (Equ p q) = Equ (subst_p i p) (subst_p i q)"
"subst_p i (NOT p) = (NOT (subst_p i p))"

(* subs_p preserves correctness *)
lemma subst_p_corr: 
  assumes qf: "isqfree p" 
  shows "qinterp (a # ats) (subst_p i p) = qinterp ((I_intterm (a#ats) i)#ats) p "
  using qf
by (induct p rule: subst_p.induct) (simp_all add: subst_it_corr)

(* novar0 p is true if the fomula doese not depend on the quantified variable*)
consts novar0I:: "intterm \<Rightarrow> bool"
primrec
"novar0I (Cst i) = True"
"novar0I (Var n) = (n > 0)"
"novar0I (Neg a) = (novar0I a)"
"novar0I (Add a b) = (novar0I a \<and> novar0I b)"
"novar0I (Sub a b) = (novar0I a \<and> novar0I b)"
"novar0I (Mult a b) = (novar0I a \<and> novar0I b)"

consts novar0:: "QF \<Rightarrow> bool"
recdef novar0 "measure size"
"novar0 (Lt a b) = (novar0I a \<and> novar0I b)"
"novar0 (Gt a b) = (novar0I a \<and> novar0I b)"
"novar0 (Le a b) = (novar0I a \<and> novar0I b)"
"novar0 (Ge a b) = (novar0I a \<and> novar0I b)"
"novar0 (Eq a b) = (novar0I a \<and> novar0I b)"
"novar0 (Divides a b) = (novar0I a \<and> novar0I b)"
"novar0 T = True" 
"novar0 F = True"
"novar0 (NOT p) = novar0 p" 
"novar0 (And p q) = (novar0 p \<and> novar0 q)"
"novar0 (Or p q)  = (novar0 p \<and> novar0 q)"
"novar0 (Imp p q) = (novar0 p \<and> novar0 q)"
"novar0 (Equ p q) = (novar0 p \<and> novar0 q)"
"novar0 p = False"

(* Interpretation of terms, that doese not depend on Var 0 *)
lemma I_intterm_novar0:
  assumes nov0: "novar0I x"
  shows "I_intterm (a#ats) x = I_intterm (b#ats) x"
using nov0
by (induct x) (auto simp add: nth_pos2)

(* substition is meaningless for term independent of Var 0*)
lemma subst_p_novar0_corr:
assumes qfp: "isqfree p"
  and nov0: "novar0I i"
  shows "qinterp (a#ats) (subst_p i p) = qinterp (I_intterm (b#ats) i#ats) p"
proof-
  have "qinterp (a#ats) (subst_p i p) = qinterp (I_intterm (a#ats) i#ats) p"
    by (rule subst_p_corr[OF qfp])
  moreover have "I_intterm (a#ats) i#ats = I_intterm (b#ats) i#ats"
    by (simp add: I_intterm_novar0[OF nov0, where a="a" and b="b"])
  ultimately show ?thesis by simp
qed

(* linearity and independence on Var 0*)
lemma lin_novar0: 
  assumes linx: "islinintterm x"
  and nov0: "novar0I x"
  shows "\<exists> n > 0. islintn(n,x)"
using linx nov0
by (induct x rule: islinintterm.induct) auto

lemma lintnpos_novar0:
 assumes  npos: "n > 0"
  and linx: "islintn(n,x)"
  shows "novar0I x"
using npos linx
by (induct n x rule: islintn.induct) auto

(* lin_add preserves independence on Var 0*)
lemma lin_add_novar0:
  assumes nov0a: "novar0I a"
  and nov0b : "novar0I b"
  and lina : "islinintterm a"
  and linb: "islinintterm b"
  shows "novar0I (lin_add (a,b))"
proof-
  have "\<exists> na > 0. islintn(na, a)" by (rule lin_novar0[OF lina nov0a]) 
  then obtain "na" where na: "na > 0 \<and> islintn(na,a)" by blast
  have "\<exists> nb > 0. islintn(nb, b)" by (rule lin_novar0[OF linb nov0b]) 
  then obtain "nb" where nb: "nb > 0 \<and> islintn(nb,b)" by blast
  from na have napos: "na > 0" by simp
  from na have linna: "islintn(na,a)" by simp
  from nb have nbpos: "nb > 0" by simp
  from nb have linnb: "islintn(nb,b)" by simp
  have "min na nb \<le> min na nb" by simp
  then have "islintn (min na nb, lin_add(a,b))" by (simp add: lin_add_lint[OF linna linnb])
  moreover have "min na nb > 0" using napos nbpos by (simp add: min_def)
  ultimately show ?thesis by (simp only: lintnpos_novar0)
qed

(* lin__mul preserves independence on Var 0*)
lemma lin_mul_novar0:
  assumes linx: "islinintterm x"
  and nov0: "novar0I x"
  shows "novar0I (lin_mul(i,x))"
  using linx nov0
proof (induct i x rule: lin_mul.induct, auto)
  case (goal1 c c' n r)
  from prems have lincnr: "islinintterm (Add (Mult (Cst c') (Var n)) r)" by simp
  have "islinintterm r" by (rule islinintterm_subt[OF lincnr])
  then show ?case using prems by simp
qed
    
(* lin_neg preserves indepenednce on Var 0*)
lemma lin_neg_novar0:
  assumes linx: "islinintterm x"
  and nov0: "novar0I x"
  shows "novar0I (lin_neg x)"
by (auto simp add: lin_mul_novar0 linx nov0 lin_neg_def)

(* subterms of linear terms are independent on Var 0*)
lemma intterm_subt_novar0:
  assumes lincnr: "islinintterm (Add (Mult (Cst c) (Var n)) r)"
  shows "novar0I r"
proof-
  have cnz: "c \<noteq> 0" by (rule islinintterm_cnz[OF lincnr])
  have "islintn(0,Add (Mult (Cst c) (Var n)) r)" using lincnr
    by (simp only: islinintterm_eq_islint islint_def)
  then have "islintn (n+1,r)" by auto
  moreover have "n+1 >0 " by arith
  ultimately show ?thesis 
    using lintnpos_novar0
    by auto
qed

(* decrease the De-Bruijn indices*)
consts decrvarsI:: "intterm \<Rightarrow> intterm"
primrec
"decrvarsI (Cst i) = (Cst i)"
"decrvarsI (Var n) = (Var (n - 1))"
"decrvarsI (Neg a) = (Neg (decrvarsI a))"
"decrvarsI (Add a b) = (Add (decrvarsI a) (decrvarsI b))"
"decrvarsI (Sub a b) = (Sub (decrvarsI a) (decrvarsI b))"
"decrvarsI (Mult a b) = (Mult (decrvarsI a) (decrvarsI b))"

(* One can decrease the indics for terms and formulae independent on Var 0*)
lemma intterm_decrvarsI:
  assumes nov0: "novar0I t"
  shows "I_intterm (a#ats) t = I_intterm ats (decrvarsI t)"
using nov0
by (induct t) (auto simp add: nth_pos2)

consts decrvars:: "QF \<Rightarrow> QF"
primrec
"decrvars (Lt a b) = (Lt (decrvarsI a) (decrvarsI b))"
"decrvars (Gt a b) = (Gt (decrvarsI a) (decrvarsI b))"
"decrvars (Le a b) = (Le (decrvarsI a) (decrvarsI b))"
"decrvars (Ge a b) = (Ge (decrvarsI a) (decrvarsI b))"
"decrvars (Eq a b) = (Eq (decrvarsI a) (decrvarsI b))"
"decrvars (Divides a b) = (Divides (decrvarsI a) (decrvarsI b))"
"decrvars T = T" 
"decrvars F = F"
"decrvars (NOT p) = (NOT (decrvars p))" 
"decrvars (And p q) = (And (decrvars p) (decrvars q))"
"decrvars (Or p q)  = (Or (decrvars p) (decrvars q))"
"decrvars (Imp p q) = (Imp (decrvars p) (decrvars q))"
"decrvars (Equ p q) = (Equ (decrvars p) (decrvars q))"

(* decrvars preserves quantifier freeness*)
lemma decrvars_qfree: "isqfree p \<Longrightarrow> isqfree (decrvars p)"
by (induct p rule: isqfree.induct, auto)

lemma novar0_qfree: "novar0 p \<Longrightarrow> isqfree p"
by (induct p) auto

lemma qinterp_novar0:
  assumes nov0: "novar0 p"
  shows "qinterp (a#ats) p = qinterp ats (decrvars p)"
using nov0
by(induct p) (simp_all add: intterm_decrvarsI)

(* All elements of bset p doese not depend on Var 0*)
lemma bset_novar0:
  assumes unifp: "isunified p"
  shows "\<forall> b\<in> set (bset p). novar0I b "
  using unifp
proof(induct p rule: bset.induct)
  case (1 c r z) 
  from prems have zz: "z = Cst 0" by (cases "z", auto) 
    from prems zz have lincnr: "islinintterm(Add (Mult (Cst c) (Var 0)) r)" by simp
    have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
    have novar0r: "novar0I r" by (rule intterm_subt_novar0[OF lincnr])
    from prems zz have "c = 1 \<or> c = -1" by auto
    moreover 
    {
      assume c1: "c=1"
      have lin1: "islinintterm (Cst 1)" by simp
      have novar01: "novar0I (Cst 1)" by simp
      then have ?case 
	using prems zz novar0r lin1 novar01
	by (auto simp add: lin_add_novar0 lin_neg_novar0 linr lin_neg_lin)
    }
    moreover 
    {
      assume c1: "c= -1"
      have lin1: "islinintterm (Cst -1)" by simp
      have novar01: "novar0I (Cst -1)" by simp
      then have ?case 
	using prems zz novar0r lin1 novar01
	by (auto simp add: lin_add_novar0 lin_neg_novar0 linr lin_neg_lin)
    }
    ultimately show ?case by blast
next 
  case (2 c r z) 
  from prems have zz: "z = Cst 0" by (cases "z", auto) 
    from prems zz have lincnr: "islinintterm(Add (Mult (Cst c) (Var 0)) r)" by simp
    have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
    have novar0r: "novar0I r" by (rule intterm_subt_novar0[OF lincnr])
    from prems zz have "c = 1 \<or> c = -1" by auto
    moreover 
    {
      assume c1: "c=1"
      have lin1: "islinintterm (Cst 1)" by simp
      have novar01: "novar0I (Cst 1)" by simp
      then have ?case 
	using prems zz novar0r lin1 novar01
	by (auto simp add: lin_add_novar0 lin_neg_novar0 linr lin_neg_lin)
    }
    moreover 
    {
      assume c1: "c= -1"
      have lin1: "islinintterm (Cst -1)" by simp
      have novar01: "novar0I (Cst -1)" by simp
      then have ?case 
	using prems zz novar0r lin1 novar01
	by (auto simp add: lin_add_novar0 lin_neg_novar0 linr lin_neg_lin)
    }
    ultimately show ?case by blast
next 
  case (3 c r z) 
  from prems have zz: "z = Cst 0" by (cases "z", auto) 
    from prems zz have lincnr: "islinintterm(Add (Mult (Cst c) (Var 0)) r)" by simp
    have linr: "islinintterm r" by (rule islinintterm_subt[OF lincnr])
    have novar0r: "novar0I r" by (rule intterm_subt_novar0[OF lincnr])
    from prems zz have "c = 1 \<or> c = -1" by auto
    moreover 
    {
      assume c1: "c=1"
      have lin1: "islinintterm (Cst 1)" by simp
      have novar01: "novar0I (Cst 1)" by simp
      then have ?case 
	using prems zz novar0r lin1 novar01
	by (auto simp add: lin_add_novar0 lin_neg_novar0 linr lin_neg_lin)
    }
    moreover 
    {
      assume c1: "c= -1"
      have lin1: "islinintterm (Cst -1)" by simp
      have novar01: "novar0I (Cst -1)" by simp
      then have ?case 
	using prems zz novar0r lin1 novar01
	by (auto simp add: lin_add_novar0 lin_neg_novar0 linr lin_neg_lin)
    }
    ultimately show ?case by blast
qed auto

(* substitution preserves independence on Var 0*)
lemma subst_it_novar0:
  assumes nov0x: "novar0I x"
  shows "novar0I (subst_it x t)"
  using nov0x
  by (induct t) auto

lemma subst_p_novar0:
  assumes nov0x:"novar0I x"
  and qfp: "isqfree p"
  shows "novar0 (subst_p x p)"
  using nov0x qfp
  by (induct p rule: novar0.induct) (simp_all add: subst_it_novar0)

(* linearize preserves independence on Var 0 *)
lemma linearize_novar0: 
  assumes nov0t: "novar0I t "
  shows "\<And> t'. linearize t = Some t' \<Longrightarrow> novar0I t'"
using nov0t
proof(induct t rule: novar0I.induct)
  case (Neg a)
  let ?la = "linearize a"
  from prems have "\<exists> a'. ?la = Some a'" by (cases ?la, auto)
  then obtain "a'" where "?la = Some a'" by blast
  with prems have nv0a':"novar0I a'" by simp
  have "islinintterm a'" using prems by (simp add: linearize_linear)
  with nv0a' have "novar0I (lin_neg a')" 
    by (simp add: lin_neg_novar0)
  then 
  show ?case using prems by simp 
next 
  case (Add a b) 
  let ?la = "linearize a"
  let ?lb = "linearize b"
  from prems have linab: "linearize (Add a b) = Some t'" by simp
  then have "\<exists> a'. ?la = Some a'" by (cases ?la) auto
  then obtain "a'" where "?la = Some a'" by blast
  with prems have nv0a':"novar0I a'" by simp
  have lina': "islinintterm a'" using prems by (simp add: linearize_linear)
  from linab have "\<exists> b'. ?lb = Some b'"
    by (cases ?la, auto simp add: measure_def inv_image_def) (cases ?lb, auto)
  then obtain "b'" where "?lb = Some b'" by blast
  with prems have nv0b':"novar0I b'" by simp
  have linb': "islinintterm b'" using prems by (simp add: linearize_linear)
  then show ?case using prems lina' linb' nv0a' nv0b'
    by (auto simp add: measure_def inv_image_def lin_add_novar0)
next 
  case (Sub a b)
    let ?la = "linearize a"
  let ?lb = "linearize b"
  from prems have linab: "linearize (Sub a b) = Some t'" by simp
  then have "\<exists> a'. ?la = Some a'" by (cases ?la) auto
  then obtain "a'" where "?la = Some a'" by blast
  with prems have nv0a':"novar0I a'" by simp
  have lina': "islinintterm a'" using prems by (simp add: linearize_linear)
  from linab have "\<exists> b'. ?lb = Some b'"
    by (cases ?la, auto simp add: measure_def inv_image_def) (cases ?lb, auto)
  then obtain "b'" where "?lb = Some b'" by blast
  with prems have nv0b':"novar0I b'" by simp
  have linb': "islinintterm b'" using prems by (simp add: linearize_linear)
  then show ?case using prems lina' linb' nv0a' nv0b'
    by (auto simp add: 
      measure_def inv_image_def lin_add_novar0 lin_neg_novar0 lin_neg_lin)
next 
  case (Mult a b)     
  let ?la = "linearize a"
  let ?lb = "linearize b"
  from prems have linab: "linearize (Mult a b) = Some t'" by simp
  then have "\<exists> a'. ?la = Some a'"
    by (cases ?la, auto simp add: measure_def inv_image_def)
  then obtain "a'" where "?la = Some a'" by blast
  with prems have nv0a':"novar0I a'" by simp
  have lina': "islinintterm a'" using prems by (simp add: linearize_linear)
  from prems linab have "\<exists> b'. ?lb = Some b'"
    apply (cases ?la, auto simp add: measure_def inv_image_def) 
    by (cases "a'",auto simp add: measure_def inv_image_def) (cases ?lb, auto)+
  then obtain "b'" where "?lb = Some b'" by blast
  with prems have nv0b':"novar0I b'" by simp
  have linb': "islinintterm b'" using prems by (simp add: linearize_linear)
  then show ?case using prems lina' linb' nv0a' nv0b' 
    by (cases "a'",auto simp add: measure_def inv_image_def lin_mul_novar0)
  (cases "b'",auto simp add: measure_def inv_image_def lin_mul_novar0)
qed auto


(* simplification of formulae *)
consts psimpl :: "QF \<Rightarrow> QF"
recdef psimpl "measure size"
"psimpl (Le l r) = 
  (case (linearize (Sub l r)) of
   None \<Rightarrow> Le l r
 | Some x \<Rightarrow> (case x of 
       Cst i \<Rightarrow> (if i \<le> 0 then T else F)
     | _ \<Rightarrow> (Le x (Cst 0))))"
"psimpl (Eq l r) = 
  (case (linearize (Sub l r)) of
   None \<Rightarrow> Eq l r
 | Some x \<Rightarrow> (case x of 
       Cst i \<Rightarrow> (if i = 0 then T else F)
     | _ \<Rightarrow> (Eq x (Cst 0))))"

"psimpl (Divides (Cst d) t) = 
  (case (linearize t) of
  None \<Rightarrow> (Divides (Cst d) t)
  | Some c \<Rightarrow> (case c of
     Cst i \<Rightarrow> (if d dvd i then T else F)
   | _ \<Rightarrow>  (Divides (Cst d) c)))"

"psimpl (And p q) = 
  (let p'= psimpl p
  in (case p' of 
       F \<Rightarrow> F
      |T \<Rightarrow> psimpl q
      | _ \<Rightarrow> let q' = psimpl q
             in (case q' of
                     F \<Rightarrow> F
                   | T \<Rightarrow> p'
                   | _ \<Rightarrow> (And p' q'))))"

"psimpl (Or p q) = 
  (let p'= psimpl p
  in (case p' of 
        T \<Rightarrow> T
      | F \<Rightarrow> psimpl q
      | _ \<Rightarrow> let q' = psimpl q
             in (case q' of
                     T \<Rightarrow> T
                   | F \<Rightarrow> p'
                   | _ \<Rightarrow> (Or p' q'))))"

"psimpl (Imp p q) = 
  (let p'= psimpl p
  in (case p' of 
       F \<Rightarrow> T
      |T \<Rightarrow> psimpl q
      | NOT p1 \<Rightarrow> let q' = psimpl q
             in (case q' of
                     F \<Rightarrow> p1
                   | T \<Rightarrow> T
                   | _ \<Rightarrow> (Or p1 q'))
      | _ \<Rightarrow> let q' = psimpl q
             in (case q' of
                     F \<Rightarrow> NOT p'
                   | T \<Rightarrow> T
                   | _ \<Rightarrow> (Imp p' q'))))"

"psimpl (Equ p q) = 
  (let p'= psimpl p ; q' = psimpl q
  in (case p' of 
        T \<Rightarrow> q'
      | F \<Rightarrow> (case q' of
                  T \<Rightarrow> F
                | F \<Rightarrow> T
                | NOT q1 \<Rightarrow> q1
                | _ \<Rightarrow> NOT q')
      | NOT p1 \<Rightarrow>  (case q' of
                  T \<Rightarrow> p'
                | F \<Rightarrow> p1
                | NOT q1 \<Rightarrow> (Equ p1 q1)
                | _ \<Rightarrow> (Equ p' q'))
      | _ \<Rightarrow> (case q' of
                  T \<Rightarrow> p'
                | F \<Rightarrow> NOT p'
                | _ \<Rightarrow> (Equ p' q'))))"

"psimpl (NOT p) = 
  (let p' = psimpl p
  in ( case p' of 
       F \<Rightarrow> T
     | T \<Rightarrow> F
     | NOT p1 \<Rightarrow> p1 
     | _ \<Rightarrow> (NOT p')))"
"psimpl p = p"

(* psimpl preserves semantics *)
lemma psimpl_corr: "qinterp ats p = qinterp ats (psimpl p)"
proof(induct p rule: psimpl.induct)
  case (1 l r)
  have "(\<exists> lx. linearize (Sub l r) = Some lx) \<or> (linearize (Sub l r) = None)" by auto
  moreover
  {
    assume lin: "\<exists> lx. linearize (Sub l r) = Some lx"
    from lin obtain "lx" where lx: "linearize (Sub l r) = Some lx" by blast
    from lx have "I_intterm ats (Sub l r) = I_intterm ats lx"
      by (rule linearize_corr[where t="Sub l r" and t'= "lx"])
    then have feq: "qinterp ats (Le l r) = qinterp ats (Le lx (Cst 0))" by (simp , arith)
    from lx have lxlin: "islinintterm lx" by (rule linearize_linear)
    from lxlin feq have ?case 
      proof-
	have "(\<exists> i. lx = Cst i) \<or> (\<not> (\<exists> i. lx = Cst i))" by blast
	moreover
	{
	  assume lxcst: "\<exists> i. lx = Cst i"
	  from lxcst obtain "i" where lxi: "lx = Cst i" by blast
	  with feq have "qinterp ats (Le l r) = (i \<le> 0)" by simp
	  then have ?case using prems by (simp add: measure_def inv_image_def)
	}
	moreover 
	{
	  assume "(\<not> (\<exists> i. lx = Cst i))"
	  then have "(case lx of 
	    Cst i \<Rightarrow> (if i \<le> 0 then T else F)
	    | _ \<Rightarrow> (Le lx (Cst 0))) = (Le lx (Cst 0))" 
	    by (case_tac "lx::intterm", auto)
	  with prems lxlin feq have ?case by (auto simp add: measure_def inv_image_def)
	}
	ultimately show ?thesis  by blast
      qed
  }
  moreover
  {
    assume "linearize (Sub l r) = None"
    then have ?case using prems by simp
  }
  ultimately show ?case by blast
  
next 
  case (2 l r)
  have "(\<exists> lx. linearize (Sub l r) = Some lx) \<or> (linearize (Sub l r) = None)" by auto
  moreover
  {
    assume lin: "\<exists> lx. linearize (Sub l r) = Some lx"
    from lin obtain "lx" where lx: "linearize (Sub l r) = Some lx" by blast
    from lx have "I_intterm ats (Sub l r) = I_intterm ats lx"
      by (rule linearize_corr[where t="Sub l r" and t'= "lx"])
    then have feq: "qinterp ats (Eq l r) = qinterp ats (Eq lx (Cst 0))" by (simp , arith)
    from lx have lxlin: "islinintterm lx" by (rule linearize_linear)
    from lxlin feq have ?case 
      proof-
	have "(\<exists> i. lx = Cst i) \<or> (\<not> (\<exists> i. lx = Cst i))" by blast
	moreover
	{
	  assume lxcst: "\<exists> i. lx = Cst i"
	  from lxcst obtain "i" where lxi: "lx = Cst i" by blast
	  with feq have "qinterp ats (Eq l r) = (i = 0)" by simp
	  then have ?case using prems by (simp add: measure_def inv_image_def)
	}
	moreover 
	{
	  assume "(\<not> (\<exists> i. lx = Cst i))"
	  then have "(case lx of 
	    Cst i \<Rightarrow> (if i = 0 then T else F)
	    | _ \<Rightarrow> (Eq lx (Cst 0))) = (Eq lx (Cst 0))" 
	    by (case_tac "lx::intterm", auto)
	  with prems lxlin feq have ?case by (auto simp add: measure_def inv_image_def)
	}
	ultimately show ?thesis  by blast
      qed
  }
  moreover
  {
    assume "linearize (Sub l r) = None"
    then have ?case using prems by simp
  }
  ultimately show ?case by blast
  
next 
    
  case (3 d t)  
  have "(\<exists> lt. linearize t = Some lt) \<or> (linearize t = None)" by auto
  moreover
  {
    assume lin: "\<exists> lt. linearize t  = Some lt"
    from lin obtain "lt" where lt: "linearize t = Some lt" by blast
    from lt have "I_intterm ats t = I_intterm ats lt"
      by (rule linearize_corr[where t="t" and t'= "lt"])
    then have feq: "qinterp ats (Divides (Cst d) t) = qinterp ats (Divides (Cst d) lt)" by (simp)
    from lt have ltlin: "islinintterm lt" by (rule linearize_linear)
    from ltlin feq have ?case using prems  apply simp by (case_tac "lt::intterm", simp_all)
  }
  moreover
  {
    assume "linearize t = None"
    then have ?case using prems by simp
  }
  ultimately show ?case by blast
  
next 
  case (4 f g)

    let ?sf = "psimpl f"
  let ?sg = "psimpl g"
  show ?case using prems 
    by (cases ?sf, simp_all add: Let_def measure_def inv_image_def) 
  (cases ?sg, simp_all)+
next
  case (5 f g)
      let ?sf = "psimpl f"
  let ?sg = "psimpl g"
  show ?case using prems
    apply (cases ?sf, simp_all add: Let_def measure_def inv_image_def) 
    apply (cases ?sg, simp_all)
    apply (cases ?sg, simp_all)
    apply (cases ?sg, simp_all)
    apply (cases ?sg, simp_all)
    apply (cases ?sg, simp_all)
    apply (cases ?sg, simp_all)
    apply (cases ?sg, simp_all)
    apply blast
    apply (cases ?sg, simp_all)
    apply (cases ?sg, simp_all)
     apply (cases ?sg, simp_all)
   apply blast
    apply (cases ?sg, simp_all)
    by (cases ?sg, simp_all) (cases ?sg, simp_all)
next
  case (6 f g)
  let ?sf = "psimpl f"
  let ?sg = "psimpl g"
  show ?case using prems 
    apply(simp add: Let_def measure_def inv_image_def)
    apply(cases ?sf,simp_all)
    apply (simp_all add: Let_def measure_def inv_image_def)
    apply(cases ?sg, simp_all)
    apply(cases ?sg, simp_all)
    apply(cases ?sg, simp_all)
    apply(cases ?sg, simp_all)
    apply(cases ?sg, simp_all)
    apply(cases ?sg, simp_all)
    apply(cases ?sg, simp_all)
    apply blast
    apply blast
    apply blast
    apply blast
    apply blast
    apply blast
    apply blast
    apply blast
    apply blast
    apply blast
    apply blast
    apply blast
    apply blast
    apply(cases ?sg, simp_all)
    apply(cases ?sg, simp_all)
    apply(cases ?sg, simp_all)
    apply(cases ?sg, simp_all)
    apply(cases ?sg, simp_all)
    apply(cases ?sg, simp_all)
    done
next
  case (7 f g)
  let ?sf = "psimpl f"
  let ?sg = "psimpl g"
  show ?case 
    using prems
    by (cases ?sf, simp_all add: Let_def) (cases ?sg, simp_all)+
next
  case (8 f) show ?case 
    using prems
    apply (simp add: Let_def)
    by (case_tac "psimpl f", simp_all)
qed simp_all

(* psimpl preserves independence on Var 0*)
lemma psimpl_novar0:
  assumes nov0p: "novar0 p"
  shows "novar0 (psimpl p)"
  using nov0p
proof (induct p rule: psimpl.induct)
  case (1 l r)
  let ?ls = "linearize (Sub l r)"
  have "?ls = None \<or> (\<exists> x. ?ls = Some x)" by auto
  moreover
  {
    assume "?ls = None" then have ?case 
      using prems by (simp add: measure_def inv_image_def)
  }
  moreover {
    assume "\<exists> x. ?ls = Some x"
    then obtain "x" where ls_d: "?ls = Some x" by blast
    from prems have "novar0I l" by simp
    moreover from prems have "novar0I r" by simp
    ultimately have nv0s: "novar0I (Sub l r)" by simp
    from prems have "novar0I x" 
      by (simp add: linearize_novar0[OF nv0s, where t'="x"])
    then have ?case
      using prems
      by (cases "x") (auto simp add: measure_def inv_image_def)
  }
  ultimately show ?case by blast
next
  case (2 l r)
  let ?ls = "linearize (Sub l r)"
  have "?ls = None \<or> (\<exists> x. ?ls = Some x)" by auto
  moreover
  {
    assume "?ls = None" then have ?case 
      using prems by (simp add: measure_def inv_image_def)
  }
  moreover {
    assume "\<exists> x. ?ls = Some x"
    then obtain "x" where ls_d: "?ls = Some x" by blast
    from prems have "novar0I l" by simp
    moreover from prems have "novar0I r" by simp
    ultimately have nv0s: "novar0I (Sub l r)" by simp
    from prems have "novar0I x" 
      by (simp add: linearize_novar0[OF nv0s, where t'="x"])
    then have ?case
      using prems
      by (cases "x") (auto simp add: measure_def inv_image_def)
  }
  ultimately show ?case by blast
next
  case (3 d t)
  let ?lt = "linearize t"
  have "?lt = None \<or> (\<exists> x. ?lt = Some x)"  by auto
  moreover 
  { assume "?lt = None" then have ?case using prems by simp }
  moreover {
    assume "\<exists>x. ?lt = Some x"
    then obtain "x" where x_d: "?lt = Some x" by blast
    from prems have nv0t: "novar0I t" by simp
    with x_d have "novar0I x" 
      by (simp add: linearize_novar0[OF nv0t])
    with prems have ?case 
      by (cases "x") simp_all
  }
  ultimately show ?case by blast
next
  case (4 f g)
  let ?sf = "psimpl f"
  let ?sg = "psimpl g"
  show ?case 
    using prems 
    by (cases ?sf, simp_all add: Let_def measure_def inv_image_def)
  (cases ?sg,simp_all)+
next
  case (5 f g)
  let ?sf = "psimpl f"
  let ?sg = "psimpl g"
  show ?case 
    using prems 
    by (cases ?sf, simp_all add: Let_def measure_def inv_image_def)
  (cases ?sg,simp_all)+
next
  case (6 f g)
  let ?sf = "psimpl f"
  let ?sg = "psimpl g"
  show ?case 
    using prems 
    by (cases ?sf, simp_all add: Let_def measure_def inv_image_def)
  (cases ?sg,simp_all)+
next
  case (7 f g)
  let ?sf = "psimpl f"
  let ?sg = "psimpl g"
  show ?case 
    using prems 
    by (cases ?sf, simp_all add: Let_def measure_def inv_image_def)
  (cases ?sg,simp_all)+

next
  case (8 f)
  let ?sf = "psimpl f"
  from prems have nv0sf:"novar0 ?sf" by simp
  show ?case using prems nv0sf 
    by (cases ?sf, auto simp add: Let_def measure_def inv_image_def)
qed simp_all

(* implements a disj of p applied to all elements of the list*)
consts explode_disj :: "(intterm list \<times> QF) \<Rightarrow> QF"
recdef explode_disj "measure (\<lambda>(is,p). length is)"
"explode_disj ([],p) = F"
"explode_disj (i#is,p) = 
  (let pi = psimpl (subst_p i p)
   in ( case pi of
        T \<Rightarrow> T 
       | F \<Rightarrow> explode_disj (is,p)
       | _ \<Rightarrow> (let r = explode_disj (is,p)
               in (case r of
                      T \<Rightarrow> T
                    | F \<Rightarrow> pi
                    | _ \<Rightarrow> Or pi r))))"

(* correctness theorem for one iteration of explode_disj *)
lemma explode_disj_disj: 
  assumes qfp: "isqfree p"
  shows "(qinterp (x#xs) (explode_disj(i#is,p))) = 
  (qinterp (x#xs) (subst_p i p) \<or> (qinterp (x#xs) (explode_disj(is,p))))"
  using qfp
proof-
  let ?pi = "psimpl (subst_p i p)"
  have pi: "qinterp (x#xs) ?pi = qinterp (x#xs) (subst_p i p)"
    by (simp add: psimpl_corr[where p="(subst_p i p)"])
  let ?dp = "explode_disj(is,p)"
  show ?thesis using pi
  proof (cases)
    assume "?pi= T \<or> ?pi = F"
    then show ?thesis using pi by (case_tac "?pi::QF", auto)
    
  next
    assume notTF: "\<not> (?pi = T \<or> ?pi = F)" 
    let ?dp = "explode_disj(is,p)"
    have dp_cases: "explode_disj(i#is,p) = 
      (case (explode_disj(is,p)) of
      T \<Rightarrow> T
      | F \<Rightarrow> psimpl (subst_p i p)
      | _ \<Rightarrow> Or (psimpl (subst_p i p)) (explode_disj(is,p)))" using notTF
      by (cases "?pi")
    (simp_all add: Let_def cong del: QF.weak_case_cong)
    show ?thesis using pi dp_cases notTF
    proof(cases)
      assume "?dp = T \<or> ?dp = F"
      then show ?thesis 
	using pi dp_cases
	by (cases "?dp") auto
    next
      assume "\<not> (?dp = T \<or> ?dp = F)"
      then show ?thesis using pi dp_cases notTF
	by (cases ?dp) auto 
    qed
  qed
qed

(* correctness theorem for explode_disj *)
lemma explode_disj_corr: 
  assumes qfp: "isqfree p"
  shows "(\<exists> x \<in> set xs. qinterp (a#ats) (subst_p x p)) = 
  (qinterp (a#ats) (explode_disj(xs,p)))" (is "(\<exists> x \<in> set xs. ?P x) = (?DP a xs )")
  using qfp
  proof (induct xs)
    case Nil show ?case by simp
  next 
    case (Cons y ys)
    have "(\<exists> x \<in> set (y#ys). ?P x) = (?P y \<or> (\<exists> x\<in> set ys. ?P x))"
      by auto
    also have "\<dots> = (?P y \<or> ?DP a ys)" using "Cons.hyps" qfp by auto 
    also have "\<dots> = ?DP a (y#ys)" using explode_disj_disj[OF qfp] by auto
    finally show ?case by simp
qed

(* explode_disj preserves independence on Var 0*)
lemma explode_disj_novar0:
  assumes nov0xs: "\<forall>x \<in> set xs. novar0I x"
  and qfp: "isqfree p"
  shows "novar0 (explode_disj (xs,p))"
  using nov0xs qfp
proof (induct xs, auto simp add: Let_def)
  case (goal1 a as)
  let ?q = "subst_p a p"
  let ?qs = "psimpl ?q"
  have "?qs = T \<or> ?qs = F \<or> (?qs \<noteq> T \<or> ?qs \<noteq> F)" by simp
  moreover
  { assume "?qs = T"  then have ?case  by simp }
  moreover
  { assume "?qs = F"  then have ?case by simp }
  moreover
  {
    assume qsnTF: "?qs \<noteq> T \<and> ?qs \<noteq> F"
    let ?r = "explode_disj (as,p)"
    have nov0qs: "novar0 ?qs"
      using prems
      by (auto simp add: psimpl_novar0 subst_p_novar0)
    have "?r = T \<or> ?r = F \<or> (?r \<noteq> T \<or> ?r \<noteq> F)" by simp
    moreover
    { assume "?r = T" then have ?case by (cases ?qs) auto  }
    moreover
    { assume "?r = F"  then have ?case  using nov0qs by (cases ?qs, auto)  }
    moreover
    { assume "?r \<noteq> T \<and> ?r \<noteq> F"  then have ?case using nov0qs prems qsnTF
	by (cases ?qs, auto simp add: Let_def) (cases ?r,auto)+
    }
    ultimately have ?case by blast
  }
  ultimately show ?case by blast
qed  
  
(* Some simple lemmas used for technical reasons *)
lemma eval_Or_cases: 
  "qinterp (a#ats) (case f of 
       T \<Rightarrow> T
       | F \<Rightarrow> g
       | _ \<Rightarrow> (case g of 
                     T \<Rightarrow> T
                   | F \<Rightarrow> f
                   | _ \<Rightarrow> Or f g)) = (qinterp (a#ats) f \<or> qinterp (a#ats) g)"
proof-
  let ?result = "
    (case f of 
    T \<Rightarrow> T
    | F \<Rightarrow> g
    | _ \<Rightarrow> (case g of 
    T \<Rightarrow> T
    | F \<Rightarrow> f
    | _ \<Rightarrow> Or f g))"
  have "f = T \<or> f = F \<or> (f \<noteq> T \<and> f\<noteq> F)" by auto
  moreover 
  {
    assume fT: "f = T"
    then have ?thesis by auto
  }
  moreover 
  {
    assume "f=F"
    then have ?thesis by auto
  }
  moreover 
  {
    assume fnT: "f\<noteq>T"
      and fnF: "f\<noteq>F"
    have "g = T \<or> g = F \<or> (g \<noteq> T \<and> g\<noteq> F)" by auto
    moreover 
    {
      assume "g=T"
      then have ?thesis using fnT fnF by (cases f, auto)
    }
    moreover 
    {
      assume "g=F"
      then have ?thesis using fnT fnF by (cases f, auto)
    }
    moreover 
    {
      assume gnT: "g\<noteq>T"
	and gnF: "g\<noteq>F"
      then have "?result = (case g of 
        T \<Rightarrow> T
        | F \<Rightarrow> f
        | _ \<Rightarrow> Or f g)"
	using fnT fnF
	by (cases f, auto)
      also have "\<dots> = Or f g"
	using gnT gnF
	by (cases g, auto)
      finally have "?result = Or f g" by simp
      then
      have  ?thesis by simp
    }
    ultimately have ?thesis by blast
	   
  }
  
  ultimately show ?thesis by blast
qed

lemma or_case_novar0:
  assumes fnTF: "f \<noteq> T \<and> f \<noteq> F"
  and gnTF: "g \<noteq> T \<and> g \<noteq> F"
  and f0: "novar0 f"
  and g0: "novar0 g"
  shows "novar0 
     (case f of T \<Rightarrow> T | F \<Rightarrow> g
     | _ \<Rightarrow> (case g of T \<Rightarrow> T | F \<Rightarrow> f | _ \<Rightarrow> Or f g))"
using fnTF gnTF f0 g0
by (cases f, auto) (cases g, auto)+


(* An implementation of sets trough lists *)
constdefs list_insert :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  "list_insert x xs \<equiv> (if x mem xs then xs else x#xs)"

lemma list_insert_set: "set (list_insert x xs) = set (x#xs)"
by(induct xs) (auto simp add: list_insert_def)

consts list_union :: "('a list \<times> 'a list) \<Rightarrow> 'a list"

recdef list_union "measure (\<lambda>(xs,ys). length xs)"
"list_union ([], ys) = ys"
"list_union (xs, []) = xs"
"list_union (x#xs,ys) = list_insert x (list_union (xs,ys))"

lemma list_union_set: "set (list_union(xs,ys)) = set (xs@ys)"
  by(induct xs ys rule: list_union.induct, auto simp add:list_insert_set)


consts list_set ::"'a list \<Rightarrow> 'a list"
primrec 
  "list_set [] = []"
  "list_set (x#xs) = list_insert x (list_set xs)"

lemma list_set_set: "set xs = set (list_set xs)"
by (induct xs) (auto simp add: list_insert_set)

consts iupto :: "int \<times> int \<Rightarrow> int list"
recdef iupto "measure (\<lambda> (i,j). nat (j - i +1))"
"iupto(i,j) = (if j<i then [] else (i#(iupto(i+1,j))))"

(* correctness theorem for iupto *)
lemma iupto_set: "set (iupto(i,j)) = {i .. j}"
proof(induct rule: iupto.induct)
  case (1 a b)
  show ?case
    using prems by (simp add: simp_from_to)
qed

consts all_sums :: "int \<times> intterm list \<Rightarrow> intterm list"
recdef all_sums "measure (\<lambda>(i,is). length is)"
"all_sums (j,[]) = []"
"all_sums (j,i#is) = (map (\<lambda>x. lin_add (i,(Cst x))) (iupto(1,j))@(all_sums (j,is)))"
(* all_sums preserves independence on Var 0*)
lemma all_sums_novar0:
  assumes nov0xs: "\<forall> x\<in> set xs. novar0I x"
  and linxs: "\<forall> x\<in> set xs. islinintterm x "
  shows "\<forall> x\<in> set (all_sums (d,xs)). novar0I x"
  using nov0xs linxs
proof(induct d xs rule: all_sums.induct)
  case 1 show ?case by simp
next 
  case (2 j a as)
  have lina: "islinintterm a" using "2.prems" by auto
  have nov0a: "novar0I a" using "2.prems" by auto
  let ?ys = "map (\<lambda>x. lin_add (a,(Cst x))) (iupto(1,j))"
  have nov0ys: "\<forall> y\<in> set ?ys. novar0I y"
  proof-
    have linx: "\<forall> x \<in> set (iupto(1,j)). islinintterm (Cst x)" by simp
    have nov0x: "\<forall> x \<in> set (iupto(1,j)). novar0I (Cst x)" by simp
    with nov0a lina linx have "\<forall> x\<in> set (iupto(1,j)). novar0I (lin_add (a,Cst x))" 
      by (simp add: lin_add_novar0)
    then show ?thesis by auto
  qed
  from "2.prems"
  have linas: "\<forall>u\<in>set as. islinintterm u" by auto
  from "2.prems" have nov0as: "\<forall>u\<in>set as. novar0I u" by auto
  from "2.hyps" linas nov0as have nov0alls: "\<forall>u\<in>set (all_sums (j, as)). novar0I u" by simp
  from nov0alls nov0ys have 
    cs: "(\<forall> u\<in> set (?ys@ (all_sums (j,as))). novar0I u)"
    by (simp only: sym[OF list_all_iff]) auto
  
  have "all_sums(j,a#as) = ?ys@(all_sums(j,as))"
    by simp
  then 
  have "?case = (\<forall> x\<in> set (?ys@ (all_sums (j,as))). novar0I x)"
    by auto
  with cs show ?case by blast
qed

(* correctness theorem for all_sums*)
lemma all_sums_ex: 
  "(\<exists> j\<in> {1..d}. \<exists> b\<in> (set xs). P (lin_add(b,Cst j))) = 
  (\<exists> x\<in> set (all_sums (d,xs)). P x)"
proof(induct d xs rule: all_sums.induct)
  case (1 a) show ?case by simp
next 
  case (2 a y ys)
  have "(\<exists> x\<in> set (map (\<lambda>x. lin_add (y,(Cst x))) (iupto(1,a))) . P x) = 
    (\<exists> j\<in> set (iupto(1,a)). P (lin_add(y,Cst j)))" 
    by auto
  also have "\<dots> = (\<exists> j\<in> {1..a}. P (lin_add(y,Cst j)))" 
    by (simp only : iupto_set)
  finally
  have dsj1:"(\<exists>j\<in>{1..a}. P (lin_add (y, Cst j))) = (\<exists>x\<in>set (map (\<lambda>x. lin_add (y, Cst x)) (iupto (1, a))). P x)" by simp
  
  from prems have "(\<exists> j\<in> {1..a}. \<exists> b\<in> (set (y#ys)). P (lin_add(b,Cst j))) = 
    ((\<exists> j\<in> {1..a}. P (lin_add(y,Cst j))) \<or> (\<exists> j\<in> {1..a}. \<exists> b \<in> set ys. P (lin_add(b,Cst j))))" by auto
  also
  have " \<dots> = ((\<exists> j\<in> {1..a}. P (lin_add(y,Cst j))) \<or> (\<exists> x\<in> set (all_sums(a, ys)). P x))" using prems by simp
  also have "\<dots> = ((\<exists>x\<in>set (map (\<lambda>x. lin_add (y, Cst x)) (iupto (1, a))). P x) \<or> (\<exists>x\<in>set (all_sums (a, ys)). P x))" using dsj1 by simp
  also have "\<dots> = (\<exists> x\<in> (set (map (\<lambda>x. lin_add (y, Cst x)) (iupto (1, a)))) \<union> (set (all_sums(a, ys))). P x)" by blast
  finally show ?case by simp
qed



(* explode_minf (p,B)  assumes that p is unified and B = bset p, it computes the rhs of cooper_mi_eq*)

consts explode_minf :: "(QF \<times> intterm list) \<Rightarrow> QF"
recdef explode_minf "measure size"
"explode_minf (q,B) = 
  (let d = divlcm q;
       pm = minusinf q;
        dj1 = explode_disj ((map Cst (iupto (1, d))),pm)
   in (case dj1 of 
         T \<Rightarrow> T
       | F \<Rightarrow> explode_disj (all_sums (d,B),q)
        | _ \<Rightarrow> (let dj2 = explode_disj (all_sums (d,B),q)
              in ( case dj2 of 
                     T \<Rightarrow> T
                   | F \<Rightarrow> dj1
                   | _ \<Rightarrow> Or dj1 dj2))))"

(* The result of the rhs of cooper's theorem doese not depend on Var 0*)
lemma explode_minf_novar0:
  assumes unifp : "isunified p"
  and bst: "set (bset p) = set B"
  shows "novar0 (explode_minf (p,B))"
proof-
  let ?d = "divlcm p"
  let ?pm = "minusinf p"
  let ?dj1 = "explode_disj (map Cst (iupto(1,?d)),?pm)"
  
  have qfpm: "isqfree ?pm"  using unified_islinform[OF unifp] minusinf_qfree by simp
  have dpos: "?d >0" using unified_islinform[OF unifp] divlcm_pos by simp 
  have "\<forall> x\<in> set (map Cst (iupto(1,?d))). novar0I x" by auto
  then have dj1_nov0: "novar0 ?dj1" using qfpm explode_disj_novar0 by simp
  
  let ?dj2 = "explode_disj (all_sums (?d,B),p)"
  have 
    bstlin: "\<forall>b\<in>set B. islinintterm b"
    using bset_lin[OF unifp] bst
    by simp
  
  have bstnov0: "\<forall>b\<in>set B. novar0I b"
    using bst bset_novar0[OF unifp] by simp
  have allsnov0: "\<forall>x\<in>set (all_sums(?d,B)). novar0I x "
    by (simp add:all_sums_novar0[OF bstnov0 bstlin] )
  then have dj2_nov0: "novar0 ?dj2" 
    using explode_disj_novar0 unified_isqfree[OF unifp] bst by simp
  have "?dj1 = T \<or> ?dj1 = F \<or> (?dj1 \<noteq> T \<and> ?dj1 \<noteq> F)" by auto
  moreover
  { assume "?dj1 = T" then have ?thesis by simp }
  moreover
  { assume "?dj1 = F" then have ?thesis using bst dj2_nov0 by (simp add: Let_def)}
  moreover
  {
    assume dj1nFT:"?dj1 \<noteq> T \<and> ?dj1 \<noteq> F"
    
    have "?dj2 = T \<or> ?dj2 = F \<or> (?dj2 \<noteq> T \<and> ?dj2 \<noteq> F)" by auto
    moreover
    { assume "?dj2 = T" then have ?thesis by (cases ?dj1) simp_all }
    moreover
    { assume "?dj2 = F" then have ?thesis using dj1_nov0 bst
	by (cases ?dj1) (simp_all add: Let_def)}
    moreover
    {
      assume dj2_nTF:"?dj2 \<noteq> T \<and> ?dj2 \<noteq> F"
      let ?res = "\<lambda>f. \<lambda>g. (case f of T \<Rightarrow> T | F \<Rightarrow> g
	| _ \<Rightarrow> (case g of T \<Rightarrow> T| F \<Rightarrow> f| _ \<Rightarrow> Or f g))"
      have expth: "explode_minf (p,B) = ?res ?dj1 ?dj2"
	by (simp add: Let_def del: iupto.simps split del: split_if
	  cong del: QF.weak_case_cong)
      then have ?thesis
	using prems or_case_novar0 [OF dj1nFT dj2_nTF dj1_nov0 dj2_nov0]
	by (simp add: Let_def del: iupto.simps cong del: QF.weak_case_cong)
    }
    ultimately have ?thesis by blast
  }
  ultimately show ?thesis by blast
qed
  
(* explode_minf computes the rhs of cooper's thm*)
lemma explode_minf_corr:
  assumes unifp : "isunified p"
  and bst: "set (bset p) = set B"
  shows "(\<exists> x . qinterp (x#ats) p) = (qinterp (a#ats) (explode_minf (p,B)))"
  (is "(\<exists> x. ?P x) = (?EXP a p)")
proof-
  let ?d = "divlcm p"
  let ?pm = "minusinf p"
  let ?dj1 = "explode_disj (map Cst (iupto(1,?d)),?pm)"
  have qfpm: "isqfree ?pm"  using unified_islinform[OF unifp] minusinf_qfree by simp 
  have nnfp: "isnnf p" by (rule unified_isnnf[OF unifp])

  have "(\<exists>j\<in>{1..?d}. qinterp (j # ats) (minusinf p))
    = (\<exists>j\<in> set (iupto(1,?d)). qinterp (j#ats) (minusinf p))"
    (is "(\<exists> j\<in> {1..?d}. ?QM j) = \<dots>")
    by (simp add: sym[OF iupto_set] )
  also
  have "\<dots> =(\<exists>j\<in> set (iupto(1,?d)). qinterp ((I_intterm (a#ats) (Cst j))#ats) (minusinf p))"
    by simp
  also have 
    "\<dots> = (\<exists>j\<in> set (map Cst (iupto(1,?d))). qinterp ((I_intterm (a#ats) j)#ats) (minusinf p))" by simp
  also have 
    "\<dots> = 
    (\<exists>j\<in> set (map Cst (iupto(1,?d))). qinterp (a#ats) (subst_p j (minusinf p)))"
    by (simp add: subst_p_corr[OF qfpm])
  finally have dj1_thm: 
    "(\<exists> j\<in> {1..?d}. ?QM j) = (qinterp (a#ats) ?dj1)"
    by (simp only: explode_disj_corr[OF qfpm])
  let ?dj2 = "explode_disj (all_sums (?d,B),p)"
  have 
    bstlin: "\<forall>b\<in>set B. islinintterm b" 
    using bst by (simp add: bset_lin[OF unifp])
  have bstnov0: "\<forall>b\<in>set B. novar0I b" 
    using bst by (simp add: bset_novar0[OF unifp])
  have allsnov0: "\<forall>x\<in>set (all_sums(?d,B)). novar0I x "
    by (simp add:all_sums_novar0[OF bstnov0 bstlin] )
  have "(\<exists> j\<in> {1..?d}. \<exists> b\<in> set B. ?P (I_intterm (a#ats) b + j)) = 
   (\<exists> j\<in> {1..?d}. \<exists> b\<in> set B. ?P (I_intterm (a#ats) (lin_add(b,Cst j))))"
    using bst by (auto simp add: lin_add_corr bset_lin[OF unifp])
  also have "\<dots> = (\<exists> x \<in> set (all_sums (?d, B)). ?P (I_intterm (a#ats) x))"
    by (simp add: all_sums_ex[where P="\<lambda> t. ?P (I_intterm (a#ats) t)"])
  finally 
  have "(\<exists> j\<in> {1..?d}. \<exists> b\<in> set B. ?P (I_intterm (a#ats) b + j)) = 
    (\<exists> x \<in> set (all_sums (?d, B)). qinterp (a#ats) (subst_p x p))"
    using allsnov0 prems linform_isqfree unified_islinform[OF unifp]
    by (simp add: all_sums_ex subst_p_corr)
  also have "\<dots> = (qinterp (a#ats) ?dj2)"
    using linform_isqfree unified_islinform[OF unifp]
    by (simp add: explode_disj_corr)
  finally have dj2th: 
    "(\<exists> j\<in> {1..?d}. \<exists> b\<in> set B. ?P (I_intterm (a#ats) b + j)) =  
    (qinterp (a#ats) ?dj2)" by simp
  let ?result = "\<lambda>f. \<lambda>g. 
    (case f of 
    T \<Rightarrow> T
    | F \<Rightarrow> g
    | _ \<Rightarrow> (case g of 
    T \<Rightarrow> T
    | F \<Rightarrow> f
    | _ \<Rightarrow> Or f g))"
  have "?EXP a p =  qinterp (a#ats) (?result ?dj1 ?dj2)"
    by (simp only: explode_minf.simps Let_def)
  also
  have "\<dots> = (qinterp (a#ats) ?dj1 \<or> qinterp (a#ats) ?dj2)" 
    by (rule eval_Or_cases[where f="?dj1" and g="?dj2" and a="a" and ats="ats"])
  also 
  have "\<dots> = ((\<exists> j\<in> {1..?d}. ?QM j) \<or> 
    (\<exists> j\<in> {1..?d}. \<exists> b\<in> set B. ?P (I_intterm (a#ats) b + j)))"
    by (simp add: dj1_thm dj2th)
  also
  have "\<dots> = (\<exists> x. ?P x)"
    using bst sym[OF cooper_mi_eq[OF unifp]] by simp
  finally show ?thesis by simp
qed


lemma explode_minf_corr2:
  assumes unifp : "isunified p"
  and bst: "set (bset p) = set B"
  shows "(qinterp ats (QEx p)) = (qinterp ats (decrvars(explode_minf (p,B))))"
  (is "?P = (?Qe p)")
proof-
  have "?P = (\<exists>x. qinterp (x#ats) p)" by simp
  also have "\<dots>  = (qinterp (a # ats) (explode_minf (p,B)))"
    using unifp bst explode_minf_corr by simp
  finally have ex: "?P = (qinterp (a # ats) (explode_minf (p,B)))" .
  have nv0: "novar0 (explode_minf (p,B))"
    by (rule explode_minf_novar0[OF unifp])
  show ?thesis
    using qinterp_novar0[OF nv0] ex by simp
qed

(* An implementation of cooper's method for both plus/minus/infinity *)

(* unify the formula *)
constdefs unify:: "QF \<Rightarrow> (QF \<times> intterm list)"
  "unify p \<equiv> 
  (let q = unitycoeff p;
       B = list_set(bset q);
       A = list_set (aset q)
  in
  if (length B \<le> length A)
             then (q,B)
             else (mirror q, map lin_neg A))"
  
(* unify behaves like unitycoeff *)
lemma unify_ex:
  assumes linp: "islinform p"
  shows "qinterp ats (QEx p) = qinterp ats (QEx (fst (unify p)))"
proof-
  have "length (list_set(bset (unitycoeff p))) \<le> length (list_set (aset (unitycoeff p))) \<or> length (list_set(bset (unitycoeff p))) > length (list_set (aset (unitycoeff p)))" by arith
  moreover
  {
    assume "length (list_set(bset (unitycoeff p))) \<le> length (list_set (aset (unitycoeff p)))"
    then have "fst (unify p) = unitycoeff p" using unify_def by (simp add: Let_def)
    then have ?thesis using unitycoeff_corr[OF linp]
      by simp
  }
  moreover 
  {
    assume "length (list_set(bset (unitycoeff p))) > length (list_set (aset (unitycoeff p)))"
    then have unif: "fst(unify p) = mirror (unitycoeff p)"
      using unify_def by (simp add: Let_def)
    let ?q ="unitycoeff p"
    have unifq: "isunified ?q" by(rule unitycoeff_unified[OF linp])
    have linq: "islinform ?q" by (rule unified_islinform[OF unifq])
    have "qinterp ats (QEx ?q) = qinterp ats (QEx (mirror ?q))" 
      by (rule mirror_ex2[OF unifq])
    moreover have "qinterp ats (QEx p) = qinterp ats (QEx ?q)"
      using unitycoeff_corr linp by simp
    ultimately have ?thesis using prems unif by simp
  }
  ultimately show ?thesis by blast
qed

(* unify's result is a unified formula *)
lemma unify_unified: 
  assumes linp: "islinform p"
  shows "isunified (fst (unify p))"
  using linp unitycoeff_unified mirror_unified unify_def unified_islinform
  by (auto simp add: Let_def)


(* unify preserves quantifier-freeness*)
lemma unify_qfree:
  assumes linp: "islinform p"
  shows "isqfree (fst(unify p))"
  using linp unify_unified unified_isqfree by simp

lemma unify_bst: 
  assumes linp: " islinform p" 
  and unif: "unify p = (q,B)"
  shows "set B = set (bset q)" 
proof-
  let ?q = "unitycoeff p"
  let ?a = "aset ?q"
  let ?b = "bset ?q"
  let ?la = "list_set ?a"
  let ?lb = "list_set ?b"
  have " length ?lb \<le> length ?la \<or> length ?lb > length ?la" by arith
  moreover 
  {
    assume "length ?lb \<le> length ?la"
    then
    have "unify p = (?q,?lb)"using unify_def prems by (simp add: Let_def)
    then 
    have ?thesis using prems by (simp add: sym[OF list_set_set])
  }
  moreover
  {    assume "length ?lb > length ?la"
    have r: "unify p = (mirror ?q,map lin_neg ?la)"using unify_def prems by (simp add: Let_def)
    have lin: "\<forall> x\<in> set (bset (mirror ?q)). islinintterm x"
      using bset_lin mirror_unified unitycoeff_unified[OF linp] by auto
    with r prems aset_eq_bset_mirror lin_neg_idemp unitycoeff_unified linp
    have "set B = set (map lin_neg (map lin_neg (bset (mirror (unitycoeff p)))))"
       by (simp add: sym[OF list_set_set])
     also have "\<dots> = set (map (\<lambda>x. lin_neg (lin_neg x)) (bset (mirror (unitycoeff p))))"
       by auto
     also have "\<dots> = set (bset (mirror (unitycoeff p)))"
       using lin lin_neg_idemp  by (auto simp add: map_idI)
     finally
     have ?thesis using r prems aset_eq_bset_mirror lin_neg_idemp unitycoeff_unified linp
       by (simp add: sym[OF list_set_set])}
  ultimately show ?thesis by blast
qed

lemma explode_minf_unify_novar0: 
  assumes linp: "islinform p"
  shows "novar0 (explode_minf (unify p))"
proof-
  have "\<exists> q B. unify p = (q,B)" by simp
  then obtain "q" "B" where qB_def: "unify p = (q,B)" by blast
  have unifq: "isunified q" using unify_unified[OF linp] qB_def by simp
  have bst: "set B = set (bset q)" using unify_bst linp qB_def by simp
  from unifq bst explode_minf_novar0 show ?thesis
    using qB_def by simp
qed

lemma explode_minf_unify_corr2:
  assumes linp: "islinform p"
  shows "qinterp ats (QEx p) = qinterp ats (decrvars(explode_minf(unify p)))"
proof-
  have "\<exists> q B. unify p = (q,B)" by simp
  then obtain "q" "B" where qB_def: "unify p = (q,B)" by blast
  have unifq: "isunified q" using unify_unified[OF linp] qB_def by simp
  have bst: "set (bset q) = set B" using unify_bst linp qB_def by simp
  from explode_minf_corr2[OF unifq bst] unify_ex[OF linp] show ?thesis
    using qB_def by simp
qed
(* An implementation of cooper's method *)
constdefs cooper:: "QF \<Rightarrow> QF option"
"cooper p \<equiv> lift_un (\<lambda>q. decrvars(explode_minf (unify q))) (linform (nnf p))"

(* cooper eliminates quantifiers *)
lemma cooper_qfree: "(\<And> q q'. \<lbrakk>isqfree q ; cooper q = Some q'\<rbrakk> \<Longrightarrow>  isqfree q')"
proof-
  fix "q" "q'"
  assume qfq: "isqfree q"
    and qeq: "cooper q = Some q'"
  from qeq have "\<exists>p. linform (nnf q) = Some p"
    by (cases "linform (nnf q)") (simp_all add: cooper_def)
  then obtain "p" where p_def: "linform (nnf q) = Some p" by blast
  have linp: "islinform p" using p_def linform_lin nnf_isnnf qfq 
    by auto
  have nnfq: "isnnf (nnf q)" using nnf_isnnf qfq by simp
  then have nnfp: "isnnf p" using linform_nnf[OF nnfq] p_def by auto
  have qfp: "isqfree p" using linp linform_isqfree by simp 
  have "cooper q = Some (decrvars(explode_minf (unify p)))" using p_def 
    by (simp add: cooper_def del: explode_minf.simps)
  then have "q' = decrvars (explode_minf (unify p))" using qeq by simp
  with linp qfp nnfp  unify_unified unify_qfree unified_islinform 
  show "isqfree q'"
    using novar0_qfree explode_minf_unify_novar0 decrvars_qfree
    by simp
qed

(* cooper preserves semantics *)
lemma cooper_corr: "(\<And> q q' ats. \<lbrakk>isqfree q ; cooper q = Some q'\<rbrakk> \<Longrightarrow>  (qinterp ats (QEx q)) = (qinterp ats q'))"  (is "\<And> q q' ats. \<lbrakk> _ ; _ \<rbrakk> \<Longrightarrow> (?P ats (QEx q) = ?P ats q')")
proof-
  fix "q" "q'" "ats"
  assume qfq: "isqfree q"
    and qeq: "cooper q = Some q'"
  from qeq have "\<exists>p. linform (nnf q) = Some p"
    by (cases "linform (nnf q)") (simp_all add: cooper_def)
  then obtain "p" where p_def: "linform (nnf q) = Some p" by blast
  have linp: "islinform p" using p_def linform_lin nnf_isnnf qfq by auto
  have qfp: "isqfree p" using linp linform_isqfree by simp 
  have nnfq: "isnnf (nnf q)" using nnf_isnnf qfq by simp
  then have nnfp: "isnnf p" using linform_nnf[OF nnfq] p_def by auto
  have "\<forall> ats. ?P ats q = ?P ats (nnf q)" using nnf_corr qfq by auto
  then have qeqp: "\<forall> ats. ?P ats q = ?P ats p"
    using linform_corr p_def nnf_isnnf qfq
    by auto

  have "cooper q = Some (decrvars (explode_minf (unify p)))" using p_def 
    by (simp add: cooper_def del: explode_minf.simps)
  then have decr: "q' = decrvars(explode_minf (unify p))" using qeq by simp
  have eqq:"?P ats (QEx q) = ?P ats (QEx p)" using qeqp by auto
  with decr explode_minf_unify_corr2 unified_islinform unify_unified linp 
  show "?P ats (QEx q) = ?P ats q'" by simp
qed  

(* A decision procedure for Presburger Arithmetics *)
constdefs pa:: "QF \<Rightarrow> QF option"
"pa p \<equiv> lift_un psimpl (qelim(cooper, p))"

lemma psimpl_qfree: "isqfree p \<Longrightarrow> isqfree (psimpl p)"
apply(induct p rule: isqfree.induct)
apply(auto simp add: Let_def measure_def inv_image_def)
apply (simp_all cong del: QF.weak_case_cong add: Let_def)
apply (case_tac "psimpl p", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl p", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl p", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl p", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)
apply (case_tac "psimpl q", auto)

apply (case_tac "psimpl p", auto)
apply (case_tac "lift_bin (\<lambda>x y. lin_add (x, lin_neg y), linearize y,
                   linearize z)", auto)
apply (case_tac "a",auto)
apply (case_tac "lift_bin (\<lambda>x y. lin_add (x, lin_neg y), linearize ac,
                   linearize ad)", auto)
apply (case_tac "a",auto)
apply (case_tac "ae", auto)
apply (case_tac "linearize af", auto)
by (case_tac "a", auto)

(* pa eliminates quantifiers *)
theorem pa_qfree: "\<And> p'. pa p = Some p' \<Longrightarrow> isqfree p'"
proof(simp only: pa_def)
fix "p'"
assume qep: "lift_un psimpl (qelim (cooper, p)) = Some p'"
then have "\<exists> q. qelim (cooper, p) = Some q"
  by (cases "qelim(cooper, p)") auto
then obtain "q" where q_def: "qelim (cooper, p) = Some q" by blast
have "\<And>q q'. \<lbrakk>isqfree q; cooper q = Some q'\<rbrakk> \<Longrightarrow> isqfree q'" using cooper_qfree by blast
with q_def
have "isqfree q" using qelim_qfree by blast
then have "isqfree (psimpl q)" using psimpl_qfree
  by auto
then show "isqfree p'"
  using prems 
  by simp

qed

(* pa preserves semantics *)
theorem pa_corr: 
  "\<And> p'. pa p = Some p' \<Longrightarrow> (qinterp ats p = qinterp ats p')"
proof(simp only: pa_def)
  fix "p'"
  assume qep: "lift_un psimpl (qelim(cooper, p)) = Some p'"
 then have "\<exists> q. qelim (cooper, p) = Some q"
  by (cases "qelim(cooper, p)") auto
then obtain "q" where q_def: "qelim (cooper, p) = Some q" by blast 
  have cp1:"\<And>q q' ats. 
    \<lbrakk>isqfree q; cooper q = Some q'\<rbrakk> \<Longrightarrow> qinterp ats (QEx q) = qinterp ats q'"
    using cooper_corr by blast
  moreover have cp2: "\<And>q q'. \<lbrakk>isqfree q; cooper q = Some q'\<rbrakk> \<Longrightarrow> isqfree q'"
    using cooper_qfree by blast
  ultimately have "qinterp ats p = qinterp ats q" using qelim_corr qep psimpl_corr q_def
    by blast
  then have "qinterp ats p = qinterp ats (psimpl q)" using psimpl_corr q_def
    by auto
  then show "qinterp ats p = qinterp ats p'" using prems 
    by simp
qed

lemma [code]: "linearize (Mult i j) = 
  (case linearize i of
  None \<Rightarrow> None
  | Some li \<Rightarrow> (case li of 
     Cst b \<Rightarrow> (case linearize j of
      None \<Rightarrow> None
     | (Some lj) \<Rightarrow> Some (lin_mul(b,lj)))
  | _ \<Rightarrow> (case linearize j of
      None \<Rightarrow> None
    | (Some lj) \<Rightarrow> (case lj of 
        Cst b \<Rightarrow> Some (lin_mul (b,li))
      | _ \<Rightarrow> None))))"
by (simp add: measure_def inv_image_def)

lemma [code]: "psimpl (And p q) = 
  (let p'= psimpl p
  in (case p' of 
       F \<Rightarrow> F
      |T \<Rightarrow> psimpl q
      | _ \<Rightarrow> let q' = psimpl q
             in (case q' of
                     F \<Rightarrow> F
                   | T \<Rightarrow> p'
                   | _ \<Rightarrow> (And p' q'))))"

by (simp add: measure_def inv_image_def)

lemma [code]: "psimpl (Or p q) = 
  (let p'= psimpl p
  in (case p' of 
        T \<Rightarrow> T
      | F \<Rightarrow> psimpl q
      | _ \<Rightarrow> let q' = psimpl q
             in (case q' of
                     T \<Rightarrow> T
                   | F \<Rightarrow> p'
                   | _ \<Rightarrow> (Or p' q'))))"

by (simp add: measure_def inv_image_def)

lemma [code]: "psimpl (Imp p q) = 
  (let p'= psimpl p
  in (case p' of 
       F \<Rightarrow> T
      |T \<Rightarrow> psimpl q
      | NOT p1 \<Rightarrow> let q' = psimpl q
             in (case q' of
                     F \<Rightarrow> p1
                   | T \<Rightarrow> T
                   | _ \<Rightarrow> (Or p1 q'))
      | _ \<Rightarrow> let q' = psimpl q
             in (case q' of
                     F \<Rightarrow> NOT p'
                   | T \<Rightarrow> T
                   | _ \<Rightarrow> (Imp p' q'))))"
by (simp add: measure_def inv_image_def)

declare zdvd_iff_zmod_eq_0 [code]

(*
generate_code ("presburger.ML") test = "pa"
use "rcooper.ML"
oracle rpresburger_oracle ("term") = RCooper.rpresburger_oracle
use "rpresbtac.ML"
setup RPresburger.setup
*)

end
