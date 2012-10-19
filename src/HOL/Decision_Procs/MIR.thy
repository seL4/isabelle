(*  Title:      HOL/Decision_Procs/MIR.thy
    Author:     Amine Chaieb
*)

theory MIR
imports Complex_Main Dense_Linear_Order DP_Library
  "~~/src/HOL/Library/Efficient_Nat" "~~/src/HOL/Library/Old_Recdef"
begin

section {* Quantifier elimination for @{text "\<real> (0, 1, +, floor, <)"} *}

declare real_of_int_floor_cancel [simp del]

lemma myle: fixes a b :: "'a::{ordered_ab_group_add}"
  shows "(a \<le> b) = (0 \<le> b - a)"
by (metis add_0_left add_le_cancel_right diff_add_cancel)

lemma myless: fixes a b :: "'a::{ordered_ab_group_add}"
  shows "(a < b) = (0 < b - a)"
by (metis le_iff_diff_le_0 less_le_not_le myle)

  (* Maybe should be added to the library \<dots> *)
lemma floor_int_eq: "(real n\<le> x \<and> x < real (n+1)) = (floor x = n)"
proof( auto)
  assume lb: "real n \<le> x"
    and ub: "x < real n + 1"
  have "real (floor x) \<le> x" by simp 
  hence "real (floor x) < real (n + 1) " using ub by arith
  hence "floor x < n+1" by simp
  moreover from lb have "n \<le> floor x" using floor_mono[where x="real n" and y="x"] 
    by simp ultimately show "floor x = n" by simp
qed

(* Periodicity of dvd *)
lemma dvd_period:
  assumes advdd: "(a::int) dvd d"
  shows "(a dvd (x + t)) = (a dvd ((x+ c*d) + t))"
  using advdd  
proof-
  {fix x k
    from inf_period(3)[OF advdd, rule_format, where x=x and k="-k"]  
    have " ((a::int) dvd (x + t)) = (a dvd (x+k*d + t))" by simp}
  hence "\<forall>x.\<forall>k. ((a::int) dvd (x + t)) = (a dvd (x+k*d + t))"  by simp
  then show ?thesis by simp
qed

(* The Divisibility relation between reals *)
definition
  rdvd:: "real \<Rightarrow> real \<Rightarrow> bool" (infixl "rdvd" 50)
where
  rdvd_def: "x rdvd y \<longleftrightarrow> (\<exists>k\<Colon>int. y = x * real k)"

lemma int_rdvd_real: 
  shows "real (i::int) rdvd x = (i dvd (floor x) \<and> real (floor x) = x)" (is "?l = ?r")
proof
  assume "?l" 
  hence th: "\<exists> k. x=real (i*k)" by (simp add: rdvd_def)
  hence th': "real (floor x) = x" by (auto simp del: real_of_int_mult)
  with th have "\<exists> k. real (floor x) = real (i*k)" by simp
  hence "\<exists> k. floor x = i*k" by (simp only: real_of_int_inject)
  thus ?r  using th' by (simp add: dvd_def) 
next
  assume "?r" hence "(i\<Colon>int) dvd \<lfloor>x\<Colon>real\<rfloor>" ..
  hence "\<exists> k. real (floor x) = real (i*k)" 
    by (simp only: real_of_int_inject) (simp add: dvd_def)
  thus ?l using `?r` by (simp add: rdvd_def)
qed

lemma int_rdvd_iff: "(real (i::int) rdvd real t) = (i dvd t)"
by (auto simp add: rdvd_def dvd_def) (rule_tac x="k" in exI, simp only :real_of_int_mult[symmetric])


lemma rdvd_abs1: 
  "(abs (real d) rdvd t) = (real (d ::int) rdvd t)"
proof
  assume d: "real d rdvd t"
  from d int_rdvd_real have d2: "d dvd (floor t)" and ti: "real (floor t) = t" by auto

  from iffD2[OF abs_dvd_iff] d2 have "(abs d) dvd (floor t)" by blast
  with ti int_rdvd_real[symmetric] have "real (abs d) rdvd t" by blast 
  thus "abs (real d) rdvd t" by simp
next
  assume "abs (real d) rdvd t" hence "real (abs d) rdvd t" by simp
  with int_rdvd_real[where i="abs d" and x="t"] have d2: "abs d dvd floor t" and ti: "real (floor t) =t" by auto
  from iffD1[OF abs_dvd_iff] d2 have "d dvd floor t" by blast
  with ti int_rdvd_real[symmetric] show "real d rdvd t" by blast
qed

lemma rdvd_minus: "(real (d::int) rdvd t) = (real d rdvd -t)"
  apply (auto simp add: rdvd_def)
  apply (rule_tac x="-k" in exI, simp) 
  apply (rule_tac x="-k" in exI, simp)
done

lemma rdvd_left_0_eq: "(0 rdvd t) = (t=0)"
by (auto simp add: rdvd_def)

lemma rdvd_mult: 
  assumes knz: "k\<noteq>0"
  shows "(real (n::int) * real (k::int) rdvd x * real k) = (real n rdvd x)"
using knz by (simp add:rdvd_def)

  (*********************************************************************************)
  (****                            SHADOW SYNTAX AND SEMANTICS                  ****)
  (*********************************************************************************)

datatype num = C int | Bound nat | CN nat int num | Neg num | Add num num| Sub num num 
  | Mul int num | Floor num| CF int num num

  (* A size for num to make inductive proofs simpler*)
primrec num_size :: "num \<Rightarrow> nat" where
 "num_size (C c) = 1"
| "num_size (Bound n) = 1"
| "num_size (Neg a) = 1 + num_size a"
| "num_size (Add a b) = 1 + num_size a + num_size b"
| "num_size (Sub a b) = 3 + num_size a + num_size b"
| "num_size (CN n c a) = 4 + num_size a "
| "num_size (CF c a b) = 4 + num_size a + num_size b"
| "num_size (Mul c a) = 1 + num_size a"
| "num_size (Floor a) = 1 + num_size a"

  (* Semantics of numeral terms (num) *)
primrec Inum :: "real list \<Rightarrow> num \<Rightarrow> real" where
  "Inum bs (C c) = (real c)"
| "Inum bs (Bound n) = bs!n"
| "Inum bs (CN n c a) = (real c) * (bs!n) + (Inum bs a)"
| "Inum bs (Neg a) = -(Inum bs a)"
| "Inum bs (Add a b) = Inum bs a + Inum bs b"
| "Inum bs (Sub a b) = Inum bs a - Inum bs b"
| "Inum bs (Mul c a) = (real c) * Inum bs a"
| "Inum bs (Floor a) = real (floor (Inum bs a))"
| "Inum bs (CF c a b) = real c * real (floor (Inum bs a)) + Inum bs b"
definition "isint t bs \<equiv> real (floor (Inum bs t)) = Inum bs t"

lemma isint_iff: "isint n bs = (real (floor (Inum bs n)) = Inum bs n)"
by (simp add: isint_def)

lemma isint_Floor: "isint (Floor n) bs"
  by (simp add: isint_iff)

lemma isint_Mul: "isint e bs \<Longrightarrow> isint (Mul c e) bs"
proof-
  let ?e = "Inum bs e"
  let ?fe = "floor ?e"
  assume be: "isint e bs" hence efe:"real ?fe = ?e" by (simp add: isint_iff)
  have "real ((floor (Inum bs (Mul c e)))) = real (floor (real (c * ?fe)))" using efe by simp
  also have "\<dots> = real (c* ?fe)" by (simp only: floor_real_of_int) 
  also have "\<dots> = real c * ?e" using efe by simp
  finally show ?thesis using isint_iff by simp
qed

lemma isint_neg: "isint e bs \<Longrightarrow> isint (Neg e) bs"
proof-
  let ?I = "\<lambda> t. Inum bs t"
  assume ie: "isint e bs"
  hence th: "real (floor (?I e)) = ?I e" by (simp add: isint_def)  
  have "real (floor (?I (Neg e))) = real (floor (- (real (floor (?I e)))))" by (simp add: th)
  also have "\<dots> = - real (floor (?I e))" by(simp add: floor_minus_real_of_int) 
  finally show "isint (Neg e) bs" by (simp add: isint_def th)
qed

lemma isint_sub: 
  assumes ie: "isint e bs" shows "isint (Sub (C c) e) bs"
proof-
  let ?I = "\<lambda> t. Inum bs t"
  from ie have th: "real (floor (?I e)) = ?I e" by (simp add: isint_def)  
  have "real (floor (?I (Sub (C c) e))) = real (floor ((real (c -floor (?I e)))))" by (simp add: th)
  also have "\<dots> = real (c- floor (?I e))" by(simp add: floor_minus_real_of_int) 
  finally show "isint (Sub (C c) e) bs" by (simp add: isint_def th)
qed

lemma isint_add: assumes
  ai:"isint a bs" and bi: "isint b bs" shows "isint (Add a b) bs"
proof-
  let ?a = "Inum bs a"
  let ?b = "Inum bs b"
  from ai bi isint_iff have "real (floor (?a + ?b)) = real (floor (real (floor ?a) + real (floor ?b)))" by simp
  also have "\<dots> = real (floor ?a) + real (floor ?b)" by simp
  also have "\<dots> = ?a + ?b" using ai bi isint_iff by simp
  finally show "isint (Add a b) bs" by (simp add: isint_iff)
qed

lemma isint_c: "isint (C j) bs"
  by (simp add: isint_iff)


    (* FORMULAE *)
datatype fm  = 
  T| F| Lt num| Le num| Gt num| Ge num| Eq num| NEq num| Dvd int num| NDvd int num|
  NOT fm| And fm fm|  Or fm fm| Imp fm fm| Iff fm fm| E fm| A fm


  (* A size for fm *)
fun fmsize :: "fm \<Rightarrow> nat" where
 "fmsize (NOT p) = 1 + fmsize p"
| "fmsize (And p q) = 1 + fmsize p + fmsize q"
| "fmsize (Or p q) = 1 + fmsize p + fmsize q"
| "fmsize (Imp p q) = 3 + fmsize p + fmsize q"
| "fmsize (Iff p q) = 3 + 2*(fmsize p + fmsize q)"
| "fmsize (E p) = 1 + fmsize p"
| "fmsize (A p) = 4+ fmsize p"
| "fmsize (Dvd i t) = 2"
| "fmsize (NDvd i t) = 2"
| "fmsize p = 1"
  (* several lemmas about fmsize *)
lemma fmsize_pos: "fmsize p > 0"
by (induct p rule: fmsize.induct) simp_all

  (* Semantics of formulae (fm) *)
primrec Ifm ::"real list \<Rightarrow> fm \<Rightarrow> bool" where
  "Ifm bs T = True"
| "Ifm bs F = False"
| "Ifm bs (Lt a) = (Inum bs a < 0)"
| "Ifm bs (Gt a) = (Inum bs a > 0)"
| "Ifm bs (Le a) = (Inum bs a \<le> 0)"
| "Ifm bs (Ge a) = (Inum bs a \<ge> 0)"
| "Ifm bs (Eq a) = (Inum bs a = 0)"
| "Ifm bs (NEq a) = (Inum bs a \<noteq> 0)"
| "Ifm bs (Dvd i b) = (real i rdvd Inum bs b)"
| "Ifm bs (NDvd i b) = (\<not>(real i rdvd Inum bs b))"
| "Ifm bs (NOT p) = (\<not> (Ifm bs p))"
| "Ifm bs (And p q) = (Ifm bs p \<and> Ifm bs q)"
| "Ifm bs (Or p q) = (Ifm bs p \<or> Ifm bs q)"
| "Ifm bs (Imp p q) = ((Ifm bs p) \<longrightarrow> (Ifm bs q))"
| "Ifm bs (Iff p q) = (Ifm bs p = Ifm bs q)"
| "Ifm bs (E p) = (\<exists> x. Ifm (x#bs) p)"
| "Ifm bs (A p) = (\<forall> x. Ifm (x#bs) p)"

consts prep :: "fm \<Rightarrow> fm"
recdef prep "measure fmsize"
  "prep (E T) = T"
  "prep (E F) = F"
  "prep (E (Or p q)) = Or (prep (E p)) (prep (E q))"
  "prep (E (Imp p q)) = Or (prep (E (NOT p))) (prep (E q))"
  "prep (E (Iff p q)) = Or (prep (E (And p q))) (prep (E (And (NOT p) (NOT q))))" 
  "prep (E (NOT (And p q))) = Or (prep (E (NOT p))) (prep (E(NOT q)))"
  "prep (E (NOT (Imp p q))) = prep (E (And p (NOT q)))"
  "prep (E (NOT (Iff p q))) = Or (prep (E (And p (NOT q)))) (prep (E(And (NOT p) q)))"
  "prep (E p) = E (prep p)"
  "prep (A (And p q)) = And (prep (A p)) (prep (A q))"
  "prep (A p) = prep (NOT (E (NOT p)))"
  "prep (NOT (NOT p)) = prep p"
  "prep (NOT (And p q)) = Or (prep (NOT p)) (prep (NOT q))"
  "prep (NOT (A p)) = prep (E (NOT p))"
  "prep (NOT (Or p q)) = And (prep (NOT p)) (prep (NOT q))"
  "prep (NOT (Imp p q)) = And (prep p) (prep (NOT q))"
  "prep (NOT (Iff p q)) = Or (prep (And p (NOT q))) (prep (And (NOT p) q))"
  "prep (NOT p) = NOT (prep p)"
  "prep (Or p q) = Or (prep p) (prep q)"
  "prep (And p q) = And (prep p) (prep q)"
  "prep (Imp p q) = prep (Or (NOT p) q)"
  "prep (Iff p q) = Or (prep (And p q)) (prep (And (NOT p) (NOT q)))"
  "prep p = p"
(hints simp add: fmsize_pos)
lemma prep: "\<And> bs. Ifm bs (prep p) = Ifm bs p"
by (induct p rule: prep.induct, auto)


  (* Quantifier freeness *)
fun qfree:: "fm \<Rightarrow> bool" where
  "qfree (E p) = False"
  | "qfree (A p) = False"
  | "qfree (NOT p) = qfree p" 
  | "qfree (And p q) = (qfree p \<and> qfree q)" 
  | "qfree (Or  p q) = (qfree p \<and> qfree q)" 
  | "qfree (Imp p q) = (qfree p \<and> qfree q)" 
  | "qfree (Iff p q) = (qfree p \<and> qfree q)"
  | "qfree p = True"

  (* Boundedness and substitution *)
primrec numbound0 :: "num \<Rightarrow> bool" (* a num is INDEPENDENT of Bound 0 *) where
  "numbound0 (C c) = True"
  | "numbound0 (Bound n) = (n>0)"
  | "numbound0 (CN n i a) = (n > 0 \<and> numbound0 a)"
  | "numbound0 (Neg a) = numbound0 a"
  | "numbound0 (Add a b) = (numbound0 a \<and> numbound0 b)"
  | "numbound0 (Sub a b) = (numbound0 a \<and> numbound0 b)" 
  | "numbound0 (Mul i a) = numbound0 a"
  | "numbound0 (Floor a) = numbound0 a"
  | "numbound0 (CF c a b) = (numbound0 a \<and> numbound0 b)" 

lemma numbound0_I:
  assumes nb: "numbound0 a"
  shows "Inum (b#bs) a = Inum (b'#bs) a"
  using nb by (induct a) auto

lemma numbound0_gen: 
  assumes nb: "numbound0 t" and ti: "isint t (x#bs)"
  shows "\<forall> y. isint t (y#bs)"
using nb ti 
proof(clarify)
  fix y
  from numbound0_I[OF nb, where bs="bs" and b="y" and b'="x"] ti[simplified isint_def]
  show "isint t (y#bs)"
    by (simp add: isint_def)
qed

primrec bound0:: "fm \<Rightarrow> bool" (* A Formula is independent of Bound 0 *) where
  "bound0 T = True"
  | "bound0 F = True"
  | "bound0 (Lt a) = numbound0 a"
  | "bound0 (Le a) = numbound0 a"
  | "bound0 (Gt a) = numbound0 a"
  | "bound0 (Ge a) = numbound0 a"
  | "bound0 (Eq a) = numbound0 a"
  | "bound0 (NEq a) = numbound0 a"
  | "bound0 (Dvd i a) = numbound0 a"
  | "bound0 (NDvd i a) = numbound0 a"
  | "bound0 (NOT p) = bound0 p"
  | "bound0 (And p q) = (bound0 p \<and> bound0 q)"
  | "bound0 (Or p q) = (bound0 p \<and> bound0 q)"
  | "bound0 (Imp p q) = ((bound0 p) \<and> (bound0 q))"
  | "bound0 (Iff p q) = (bound0 p \<and> bound0 q)"
  | "bound0 (E p) = False"
  | "bound0 (A p) = False"

lemma bound0_I:
  assumes bp: "bound0 p"
  shows "Ifm (b#bs) p = Ifm (b'#bs) p"
 using bp numbound0_I [where b="b" and bs="bs" and b'="b'"]
  by (induct p) auto

primrec numsubst0:: "num \<Rightarrow> num \<Rightarrow> num" (* substitute a num into a num for Bound 0 *) where
  "numsubst0 t (C c) = (C c)"
  | "numsubst0 t (Bound n) = (if n=0 then t else Bound n)"
  | "numsubst0 t (CN n i a) = (if n=0 then Add (Mul i t) (numsubst0 t a) else CN n i (numsubst0 t a))"
  | "numsubst0 t (CF i a b) = CF i (numsubst0 t a) (numsubst0 t b)"
  | "numsubst0 t (Neg a) = Neg (numsubst0 t a)"
  | "numsubst0 t (Add a b) = Add (numsubst0 t a) (numsubst0 t b)"
  | "numsubst0 t (Sub a b) = Sub (numsubst0 t a) (numsubst0 t b)" 
  | "numsubst0 t (Mul i a) = Mul i (numsubst0 t a)"
  | "numsubst0 t (Floor a) = Floor (numsubst0 t a)"

lemma numsubst0_I:
  shows "Inum (b#bs) (numsubst0 a t) = Inum ((Inum (b#bs) a)#bs) t"
  by (induct t) simp_all

primrec subst0:: "num \<Rightarrow> fm \<Rightarrow> fm" (* substitue a num into a formula for Bound 0 *) where
  "subst0 t T = T"
  | "subst0 t F = F"
  | "subst0 t (Lt a) = Lt (numsubst0 t a)"
  | "subst0 t (Le a) = Le (numsubst0 t a)"
  | "subst0 t (Gt a) = Gt (numsubst0 t a)"
  | "subst0 t (Ge a) = Ge (numsubst0 t a)"
  | "subst0 t (Eq a) = Eq (numsubst0 t a)"
  | "subst0 t (NEq a) = NEq (numsubst0 t a)"
  | "subst0 t (Dvd i a) = Dvd i (numsubst0 t a)"
  | "subst0 t (NDvd i a) = NDvd i (numsubst0 t a)"
  | "subst0 t (NOT p) = NOT (subst0 t p)"
  | "subst0 t (And p q) = And (subst0 t p) (subst0 t q)"
  | "subst0 t (Or p q) = Or (subst0 t p) (subst0 t q)"
  | "subst0 t (Imp p q) = Imp (subst0 t p) (subst0 t q)"
  | "subst0 t (Iff p q) = Iff (subst0 t p) (subst0 t q)"

lemma subst0_I: assumes qfp: "qfree p"
  shows "Ifm (b#bs) (subst0 a p) = Ifm ((Inum (b#bs) a)#bs) p"
  using qfp numsubst0_I[where b="b" and bs="bs" and a="a"]
  by (induct p) simp_all

fun decrnum:: "num \<Rightarrow> num" where
  "decrnum (Bound n) = Bound (n - 1)"
| "decrnum (Neg a) = Neg (decrnum a)"
| "decrnum (Add a b) = Add (decrnum a) (decrnum b)"
| "decrnum (Sub a b) = Sub (decrnum a) (decrnum b)"
| "decrnum (Mul c a) = Mul c (decrnum a)"
| "decrnum (Floor a) = Floor (decrnum a)"
| "decrnum (CN n c a) = CN (n - 1) c (decrnum a)"
| "decrnum (CF c a b) = CF c (decrnum a) (decrnum b)"
| "decrnum a = a"

fun decr :: "fm \<Rightarrow> fm" where
  "decr (Lt a) = Lt (decrnum a)"
| "decr (Le a) = Le (decrnum a)"
| "decr (Gt a) = Gt (decrnum a)"
| "decr (Ge a) = Ge (decrnum a)"
| "decr (Eq a) = Eq (decrnum a)"
| "decr (NEq a) = NEq (decrnum a)"
| "decr (Dvd i a) = Dvd i (decrnum a)"
| "decr (NDvd i a) = NDvd i (decrnum a)"
| "decr (NOT p) = NOT (decr p)" 
| "decr (And p q) = And (decr p) (decr q)"
| "decr (Or p q) = Or (decr p) (decr q)"
| "decr (Imp p q) = Imp (decr p) (decr q)"
| "decr (Iff p q) = Iff (decr p) (decr q)"
| "decr p = p"

lemma decrnum: assumes nb: "numbound0 t"
  shows "Inum (x#bs) t = Inum bs (decrnum t)"
  using nb by (induct t rule: decrnum.induct, simp_all)

lemma decr: assumes nb: "bound0 p"
  shows "Ifm (x#bs) p = Ifm bs (decr p)"
  using nb 
  by (induct p rule: decr.induct, simp_all add: decrnum)

lemma decr_qf: "bound0 p \<Longrightarrow> qfree (decr p)"
by (induct p, simp_all)

fun isatom :: "fm \<Rightarrow> bool" (* test for atomicity *) where
  "isatom T = True"
| "isatom F = True"
| "isatom (Lt a) = True"
| "isatom (Le a) = True"
| "isatom (Gt a) = True"
| "isatom (Ge a) = True"
| "isatom (Eq a) = True"
| "isatom (NEq a) = True"
| "isatom (Dvd i b) = True"
| "isatom (NDvd i b) = True"
| "isatom p = False"

lemma numsubst0_numbound0: assumes nb: "numbound0 t"
  shows "numbound0 (numsubst0 t a)"
using nb by (induct a, auto)

lemma subst0_bound0: assumes qf: "qfree p" and nb: "numbound0 t"
  shows "bound0 (subst0 t p)"
using qf numsubst0_numbound0[OF nb] by (induct p, auto)

lemma bound0_qf: "bound0 p \<Longrightarrow> qfree p"
by (induct p, simp_all)


definition djf:: "('a \<Rightarrow> fm) \<Rightarrow> 'a \<Rightarrow> fm \<Rightarrow> fm" where
  "djf f p q = (if q=T then T else if q=F then f p else 
  (let fp = f p in case fp of T \<Rightarrow> T | F \<Rightarrow> q | _ \<Rightarrow> Or fp q))"

definition evaldjf:: "('a \<Rightarrow> fm) \<Rightarrow> 'a list \<Rightarrow> fm" where
  "evaldjf f ps = foldr (djf f) ps F"

lemma djf_Or: "Ifm bs (djf f p q) = Ifm bs (Or (f p) q)"
by (cases "q=T", simp add: djf_def,cases "q=F",simp add: djf_def) 
(cases "f p", simp_all add: Let_def djf_def) 

lemma evaldjf_ex: "Ifm bs (evaldjf f ps) = (\<exists> p \<in> set ps. Ifm bs (f p))"
  by(induct ps, simp_all add: evaldjf_def djf_Or)

lemma evaldjf_bound0: 
  assumes nb: "\<forall> x\<in> set xs. bound0 (f x)"
  shows "bound0 (evaldjf f xs)"
  using nb by (induct xs, auto simp add: evaldjf_def djf_def Let_def) (case_tac "f a", auto) 

lemma evaldjf_qf: 
  assumes nb: "\<forall> x\<in> set xs. qfree (f x)"
  shows "qfree (evaldjf f xs)"
  using nb by (induct xs, auto simp add: evaldjf_def djf_def Let_def) (case_tac "f a", auto) 

fun disjuncts :: "fm \<Rightarrow> fm list" where
  "disjuncts (Or p q) = (disjuncts p) @ (disjuncts q)"
| "disjuncts F = []"
| "disjuncts p = [p]"

fun conjuncts :: "fm \<Rightarrow> fm list" where
  "conjuncts (And p q) = (conjuncts p) @ (conjuncts q)"
| "conjuncts T = []"
| "conjuncts p = [p]"

lemma conjuncts: "(\<forall> q\<in> set (conjuncts p). Ifm bs q) = Ifm bs p"
by(induct p rule: conjuncts.induct, auto)

lemma disjuncts_qf: "qfree p \<Longrightarrow> \<forall> q\<in> set (disjuncts p). qfree q"
proof-
  assume qf: "qfree p"
  hence "list_all qfree (disjuncts p)"
    by (induct p rule: disjuncts.induct, auto)
  thus ?thesis by (simp only: list_all_iff)
qed
lemma conjuncts_qf: "qfree p \<Longrightarrow> \<forall> q\<in> set (conjuncts p). qfree q"
proof-
  assume qf: "qfree p"
  hence "list_all qfree (conjuncts p)"
    by (induct p rule: conjuncts.induct, auto)
  thus ?thesis by (simp only: list_all_iff)
qed

definition DJ :: "(fm \<Rightarrow> fm) \<Rightarrow> fm \<Rightarrow> fm" where
  "DJ f p \<equiv> evaldjf f (disjuncts p)"

lemma DJ: assumes fdj: "\<forall> p q. f (Or p q) = Or (f p) (f q)"
  and fF: "f F = F"
  shows "Ifm bs (DJ f p) = Ifm bs (f p)"
proof-
  have "Ifm bs (DJ f p) = (\<exists> q \<in> set (disjuncts p). Ifm bs (f q))"
    by (simp add: DJ_def evaldjf_ex) 
  also have "\<dots> = Ifm bs (f p)" using fdj fF by (induct p rule: disjuncts.induct, auto)
  finally show ?thesis .
qed

lemma DJ_qf: assumes 
  fqf: "\<forall> p. qfree p \<longrightarrow> qfree (f p)"
  shows "\<forall>p. qfree p \<longrightarrow> qfree (DJ f p) "
proof(clarify)
  fix  p assume qf: "qfree p"
  have th: "DJ f p = evaldjf f (disjuncts p)" by (simp add: DJ_def)
  from disjuncts_qf[OF qf] have "\<forall> q\<in> set (disjuncts p). qfree q" .
  with fqf have th':"\<forall> q\<in> set (disjuncts p). qfree (f q)" by blast
  
  from evaldjf_qf[OF th'] th show "qfree (DJ f p)" by simp
qed

lemma DJ_qe: assumes qe: "\<forall> bs p. qfree p \<longrightarrow> qfree (qe p) \<and> (Ifm bs (qe p) = Ifm bs (E p))"
  shows "\<forall> bs p. qfree p \<longrightarrow> qfree (DJ qe p) \<and> (Ifm bs ((DJ qe p)) = Ifm bs (E p))"
proof(clarify)
  fix p::fm and bs
  assume qf: "qfree p"
  from qe have qth: "\<forall> p. qfree p \<longrightarrow> qfree (qe p)" by blast
  from DJ_qf[OF qth] qf have qfth:"qfree (DJ qe p)" by auto
  have "Ifm bs (DJ qe p) = (\<exists> q\<in> set (disjuncts p). Ifm bs (qe q))"
    by (simp add: DJ_def evaldjf_ex)
  also have "\<dots> = (\<exists> q \<in> set(disjuncts p). Ifm bs (E q))" using qe disjuncts_qf[OF qf] by auto
  also have "\<dots> = Ifm bs (E p)" by (induct p rule: disjuncts.induct, auto)
  finally show "qfree (DJ qe p) \<and> Ifm bs (DJ qe p) = Ifm bs (E p)" using qfth by blast
qed
  (* Simplification *)

  (* Algebraic simplifications for nums *)
fun bnds:: "num \<Rightarrow> nat list" where
  "bnds (Bound n) = [n]"
| "bnds (CN n c a) = n#(bnds a)"
| "bnds (Neg a) = bnds a"
| "bnds (Add a b) = (bnds a)@(bnds b)"
| "bnds (Sub a b) = (bnds a)@(bnds b)"
| "bnds (Mul i a) = bnds a"
| "bnds (Floor a) = bnds a"
| "bnds (CF c a b) = (bnds a)@(bnds b)"
| "bnds a = []"
fun lex_ns:: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "lex_ns [] ms = True"
| "lex_ns ns [] = False"
| "lex_ns (n#ns) (m#ms) = (n<m \<or> ((n = m) \<and> lex_ns ns ms)) "
definition lex_bnd :: "num \<Rightarrow> num \<Rightarrow> bool" where
  "lex_bnd t s \<equiv> lex_ns (bnds t) (bnds s)"

fun maxcoeff:: "num \<Rightarrow> int" where
  "maxcoeff (C i) = abs i"
| "maxcoeff (CN n c t) = max (abs c) (maxcoeff t)"
| "maxcoeff (CF c t s) = max (abs c) (maxcoeff s)"
| "maxcoeff t = 1"

lemma maxcoeff_pos: "maxcoeff t \<ge> 0"
  apply (induct t rule: maxcoeff.induct, auto) 
  done

fun numgcdh:: "num \<Rightarrow> int \<Rightarrow> int" where
  "numgcdh (C i) = (\<lambda>g. gcd i g)"
| "numgcdh (CN n c t) = (\<lambda>g. gcd c (numgcdh t g))"
| "numgcdh (CF c s t) = (\<lambda>g. gcd c (numgcdh t g))"
| "numgcdh t = (\<lambda>g. 1)"

definition
  numgcd :: "num \<Rightarrow> int"
where
  numgcd_def: "numgcd t = numgcdh t (maxcoeff t)"

fun reducecoeffh:: "num \<Rightarrow> int \<Rightarrow> num" where
  "reducecoeffh (C i) = (\<lambda> g. C (i div g))"
| "reducecoeffh (CN n c t) = (\<lambda> g. CN n (c div g) (reducecoeffh t g))"
| "reducecoeffh (CF c s t) = (\<lambda> g. CF (c div g)  s (reducecoeffh t g))"
| "reducecoeffh t = (\<lambda>g. t)"

definition
  reducecoeff :: "num \<Rightarrow> num"
where
  reducecoeff_def: "reducecoeff t =
  (let g = numgcd t in 
  if g = 0 then C 0 else if g=1 then t else reducecoeffh t g)"

fun dvdnumcoeff:: "num \<Rightarrow> int \<Rightarrow> bool" where
  "dvdnumcoeff (C i) = (\<lambda> g. g dvd i)"
| "dvdnumcoeff (CN n c t) = (\<lambda> g. g dvd c \<and> (dvdnumcoeff t g))"
| "dvdnumcoeff (CF c s t) = (\<lambda> g. g dvd c \<and> (dvdnumcoeff t g))"
| "dvdnumcoeff t = (\<lambda>g. False)"

lemma dvdnumcoeff_trans: 
  assumes gdg: "g dvd g'" and dgt':"dvdnumcoeff t g'"
  shows "dvdnumcoeff t g"
  using dgt' gdg 
  by (induct t rule: dvdnumcoeff.induct, simp_all add: gdg dvd_trans[OF gdg])

declare dvd_trans [trans add]

lemma numgcd0:
  assumes g0: "numgcd t = 0"
  shows "Inum bs t = 0"
proof-
  have "\<And>x. numgcdh t x= 0 \<Longrightarrow> Inum bs t = 0"
    by (induct t rule: numgcdh.induct, auto)
  thus ?thesis using g0[simplified numgcd_def] by blast
qed

lemma numgcdh_pos: assumes gp: "g \<ge> 0" shows "numgcdh t g \<ge> 0"
  using gp
  by (induct t rule: numgcdh.induct, auto)

lemma numgcd_pos: "numgcd t \<ge>0"
  by (simp add: numgcd_def numgcdh_pos maxcoeff_pos)

lemma reducecoeffh:
  assumes gt: "dvdnumcoeff t g" and gp: "g > 0" 
  shows "real g *(Inum bs (reducecoeffh t g)) = Inum bs t"
  using gt
proof(induct t rule: reducecoeffh.induct) 
  case (1 i) hence gd: "g dvd i" by simp
  from assms 1 show ?case by (simp add: real_of_int_div[OF gd])
next
  case (2 n c t)  hence gd: "g dvd c" by simp
  from assms 2 show ?case by (simp add: real_of_int_div[OF gd] algebra_simps)
next
  case (3 c s t)  hence gd: "g dvd c" by simp
  from assms 3 show ?case by (simp add: real_of_int_div[OF gd] algebra_simps) 
qed (auto simp add: numgcd_def gp)

fun ismaxcoeff:: "num \<Rightarrow> int \<Rightarrow> bool" where
  "ismaxcoeff (C i) = (\<lambda> x. abs i \<le> x)"
| "ismaxcoeff (CN n c t) = (\<lambda>x. abs c \<le> x \<and> (ismaxcoeff t x))"
| "ismaxcoeff (CF c s t) = (\<lambda>x. abs c \<le> x \<and> (ismaxcoeff t x))"
| "ismaxcoeff t = (\<lambda>x. True)"

lemma ismaxcoeff_mono: "ismaxcoeff t c \<Longrightarrow> c \<le> c' \<Longrightarrow> ismaxcoeff t c'"
by (induct t rule: ismaxcoeff.induct, auto)

lemma maxcoeff_ismaxcoeff: "ismaxcoeff t (maxcoeff t)"
proof (induct t rule: maxcoeff.induct)
  case (2 n c t)
  hence H:"ismaxcoeff t (maxcoeff t)" .
  have thh: "maxcoeff t \<le> max (abs c) (maxcoeff t)" by simp
  from ismaxcoeff_mono[OF H thh] show ?case by (simp add: le_maxI1)
next
  case (3 c t s) 
  hence H1:"ismaxcoeff s (maxcoeff s)" by auto
  have thh1: "maxcoeff s \<le> max \<bar>c\<bar> (maxcoeff s)" by (simp add: max_def)
  from ismaxcoeff_mono[OF H1 thh1] show ?case by (simp add: le_maxI1)
qed simp_all

lemma zgcd_gt1: "gcd i j > (1::int) \<Longrightarrow> ((abs i > 1 \<and> abs j > 1) \<or> (abs i = 0 \<and> abs j > 1) \<or> (abs i > 1 \<and> abs j = 0))"
  apply (unfold gcd_int_def)
  apply (cases "i = 0", simp_all)
  apply (cases "j = 0", simp_all)
  apply (cases "abs i = 1", simp_all)
  apply (cases "abs j = 1", simp_all)
  apply auto
  done
lemma numgcdh0:"numgcdh t m = 0 \<Longrightarrow>  m =0"
  by (induct t rule: numgcdh.induct) auto

lemma dvdnumcoeff_aux:
  assumes "ismaxcoeff t m" and mp:"m \<ge> 0" and "numgcdh t m > 1"
  shows "dvdnumcoeff t (numgcdh t m)"
using assms
proof(induct t rule: numgcdh.induct)
  case (2 n c t) 
  let ?g = "numgcdh t m"
  from 2 have th:"gcd c ?g > 1" by simp
  from zgcd_gt1[OF th] numgcdh_pos[OF mp, where t="t"]
  have "(abs c > 1 \<and> ?g > 1) \<or> (abs c = 0 \<and> ?g > 1) \<or> (abs c > 1 \<and> ?g = 0)" by simp
  moreover {assume "abs c > 1" and gp: "?g > 1" with 2
    have th: "dvdnumcoeff t ?g" by simp
    have th': "gcd c ?g dvd ?g" by simp
    from dvdnumcoeff_trans[OF th' th] have ?case by simp }
  moreover {assume "abs c = 0 \<and> ?g > 1"
    with 2 have th: "dvdnumcoeff t ?g" by simp
    have th': "gcd c ?g dvd ?g" by simp
    from dvdnumcoeff_trans[OF th' th] have ?case by simp
    hence ?case by simp }
  moreover {assume "abs c > 1" and g0:"?g = 0" 
    from numgcdh0[OF g0] have "m=0". with 2 g0 have ?case by simp }
  ultimately show ?case by blast
next
  case (3 c s t) 
  let ?g = "numgcdh t m"
  from 3 have th:"gcd c ?g > 1" by simp
  from zgcd_gt1[OF th] numgcdh_pos[OF mp, where t="t"]
  have "(abs c > 1 \<and> ?g > 1) \<or> (abs c = 0 \<and> ?g > 1) \<or> (abs c > 1 \<and> ?g = 0)" by simp
  moreover {assume "abs c > 1" and gp: "?g > 1" with 3
    have th: "dvdnumcoeff t ?g" by simp
    have th': "gcd c ?g dvd ?g" by simp
    from dvdnumcoeff_trans[OF th' th] have ?case by simp }
  moreover {assume "abs c = 0 \<and> ?g > 1"
    with 3 have th: "dvdnumcoeff t ?g" by simp
    have th': "gcd c ?g dvd ?g" by simp
    from dvdnumcoeff_trans[OF th' th] have ?case by simp
    hence ?case by simp }
  moreover {assume "abs c > 1" and g0:"?g = 0" 
    from numgcdh0[OF g0] have "m=0". with 3 g0 have ?case by simp }
  ultimately show ?case by blast
qed auto

lemma dvdnumcoeff_aux2:
  assumes "numgcd t > 1" shows "dvdnumcoeff t (numgcd t) \<and> numgcd t > 0"
  using assms 
proof (simp add: numgcd_def)
  let ?mc = "maxcoeff t"
  let ?g = "numgcdh t ?mc"
  have th1: "ismaxcoeff t ?mc" by (rule maxcoeff_ismaxcoeff)
  have th2: "?mc \<ge> 0" by (rule maxcoeff_pos)
  assume H: "numgcdh t ?mc > 1"
  from dvdnumcoeff_aux[OF th1 th2 H] show "dvdnumcoeff t ?g" .
qed

lemma reducecoeff: "real (numgcd t) * (Inum bs (reducecoeff t)) = Inum bs t"
proof-
  let ?g = "numgcd t"
  have "?g \<ge> 0"  by (simp add: numgcd_pos)
  hence "?g = 0 \<or> ?g = 1 \<or> ?g > 1" by auto
  moreover {assume "?g = 0" hence ?thesis by (simp add: numgcd0)} 
  moreover {assume "?g = 1" hence ?thesis by (simp add: reducecoeff_def)} 
  moreover { assume g1:"?g > 1"
    from dvdnumcoeff_aux2[OF g1] have th1:"dvdnumcoeff t ?g" and g0: "?g > 0" by blast+
    from reducecoeffh[OF th1 g0, where bs="bs"] g1 have ?thesis 
      by (simp add: reducecoeff_def Let_def)} 
  ultimately show ?thesis by blast
qed

lemma reducecoeffh_numbound0: "numbound0 t \<Longrightarrow> numbound0 (reducecoeffh t g)"
by (induct t rule: reducecoeffh.induct, auto)

lemma reducecoeff_numbound0: "numbound0 t \<Longrightarrow> numbound0 (reducecoeff t)"
using reducecoeffh_numbound0 by (simp add: reducecoeff_def Let_def)

consts
  numadd:: "num \<times> num \<Rightarrow> num"

recdef numadd "measure (\<lambda> (t,s). size t + size s)"
  "numadd (CN n1 c1 r1,CN n2 c2 r2) =
  (if n1=n2 then 
  (let c = c1 + c2
  in (if c=0 then numadd(r1,r2) else CN n1 c (numadd (r1,r2))))
  else if n1 \<le> n2 then CN n1 c1 (numadd (r1,CN n2 c2 r2))
  else (CN n2 c2 (numadd (CN n1 c1 r1,r2))))"
  "numadd (CN n1 c1 r1,t) = CN n1 c1 (numadd (r1, t))"  
  "numadd (t,CN n2 c2 r2) = CN n2 c2 (numadd (t,r2))" 
  "numadd (CF c1 t1 r1,CF c2 t2 r2) = 
   (if t1 = t2 then 
    (let c=c1+c2; s= numadd(r1,r2) in (if c=0 then s else CF c t1 s))
   else if lex_bnd t1 t2 then CF c1 t1 (numadd(r1,CF c2 t2 r2))
   else CF c2 t2 (numadd(CF c1 t1 r1,r2)))"
  "numadd (CF c1 t1 r1,C c) = CF c1 t1 (numadd (r1, C c))"
  "numadd (C c,CF c1 t1 r1) = CF c1 t1 (numadd (r1, C c))"
  "numadd (C b1, C b2) = C (b1+b2)"
  "numadd (a,b) = Add a b"

lemma numadd[simp]: "Inum bs (numadd (t,s)) = Inum bs (Add t s)"
apply (induct t s rule: numadd.induct, simp_all add: Let_def)
 apply (case_tac "c1+c2 = 0",case_tac "n1 \<le> n2", simp_all)
  apply (case_tac "n1 = n2", simp_all add: algebra_simps)
  apply (simp only: distrib_right[symmetric])
 apply simp
apply (case_tac "lex_bnd t1 t2", simp_all)
 apply (case_tac "c1+c2 = 0")
  by (case_tac "t1 = t2", simp_all add: algebra_simps distrib_right[symmetric] real_of_int_mult[symmetric] real_of_int_add[symmetric]del: real_of_int_mult real_of_int_add distrib_right)

lemma numadd_nb[simp]: "\<lbrakk> numbound0 t ; numbound0 s\<rbrakk> \<Longrightarrow> numbound0 (numadd (t,s))"
by (induct t s rule: numadd.induct, auto simp add: Let_def)

fun nummul:: "num \<Rightarrow> int \<Rightarrow> num" where
  "nummul (C j) = (\<lambda> i. C (i*j))"
| "nummul (CN n c t) = (\<lambda> i. CN n (c*i) (nummul t i))"
| "nummul (CF c t s) = (\<lambda> i. CF (c*i) t (nummul s i))"
| "nummul (Mul c t) = (\<lambda> i. nummul t (i*c))"
| "nummul t = (\<lambda> i. Mul i t)"

lemma nummul[simp]: "\<And> i. Inum bs (nummul t i) = Inum bs (Mul i t)"
by (induct t rule: nummul.induct, auto simp add: algebra_simps)

lemma nummul_nb[simp]: "\<And> i. numbound0 t \<Longrightarrow> numbound0 (nummul t i)"
by (induct t rule: nummul.induct, auto)

definition numneg :: "num \<Rightarrow> num" where
  "numneg t \<equiv> nummul t (- 1)"

definition numsub :: "num \<Rightarrow> num \<Rightarrow> num" where
  "numsub s t \<equiv> (if s = t then C 0 else numadd (s,numneg t))"

lemma numneg[simp]: "Inum bs (numneg t) = Inum bs (Neg t)"
using numneg_def nummul by simp

lemma numneg_nb[simp]: "numbound0 t \<Longrightarrow> numbound0 (numneg t)"
using numneg_def by simp

lemma numsub[simp]: "Inum bs (numsub a b) = Inum bs (Sub a b)"
using numsub_def by simp

lemma numsub_nb[simp]: "\<lbrakk> numbound0 t ; numbound0 s\<rbrakk> \<Longrightarrow> numbound0 (numsub t s)"
using numsub_def by simp

lemma isint_CF: assumes si: "isint s bs" shows "isint (CF c t s) bs"
proof-
  have cti: "isint (Mul c (Floor t)) bs" by (simp add: isint_Mul isint_Floor)
  
  have "?thesis = isint (Add (Mul c (Floor t)) s) bs" by (simp add: isint_def)
  also have "\<dots>" by (simp add: isint_add cti si)
  finally show ?thesis .
qed

fun split_int:: "num \<Rightarrow> num \<times> num" where
  "split_int (C c) = (C 0, C c)"
| "split_int (CN n c b) = 
     (let (bv,bi) = split_int b 
       in (CN n c bv, bi))"
| "split_int (CF c a b) = 
     (let (bv,bi) = split_int b 
       in (bv, CF c a bi))"
| "split_int a = (a,C 0)"

lemma split_int: "\<And>tv ti. split_int t = (tv,ti) \<Longrightarrow> (Inum bs (Add tv ti) = Inum bs t) \<and> isint ti bs"
proof (induct t rule: split_int.induct)
  case (2 c n b tv ti)
  let ?bv = "fst (split_int b)"
  let ?bi = "snd (split_int b)"
  have "split_int b = (?bv,?bi)" by simp
  with 2(1) have b:"Inum bs (Add ?bv ?bi) = Inum bs b" and bii: "isint ?bi bs" by blast+
  from 2(2) have tibi: "ti = ?bi" by (simp add: Let_def split_def)
  from 2(2) b[symmetric] bii show ?case by (auto simp add: Let_def split_def)
next
  case (3 c a b tv ti) 
  let ?bv = "fst (split_int b)"
  let ?bi = "snd (split_int b)"
  have "split_int b = (?bv,?bi)" by simp
  with 3(1) have b:"Inum bs (Add ?bv ?bi) = Inum bs b" and bii: "isint ?bi bs" by blast+
  from 3(2) have tibi: "ti = CF c a ?bi"
    by (simp add: Let_def split_def)
  from 3(2) b[symmetric] bii show ?case
    by (auto simp add: Let_def split_def isint_Floor isint_add isint_Mul isint_CF)
qed (auto simp add: Let_def isint_iff isint_Floor isint_add isint_Mul split_def algebra_simps)

lemma split_int_nb: "numbound0 t \<Longrightarrow> numbound0 (fst (split_int t)) \<and> numbound0 (snd (split_int t)) "
  by (induct t rule: split_int.induct) (auto simp add: Let_def split_def)

definition numfloor:: "num \<Rightarrow> num"
where
  "numfloor t = (let (tv,ti) = split_int t in 
  (case tv of C i \<Rightarrow> numadd (tv,ti) 
  | _ \<Rightarrow> numadd(CF 1 tv (C 0),ti)))"

lemma numfloor[simp]: "Inum bs (numfloor t) = Inum bs (Floor t)" (is "?n t = ?N (Floor t)")
proof-
  let ?tv = "fst (split_int t)"
  let ?ti = "snd (split_int t)"
  have tvti:"split_int t = (?tv,?ti)" by simp
  {assume H: "\<forall> v. ?tv \<noteq> C v"
    hence th1: "?n t = ?N (Add (Floor ?tv) ?ti)" 
      by (cases ?tv, auto simp add: numfloor_def Let_def split_def numadd)
    from split_int[OF tvti] have "?N (Floor t) = ?N (Floor(Add ?tv ?ti))" and tii:"isint ?ti bs" by simp+
    hence "?N (Floor t) = real (floor (?N (Add ?tv ?ti)))" by simp 
    also have "\<dots> = real (floor (?N ?tv) + (floor (?N ?ti)))"
      by (simp,subst tii[simplified isint_iff, symmetric]) simp
    also have "\<dots> = ?N (Add (Floor ?tv) ?ti)" by (simp add: tii[simplified isint_iff])
    finally have ?thesis using th1 by simp}
  moreover {fix v assume H:"?tv = C v" 
    from split_int[OF tvti] have "?N (Floor t) = ?N (Floor(Add ?tv ?ti))" and tii:"isint ?ti bs" by simp+
    hence "?N (Floor t) = real (floor (?N (Add ?tv ?ti)))" by simp 
    also have "\<dots> = real (floor (?N ?tv) + (floor (?N ?ti)))"
      by (simp,subst tii[simplified isint_iff, symmetric]) simp
    also have "\<dots> = ?N (Add (Floor ?tv) ?ti)" by (simp add: tii[simplified isint_iff])
    finally have ?thesis by (simp add: H numfloor_def Let_def split_def numadd) }
  ultimately show ?thesis by auto
qed

lemma numfloor_nb[simp]: "numbound0 t \<Longrightarrow> numbound0 (numfloor t)"
  using split_int_nb[where t="t"]
  by (cases "fst(split_int t)" , auto simp add: numfloor_def Let_def split_def  numadd_nb)

function simpnum:: "num \<Rightarrow> num" where
  "simpnum (C j) = C j"
| "simpnum (Bound n) = CN n 1 (C 0)"
| "simpnum (Neg t) = numneg (simpnum t)"
| "simpnum (Add t s) = numadd (simpnum t,simpnum s)"
| "simpnum (Sub t s) = numsub (simpnum t) (simpnum s)"
| "simpnum (Mul i t) = (if i = 0 then (C 0) else nummul (simpnum t) i)"
| "simpnum (Floor t) = numfloor (simpnum t)"
| "simpnum (CN n c t) = (if c=0 then simpnum t else CN n c (simpnum t))"
| "simpnum (CF c t s) = simpnum(Add (Mul c (Floor t)) s)"
by pat_completeness auto
termination by (relation "measure num_size") auto

lemma simpnum_ci[simp]: "Inum bs (simpnum t) = Inum bs t"
by (induct t rule: simpnum.induct, auto)

lemma simpnum_numbound0[simp]: 
  "numbound0 t \<Longrightarrow> numbound0 (simpnum t)"
by (induct t rule: simpnum.induct, auto)

fun nozerocoeff:: "num \<Rightarrow> bool" where
  "nozerocoeff (C c) = True"
| "nozerocoeff (CN n c t) = (c\<noteq>0 \<and> nozerocoeff t)"
| "nozerocoeff (CF c s t) = (c \<noteq> 0 \<and> nozerocoeff t)"
| "nozerocoeff (Mul c t) = (c\<noteq>0 \<and> nozerocoeff t)"
| "nozerocoeff t = True"

lemma numadd_nz : "nozerocoeff a \<Longrightarrow> nozerocoeff b \<Longrightarrow> nozerocoeff (numadd (a,b))"
by (induct a b rule: numadd.induct,auto simp add: Let_def)

lemma nummul_nz : "\<And> i. i\<noteq>0 \<Longrightarrow> nozerocoeff a \<Longrightarrow> nozerocoeff (nummul a i)"
  by (induct a rule: nummul.induct,auto simp add: Let_def numadd_nz)

lemma numneg_nz : "nozerocoeff a \<Longrightarrow> nozerocoeff (numneg a)"
by (simp add: numneg_def nummul_nz)

lemma numsub_nz: "nozerocoeff a \<Longrightarrow> nozerocoeff b \<Longrightarrow> nozerocoeff (numsub a b)"
by (simp add: numsub_def numneg_nz numadd_nz)

lemma split_int_nz: "nozerocoeff t \<Longrightarrow> nozerocoeff (fst (split_int t)) \<and> nozerocoeff (snd (split_int t))"
by (induct t rule: split_int.induct,auto simp add: Let_def split_def)

lemma numfloor_nz: "nozerocoeff t \<Longrightarrow> nozerocoeff (numfloor t)"
by (simp add: numfloor_def Let_def split_def)
(cases "fst (split_int t)", simp_all add: split_int_nz numadd_nz)

lemma simpnum_nz: "nozerocoeff (simpnum t)"
by(induct t rule: simpnum.induct, auto simp add: numadd_nz numneg_nz numsub_nz nummul_nz numfloor_nz)

lemma maxcoeff_nz: "nozerocoeff t \<Longrightarrow> maxcoeff t = 0 \<Longrightarrow> t = C 0"
proof (induct t rule: maxcoeff.induct)
  case (2 n c t)
  hence cnz: "c \<noteq>0" and mx: "max (abs c) (maxcoeff t) = 0" by simp+
  have "max (abs c) (maxcoeff t) \<ge> abs c" by (simp add: le_maxI1)
  with cnz have "max (abs c) (maxcoeff t) > 0" by arith
  with 2 show ?case by simp
next
  case (3 c s t) 
  hence cnz: "c \<noteq>0" and mx: "max (abs c) (maxcoeff t) = 0" by simp+
  have "max (abs c) (maxcoeff t) \<ge> abs c" by (simp add: le_maxI1)
  with cnz have "max (abs c) (maxcoeff t) > 0" by arith
  with 3 show ?case by simp
qed auto

lemma numgcd_nz: assumes nz: "nozerocoeff t" and g0: "numgcd t = 0" shows "t = C 0"
proof-
  from g0 have th:"numgcdh t (maxcoeff t) = 0" by (simp add: numgcd_def)
  from numgcdh0[OF th]  have th:"maxcoeff t = 0" .
  from maxcoeff_nz[OF nz th] show ?thesis .
qed

definition simp_num_pair :: "(num \<times> int) \<Rightarrow> num \<times> int" where
  "simp_num_pair \<equiv> (\<lambda> (t,n). (if n = 0 then (C 0, 0) else
   (let t' = simpnum t ; g = numgcd t' in 
      if g > 1 then (let g' = gcd n g in 
        if g' = 1 then (t',n) 
        else (reducecoeffh t' g', n div g')) 
      else (t',n))))"

lemma simp_num_pair_ci:
  shows "((\<lambda> (t,n). Inum bs t / real n) (simp_num_pair (t,n))) = ((\<lambda> (t,n). Inum bs t / real n) (t,n))"
  (is "?lhs = ?rhs")
proof-
  let ?t' = "simpnum t"
  let ?g = "numgcd ?t'"
  let ?g' = "gcd n ?g"
  {assume nz: "n = 0" hence ?thesis by (simp add: Let_def simp_num_pair_def)}
  moreover
  { assume nnz: "n \<noteq> 0"
    {assume "\<not> ?g > 1" hence ?thesis by (simp add: Let_def simp_num_pair_def)}
    moreover
    {assume g1:"?g>1" hence g0: "?g > 0" by simp
      from g1 nnz have gp0: "?g' \<noteq> 0" by simp
      hence g'p: "?g' > 0" using gcd_ge_0_int[where x="n" and y="numgcd ?t'"] by arith
      hence "?g'= 1 \<or> ?g' > 1" by arith
      moreover {assume "?g'=1" hence ?thesis by (simp add: Let_def simp_num_pair_def)}
      moreover {assume g'1:"?g'>1"
        from dvdnumcoeff_aux2[OF g1] have th1:"dvdnumcoeff ?t' ?g" ..
        let ?tt = "reducecoeffh ?t' ?g'"
        let ?t = "Inum bs ?tt"
        have gpdg: "?g' dvd ?g" by simp
        have gpdd: "?g' dvd n" by simp
        have gpdgp: "?g' dvd ?g'" by simp
        from reducecoeffh[OF dvdnumcoeff_trans[OF gpdg th1] g'p] 
        have th2:"real ?g' * ?t = Inum bs ?t'" by simp
        from nnz g1 g'1 have "?lhs = ?t / real (n div ?g')" by (simp add: simp_num_pair_def Let_def)
        also have "\<dots> = (real ?g' * ?t) / (real ?g' * (real (n div ?g')))" by simp
        also have "\<dots> = (Inum bs ?t' / real n)"
          using real_of_int_div[OF gpdd] th2 gp0 by simp
        finally have "?lhs = Inum bs t / real n" by simp
        then have ?thesis using nnz g1 g'1 by (simp add: simp_num_pair_def) }
      ultimately have ?thesis by blast }
    ultimately have ?thesis by blast }
  ultimately show ?thesis by blast
qed

lemma simp_num_pair_l:
  assumes tnb: "numbound0 t" and np: "n >0" and tn: "simp_num_pair (t,n) = (t',n')"
  shows "numbound0 t' \<and> n' >0"
proof-
  let ?t' = "simpnum t"
  let ?g = "numgcd ?t'"
  let ?g' = "gcd n ?g"
  { assume nz: "n = 0" hence ?thesis using assms by (simp add: Let_def simp_num_pair_def) }
  moreover
  { assume nnz: "n \<noteq> 0"
    {assume "\<not> ?g > 1" hence ?thesis using assms by (auto simp add: Let_def simp_num_pair_def) }
    moreover
    {assume g1:"?g>1" hence g0: "?g > 0" by simp
      from g1 nnz have gp0: "?g' \<noteq> 0" by simp
      hence g'p: "?g' > 0" using gcd_ge_0_int[where x="n" and y="numgcd ?t'"] by arith
      hence "?g'= 1 \<or> ?g' > 1" by arith
      moreover {assume "?g'=1" hence ?thesis using assms g1 g0
          by (auto simp add: Let_def simp_num_pair_def) }
      moreover {assume g'1:"?g'>1"
        have gpdg: "?g' dvd ?g" by simp
        have gpdd: "?g' dvd n" by simp
        have gpdgp: "?g' dvd ?g'" by simp
        from zdvd_imp_le[OF gpdd np] have g'n: "?g' \<le> n" .
        from zdiv_mono1[OF g'n g'p, simplified div_self[OF gp0]]
        have "n div ?g' >0" by simp
        hence ?thesis using assms g1 g'1
          by(auto simp add: simp_num_pair_def Let_def reducecoeffh_numbound0)}
      ultimately have ?thesis by blast }
    ultimately have ?thesis by blast } 
  ultimately show ?thesis by blast
qed

fun not:: "fm \<Rightarrow> fm" where
  "not (NOT p) = p"
| "not T = F"
| "not F = T"
| "not (Lt t) = Ge t"
| "not (Le t) = Gt t"
| "not (Gt t) = Le t"
| "not (Ge t) = Lt t"
| "not (Eq t) = NEq t"
| "not (NEq t) = Eq t"
| "not (Dvd i t) = NDvd i t"
| "not (NDvd i t) = Dvd i t"
| "not (And p q) = Or (not p) (not q)"
| "not (Or p q) = And (not p) (not q)"
| "not p = NOT p"
lemma not[simp]: "Ifm bs (not p) = Ifm bs (NOT p)"
  by (induct p) auto
lemma not_qf[simp]: "qfree p \<Longrightarrow> qfree (not p)"
  by (induct p) auto
lemma not_nb[simp]: "bound0 p \<Longrightarrow> bound0 (not p)"
  by (induct p) auto

definition conj :: "fm \<Rightarrow> fm \<Rightarrow> fm" where
  "conj p q \<equiv> (if (p = F \<or> q=F) then F else if p=T then q else if q=T then p else 
   if p = q then p else And p q)"
lemma conj[simp]: "Ifm bs (conj p q) = Ifm bs (And p q)"
  by (cases "p=F \<or> q=F", simp_all add: conj_def) (cases p, simp_all)

lemma conj_qf[simp]: "\<lbrakk>qfree p ; qfree q\<rbrakk> \<Longrightarrow> qfree (conj p q)"
  using conj_def by auto 
lemma conj_nb[simp]: "\<lbrakk>bound0 p ; bound0 q\<rbrakk> \<Longrightarrow> bound0 (conj p q)"
  using conj_def by auto 

definition disj :: "fm \<Rightarrow> fm \<Rightarrow> fm" where
  "disj p q \<equiv> (if (p = T \<or> q=T) then T else if p=F then q else if q=F then p 
       else if p=q then p else Or p q)"

lemma disj[simp]: "Ifm bs (disj p q) = Ifm bs (Or p q)"
  by (cases "p=T \<or> q=T",simp_all add: disj_def) (cases p,simp_all)
lemma disj_qf[simp]: "\<lbrakk>qfree p ; qfree q\<rbrakk> \<Longrightarrow> qfree (disj p q)"
  using disj_def by auto 
lemma disj_nb[simp]: "\<lbrakk>bound0 p ; bound0 q\<rbrakk> \<Longrightarrow> bound0 (disj p q)"
  using disj_def by auto 

definition imp :: "fm \<Rightarrow> fm \<Rightarrow> fm" where
  "imp p q \<equiv> (if (p = F \<or> q=T \<or> p=q) then T else if p=T then q else if q=F then not p 
    else Imp p q)"
lemma imp[simp]: "Ifm bs (imp p q) = Ifm bs (Imp p q)"
  by (cases "p=F \<or> q=T",simp_all add: imp_def)
lemma imp_qf[simp]: "\<lbrakk>qfree p ; qfree q\<rbrakk> \<Longrightarrow> qfree (imp p q)"
  using imp_def by (cases "p=F \<or> q=T",simp_all add: imp_def)

definition iff :: "fm \<Rightarrow> fm \<Rightarrow> fm" where
  "iff p q \<equiv> (if (p = q) then T else if (p = not q \<or> not p = q) then F else 
       if p=F then not q else if q=F then not p else if p=T then q else if q=T then p else 
  Iff p q)"
lemma iff[simp]: "Ifm bs (iff p q) = Ifm bs (Iff p q)"
  by (unfold iff_def,cases "p=q", simp,cases "p=not q", simp add:not) 
(cases "not p= q", auto simp add:not)
lemma iff_qf[simp]: "\<lbrakk>qfree p ; qfree q\<rbrakk> \<Longrightarrow> qfree (iff p q)"
  by (unfold iff_def,cases "p=q", auto)

fun check_int:: "num \<Rightarrow> bool" where
  "check_int (C i) = True"
| "check_int (Floor t) = True"
| "check_int (Mul i t) = check_int t"
| "check_int (Add t s) = (check_int t \<and> check_int s)"
| "check_int (Neg t) = check_int t"
| "check_int (CF c t s) = check_int s"
| "check_int t = False"
lemma check_int: "check_int t \<Longrightarrow> isint t bs"
by (induct t, auto simp add: isint_add isint_Floor isint_Mul isint_neg isint_c isint_CF)

lemma rdvd_left1_int: "real \<lfloor>t\<rfloor> = t \<Longrightarrow> 1 rdvd t"
  by (simp add: rdvd_def,rule_tac x="\<lfloor>t\<rfloor>" in exI) simp

lemma rdvd_reduce: 
  assumes gd:"g dvd d" and gc:"g dvd c" and gp: "g > 0"
  shows "real (d::int) rdvd real (c::int)*t = (real (d div g) rdvd real (c div g)*t)"
proof
  assume d: "real d rdvd real c * t"
  from d rdvd_def obtain k where k_def: "real c * t = real d* real (k::int)" by auto
  from gd dvd_def obtain kd where kd_def: "d = g * kd" by auto
  from gc dvd_def obtain kc where kc_def: "c = g * kc" by auto
  from k_def kd_def kc_def have "real g * real kc * t = real g * real kd * real k" by simp
  hence "real kc * t = real kd * real k" using gp by simp
  hence th:"real kd rdvd real kc * t" using rdvd_def by blast
  from kd_def gp have th':"kd = d div g" by simp
  from kc_def gp have "kc = c div g" by simp
  with th th' show "real (d div g) rdvd real (c div g) * t" by simp
next
  assume d: "real (d div g) rdvd real (c div g) * t"
  from gp have gnz: "g \<noteq> 0" by simp
  thus "real d rdvd real c * t" using d rdvd_mult[OF gnz, where n="d div g" and x="real (c div g) * t"] real_of_int_div[OF gd] real_of_int_div[OF gc] by simp
qed

definition simpdvd :: "int \<Rightarrow> num \<Rightarrow> (int \<times> num)" where
  "simpdvd d t \<equiv> 
   (let g = numgcd t in 
      if g > 1 then (let g' = gcd d g in 
        if g' = 1 then (d, t) 
        else (d div g',reducecoeffh t g')) 
      else (d, t))"
lemma simpdvd: 
  assumes tnz: "nozerocoeff t" and dnz: "d \<noteq> 0"
  shows "Ifm bs (Dvd (fst (simpdvd d t)) (snd (simpdvd d t))) = Ifm bs (Dvd d t)"
proof-
  let ?g = "numgcd t"
  let ?g' = "gcd d ?g"
  {assume "\<not> ?g > 1" hence ?thesis by (simp add: Let_def simpdvd_def)}
  moreover
  {assume g1:"?g>1" hence g0: "?g > 0" by simp
    from g1 dnz have gp0: "?g' \<noteq> 0" by simp
    hence g'p: "?g' > 0" using gcd_ge_0_int[where x="d" and y="numgcd t"] by arith
    hence "?g'= 1 \<or> ?g' > 1" by arith
    moreover {assume "?g'=1" hence ?thesis by (simp add: Let_def simpdvd_def)}
    moreover {assume g'1:"?g'>1"
      from dvdnumcoeff_aux2[OF g1] have th1:"dvdnumcoeff t ?g" ..
      let ?tt = "reducecoeffh t ?g'"
      let ?t = "Inum bs ?tt"
      have gpdg: "?g' dvd ?g" by simp
      have gpdd: "?g' dvd d" by simp
      have gpdgp: "?g' dvd ?g'" by simp
      from reducecoeffh[OF dvdnumcoeff_trans[OF gpdg th1] g'p] 
      have th2:"real ?g' * ?t = Inum bs t" by simp
      from assms g1 g0 g'1
      have "Ifm bs (Dvd (fst (simpdvd d t)) (snd(simpdvd d t))) = Ifm bs (Dvd (d div ?g') ?tt)"
        by (simp add: simpdvd_def Let_def)
      also have "\<dots> = (real d rdvd (Inum bs t))"
        using rdvd_reduce[OF gpdd gpdgp g'p, where t="?t", simplified div_self[OF gp0]] 
          th2[symmetric] by simp
      finally have ?thesis by simp  }
    ultimately have ?thesis by blast
  }
  ultimately show ?thesis by blast
qed

function (sequential) simpfm :: "fm \<Rightarrow> fm" where
  "simpfm (And p q) = conj (simpfm p) (simpfm q)"
| "simpfm (Or p q) = disj (simpfm p) (simpfm q)"
| "simpfm (Imp p q) = imp (simpfm p) (simpfm q)"
| "simpfm (Iff p q) = iff (simpfm p) (simpfm q)"
| "simpfm (NOT p) = not (simpfm p)"
| "simpfm (Lt a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v < 0) then T else F 
  | _ \<Rightarrow> Lt (reducecoeff a'))"
| "simpfm (Le a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v \<le> 0)  then T else F | _ \<Rightarrow> Le (reducecoeff a'))"
| "simpfm (Gt a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v > 0)  then T else F | _ \<Rightarrow> Gt (reducecoeff a'))"
| "simpfm (Ge a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v \<ge> 0)  then T else F | _ \<Rightarrow> Ge (reducecoeff a'))"
| "simpfm (Eq a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v = 0)  then T else F | _ \<Rightarrow> Eq (reducecoeff a'))"
| "simpfm (NEq a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v \<noteq> 0)  then T else F | _ \<Rightarrow> NEq (reducecoeff a'))"
| "simpfm (Dvd i a) = (if i=0 then simpfm (Eq a)
             else if (abs i = 1) \<and> check_int a then T
             else let a' = simpnum a in case a' of C v \<Rightarrow> if (i dvd v)  then T else F | _ \<Rightarrow> (let (d,t) = simpdvd i a' in Dvd d t))"
| "simpfm (NDvd i a) = (if i=0 then simpfm (NEq a) 
             else if (abs i = 1) \<and> check_int a then F
             else let a' = simpnum a in case a' of C v \<Rightarrow> if (\<not>(i dvd v)) then T else F | _ \<Rightarrow> (let (d,t) = simpdvd i a' in NDvd d t))"
| "simpfm p = p"
by pat_completeness auto
termination by (relation "measure fmsize") auto

lemma simpfm[simp]: "Ifm bs (simpfm p) = Ifm bs p"
proof(induct p rule: simpfm.induct)
  case (6 a) let ?sa = "simpnum a" have sa: "Inum bs ?sa = Inum bs a" by simp
  {fix v assume "?sa = C v" hence ?case using sa by simp }
  moreover {assume H:"\<not> (\<exists> v. ?sa = C v)"
    let ?g = "numgcd ?sa"
    let ?rsa = "reducecoeff ?sa"
    let ?r = "Inum bs ?rsa"
    have sa_nz: "nozerocoeff ?sa" by (rule simpnum_nz)
    {assume gz: "?g=0" from numgcd_nz[OF sa_nz gz] H have "False" by auto}
    with numgcd_pos[where t="?sa"] have "?g > 0" by (cases "?g=0", auto)
    hence gp: "real ?g > 0" by simp
    have "Inum bs ?sa = real ?g* ?r" by (simp add: reducecoeff)
    with sa have "Inum bs a < 0 = (real ?g * ?r < real ?g * 0)" by simp
    also have "\<dots> = (?r < 0)" using gp
      by (simp only: mult_less_cancel_left) simp
    finally have ?case using H by (cases "?sa" , simp_all add: Let_def)}
  ultimately show ?case by blast
next
  case (7 a)  let ?sa = "simpnum a" have sa: "Inum bs ?sa = Inum bs a" by simp
  {fix v assume "?sa = C v" hence ?case using sa by simp }
  moreover {assume H:"\<not> (\<exists> v. ?sa = C v)"
    let ?g = "numgcd ?sa"
    let ?rsa = "reducecoeff ?sa"
    let ?r = "Inum bs ?rsa"
    have sa_nz: "nozerocoeff ?sa" by (rule simpnum_nz)
    {assume gz: "?g=0" from numgcd_nz[OF sa_nz gz] H have "False" by auto}
    with numgcd_pos[where t="?sa"] have "?g > 0" by (cases "?g=0", auto)
    hence gp: "real ?g > 0" by simp
    have "Inum bs ?sa = real ?g* ?r" by (simp add: reducecoeff)
    with sa have "Inum bs a \<le> 0 = (real ?g * ?r \<le> real ?g * 0)" by simp
    also have "\<dots> = (?r \<le> 0)" using gp
      by (simp only: mult_le_cancel_left) simp
    finally have ?case using H by (cases "?sa" , simp_all add: Let_def)}
  ultimately show ?case by blast
next
  case (8 a)  let ?sa = "simpnum a" have sa: "Inum bs ?sa = Inum bs a" by simp
  {fix v assume "?sa = C v" hence ?case using sa by simp }
  moreover {assume H:"\<not> (\<exists> v. ?sa = C v)"
    let ?g = "numgcd ?sa"
    let ?rsa = "reducecoeff ?sa"
    let ?r = "Inum bs ?rsa"
    have sa_nz: "nozerocoeff ?sa" by (rule simpnum_nz)
    {assume gz: "?g=0" from numgcd_nz[OF sa_nz gz] H have "False" by auto}
    with numgcd_pos[where t="?sa"] have "?g > 0" by (cases "?g=0", auto)
    hence gp: "real ?g > 0" by simp
    have "Inum bs ?sa = real ?g* ?r" by (simp add: reducecoeff)
    with sa have "Inum bs a > 0 = (real ?g * ?r > real ?g * 0)" by simp
    also have "\<dots> = (?r > 0)" using gp
      by (simp only: mult_less_cancel_left) simp
    finally have ?case using H by (cases "?sa" , simp_all add: Let_def)}
  ultimately show ?case by blast
next
  case (9 a)  let ?sa = "simpnum a" have sa: "Inum bs ?sa = Inum bs a" by simp
  {fix v assume "?sa = C v" hence ?case using sa by simp }
  moreover {assume H:"\<not> (\<exists> v. ?sa = C v)"
    let ?g = "numgcd ?sa"
    let ?rsa = "reducecoeff ?sa"
    let ?r = "Inum bs ?rsa"
    have sa_nz: "nozerocoeff ?sa" by (rule simpnum_nz)
    {assume gz: "?g=0" from numgcd_nz[OF sa_nz gz] H have "False" by auto}
    with numgcd_pos[where t="?sa"] have "?g > 0" by (cases "?g=0", auto)
    hence gp: "real ?g > 0" by simp
    have "Inum bs ?sa = real ?g* ?r" by (simp add: reducecoeff)
    with sa have "Inum bs a \<ge> 0 = (real ?g * ?r \<ge> real ?g * 0)" by simp
    also have "\<dots> = (?r \<ge> 0)" using gp
      by (simp only: mult_le_cancel_left) simp
    finally have ?case using H by (cases "?sa" , simp_all add: Let_def)}
  ultimately show ?case by blast
next
  case (10 a)  let ?sa = "simpnum a" have sa: "Inum bs ?sa = Inum bs a" by simp
  {fix v assume "?sa = C v" hence ?case using sa by simp }
  moreover {assume H:"\<not> (\<exists> v. ?sa = C v)"
    let ?g = "numgcd ?sa"
    let ?rsa = "reducecoeff ?sa"
    let ?r = "Inum bs ?rsa"
    have sa_nz: "nozerocoeff ?sa" by (rule simpnum_nz)
    {assume gz: "?g=0" from numgcd_nz[OF sa_nz gz] H have "False" by auto}
    with numgcd_pos[where t="?sa"] have "?g > 0" by (cases "?g=0", auto)
    hence gp: "real ?g > 0" by simp
    have "Inum bs ?sa = real ?g* ?r" by (simp add: reducecoeff)
    with sa have "Inum bs a = 0 = (real ?g * ?r = 0)" by simp
    also have "\<dots> = (?r = 0)" using gp
      by (simp add: mult_eq_0_iff)
    finally have ?case using H by (cases "?sa" , simp_all add: Let_def)}
  ultimately show ?case by blast
next
  case (11 a)  let ?sa = "simpnum a" have sa: "Inum bs ?sa = Inum bs a" by simp
  {fix v assume "?sa = C v" hence ?case using sa by simp }
  moreover {assume H:"\<not> (\<exists> v. ?sa = C v)"
    let ?g = "numgcd ?sa"
    let ?rsa = "reducecoeff ?sa"
    let ?r = "Inum bs ?rsa"
    have sa_nz: "nozerocoeff ?sa" by (rule simpnum_nz)
    {assume gz: "?g=0" from numgcd_nz[OF sa_nz gz] H have "False" by auto}
    with numgcd_pos[where t="?sa"] have "?g > 0" by (cases "?g=0", auto)
    hence gp: "real ?g > 0" by simp
    have "Inum bs ?sa = real ?g* ?r" by (simp add: reducecoeff)
    with sa have "Inum bs a \<noteq> 0 = (real ?g * ?r \<noteq> 0)" by simp
    also have "\<dots> = (?r \<noteq> 0)" using gp
      by (simp add: mult_eq_0_iff)
    finally have ?case using H by (cases "?sa" , simp_all add: Let_def)}
  ultimately show ?case by blast
next
  case (12 i a)  let ?sa = "simpnum a"   have sa: "Inum bs ?sa = Inum bs a" by simp
  have "i=0 \<or> (abs i = 1 \<and> check_int a) \<or> (i\<noteq>0 \<and> ((abs i \<noteq> 1) \<or> (\<not> check_int a)))" by auto
  {assume "i=0" hence ?case using "12.hyps" by (simp add: rdvd_left_0_eq Let_def)}
  moreover 
  {assume ai1: "abs i = 1" and ai: "check_int a" 
    hence "i=1 \<or> i= - 1" by arith
    moreover {assume i1: "i = 1" 
      from rdvd_left1_int[OF check_int[OF ai, simplified isint_iff]] 
      have ?case using i1 ai by simp }
    moreover {assume i1: "i = - 1" 
      from rdvd_left1_int[OF check_int[OF ai, simplified isint_iff]] 
        rdvd_abs1[where d="- 1" and t="Inum bs a"]
      have ?case using i1 ai by simp }
    ultimately have ?case by blast}
  moreover   
  {assume inz: "i\<noteq>0" and cond: "(abs i \<noteq> 1) \<or> (\<not> check_int a)"
    {fix v assume "?sa = C v" hence ?case using sa[symmetric] inz cond
        by (cases "abs i = 1", auto simp add: int_rdvd_iff) }
    moreover {assume H:"\<not> (\<exists> v. ?sa = C v)" 
      hence th: "simpfm (Dvd i a) = Dvd (fst (simpdvd i ?sa)) (snd (simpdvd i ?sa))" using inz cond by (cases ?sa, auto simp add: Let_def split_def)
      from simpnum_nz have nz:"nozerocoeff ?sa" by simp
      from simpdvd [OF nz inz] th have ?case using sa by simp}
    ultimately have ?case by blast}
  ultimately show ?case by blast
next
  case (13 i a)  let ?sa = "simpnum a"   have sa: "Inum bs ?sa = Inum bs a" by simp
  have "i=0 \<or> (abs i = 1 \<and> check_int a) \<or> (i\<noteq>0 \<and> ((abs i \<noteq> 1) \<or> (\<not> check_int a)))" by auto
  {assume "i=0" hence ?case using "13.hyps" by (simp add: rdvd_left_0_eq Let_def)}
  moreover 
  {assume ai1: "abs i = 1" and ai: "check_int a" 
    hence "i=1 \<or> i= - 1" by arith
    moreover {assume i1: "i = 1" 
      from rdvd_left1_int[OF check_int[OF ai, simplified isint_iff]] 
      have ?case using i1 ai by simp }
    moreover {assume i1: "i = - 1" 
      from rdvd_left1_int[OF check_int[OF ai, simplified isint_iff]] 
        rdvd_abs1[where d="- 1" and t="Inum bs a"]
      have ?case using i1 ai by simp }
    ultimately have ?case by blast}
  moreover   
  {assume inz: "i\<noteq>0" and cond: "(abs i \<noteq> 1) \<or> (\<not> check_int a)"
    {fix v assume "?sa = C v" hence ?case using sa[symmetric] inz cond
        by (cases "abs i = 1", auto simp add: int_rdvd_iff) }
    moreover {assume H:"\<not> (\<exists> v. ?sa = C v)" 
      hence th: "simpfm (NDvd i a) = NDvd (fst (simpdvd i ?sa)) (snd (simpdvd i ?sa))" using inz cond 
        by (cases ?sa, auto simp add: Let_def split_def)
      from simpnum_nz have nz:"nozerocoeff ?sa" by simp
      from simpdvd [OF nz inz] th have ?case using sa by simp}
    ultimately have ?case by blast}
  ultimately show ?case by blast
qed (induct p rule: simpfm.induct, simp_all)

lemma simpdvd_numbound0: "numbound0 t \<Longrightarrow> numbound0 (snd (simpdvd d t))"
  by (simp add: simpdvd_def Let_def split_def reducecoeffh_numbound0)

lemma simpfm_bound0[simp]: "bound0 p \<Longrightarrow> bound0 (simpfm p)"
proof(induct p rule: simpfm.induct)
  case (6 a) hence nb: "numbound0 a" by simp
  hence "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  thus ?case by (cases "simpnum a", auto simp add: Let_def reducecoeff_numbound0)
next
  case (7 a) hence nb: "numbound0 a" by simp
  hence "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  thus ?case by (cases "simpnum a", auto simp add: Let_def reducecoeff_numbound0)
next
  case (8 a) hence nb: "numbound0 a" by simp
  hence "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  thus ?case by (cases "simpnum a", auto simp add: Let_def reducecoeff_numbound0)
next
  case (9 a) hence nb: "numbound0 a" by simp
  hence "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  thus ?case by (cases "simpnum a", auto simp add: Let_def reducecoeff_numbound0)
next
  case (10 a) hence nb: "numbound0 a" by simp
  hence "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  thus ?case by (cases "simpnum a", auto simp add: Let_def reducecoeff_numbound0)
next
  case (11 a) hence nb: "numbound0 a" by simp
  hence "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  thus ?case by (cases "simpnum a", auto simp add: Let_def reducecoeff_numbound0)
next
  case (12 i a) hence nb: "numbound0 a" by simp
  hence "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  thus ?case by (cases "simpnum a", auto simp add: Let_def reducecoeff_numbound0 simpdvd_numbound0 split_def)
next
  case (13 i a) hence nb: "numbound0 a" by simp
  hence "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  thus ?case by (cases "simpnum a", auto simp add: Let_def reducecoeff_numbound0 simpdvd_numbound0 split_def)
qed(auto simp add: disj_def imp_def iff_def conj_def)

lemma simpfm_qf[simp]: "qfree p \<Longrightarrow> qfree (simpfm p)"
by (induct p rule: simpfm.induct, auto simp add: Let_def)
(case_tac "simpnum a",auto simp add: split_def Let_def)+


  (* Generic quantifier elimination *)

definition list_conj :: "fm list \<Rightarrow> fm" where
  "list_conj ps \<equiv> foldr conj ps T"
lemma list_conj: "Ifm bs (list_conj ps) = (\<forall>p\<in> set ps. Ifm bs p)"
  by (induct ps, auto simp add: list_conj_def)
lemma list_conj_qf: " \<forall>p\<in> set ps. qfree p \<Longrightarrow> qfree (list_conj ps)"
  by (induct ps, auto simp add: list_conj_def)
lemma list_conj_nb: " \<forall>p\<in> set ps. bound0 p \<Longrightarrow> bound0 (list_conj ps)"
  by (induct ps, auto simp add: list_conj_def)
definition CJNB :: "(fm \<Rightarrow> fm) \<Rightarrow> fm \<Rightarrow> fm" where
  "CJNB f p \<equiv> (let cjs = conjuncts p ; (yes,no) = List.partition bound0 cjs
                   in conj (decr (list_conj yes)) (f (list_conj no)))"

lemma CJNB_qe: 
  assumes qe: "\<forall> bs p. qfree p \<longrightarrow> qfree (qe p) \<and> (Ifm bs (qe p) = Ifm bs (E p))"
  shows "\<forall> bs p. qfree p \<longrightarrow> qfree (CJNB qe p) \<and> (Ifm bs ((CJNB qe p)) = Ifm bs (E p))"
proof(clarify)
  fix bs p
  assume qfp: "qfree p"
  let ?cjs = "conjuncts p"
  let ?yes = "fst (List.partition bound0 ?cjs)"
  let ?no = "snd (List.partition bound0 ?cjs)"
  let ?cno = "list_conj ?no"
  let ?cyes = "list_conj ?yes"
  have part: "List.partition bound0 ?cjs = (?yes,?no)" by simp
  from partition_P[OF part] have "\<forall> q\<in> set ?yes. bound0 q" by blast 
  hence yes_nb: "bound0 ?cyes" by (simp add: list_conj_nb) 
  hence yes_qf: "qfree (decr ?cyes )" by (simp add: decr_qf)
  from conjuncts_qf[OF qfp] partition_set[OF part] 
  have " \<forall>q\<in> set ?no. qfree q" by auto
  hence no_qf: "qfree ?cno"by (simp add: list_conj_qf)
  with qe have cno_qf:"qfree (qe ?cno )" 
    and noE: "Ifm bs (qe ?cno) = Ifm bs (E ?cno)" by blast+
  from cno_qf yes_qf have qf: "qfree (CJNB qe p)" 
    by (simp add: CJNB_def Let_def conj_qf split_def)
  {fix bs
    from conjuncts have "Ifm bs p = (\<forall>q\<in> set ?cjs. Ifm bs q)" by blast
    also have "\<dots> = ((\<forall>q\<in> set ?yes. Ifm bs q) \<and> (\<forall>q\<in> set ?no. Ifm bs q))"
      using partition_set[OF part] by auto
    finally have "Ifm bs p = ((Ifm bs ?cyes) \<and> (Ifm bs ?cno))" using list_conj by simp}
  hence "Ifm bs (E p) = (\<exists>x. (Ifm (x#bs) ?cyes) \<and> (Ifm (x#bs) ?cno))" by simp
  also fix y have "\<dots> = (\<exists>x. (Ifm (y#bs) ?cyes) \<and> (Ifm (x#bs) ?cno))"
    using bound0_I[OF yes_nb, where bs="bs" and b'="y"] by blast
  also have "\<dots> = (Ifm bs (decr ?cyes) \<and> Ifm bs (E ?cno))"
    by (auto simp add: decr[OF yes_nb] simp del: partition_filter_conv)
  also have "\<dots> = (Ifm bs (conj (decr ?cyes) (qe ?cno)))"
    using qe[rule_format, OF no_qf] by auto
  finally have "Ifm bs (E p) = Ifm bs (CJNB qe p)" 
    by (simp add: Let_def CJNB_def split_def)
  with qf show "qfree (CJNB qe p) \<and> Ifm bs (CJNB qe p) = Ifm bs (E p)" by blast
qed

function (sequential) qelim :: "fm \<Rightarrow> (fm \<Rightarrow> fm) \<Rightarrow> fm" where
  "qelim (E p) = (\<lambda> qe. DJ (CJNB qe) (qelim p qe))"
| "qelim (A p) = (\<lambda> qe. not (qe ((qelim (NOT p) qe))))"
| "qelim (NOT p) = (\<lambda> qe. not (qelim p qe))"
| "qelim (And p q) = (\<lambda> qe. conj (qelim p qe) (qelim q qe))" 
| "qelim (Or  p q) = (\<lambda> qe. disj (qelim p qe) (qelim q qe))" 
| "qelim (Imp p q) = (\<lambda> qe. disj (qelim (NOT p) qe) (qelim q qe))"
| "qelim (Iff p q) = (\<lambda> qe. iff (qelim p qe) (qelim q qe))"
| "qelim p = (\<lambda> y. simpfm p)"
by pat_completeness auto
termination by (relation "measure fmsize") auto

lemma qelim_ci:
  assumes qe_inv: "\<forall> bs p. qfree p \<longrightarrow> qfree (qe p) \<and> (Ifm bs (qe p) = Ifm bs (E p))"
  shows "\<And> bs. qfree (qelim p qe) \<and> (Ifm bs (qelim p qe) = Ifm bs p)"
  using qe_inv DJ_qe[OF CJNB_qe[OF qe_inv]] 
  by (induct p rule: qelim.induct) (auto simp del: simpfm.simps)


text {* The @{text "\<int>"} Part *}
text{* Linearity for fm where Bound 0 ranges over @{text "\<int>"} *}

function zsplit0 :: "num \<Rightarrow> int \<times> num" (* splits the bounded from the unbounded part*) where
  "zsplit0 (C c) = (0,C c)"
| "zsplit0 (Bound n) = (if n=0 then (1, C 0) else (0,Bound n))"
| "zsplit0 (CN n c a) = zsplit0 (Add (Mul c (Bound n)) a)"
| "zsplit0 (CF c a b) = zsplit0 (Add (Mul c (Floor a)) b)"
| "zsplit0 (Neg a) = (let (i',a') =  zsplit0 a in (-i', Neg a'))"
| "zsplit0 (Add a b) = (let (ia,a') =  zsplit0 a ; 
                            (ib,b') =  zsplit0 b 
                            in (ia+ib, Add a' b'))"
| "zsplit0 (Sub a b) = (let (ia,a') =  zsplit0 a ; 
                            (ib,b') =  zsplit0 b 
                            in (ia-ib, Sub a' b'))"
| "zsplit0 (Mul i a) = (let (i',a') =  zsplit0 a in (i*i', Mul i a'))"
| "zsplit0 (Floor a) = (let (i',a') =  zsplit0 a in (i',Floor a'))"
by pat_completeness auto
termination by (relation "measure num_size") auto

lemma zsplit0_I:
  shows "\<And> n a. zsplit0 t = (n,a) \<Longrightarrow> (Inum ((real (x::int)) #bs) (CN 0 n a) = Inum (real x #bs) t) \<and> numbound0 a"
  (is "\<And> n a. ?S t = (n,a) \<Longrightarrow> (?I x (CN 0 n a) = ?I x t) \<and> ?N a")
proof(induct t rule: zsplit0.induct)
  case (1 c n a) thus ?case by auto 
next
  case (2 m n a) thus ?case by (cases "m=0") auto
next
  case (3 n i a n a') thus ?case by auto
next 
  case (4 c a b n a') thus ?case by auto
next
  case (5 t n a)
  let ?nt = "fst (zsplit0 t)"
  let ?at = "snd (zsplit0 t)"
  have abj: "zsplit0 t = (?nt,?at)" by simp hence th: "a=Neg ?at \<and> n=-?nt" using 5 
    by (simp add: Let_def split_def)
  from abj 5 have th2: "(?I x (CN 0 ?nt ?at) = ?I x t) \<and> ?N ?at" by blast
  from th2[simplified] th[simplified] show ?case by simp
next
  case (6 s t n a)
  let ?ns = "fst (zsplit0 s)"
  let ?as = "snd (zsplit0 s)"
  let ?nt = "fst (zsplit0 t)"
  let ?at = "snd (zsplit0 t)"
  have abjs: "zsplit0 s = (?ns,?as)" by simp 
  moreover have abjt:  "zsplit0 t = (?nt,?at)" by simp 
  ultimately have th: "a=Add ?as ?at \<and> n=?ns + ?nt" using 6
    by (simp add: Let_def split_def)
  from abjs[symmetric] have bluddy: "\<exists> x y. (x,y) = zsplit0 s" by blast
  from 6 have "(\<exists> x y. (x,y) = zsplit0 s) \<longrightarrow> (\<forall>xa xb. zsplit0 t = (xa, xb) \<longrightarrow> Inum (real x # bs) (CN 0 xa xb) = Inum (real x # bs) t \<and> numbound0 xb)" by blast (*FIXME*)
  with bluddy abjt have th3: "(?I x (CN 0 ?nt ?at) = ?I x t) \<and> ?N ?at" by blast
  from abjs 6  have th2: "(?I x (CN 0 ?ns ?as) = ?I x s) \<and> ?N ?as" by blast
  from th3[simplified] th2[simplified] th[simplified] show ?case 
    by (simp add: distrib_right)
next
  case (7 s t n a)
  let ?ns = "fst (zsplit0 s)"
  let ?as = "snd (zsplit0 s)"
  let ?nt = "fst (zsplit0 t)"
  let ?at = "snd (zsplit0 t)"
  have abjs: "zsplit0 s = (?ns,?as)" by simp 
  moreover have abjt:  "zsplit0 t = (?nt,?at)" by simp 
  ultimately have th: "a=Sub ?as ?at \<and> n=?ns - ?nt" using 7
    by (simp add: Let_def split_def)
  from abjs[symmetric] have bluddy: "\<exists> x y. (x,y) = zsplit0 s" by blast
  from 7 have "(\<exists> x y. (x,y) = zsplit0 s) \<longrightarrow> (\<forall>xa xb. zsplit0 t = (xa, xb) \<longrightarrow> Inum (real x # bs) (CN 0 xa xb) = Inum (real x # bs) t \<and> numbound0 xb)" by blast (*FIXME*)
  with bluddy abjt have th3: "(?I x (CN 0 ?nt ?at) = ?I x t) \<and> ?N ?at" by blast
  from abjs 7 have th2: "(?I x (CN 0 ?ns ?as) = ?I x s) \<and> ?N ?as" by blast
  from th3[simplified] th2[simplified] th[simplified] show ?case 
    by (simp add: left_diff_distrib)
next
  case (8 i t n a)
  let ?nt = "fst (zsplit0 t)"
  let ?at = "snd (zsplit0 t)"
  have abj: "zsplit0 t = (?nt,?at)" by simp hence th: "a=Mul i ?at \<and> n=i*?nt" using 8
    by (simp add: Let_def split_def)
  from abj 8 have th2: "(?I x (CN 0 ?nt ?at) = ?I x t) \<and> ?N ?at" by blast
  hence "?I x (Mul i t) = (real i) * ?I x (CN 0 ?nt ?at)" by simp
  also have "\<dots> = ?I x (CN 0 (i*?nt) (Mul i ?at))" by (simp add: distrib_left)
  finally show ?case using th th2 by simp
next
  case (9 t n a)
  let ?nt = "fst (zsplit0 t)"
  let ?at = "snd (zsplit0 t)"
  have abj: "zsplit0 t = (?nt,?at)" by simp hence th: "a= Floor ?at \<and> n=?nt" using 9
    by (simp add: Let_def split_def)
  from abj 9 have th2: "(?I x (CN 0 ?nt ?at) = ?I x t) \<and> ?N ?at" by blast
  hence na: "?N a" using th by simp
  have th': "(real ?nt)*(real x) = real (?nt * x)" by simp
  have "?I x (Floor t) = ?I x (Floor (CN 0 ?nt ?at))" using th2 by simp
  also have "\<dots> = real (floor ((real ?nt)* real(x) + ?I x ?at))" by simp
  also have "\<dots> = real (floor (?I x ?at + real (?nt* x)))" by (simp add: add_ac)
  also have "\<dots> = real (floor (?I x ?at) + (?nt* x))" 
    using floor_add[where x="?I x ?at" and a="?nt* x"] by simp 
  also have "\<dots> = real (?nt)*(real x) + real (floor (?I x ?at))" by (simp add: add_ac)
  finally have "?I x (Floor t) = ?I x (CN 0 n a)" using th by simp
  with na show ?case by simp
qed

consts
  iszlfm :: "fm \<Rightarrow> real list \<Rightarrow> bool"   (* Linearity test for fm *)
  zlfm :: "fm \<Rightarrow> fm"       (* Linearity transformation for fm *)
recdef iszlfm "measure size"
  "iszlfm (And p q) = (\<lambda> bs. iszlfm p bs \<and> iszlfm q bs)" 
  "iszlfm (Or p q) = (\<lambda> bs. iszlfm p bs \<and> iszlfm q bs)" 
  "iszlfm (Eq  (CN 0 c e)) = (\<lambda> bs. c>0 \<and> numbound0 e \<and> isint e bs)"
  "iszlfm (NEq (CN 0 c e)) = (\<lambda> bs. c>0 \<and> numbound0 e \<and> isint e bs)"
  "iszlfm (Lt  (CN 0 c e)) = (\<lambda> bs. c>0 \<and> numbound0 e \<and> isint e bs)"
  "iszlfm (Le  (CN 0 c e)) = (\<lambda> bs. c>0 \<and> numbound0 e \<and> isint e bs)"
  "iszlfm (Gt  (CN 0 c e)) = (\<lambda> bs. c>0 \<and> numbound0 e \<and> isint e bs)"
  "iszlfm (Ge  (CN 0 c e)) = (\<lambda> bs. c>0 \<and> numbound0 e \<and> isint e bs)"
  "iszlfm (Dvd i (CN 0 c e)) = 
                 (\<lambda> bs. c>0 \<and> i>0 \<and> numbound0 e \<and> isint e bs)"
  "iszlfm (NDvd i (CN 0 c e))= 
                 (\<lambda> bs. c>0 \<and> i>0 \<and> numbound0 e \<and> isint e bs)"
  "iszlfm p = (\<lambda> bs. isatom p \<and> (bound0 p))"

lemma zlin_qfree: "iszlfm p bs \<Longrightarrow> qfree p"
  by (induct p rule: iszlfm.induct) auto

lemma iszlfm_gen:
  assumes lp: "iszlfm p (x#bs)"
  shows "\<forall> y. iszlfm p (y#bs)"
proof
  fix y
  show "iszlfm p (y#bs)"
    using lp
  by(induct p rule: iszlfm.induct, simp_all add: numbound0_gen[rule_format, where x="x" and y="y"])
qed

lemma conj_zl[simp]: "iszlfm p bs \<Longrightarrow> iszlfm q bs \<Longrightarrow> iszlfm (conj p q) bs"
  using conj_def by (cases p,auto)
lemma disj_zl[simp]: "iszlfm p bs \<Longrightarrow> iszlfm q bs \<Longrightarrow> iszlfm (disj p q) bs"
  using disj_def by (cases p,auto)

recdef zlfm "measure fmsize"
  "zlfm (And p q) = conj (zlfm p) (zlfm q)"
  "zlfm (Or p q) = disj (zlfm p) (zlfm q)"
  "zlfm (Imp p q) = disj (zlfm (NOT p)) (zlfm q)"
  "zlfm (Iff p q) = disj (conj (zlfm p) (zlfm q)) (conj (zlfm (NOT p)) (zlfm (NOT q)))"
  "zlfm (Lt a) = (let (c,r) = zsplit0 a in 
     if c=0 then Lt r else 
     if c>0 then Or (Lt (CN 0 c (Neg (Floor (Neg r))))) (And (Eq (CN 0 c (Neg (Floor (Neg r))))) (Lt (Add (Floor (Neg r)) r))) 
     else Or (Gt (CN 0 (-c) (Floor(Neg r)))) (And (Eq(CN 0 (-c) (Floor(Neg r)))) (Lt (Add (Floor (Neg r)) r))))"
  "zlfm (Le a) = (let (c,r) = zsplit0 a in 
     if c=0 then Le r else 
     if c>0 then Or (Le (CN 0 c (Neg (Floor (Neg r))))) (And (Eq (CN 0 c (Neg (Floor (Neg r))))) (Lt (Add (Floor (Neg r)) r))) 
     else Or (Ge (CN 0 (-c) (Floor(Neg r)))) (And (Eq(CN 0 (-c) (Floor(Neg r)))) (Lt (Add (Floor (Neg r)) r))))"
  "zlfm (Gt a) = (let (c,r) = zsplit0 a in 
     if c=0 then Gt r else 
     if c>0 then Or (Gt (CN 0 c (Floor r))) (And (Eq (CN 0 c (Floor r))) (Lt (Sub (Floor r) r))) 
     else Or (Lt (CN 0 (-c) (Neg (Floor r)))) (And (Eq(CN 0 (-c) (Neg (Floor r)))) (Lt (Sub (Floor r) r))))"
  "zlfm (Ge a) = (let (c,r) = zsplit0 a in 
     if c=0 then Ge r else 
     if c>0 then Or (Ge (CN 0 c (Floor r))) (And (Eq (CN 0 c (Floor r))) (Lt (Sub (Floor r) r))) 
     else Or (Le (CN 0 (-c) (Neg (Floor r)))) (And (Eq(CN 0 (-c) (Neg (Floor r)))) (Lt (Sub (Floor r) r))))"
  "zlfm (Eq a) = (let (c,r) = zsplit0 a in 
              if c=0 then Eq r else 
      if c>0 then (And (Eq (CN 0 c (Neg (Floor (Neg r))))) (Eq (Add (Floor (Neg r)) r)))
      else (And (Eq (CN 0 (-c) (Floor (Neg r)))) (Eq (Add (Floor (Neg r)) r))))"
  "zlfm (NEq a) = (let (c,r) = zsplit0 a in 
              if c=0 then NEq r else 
      if c>0 then (Or (NEq (CN 0 c (Neg (Floor (Neg r))))) (NEq (Add (Floor (Neg r)) r)))
      else (Or (NEq (CN 0 (-c) (Floor (Neg r)))) (NEq (Add (Floor (Neg r)) r))))"
  "zlfm (Dvd i a) = (if i=0 then zlfm (Eq a) 
  else (let (c,r) = zsplit0 a in 
              if c=0 then Dvd (abs i) r else 
      if c>0 then And (Eq (Sub (Floor r) r)) (Dvd (abs i) (CN 0 c (Floor r))) 
      else And (Eq (Sub (Floor r) r)) (Dvd (abs i) (CN 0 (-c) (Neg (Floor r))))))"
  "zlfm (NDvd i a) = (if i=0 then zlfm (NEq a) 
  else (let (c,r) = zsplit0 a in 
              if c=0 then NDvd (abs i) r else 
      if c>0 then Or (NEq (Sub (Floor r) r)) (NDvd (abs i) (CN 0 c (Floor r))) 
      else Or (NEq (Sub (Floor r) r)) (NDvd (abs i) (CN 0 (-c) (Neg (Floor r))))))"
  "zlfm (NOT (And p q)) = disj (zlfm (NOT p)) (zlfm (NOT q))"
  "zlfm (NOT (Or p q)) = conj (zlfm (NOT p)) (zlfm (NOT q))"
  "zlfm (NOT (Imp p q)) = conj (zlfm p) (zlfm (NOT q))"
  "zlfm (NOT (Iff p q)) = disj (conj(zlfm p) (zlfm(NOT q))) (conj (zlfm(NOT p)) (zlfm q))"
  "zlfm (NOT (NOT p)) = zlfm p"
  "zlfm (NOT T) = F"
  "zlfm (NOT F) = T"
  "zlfm (NOT (Lt a)) = zlfm (Ge a)"
  "zlfm (NOT (Le a)) = zlfm (Gt a)"
  "zlfm (NOT (Gt a)) = zlfm (Le a)"
  "zlfm (NOT (Ge a)) = zlfm (Lt a)"
  "zlfm (NOT (Eq a)) = zlfm (NEq a)"
  "zlfm (NOT (NEq a)) = zlfm (Eq a)"
  "zlfm (NOT (Dvd i a)) = zlfm (NDvd i a)"
  "zlfm (NOT (NDvd i a)) = zlfm (Dvd i a)"
  "zlfm p = p" (hints simp add: fmsize_pos)

lemma split_int_less_real: 
  "(real (a::int) < b) = (a < floor b \<or> (a = floor b \<and> real (floor b) < b))"
proof( auto)
  assume alb: "real a < b" and agb: "\<not> a < floor b"
  from agb have "floor b \<le> a" by simp hence th: "b < real a + 1" by (simp only: floor_le_eq)
  from floor_eq[OF alb th] show "a= floor b" by simp 
next
  assume alb: "a < floor b"
  hence "real a < real (floor b)" by simp
  moreover have "real (floor b) \<le> b" by simp ultimately show  "real a < b" by arith 
qed

lemma split_int_less_real': 
  "(real (a::int) + b < 0) = (real a - real (floor(-b)) < 0 \<or> (real a - real (floor (-b)) = 0 \<and> real (floor (-b)) + b < 0))"
proof- 
  have "(real a + b <0) = (real a < -b)" by arith
  with split_int_less_real[where a="a" and b="-b"] show ?thesis by arith  
qed

lemma split_int_gt_real': 
  "(real (a::int) + b > 0) = (real a + real (floor b) > 0 \<or> (real a + real (floor b) = 0 \<and> real (floor b) - b < 0))"
proof- 
  have th: "(real a + b >0) = (real (-a) + (-b)< 0)" by arith
  show ?thesis using myless[of _ "real (floor b)"] 
    by (simp only:th split_int_less_real'[where a="-a" and b="-b"]) 
    (simp add: algebra_simps diff_minus[symmetric],arith)
qed

lemma split_int_le_real: 
  "(real (a::int) \<le> b) = (a \<le> floor b \<or> (a = floor b \<and> real (floor b) < b))"
proof( auto)
  assume alb: "real a \<le> b" and agb: "\<not> a \<le> floor b"
  from alb have "floor (real a) \<le> floor b " by (simp only: floor_mono) 
  hence "a \<le> floor b" by simp with agb show "False" by simp
next
  assume alb: "a \<le> floor b"
  hence "real a \<le> real (floor b)" by (simp only: floor_mono)
  also have "\<dots>\<le> b" by simp  finally show  "real a \<le> b" . 
qed

lemma split_int_le_real': 
  "(real (a::int) + b \<le> 0) = (real a - real (floor(-b)) \<le> 0 \<or> (real a - real (floor (-b)) = 0 \<and> real (floor (-b)) + b < 0))"
proof- 
  have "(real a + b \<le>0) = (real a \<le> -b)" by arith
  with split_int_le_real[where a="a" and b="-b"] show ?thesis by arith  
qed

lemma split_int_ge_real': 
  "(real (a::int) + b \<ge> 0) = (real a + real (floor b) \<ge> 0 \<or> (real a + real (floor b) = 0 \<and> real (floor b) - b < 0))"
proof- 
  have th: "(real a + b \<ge>0) = (real (-a) + (-b) \<le> 0)" by arith
  show ?thesis by (simp only: th split_int_le_real'[where a="-a" and b="-b"])
    (simp add: algebra_simps diff_minus[symmetric],arith)
qed

lemma split_int_eq_real: "(real (a::int) = b) = ( a = floor b \<and> b = real (floor b))" (is "?l = ?r")
by auto

lemma split_int_eq_real': "(real (a::int) + b = 0) = ( a - floor (-b) = 0 \<and> real (floor (-b)) + b = 0)" (is "?l = ?r")
proof-
  have "?l = (real a = -b)" by arith
  with split_int_eq_real[where a="a" and b="-b"] show ?thesis by simp arith
qed

lemma zlfm_I:
  assumes qfp: "qfree p"
  shows "(Ifm (real i #bs) (zlfm p) = Ifm (real i# bs) p) \<and> iszlfm (zlfm p) (real (i::int) #bs)"
  (is "(?I (?l p) = ?I p) \<and> ?L (?l p)")
using qfp
proof(induct p rule: zlfm.induct)
  case (5 a) 
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c,?r)" by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"] 
  have Ia:"Inum (real i # bs) a = Inum (real i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r" by auto 
  let ?N = "\<lambda> t. Inum (real i#bs) t"
  have "?c = 0 \<or> (?c >0 \<and> ?c\<noteq>0) \<or> (?c<0 \<and> ?c\<noteq>0)" by arith
  moreover
  {assume "?c=0" hence ?case using zsplit0_I[OF spl, where x="i" and bs="bs"] 
      by (cases "?r", simp_all add: Let_def split_def,case_tac "nat", simp_all)}
  moreover
  {assume cp: "?c > 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Lt a))" 
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Lt a) = (real (?c * i) + (?N ?r) < 0)" using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (?I (?l (Lt a)))" apply (simp only: split_int_less_real'[where a="?c*i" and b="?N ?r"]) by (simp add: Ia cp cnz Let_def split_def diff_minus)
    finally have ?case using l by simp}
  moreover
  {assume cn: "?c < 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Lt a))" 
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Lt a) = (real (?c * i) + (?N ?r) < 0)" using Ia by (simp add: Let_def split_def)
    also from cn cnz have "\<dots> = (?I (?l (Lt a)))" by (simp only: split_int_less_real'[where a="?c*i" and b="?N ?r"]) (simp add: Ia Let_def split_def diff_minus[symmetric] add_ac, arith)
    finally have ?case using l by simp}
  ultimately show ?case by blast
next
  case (6 a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c,?r)" by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"] 
  have Ia:"Inum (real i # bs) a = Inum (real i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r" by auto 
  let ?N = "\<lambda> t. Inum (real i#bs) t"
  have "?c = 0 \<or> (?c >0 \<and> ?c\<noteq>0) \<or> (?c<0 \<and> ?c\<noteq>0)" by arith
  moreover
  {assume "?c=0" hence ?case using zsplit0_I[OF spl, where x="i" and bs="bs"] 
      by (cases "?r", simp_all add: Let_def split_def, case_tac "nat",simp_all)}
  moreover
  {assume cp: "?c > 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Le a))" 
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Le a) = (real (?c * i) + (?N ?r) \<le> 0)" using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (?I (?l (Le a)))" by (simp only: split_int_le_real'[where a="?c*i" and b="?N ?r"]) (simp add: Ia cp cnz Let_def split_def diff_minus)
    finally have ?case using l by simp}
  moreover
  {assume cn: "?c < 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Le a))" 
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Le a) = (real (?c * i) + (?N ?r) \<le> 0)" using Ia by (simp add: Let_def split_def)
    also from cn cnz have "\<dots> = (?I (?l (Le a)))" by (simp only: split_int_le_real'[where a="?c*i" and b="?N ?r"]) (simp add: Ia Let_def split_def diff_minus[symmetric] add_ac ,arith)
    finally have ?case using l by simp}
  ultimately show ?case by blast
next
  case (7 a) 
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c,?r)" by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"] 
  have Ia:"Inum (real i # bs) a = Inum (real i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r" by auto 
  let ?N = "\<lambda> t. Inum (real i#bs) t"
  have "?c = 0 \<or> (?c >0 \<and> ?c\<noteq>0) \<or> (?c<0 \<and> ?c\<noteq>0)" by arith
  moreover
  {assume "?c=0" hence ?case using zsplit0_I[OF spl, where x="i" and bs="bs"] 
      by (cases "?r", simp_all add: Let_def split_def, case_tac "nat", simp_all)}
  moreover
  {assume cp: "?c > 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Gt a))" 
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Gt a) = (real (?c * i) + (?N ?r) > 0)" using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (?I (?l (Gt a)))" by (simp only: split_int_gt_real'[where a="?c*i" and b="?N ?r"]) (simp add: Ia cp cnz Let_def split_def diff_minus)
    finally have ?case using l by simp}
  moreover
  {assume cn: "?c < 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Gt a))" 
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Gt a) = (real (?c * i) + (?N ?r) > 0)" using Ia by (simp add: Let_def split_def)
    also from cn cnz have "\<dots> = (?I (?l (Gt a)))" by (simp only: split_int_gt_real'[where a="?c*i" and b="?N ?r"]) (simp add: Ia Let_def split_def diff_minus[symmetric] add_ac, arith)
    finally have ?case using l by simp}
  ultimately show ?case by blast
next
  case (8 a)
   let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c,?r)" by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"] 
  have Ia:"Inum (real i # bs) a = Inum (real i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r" by auto 
  let ?N = "\<lambda> t. Inum (real i#bs) t"
  have "?c = 0 \<or> (?c >0 \<and> ?c\<noteq>0) \<or> (?c<0 \<and> ?c\<noteq>0)" by arith
  moreover
  {assume "?c=0" hence ?case using zsplit0_I[OF spl, where x="i" and bs="bs"] 
      by (cases "?r", simp_all add: Let_def split_def, case_tac "nat", simp_all)}
  moreover
  {assume cp: "?c > 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Ge a))" 
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Ge a) = (real (?c * i) + (?N ?r) \<ge> 0)" using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (?I (?l (Ge a)))" by (simp only: split_int_ge_real'[where a="?c*i" and b="?N ?r"]) (simp add: Ia cp cnz Let_def split_def diff_minus)
    finally have ?case using l by simp}
  moreover
  {assume cn: "?c < 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Ge a))" 
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Ge a) = (real (?c * i) + (?N ?r) \<ge> 0)" using Ia by (simp add: Let_def split_def)
    also from cn cnz have "\<dots> = (?I (?l (Ge a)))" by (simp only: split_int_ge_real'[where a="?c*i" and b="?N ?r"]) (simp add: Ia Let_def split_def diff_minus[symmetric] add_ac, arith)
    finally have ?case using l by simp}
  ultimately show ?case by blast
next
  case (9 a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c,?r)" by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"] 
  have Ia:"Inum (real i # bs) a = Inum (real i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r" by auto 
  let ?N = "\<lambda> t. Inum (real i#bs) t"
  have "?c = 0 \<or> (?c >0 \<and> ?c\<noteq>0) \<or> (?c<0 \<and> ?c\<noteq>0)" by arith
  moreover
  {assume "?c=0" hence ?case using zsplit0_I[OF spl, where x="i" and bs="bs"] 
      by (cases "?r", simp_all add: Let_def split_def, case_tac "nat", simp_all)}
  moreover
  {assume cp: "?c > 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Eq a))" 
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Eq a) = (real (?c * i) + (?N ?r) = 0)" using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (?I (?l (Eq a)))" using cp cnz  by (simp only: split_int_eq_real'[where a="?c*i" and b="?N ?r"]) (simp add: Let_def split_def Ia real_of_int_mult[symmetric] del: real_of_int_mult)
    finally have ?case using l by simp}
  moreover
  {assume cn: "?c < 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Eq a))" 
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Eq a) = (real (?c * i) + (?N ?r) = 0)" using Ia by (simp add: Let_def split_def)
    also from cn cnz have "\<dots> = (?I (?l (Eq a)))" by (simp only: split_int_eq_real'[where a="?c*i" and b="?N ?r"]) (simp add: Let_def split_def Ia real_of_int_mult[symmetric] del: real_of_int_mult,arith)
    finally have ?case using l by simp}
  ultimately show ?case by blast
next
  case (10 a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c,?r)" by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"] 
  have Ia:"Inum (real i # bs) a = Inum (real i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r" by auto 
  let ?N = "\<lambda> t. Inum (real i#bs) t"
  have "?c = 0 \<or> (?c >0 \<and> ?c\<noteq>0) \<or> (?c<0 \<and> ?c\<noteq>0)" by arith
  moreover
  {assume "?c=0" hence ?case using zsplit0_I[OF spl, where x="i" and bs="bs"] 
      by (cases "?r", simp_all add: Let_def split_def, case_tac "nat", simp_all)}
  moreover
  {assume cp: "?c > 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (NEq a))" 
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (NEq a) = (real (?c * i) + (?N ?r) \<noteq> 0)" using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (?I (?l (NEq a)))" using cp cnz  by (simp only: split_int_eq_real'[where a="?c*i" and b="?N ?r"]) (simp add: Let_def split_def Ia real_of_int_mult[symmetric] del: real_of_int_mult)
    finally have ?case using l by simp}
  moreover
  {assume cn: "?c < 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (NEq a))" 
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (NEq a) = (real (?c * i) + (?N ?r) \<noteq> 0)" using Ia by (simp add: Let_def split_def)
    also from cn cnz have "\<dots> = (?I (?l (NEq a)))" by (simp only: split_int_eq_real'[where a="?c*i" and b="?N ?r"]) (simp add: Let_def split_def Ia real_of_int_mult[symmetric] del: real_of_int_mult,arith)
    finally have ?case using l by simp}
  ultimately show ?case by blast
next
  case (11 j a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c,?r)" by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"] 
  have Ia:"Inum (real i # bs) a = Inum (real i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r" by auto 
  let ?N = "\<lambda> t. Inum (real i#bs) t"
  have "j=0 \<or> (j\<noteq>0 \<and> ?c = 0) \<or> (j\<noteq>0 \<and> ?c >0 \<and> ?c\<noteq>0) \<or> (j\<noteq> 0 \<and> ?c<0 \<and> ?c\<noteq>0)" by arith
  moreover
  { assume j: "j=0" hence z: "zlfm (Dvd j a) = (zlfm (Eq a))" by (simp add: Let_def) 
    hence ?case using 11 j by (simp del: zlfm.simps add: rdvd_left_0_eq)}
  moreover
  {assume "?c=0" and "j\<noteq>0" hence ?case 
      using zsplit0_I[OF spl, where x="i" and bs="bs"] rdvd_abs1[where d="j"]
      by (cases "?r", simp_all add: Let_def split_def, case_tac "nat", simp_all)}
  moreover
  {assume cp: "?c > 0" and cnz: "?c\<noteq>0" and jnz: "j\<noteq>0" hence l: "?L (?l (Dvd j a))" 
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Dvd j a) = (real j rdvd (real (?c * i) + (?N ?r)))" 
      using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (real (abs j) rdvd real (?c*i) + (?N ?r))" 
      by (simp only: rdvd_abs1[where d="j" and t="real (?c*i) + ?N ?r", symmetric]) simp
    also have "\<dots> = ((abs j) dvd (floor ((?N ?r) + real (?c*i))) \<and> 
       (real (floor ((?N ?r) + real (?c*i))) = (real (?c*i) + (?N ?r))))" 
      by(simp only: int_rdvd_real[where i="abs j" and x="real (?c*i) + (?N ?r)"]) (simp only: add_ac)
    also have "\<dots> = (?I (?l (Dvd j a)))" using cp cnz jnz  
      by (simp add: Let_def split_def int_rdvd_iff[symmetric]  
        del: real_of_int_mult) (auto simp add: add_ac)
    finally have ?case using l jnz  by simp }
  moreover
  {assume cn: "?c < 0" and cnz: "?c\<noteq>0" and jnz: "j\<noteq>0" hence l: "?L (?l (Dvd j a))" 
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Dvd j a) = (real j rdvd (real (?c * i) + (?N ?r)))" 
      using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (real (abs j) rdvd real (?c*i) + (?N ?r))" 
      by (simp only: rdvd_abs1[where d="j" and t="real (?c*i) + ?N ?r", symmetric]) simp
    also have "\<dots> = ((abs j) dvd (floor ((?N ?r) + real (?c*i))) \<and> 
       (real (floor ((?N ?r) + real (?c*i))) = (real (?c*i) + (?N ?r))))" 
      by(simp only: int_rdvd_real[where i="abs j" and x="real (?c*i) + (?N ?r)"]) (simp only: add_ac)
    also have "\<dots> = (?I (?l (Dvd j a)))" using cn cnz jnz
      using rdvd_minus [where d="abs j" and t="real (?c*i + floor (?N ?r))", simplified, symmetric]
      by (simp add: Let_def split_def int_rdvd_iff[symmetric]  
        del: real_of_int_mult) (auto simp add: add_ac)
    finally have ?case using l jnz by blast }
  ultimately show ?case by blast
next
  case (12 j a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c,?r)" by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"] 
  have Ia:"Inum (real i # bs) a = Inum (real i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r" by auto 
  let ?N = "\<lambda> t. Inum (real i#bs) t"
  have "j=0 \<or> (j\<noteq>0 \<and> ?c = 0) \<or> (j\<noteq>0 \<and> ?c >0 \<and> ?c\<noteq>0) \<or> (j\<noteq> 0 \<and> ?c<0 \<and> ?c\<noteq>0)" by arith
  moreover
  {assume j: "j=0" hence z: "zlfm (NDvd j a) = (zlfm (NEq a))" by (simp add: Let_def) 
    hence ?case using 12 j by (simp del: zlfm.simps add: rdvd_left_0_eq)}
  moreover
  {assume "?c=0" and "j\<noteq>0" hence ?case 
      using zsplit0_I[OF spl, where x="i" and bs="bs"] rdvd_abs1[where d="j"]
      by (cases "?r", simp_all add: Let_def split_def, case_tac "nat", simp_all)}
  moreover
  {assume cp: "?c > 0" and cnz: "?c\<noteq>0" and jnz: "j\<noteq>0" hence l: "?L (?l (NDvd j a))" 
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (NDvd j a) = (\<not> (real j rdvd (real (?c * i) + (?N ?r))))" 
      using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (\<not> (real (abs j) rdvd real (?c*i) + (?N ?r)))" 
      by (simp only: rdvd_abs1[where d="j" and t="real (?c*i) + ?N ?r", symmetric]) simp
    also have "\<dots> = (\<not> ((abs j) dvd (floor ((?N ?r) + real (?c*i))) \<and> 
       (real (floor ((?N ?r) + real (?c*i))) = (real (?c*i) + (?N ?r)))))" 
      by(simp only: int_rdvd_real[where i="abs j" and x="real (?c*i) + (?N ?r)"]) (simp only: add_ac)
    also have "\<dots> = (?I (?l (NDvd j a)))" using cp cnz jnz  
      by (simp add: Let_def split_def int_rdvd_iff[symmetric]  
        del: real_of_int_mult) (auto simp add: add_ac)
    finally have ?case using l jnz  by simp }
  moreover
  {assume cn: "?c < 0" and cnz: "?c\<noteq>0" and jnz: "j\<noteq>0" hence l: "?L (?l (NDvd j a))" 
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (NDvd j a) = (\<not> (real j rdvd (real (?c * i) + (?N ?r))))" 
      using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (\<not> (real (abs j) rdvd real (?c*i) + (?N ?r)))" 
      by (simp only: rdvd_abs1[where d="j" and t="real (?c*i) + ?N ?r", symmetric]) simp
    also have "\<dots> = (\<not> ((abs j) dvd (floor ((?N ?r) + real (?c*i))) \<and> 
       (real (floor ((?N ?r) + real (?c*i))) = (real (?c*i) + (?N ?r)))))" 
      by(simp only: int_rdvd_real[where i="abs j" and x="real (?c*i) + (?N ?r)"]) (simp only: add_ac)
    also have "\<dots> = (?I (?l (NDvd j a)))" using cn cnz jnz
      using rdvd_minus [where d="abs j" and t="real (?c*i + floor (?N ?r))", simplified, symmetric]
      by (simp add: Let_def split_def int_rdvd_iff[symmetric]  
        del: real_of_int_mult) (auto simp add: add_ac)
    finally have ?case using l jnz by blast }
  ultimately show ?case by blast
qed auto

text{* plusinf : Virtual substitution of @{text "+\<infinity>"}
       minusinf: Virtual substitution of @{text "-\<infinity>"}
       @{text "\<delta>"} Compute lcm @{text "d| Dvd d  c*x+t \<in> p"}
       @{text "d\<delta>"} checks if a given l divides all the ds above*}

fun minusinf:: "fm \<Rightarrow> fm" where
  "minusinf (And p q) = conj (minusinf p) (minusinf q)" 
| "minusinf (Or p q) = disj (minusinf p) (minusinf q)" 
| "minusinf (Eq  (CN 0 c e)) = F"
| "minusinf (NEq (CN 0 c e)) = T"
| "minusinf (Lt  (CN 0 c e)) = T"
| "minusinf (Le  (CN 0 c e)) = T"
| "minusinf (Gt  (CN 0 c e)) = F"
| "minusinf (Ge  (CN 0 c e)) = F"
| "minusinf p = p"

lemma minusinf_qfree: "qfree p \<Longrightarrow> qfree (minusinf p)"
  by (induct p rule: minusinf.induct, auto)

fun plusinf:: "fm \<Rightarrow> fm" where
  "plusinf (And p q) = conj (plusinf p) (plusinf q)" 
| "plusinf (Or p q) = disj (plusinf p) (plusinf q)" 
| "plusinf (Eq  (CN 0 c e)) = F"
| "plusinf (NEq (CN 0 c e)) = T"
| "plusinf (Lt  (CN 0 c e)) = F"
| "plusinf (Le  (CN 0 c e)) = F"
| "plusinf (Gt  (CN 0 c e)) = T"
| "plusinf (Ge  (CN 0 c e)) = T"
| "plusinf p = p"

fun \<delta> :: "fm \<Rightarrow> int" where
  "\<delta> (And p q) = lcm (\<delta> p) (\<delta> q)" 
| "\<delta> (Or p q) = lcm (\<delta> p) (\<delta> q)" 
| "\<delta> (Dvd i (CN 0 c e)) = i"
| "\<delta> (NDvd i (CN 0 c e)) = i"
| "\<delta> p = 1"

fun d\<delta> :: "fm \<Rightarrow> int \<Rightarrow> bool" where
  "d\<delta> (And p q) = (\<lambda> d. d\<delta> p d \<and> d\<delta> q d)" 
| "d\<delta> (Or p q) = (\<lambda> d. d\<delta> p d \<and> d\<delta> q d)" 
| "d\<delta> (Dvd i (CN 0 c e)) = (\<lambda> d. i dvd d)"
| "d\<delta> (NDvd i (CN 0 c e)) = (\<lambda> d. i dvd d)"
| "d\<delta> p = (\<lambda> d. True)"

lemma delta_mono: 
  assumes lin: "iszlfm p bs"
  and d: "d dvd d'"
  and ad: "d\<delta> p d"
  shows "d\<delta> p d'"
  using lin ad d
proof(induct p rule: iszlfm.induct)
  case (9 i c e)  thus ?case using d
    by (simp add: dvd_trans[of "i" "d" "d'"])
next
  case (10 i c e) thus ?case using d
    by (simp add: dvd_trans[of "i" "d" "d'"])
qed simp_all

lemma \<delta> : assumes lin:"iszlfm p bs"
  shows "d\<delta> p (\<delta> p) \<and> \<delta> p >0"
using lin
proof (induct p rule: iszlfm.induct)
  case (1 p q) 
  let ?d = "\<delta> (And p q)"
  from 1 lcm_pos_int have dp: "?d >0" by simp
  have d1: "\<delta> p dvd \<delta> (And p q)" using 1 by simp 
  hence th: "d\<delta> p ?d" 
    using delta_mono 1 by (simp only: iszlfm.simps) blast
  have "\<delta> q dvd \<delta> (And p q)" using 1 by simp 
  hence th': "d\<delta> q ?d" using delta_mono 1 by (simp only: iszlfm.simps) blast
  from th th' dp show ?case by simp 
next
  case (2 p q)  
  let ?d = "\<delta> (And p q)"
  from 2 lcm_pos_int have dp: "?d >0" by simp
  have "\<delta> p dvd \<delta> (And p q)" using 2 by simp
  hence th: "d\<delta> p ?d" using delta_mono 2 by (simp only: iszlfm.simps) blast
  have "\<delta> q dvd \<delta> (And p q)" using 2 by simp
  hence th': "d\<delta> q ?d" using delta_mono 2 by (simp only: iszlfm.simps) blast
  from th th' dp show ?case by simp
qed simp_all


lemma minusinf_inf:
  assumes linp: "iszlfm p (a # bs)"
  shows "\<exists> (z::int). \<forall> x < z. Ifm ((real x)#bs) (minusinf p) = Ifm ((real x)#bs) p"
  (is "?P p" is "\<exists> (z::int). \<forall> x < z. ?I x (?M p) = ?I x p")
using linp
proof (induct p rule: minusinf.induct)
  case (1 f g)
  then have "?P f" by simp
  then obtain z1 where z1_def: "\<forall> x < z1. ?I x (?M f) = ?I x f" by blast
  with 1 have "?P g" by simp
  then obtain z2 where z2_def: "\<forall> x < z2. ?I x (?M g) = ?I x g" by blast
  let ?z = "min z1 z2"
  from z1_def z2_def have "\<forall> x < ?z. ?I x (?M (And f g)) = ?I x (And f g)" by simp
  thus ?case by blast
next
  case (2 f g)
  then have "?P f" by simp
  then obtain z1 where z1_def: "\<forall> x < z1. ?I x (?M f) = ?I x f" by blast
  with 2 have "?P g" by simp
  then obtain z2 where z2_def: "\<forall> x < z2. ?I x (?M g) = ?I x g" by blast
  let ?z = "min z1 z2"
  from z1_def z2_def have "\<forall> x < ?z. ?I x (?M (Or f g)) = ?I x (Or f g)" by simp
  thus ?case by blast
next
  case (3 c e) 
  then have "c > 0" by simp
  hence rcpos: "real c > 0" by simp
  from 3 have nbe: "numbound0 e" by simp
  fix y
  have "\<forall> x < (floor (- (Inum (y#bs) e) / (real c))). ?I x (?M (Eq (CN 0 c e))) = ?I x (Eq (CN 0 c e))"
  proof (simp add: less_floor_eq , rule allI, rule impI) 
    fix x
    assume A: "real x + (1\<Colon>real) \<le> - (Inum (y # bs) e / real c)"
    hence th1:"real x < - (Inum (y # bs) e / real c)" by simp
    with rcpos  have "(real c)*(real  x) < (real c)*(- (Inum (y # bs) e / real c))"
      by (simp only: mult_strict_left_mono [OF th1 rcpos])
    hence "real c * real x + Inum (y # bs) e \<noteq> 0"using rcpos  by simp
    thus "real c * real x + Inum (real x # bs) e \<noteq> 0" 
      using numbound0_I[OF nbe, where b="y" and bs="bs" and b'="real x"]  by simp
  qed
  thus ?case by blast
next
  case (4 c e) 
  then have "c > 0" by simp hence rcpos: "real c > 0" by simp
  from 4 have nbe: "numbound0 e" by simp
  fix y
  have "\<forall> x < (floor (- (Inum (y#bs) e) / (real c))). ?I x (?M (NEq (CN 0 c e))) = ?I x (NEq (CN 0 c e))"
  proof (simp add: less_floor_eq , rule allI, rule impI) 
    fix x
    assume A: "real x + (1\<Colon>real) \<le> - (Inum (y # bs) e / real c)"
    hence th1:"real x < - (Inum (y # bs) e / real c)" by simp
    with rcpos  have "(real c)*(real  x) < (real c)*(- (Inum (y # bs) e / real c))"
      by (simp only: mult_strict_left_mono [OF th1 rcpos])
    hence "real c * real x + Inum (y # bs) e \<noteq> 0"using rcpos  by simp
    thus "real c * real x + Inum (real x # bs) e \<noteq> 0" 
      using numbound0_I[OF nbe, where b="y" and bs="bs" and b'="real x"]  by simp
  qed
  thus ?case by blast
next
  case (5 c e) 
  then have "c > 0" by simp hence rcpos: "real c > 0" by simp
  from 5 have nbe: "numbound0 e" by simp
  fix y
  have "\<forall> x < (floor (- (Inum (y#bs) e) / (real c))). ?I x (?M (Lt (CN 0 c e))) = ?I x (Lt (CN 0 c e))"
  proof (simp add: less_floor_eq , rule allI, rule impI) 
    fix x
    assume A: "real x + (1\<Colon>real) \<le> - (Inum (y # bs) e / real c)"
    hence th1:"real x < - (Inum (y # bs) e / real c)" by simp
    with rcpos  have "(real c)*(real  x) < (real c)*(- (Inum (y # bs) e / real c))"
      by (simp only: mult_strict_left_mono [OF th1 rcpos])
    thus "real c * real x + Inum (real x # bs) e < 0" 
      using numbound0_I[OF nbe, where b="y" and bs="bs" and b'="real x"] rcpos by simp
  qed
  thus ?case by blast
next
  case (6 c e) 
  then have "c > 0" by simp hence rcpos: "real c > 0" by simp
  from 6 have nbe: "numbound0 e" by simp
  fix y
  have "\<forall> x < (floor (- (Inum (y#bs) e) / (real c))). ?I x (?M (Le (CN 0 c e))) = ?I x (Le (CN 0 c e))"
  proof (simp add: less_floor_eq , rule allI, rule impI) 
    fix x
    assume A: "real x + (1\<Colon>real) \<le> - (Inum (y # bs) e / real c)"
    hence th1:"real x < - (Inum (y # bs) e / real c)" by simp
    with rcpos  have "(real c)*(real  x) < (real c)*(- (Inum (y # bs) e / real c))"
      by (simp only: mult_strict_left_mono [OF th1 rcpos])
    thus "real c * real x + Inum (real x # bs) e \<le> 0" 
      using numbound0_I[OF nbe, where b="y" and bs="bs" and b'="real x"] rcpos by simp
  qed
  thus ?case by blast
next
  case (7 c e) 
  then have "c > 0" by simp hence rcpos: "real c > 0" by simp
  from 7 have nbe: "numbound0 e" by simp
  fix y
  have "\<forall> x < (floor (- (Inum (y#bs) e) / (real c))). ?I x (?M (Gt (CN 0 c e))) = ?I x (Gt (CN 0 c e))"
  proof (simp add: less_floor_eq , rule allI, rule impI) 
    fix x
    assume A: "real x + (1\<Colon>real) \<le> - (Inum (y # bs) e / real c)"
    hence th1:"real x < - (Inum (y # bs) e / real c)" by simp
    with rcpos  have "(real c)*(real  x) < (real c)*(- (Inum (y # bs) e / real c))"
      by (simp only: mult_strict_left_mono [OF th1 rcpos])
    thus "\<not> (real c * real x + Inum (real x # bs) e>0)" 
      using numbound0_I[OF nbe, where b="y" and bs="bs" and b'="real x"] rcpos by simp
  qed
  thus ?case by blast
next
  case (8 c e) 
  then have "c > 0" by simp hence rcpos: "real c > 0" by simp
  from 8 have nbe: "numbound0 e" by simp
  fix y
  have "\<forall> x < (floor (- (Inum (y#bs) e) / (real c))). ?I x (?M (Ge (CN 0 c e))) = ?I x (Ge (CN 0 c e))"
  proof (simp add: less_floor_eq , rule allI, rule impI) 
    fix x
    assume A: "real x + (1\<Colon>real) \<le> - (Inum (y # bs) e / real c)"
    hence th1:"real x < - (Inum (y # bs) e / real c)" by simp
    with rcpos  have "(real c)*(real  x) < (real c)*(- (Inum (y # bs) e / real c))"
      by (simp only: mult_strict_left_mono [OF th1 rcpos])
    thus "\<not> real c * real x + Inum (real x # bs) e \<ge> 0" 
      using numbound0_I[OF nbe, where b="y" and bs="bs" and b'="real x"] rcpos by simp
  qed
  thus ?case by blast
qed simp_all

lemma minusinf_repeats:
  assumes d: "d\<delta> p d" and linp: "iszlfm p (a # bs)"
  shows "Ifm ((real(x - k*d))#bs) (minusinf p) = Ifm (real x #bs) (minusinf p)"
using linp d
proof(induct p rule: iszlfm.induct) 
  case (9 i c e) hence nbe: "numbound0 e"  and id: "i dvd d" by simp+
    hence "\<exists> k. d=i*k" by (simp add: dvd_def)
    then obtain "di" where di_def: "d=i*di" by blast
    show ?case 
    proof(simp add: numbound0_I[OF nbe,where bs="bs" and b="real x - real k * real d" and b'="real x"] right_diff_distrib, rule iffI)
      assume 
        "real i rdvd real c * real x - real c * (real k * real d) + Inum (real x # bs) e"
      (is "?ri rdvd ?rc*?rx - ?rc*(?rk*?rd) + ?I x e" is "?ri rdvd ?rt")
      hence "\<exists> (l::int). ?rt = ?ri * (real l)" by (simp add: rdvd_def)
      hence "\<exists> (l::int). ?rc*?rx+ ?I x e = ?ri*(real l)+?rc*(?rk * (real i) * (real di))" 
        by (simp add: algebra_simps di_def)
      hence "\<exists> (l::int). ?rc*?rx+ ?I x e = ?ri*(real (l + c*k*di))"
        by (simp add: algebra_simps)
      hence "\<exists> (l::int). ?rc*?rx+ ?I x e = ?ri* (real l)" by blast
      thus "real i rdvd real c * real x + Inum (real x # bs) e" using rdvd_def by simp
    next
      assume 
        "real i rdvd real c * real x + Inum (real x # bs) e" (is "?ri rdvd ?rc*?rx+?e")
      hence "\<exists> (l::int). ?rc*?rx+?e = ?ri * (real l)" by (simp add: rdvd_def)
      hence "\<exists> (l::int). ?rc*?rx - real c * (real k * real d) +?e = ?ri * (real l) - real c * (real k * real d)" by simp
      hence "\<exists> (l::int). ?rc*?rx - real c * (real k * real d) +?e = ?ri * (real l) - real c * (real k * real i * real di)" by (simp add: di_def)
      hence "\<exists> (l::int). ?rc*?rx - real c * (real k * real d) +?e = ?ri * (real (l - c*k*di))" by (simp add: algebra_simps)
      hence "\<exists> (l::int). ?rc*?rx - real c * (real k * real d) +?e = ?ri * (real l)"
        by blast
      thus "real i rdvd real c * real x - real c * (real k * real d) + Inum (real x # bs) e" using rdvd_def by simp
    qed
next
  case (10 i c e) hence nbe: "numbound0 e"  and id: "i dvd d" by simp+
    hence "\<exists> k. d=i*k" by (simp add: dvd_def)
    then obtain "di" where di_def: "d=i*di" by blast
    show ?case 
    proof(simp add: numbound0_I[OF nbe,where bs="bs" and b="real x - real k * real d" and b'="real x"] right_diff_distrib, rule iffI)
      assume 
        "real i rdvd real c * real x - real c * (real k * real d) + Inum (real x # bs) e"
      (is "?ri rdvd ?rc*?rx - ?rc*(?rk*?rd) + ?I x e" is "?ri rdvd ?rt")
      hence "\<exists> (l::int). ?rt = ?ri * (real l)" by (simp add: rdvd_def)
      hence "\<exists> (l::int). ?rc*?rx+ ?I x e = ?ri*(real l)+?rc*(?rk * (real i) * (real di))" 
        by (simp add: algebra_simps di_def)
      hence "\<exists> (l::int). ?rc*?rx+ ?I x e = ?ri*(real (l + c*k*di))"
        by (simp add: algebra_simps)
      hence "\<exists> (l::int). ?rc*?rx+ ?I x e = ?ri* (real l)" by blast
      thus "real i rdvd real c * real x + Inum (real x # bs) e" using rdvd_def by simp
    next
      assume 
        "real i rdvd real c * real x + Inum (real x # bs) e" (is "?ri rdvd ?rc*?rx+?e")
      hence "\<exists> (l::int). ?rc*?rx+?e = ?ri * (real l)" by (simp add: rdvd_def)
      hence "\<exists> (l::int). ?rc*?rx - real c * (real k * real d) +?e = ?ri * (real l) - real c * (real k * real d)" by simp
      hence "\<exists> (l::int). ?rc*?rx - real c * (real k * real d) +?e = ?ri * (real l) - real c * (real k * real i * real di)" by (simp add: di_def)
      hence "\<exists> (l::int). ?rc*?rx - real c * (real k * real d) +?e = ?ri * (real (l - c*k*di))" by (simp add: algebra_simps)
      hence "\<exists> (l::int). ?rc*?rx - real c * (real k * real d) +?e = ?ri * (real l)"
        by blast
      thus "real i rdvd real c * real x - real c * (real k * real d) + Inum (real x # bs) e" using rdvd_def by simp
    qed
qed (auto simp add: numbound0_I[where bs="bs" and b="real(x - k*d)" and b'="real x"] simp del: real_of_int_mult real_of_int_diff)

lemma minusinf_ex:
  assumes lin: "iszlfm p (real (a::int) #bs)"
  and exmi: "\<exists> (x::int). Ifm (real x#bs) (minusinf p)" (is "\<exists> x. ?P1 x")
  shows "\<exists> (x::int). Ifm (real x#bs) p" (is "\<exists> x. ?P x")
proof-
  let ?d = "\<delta> p"
  from \<delta> [OF lin] have dpos: "?d >0" by simp
  from \<delta> [OF lin] have alld: "d\<delta> p ?d" by simp
  from minusinf_repeats[OF alld lin] have th1:"\<forall> x k. ?P1 x = ?P1 (x - (k * ?d))" by simp
  from minusinf_inf[OF lin] have th2:"\<exists> z. \<forall> x. x<z \<longrightarrow> (?P x = ?P1 x)" by blast
  from minusinfinity [OF dpos th1 th2] exmi show ?thesis by blast
qed

lemma minusinf_bex:
  assumes lin: "iszlfm p (real (a::int) #bs)"
  shows "(\<exists> (x::int). Ifm (real x#bs) (minusinf p)) = 
         (\<exists> (x::int)\<in> {1..\<delta> p}. Ifm (real x#bs) (minusinf p))"
  (is "(\<exists> x. ?P x) = _")
proof-
  let ?d = "\<delta> p"
  from \<delta> [OF lin] have dpos: "?d >0" by simp
  from \<delta> [OF lin] have alld: "d\<delta> p ?d" by simp
  from minusinf_repeats[OF alld lin] have th1:"\<forall> x k. ?P x = ?P (x - (k * ?d))" by simp
  from periodic_finite_ex[OF dpos th1] show ?thesis by blast
qed

lemma dvd1_eq1: "x >0 \<Longrightarrow> (x::int) dvd 1 = (x = 1)" by auto

consts 
  a\<beta> :: "fm \<Rightarrow> int \<Rightarrow> fm" (* adjusts the coeffitients of a formula *)
  d\<beta> :: "fm \<Rightarrow> int \<Rightarrow> bool" (* tests if all coeffs c of c divide a given l*)
  \<zeta>  :: "fm \<Rightarrow> int" (* computes the lcm of all coefficients of x*)
  \<beta> :: "fm \<Rightarrow> num list"
  \<alpha> :: "fm \<Rightarrow> num list"

recdef a\<beta> "measure size"
  "a\<beta> (And p q) = (\<lambda> k. And (a\<beta> p k) (a\<beta> q k))" 
  "a\<beta> (Or p q) = (\<lambda> k. Or (a\<beta> p k) (a\<beta> q k))" 
  "a\<beta> (Eq  (CN 0 c e)) = (\<lambda> k. Eq (CN 0 1 (Mul (k div c) e)))"
  "a\<beta> (NEq (CN 0 c e)) = (\<lambda> k. NEq (CN 0 1 (Mul (k div c) e)))"
  "a\<beta> (Lt  (CN 0 c e)) = (\<lambda> k. Lt (CN 0 1 (Mul (k div c) e)))"
  "a\<beta> (Le  (CN 0 c e)) = (\<lambda> k. Le (CN 0 1 (Mul (k div c) e)))"
  "a\<beta> (Gt  (CN 0 c e)) = (\<lambda> k. Gt (CN 0 1 (Mul (k div c) e)))"
  "a\<beta> (Ge  (CN 0 c e)) = (\<lambda> k. Ge (CN 0 1 (Mul (k div c) e)))"
  "a\<beta> (Dvd i (CN 0 c e)) =(\<lambda> k. Dvd ((k div c)*i) (CN 0 1 (Mul (k div c) e)))"
  "a\<beta> (NDvd i (CN 0 c e))=(\<lambda> k. NDvd ((k div c)*i) (CN 0 1 (Mul (k div c) e)))"
  "a\<beta> p = (\<lambda> k. p)"

recdef d\<beta> "measure size"
  "d\<beta> (And p q) = (\<lambda> k. (d\<beta> p k) \<and> (d\<beta> q k))" 
  "d\<beta> (Or p q) = (\<lambda> k. (d\<beta> p k) \<and> (d\<beta> q k))" 
  "d\<beta> (Eq  (CN 0 c e)) = (\<lambda> k. c dvd k)"
  "d\<beta> (NEq (CN 0 c e)) = (\<lambda> k. c dvd k)"
  "d\<beta> (Lt  (CN 0 c e)) = (\<lambda> k. c dvd k)"
  "d\<beta> (Le  (CN 0 c e)) = (\<lambda> k. c dvd k)"
  "d\<beta> (Gt  (CN 0 c e)) = (\<lambda> k. c dvd k)"
  "d\<beta> (Ge  (CN 0 c e)) = (\<lambda> k. c dvd k)"
  "d\<beta> (Dvd i (CN 0 c e)) =(\<lambda> k. c dvd k)"
  "d\<beta> (NDvd i (CN 0 c e))=(\<lambda> k. c dvd k)"
  "d\<beta> p = (\<lambda> k. True)"

recdef \<zeta> "measure size"
  "\<zeta> (And p q) = lcm (\<zeta> p) (\<zeta> q)" 
  "\<zeta> (Or p q) = lcm (\<zeta> p) (\<zeta> q)" 
  "\<zeta> (Eq  (CN 0 c e)) = c"
  "\<zeta> (NEq (CN 0 c e)) = c"
  "\<zeta> (Lt  (CN 0 c e)) = c"
  "\<zeta> (Le  (CN 0 c e)) = c"
  "\<zeta> (Gt  (CN 0 c e)) = c"
  "\<zeta> (Ge  (CN 0 c e)) = c"
  "\<zeta> (Dvd i (CN 0 c e)) = c"
  "\<zeta> (NDvd i (CN 0 c e))= c"
  "\<zeta> p = 1"

recdef \<beta> "measure size"
  "\<beta> (And p q) = (\<beta> p @ \<beta> q)" 
  "\<beta> (Or p q) = (\<beta> p @ \<beta> q)" 
  "\<beta> (Eq  (CN 0 c e)) = [Sub (C -1) e]"
  "\<beta> (NEq (CN 0 c e)) = [Neg e]"
  "\<beta> (Lt  (CN 0 c e)) = []"
  "\<beta> (Le  (CN 0 c e)) = []"
  "\<beta> (Gt  (CN 0 c e)) = [Neg e]"
  "\<beta> (Ge  (CN 0 c e)) = [Sub (C -1) e]"
  "\<beta> p = []"

recdef \<alpha> "measure size"
  "\<alpha> (And p q) = (\<alpha> p @ \<alpha> q)" 
  "\<alpha> (Or p q) = (\<alpha> p @ \<alpha> q)" 
  "\<alpha> (Eq  (CN 0 c e)) = [Add (C -1) e]"
  "\<alpha> (NEq (CN 0 c e)) = [e]"
  "\<alpha> (Lt  (CN 0 c e)) = [e]"
  "\<alpha> (Le  (CN 0 c e)) = [Add (C -1) e]"
  "\<alpha> (Gt  (CN 0 c e)) = []"
  "\<alpha> (Ge  (CN 0 c e)) = []"
  "\<alpha> p = []"
consts mirror :: "fm \<Rightarrow> fm"
recdef mirror "measure size"
  "mirror (And p q) = And (mirror p) (mirror q)" 
  "mirror (Or p q) = Or (mirror p) (mirror q)" 
  "mirror (Eq  (CN 0 c e)) = Eq (CN 0 c (Neg e))"
  "mirror (NEq (CN 0 c e)) = NEq (CN 0 c (Neg e))"
  "mirror (Lt  (CN 0 c e)) = Gt (CN 0 c (Neg e))"
  "mirror (Le  (CN 0 c e)) = Ge (CN 0 c (Neg e))"
  "mirror (Gt  (CN 0 c e)) = Lt (CN 0 c (Neg e))"
  "mirror (Ge  (CN 0 c e)) = Le (CN 0 c (Neg e))"
  "mirror (Dvd i (CN 0 c e)) = Dvd i (CN 0 c (Neg e))"
  "mirror (NDvd i (CN 0 c e)) = NDvd i (CN 0 c (Neg e))"
  "mirror p = p"

lemma mirror\<alpha>\<beta>:
  assumes lp: "iszlfm p (a#bs)"
  shows "(Inum (real (i::int)#bs)) ` set (\<alpha> p) = (Inum (real i#bs)) ` set (\<beta> (mirror p))"
using lp
by (induct p rule: mirror.induct, auto)

lemma mirror: 
  assumes lp: "iszlfm p (a#bs)"
  shows "Ifm (real (x::int)#bs) (mirror p) = Ifm (real (- x)#bs) p" 
using lp
proof(induct p rule: iszlfm.induct)
  case (9 j c e)
  have th: "(real j rdvd real c * real x - Inum (real x # bs) e) =
       (real j rdvd - (real c * real x - Inum (real x # bs) e))"
    by (simp only: rdvd_minus[symmetric])
  from 9 th show ?case
    by (simp add: algebra_simps
      numbound0_I[where bs="bs" and b'="real x" and b="- real x"])
next
  case (10 j c e)
  have th: "(real j rdvd real c * real x - Inum (real x # bs) e) =
       (real j rdvd - (real c * real x - Inum (real x # bs) e))"
    by (simp only: rdvd_minus[symmetric])
  from 10 th show  ?case
    by (simp add: algebra_simps
      numbound0_I[where bs="bs" and b'="real x" and b="- real x"])
qed (auto simp add: numbound0_I[where bs="bs" and b="real x" and b'="- real x"])

lemma mirror_l: "iszlfm p (a#bs) \<Longrightarrow> iszlfm (mirror p) (a#bs)"
by (induct p rule: mirror.induct, auto simp add: isint_neg)

lemma mirror_d\<beta>: "iszlfm p (a#bs) \<and> d\<beta> p 1 
  \<Longrightarrow> iszlfm (mirror p) (a#bs) \<and> d\<beta> (mirror p) 1"
by (induct p rule: mirror.induct, auto simp add: isint_neg)

lemma mirror_\<delta>: "iszlfm p (a#bs) \<Longrightarrow> \<delta> (mirror p) = \<delta> p"
by (induct p rule: mirror.induct,auto)


lemma mirror_ex: 
  assumes lp: "iszlfm p (real (i::int)#bs)"
  shows "(\<exists> (x::int). Ifm (real x#bs) (mirror p)) = (\<exists> (x::int). Ifm (real x#bs) p)"
  (is "(\<exists> x. ?I x ?mp) = (\<exists> x. ?I x p)")
proof(auto)
  fix x assume "?I x ?mp" hence "?I (- x) p" using mirror[OF lp] by blast
  thus "\<exists> x. ?I x p" by blast
next
  fix x assume "?I x p" hence "?I (- x) ?mp" 
    using mirror[OF lp, where x="- x", symmetric] by auto
  thus "\<exists> x. ?I x ?mp" by blast
qed

lemma \<beta>_numbound0: assumes lp: "iszlfm p bs"
  shows "\<forall> b\<in> set (\<beta> p). numbound0 b"
  using lp by (induct p rule: \<beta>.induct,auto)

lemma d\<beta>_mono: 
  assumes linp: "iszlfm p (a #bs)"
  and dr: "d\<beta> p l"
  and d: "l dvd l'"
  shows "d\<beta> p l'"
using dr linp dvd_trans[of _ "l" "l'", simplified d]
by (induct p rule: iszlfm.induct) simp_all

lemma \<alpha>_l: assumes lp: "iszlfm p (a#bs)"
  shows "\<forall> b\<in> set (\<alpha> p). numbound0 b \<and> isint b (a#bs)"
using lp
by(induct p rule: \<alpha>.induct, auto simp add: isint_add isint_c)

lemma \<zeta>: 
  assumes linp: "iszlfm p (a #bs)"
  shows "\<zeta> p > 0 \<and> d\<beta> p (\<zeta> p)"
using linp
proof(induct p rule: iszlfm.induct)
  case (1 p q)
  then  have dl1: "\<zeta> p dvd lcm (\<zeta> p) (\<zeta> q)" by simp
  from 1 have dl2: "\<zeta> q dvd lcm (\<zeta> p) (\<zeta> q)" by simp
  from 1 d\<beta>_mono[where p = "p" and l="\<zeta> p" and l'="lcm (\<zeta> p) (\<zeta> q)"] 
    d\<beta>_mono[where p = "q" and l="\<zeta> q" and l'="lcm (\<zeta> p) (\<zeta> q)"] 
    dl1 dl2 show ?case by (auto simp add: lcm_pos_int)
next
  case (2 p q)
  then have dl1: "\<zeta> p dvd lcm (\<zeta> p) (\<zeta> q)" by simp
  from 2 have dl2: "\<zeta> q dvd lcm (\<zeta> p) (\<zeta> q)" by simp
  from 2 d\<beta>_mono[where p = "p" and l="\<zeta> p" and l'="lcm (\<zeta> p) (\<zeta> q)"] 
    d\<beta>_mono[where p = "q" and l="\<zeta> q" and l'="lcm (\<zeta> p) (\<zeta> q)"] 
    dl1 dl2 show ?case by (auto simp add: lcm_pos_int)
qed (auto simp add: lcm_pos_int)

lemma a\<beta>: assumes linp: "iszlfm p (a #bs)" and d: "d\<beta> p l" and lp: "l > 0"
  shows "iszlfm (a\<beta> p l) (a #bs) \<and> d\<beta> (a\<beta> p l) 1 \<and> (Ifm (real (l * x) #bs) (a\<beta> p l) = Ifm ((real x)#bs) p)"
using linp d
proof (induct p rule: iszlfm.induct)
  case (5 c e) hence cp: "c>0" and be: "numbound0 e" and ei:"isint e (a#bs)" and d': "c dvd l" by simp+
    from lp cp have clel: "c\<le>l" by (simp add: zdvd_imp_le [OF d' lp])
    from cp have cnz: "c \<noteq> 0" by simp
    have "c div c\<le> l div c"
      by (simp add: zdiv_mono1[OF clel cp])
    then have ldcp:"0 < l div c" 
      by (simp add: div_self[OF cnz])
    have "c * (l div c) = c* (l div c) + l mod c" using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
    hence cl:"c * (l div c) =l" using zmod_zdiv_equality[where a="l" and b="c", symmetric] 
      by simp
    hence "(real l * real x + real (l div c) * Inum (real x # bs) e < (0\<Colon>real)) =
          (real (c * (l div c)) * real x + real (l div c) * Inum (real x # bs) e < 0)"
      by simp
    also have "\<dots> = (real (l div c) * (real c * real x + Inum (real x # bs) e) < (real (l div c)) * 0)" by (simp add: algebra_simps)
    also have "\<dots> = (real c * real x + Inum (real x # bs) e < 0)"
    using mult_less_0_iff [where a="real (l div c)" and b="real c * real x + Inum (real x # bs) e"] ldcp by simp
  finally show ?case using numbound0_I[OF be,where b="real (l * x)" and b'="real x" and bs="bs"] be  isint_Mul[OF ei] by simp
next
  case (6 c e) hence cp: "c>0" and be: "numbound0 e" and ei:"isint e (a#bs)" and d': "c dvd l" by simp+
    from lp cp have clel: "c\<le>l" by (simp add: zdvd_imp_le [OF d' lp])
    from cp have cnz: "c \<noteq> 0" by simp
    have "c div c\<le> l div c"
      by (simp add: zdiv_mono1[OF clel cp])
    then have ldcp:"0 < l div c" 
      by (simp add: div_self[OF cnz])
    have "c * (l div c) = c* (l div c) + l mod c" using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
    hence cl:"c * (l div c) =l" using zmod_zdiv_equality[where a="l" and b="c", symmetric] 
      by simp
    hence "(real l * real x + real (l div c) * Inum (real x # bs) e \<le> (0\<Colon>real)) =
          (real (c * (l div c)) * real x + real (l div c) * Inum (real x # bs) e \<le> 0)"
      by simp
    also have "\<dots> = (real (l div c) * (real c * real x + Inum (real x # bs) e) \<le> (real (l div c)) * 0)" by (simp add: algebra_simps)
    also have "\<dots> = (real c * real x + Inum (real x # bs) e \<le> 0)"
    using mult_le_0_iff [where a="real (l div c)" and b="real c * real x + Inum (real x # bs) e"] ldcp by simp
  finally show ?case using numbound0_I[OF be,where b="real (l * x)" and b'="real x" and bs="bs"]  be  isint_Mul[OF ei] by simp
next
  case (7 c e) hence cp: "c>0" and be: "numbound0 e" and ei:"isint e (a#bs)" and d': "c dvd l" by simp+
    from lp cp have clel: "c\<le>l" by (simp add: zdvd_imp_le [OF d' lp])
    from cp have cnz: "c \<noteq> 0" by simp
    have "c div c\<le> l div c"
      by (simp add: zdiv_mono1[OF clel cp])
    then have ldcp:"0 < l div c" 
      by (simp add: div_self[OF cnz])
    have "c * (l div c) = c* (l div c) + l mod c" using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
    hence cl:"c * (l div c) =l" using zmod_zdiv_equality[where a="l" and b="c", symmetric] 
      by simp
    hence "(real l * real x + real (l div c) * Inum (real x # bs) e > (0\<Colon>real)) =
          (real (c * (l div c)) * real x + real (l div c) * Inum (real x # bs) e > 0)"
      by simp
    also have "\<dots> = (real (l div c) * (real c * real x + Inum (real x # bs) e) > (real (l div c)) * 0)" by (simp add: algebra_simps)
    also have "\<dots> = (real c * real x + Inum (real x # bs) e > 0)"
    using zero_less_mult_iff [where a="real (l div c)" and b="real c * real x + Inum (real x # bs) e"] ldcp by simp
  finally show ?case using numbound0_I[OF be,where b="real (l * x)" and b'="real x" and bs="bs"]  be  isint_Mul[OF ei] by simp
next
  case (8 c e) hence cp: "c>0" and be: "numbound0 e"  and ei:"isint e (a#bs)" and d': "c dvd l" by simp+
    from lp cp have clel: "c\<le>l" by (simp add: zdvd_imp_le [OF d' lp])
    from cp have cnz: "c \<noteq> 0" by simp
    have "c div c\<le> l div c"
      by (simp add: zdiv_mono1[OF clel cp])
    then have ldcp:"0 < l div c" 
      by (simp add: div_self[OF cnz])
    have "c * (l div c) = c* (l div c) + l mod c" using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
    hence cl:"c * (l div c) =l" using zmod_zdiv_equality[where a="l" and b="c", symmetric] 
      by simp
    hence "(real l * real x + real (l div c) * Inum (real x # bs) e \<ge> (0\<Colon>real)) =
          (real (c * (l div c)) * real x + real (l div c) * Inum (real x # bs) e \<ge> 0)"
      by simp
    also have "\<dots> = (real (l div c) * (real c * real x + Inum (real x # bs) e) \<ge> (real (l div c)) * 0)" by (simp add: algebra_simps)
    also have "\<dots> = (real c * real x + Inum (real x # bs) e \<ge> 0)"
    using zero_le_mult_iff [where a="real (l div c)" and b="real c * real x + Inum (real x # bs) e"] ldcp by simp
  finally show ?case using numbound0_I[OF be,where b="real (l * x)" and b'="real x" and bs="bs"]  be  isint_Mul[OF ei] by simp
next
  case (3 c e) hence cp: "c>0" and be: "numbound0 e" and ei:"isint e (a#bs)" and d': "c dvd l" by simp+
    from lp cp have clel: "c\<le>l" by (simp add: zdvd_imp_le [OF d' lp])
    from cp have cnz: "c \<noteq> 0" by simp
    have "c div c\<le> l div c"
      by (simp add: zdiv_mono1[OF clel cp])
    then have ldcp:"0 < l div c" 
      by (simp add: div_self[OF cnz])
    have "c * (l div c) = c* (l div c) + l mod c" using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
    hence cl:"c * (l div c) =l" using zmod_zdiv_equality[where a="l" and b="c", symmetric] 
      by simp
    hence "(real l * real x + real (l div c) * Inum (real x # bs) e = (0\<Colon>real)) =
          (real (c * (l div c)) * real x + real (l div c) * Inum (real x # bs) e = 0)"
      by simp
    also have "\<dots> = (real (l div c) * (real c * real x + Inum (real x # bs) e) = (real (l div c)) * 0)" by (simp add: algebra_simps)
    also have "\<dots> = (real c * real x + Inum (real x # bs) e = 0)"
    using mult_eq_0_iff [where a="real (l div c)" and b="real c * real x + Inum (real x # bs) e"] ldcp by simp
  finally show ?case using numbound0_I[OF be,where b="real (l * x)" and b'="real x" and bs="bs"]  be  isint_Mul[OF ei] by simp
next
  case (4 c e) hence cp: "c>0" and be: "numbound0 e" and ei:"isint e (a#bs)" and d': "c dvd l" by simp+
    from lp cp have clel: "c\<le>l" by (simp add: zdvd_imp_le [OF d' lp])
    from cp have cnz: "c \<noteq> 0" by simp
    have "c div c\<le> l div c"
      by (simp add: zdiv_mono1[OF clel cp])
    then have ldcp:"0 < l div c" 
      by (simp add: div_self[OF cnz])
    have "c * (l div c) = c* (l div c) + l mod c" using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
    hence cl:"c * (l div c) =l" using zmod_zdiv_equality[where a="l" and b="c", symmetric] 
      by simp
    hence "(real l * real x + real (l div c) * Inum (real x # bs) e \<noteq> (0\<Colon>real)) =
          (real (c * (l div c)) * real x + real (l div c) * Inum (real x # bs) e \<noteq> 0)"
      by simp
    also have "\<dots> = (real (l div c) * (real c * real x + Inum (real x # bs) e) \<noteq> (real (l div c)) * 0)" by (simp add: algebra_simps)
    also have "\<dots> = (real c * real x + Inum (real x # bs) e \<noteq> 0)"
    using zero_le_mult_iff [where a="real (l div c)" and b="real c * real x + Inum (real x # bs) e"] ldcp by simp
  finally show ?case using numbound0_I[OF be,where b="real (l * x)" and b'="real x" and bs="bs"]  be  isint_Mul[OF ei] by simp
next
  case (9 j c e) hence cp: "c>0" and be: "numbound0 e" and ei:"isint e (a#bs)" and jp: "j > 0" and d': "c dvd l" by simp+
    from lp cp have clel: "c\<le>l" by (simp add: zdvd_imp_le [OF d' lp])
    from cp have cnz: "c \<noteq> 0" by simp
    have "c div c\<le> l div c"
      by (simp add: zdiv_mono1[OF clel cp])
    then have ldcp:"0 < l div c" 
      by (simp add: div_self[OF cnz])
    have "c * (l div c) = c* (l div c) + l mod c" using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
    hence cl:"c * (l div c) =l" using zmod_zdiv_equality[where a="l" and b="c", symmetric] 
      by simp
    hence "(\<exists> (k::int). real l * real x + real (l div c) * Inum (real x # bs) e = (real (l div c) * real j) * real k) = (\<exists> (k::int). real (c * (l div c)) * real x + real (l div c) * Inum (real x # bs) e = (real (l div c) * real j) * real k)"  by simp
    also have "\<dots> = (\<exists> (k::int). real (l div c) * (real c * real x + Inum (real x # bs) e - real j * real k) = real (l div c)*0)" by (simp add: algebra_simps)
    also fix k have "\<dots> = (\<exists> (k::int). real c * real x + Inum (real x # bs) e - real j * real k = 0)"
    using zero_le_mult_iff [where a="real (l div c)" and b="real c * real x + Inum (real x # bs) e - real j * real k"] ldcp by simp
  also have "\<dots> = (\<exists> (k::int). real c * real x + Inum (real x # bs) e = real j * real k)" by simp
  finally show ?case using numbound0_I[OF be,where b="real (l * x)" and b'="real x" and bs="bs"] rdvd_def  be  isint_Mul[OF ei] mult_strict_mono[OF ldcp jp ldcp ] by simp 
next
  case (10 j c e) hence cp: "c>0" and be: "numbound0 e" and ei:"isint e (a#bs)" and jp: "j > 0" and d': "c dvd l" by simp+
    from lp cp have clel: "c\<le>l" by (simp add: zdvd_imp_le [OF d' lp])
    from cp have cnz: "c \<noteq> 0" by simp
    have "c div c\<le> l div c"
      by (simp add: zdiv_mono1[OF clel cp])
    then have ldcp:"0 < l div c" 
      by (simp add: div_self[OF cnz])
    have "c * (l div c) = c* (l div c) + l mod c" using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
    hence cl:"c * (l div c) =l" using zmod_zdiv_equality[where a="l" and b="c", symmetric] 
      by simp
    hence "(\<exists> (k::int). real l * real x + real (l div c) * Inum (real x # bs) e = (real (l div c) * real j) * real k) = (\<exists> (k::int). real (c * (l div c)) * real x + real (l div c) * Inum (real x # bs) e = (real (l div c) * real j) * real k)"  by simp
    also have "\<dots> = (\<exists> (k::int). real (l div c) * (real c * real x + Inum (real x # bs) e - real j * real k) = real (l div c)*0)" by (simp add: algebra_simps)
    also fix k have "\<dots> = (\<exists> (k::int). real c * real x + Inum (real x # bs) e - real j * real k = 0)"
    using zero_le_mult_iff [where a="real (l div c)" and b="real c * real x + Inum (real x # bs) e - real j * real k"] ldcp by simp
  also have "\<dots> = (\<exists> (k::int). real c * real x + Inum (real x # bs) e = real j * real k)" by simp
  finally show ?case using numbound0_I[OF be,where b="real (l * x)" and b'="real x" and bs="bs"] rdvd_def  be  isint_Mul[OF ei]  mult_strict_mono[OF ldcp jp ldcp ] by simp
qed (simp_all add: numbound0_I[where bs="bs" and b="real (l * x)" and b'="real x"] isint_Mul del: real_of_int_mult)

lemma a\<beta>_ex: assumes linp: "iszlfm p (a#bs)" and d: "d\<beta> p l" and lp: "l>0"
  shows "(\<exists> x. l dvd x \<and> Ifm (real x #bs) (a\<beta> p l)) = (\<exists> (x::int). Ifm (real x#bs) p)"
  (is "(\<exists> x. l dvd x \<and> ?P x) = (\<exists> x. ?P' x)")
proof-
  have "(\<exists> x. l dvd x \<and> ?P x) = (\<exists> (x::int). ?P (l*x))"
    using unity_coeff_ex[where l="l" and P="?P", simplified] by simp
  also have "\<dots> = (\<exists> (x::int). ?P' x)" using a\<beta>[OF linp d lp] by simp
  finally show ?thesis  . 
qed

lemma \<beta>:
  assumes lp: "iszlfm p (a#bs)"
  and u: "d\<beta> p 1"
  and d: "d\<delta> p d"
  and dp: "d > 0"
  and nob: "\<not>(\<exists>(j::int) \<in> {1 .. d}. \<exists> b\<in> (Inum (a#bs)) ` set(\<beta> p). real x = b + real j)"
  and p: "Ifm (real x#bs) p" (is "?P x")
  shows "?P (x - d)"
using lp u d dp nob p
proof(induct p rule: iszlfm.induct)
  case (5 c e) hence c1: "c=1" and  bn:"numbound0 e" using dvd1_eq1[where x="c"] by simp_all
  with dp p c1 numbound0_I[OF bn,where b="real (x-d)" and b'="real x" and bs="bs"] 5
  show ?case by (simp del: real_of_int_minus)
next
  case (6 c e)  hence c1: "c=1" and  bn:"numbound0 e" using dvd1_eq1[where x="c"] by simp_all
  with dp p c1 numbound0_I[OF bn,where b="real (x-d)" and b'="real x" and bs="bs"] 6
  show ?case by (simp del: real_of_int_minus)
next
  case (7 c e) hence p: "Ifm (real x #bs) (Gt (CN 0 c e))" and c1: "c=1"
    and bn:"numbound0 e" and ie1:"isint e (a#bs)" using dvd1_eq1[where x="c"] by simp_all
  let ?e = "Inum (real x # bs) e"
  from ie1 have ie: "real (floor ?e) = ?e" using isint_iff[where n="e" and bs="a#bs"]
      numbound0_I[OF bn,where b="a" and b'="real x" and bs="bs"]
    by (simp add: isint_iff)
    {assume "real (x-d) +?e > 0" hence ?case using c1 
      numbound0_I[OF bn,where b="real (x-d)" and b'="real x" and bs="bs"]
        by (simp del: real_of_int_minus)}
    moreover
    {assume H: "\<not> real (x-d) + ?e > 0" 
      let ?v="Neg e"
      have vb: "?v \<in> set (\<beta> (Gt (CN 0 c e)))" by simp
      from 7(5)[simplified simp_thms Inum.simps \<beta>.simps set.simps bex_simps numbound0_I[OF bn,where b="a" and b'="real x" and bs="bs"]] 
      have nob: "\<not> (\<exists> j\<in> {1 ..d}. real x =  - ?e + real j)" by auto 
      from H p have "real x + ?e > 0 \<and> real x + ?e \<le> real d" by (simp add: c1)
      hence "real (x + floor ?e) > real (0::int) \<and> real (x + floor ?e) \<le> real d"
        using ie by simp
      hence "x + floor ?e \<ge> 1 \<and> x + floor ?e \<le> d"  by simp
      hence "\<exists> (j::int) \<in> {1 .. d}. j = x + floor ?e" by simp
      hence "\<exists> (j::int) \<in> {1 .. d}. real x = real (- floor ?e + j)" 
        by (simp only: real_of_int_inject) (simp add: algebra_simps)
      hence "\<exists> (j::int) \<in> {1 .. d}. real x = - ?e + real j" 
        by (simp add: ie[simplified isint_iff])
      with nob have ?case by auto}
    ultimately show ?case by blast
next
  case (8 c e) hence p: "Ifm (real x #bs) (Ge (CN 0 c e))" and c1: "c=1" and bn:"numbound0 e" 
    and ie1:"isint e (a #bs)" using dvd1_eq1[where x="c"] by simp+
    let ?e = "Inum (real x # bs) e"
    from ie1 have ie: "real (floor ?e) = ?e" using numbound0_I[OF bn,where b="real x" and b'="a" and bs="bs"] isint_iff[where n="e" and bs="(real x)#bs"]
      by (simp add: isint_iff)
    {assume "real (x-d) +?e \<ge> 0" hence ?case using  c1 
      numbound0_I[OF bn,where b="real (x-d)" and b'="real x" and bs="bs"]
        by (simp del: real_of_int_minus)}
    moreover
    {assume H: "\<not> real (x-d) + ?e \<ge> 0" 
      let ?v="Sub (C -1) e"
      have vb: "?v \<in> set (\<beta> (Ge (CN 0 c e)))" by simp
      from 8(5)[simplified simp_thms Inum.simps \<beta>.simps set.simps bex_simps numbound0_I[OF bn,where b="a" and b'="real x" and bs="bs"]] 
      have nob: "\<not> (\<exists> j\<in> {1 ..d}. real x =  - ?e - 1 + real j)" by auto 
      from H p have "real x + ?e \<ge> 0 \<and> real x + ?e < real d" by (simp add: c1)
      hence "real (x + floor ?e) \<ge> real (0::int) \<and> real (x + floor ?e) < real d"
        using ie by simp
      hence "x + floor ?e +1 \<ge> 1 \<and> x + floor ?e + 1 \<le> d"  by simp
      hence "\<exists> (j::int) \<in> {1 .. d}. j = x + floor ?e + 1" by simp
      hence "\<exists> (j::int) \<in> {1 .. d}. x= - floor ?e - 1 + j" by (simp add: algebra_simps)
      hence "\<exists> (j::int) \<in> {1 .. d}. real x= real (- floor ?e - 1 + j)" 
        by (simp only: real_of_int_inject)
      hence "\<exists> (j::int) \<in> {1 .. d}. real x= - ?e - 1 + real j" 
        by (simp add: ie[simplified isint_iff])
      with nob have ?case by simp }
    ultimately show ?case by blast
next
  case (3 c e) hence p: "Ifm (real x #bs) (Eq (CN 0 c e))" (is "?p x") and c1: "c=1" 
    and bn:"numbound0 e" and ie1: "isint e (a #bs)" using dvd1_eq1[where x="c"] by simp+
    let ?e = "Inum (real x # bs) e"
    let ?v="(Sub (C -1) e)"
    have vb: "?v \<in> set (\<beta> (Eq (CN 0 c e)))" by simp
    from p have "real x= - ?e" by (simp add: c1) with 3(5) show ?case using dp
      by simp (erule ballE[where x="1"],
        simp_all add:algebra_simps numbound0_I[OF bn,where b="real x"and b'="a"and bs="bs"])
next
  case (4 c e)hence p: "Ifm (real x #bs) (NEq (CN 0 c e))" (is "?p x") and c1: "c=1" 
    and bn:"numbound0 e" and ie1: "isint e (a #bs)" using dvd1_eq1[where x="c"] by simp+
    let ?e = "Inum (real x # bs) e"
    let ?v="Neg e"
    have vb: "?v \<in> set (\<beta> (NEq (CN 0 c e)))" by simp
    {assume "real x - real d + Inum ((real (x -d)) # bs) e \<noteq> 0" 
      hence ?case by (simp add: c1)}
    moreover
    {assume H: "real x - real d + Inum ((real (x -d)) # bs) e = 0"
      hence "real x = - Inum ((real (x -d)) # bs) e + real d" by simp
      hence "real x = - Inum (a # bs) e + real d"
        by (simp add: numbound0_I[OF bn,where b="real x - real d"and b'="a"and bs="bs"])
       with 4(5) have ?case using dp by simp}
  ultimately show ?case by blast
next 
  case (9 j c e) hence p: "Ifm (real x #bs) (Dvd j (CN 0 c e))" (is "?p x") and c1: "c=1" 
    and bn:"numbound0 e" using dvd1_eq1[where x="c"] by simp+
  let ?e = "Inum (real x # bs) e"
  from 9 have "isint e (a #bs)"  by simp 
  hence ie: "real (floor ?e) = ?e" using isint_iff[where n="e" and bs="(real x)#bs"] numbound0_I[OF bn,where b="real x" and b'="a" and bs="bs"]
    by (simp add: isint_iff)
  from 9 have id: "j dvd d" by simp
  from c1 ie[symmetric] have "?p x = (real j rdvd real (x+ floor ?e))" by simp
  also have "\<dots> = (j dvd x + floor ?e)" 
    using int_rdvd_real[where i="j" and x="real (x+ floor ?e)"] by simp
  also have "\<dots> = (j dvd x - d + floor ?e)" 
    using dvd_period[OF id, where x="x" and c="-1" and t="floor ?e"] by simp
  also have "\<dots> = (real j rdvd real (x - d + floor ?e))" 
    using int_rdvd_real[where i="j" and x="real (x-d + floor ?e)",symmetric, simplified]
      ie by simp
  also have "\<dots> = (real j rdvd real x - real d + ?e)" 
    using ie by simp
  finally show ?case 
    using numbound0_I[OF bn,where b="real (x-d)" and b'="real x" and bs="bs"] c1 p by simp
next
  case (10 j c e) hence p: "Ifm (real x #bs) (NDvd j (CN 0 c e))" (is "?p x") and c1: "c=1" and bn:"numbound0 e" using dvd1_eq1[where x="c"] by simp+
  let ?e = "Inum (real x # bs) e"
  from 10 have "isint e (a#bs)"  by simp 
  hence ie: "real (floor ?e) = ?e" using numbound0_I[OF bn,where b="real x" and b'="a" and bs="bs"] isint_iff[where n="e" and bs="(real x)#bs"]
    by (simp add: isint_iff)
  from 10 have id: "j dvd d" by simp
  from c1 ie[symmetric] have "?p x = (\<not> real j rdvd real (x+ floor ?e))" by simp
  also have "\<dots> = (\<not> j dvd x + floor ?e)" 
    using int_rdvd_real[where i="j" and x="real (x+ floor ?e)"] by simp
  also have "\<dots> = (\<not> j dvd x - d + floor ?e)" 
    using dvd_period[OF id, where x="x" and c="-1" and t="floor ?e"] by simp
  also have "\<dots> = (\<not> real j rdvd real (x - d + floor ?e))" 
    using int_rdvd_real[where i="j" and x="real (x-d + floor ?e)",symmetric, simplified]
      ie by simp
  also have "\<dots> = (\<not> real j rdvd real x - real d + ?e)" 
    using ie by simp
  finally show ?case
    using numbound0_I[OF bn,where b="real (x-d)" and b'="real x" and bs="bs"] c1 p by simp
qed (auto simp add: numbound0_I[where bs="bs" and b="real (x - d)" and b'="real x"]
  simp del: real_of_int_diff)

lemma \<beta>':   
  assumes lp: "iszlfm p (a #bs)"
  and u: "d\<beta> p 1"
  and d: "d\<delta> p d"
  and dp: "d > 0"
  shows "\<forall> x. \<not>(\<exists>(j::int) \<in> {1 .. d}. \<exists> b\<in> set(\<beta> p). Ifm ((Inum (a#bs) b + real j) #bs) p) \<longrightarrow> Ifm (real x#bs) p \<longrightarrow> Ifm (real (x - d)#bs) p" (is "\<forall> x. ?b \<longrightarrow> ?P x \<longrightarrow> ?P (x - d)")
proof(clarify)
  fix x 
  assume nb:"?b" and px: "?P x" 
  hence nb2: "\<not>(\<exists>(j::int) \<in> {1 .. d}. \<exists> b\<in> (Inum (a#bs)) ` set(\<beta> p). real x = b + real j)"
    by auto
  from  \<beta>[OF lp u d dp nb2 px] show "?P (x -d )" .
qed

lemma \<beta>_int: assumes lp: "iszlfm p bs"
  shows "\<forall> b\<in> set (\<beta> p). isint b bs"
using lp by (induct p rule: iszlfm.induct) (auto simp add: isint_neg isint_sub)

lemma cpmi_eq: "0 < D \<Longrightarrow> (EX z::int. ALL x. x < z --> (P x = P1 x))
==> ALL x.~(EX (j::int) : {1..D}. EX (b::int) : B. P(b+j)) --> P (x) --> P (x - D) 
==> (ALL (x::int). ALL (k::int). ((P1 x)= (P1 (x-k*D))))
==> (EX (x::int). P(x)) = ((EX (j::int) : {1..D} . (P1(j))) | (EX (j::int) : {1..D}. EX (b::int) : B. P (b+j)))"
apply(rule iffI)
prefer 2
apply(drule minusinfinity)
apply assumption+
apply(fastforce)
apply clarsimp
apply(subgoal_tac "!!k. 0<=k \<Longrightarrow> !x. P x \<longrightarrow> P (x - k*D)")
apply(frule_tac x = x and z=z in decr_lemma)
apply(subgoal_tac "P1(x - (\<bar>x - z\<bar> + 1) * D)")
prefer 2
apply(subgoal_tac "0 <= (\<bar>x - z\<bar> + 1)")
prefer 2 apply arith
 apply fastforce
apply(drule (1)  periodic_finite_ex)
apply blast
apply(blast dest:decr_mult_lemma)
done


theorem cp_thm:
  assumes lp: "iszlfm p (a #bs)"
  and u: "d\<beta> p 1"
  and d: "d\<delta> p d"
  and dp: "d > 0"
  shows "(\<exists> (x::int). Ifm (real x #bs) p) = (\<exists> j\<in> {1.. d}. Ifm (real j #bs) (minusinf p) \<or> (\<exists> b \<in> set (\<beta> p). Ifm ((Inum (a#bs) b + real j) #bs) p))"
  (is "(\<exists> (x::int). ?P (real x)) = (\<exists> j\<in> ?D. ?M j \<or> (\<exists> b\<in> ?B. ?P (?I b + real j)))")
proof-
  from minusinf_inf[OF lp] 
  have th: "\<exists>(z::int). \<forall>x<z. ?P (real x) = ?M x" by blast
  let ?B' = "{floor (?I b) | b. b\<in> ?B}"
  from \<beta>_int[OF lp] isint_iff[where bs="a # bs"] have B: "\<forall> b\<in> ?B. real (floor (?I b)) = ?I b" by simp
  from B[rule_format] 
  have "(\<exists>j\<in>?D. \<exists>b\<in> ?B. ?P (?I b + real j)) = (\<exists>j\<in>?D. \<exists>b\<in> ?B. ?P (real (floor (?I b)) + real j))" 
    by simp
  also have "\<dots> = (\<exists>j\<in>?D. \<exists>b\<in> ?B. ?P (real (floor (?I b) + j)))" by simp
  also have"\<dots> = (\<exists> j \<in> ?D. \<exists> b \<in> ?B'. ?P (real (b + j)))"  by blast
  finally have BB': 
    "(\<exists>j\<in>?D. \<exists>b\<in> ?B. ?P (?I b + real j)) = (\<exists> j \<in> ?D. \<exists> b \<in> ?B'. ?P (real (b + j)))" 
    by blast 
  hence th2: "\<forall> x. \<not> (\<exists> j \<in> ?D. \<exists> b \<in> ?B'. ?P (real (b + j))) \<longrightarrow> ?P (real x) \<longrightarrow> ?P (real (x - d))" using \<beta>'[OF lp u d dp] by blast
  from minusinf_repeats[OF d lp]
  have th3: "\<forall> x k. ?M x = ?M (x-k*d)" by simp
  from cpmi_eq[OF dp th th2 th3] BB' show ?thesis by blast
qed

    (* Reddy and Loveland *)


consts 
  \<rho> :: "fm \<Rightarrow> (num \<times> int) list" (* Compute the Reddy and Loveland Bset*)
  \<sigma>\<rho>:: "fm \<Rightarrow> num \<times> int \<Rightarrow> fm" (* Performs the modified substitution of Reddy and Loveland*)
  \<alpha>\<rho> :: "fm \<Rightarrow> (num\<times>int) list"
  a\<rho> :: "fm \<Rightarrow> int \<Rightarrow> fm"
recdef \<rho> "measure size"
  "\<rho> (And p q) = (\<rho> p @ \<rho> q)" 
  "\<rho> (Or p q) = (\<rho> p @ \<rho> q)" 
  "\<rho> (Eq  (CN 0 c e)) = [(Sub (C -1) e,c)]"
  "\<rho> (NEq (CN 0 c e)) = [(Neg e,c)]"
  "\<rho> (Lt  (CN 0 c e)) = []"
  "\<rho> (Le  (CN 0 c e)) = []"
  "\<rho> (Gt  (CN 0 c e)) = [(Neg e, c)]"
  "\<rho> (Ge  (CN 0 c e)) = [(Sub (C (-1)) e, c)]"
  "\<rho> p = []"

recdef \<sigma>\<rho> "measure size"
  "\<sigma>\<rho> (And p q) = (\<lambda> (t,k). And (\<sigma>\<rho> p (t,k)) (\<sigma>\<rho> q (t,k)))" 
  "\<sigma>\<rho> (Or p q) = (\<lambda> (t,k). Or (\<sigma>\<rho> p (t,k)) (\<sigma>\<rho> q (t,k)))" 
  "\<sigma>\<rho> (Eq  (CN 0 c e)) = (\<lambda> (t,k). if k dvd c then (Eq (Add (Mul (c div k) t) e)) 
                                            else (Eq (Add (Mul c t) (Mul k e))))"
  "\<sigma>\<rho> (NEq (CN 0 c e)) = (\<lambda> (t,k). if k dvd c then (NEq (Add (Mul (c div k) t) e)) 
                                            else (NEq (Add (Mul c t) (Mul k e))))"
  "\<sigma>\<rho> (Lt  (CN 0 c e)) = (\<lambda> (t,k). if k dvd c then (Lt (Add (Mul (c div k) t) e)) 
                                            else (Lt (Add (Mul c t) (Mul k e))))"
  "\<sigma>\<rho> (Le  (CN 0 c e)) = (\<lambda> (t,k). if k dvd c then (Le (Add (Mul (c div k) t) e)) 
                                            else (Le (Add (Mul c t) (Mul k e))))"
  "\<sigma>\<rho> (Gt  (CN 0 c e)) = (\<lambda> (t,k). if k dvd c then (Gt (Add (Mul (c div k) t) e)) 
                                            else (Gt (Add (Mul c t) (Mul k e))))"
  "\<sigma>\<rho> (Ge  (CN 0 c e)) = (\<lambda> (t,k). if k dvd c then (Ge (Add (Mul (c div k) t) e)) 
                                            else (Ge (Add (Mul c t) (Mul k e))))"
  "\<sigma>\<rho> (Dvd i (CN 0 c e)) =(\<lambda> (t,k). if k dvd c then (Dvd i (Add (Mul (c div k) t) e)) 
                                            else (Dvd (i*k) (Add (Mul c t) (Mul k e))))"
  "\<sigma>\<rho> (NDvd i (CN 0 c e))=(\<lambda> (t,k). if k dvd c then (NDvd i (Add (Mul (c div k) t) e)) 
                                            else (NDvd (i*k) (Add (Mul c t) (Mul k e))))"
  "\<sigma>\<rho> p = (\<lambda> (t,k). p)"

recdef \<alpha>\<rho> "measure size"
  "\<alpha>\<rho> (And p q) = (\<alpha>\<rho> p @ \<alpha>\<rho> q)" 
  "\<alpha>\<rho> (Or p q) = (\<alpha>\<rho> p @ \<alpha>\<rho> q)" 
  "\<alpha>\<rho> (Eq  (CN 0 c e)) = [(Add (C -1) e,c)]"
  "\<alpha>\<rho> (NEq (CN 0 c e)) = [(e,c)]"
  "\<alpha>\<rho> (Lt  (CN 0 c e)) = [(e,c)]"
  "\<alpha>\<rho> (Le  (CN 0 c e)) = [(Add (C -1) e,c)]"
  "\<alpha>\<rho> p = []"

    (* Simulates normal substituion by modifying the formula see correctness theorem *)

definition \<sigma> :: "fm \<Rightarrow> int \<Rightarrow> num \<Rightarrow> fm" where
  "\<sigma> p k t \<equiv> And (Dvd k t) (\<sigma>\<rho> p (t,k))"

lemma \<sigma>\<rho>:
  assumes linp: "iszlfm p (real (x::int)#bs)"
  and kpos: "real k > 0"
  and tnb: "numbound0 t"
  and tint: "isint t (real x#bs)"
  and kdt: "k dvd floor (Inum (b'#bs) t)"
  shows "Ifm (real x#bs) (\<sigma>\<rho> p (t,k)) = 
  (Ifm ((real ((floor (Inum (b'#bs) t)) div k))#bs) p)" 
  (is "?I (real x) (?s p) = (?I (real ((floor (?N b' t)) div k)) p)" is "_ = (?I ?tk p)")
using linp kpos tnb
proof(induct p rule: \<sigma>\<rho>.induct)
  case (3 c e) 
  from 3 have cp: "c > 0" and nb: "numbound0 e" by auto
  { assume kdc: "k dvd c" 
    from tint have ti: "real (floor (?N (real x) t)) = ?N (real x) t" using isint_def by simp
    from kdc have ?case using real_of_int_div[OF kdc] real_of_int_div[OF kdt]
      numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
      numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"] by (simp add: ti) } 
  moreover 
  { assume *: "\<not> k dvd c"
    from kpos have knz': "real k \<noteq> 0" by simp
    from tint have ti: "real (floor (?N (real x) t)) = ?N (real x) t"
      using isint_def by simp
    from assms * have "?I (real x) (?s (Eq (CN 0 c e))) = ((real c * (?N (real x) t / real k) + ?N (real x) e)* real k = 0)"
      using real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"]
      by (simp add: ti algebra_simps)
      also have "\<dots> = (?I ?tk (Eq (CN 0 c e)))"
        using nonzero_eq_divide_eq[OF knz',
            where a="real c * (?N (real x) t / real k) + ?N (real x) e" and b="0", symmetric]
          real_of_int_div[OF kdt] numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
          numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"]
        by (simp add: ti)
      finally have ?case . }
    ultimately show ?case by blast 
next
  case (4 c e)  
  then have cp: "c > 0" and nb: "numbound0 e" by auto
  { assume kdc: "k dvd c" 
    from tint have ti: "real (floor (?N (real x) t)) = ?N (real x) t" using isint_def by simp
    from kdc have  ?case using real_of_int_div[OF kdc] real_of_int_div[OF kdt]
      numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
      numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"] by (simp add: ti) } 
  moreover 
  { assume *: "\<not> k dvd c"
    from kpos have knz': "real k \<noteq> 0" by simp
    from tint have ti: "real (floor (?N (real x) t)) = ?N (real x) t" using isint_def by simp
    from assms * have "?I (real x) (?s (NEq (CN 0 c e))) = ((real c * (?N (real x) t / real k) + ?N (real x) e)* real k \<noteq> 0)"
      using real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"]
      by (simp add: ti algebra_simps)
    also have "\<dots> = (?I ?tk (NEq (CN 0 c e)))"
      using nonzero_eq_divide_eq[OF knz',
          where a="real c * (?N (real x) t / real k) + ?N (real x) e" and b="0", symmetric]
        real_of_int_div[OF kdt] numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"]
      by (simp add: ti)
    finally have ?case . }
  ultimately show ?case by blast 
next
  case (5 c e) 
  then have cp: "c > 0" and nb: "numbound0 e" by auto
  { assume kdc: "k dvd c" 
    from tint have ti: "real (floor (?N (real x) t)) = ?N (real x) t" using isint_def by simp
    from kdc have  ?case using real_of_int_div[OF kdc] real_of_int_div[OF kdt]
      numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
      numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"] by (simp add: ti) } 
  moreover 
  { assume *: "\<not> k dvd c"
    from tint have ti: "real (floor (?N (real x) t)) = ?N (real x) t" using isint_def by simp
    from assms * have "?I (real x) (?s (Lt (CN 0 c e))) = ((real c * (?N (real x) t / real k) + ?N (real x) e)* real k < 0)"
      using real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"]
      by (simp add: ti algebra_simps)
    also have "\<dots> = (?I ?tk (Lt (CN 0 c e)))"
      using pos_less_divide_eq[OF kpos,
          where a="real c * (?N (real x) t / real k) + ?N (real x) e" and b="0", symmetric]
        real_of_int_div[OF kdt] numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"]
      by (simp add: ti)
    finally have ?case . }
  ultimately show ?case by blast 
next
  case (6 c e)
  then have cp: "c > 0" and nb: "numbound0 e" by auto
  { assume kdc: "k dvd c" 
    from tint have ti: "real (floor (?N (real x) t)) = ?N (real x) t" using isint_def by simp
    from kdc have  ?case using real_of_int_div[OF kdc] real_of_int_div[OF kdt]
      numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
      numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"] by (simp add: ti) } 
  moreover 
  { assume *: "\<not> k dvd c"
    from tint have ti: "real (floor (?N (real x) t)) = ?N (real x) t" using isint_def by simp
    from assms * have "?I (real x) (?s (Le (CN 0 c e))) = ((real c * (?N (real x) t / real k) + ?N (real x) e)* real k \<le> 0)"
      using real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"]
      by (simp add: ti algebra_simps)
    also have "\<dots> = (?I ?tk (Le (CN 0 c e)))"
      using pos_le_divide_eq[OF kpos,
          where a="real c * (?N (real x) t / real k) + ?N (real x) e" and b="0", symmetric]
        real_of_int_div[OF kdt] numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"]
      by (simp add: ti)
    finally have ?case . }
  ultimately show ?case by blast 
next
  case (7 c e) 
  then have cp: "c > 0" and nb: "numbound0 e" by auto
  { assume kdc: "k dvd c" 
    from tint have ti: "real (floor (?N (real x) t)) = ?N (real x) t" using isint_def by simp
    from kdc have  ?case using real_of_int_div[OF kdc] real_of_int_div[OF kdt]
      numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
      numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"] by (simp add: ti) } 
  moreover 
  { assume *: "\<not> k dvd c"
    from tint have ti: "real (floor (?N (real x) t)) = ?N (real x) t" using isint_def by simp
    from assms * have "?I (real x) (?s (Gt (CN 0 c e))) = ((real c * (?N (real x) t / real k) + ?N (real x) e)* real k > 0)"
      using real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"]
      by (simp add: ti algebra_simps)
    also have "\<dots> = (?I ?tk (Gt (CN 0 c e)))"
      using pos_divide_less_eq[OF kpos,
          where a="real c * (?N (real x) t / real k) + ?N (real x) e" and b="0", symmetric]
        real_of_int_div[OF kdt] numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"]
      by (simp add: ti)
    finally have ?case . }
  ultimately show ?case by blast 
next
  case (8 c e)  
  then have cp: "c > 0" and nb: "numbound0 e" by auto
  { assume kdc: "k dvd c" 
    from tint have ti: "real (floor (?N (real x) t)) = ?N (real x) t" using isint_def by simp
    from kdc have  ?case using real_of_int_div[OF kdc] real_of_int_div[OF kdt]
      numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
      numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"] by (simp add: ti) } 
  moreover 
  { assume *: "\<not> k dvd c"
    from tint have ti: "real (floor (?N (real x) t)) = ?N (real x) t" using isint_def by simp
    from assms * have "?I (real x) (?s (Ge (CN 0 c e))) = ((real c * (?N (real x) t / real k) + ?N (real x) e)* real k \<ge> 0)"
      using real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"]
      by (simp add: ti algebra_simps)
    also have "\<dots> = (?I ?tk (Ge (CN 0 c e)))"
      using pos_divide_le_eq[OF kpos,
          where a="real c * (?N (real x) t / real k) + ?N (real x) e" and b="0", symmetric]
        real_of_int_div[OF kdt] numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"]
      by (simp add: ti)
    finally have ?case . }
  ultimately show ?case by blast 
next
  case (9 i c e)
  then have cp: "c > 0" and nb: "numbound0 e" by auto
  { assume kdc: "k dvd c" 
    from tint have ti: "real (floor (?N (real x) t)) = ?N (real x) t" using isint_def by simp
    from kdc have ?case using real_of_int_div[OF kdc] real_of_int_div[OF kdt]
      numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
      numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"] by (simp add: ti) } 
  moreover 
  { assume *: "\<not> k dvd c"
    from kpos have knz: "k\<noteq>0" by simp hence knz': "real k \<noteq> 0" by simp
    from tint have ti: "real (floor (?N (real x) t)) = ?N (real x) t" using isint_def by simp
    from assms * have "?I (real x) (?s (Dvd i (CN 0 c e))) = (real i * real k rdvd (real c * (?N (real x) t / real k) + ?N (real x) e)* real k)"
      using real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"]
      by (simp add: ti algebra_simps)
    also have "\<dots> = (?I ?tk (Dvd i (CN 0 c e)))"
      using rdvd_mult[OF knz, where n="i"]
        real_of_int_div[OF kdt] numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"]
      by (simp add: ti)
    finally have ?case . }
  ultimately show ?case by blast 
next
  case (10 i c e)
  then have cp: "c > 0" and nb: "numbound0 e" by auto
  { assume kdc: "k dvd c" 
    from tint have ti: "real (floor (?N (real x) t)) = ?N (real x) t" using isint_def by simp
    from kdc have  ?case using real_of_int_div[OF kdc] real_of_int_div[OF kdt]
      numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
      numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"] by (simp add: ti) } 
  moreover 
  { assume *: "\<not> k dvd c"
    from kpos have knz: "k\<noteq>0" by simp hence knz': "real k \<noteq> 0" by simp
    from tint have ti: "real (floor (?N (real x) t)) = ?N (real x) t" using isint_def by simp
    from assms * have "?I (real x) (?s (NDvd i (CN 0 c e))) = (\<not> (real i * real k rdvd (real c * (?N (real x) t / real k) + ?N (real x) e)* real k))"
      using real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"]
      by (simp add: ti algebra_simps)
    also have "\<dots> = (?I ?tk (NDvd i (CN 0 c e)))"
      using rdvd_mult[OF knz, where n="i"] real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real x"]
      by (simp add: ti)
    finally have ?case . }
  ultimately show ?case by blast 
qed (simp_all add: bound0_I[where bs="bs" and b="real ((floor (?N b' t)) div k)" and b'="real x"]
  numbound0_I[where bs="bs" and b="real ((floor (?N b' t)) div k)" and b'="real x"])


lemma \<sigma>\<rho>_nb: assumes lp:"iszlfm p (a#bs)" and nb: "numbound0 t"
  shows "bound0 (\<sigma>\<rho> p (t,k))"
  using lp
  by (induct p rule: iszlfm.induct, auto simp add: nb)

lemma \<rho>_l:
  assumes lp: "iszlfm p (real (i::int)#bs)"
  shows "\<forall> (b,k) \<in> set (\<rho> p). k >0 \<and> numbound0 b \<and> isint b (real i#bs)"
using lp by (induct p rule: \<rho>.induct, auto simp add: isint_sub isint_neg)

lemma \<alpha>\<rho>_l:
  assumes lp: "iszlfm p (real (i::int)#bs)"
  shows "\<forall> (b,k) \<in> set (\<alpha>\<rho> p). k >0 \<and> numbound0 b \<and> isint b (real i#bs)"
using lp isint_add [OF isint_c[where j="- 1"],where bs="real i#bs"]
 by (induct p rule: \<alpha>\<rho>.induct, auto)

lemma \<rho>: assumes lp: "iszlfm p (real (i::int) #bs)"
  and pi: "Ifm (real i#bs) p"
  and d: "d\<delta> p d"
  and dp: "d > 0"
  and nob: "\<forall>(e,c) \<in> set (\<rho> p). \<forall> j\<in> {1 .. c*d}. real (c*i) \<noteq> Inum (real i#bs) e + real j"
  (is "\<forall>(e,c) \<in> set (\<rho> p). \<forall> j\<in> {1 .. c*d}. _ \<noteq> ?N i e + _")
  shows "Ifm (real(i - d)#bs) p"
  using lp pi d nob
proof(induct p rule: iszlfm.induct)
  case (3 c e) hence cp: "c >0" and nb: "numbound0 e" and ei: "isint e (real i#bs)"
    and pi: "real (c*i) = - 1 -  ?N i e + real (1::int)" and nob: "\<forall> j\<in> {1 .. c*d}. real (c*i) \<noteq> -1 - ?N i e + real j"
    by simp+
  from mult_strict_left_mono[OF dp cp]  have one:"1 \<in> {1 .. c*d}" by auto
  from nob[rule_format, where j="1", OF one] pi show ?case by simp
next
  case (4 c e)  
  hence cp: "c >0" and nb: "numbound0 e" and ei: "isint e (real i#bs)"
    and nob: "\<forall> j\<in> {1 .. c*d}. real (c*i) \<noteq> - ?N i e + real j"
    by simp+
  {assume "real (c*i) \<noteq> - ?N i e + real (c*d)"
    with numbound0_I[OF nb, where bs="bs" and b="real i - real d" and b'="real i"]
    have ?case by (simp add: algebra_simps)}
  moreover
  {assume pi: "real (c*i) = - ?N i e + real (c*d)"
    from mult_strict_left_mono[OF dp cp] have d: "(c*d) \<in> {1 .. c*d}" by simp
    from nob[rule_format, where j="c*d", OF d] pi have ?case by simp }
  ultimately show ?case by blast
next
  case (5 c e) hence cp: "c > 0" by simp
  from 5 mult_strict_left_mono[OF dp cp, simplified real_of_int_less_iff[symmetric] 
    real_of_int_mult]
  show ?case using 5 dp 
    by (simp add: add: numbound0_I[where bs="bs" and b="real i - real d" and b'="real i"] 
      algebra_simps)
next
  case (6 c e) hence cp: "c > 0" by simp
  from 6 mult_strict_left_mono[OF dp cp, simplified real_of_int_less_iff[symmetric] 
    real_of_int_mult]
  show ?case using 6 dp 
    by (simp add: add: numbound0_I[where bs="bs" and b="real i - real d" and b'="real i"] 
      algebra_simps)
next
  case (7 c e) hence cp: "c >0" and nb: "numbound0 e" and ei: "isint e (real i#bs)"
    and nob: "\<forall> j\<in> {1 .. c*d}. real (c*i) \<noteq> - ?N i e + real j"
    and pi: "real (c*i) + ?N i e > 0" and cp': "real c >0"
    by simp+
  let ?fe = "floor (?N i e)"
  from pi cp have th:"(real i +?N i e / real c)*real c > 0" by (simp add: algebra_simps)
  from pi ei[simplified isint_iff] have "real (c*i + ?fe) > real (0::int)" by simp
  hence pi': "c*i + ?fe > 0" by (simp only: real_of_int_less_iff[symmetric])
  have "real (c*i) + ?N i e > real (c*d) \<or> real (c*i) + ?N i e \<le> real (c*d)" by auto
  moreover
  {assume "real (c*i) + ?N i e > real (c*d)" hence ?case
      by (simp add: algebra_simps 
        numbound0_I[OF nb,where bs="bs" and b="real i - real d" and b'="real i"])} 
  moreover 
  {assume H:"real (c*i) + ?N i e \<le> real (c*d)"
    with ei[simplified isint_iff] have "real (c*i + ?fe) \<le> real (c*d)" by simp
    hence pid: "c*i + ?fe \<le> c*d" by (simp only: real_of_int_le_iff)
    with pi' have "\<exists> j1\<in> {1 .. c*d}. c*i + ?fe = j1" by auto
    hence "\<exists> j1\<in> {1 .. c*d}. real (c*i) = - ?N i e + real j1" 
      by (simp only: diff_minus[symmetric] real_of_int_mult real_of_int_add real_of_int_inject[symmetric] ei[simplified isint_iff] algebra_simps)
    with nob  have ?case by blast }
  ultimately show ?case by blast
next
  case (8 c e)  hence cp: "c >0" and nb: "numbound0 e" and ei: "isint e (real i#bs)"
    and nob: "\<forall> j\<in> {1 .. c*d}. real (c*i) \<noteq> - 1 - ?N i e + real j"
    and pi: "real (c*i) + ?N i e \<ge> 0" and cp': "real c >0"
    by simp+
  let ?fe = "floor (?N i e)"
  from pi cp have th:"(real i +?N i e / real c)*real c \<ge> 0" by (simp add: algebra_simps)
  from pi ei[simplified isint_iff] have "real (c*i + ?fe) \<ge> real (0::int)" by simp
  hence pi': "c*i + 1 + ?fe \<ge> 1" by (simp only: real_of_int_le_iff[symmetric])
  have "real (c*i) + ?N i e \<ge> real (c*d) \<or> real (c*i) + ?N i e < real (c*d)" by auto
  moreover
  {assume "real (c*i) + ?N i e \<ge> real (c*d)" hence ?case
      by (simp add: algebra_simps 
        numbound0_I[OF nb,where bs="bs" and b="real i - real d" and b'="real i"])} 
  moreover 
  {assume H:"real (c*i) + ?N i e < real (c*d)"
    with ei[simplified isint_iff] have "real (c*i + ?fe) < real (c*d)" by simp
    hence pid: "c*i + 1 + ?fe \<le> c*d" by (simp only: real_of_int_le_iff)
    with pi' have "\<exists> j1\<in> {1 .. c*d}. c*i + 1+ ?fe = j1" by auto
    hence "\<exists> j1\<in> {1 .. c*d}. real (c*i) + 1= - ?N i e + real j1"
      by (simp only: diff_minus[symmetric] real_of_int_mult real_of_int_add real_of_int_inject[symmetric] ei[simplified isint_iff] algebra_simps real_of_one) 
    hence "\<exists> j1\<in> {1 .. c*d}. real (c*i) = (- ?N i e + real j1) - 1"
      by (simp only: algebra_simps diff_minus[symmetric])
        hence "\<exists> j1\<in> {1 .. c*d}. real (c*i) = - 1 - ?N i e + real j1"
          by (simp only: add_ac diff_minus)
    with nob  have ?case by blast }
  ultimately show ?case by blast
next
  case (9 j c e)  hence p: "real j rdvd real (c*i) + ?N i e" (is "?p x") and cp: "c > 0" and bn:"numbound0 e"  by simp+
  let ?e = "Inum (real i # bs) e"
  from 9 have "isint e (real i #bs)"  by simp 
  hence ie: "real (floor ?e) = ?e" using isint_iff[where n="e" and bs="(real i)#bs"] numbound0_I[OF bn,where b="real i" and b'="real i" and bs="bs"]
    by (simp add: isint_iff)
  from 9 have id: "j dvd d" by simp
  from ie[symmetric] have "?p i = (real j rdvd real (c*i+ floor ?e))" by simp
  also have "\<dots> = (j dvd c*i + floor ?e)" 
    using int_rdvd_iff [where i="j" and t="c*i+ floor ?e"] by simp
  also have "\<dots> = (j dvd c*i - c*d + floor ?e)" 
    using dvd_period[OF id, where x="c*i" and c="-c" and t="floor ?e"] by simp
  also have "\<dots> = (real j rdvd real (c*i - c*d + floor ?e))" 
    using int_rdvd_iff[where i="j" and t="(c*i - c*d + floor ?e)",symmetric, simplified]
      ie by simp
  also have "\<dots> = (real j rdvd real (c*(i - d)) + ?e)" 
    using ie by (simp add:algebra_simps)
  finally show ?case 
    using numbound0_I[OF bn,where b="real i - real d" and b'="real i" and bs="bs"] p 
    by (simp add: algebra_simps)
next
  case (10 j c e)
  hence p: "\<not> (real j rdvd real (c*i) + ?N i e)" (is "?p x") and cp: "c > 0" and bn:"numbound0 e"
    by simp+
  let ?e = "Inum (real i # bs) e"
  from 10 have "isint e (real i #bs)"  by simp 
  hence ie: "real (floor ?e) = ?e"
    using isint_iff[where n="e" and bs="(real i)#bs"] numbound0_I[OF bn,where b="real i" and b'="real i" and bs="bs"]
    by (simp add: isint_iff)
  from 10 have id: "j dvd d" by simp
  from ie[symmetric] have "?p i = (\<not> (real j rdvd real (c*i+ floor ?e)))" by simp
  also have "\<dots> = Not (j dvd c*i + floor ?e)" 
    using int_rdvd_iff [where i="j" and t="c*i+ floor ?e"] by simp
  also have "\<dots> = Not (j dvd c*i - c*d + floor ?e)" 
    using dvd_period[OF id, where x="c*i" and c="-c" and t="floor ?e"] by simp
  also have "\<dots> = Not (real j rdvd real (c*i - c*d + floor ?e))" 
    using int_rdvd_iff[where i="j" and t="(c*i - c*d + floor ?e)",symmetric, simplified]
      ie by simp
  also have "\<dots> = Not (real j rdvd real (c*(i - d)) + ?e)" 
    using ie by (simp add:algebra_simps)
  finally show ?case 
    using numbound0_I[OF bn,where b="real i - real d" and b'="real i" and bs="bs"] p 
    by (simp add: algebra_simps)
qed (auto simp add: numbound0_I[where bs="bs" and b="real i - real d" and b'="real i"])

lemma \<sigma>_nb: assumes lp: "iszlfm p (a#bs)" and nb: "numbound0 t"
  shows "bound0 (\<sigma> p k t)"
  using \<sigma>\<rho>_nb[OF lp nb] nb by (simp add: \<sigma>_def)
  
lemma \<rho>':   assumes lp: "iszlfm p (a #bs)"
  and d: "d\<delta> p d"
  and dp: "d > 0"
  shows "\<forall> x. \<not>(\<exists> (e,c) \<in> set(\<rho> p). \<exists>(j::int) \<in> {1 .. c*d}. Ifm (a #bs) (\<sigma> p c (Add e (C j)))) \<longrightarrow> Ifm (real x#bs) p \<longrightarrow> Ifm (real (x - d)#bs) p" (is "\<forall> x. ?b x \<longrightarrow> ?P x \<longrightarrow> ?P (x - d)")
proof(clarify)
  fix x 
  assume nob1:"?b x" and px: "?P x" 
  from iszlfm_gen[OF lp, rule_format, where y="real x"] have lp': "iszlfm p (real x#bs)".
  have nob: "\<forall>(e, c)\<in>set (\<rho> p). \<forall>j\<in>{1..c * d}. real (c * x) \<noteq> Inum (real x # bs) e + real j" 
  proof(clarify)
    fix e c j assume ecR: "(e,c) \<in> set (\<rho> p)" and jD: "j\<in> {1 .. c*d}"
      and cx: "real (c*x) = Inum (real x#bs) e + real j"
    let ?e = "Inum (real x#bs) e"
    let ?fe = "floor ?e"
    from \<rho>_l[OF lp'] ecR have ei:"isint e (real x#bs)" and cp:"c>0" and nb:"numbound0 e"
      by auto
    from numbound0_gen [OF nb ei, rule_format,where y="a"] have "isint e (a#bs)" .
    from cx ei[simplified isint_iff] have "real (c*x) = real (?fe + j)" by simp
    hence cx: "c*x = ?fe + j" by (simp only: real_of_int_inject)
    hence cdej:"c dvd ?fe + j" by (simp add: dvd_def) (rule_tac x="x" in exI, simp)
    hence "real c rdvd real (?fe + j)" by (simp only: int_rdvd_iff)
    hence rcdej: "real c rdvd ?e + real j" by (simp add: ei[simplified isint_iff])
    from cx have "(c*x) div c = (?fe + j) div c" by simp
    with cp have "x = (?fe + j) div c" by simp
    with px have th: "?P ((?fe + j) div c)" by auto
    from cp have cp': "real c > 0" by simp
    from cdej have cdej': "c dvd floor (Inum (real x#bs) (Add e (C j)))" by simp
    from nb have nb': "numbound0 (Add e (C j))" by simp
    have ji: "isint (C j) (real x#bs)" by (simp add: isint_def)
    from isint_add[OF ei ji] have ei':"isint (Add e (C j)) (real x#bs)" .
    from th \<sigma>\<rho>[where b'="real x", OF lp' cp' nb' ei' cdej',symmetric]
    have "Ifm (real x#bs) (\<sigma>\<rho> p (Add e (C j), c))" by simp
    with rcdej have th: "Ifm (real x#bs) (\<sigma> p c (Add e (C j)))" by (simp add: \<sigma>_def)
    from th bound0_I[OF \<sigma>_nb[OF lp nb', where k="c"],where bs="bs" and b="real x" and b'="a"]
    have "Ifm (a#bs) (\<sigma> p c (Add e (C j)))" by blast
      with ecR jD nob1    show "False" by blast
  qed
  from \<rho>[OF lp' px d dp nob] show "?P (x -d )" . 
qed


lemma rl_thm: 
  assumes lp: "iszlfm p (real (i::int)#bs)"
  shows "(\<exists> (x::int). Ifm (real x#bs) p) = ((\<exists> j\<in> {1 .. \<delta> p}. Ifm (real j#bs) (minusinf p)) \<or> (\<exists> (e,c) \<in> set (\<rho> p). \<exists> j\<in> {1 .. c*(\<delta> p)}. Ifm (a#bs) (\<sigma> p c (Add e (C j)))))"
  (is "(\<exists>(x::int). ?P x) = ((\<exists> j\<in> {1.. \<delta> p}. ?MP j)\<or>(\<exists> (e,c) \<in> ?R. \<exists> j\<in> _. ?SP c e j))" 
    is "?lhs = (?MD \<or> ?RD)"  is "?lhs = ?rhs")
proof-
  let ?d= "\<delta> p"
  from \<delta>[OF lp] have d:"d\<delta> p ?d" and dp: "?d > 0" by auto
  { assume H:"?MD" hence th:"\<exists> (x::int). ?MP x" by blast
    from H minusinf_ex[OF lp th] have ?thesis  by blast}
  moreover
  { fix e c j assume exR:"(e,c) \<in> ?R" and jD:"j\<in> {1 .. c*?d}" and spx:"?SP c e j"
    from exR \<rho>_l[OF lp] have nb: "numbound0 e" and ei:"isint e (real i#bs)" and cp: "c > 0"
      by auto
    have "isint (C j) (real i#bs)" by (simp add: isint_iff)
    with isint_add[OF numbound0_gen[OF nb ei,rule_format, where y="real i"]]
    have eji:"isint (Add e (C j)) (real i#bs)" by simp
    from nb have nb': "numbound0 (Add e (C j))" by simp
    from spx bound0_I[OF \<sigma>_nb[OF lp nb', where k="c"], where bs="bs" and b="a" and b'="real i"]
    have spx': "Ifm (real i # bs) (\<sigma> p c (Add e (C j)))" by blast
    from spx' have rcdej:"real c rdvd (Inum (real i#bs) (Add e (C j)))" 
      and sr:"Ifm (real i#bs) (\<sigma>\<rho> p (Add e (C j),c))" by (simp add: \<sigma>_def)+
    from rcdej eji[simplified isint_iff] 
    have "real c rdvd real (floor (Inum (real i#bs) (Add e (C j))))" by simp
    hence cdej:"c dvd floor (Inum (real i#bs) (Add e (C j)))" by (simp only: int_rdvd_iff)
    from cp have cp': "real c > 0" by simp
    from \<sigma>\<rho>[OF lp cp' nb' eji cdej] spx' have "?P (\<lfloor>Inum (real i # bs) (Add e (C j))\<rfloor> div c)"
      by (simp add: \<sigma>_def)
    hence ?lhs by blast
    with exR jD spx have ?thesis by blast}
  moreover
  { fix x assume px: "?P x" and nob: "\<not> ?RD"
    from iszlfm_gen [OF lp,rule_format, where y="a"] have lp':"iszlfm p (a#bs)" .
    from \<rho>'[OF lp' d dp, rule_format, OF nob] have th:"\<forall> x. ?P x \<longrightarrow> ?P (x - ?d)" by blast
    from minusinf_inf[OF lp] obtain z where z:"\<forall> x<z. ?MP x = ?P x" by blast
    have zp: "abs (x - z) + 1 \<ge> 0" by arith
    from decr_lemma[OF dp,where x="x" and z="z"] 
      decr_mult_lemma[OF dp th zp, rule_format, OF px] z have th:"\<exists> x. ?MP x" by auto
    with minusinf_bex[OF lp] px nob have ?thesis by blast}
  ultimately show ?thesis by blast
qed

lemma mirror_\<alpha>\<rho>:   assumes lp: "iszlfm p (a#bs)"
  shows "(\<lambda> (t,k). (Inum (a#bs) t, k)) ` set (\<alpha>\<rho> p) = (\<lambda> (t,k). (Inum (a#bs) t,k)) ` set (\<rho> (mirror p))"
using lp
by (induct p rule: mirror.induct, simp_all add: split_def image_Un )
  
text {* The @{text "\<real>"} part*}

text{* Linearity for fm where Bound 0 ranges over @{text "\<real>"}*}
consts
  isrlfm :: "fm \<Rightarrow> bool"   (* Linearity test for fm *)
recdef isrlfm "measure size"
  "isrlfm (And p q) = (isrlfm p \<and> isrlfm q)" 
  "isrlfm (Or p q) = (isrlfm p \<and> isrlfm q)" 
  "isrlfm (Eq  (CN 0 c e)) = (c>0 \<and> numbound0 e)"
  "isrlfm (NEq (CN 0 c e)) = (c>0 \<and> numbound0 e)"
  "isrlfm (Lt  (CN 0 c e)) = (c>0 \<and> numbound0 e)"
  "isrlfm (Le  (CN 0 c e)) = (c>0 \<and> numbound0 e)"
  "isrlfm (Gt  (CN 0 c e)) = (c>0 \<and> numbound0 e)"
  "isrlfm (Ge  (CN 0 c e)) = (c>0 \<and> numbound0 e)"
  "isrlfm p = (isatom p \<and> (bound0 p))"

definition fp :: "fm \<Rightarrow> int \<Rightarrow> num \<Rightarrow> int \<Rightarrow> fm" where
  "fp p n s j \<equiv> (if n > 0 then 
            (And p (And (Ge (CN 0 n (Sub s (Add (Floor s) (C j)))))
                        (Lt (CN 0 n (Sub s (Add (Floor s) (C (j+1))))))))
            else 
            (And p (And (Le (CN 0 (-n) (Add (Neg s) (Add (Floor s) (C j))))) 
                        (Gt (CN 0 (-n) (Add (Neg s) (Add (Floor s) (C (j + 1)))))))))"

  (* splits the bounded from the unbounded part*)
function (sequential) rsplit0 :: "num \<Rightarrow> (fm \<times> int \<times> num) list" where
  "rsplit0 (Bound 0) = [(T,1,C 0)]"
| "rsplit0 (Add a b) = (let acs = rsplit0 a ; bcs = rsplit0 b 
              in map (\<lambda> ((p,n,t),(q,m,s)). (And p q, n+m, Add t s)) [(a,b). a\<leftarrow>acs,b\<leftarrow>bcs])"
| "rsplit0 (Sub a b) = rsplit0 (Add a (Neg b))"
| "rsplit0 (Neg a) = map (\<lambda> (p,n,s). (p,-n,Neg s)) (rsplit0 a)"
| "rsplit0 (Floor a) = concat (map 
      (\<lambda> (p,n,s). if n=0 then [(p,0,Floor s)]
          else (map (\<lambda> j. (fp p n s j, 0, Add (Floor s) (C j))) (if n > 0 then [0 .. n] else [n .. 0])))
       (rsplit0 a))"
| "rsplit0 (CN 0 c a) = map (\<lambda> (p,n,s). (p,n+c,s)) (rsplit0 a)"
| "rsplit0 (CN m c a) = map (\<lambda> (p,n,s). (p,n,CN m c s)) (rsplit0 a)"
| "rsplit0 (CF c t s) = rsplit0 (Add (Mul c (Floor t)) s)"
| "rsplit0 (Mul c a) = map (\<lambda> (p,n,s). (p,c*n,Mul c s)) (rsplit0 a)"
| "rsplit0 t = [(T,0,t)]"
by pat_completeness auto
termination by (relation "measure num_size") auto

lemma conj_rl[simp]: "isrlfm p \<Longrightarrow> isrlfm q \<Longrightarrow> isrlfm (conj p q)"
  using conj_def by (cases p, auto)
lemma disj_rl[simp]: "isrlfm p \<Longrightarrow> isrlfm q \<Longrightarrow> isrlfm (disj p q)"
  using disj_def by (cases p, auto)


lemma rsplit0_cs:
  shows "\<forall> (p,n,s) \<in> set (rsplit0 t). 
  (Ifm (x#bs) p \<longrightarrow>  (Inum (x#bs) t = Inum (x#bs) (CN 0 n s))) \<and> numbound0 s \<and> isrlfm p" 
  (is "\<forall> (p,n,s) \<in> ?SS t. (?I p \<longrightarrow> ?N t = ?N (CN 0 n s)) \<and> _ \<and> _ ")
proof(induct t rule: rsplit0.induct)
  case (5 a) 
  let ?p = "\<lambda> (p,n,s) j. fp p n s j"
  let ?f = "(\<lambda> (p,n,s) j. (?p (p,n,s) j, (0::int),Add (Floor s) (C j)))"
  let ?J = "\<lambda> n. if n>0 then [0..n] else [n..0]"
  let ?ff=" (\<lambda> (p,n,s). if n= 0 then [(p,0,Floor s)] else map (?f (p,n,s)) (?J n))"
  have int_cases: "\<forall> (i::int). i= 0 \<or> i < 0 \<or> i > 0" by arith
  have U1: "(UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). set (?ff (p,n,s)))) = 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). set [(p,0,Floor s)]))" by auto
  have U2': "\<forall> (p,n,s) \<in> {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0}. 
    ?ff (p,n,s) = map (?f(p,n,s)) [0..n]" by auto
  hence U2: "(UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). set (?ff (p,n,s)))) = 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). 
    set (map (?f(p,n,s)) [0..n])))"
  proof-
    fix M :: "('a\<times>'b\<times>'c) set" and f :: "('a\<times>'b\<times>'c) \<Rightarrow> 'd list" and g
    assume "\<forall> (a,b,c) \<in> M. f (a,b,c) = g a b c"
    thus "(UNION M (\<lambda> (a,b,c). set (f (a,b,c)))) = (UNION M (\<lambda> (a,b,c). set (g a b c)))"
      by (auto simp add: split_def)
  qed
  have U3': "\<forall> (p,n,s) \<in> {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0}. ?ff (p,n,s) = map (?f(p,n,s)) [n..0]"
    by auto
  hence U3: "(UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s). set (?ff (p,n,s)))) = 
    (UNION {(p,n,s). (p,n,s)\<in> ?SS a\<and>n<0} (\<lambda>(p,n,s). set (map (?f(p,n,s)) [n..0])))"
      proof-
    fix M :: "('a\<times>'b\<times>'c) set" and f :: "('a\<times>'b\<times>'c) \<Rightarrow> 'd list" and g
    assume "\<forall> (a,b,c) \<in> M. f (a,b,c) = g a b c"
    thus "(UNION M (\<lambda> (a,b,c). set (f (a,b,c)))) = (UNION M (\<lambda> (a,b,c). set (g a b c)))"
      by (auto simp add: split_def)
  qed
  have "?SS (Floor a) = UNION (?SS a) (\<lambda>x. set (?ff x))"
    by auto
  also have "\<dots> = UNION (?SS a) (\<lambda> (p,n,s). set (?ff (p,n,s)))" by blast
  also have "\<dots> = 
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). set (?ff (p,n,s)))) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). set (?ff (p,n,s)))) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s). set (?ff (p,n,s)))))" 
    using int_cases[rule_format] by blast
  also have "\<dots> =  
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). set [(p,0,Floor s)])) Un 
   (UNION {(p,n,s). (p,n,s)\<in> ?SS a\<and>n>0} (\<lambda>(p,n,s). set(map(?f(p,n,s)) [0..n]))) Un 
   (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s). 
    set (map (?f(p,n,s)) [n..0]))))" by (simp only: U1 U2 U3)
  also have "\<dots> =  
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). {(p,0,Floor s)})) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). (?f(p,n,s)) ` {0 .. n})) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s). (?f(p,n,s)) ` {n .. 0})))"
    by (simp only: set_map set_upto set.simps)
  also have "\<dots> =   
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). {(p,0,Floor s)})) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). {?f(p,n,s) j| j. j\<in> {0 .. n}})) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s).  {?f(p,n,s) j| j. j\<in> {n .. 0}})))" by blast
  finally 
  have FS: "?SS (Floor a) =   
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). {(p,0,Floor s)})) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). {?f(p,n,s) j| j. j\<in> {0 .. n}})) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s).  {?f(p,n,s) j| j. j\<in> {n .. 0}})))"    by blast
  show ?case
  proof(simp only: FS, clarsimp simp del: Ifm.simps Inum.simps, -)
    fix p n s
    let ?ths = "(?I p \<longrightarrow> (?N (Floor a) = ?N (CN 0 n s))) \<and> numbound0 s \<and> isrlfm p"
    assume "(\<exists>ba. (p, 0, ba) \<in> set (rsplit0 a) \<and> n = 0 \<and> s = Floor ba) \<or>
       (\<exists>ab ac ba.
           (ab, ac, ba) \<in> set (rsplit0 a) \<and>
           0 < ac \<and>
           (\<exists>j. p = fp ab ac ba j \<and>
                n = 0 \<and> s = Add (Floor ba) (C j) \<and> 0 \<le> j \<and> j \<le> ac)) \<or>
       (\<exists>ab ac ba.
           (ab, ac, ba) \<in> set (rsplit0 a) \<and>
           ac < 0 \<and>
           (\<exists>j. p = fp ab ac ba j \<and>
                n = 0 \<and> s = Add (Floor ba) (C j) \<and> ac \<le> j \<and> j \<le> 0))"
    moreover 
    { fix s'
      assume "(p, 0, s') \<in> ?SS a" and "n = 0" and "s = Floor s'"
      hence ?ths using 5(1) by auto }
    moreover
    { fix p' n' s' j
      assume pns: "(p', n', s') \<in> ?SS a" 
        and np: "0 < n'" 
        and p_def: "p = ?p (p',n',s') j" 
        and n0: "n = 0" 
        and s_def: "s = (Add (Floor s') (C j))" 
        and jp: "0 \<le> j" and jn: "j \<le> n'"
      from 5 pns have H:"(Ifm ((x\<Colon>real) # (bs\<Colon>real list)) p' \<longrightarrow>
          Inum (x # bs) a = Inum (x # bs) (CN 0 n' s')) \<and>
          numbound0 s' \<and> isrlfm p'" by blast
      hence nb: "numbound0 s'" by simp
      from H have nf: "isrlfm (?p (p',n',s') j)" using fp_def np by (simp add: numsub_nb)
      let ?nxs = "CN 0 n' s'"
      let ?l = "floor (?N s') + j"
      from H 
      have "?I (?p (p',n',s') j) \<longrightarrow> 
          (((?N ?nxs \<ge> real ?l) \<and> (?N ?nxs < real (?l + 1))) \<and> (?N a = ?N ?nxs ))" 
        by (simp add: fp_def np algebra_simps numsub numadd numfloor)
      also have "\<dots> \<longrightarrow> ((floor (?N ?nxs) = ?l) \<and> (?N a = ?N ?nxs ))"
        using floor_int_eq[where x="?N ?nxs" and n="?l"] by simp
      moreover
      have "\<dots> \<longrightarrow> (?N (Floor a) = ?N ((Add (Floor s') (C j))))" by simp
      ultimately have "?I (?p (p',n',s') j) \<longrightarrow> (?N (Floor a) = ?N ((Add (Floor s') (C j))))"
        by blast
      with s_def n0 p_def nb nf have ?ths by auto}
    moreover
    { fix p' n' s' j
      assume pns: "(p', n', s') \<in> ?SS a" 
        and np: "n' < 0" 
        and p_def: "p = ?p (p',n',s') j" 
        and n0: "n = 0" 
        and s_def: "s = (Add (Floor s') (C j))" 
        and jp: "n' \<le> j" and jn: "j \<le> 0"
      from 5 pns have H:"(Ifm ((x\<Colon>real) # (bs\<Colon>real list)) p' \<longrightarrow>
          Inum (x # bs) a = Inum (x # bs) (CN 0 n' s')) \<and>
          numbound0 s' \<and> isrlfm p'" by blast
      hence nb: "numbound0 s'" by simp
      from H have nf: "isrlfm (?p (p',n',s') j)" using fp_def np by (simp add: numneg_nb)
      let ?nxs = "CN 0 n' s'"
      let ?l = "floor (?N s') + j"
      from H 
      have "?I (?p (p',n',s') j) \<longrightarrow> 
          (((?N ?nxs \<ge> real ?l) \<and> (?N ?nxs < real (?l + 1))) \<and> (?N a = ?N ?nxs ))" 
        by (simp add: np fp_def algebra_simps numneg numfloor numadd numsub)
      also have "\<dots> \<longrightarrow> ((floor (?N ?nxs) = ?l) \<and> (?N a = ?N ?nxs ))"
        using floor_int_eq[where x="?N ?nxs" and n="?l"] by simp
      moreover
      have "\<dots> \<longrightarrow> (?N (Floor a) = ?N ((Add (Floor s') (C j))))"  by simp
      ultimately have "?I (?p (p',n',s') j) \<longrightarrow> (?N (Floor a) = ?N ((Add (Floor s') (C j))))"
        by blast
      with s_def n0 p_def nb nf have ?ths by auto}
    ultimately show ?ths by auto
  qed
next
  case (3 a b) then show ?case
    apply auto
    apply (erule_tac x = "(aa, aaa, ba)" in ballE) apply simp_all
    apply (erule_tac x = "(ab, ac, baa)" in ballE) apply simp_all
    done
qed (auto simp add: Let_def split_def algebra_simps conj_rl)

lemma real_in_int_intervals: 
  assumes xb: "real m \<le> x \<and> x < real ((n::int) + 1)"
  shows "\<exists> j\<in> {m.. n}. real j \<le> x \<and> x < real (j+1)" (is "\<exists> j\<in> ?N. ?P j")
by (rule bexI[where P="?P" and x="floor x" and A="?N"]) 
(auto simp add: floor_less_eq[where x="x" and a="n+1", simplified] xb[simplified] floor_mono[where x="real m" and y="x", OF conjunct1[OF xb], simplified floor_real_of_int[where n="m"]])

lemma rsplit0_complete:
  assumes xp:"0 \<le> x" and x1:"x < 1"
  shows "\<exists> (p,n,s) \<in> set (rsplit0 t). Ifm (x#bs) p" (is "\<exists> (p,n,s) \<in> ?SS t. ?I p")
proof(induct t rule: rsplit0.induct)
  case (2 a b) 
  then have "\<exists> (pa,na,sa) \<in> ?SS a. ?I pa" by auto
  then obtain "pa" "na" "sa" where pa: "(pa,na,sa)\<in> ?SS a \<and> ?I pa" by blast
  with 2 have "\<exists> (pb,nb,sb) \<in> ?SS b. ?I pb" by blast
  then obtain "pb" "nb" "sb" where pb: "(pb,nb,sb)\<in> ?SS b \<and> ?I pb" by blast
  from pa pb have th: "((pa,na,sa),(pb,nb,sb)) \<in> set[(x,y). x\<leftarrow>rsplit0 a, y\<leftarrow>rsplit0 b]"
    by (auto)
  let ?f="(\<lambda> ((p,n,t),(q,m,s)). (And p q, n+m, Add t s))"
  from imageI[OF th, where f="?f"] have "?f ((pa,na,sa),(pb,nb,sb)) \<in> ?SS (Add a b)"
    by (simp add: Let_def)
  hence "(And pa pb, na +nb, Add sa sb) \<in> ?SS (Add a b)" by simp
  moreover from pa pb have "?I (And pa pb)" by simp
  ultimately show ?case by blast
next
  case (5 a) 
  let ?p = "\<lambda> (p,n,s) j. fp p n s j"
  let ?f = "(\<lambda> (p,n,s) j. (?p (p,n,s) j, (0::int),(Add (Floor s) (C j))))"
  let ?J = "\<lambda> n. if n>0 then [0..n] else [n..0]"
  let ?ff=" (\<lambda> (p,n,s). if n= 0 then [(p,0,Floor s)] else map (?f (p,n,s)) (?J n))"
  have int_cases: "\<forall> (i::int). i= 0 \<or> i < 0 \<or> i > 0" by arith
  have U1: "(UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). set (?ff (p,n,s)))) = (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). set [(p,0,Floor s)]))" by auto
  have U2': "\<forall> (p,n,s) \<in> {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0}. ?ff (p,n,s) = map (?f(p,n,s)) [0..n]"
    by auto
  hence U2: "(UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). set (?ff (p,n,s)))) = (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). set (map (?f(p,n,s)) [0..n])))"
  proof-
    fix M :: "('a\<times>'b\<times>'c) set" and f :: "('a\<times>'b\<times>'c) \<Rightarrow> 'd list" and g
    assume "\<forall> (a,b,c) \<in> M. f (a,b,c) = g a b c"
    thus "(UNION M (\<lambda> (a,b,c). set (f (a,b,c)))) = (UNION M (\<lambda> (a,b,c). set (g a b c)))"
      by (auto simp add: split_def)
  qed
  have U3': "\<forall> (p,n,s) \<in> {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0}. ?ff (p,n,s) = map (?f(p,n,s)) [n..0]"
    by auto
  hence U3: "(UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s). set (?ff (p,n,s)))) = (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s). set (map (?f(p,n,s)) [n..0])))"
  proof-
    fix M :: "('a\<times>'b\<times>'c) set" and f :: "('a\<times>'b\<times>'c) \<Rightarrow> 'd list" and g
    assume "\<forall> (a,b,c) \<in> M. f (a,b,c) = g a b c"
    thus "(UNION M (\<lambda> (a,b,c). set (f (a,b,c)))) = (UNION M (\<lambda> (a,b,c). set (g a b c)))"
      by (auto simp add: split_def)
  qed

  have "?SS (Floor a) = UNION (?SS a) (\<lambda>x. set (?ff x))" by auto
  also have "\<dots> = UNION (?SS a) (\<lambda> (p,n,s). set (?ff (p,n,s)))" by blast
  also have "\<dots> = 
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). set (?ff (p,n,s)))) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). set (?ff (p,n,s)))) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s). set (?ff (p,n,s)))))" 
    using int_cases[rule_format] by blast
  also have "\<dots> =  
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). set [(p,0,Floor s)])) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). set (map (?f(p,n,s)) [0..n]))) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s). set (map (?f(p,n,s)) [n..0]))))" by (simp only: U1 U2 U3)
  also have "\<dots> =  
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). {(p,0,Floor s)})) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). (?f(p,n,s)) ` {0 .. n})) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s). (?f(p,n,s)) ` {n .. 0})))"
    by (simp only: set_map set_upto set.simps)
  also have "\<dots> =   
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). {(p,0,Floor s)})) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). {?f(p,n,s) j| j. j\<in> {0 .. n}})) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s).  {?f(p,n,s) j| j. j\<in> {n .. 0}})))" by blast
  finally 
  have FS: "?SS (Floor a) =   
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). {(p,0,Floor s)})) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). {?f(p,n,s) j| j. j\<in> {0 .. n}})) Un 
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s).  {?f(p,n,s) j| j. j\<in> {n .. 0}})))"
    by blast
  from 5 have "\<exists> (p,n,s) \<in> ?SS a. ?I p" by auto
  then obtain "p" "n" "s" where pns: "(p,n,s) \<in> ?SS a \<and> ?I p" by blast
  let ?N = "\<lambda> t. Inum (x#bs) t"
  from rsplit0_cs[rule_format] pns have ans:"(?N a = ?N (CN 0 n s)) \<and> numbound0 s \<and> isrlfm p"
    by auto
  
  have "n=0 \<or> n >0 \<or> n <0" by arith
  moreover {assume "n=0" hence ?case using pns by (simp only: FS) auto }
  moreover
  {
    assume np: "n > 0"
    from real_of_int_floor_le[where r="?N s"] have "?N (Floor s) \<le> ?N s" by simp
    also from mult_left_mono[OF xp] np have "?N s \<le> real n * x + ?N s" by simp
    finally have "?N (Floor s) \<le> real n * x + ?N s" .
    moreover
    {from x1 np have "real n *x + ?N s < real n + ?N s" by simp
      also from real_of_int_floor_add_one_gt[where r="?N s"] 
      have "\<dots> < real n + ?N (Floor s) + 1" by simp
      finally have "real n *x + ?N s < ?N (Floor s) + real (n+1)" by simp}
    ultimately have "?N (Floor s) \<le> real n *x + ?N s\<and> real n *x + ?N s < ?N (Floor s) + real (n+1)" by simp
    hence th: "0 \<le> real n *x + ?N s - ?N (Floor s) \<and> real n *x + ?N s - ?N (Floor s) < real (n+1)" by simp
    from real_in_int_intervals th have  "\<exists> j\<in> {0 .. n}. real j \<le> real n *x + ?N s - ?N (Floor s)\<and> real n *x + ?N s - ?N (Floor s) < real (j+1)" by simp
    
    hence "\<exists> j\<in> {0 .. n}. 0 \<le> real n *x + ?N s - ?N (Floor s) - real j \<and> real n *x + ?N s - ?N (Floor s) - real (j+1) < 0"
      by(simp only: myle[of _ "real n * x + Inum (x # bs) s - Inum (x # bs) (Floor s)"] less_iff_diff_less_0[where a="real n *x + ?N s - ?N (Floor s)"]) 
    hence "\<exists> j\<in> {0.. n}. ?I (?p (p,n,s) j)"
      using pns by (simp add: fp_def np algebra_simps numsub numadd)
    then obtain "j" where j_def: "j\<in> {0 .. n} \<and> ?I (?p (p,n,s) j)" by blast
    hence "\<exists>x \<in> {?p (p,n,s) j |j. 0\<le> j \<and> j \<le> n }. ?I x" by auto
    hence ?case using pns 
      by (simp only: FS,simp add: bex_Un) 
    (rule disjI2, rule disjI1,rule exI [where x="p"],
      rule exI [where x="n"],rule exI [where x="s"],simp_all add: np)
  }
  moreover
  { assume nn: "n < 0" hence np: "-n >0" by simp
    from real_of_int_floor_le[where r="?N s"] have "?N (Floor s) + 1 > ?N s" by simp
    moreover from mult_left_mono_neg[OF xp] nn have "?N s \<ge> real n * x + ?N s" by simp
    ultimately have "?N (Floor s) + 1 > real n * x + ?N s" by arith 
    moreover
    {from x1 nn have "real n *x + ?N s \<ge> real n + ?N s" by simp
      moreover from real_of_int_floor_le[where r="?N s"]  have "real n + ?N s \<ge> real n + ?N (Floor s)" by simp
      ultimately have "real n *x + ?N s \<ge> ?N (Floor s) + real n" 
        by (simp only: algebra_simps)}
    ultimately have "?N (Floor s) + real n \<le> real n *x + ?N s\<and> real n *x + ?N s < ?N (Floor s) + real (1::int)" by simp
    hence th: "real n \<le> real n *x + ?N s - ?N (Floor s) \<and> real n *x + ?N s - ?N (Floor s) < real (1::int)" by simp
    have th1: "\<forall> (a::real). (- a > 0) = (a < 0)" by auto
    have th2: "\<forall> (a::real). (0 \<ge> - a) = (a \<ge> 0)" by auto
    from real_in_int_intervals th  have  "\<exists> j\<in> {n .. 0}. real j \<le> real n *x + ?N s - ?N (Floor s)\<and> real n *x + ?N s - ?N (Floor s) < real (j+1)" by simp
    
    hence "\<exists> j\<in> {n .. 0}. 0 \<le> real n *x + ?N s - ?N (Floor s) - real j \<and> real n *x + ?N s - ?N (Floor s) - real (j+1) < 0"
      by(simp only: myle[of _ "real n * x + Inum (x # bs) s - Inum (x # bs) (Floor s)"] less_iff_diff_less_0[where a="real n *x + ?N s - ?N (Floor s)"]) 
    hence "\<exists> j\<in> {n .. 0}. 0 \<ge> - (real n *x + ?N s - ?N (Floor s) - real j) \<and> - (real n *x + ?N s - ?N (Floor s) - real (j+1)) > 0" by (simp only: th1[rule_format] th2[rule_format])
    hence "\<exists> j\<in> {n.. 0}. ?I (?p (p,n,s) j)"
      using pns by (simp add: fp_def nn diff_minus add_ac mult_ac numfloor numadd numneg
        del: diff_less_0_iff_less diff_le_0_iff_le) 
    then obtain "j" where j_def: "j\<in> {n .. 0} \<and> ?I (?p (p,n,s) j)" by blast
    hence "\<exists>x \<in> {?p (p,n,s) j |j. n\<le> j \<and> j \<le> 0 }. ?I x" by auto
    hence ?case using pns 
      by (simp only: FS,simp add: bex_Un)
    (rule disjI2, rule disjI2,rule exI [where x="p"],
      rule exI [where x="n"],rule exI [where x="s"],simp_all add: nn)
  }
  ultimately show ?case by blast
qed (auto simp add: Let_def split_def)

    (* Linearize a formula where Bound 0 ranges over [0,1) *)

definition rsplit :: "(int \<Rightarrow> num \<Rightarrow> fm) \<Rightarrow> num \<Rightarrow> fm" where
  "rsplit f a \<equiv> foldr disj (map (\<lambda> (\<phi>, n, s). conj \<phi> (f n s)) (rsplit0 a)) F"

lemma foldr_disj_map: "Ifm bs (foldr disj (map f xs) F) = (\<exists> x \<in> set xs. Ifm bs (f x))"
by(induct xs, simp_all)

lemma foldr_conj_map: "Ifm bs (foldr conj (map f xs) T) = (\<forall> x \<in> set xs. Ifm bs (f x))"
by(induct xs, simp_all)

lemma foldr_disj_map_rlfm: 
  assumes lf: "\<forall> n s. numbound0 s \<longrightarrow> isrlfm (f n s)"
  and \<phi>: "\<forall> (\<phi>,n,s) \<in> set xs. numbound0 s \<and> isrlfm \<phi>"
  shows "isrlfm (foldr disj (map (\<lambda> (\<phi>, n, s). conj \<phi> (f n s)) xs) F)"
using lf \<phi> by (induct xs, auto)

lemma rsplit_ex: "Ifm bs (rsplit f a) = (\<exists> (\<phi>,n,s) \<in> set (rsplit0 a). Ifm bs (conj \<phi> (f n s)))"
using foldr_disj_map[where xs="rsplit0 a"] rsplit_def by (simp add: split_def)

lemma rsplit_l: assumes lf: "\<forall> n s. numbound0 s \<longrightarrow> isrlfm (f n s)"
  shows "isrlfm (rsplit f a)"
proof-
  from rsplit0_cs[where t="a"] have th: "\<forall> (\<phi>,n,s) \<in> set (rsplit0 a). numbound0 s \<and> isrlfm \<phi>" by blast
  from foldr_disj_map_rlfm[OF lf th] rsplit_def show ?thesis by simp
qed

lemma rsplit: 
  assumes xp: "x \<ge> 0" and x1: "x < 1"
  and f: "\<forall> a n s. Inum (x#bs) a = Inum (x#bs) (CN 0 n s) \<and> numbound0 s \<longrightarrow> (Ifm (x#bs) (f n s) = Ifm (x#bs) (g a))"
  shows "Ifm (x#bs) (rsplit f a) = Ifm (x#bs) (g a)"
proof(auto)
  let ?I = "\<lambda>x p. Ifm (x#bs) p"
  let ?N = "\<lambda> x t. Inum (x#bs) t"
  assume "?I x (rsplit f a)"
  hence "\<exists> (\<phi>,n,s) \<in> set (rsplit0 a). ?I x (And \<phi> (f n s))" using rsplit_ex by simp
  then obtain "\<phi>" "n" "s" where fnsS:"(\<phi>,n,s) \<in> set (rsplit0 a)" and "?I x (And \<phi> (f n s))" by blast
  hence \<phi>: "?I x \<phi>" and fns: "?I x (f n s)" by auto
  from rsplit0_cs[where t="a" and bs="bs" and x="x", rule_format, OF fnsS] \<phi> 
  have th: "(?N x a = ?N x (CN 0 n s)) \<and> numbound0 s" by auto
  from f[rule_format, OF th] fns show "?I x (g a)" by simp
next
  let ?I = "\<lambda>x p. Ifm (x#bs) p"
  let ?N = "\<lambda> x t. Inum (x#bs) t"
  assume ga: "?I x (g a)"
  from rsplit0_complete[OF xp x1, where bs="bs" and t="a"] 
  obtain "\<phi>" "n" "s" where fnsS:"(\<phi>,n,s) \<in> set (rsplit0 a)" and fx: "?I x \<phi>" by blast
  from rsplit0_cs[where t="a" and x="x" and bs="bs"] fnsS fx
  have ans: "?N x a = ?N x (CN 0 n s)" and nb: "numbound0 s" by auto
  with ga f have "?I x (f n s)" by auto
  with rsplit_ex fnsS fx show "?I x (rsplit f a)" by auto
qed

definition lt :: "int \<Rightarrow> num \<Rightarrow> fm" where
  lt_def: "lt c t = (if c = 0 then (Lt t) else if c > 0 then (Lt (CN 0 c t)) 
                        else (Gt (CN 0 (-c) (Neg t))))"

definition  le :: "int \<Rightarrow> num \<Rightarrow> fm" where
  le_def: "le c t = (if c = 0 then (Le t) else if c > 0 then (Le (CN 0 c t)) 
                        else (Ge (CN 0 (-c) (Neg t))))"

definition  gt :: "int \<Rightarrow> num \<Rightarrow> fm" where
  gt_def: "gt c t = (if c = 0 then (Gt t) else if c > 0 then (Gt (CN 0 c t)) 
                        else (Lt (CN 0 (-c) (Neg t))))"

definition  ge :: "int \<Rightarrow> num \<Rightarrow> fm" where
  ge_def: "ge c t = (if c = 0 then (Ge t) else if c > 0 then (Ge (CN 0 c t)) 
                        else (Le (CN 0 (-c) (Neg t))))"

definition  eq :: "int \<Rightarrow> num \<Rightarrow> fm" where
  eq_def: "eq c t = (if c = 0 then (Eq t) else if c > 0 then (Eq (CN 0 c t)) 
                        else (Eq (CN 0 (-c) (Neg t))))"

definition neq :: "int \<Rightarrow> num \<Rightarrow> fm" where
  neq_def: "neq c t = (if c = 0 then (NEq t) else if c > 0 then (NEq (CN 0 c t)) 
                        else (NEq (CN 0 (-c) (Neg t))))"

lemma lt_mono: "\<forall> a n s. Inum (x#bs) a = Inum (x#bs) (CN 0 n s) \<and> numbound0 s \<longrightarrow> Ifm (x#bs) (lt n s) = Ifm (x#bs) (Lt a)"
  (is "\<forall> a n s . ?N a = ?N (CN 0 n s) \<and> _\<longrightarrow> ?I (lt n s) = ?I (Lt a)")
proof(clarify)
  fix a n s
  assume H: "?N a = ?N (CN 0 n s)"
  show "?I (lt n s) = ?I (Lt a)" using H by (cases "n=0", (simp add: lt_def))
  (cases "n > 0", simp_all add: lt_def algebra_simps myless[of _ "0"])
qed

lemma lt_l: "isrlfm (rsplit lt a)"
  by (rule rsplit_l[where f="lt" and a="a"], auto simp add: lt_def,
    case_tac s, simp_all, case_tac "nat", simp_all)

lemma le_mono: "\<forall> a n s. Inum (x#bs) a = Inum (x#bs) (CN 0 n s) \<and> numbound0 s \<longrightarrow> Ifm (x#bs) (le n s) = Ifm (x#bs) (Le a)" (is "\<forall> a n s. ?N a = ?N (CN 0 n s) \<and> _ \<longrightarrow> ?I (le n s) = ?I (Le a)")
proof(clarify)
  fix a n s
  assume H: "?N a = ?N (CN 0 n s)"
  show "?I (le n s) = ?I (Le a)" using H by (cases "n=0", (simp add: le_def))
  (cases "n > 0", simp_all add: le_def algebra_simps myle[of _ "0"])
qed

lemma le_l: "isrlfm (rsplit le a)"
  by (rule rsplit_l[where f="le" and a="a"], auto simp add: le_def) 
(case_tac s, simp_all, case_tac "nat",simp_all)

lemma gt_mono: "\<forall> a n s. Inum (x#bs) a = Inum (x#bs) (CN 0 n s) \<and> numbound0 s \<longrightarrow> Ifm (x#bs) (gt n s) = Ifm (x#bs) (Gt a)" (is "\<forall> a n s. ?N a = ?N (CN 0 n s) \<and> _ \<longrightarrow> ?I (gt n s) = ?I (Gt a)")
proof(clarify)
  fix a n s
  assume H: "?N a = ?N (CN 0 n s)"
  show "?I (gt n s) = ?I (Gt a)" using H by (cases "n=0", (simp add: gt_def))
  (cases "n > 0", simp_all add: gt_def algebra_simps myless[of _ "0"])
qed
lemma gt_l: "isrlfm (rsplit gt a)"
  by (rule rsplit_l[where f="gt" and a="a"], auto simp add: gt_def) 
(case_tac s, simp_all, case_tac "nat", simp_all)

lemma ge_mono: "\<forall> a n s. Inum (x#bs) a = Inum (x#bs) (CN 0 n s) \<and> numbound0 s \<longrightarrow> Ifm (x#bs) (ge n s) = Ifm (x#bs) (Ge a)" (is "\<forall> a n s . ?N a = ?N (CN 0 n s) \<and> _ \<longrightarrow> ?I (ge n s) = ?I (Ge a)")
proof(clarify)
  fix a n s 
  assume H: "?N a = ?N (CN 0 n s)"
  show "?I (ge n s) = ?I (Ge a)" using H by (cases "n=0", (simp add: ge_def))
  (cases "n > 0", simp_all add: ge_def algebra_simps myle[of _ "0"])
qed
lemma ge_l: "isrlfm (rsplit ge a)"
  by (rule rsplit_l[where f="ge" and a="a"], auto simp add: ge_def) 
(case_tac s, simp_all, case_tac "nat", simp_all)

lemma eq_mono: "\<forall> a n s. Inum (x#bs) a = Inum (x#bs) (CN 0 n s) \<and> numbound0 s \<longrightarrow> Ifm (x#bs) (eq n s) = Ifm (x#bs) (Eq a)" (is "\<forall> a n s. ?N a = ?N (CN 0 n s) \<and> _ \<longrightarrow> ?I (eq n s) = ?I (Eq a)")
proof(clarify)
  fix a n s 
  assume H: "?N a = ?N (CN 0 n s)"
  show "?I (eq n s) = ?I (Eq a)" using H by (auto simp add: eq_def algebra_simps)
qed
lemma eq_l: "isrlfm (rsplit eq a)"
  by (rule rsplit_l[where f="eq" and a="a"], auto simp add: eq_def) 
(case_tac s, simp_all, case_tac"nat", simp_all)

lemma neq_mono: "\<forall> a n s. Inum (x#bs) a = Inum (x#bs) (CN 0 n s) \<and> numbound0 s \<longrightarrow> Ifm (x#bs) (neq n s) = Ifm (x#bs) (NEq a)" (is "\<forall> a n s. ?N a = ?N (CN 0 n s) \<and> _ \<longrightarrow> ?I (neq n s) = ?I (NEq a)")
proof(clarify)
  fix a n s bs
  assume H: "?N a = ?N (CN 0 n s)"
  show "?I (neq n s) = ?I (NEq a)" using H by (auto simp add: neq_def algebra_simps)
qed

lemma neq_l: "isrlfm (rsplit neq a)"
  by (rule rsplit_l[where f="neq" and a="a"], auto simp add: neq_def) 
(case_tac s, simp_all, case_tac"nat", simp_all)

lemma small_le: 
  assumes u0:"0 \<le> u" and u1: "u < 1"
  shows "(-u \<le> real (n::int)) = (0 \<le> n)"
using u0 u1  by auto

lemma small_lt: 
  assumes u0:"0 \<le> u" and u1: "u < 1"
  shows "(real (n::int) < real (m::int) - u) = (n < m)"
using u0 u1  by auto

lemma rdvd01_cs: 
  assumes up: "u \<ge> 0" and u1: "u<1" and np: "real n > 0"
  shows "(real (i::int) rdvd real (n::int) * u - s) = (\<exists> j\<in> {0 .. n - 1}. real n * u = s - real (floor s) + real j \<and> real i rdvd real (j - floor s))" (is "?lhs = ?rhs")
proof-
  let ?ss = "s - real (floor s)"
  from real_of_int_floor_add_one_gt[where r="s", simplified myless[of "s"]] 
    real_of_int_floor_le[where r="s"]  have ss0:"?ss \<ge> 0" and ss1:"?ss < 1" 
    by (auto simp add: myle[of _ "s", symmetric] myless[of "?ss"])
  from np have n0: "real n \<ge> 0" by simp
  from mult_left_mono[OF up n0] mult_strict_left_mono[OF u1 np] 
  have nu0:"real n * u - s \<ge> -s" and nun:"real n * u -s < real n - s" by auto  
  from int_rdvd_real[where i="i" and x="real (n::int) * u - s"] 
  have "real i rdvd real n * u - s = 
    (i dvd floor (real n * u -s) \<and> (real (floor (real n * u - s)) = real n * u - s ))" 
    (is "_ = (?DE)" is "_ = (?D \<and> ?E)") by simp
  also have "\<dots> = (?DE \<and> real(floor (real n * u - s) + floor s)\<ge> -?ss 
    \<and> real(floor (real n * u - s) + floor s)< real n - ?ss)" (is "_=(?DE \<and>real ?a \<ge> _ \<and> real ?a < _)")
    using nu0 nun  by auto
  also have "\<dots> = (?DE \<and> ?a \<ge> 0 \<and> ?a < n)" by(simp only: small_le[OF ss0 ss1] small_lt[OF ss0 ss1])
  also have "\<dots> = (?DE \<and> (\<exists> j\<in> {0 .. (n - 1)}. ?a = j))" by simp
  also have "\<dots> = (?DE \<and> (\<exists> j\<in> {0 .. (n - 1)}. real (\<lfloor>real n * u - s\<rfloor>) = real j - real \<lfloor>s\<rfloor> ))"
    by (simp only: algebra_simps real_of_int_diff[symmetric] real_of_int_inject del: real_of_int_diff)
  also have "\<dots> = ((\<exists> j\<in> {0 .. (n - 1)}. real n * u - s = real j - real \<lfloor>s\<rfloor> \<and> real i rdvd real n * u - s))" using int_rdvd_iff[where i="i" and t="\<lfloor>real n * u - s\<rfloor>"]
    by (auto cong: conj_cong)
  also have "\<dots> = ?rhs" by(simp cong: conj_cong) (simp add: algebra_simps )
  finally show ?thesis .
qed

definition
  DVDJ:: "int \<Rightarrow> int \<Rightarrow> num \<Rightarrow> fm"
where
  DVDJ_def: "DVDJ i n s = (foldr disj (map (\<lambda> j. conj (Eq (CN 0 n (Add s (Sub (Floor (Neg s)) (C j))))) (Dvd i (Sub (C j) (Floor (Neg s))))) [0..n - 1]) F)"

definition
  NDVDJ:: "int \<Rightarrow> int \<Rightarrow> num \<Rightarrow> fm"
where
  NDVDJ_def: "NDVDJ i n s = (foldr conj (map (\<lambda> j. disj (NEq (CN 0 n (Add s (Sub (Floor (Neg s)) (C j))))) (NDvd i (Sub (C j) (Floor (Neg s))))) [0..n - 1]) T)"

lemma DVDJ_DVD: 
  assumes xp:"x\<ge> 0" and x1: "x < 1" and np:"real n > 0"
  shows "Ifm (x#bs) (DVDJ i n s) = Ifm (x#bs) (Dvd i (CN 0 n s))"
proof-
  let ?f = "\<lambda> j. conj (Eq(CN 0 n (Add s (Sub(Floor (Neg s)) (C j))))) (Dvd i (Sub (C j) (Floor (Neg s))))"
  let ?s= "Inum (x#bs) s"
  from foldr_disj_map[where xs="[0..n - 1]" and bs="x#bs" and f="?f"]
  have "Ifm (x#bs) (DVDJ i n s) = (\<exists> j\<in> {0 .. (n - 1)}. Ifm (x#bs) (?f j))" 
    by (simp add: np DVDJ_def)
  also have "\<dots> = (\<exists> j\<in> {0 .. (n - 1)}. real n * x = (- ?s) - real (floor (- ?s)) + real j \<and> real i rdvd real (j - floor (- ?s)))" by (simp add: algebra_simps diff_minus[symmetric])
  also from rdvd01_cs[OF xp x1 np, where i="i" and s="-?s"] 
  have "\<dots> = (real i rdvd real n * x - (-?s))" by simp
  finally show ?thesis by simp
qed

lemma NDVDJ_NDVD: 
  assumes xp:"x\<ge> 0" and x1: "x < 1" and np:"real n > 0"
  shows "Ifm (x#bs) (NDVDJ i n s) = Ifm (x#bs) (NDvd i (CN 0 n s))"
proof-
  let ?f = "\<lambda> j. disj(NEq(CN 0 n (Add s (Sub (Floor (Neg s)) (C j))))) (NDvd i (Sub (C j) (Floor(Neg s))))"
  let ?s= "Inum (x#bs) s"
  from foldr_conj_map[where xs="[0..n - 1]" and bs="x#bs" and f="?f"]
  have "Ifm (x#bs) (NDVDJ i n s) = (\<forall> j\<in> {0 .. (n - 1)}. Ifm (x#bs) (?f j))" 
    by (simp add: np NDVDJ_def)
  also have "\<dots> = (\<not> (\<exists> j\<in> {0 .. (n - 1)}. real n * x = (- ?s) - real (floor (- ?s)) + real j \<and> real i rdvd real (j - floor (- ?s))))" by (simp add: algebra_simps diff_minus[symmetric])
  also from rdvd01_cs[OF xp x1 np, where i="i" and s="-?s"] 
  have "\<dots> = (\<not> (real i rdvd real n * x - (-?s)))" by simp
  finally show ?thesis by simp
qed  

lemma foldr_disj_map_rlfm2: 
  assumes lf: "\<forall> n . isrlfm (f n)"
  shows "isrlfm (foldr disj (map f xs) F)"
using lf by (induct xs, auto)
lemma foldr_And_map_rlfm2: 
  assumes lf: "\<forall> n . isrlfm (f n)"
  shows "isrlfm (foldr conj (map f xs) T)"
using lf by (induct xs, auto)

lemma DVDJ_l: assumes ip: "i >0" and np: "n>0" and nb: "numbound0 s"
  shows "isrlfm (DVDJ i n s)"
proof-
  let ?f="\<lambda>j. conj (Eq (CN 0 n (Add s (Sub (Floor (Neg s)) (C j)))))
                         (Dvd i (Sub (C j) (Floor (Neg s))))"
  have th: "\<forall> j. isrlfm (?f j)" using nb np by auto
  from DVDJ_def foldr_disj_map_rlfm2[OF th] show ?thesis by simp 
qed

lemma NDVDJ_l: assumes ip: "i >0" and np: "n>0" and nb: "numbound0 s"
  shows "isrlfm (NDVDJ i n s)"
proof-
  let ?f="\<lambda>j. disj (NEq (CN 0 n (Add s (Sub (Floor (Neg s)) (C j)))))
                      (NDvd i (Sub (C j) (Floor (Neg s))))"
  have th: "\<forall> j. isrlfm (?f j)" using nb np by auto
  from NDVDJ_def foldr_And_map_rlfm2[OF th] show ?thesis by auto
qed

definition DVD :: "int \<Rightarrow> int \<Rightarrow> num \<Rightarrow> fm" where
  DVD_def: "DVD i c t =
  (if i=0 then eq c t else 
  if c = 0 then (Dvd i t) else if c >0 then DVDJ (abs i) c t else DVDJ (abs i) (-c) (Neg t))"

definition  NDVD :: "int \<Rightarrow> int \<Rightarrow> num \<Rightarrow> fm" where
  "NDVD i c t =
  (if i=0 then neq c t else 
  if c = 0 then (NDvd i t) else if c >0 then NDVDJ (abs i) c t else NDVDJ (abs i) (-c) (Neg t))"

lemma DVD_mono: 
  assumes xp: "0\<le> x" and x1: "x < 1" 
  shows "\<forall> a n s. Inum (x#bs) a = Inum (x#bs) (CN 0 n s) \<and> numbound0 s \<longrightarrow> Ifm (x#bs) (DVD i n s) = Ifm (x#bs) (Dvd i a)"
  (is "\<forall> a n s. ?N a = ?N (CN 0 n s) \<and> _ \<longrightarrow> ?I (DVD i n s) = ?I (Dvd i a)")
proof(clarify)
  fix a n s 
  assume H: "?N a = ?N (CN 0 n s)" and nb: "numbound0 s"
  let ?th = "?I (DVD i n s) = ?I (Dvd i a)"
  have "i=0 \<or> (i\<noteq>0 \<and> n=0) \<or> (i\<noteq>0 \<and> n < 0) \<or> (i\<noteq>0 \<and> n > 0)" by arith
  moreover {assume iz: "i=0" hence ?th using eq_mono[rule_format, OF conjI[OF H nb]] 
      by (simp add: DVD_def rdvd_left_0_eq)}
  moreover {assume inz: "i\<noteq>0" and "n=0" hence ?th by (simp add: H DVD_def) } 
  moreover {assume inz: "i\<noteq>0" and "n<0" hence ?th 
      by (simp add: DVD_def H DVDJ_DVD[OF xp x1] rdvd_abs1 
        rdvd_minus[where d="i" and t="real n * x + Inum (x # bs) s"]) } 
  moreover {assume inz: "i\<noteq>0" and "n>0" hence ?th by (simp add:DVD_def H DVDJ_DVD[OF xp x1] rdvd_abs1)}
  ultimately show ?th by blast
qed

lemma NDVD_mono:   assumes xp: "0\<le> x" and x1: "x < 1" 
  shows "\<forall> a n s. Inum (x#bs) a = Inum (x#bs) (CN 0 n s) \<and> numbound0 s \<longrightarrow> Ifm (x#bs) (NDVD i n s) = Ifm (x#bs) (NDvd i a)"
  (is "\<forall> a n s. ?N a = ?N (CN 0 n s) \<and> _ \<longrightarrow> ?I (NDVD i n s) = ?I (NDvd i a)")
proof(clarify)
  fix a n s 
  assume H: "?N a = ?N (CN 0 n s)" and nb: "numbound0 s"
  let ?th = "?I (NDVD i n s) = ?I (NDvd i a)"
  have "i=0 \<or> (i\<noteq>0 \<and> n=0) \<or> (i\<noteq>0 \<and> n < 0) \<or> (i\<noteq>0 \<and> n > 0)" by arith
  moreover {assume iz: "i=0" hence ?th using neq_mono[rule_format, OF conjI[OF H nb]] 
      by (simp add: NDVD_def rdvd_left_0_eq)}
  moreover {assume inz: "i\<noteq>0" and "n=0" hence ?th by (simp add: H NDVD_def) } 
  moreover {assume inz: "i\<noteq>0" and "n<0" hence ?th 
      by (simp add: NDVD_def H NDVDJ_NDVD[OF xp x1] rdvd_abs1 
        rdvd_minus[where d="i" and t="real n * x + Inum (x # bs) s"]) } 
  moreover {assume inz: "i\<noteq>0" and "n>0" hence ?th 
      by (simp add:NDVD_def H NDVDJ_NDVD[OF xp x1] rdvd_abs1)}
  ultimately show ?th by blast
qed

lemma DVD_l: "isrlfm (rsplit (DVD i) a)"
  by (rule rsplit_l[where f="DVD i" and a="a"], auto simp add: DVD_def eq_def DVDJ_l) 
(case_tac s, simp_all, case_tac "nat", simp_all)

lemma NDVD_l: "isrlfm (rsplit (NDVD i) a)"
  by (rule rsplit_l[where f="NDVD i" and a="a"], auto simp add: NDVD_def neq_def NDVDJ_l) 
(case_tac s, simp_all, case_tac "nat", simp_all)

consts rlfm :: "fm \<Rightarrow> fm"
recdef rlfm "measure fmsize"
  "rlfm (And p q) = conj (rlfm p) (rlfm q)"
  "rlfm (Or p q) = disj (rlfm p) (rlfm q)"
  "rlfm (Imp p q) = disj (rlfm (NOT p)) (rlfm q)"
  "rlfm (Iff p q) = disj (conj(rlfm p) (rlfm q)) (conj(rlfm (NOT p)) (rlfm (NOT q)))"
  "rlfm (Lt a) = rsplit lt a"
  "rlfm (Le a) = rsplit le a"
  "rlfm (Gt a) = rsplit gt a"
  "rlfm (Ge a) = rsplit ge a"
  "rlfm (Eq a) = rsplit eq a"
  "rlfm (NEq a) = rsplit neq a"
  "rlfm (Dvd i a) = rsplit (\<lambda> t. DVD i t) a"
  "rlfm (NDvd i a) = rsplit (\<lambda> t. NDVD i t) a"
  "rlfm (NOT (And p q)) = disj (rlfm (NOT p)) (rlfm (NOT q))"
  "rlfm (NOT (Or p q)) = conj (rlfm (NOT p)) (rlfm (NOT q))"
  "rlfm (NOT (Imp p q)) = conj (rlfm p) (rlfm (NOT q))"
  "rlfm (NOT (Iff p q)) = disj (conj(rlfm p) (rlfm(NOT q))) (conj(rlfm(NOT p)) (rlfm q))"
  "rlfm (NOT (NOT p)) = rlfm p"
  "rlfm (NOT T) = F"
  "rlfm (NOT F) = T"
  "rlfm (NOT (Lt a)) = simpfm (rlfm (Ge a))"
  "rlfm (NOT (Le a)) = simpfm (rlfm (Gt a))"
  "rlfm (NOT (Gt a)) = simpfm (rlfm (Le a))"
  "rlfm (NOT (Ge a)) = simpfm (rlfm (Lt a))"
  "rlfm (NOT (Eq a)) = simpfm (rlfm (NEq a))"
  "rlfm (NOT (NEq a)) = simpfm (rlfm (Eq a))"
  "rlfm (NOT (Dvd i a)) = simpfm (rlfm (NDvd i a))"
  "rlfm (NOT (NDvd i a)) = simpfm (rlfm (Dvd i a))"
  "rlfm p = p" (hints simp add: fmsize_pos)

lemma bound0at_l : "\<lbrakk>isatom p ; bound0 p\<rbrakk> \<Longrightarrow> isrlfm p"
  by (induct p rule: isrlfm.induct, auto)

lemma simpfm_rl: "isrlfm p \<Longrightarrow> isrlfm (simpfm p)"
proof (induct p)
  case (Lt a) 
  hence "bound0 (Lt a) \<or> (\<exists> c e. a = CN 0 c e \<and> c > 0 \<and> numbound0 e)"
    by (cases a,simp_all, case_tac "nat", simp_all)
  moreover
  {assume "bound0 (Lt a)" hence bn:"bound0 (simpfm (Lt a))"  
      using simpfm_bound0 by blast
    have "isatom (simpfm (Lt a))" by (cases "simpnum a", auto simp add: Let_def)
    with bn bound0at_l have ?case by blast}
  moreover 
  { fix c e assume a: "a = CN 0 c e" and "c>0" and "numbound0 e"
    { assume cn1:"numgcd (CN 0 c (simpnum e)) \<noteq> 1" and cnz:"numgcd (CN 0 c (simpnum e)) \<noteq> 0"
      with numgcd_pos[where t="CN 0 c (simpnum e)"]
      have th1:"numgcd (CN 0 c (simpnum e)) > 0" by simp
      from `c > 0` have th:"numgcd (CN 0 c (simpnum e)) \<le> c" 
        by (simp add: numgcd_def)
      from `c > 0` have th': "c\<noteq>0" by auto
      from `c > 0` have cp: "c \<ge> 0" by simp
      from zdiv_mono2[OF cp th1 th, simplified div_self[OF th']]
      have "0 < c div numgcd (CN 0 c (simpnum e))" by simp
    }
    with Lt a have ?case
      by (simp add: Let_def reducecoeff_def reducecoeffh_numbound0)}
  ultimately show ?case by blast
next
  case (Le a)   
  hence "bound0 (Le a) \<or> (\<exists> c e. a = CN 0 c e \<and> c > 0 \<and> numbound0 e)"
    by (cases a,simp_all, case_tac "nat", simp_all)
  moreover
  { assume "bound0 (Le a)" hence bn:"bound0 (simpfm (Le a))"  
      using simpfm_bound0 by blast
    have "isatom (simpfm (Le a))" by (cases "simpnum a", auto simp add: Let_def)
    with bn bound0at_l have ?case by blast}
  moreover 
  { fix c e assume a: "a = CN 0 c e" and "c>0" and "numbound0 e"
    { assume cn1:"numgcd (CN 0 c (simpnum e)) \<noteq> 1" and cnz:"numgcd (CN 0 c (simpnum e)) \<noteq> 0"
      with numgcd_pos[where t="CN 0 c (simpnum e)"]
      have th1:"numgcd (CN 0 c (simpnum e)) > 0" by simp
      from `c > 0` have th:"numgcd (CN 0 c (simpnum e)) \<le> c" 
        by (simp add: numgcd_def)
      from `c > 0` have th': "c\<noteq>0" by auto
      from `c > 0` have cp: "c \<ge> 0" by simp
      from zdiv_mono2[OF cp th1 th, simplified div_self[OF th']]
      have "0 < c div numgcd (CN 0 c (simpnum e))" by simp
    }
    with Le a have ?case
      by (simp add: Let_def reducecoeff_def simpnum_numbound0 reducecoeffh_numbound0)}
  ultimately show ?case by blast
next
  case (Gt a)   
  hence "bound0 (Gt a) \<or> (\<exists> c e. a = CN 0 c e \<and> c > 0 \<and> numbound0 e)"
    by (cases a,simp_all, case_tac "nat", simp_all)
  moreover
  {assume "bound0 (Gt a)" hence bn:"bound0 (simpfm (Gt a))"  
      using simpfm_bound0 by blast
    have "isatom (simpfm (Gt a))" by (cases "simpnum a", auto simp add: Let_def)
    with bn bound0at_l have ?case by blast}
  moreover 
  { fix c e assume a: "a = CN 0 c e" and "c>0" and "numbound0 e"
    { assume cn1: "numgcd (CN 0 c (simpnum e)) \<noteq> 1" and cnz:"numgcd (CN 0 c (simpnum e)) \<noteq> 0"
      with numgcd_pos[where t="CN 0 c (simpnum e)"]
      have th1:"numgcd (CN 0 c (simpnum e)) > 0" by simp
      from `c > 0` have th:"numgcd (CN 0 c (simpnum e)) \<le> c" 
        by (simp add: numgcd_def)
      from `c > 0` have th': "c\<noteq>0" by auto
      from `c > 0` have cp: "c \<ge> 0" by simp
      from zdiv_mono2[OF cp th1 th, simplified div_self[OF th']]
      have "0 < c div numgcd (CN 0 c (simpnum e))" by simp
    }
    with Gt a have ?case
      by (simp add: Let_def reducecoeff_def simpnum_numbound0 reducecoeffh_numbound0)}
  ultimately show ?case by blast
next
  case (Ge a)   
  hence "bound0 (Ge a) \<or> (\<exists> c e. a = CN 0 c e \<and> c > 0 \<and> numbound0 e)"
    by (cases a,simp_all, case_tac "nat", simp_all)
  moreover
  { assume "bound0 (Ge a)" hence bn:"bound0 (simpfm (Ge a))"  
      using simpfm_bound0 by blast
    have "isatom (simpfm (Ge a))" by (cases "simpnum a", auto simp add: Let_def)
    with bn bound0at_l have ?case by blast}
  moreover 
  { fix c e assume a: "a = CN 0 c e" and "c>0" and "numbound0 e"
    { assume cn1:"numgcd (CN 0 c (simpnum e)) \<noteq> 1" and cnz:"numgcd (CN 0 c (simpnum e)) \<noteq> 0"
      with numgcd_pos[where t="CN 0 c (simpnum e)"]
      have th1:"numgcd (CN 0 c (simpnum e)) > 0" by simp
      from `c > 0` have th:"numgcd (CN 0 c (simpnum e)) \<le> c" 
        by (simp add: numgcd_def)
      from `c > 0` have th': "c\<noteq>0" by auto
      from `c > 0` have cp: "c \<ge> 0" by simp
      from zdiv_mono2[OF cp th1 th, simplified div_self[OF th']]
      have "0 < c div numgcd (CN 0 c (simpnum e))" by simp
    }
    with Ge a have ?case
      by (simp add: Let_def reducecoeff_def simpnum_numbound0 reducecoeffh_numbound0)}
  ultimately show ?case by blast
next
  case (Eq a)   
  hence "bound0 (Eq a) \<or> (\<exists> c e. a = CN 0 c e \<and> c > 0 \<and> numbound0 e)"
    by (cases a,simp_all, case_tac "nat", simp_all)
  moreover
  { assume "bound0 (Eq a)" hence bn:"bound0 (simpfm (Eq a))"  
      using simpfm_bound0 by blast
    have "isatom (simpfm (Eq a))" by (cases "simpnum a", auto simp add: Let_def)
    with bn bound0at_l have ?case by blast}
  moreover 
  { fix c e assume a: "a = CN 0 c e" and "c>0" and "numbound0 e"
    { assume cn1:"numgcd (CN 0 c (simpnum e)) \<noteq> 1" and cnz:"numgcd (CN 0 c (simpnum e)) \<noteq> 0"
      with numgcd_pos[where t="CN 0 c (simpnum e)"]
      have th1:"numgcd (CN 0 c (simpnum e)) > 0" by simp
      from `c > 0` have th:"numgcd (CN 0 c (simpnum e)) \<le> c" 
        by (simp add: numgcd_def)
      from `c > 0` have th': "c\<noteq>0" by auto
      from `c > 0` have cp: "c \<ge> 0" by simp
      from zdiv_mono2[OF cp th1 th, simplified div_self[OF th']]
      have "0 < c div numgcd (CN 0 c (simpnum e))" by simp
    }
    with Eq a have ?case
      by (simp add: Let_def reducecoeff_def simpnum_numbound0 reducecoeffh_numbound0)}
  ultimately show ?case by blast
next
  case (NEq a)  
  hence "bound0 (NEq a) \<or> (\<exists> c e. a = CN 0 c e \<and> c > 0 \<and> numbound0 e)"
    by (cases a,simp_all, case_tac "nat", simp_all)
  moreover
  {assume "bound0 (NEq a)" hence bn:"bound0 (simpfm (NEq a))"  
      using simpfm_bound0 by blast
    have "isatom (simpfm (NEq a))" by (cases "simpnum a", auto simp add: Let_def)
    with bn bound0at_l have ?case by blast}
  moreover 
  { fix c e assume a: "a = CN 0 c e" and "c>0" and "numbound0 e"
    { assume cn1:"numgcd (CN 0 c (simpnum e)) \<noteq> 1" and cnz:"numgcd (CN 0 c (simpnum e)) \<noteq> 0"
      with numgcd_pos[where t="CN 0 c (simpnum e)"]
      have th1:"numgcd (CN 0 c (simpnum e)) > 0" by simp
      from `c > 0` have th:"numgcd (CN 0 c (simpnum e)) \<le> c" 
        by (simp add: numgcd_def)
      from `c > 0` have th': "c\<noteq>0" by auto
      from `c > 0` have cp: "c \<ge> 0" by simp
      from zdiv_mono2[OF cp th1 th, simplified div_self[OF th']]
      have "0 < c div numgcd (CN 0 c (simpnum e))" by simp
    }
    with NEq a have ?case
      by (simp add: Let_def reducecoeff_def simpnum_numbound0 reducecoeffh_numbound0)}
  ultimately show ?case by blast
next
  case (Dvd i a) hence "bound0 (Dvd i a)" by auto hence bn:"bound0 (simpfm (Dvd i a))"  
    using simpfm_bound0 by blast
  have "isatom (simpfm (Dvd i a))" by (cases "simpnum a", auto simp add: Let_def split_def)
  with bn bound0at_l show ?case by blast
next
  case (NDvd i a)  hence "bound0 (NDvd i a)" by auto hence bn:"bound0 (simpfm (NDvd i a))"  
    using simpfm_bound0 by blast
  have "isatom (simpfm (NDvd i a))" by (cases "simpnum a", auto simp add: Let_def split_def)
  with bn bound0at_l show ?case by blast
qed(auto simp add: conj_def imp_def disj_def iff_def Let_def simpfm_bound0 numadd_nb numneg_nb)

lemma rlfm_I:
  assumes qfp: "qfree p"
  and xp: "0 \<le> x" and x1: "x < 1"
  shows "(Ifm (x#bs) (rlfm p) = Ifm (x# bs) p) \<and> isrlfm (rlfm p)"
  using qfp 
by (induct p rule: rlfm.induct) 
(auto simp add: rsplit[OF xp x1 lt_mono] lt_l rsplit[OF xp x1 le_mono] le_l rsplit[OF xp x1 gt_mono] gt_l
               rsplit[OF xp x1 ge_mono] ge_l rsplit[OF xp x1 eq_mono] eq_l rsplit[OF xp x1 neq_mono] neq_l
               rsplit[OF xp x1 DVD_mono[OF xp x1]] DVD_l rsplit[OF xp x1 NDVD_mono[OF xp x1]] NDVD_l simpfm_rl)
lemma rlfm_l:
  assumes qfp: "qfree p"
  shows "isrlfm (rlfm p)"
  using qfp lt_l gt_l ge_l le_l eq_l neq_l DVD_l NDVD_l 
by (induct p rule: rlfm.induct,auto simp add: simpfm_rl)

    (* Operations needed for Ferrante and Rackoff *)
lemma rminusinf_inf:
  assumes lp: "isrlfm p"
  shows "\<exists> z. \<forall> x < z. Ifm (x#bs) (minusinf p) = Ifm (x#bs) p" (is "\<exists> z. \<forall> x. ?P z x p")
using lp
proof (induct p rule: minusinf.induct)
  case (1 p q) thus ?case by (auto,rule_tac x= "min z za" in exI) auto
next
  case (2 p q) thus ?case by (auto,rule_tac x= "min z za" in exI) auto
next
  case (3 c e) 
  from 3 have nb: "numbound0 e" by simp
  from 3 have cp: "real c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real c"
  {fix x
    assume xz: "x < ?z"
    hence "(real c * x < - ?e)" 
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] mult_ac) 
    hence "real c * x + ?e < 0" by arith
    hence "real c * x + ?e \<noteq> 0" by simp
    with xz have "?P ?z x (Eq (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp  }
  hence "\<forall> x < ?z. ?P ?z x (Eq (CN 0 c e))" by simp
  thus ?case by blast
next
  case (4 c e)   
  from 4 have nb: "numbound0 e" by simp
  from 4 have cp: "real c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real c"
  {fix x
    assume xz: "x < ?z"
    hence "(real c * x < - ?e)" 
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] mult_ac) 
    hence "real c * x + ?e < 0" by arith
    hence "real c * x + ?e \<noteq> 0" by simp
    with xz have "?P ?z x (NEq (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp }
  hence "\<forall> x < ?z. ?P ?z x (NEq (CN 0 c e))" by simp
  thus ?case by blast
next
  case (5 c e) 
  from 5 have nb: "numbound0 e" by simp
  from 5 have cp: "real c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real c"
  {fix x
    assume xz: "x < ?z"
    hence "(real c * x < - ?e)" 
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] mult_ac) 
    hence "real c * x + ?e < 0" by arith
    with xz have "?P ?z x (Lt (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"]  by simp }
  hence "\<forall> x < ?z. ?P ?z x (Lt (CN 0 c e))" by simp
  thus ?case by blast
next
  case (6 c e)  
  from 6 have nb: "numbound0 e" by simp
  from 6 have cp: "real c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real c"
  {fix x
    assume xz: "x < ?z"
    hence "(real c * x < - ?e)" 
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] mult_ac) 
    hence "real c * x + ?e < 0" by arith
    with xz have "?P ?z x (Le (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp }
  hence "\<forall> x < ?z. ?P ?z x (Le (CN 0 c e))" by simp
  thus ?case by blast
next
  case (7 c e)  
  from 7 have nb: "numbound0 e" by simp
  from 7 have cp: "real c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real c"
  {fix x
    assume xz: "x < ?z"
    hence "(real c * x < - ?e)" 
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] mult_ac) 
    hence "real c * x + ?e < 0" by arith
    with xz have "?P ?z x (Gt (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp }
  hence "\<forall> x < ?z. ?P ?z x (Gt (CN 0 c e))" by simp
  thus ?case by blast
next
  case (8 c e)  
  from 8 have nb: "numbound0 e" by simp
  from 8 have cp: "real c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real c"
  {fix x
    assume xz: "x < ?z"
    hence "(real c * x < - ?e)" 
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] mult_ac) 
    hence "real c * x + ?e < 0" by arith
    with xz have "?P ?z x (Ge (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp }
  hence "\<forall> x < ?z. ?P ?z x (Ge (CN 0 c e))" by simp
  thus ?case by blast
qed simp_all

lemma rplusinf_inf:
  assumes lp: "isrlfm p"
  shows "\<exists> z. \<forall> x > z. Ifm (x#bs) (plusinf p) = Ifm (x#bs) p" (is "\<exists> z. \<forall> x. ?P z x p")
using lp
proof (induct p rule: isrlfm.induct)
  case (1 p q) thus ?case by (auto,rule_tac x= "max z za" in exI) auto
next
  case (2 p q) thus ?case by (auto,rule_tac x= "max z za" in exI) auto
next
  case (3 c e) 
  from 3 have nb: "numbound0 e" by simp
  from 3 have cp: "real c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real c"
  {fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real c * x > - ?e)" by (simp add: mult_ac)
    hence "real c * x + ?e > 0" by arith
    hence "real c * x + ?e \<noteq> 0" by simp
    with xz have "?P ?z x (Eq (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp }
  hence "\<forall> x > ?z. ?P ?z x (Eq (CN 0 c e))" by simp
  thus ?case by blast
next
  case (4 c e) 
  from 4 have nb: "numbound0 e" by simp
  from 4 have cp: "real c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real c"
  {fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real c * x > - ?e)" by (simp add: mult_ac)
    hence "real c * x + ?e > 0" by arith
    hence "real c * x + ?e \<noteq> 0" by simp
    with xz have "?P ?z x (NEq (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp }
  hence "\<forall> x > ?z. ?P ?z x (NEq (CN 0 c e))" by simp
  thus ?case by blast
next
  case (5 c e) 
  from 5 have nb: "numbound0 e" by simp
  from 5 have cp: "real c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real c"
  {fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real c * x > - ?e)" by (simp add: mult_ac)
    hence "real c * x + ?e > 0" by arith
    with xz have "?P ?z x (Lt (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp }
  hence "\<forall> x > ?z. ?P ?z x (Lt (CN 0 c e))" by simp
  thus ?case by blast
next
  case (6 c e) 
  from 6 have nb: "numbound0 e" by simp
  from 6 have cp: "real c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real c"
  {fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real c * x > - ?e)" by (simp add: mult_ac)
    hence "real c * x + ?e > 0" by arith
    with xz have "?P ?z x (Le (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp }
  hence "\<forall> x > ?z. ?P ?z x (Le (CN 0 c e))" by simp
  thus ?case by blast
next
  case (7 c e) 
  from 7 have nb: "numbound0 e" by simp
  from 7 have cp: "real c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real c"
  {fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real c * x > - ?e)" by (simp add: mult_ac)
    hence "real c * x + ?e > 0" by arith
    with xz have "?P ?z x (Gt (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp }
  hence "\<forall> x > ?z. ?P ?z x (Gt (CN 0 c e))" by simp
  thus ?case by blast
next
  case (8 c e) 
  from 8 have nb: "numbound0 e" by simp
  from 8 have cp: "real c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real c"
  {fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real c * x > - ?e)" by (simp add: mult_ac)
    hence "real c * x + ?e > 0" by arith
    with xz have "?P ?z x (Ge (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"]   by simp }
  hence "\<forall> x > ?z. ?P ?z x (Ge (CN 0 c e))" by simp
  thus ?case by blast
qed simp_all

lemma rminusinf_bound0:
  assumes lp: "isrlfm p"
  shows "bound0 (minusinf p)"
  using lp
  by (induct p rule: minusinf.induct) simp_all

lemma rplusinf_bound0:
  assumes lp: "isrlfm p"
  shows "bound0 (plusinf p)"
  using lp
  by (induct p rule: plusinf.induct) simp_all

lemma rminusinf_ex:
  assumes lp: "isrlfm p"
  and ex: "Ifm (a#bs) (minusinf p)"
  shows "\<exists> x. Ifm (x#bs) p"
proof-
  from bound0_I [OF rminusinf_bound0[OF lp], where b="a" and bs ="bs"] ex
  have th: "\<forall> x. Ifm (x#bs) (minusinf p)" by auto
  from rminusinf_inf[OF lp, where bs="bs"] 
  obtain z where z_def: "\<forall>x<z. Ifm (x # bs) (minusinf p) = Ifm (x # bs) p" by blast
  from th have "Ifm ((z - 1)#bs) (minusinf p)" by simp
  moreover have "z - 1 < z" by simp
  ultimately show ?thesis using z_def by auto
qed

lemma rplusinf_ex:
  assumes lp: "isrlfm p"
  and ex: "Ifm (a#bs) (plusinf p)"
  shows "\<exists> x. Ifm (x#bs) p"
proof-
  from bound0_I [OF rplusinf_bound0[OF lp], where b="a" and bs ="bs"] ex
  have th: "\<forall> x. Ifm (x#bs) (plusinf p)" by auto
  from rplusinf_inf[OF lp, where bs="bs"] 
  obtain z where z_def: "\<forall>x>z. Ifm (x # bs) (plusinf p) = Ifm (x # bs) p" by blast
  from th have "Ifm ((z + 1)#bs) (plusinf p)" by simp
  moreover have "z + 1 > z" by simp
  ultimately show ?thesis using z_def by auto
qed

consts 
  \<Upsilon>:: "fm \<Rightarrow> (num \<times> int) list"
  \<upsilon> :: "fm \<Rightarrow> (num \<times> int) \<Rightarrow> fm "
recdef \<Upsilon> "measure size"
  "\<Upsilon> (And p q) = (\<Upsilon> p @ \<Upsilon> q)" 
  "\<Upsilon> (Or p q) = (\<Upsilon> p @ \<Upsilon> q)" 
  "\<Upsilon> (Eq  (CN 0 c e)) = [(Neg e,c)]"
  "\<Upsilon> (NEq (CN 0 c e)) = [(Neg e,c)]"
  "\<Upsilon> (Lt  (CN 0 c e)) = [(Neg e,c)]"
  "\<Upsilon> (Le  (CN 0 c e)) = [(Neg e,c)]"
  "\<Upsilon> (Gt  (CN 0 c e)) = [(Neg e,c)]"
  "\<Upsilon> (Ge  (CN 0 c e)) = [(Neg e,c)]"
  "\<Upsilon> p = []"

recdef \<upsilon> "measure size"
  "\<upsilon> (And p q) = (\<lambda> (t,n). And (\<upsilon> p (t,n)) (\<upsilon> q (t,n)))"
  "\<upsilon> (Or p q) = (\<lambda> (t,n). Or (\<upsilon> p (t,n)) (\<upsilon> q (t,n)))"
  "\<upsilon> (Eq (CN 0 c e)) = (\<lambda> (t,n). Eq (Add (Mul c t) (Mul n e)))"
  "\<upsilon> (NEq (CN 0 c e)) = (\<lambda> (t,n). NEq (Add (Mul c t) (Mul n e)))"
  "\<upsilon> (Lt (CN 0 c e)) = (\<lambda> (t,n). Lt (Add (Mul c t) (Mul n e)))"
  "\<upsilon> (Le (CN 0 c e)) = (\<lambda> (t,n). Le (Add (Mul c t) (Mul n e)))"
  "\<upsilon> (Gt (CN 0 c e)) = (\<lambda> (t,n). Gt (Add (Mul c t) (Mul n e)))"
  "\<upsilon> (Ge (CN 0 c e)) = (\<lambda> (t,n). Ge (Add (Mul c t) (Mul n e)))"
  "\<upsilon> p = (\<lambda> (t,n). p)"

lemma \<upsilon>_I: assumes lp: "isrlfm p"
  and np: "real n > 0" and nbt: "numbound0 t"
  shows "(Ifm (x#bs) (\<upsilon> p (t,n)) = Ifm (((Inum (x#bs) t)/(real n))#bs) p) \<and> bound0 (\<upsilon> p (t,n))" (is "(?I x (\<upsilon> p (t,n)) = ?I ?u p) \<and> ?B p" is "(_ = ?I (?t/?n) p) \<and> _" is "(_ = ?I (?N x t /_) p) \<and> _")
  using lp
proof(induct p rule: \<upsilon>.induct)
  case (5 c e)
  from 5 have cp: "c >0" and nb: "numbound0 e" by simp_all
  have "?I ?u (Lt (CN 0 c e)) = (real c *(?t/?n) + (?N x e) < 0)"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> = (?n*(real c *(?t/?n)) + ?n*(?N x e) < 0)"
    by (simp only: pos_less_divide_eq[OF np, where a="real c *(?t/?n) + (?N x e)" 
      and b="0", simplified divide_zero_left]) (simp only: algebra_simps)
  also have "\<dots> = (real c *?t + ?n* (?N x e) < 0)"
    using np by simp 
  finally show ?case using nbt nb by (simp add: algebra_simps)
next
  case (6 c e)
  from 6 have cp: "c >0" and nb: "numbound0 e" by simp_all
  have "?I ?u (Le (CN 0 c e)) = (real c *(?t/?n) + (?N x e) \<le> 0)"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> = (?n*(real c *(?t/?n)) + ?n*(?N x e) \<le> 0)"
    by (simp only: pos_le_divide_eq[OF np, where a="real c *(?t/?n) + (?N x e)" 
      and b="0", simplified divide_zero_left]) (simp only: algebra_simps)
  also have "\<dots> = (real c *?t + ?n* (?N x e) \<le> 0)"
    using np by simp 
  finally show ?case using nbt nb by (simp add: algebra_simps)
next
  case (7 c e)
  from 7 have cp: "c >0" and nb: "numbound0 e" by simp_all
  have "?I ?u (Gt (CN 0 c e)) = (real c *(?t/?n) + (?N x e) > 0)"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> = (?n*(real c *(?t/?n)) + ?n*(?N x e) > 0)"
    by (simp only: pos_divide_less_eq[OF np, where a="real c *(?t/?n) + (?N x e)" 
      and b="0", simplified divide_zero_left]) (simp only: algebra_simps)
  also have "\<dots> = (real c *?t + ?n* (?N x e) > 0)"
    using np by simp 
  finally show ?case using nbt nb by (simp add: algebra_simps)
next
  case (8 c e)
  from 8 have cp: "c >0" and nb: "numbound0 e" by simp_all
  have "?I ?u (Ge (CN 0 c e)) = (real c *(?t/?n) + (?N x e) \<ge> 0)"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> = (?n*(real c *(?t/?n)) + ?n*(?N x e) \<ge> 0)"
    by (simp only: pos_divide_le_eq[OF np, where a="real c *(?t/?n) + (?N x e)" 
      and b="0", simplified divide_zero_left]) (simp only: algebra_simps)
  also have "\<dots> = (real c *?t + ?n* (?N x e) \<ge> 0)"
    using np by simp 
  finally show ?case using nbt nb by (simp add: algebra_simps)
next
  case (3 c e)
  from 3 have cp: "c >0" and nb: "numbound0 e" by simp_all
  from np have np: "real n \<noteq> 0" by simp
  have "?I ?u (Eq (CN 0 c e)) = (real c *(?t/?n) + (?N x e) = 0)"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> = (?n*(real c *(?t/?n)) + ?n*(?N x e) = 0)"
    by (simp only: nonzero_eq_divide_eq[OF np, where a="real c *(?t/?n) + (?N x e)" 
      and b="0", simplified divide_zero_left]) (simp only: algebra_simps)
  also have "\<dots> = (real c *?t + ?n* (?N x e) = 0)"
    using np by simp 
  finally show ?case using nbt nb by (simp add: algebra_simps)
next
  case (4 c e)
  from 4 have cp: "c >0" and nb: "numbound0 e" by simp_all
  from np have np: "real n \<noteq> 0" by simp
  have "?I ?u (NEq (CN 0 c e)) = (real c *(?t/?n) + (?N x e) \<noteq> 0)"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> = (?n*(real c *(?t/?n)) + ?n*(?N x e) \<noteq> 0)"
    by (simp only: nonzero_eq_divide_eq[OF np, where a="real c *(?t/?n) + (?N x e)" 
      and b="0", simplified divide_zero_left]) (simp only: algebra_simps)
  also have "\<dots> = (real c *?t + ?n* (?N x e) \<noteq> 0)"
    using np by simp 
  finally show ?case using nbt nb by (simp add: algebra_simps)
qed(simp_all add: nbt numbound0_I[where bs ="bs" and b="(Inum (x#bs) t)/ real n" and b'="x"])

lemma \<Upsilon>_l:
  assumes lp: "isrlfm p"
  shows "\<forall> (t,k) \<in> set (\<Upsilon> p). numbound0 t \<and> k >0"
using lp
by(induct p rule: \<Upsilon>.induct)  auto

lemma rminusinf_\<Upsilon>:
  assumes lp: "isrlfm p"
  and nmi: "\<not> (Ifm (a#bs) (minusinf p))" (is "\<not> (Ifm (a#bs) (?M p))")
  and ex: "Ifm (x#bs) p" (is "?I x p")
  shows "\<exists> (s,m) \<in> set (\<Upsilon> p). x \<ge> Inum (a#bs) s / real m" (is "\<exists> (s,m) \<in> ?U p. x \<ge> ?N a s / real m")
proof-
  have "\<exists> (s,m) \<in> set (\<Upsilon> p). real m * x \<ge> Inum (a#bs) s " (is "\<exists> (s,m) \<in> ?U p. real m *x \<ge> ?N a s")
    using lp nmi ex
    by (induct p rule: minusinf.induct, auto simp add:numbound0_I[where bs="bs" and b="a" and b'="x"])
  then obtain s m where smU: "(s,m) \<in> set (\<Upsilon> p)" and mx: "real m * x \<ge> ?N a s" by blast
  from \<Upsilon>_l[OF lp] smU have mp: "real m > 0" by auto
  from pos_divide_le_eq[OF mp, where a="x" and b="?N a s", symmetric] mx have "x \<ge> ?N a s / real m" 
    by (auto simp add: mult_commute)
  thus ?thesis using smU by auto
qed

lemma rplusinf_\<Upsilon>:
  assumes lp: "isrlfm p"
  and nmi: "\<not> (Ifm (a#bs) (plusinf p))" (is "\<not> (Ifm (a#bs) (?M p))")
  and ex: "Ifm (x#bs) p" (is "?I x p")
  shows "\<exists> (s,m) \<in> set (\<Upsilon> p). x \<le> Inum (a#bs) s / real m" (is "\<exists> (s,m) \<in> ?U p. x \<le> ?N a s / real m")
proof-
  have "\<exists> (s,m) \<in> set (\<Upsilon> p). real m * x \<le> Inum (a#bs) s " (is "\<exists> (s,m) \<in> ?U p. real m *x \<le> ?N a s")
    using lp nmi ex
    by (induct p rule: minusinf.induct, auto simp add:numbound0_I[where bs="bs" and b="a" and b'="x"])
  then obtain s m where smU: "(s,m) \<in> set (\<Upsilon> p)" and mx: "real m * x \<le> ?N a s" by blast
  from \<Upsilon>_l[OF lp] smU have mp: "real m > 0" by auto
  from pos_le_divide_eq[OF mp, where a="x" and b="?N a s", symmetric] mx have "x \<le> ?N a s / real m" 
    by (auto simp add: mult_commute)
  thus ?thesis using smU by auto
qed

lemma lin_dense: 
  assumes lp: "isrlfm p"
  and noS: "\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> (\<lambda> (t,n). Inum (x#bs) t / real n) ` set (\<Upsilon> p)" 
  (is "\<forall> t. _ \<and> _ \<longrightarrow> t \<notin> (\<lambda> (t,n). ?N x t / real n ) ` (?U p)")
  and lx: "l < x" and xu:"x < u" and px:" Ifm (x#bs) p"
  and ly: "l < y" and yu: "y < u"
  shows "Ifm (y#bs) p"
using lp px noS
proof (induct p rule: isrlfm.induct)
  case (5 c e) hence cp: "real c > 0" and nb: "numbound0 e" by simp_all
  from 5 have "x * real c + ?N x e < 0" by (simp add: algebra_simps)
  hence pxc: "x < (- ?N x e) / real c" 
    by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="-?N x e"])
  from 5 have noSc:"\<forall> t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real c" by auto
  with ly yu have yne: "y \<noteq> - ?N x e / real c" by auto
  hence "y < (- ?N x e) / real c \<or> y > (-?N x e) / real c" by auto
  moreover {assume y: "y < (-?N x e)/ real c"
    hence "y * real c < - ?N x e"
      by (simp add: pos_less_divide_eq[OF cp, where a="y" and b="-?N x e", symmetric])
    hence "real c * y + ?N x e < 0" by (simp add: algebra_simps)
    hence ?case using numbound0_I[OF nb, where bs="bs" and b="x" and b'="y"] by simp}
  moreover {assume y: "y > (- ?N x e) / real c" 
    with yu have eu: "u > (- ?N x e) / real c" by auto
    with noSc ly yu have "(- ?N x e) / real c \<le> l" by (cases "(- ?N x e) / real c > l", auto)
    with lx pxc have "False" by auto
    hence ?case by simp }
  ultimately show ?case by blast
next
  case (6 c e) hence cp: "real c > 0" and nb: "numbound0 e" by simp_all
  from 6 have "x * real c + ?N x e \<le> 0" by (simp add: algebra_simps)
  hence pxc: "x \<le> (- ?N x e) / real c" 
    by (simp only: pos_le_divide_eq[OF cp, where a="x" and b="-?N x e"])
  from 6 have noSc:"\<forall> t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real c" by auto
  with ly yu have yne: "y \<noteq> - ?N x e / real c" by auto
  hence "y < (- ?N x e) / real c \<or> y > (-?N x e) / real c" by auto
  moreover {assume y: "y < (-?N x e)/ real c"
    hence "y * real c < - ?N x e"
      by (simp add: pos_less_divide_eq[OF cp, where a="y" and b="-?N x e", symmetric])
    hence "real c * y + ?N x e < 0" by (simp add: algebra_simps)
    hence ?case using numbound0_I[OF nb, where bs="bs" and b="x" and b'="y"] by simp}
  moreover {assume y: "y > (- ?N x e) / real c" 
    with yu have eu: "u > (- ?N x e) / real c" by auto
    with noSc ly yu have "(- ?N x e) / real c \<le> l" by (cases "(- ?N x e) / real c > l", auto)
    with lx pxc have "False" by auto
    hence ?case by simp }
  ultimately show ?case by blast
next
  case (7 c e) hence cp: "real c > 0" and nb: "numbound0 e" by simp_all
  from 7 have "x * real c + ?N x e > 0" by (simp add: algebra_simps)
  hence pxc: "x > (- ?N x e) / real c" 
    by (simp only: pos_divide_less_eq[OF cp, where a="x" and b="-?N x e"])
  from 7 have noSc:"\<forall> t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real c" by auto
  with ly yu have yne: "y \<noteq> - ?N x e / real c" by auto
  hence "y < (- ?N x e) / real c \<or> y > (-?N x e) / real c" by auto
  moreover {assume y: "y > (-?N x e)/ real c"
    hence "y * real c > - ?N x e"
      by (simp add: pos_divide_less_eq[OF cp, where a="y" and b="-?N x e", symmetric])
    hence "real c * y + ?N x e > 0" by (simp add: algebra_simps)
    hence ?case using numbound0_I[OF nb, where bs="bs" and b="x" and b'="y"] by simp}
  moreover {assume y: "y < (- ?N x e) / real c" 
    with ly have eu: "l < (- ?N x e) / real c" by auto
    with noSc ly yu have "(- ?N x e) / real c \<ge> u" by (cases "(- ?N x e) / real c > l", auto)
    with xu pxc have "False" by auto
    hence ?case by simp }
  ultimately show ?case by blast
next
  case (8 c e) hence cp: "real c > 0" and nb: "numbound0 e" by simp_all
  from 8 have "x * real c + ?N x e \<ge> 0" by (simp add: algebra_simps)
  hence pxc: "x \<ge> (- ?N x e) / real c" 
    by (simp only: pos_divide_le_eq[OF cp, where a="x" and b="-?N x e"])
  from 8 have noSc:"\<forall> t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real c" by auto
  with ly yu have yne: "y \<noteq> - ?N x e / real c" by auto
  hence "y < (- ?N x e) / real c \<or> y > (-?N x e) / real c" by auto
  moreover {assume y: "y > (-?N x e)/ real c"
    hence "y * real c > - ?N x e"
      by (simp add: pos_divide_less_eq[OF cp, where a="y" and b="-?N x e", symmetric])
    hence "real c * y + ?N x e > 0" by (simp add: algebra_simps)
    hence ?case using numbound0_I[OF nb, where bs="bs" and b="x" and b'="y"] by simp}
  moreover {assume y: "y < (- ?N x e) / real c" 
    with ly have eu: "l < (- ?N x e) / real c" by auto
    with noSc ly yu have "(- ?N x e) / real c \<ge> u" by (cases "(- ?N x e) / real c > l", auto)
    with xu pxc have "False" by auto
    hence ?case by simp }
  ultimately show ?case by blast
next
  case (3 c e) hence cp: "real c > 0" and nb: "numbound0 e" by simp_all
  from cp have cnz: "real c \<noteq> 0" by simp
  from 3 have "x * real c + ?N x e = 0" by (simp add: algebra_simps)
  hence pxc: "x = (- ?N x e) / real c" 
    by (simp only: nonzero_eq_divide_eq[OF cnz, where a="x" and b="-?N x e"])
  from 3 have noSc:"\<forall> t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real c" by auto
  with lx xu have yne: "x \<noteq> - ?N x e / real c" by auto
  with pxc show ?case by simp
next
  case (4 c e) hence cp: "real c > 0" and nb: "numbound0 e" by simp_all
  from cp have cnz: "real c \<noteq> 0" by simp
  from 4 have noSc:"\<forall> t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real c" by auto
  with ly yu have yne: "y \<noteq> - ?N x e / real c" by auto
  hence "y* real c \<noteq> -?N x e"      
    by (simp only: nonzero_eq_divide_eq[OF cnz, where a="y" and b="-?N x e"]) simp
  hence "y* real c + ?N x e \<noteq> 0" by (simp add: algebra_simps)
  thus ?case using numbound0_I[OF nb, where bs="bs" and b="x" and b'="y"] 
    by (simp add: algebra_simps)
qed (auto simp add: numbound0_I[where bs="bs" and b="y" and b'="x"])

lemma rinf_\<Upsilon>:
  assumes lp: "isrlfm p"
  and nmi: "\<not> (Ifm (x#bs) (minusinf p))" (is "\<not> (Ifm (x#bs) (?M p))")
  and npi: "\<not> (Ifm (x#bs) (plusinf p))" (is "\<not> (Ifm (x#bs) (?P p))")
  and ex: "\<exists> x.  Ifm (x#bs) p" (is "\<exists> x. ?I x p")
  shows "\<exists> (l,n) \<in> set (\<Upsilon> p). \<exists> (s,m) \<in> set (\<Upsilon> p).
    ?I ((Inum (x#bs) l / real n + Inum (x#bs) s / real m) / 2) p" 
proof-
  let ?N = "\<lambda> x t. Inum (x#bs) t"
  let ?U = "set (\<Upsilon> p)"
  from ex obtain a where pa: "?I a p" by blast
  from bound0_I[OF rminusinf_bound0[OF lp], where bs="bs" and b="x" and b'="a"] nmi
  have nmi': "\<not> (?I a (?M p))" by simp
  from bound0_I[OF rplusinf_bound0[OF lp], where bs="bs" and b="x" and b'="a"] npi
  have npi': "\<not> (?I a (?P p))" by simp
  have "\<exists> (l,n) \<in> set (\<Upsilon> p). \<exists> (s,m) \<in> set (\<Upsilon> p). ?I ((?N a l/real n + ?N a s /real m) / 2) p"
  proof-
    let ?M = "(\<lambda> (t,c). ?N a t / real c) ` ?U"
    have fM: "finite ?M" by auto
    from rminusinf_\<Upsilon>[OF lp nmi pa] rplusinf_\<Upsilon>[OF lp npi pa] 
    have "\<exists> (l,n) \<in> set (\<Upsilon> p). \<exists> (s,m) \<in> set (\<Upsilon> p). a \<le> ?N x l / real n \<and> a \<ge> ?N x s / real m" by blast
    then obtain "t" "n" "s" "m" where 
      tnU: "(t,n) \<in> ?U" and smU: "(s,m) \<in> ?U" 
      and xs1: "a \<le> ?N x s / real m" and tx1: "a \<ge> ?N x t / real n" by blast
    from \<Upsilon>_l[OF lp] tnU smU numbound0_I[where bs="bs" and b="x" and b'="a"] xs1 tx1 have xs: "a \<le> ?N a s / real m" and tx: "a \<ge> ?N a t / real n" by auto
    from tnU have Mne: "?M \<noteq> {}" by auto
    hence Une: "?U \<noteq> {}" by simp
    let ?l = "Min ?M"
    let ?u = "Max ?M"
    have linM: "?l \<in> ?M" using fM Mne by simp
    have uinM: "?u \<in> ?M" using fM Mne by simp
    have tnM: "?N a t / real n \<in> ?M" using tnU by auto
    have smM: "?N a s / real m \<in> ?M" using smU by auto 
    have lM: "\<forall> t\<in> ?M. ?l \<le> t" using Mne fM by auto
    have Mu: "\<forall> t\<in> ?M. t \<le> ?u" using Mne fM by auto
    have "?l \<le> ?N a t / real n" using tnM Mne by simp hence lx: "?l \<le> a" using tx by simp
    have "?N a s / real m \<le> ?u" using smM Mne by simp hence xu: "a \<le> ?u" using xs by simp
    from finite_set_intervals2[where P="\<lambda> x. ?I x p",OF pa lx xu linM uinM fM lM Mu]
    have "(\<exists> s\<in> ?M. ?I s p) \<or> 
      (\<exists> t1\<in> ?M. \<exists> t2 \<in> ?M. (\<forall> y. t1 < y \<and> y < t2 \<longrightarrow> y \<notin> ?M) \<and> t1 < a \<and> a < t2 \<and> ?I a p)" .
    moreover { fix u assume um: "u\<in> ?M" and pu: "?I u p"
      hence "\<exists> (tu,nu) \<in> ?U. u = ?N a tu / real nu" by auto
      then obtain "tu" "nu" where tuU: "(tu,nu) \<in> ?U" and tuu:"u= ?N a tu / real nu" by blast
      have "(u + u) / 2 = u" by auto with pu tuu 
      have "?I (((?N a tu / real nu) + (?N a tu / real nu)) / 2) p" by simp
      with tuU have ?thesis by blast}
    moreover{
      assume "\<exists> t1\<in> ?M. \<exists> t2 \<in> ?M. (\<forall> y. t1 < y \<and> y < t2 \<longrightarrow> y \<notin> ?M) \<and> t1 < a \<and> a < t2 \<and> ?I a p"
      then obtain t1 and t2 where t1M: "t1 \<in> ?M" and t2M: "t2\<in> ?M" 
        and noM: "\<forall> y. t1 < y \<and> y < t2 \<longrightarrow> y \<notin> ?M" and t1x: "t1 < a" and xt2: "a < t2" and px: "?I a p"
        by blast
      from t1M have "\<exists> (t1u,t1n) \<in> ?U. t1 = ?N a t1u / real t1n" by auto
      then obtain "t1u" "t1n" where t1uU: "(t1u,t1n) \<in> ?U" and t1u: "t1 = ?N a t1u / real t1n" by blast
      from t2M have "\<exists> (t2u,t2n) \<in> ?U. t2 = ?N a t2u / real t2n" by auto
      then obtain "t2u" "t2n" where t2uU: "(t2u,t2n) \<in> ?U" and t2u: "t2 = ?N a t2u / real t2n" by blast
      from t1x xt2 have t1t2: "t1 < t2" by simp
      let ?u = "(t1 + t2) / 2"
      from less_half_sum[OF t1t2] gt_half_sum[OF t1t2] have t1lu: "t1 < ?u" and ut2: "?u < t2" by auto
      from lin_dense[OF lp noM t1x xt2 px t1lu ut2] have "?I ?u p" .
      with t1uU t2uU t1u t2u have ?thesis by blast}
    ultimately show ?thesis by blast
  qed
  then obtain "l" "n" "s"  "m" where lnU: "(l,n) \<in> ?U" and smU:"(s,m) \<in> ?U" 
    and pu: "?I ((?N a l / real n + ?N a s / real m) / 2) p" by blast
  from lnU smU \<Upsilon>_l[OF lp] have nbl: "numbound0 l" and nbs: "numbound0 s" by auto
  from numbound0_I[OF nbl, where bs="bs" and b="a" and b'="x"] 
    numbound0_I[OF nbs, where bs="bs" and b="a" and b'="x"] pu
  have "?I ((?N x l / real n + ?N x s / real m) / 2) p" by simp
  with lnU smU
  show ?thesis by auto
qed
    (* The Ferrante - Rackoff Theorem *)

theorem fr_eq: 
  assumes lp: "isrlfm p"
  shows "(\<exists> x. Ifm (x#bs) p) = ((Ifm (x#bs) (minusinf p)) \<or> (Ifm (x#bs) (plusinf p)) \<or> (\<exists> (t,n) \<in> set (\<Upsilon> p). \<exists> (s,m) \<in> set (\<Upsilon> p). Ifm ((((Inum (x#bs) t)/  real n + (Inum (x#bs) s) / real m) /2)#bs) p))"
  (is "(\<exists> x. ?I x p) = (?M \<or> ?P \<or> ?F)" is "?E = ?D")
proof
  assume px: "\<exists> x. ?I x p"
  have "?M \<or> ?P \<or> (\<not> ?M \<and> \<not> ?P)" by blast
  moreover {assume "?M \<or> ?P" hence "?D" by blast}
  moreover {assume nmi: "\<not> ?M" and npi: "\<not> ?P"
    from rinf_\<Upsilon>[OF lp nmi npi] have "?F" using px by blast hence "?D" by blast}
  ultimately show "?D" by blast
next
  assume "?D" 
  moreover {assume m:"?M" from rminusinf_ex[OF lp m] have "?E" .}
  moreover {assume p: "?P" from rplusinf_ex[OF lp p] have "?E" . }
  moreover {assume f:"?F" hence "?E" by blast}
  ultimately show "?E" by blast
qed


lemma fr_eq\<upsilon>: 
  assumes lp: "isrlfm p"
  shows "(\<exists> x. Ifm (x#bs) p) = ((Ifm (x#bs) (minusinf p)) \<or> (Ifm (x#bs) (plusinf p)) \<or> (\<exists> (t,k) \<in> set (\<Upsilon> p). \<exists> (s,l) \<in> set (\<Upsilon> p). Ifm (x#bs) (\<upsilon> p (Add(Mul l t) (Mul k s) , 2*k*l))))"
  (is "(\<exists> x. ?I x p) = (?M \<or> ?P \<or> ?F)" is "?E = ?D")
proof
  assume px: "\<exists> x. ?I x p"
  have "?M \<or> ?P \<or> (\<not> ?M \<and> \<not> ?P)" by blast
  moreover {assume "?M \<or> ?P" hence "?D" by blast}
  moreover {assume nmi: "\<not> ?M" and npi: "\<not> ?P"
    let ?f ="\<lambda> (t,n). Inum (x#bs) t / real n"
    let ?N = "\<lambda> t. Inum (x#bs) t"
    {fix t n s m assume "(t,n)\<in> set (\<Upsilon> p)" and "(s,m) \<in> set (\<Upsilon> p)"
      with \<Upsilon>_l[OF lp] have tnb: "numbound0 t" and np:"real n > 0" and snb: "numbound0 s" and mp:"real m > 0"
        by auto
      let ?st = "Add (Mul m t) (Mul n s)"
      from mult_pos_pos[OF np mp] have mnp: "real (2*n*m) > 0" 
        by (simp add: mult_commute)
      from tnb snb have st_nb: "numbound0 ?st" by simp
      have st: "(?N t / real n + ?N s / real m)/2 = ?N ?st / real (2*n*m)"
        using mnp mp np by (simp add: algebra_simps add_divide_distrib)
      from \<upsilon>_I[OF lp mnp st_nb, where x="x" and bs="bs"] 
      have "?I x (\<upsilon> p (?st,2*n*m)) = ?I ((?N t / real n + ?N s / real m) /2) p" by (simp only: st[symmetric])}
    with rinf_\<Upsilon>[OF lp nmi npi px] have "?F" by blast hence "?D" by blast}
  ultimately show "?D" by blast
next
  assume "?D" 
  moreover {assume m:"?M" from rminusinf_ex[OF lp m] have "?E" .}
  moreover {assume p: "?P" from rplusinf_ex[OF lp p] have "?E" . }
  moreover {fix t k s l assume "(t,k) \<in> set (\<Upsilon> p)" and "(s,l) \<in> set (\<Upsilon> p)" 
    and px:"?I x (\<upsilon> p (Add (Mul l t) (Mul k s), 2*k*l))"
    with \<Upsilon>_l[OF lp] have tnb: "numbound0 t" and np:"real k > 0" and snb: "numbound0 s" and mp:"real l > 0" by auto
    let ?st = "Add (Mul l t) (Mul k s)"
    from mult_pos_pos[OF np mp] have mnp: "real (2*k*l) > 0" 
      by (simp add: mult_commute)
    from tnb snb have st_nb: "numbound0 ?st" by simp
    from \<upsilon>_I[OF lp mnp st_nb, where bs="bs"] px have "?E" by auto}
  ultimately show "?E" by blast
qed

text{* The overall Part *}

lemma real_ex_int_real01:
  shows "(\<exists> (x::real). P x) = (\<exists> (i::int) (u::real). 0\<le> u \<and> u< 1 \<and> P (real i + u))"
proof(auto)
  fix x
  assume Px: "P x"
  let ?i = "floor x"
  let ?u = "x - real ?i"
  have "x = real ?i + ?u" by simp
  hence "P (real ?i + ?u)" using Px by simp
  moreover have "real ?i \<le> x" using real_of_int_floor_le by simp hence "0 \<le> ?u" by arith
  moreover have "?u < 1" using real_of_int_floor_add_one_gt[where r="x"] by arith 
  ultimately show "(\<exists> (i::int) (u::real). 0\<le> u \<and> u< 1 \<and> P (real i + u))" by blast
qed

fun exsplitnum :: "num \<Rightarrow> num" where
  "exsplitnum (C c) = (C c)"
| "exsplitnum (Bound 0) = Add (Bound 0) (Bound 1)"
| "exsplitnum (Bound n) = Bound (n+1)"
| "exsplitnum (Neg a) = Neg (exsplitnum a)"
| "exsplitnum (Add a b) = Add (exsplitnum a) (exsplitnum b) "
| "exsplitnum (Sub a b) = Sub (exsplitnum a) (exsplitnum b) "
| "exsplitnum (Mul c a) = Mul c (exsplitnum a)"
| "exsplitnum (Floor a) = Floor (exsplitnum a)"
| "exsplitnum (CN 0 c a) = CN 0 c (Add (Mul c (Bound 1)) (exsplitnum a))"
| "exsplitnum (CN n c a) = CN (n+1) c (exsplitnum a)"
| "exsplitnum (CF c s t) = CF c (exsplitnum s) (exsplitnum t)"

fun exsplit :: "fm \<Rightarrow> fm" where
  "exsplit (Lt a) = Lt (exsplitnum a)"
| "exsplit (Le a) = Le (exsplitnum a)"
| "exsplit (Gt a) = Gt (exsplitnum a)"
| "exsplit (Ge a) = Ge (exsplitnum a)"
| "exsplit (Eq a) = Eq (exsplitnum a)"
| "exsplit (NEq a) = NEq (exsplitnum a)"
| "exsplit (Dvd i a) = Dvd i (exsplitnum a)"
| "exsplit (NDvd i a) = NDvd i (exsplitnum a)"
| "exsplit (And p q) = And (exsplit p) (exsplit q)"
| "exsplit (Or p q) = Or (exsplit p) (exsplit q)"
| "exsplit (Imp p q) = Imp (exsplit p) (exsplit q)"
| "exsplit (Iff p q) = Iff (exsplit p) (exsplit q)"
| "exsplit (NOT p) = NOT (exsplit p)"
| "exsplit p = p"

lemma exsplitnum: 
  "Inum (x#y#bs) (exsplitnum t) = Inum ((x+y) #bs) t"
  by(induct t rule: exsplitnum.induct) (simp_all add: algebra_simps)

lemma exsplit: 
  assumes qfp: "qfree p"
  shows "Ifm (x#y#bs) (exsplit p) = Ifm ((x+y)#bs) p"
using qfp exsplitnum[where x="x" and y="y" and bs="bs"]
by(induct p rule: exsplit.induct) simp_all

lemma splitex:
  assumes qf: "qfree p"
  shows "(Ifm bs (E p)) = (\<exists> (i::int). Ifm (real i#bs) (E (And (And (Ge(CN 0 1 (C 0))) (Lt (CN 0 1 (C (- 1))))) (exsplit p))))" (is "?lhs = ?rhs")
proof-
  have "?rhs = (\<exists> (i::int). \<exists> x. 0\<le> x \<and> x < 1 \<and> Ifm (x#(real i)#bs) (exsplit p))"
    by (simp add: myless[of _ "1"] myless[of _ "0"] add_ac diff_minus)
  also have "\<dots> = (\<exists> (i::int). \<exists> x. 0\<le> x \<and> x < 1 \<and> Ifm ((real i + x) #bs) p)"
    by (simp only: exsplit[OF qf] add_ac)
  also have "\<dots> = (\<exists> x. Ifm (x#bs) p)" 
    by (simp only: real_ex_int_real01[where P="\<lambda> x. Ifm (x#bs) p"])
  finally show ?thesis by simp
qed

    (* Implement the right hand sides of Cooper's theorem and Ferrante and Rackoff. *)

definition ferrack01 :: "fm \<Rightarrow> fm" where
  "ferrack01 p \<equiv> (let p' = rlfm(And (And (Ge(CN 0 1 (C 0))) (Lt (CN 0 1 (C (- 1))))) p);
                    U = remdups(map simp_num_pair 
                     (map (\<lambda> ((t,n),(s,m)). (Add (Mul m t) (Mul n s) , 2*n*m))
                           (alluopairs (\<Upsilon> p')))) 
  in decr (evaldjf (\<upsilon> p') U ))"

lemma fr_eq_01: 
  assumes qf: "qfree p"
  shows "(\<exists> x. Ifm (x#bs) (And (And (Ge(CN 0 1 (C 0))) (Lt (CN 0 1 (C (- 1))))) p)) = (\<exists> (t,n) \<in> set (\<Upsilon> (rlfm (And (And (Ge(CN 0 1 (C 0))) (Lt (CN 0 1 (C (- 1))))) p))). \<exists> (s,m) \<in> set (\<Upsilon> (rlfm (And (And (Ge(CN 0 1 (C 0))) (Lt (CN 0 1 (C (- 1))))) p))). Ifm (x#bs) (\<upsilon> (rlfm (And (And (Ge(CN 0 1 (C 0))) (Lt (CN 0 1 (C (- 1))))) p)) (Add (Mul m t) (Mul n s), 2*n*m)))"
  (is "(\<exists> x. ?I x ?q) = ?F")
proof-
  let ?rq = "rlfm ?q"
  let ?M = "?I x (minusinf ?rq)"
  let ?P = "?I x (plusinf ?rq)"
  have MF: "?M = False"
    apply (simp add: Let_def reducecoeff_def numgcd_def rsplit_def ge_def lt_def conj_def disj_def)
    by (cases "rlfm p = And (Ge (CN 0 1 (C 0))) (Lt (CN 0 1 (C -1)))", simp_all)
  have PF: "?P = False" apply (simp add: Let_def reducecoeff_def numgcd_def rsplit_def ge_def lt_def conj_def disj_def)
    by (cases "rlfm p = And (Ge (CN 0 1 (C 0))) (Lt (CN 0 1 (C -1)))", simp_all)
  have "(\<exists> x. ?I x ?q ) = 
    ((?I x (minusinf ?rq)) \<or> (?I x (plusinf ?rq )) \<or> (\<exists> (t,n) \<in> set (\<Upsilon> ?rq). \<exists> (s,m) \<in> set (\<Upsilon> ?rq ). ?I x (\<upsilon> ?rq (Add (Mul m t) (Mul n s), 2*n*m))))"
    (is "(\<exists> x. ?I x ?q) = (?M \<or> ?P \<or> ?F)" is "?E = ?D")
  proof
    assume "\<exists> x. ?I x ?q"  
    then obtain x where qx: "?I x ?q" by blast
    hence xp: "0\<le> x" and x1: "x< 1" and px: "?I x p" 
      by (auto simp add: rsplit_def lt_def ge_def rlfm_I[OF qf])
    from qx have "?I x ?rq " 
      by (simp add: rsplit_def lt_def ge_def rlfm_I[OF qf xp x1])
    hence lqx: "?I x ?rq " using simpfm[where p="?rq" and bs="x#bs"] by auto
    from qf have qfq:"isrlfm ?rq"  
      by (auto simp add: rsplit_def lt_def ge_def rlfm_I[OF qf xp x1])
    with lqx fr_eq\<upsilon>[OF qfq] show "?M \<or> ?P \<or> ?F" by blast
  next
    assume D: "?D"
    let ?U = "set (\<Upsilon> ?rq )"
    from MF PF D have "?F" by auto
    then obtain t n s m where aU:"(t,n) \<in> ?U" and bU:"(s,m)\<in> ?U" and rqx: "?I x (\<upsilon> ?rq (Add (Mul m t) (Mul n s), 2*n*m))" by blast
    from qf have lrq:"isrlfm ?rq"using rlfm_l[OF qf] 
      by (auto simp add: rsplit_def lt_def ge_def)
    from aU bU \<Upsilon>_l[OF lrq] have tnb: "numbound0 t" and np:"real n > 0" and snb: "numbound0 s" and mp:"real m > 0" by (auto simp add: split_def)
    let ?st = "Add (Mul m t) (Mul n s)"
    from tnb snb have stnb: "numbound0 ?st" by simp
    from mult_pos_pos[OF np mp] have mnp: "real (2*n*m) > 0" 
      by (simp add: mult_commute)
    from conjunct1[OF \<upsilon>_I[OF lrq mnp stnb, where bs="bs" and x="x"], symmetric] rqx
    have "\<exists> x. ?I x ?rq" by auto
    thus "?E" 
      using rlfm_I[OF qf] by (auto simp add: rsplit_def lt_def ge_def)
  qed
  with MF PF show ?thesis by blast
qed

lemma \<Upsilon>_cong_aux:
  assumes Ul: "\<forall> (t,n) \<in> set U. numbound0 t \<and> n >0"
  shows "((\<lambda> (t,n). Inum (x#bs) t /real n) ` (set (map (\<lambda> ((t,n),(s,m)). (Add (Mul m t) (Mul n s) , 2*n*m)) (alluopairs U)))) = ((\<lambda> ((t,n),(s,m)). (Inum (x#bs) t /real n + Inum (x#bs) s /real m)/2) ` (set U \<times> set U))"
  (is "?lhs = ?rhs")
proof(auto)
  fix t n s m
  assume "((t,n),(s,m)) \<in> set (alluopairs U)"
  hence th: "((t,n),(s,m)) \<in> (set U \<times> set U)"
    using alluopairs_set1[where xs="U"] by blast
  let ?N = "\<lambda> t. Inum (x#bs) t"
  let ?st= "Add (Mul m t) (Mul n s)"
  from Ul th have mnz: "m \<noteq> 0" by auto
  from Ul th have  nnz: "n \<noteq> 0" by auto  
  have st: "(?N t / real n + ?N s / real m)/2 = ?N ?st / real (2*n*m)"
   using mnz nnz by (simp add: algebra_simps add_divide_distrib)
 
  thus "(real m *  Inum (x # bs) t + real n * Inum (x # bs) s) /
       (2 * real n * real m)
       \<in> (\<lambda>((t, n), s, m).
             (Inum (x # bs) t / real n + Inum (x # bs) s / real m) / 2) `
         (set U \<times> set U)"using mnz nnz th  
    apply (auto simp add: th add_divide_distrib algebra_simps split_def image_def)
    by (rule_tac x="(s,m)" in bexI,simp_all) 
  (rule_tac x="(t,n)" in bexI,simp_all add: mult_commute)
next
  fix t n s m
  assume tnU: "(t,n) \<in> set U" and smU:"(s,m) \<in> set U" 
  let ?N = "\<lambda> t. Inum (x#bs) t"
  let ?st= "Add (Mul m t) (Mul n s)"
  from Ul smU have mnz: "m \<noteq> 0" by auto
  from Ul tnU have  nnz: "n \<noteq> 0" by auto  
  have st: "(?N t / real n + ?N s / real m)/2 = ?N ?st / real (2*n*m)"
   using mnz nnz by (simp add: algebra_simps add_divide_distrib)
 let ?P = "\<lambda> (t',n') (s',m'). (Inum (x # bs) t / real n + Inum (x # bs) s / real m)/2 = (Inum (x # bs) t' / real n' + Inum (x # bs) s' / real m')/2"
 have Pc:"\<forall> a b. ?P a b = ?P b a"
   by auto
 from Ul alluopairs_set1 have Up:"\<forall> ((t,n),(s,m)) \<in> set (alluopairs U). n \<noteq> 0 \<and> m \<noteq> 0" by blast
 from alluopairs_ex[OF Pc, where xs="U"] tnU smU
 have th':"\<exists> ((t',n'),(s',m')) \<in> set (alluopairs U). ?P (t',n') (s',m')"
   by blast
 then obtain t' n' s' m' where ts'_U: "((t',n'),(s',m')) \<in> set (alluopairs U)" 
   and Pts': "?P (t',n') (s',m')" by blast
 from ts'_U Up have mnz': "m' \<noteq> 0" and nnz': "n'\<noteq> 0" by auto
 let ?st' = "Add (Mul m' t') (Mul n' s')"
   have st': "(?N t' / real n' + ?N s' / real m')/2 = ?N ?st' / real (2*n'*m')"
   using mnz' nnz' by (simp add: algebra_simps add_divide_distrib)
 from Pts' have 
   "(Inum (x # bs) t / real n + Inum (x # bs) s / real m)/2 = (Inum (x # bs) t' / real n' + Inum (x # bs) s' / real m')/2" by simp
 also have "\<dots> = ((\<lambda>(t, n). Inum (x # bs) t / real n) ((\<lambda>((t, n), s, m). (Add (Mul m t) (Mul n s), 2 * n * m)) ((t',n'),(s',m'))))" by (simp add: st')
 finally show "(Inum (x # bs) t / real n + Inum (x # bs) s / real m) / 2
          \<in> (\<lambda>(t, n). Inum (x # bs) t / real n) `
            (\<lambda>((t, n), s, m). (Add (Mul m t) (Mul n s), 2 * n * m)) `
            set (alluopairs U)"
   using ts'_U by blast
qed

lemma \<Upsilon>_cong:
  assumes lp: "isrlfm p"
  and UU': "((\<lambda> (t,n). Inum (x#bs) t /real n) ` U') = ((\<lambda> ((t,n),(s,m)). (Inum (x#bs) t /real n + Inum (x#bs) s /real m)/2) ` (U \<times> U))" (is "?f ` U' = ?g ` (U\<times>U)")
  and U: "\<forall> (t,n) \<in> U. numbound0 t \<and> n > 0"
  and U': "\<forall> (t,n) \<in> U'. numbound0 t \<and> n > 0"
  shows "(\<exists> (t,n) \<in> U. \<exists> (s,m) \<in> U. Ifm (x#bs) (\<upsilon> p (Add (Mul m t) (Mul n s),2*n*m))) = (\<exists> (t,n) \<in> U'. Ifm (x#bs) (\<upsilon> p (t,n)))"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain t n s m where tnU: "(t,n) \<in> U" and smU:"(s,m) \<in> U" and 
    Pst: "Ifm (x#bs) (\<upsilon> p (Add (Mul m t) (Mul n s),2*n*m))" by blast
  let ?N = "\<lambda> t. Inum (x#bs) t"
  from tnU smU U have tnb: "numbound0 t" and np: "n > 0" 
    and snb: "numbound0 s" and mp:"m > 0"  by auto
  let ?st= "Add (Mul m t) (Mul n s)"
  from mult_pos_pos[OF np mp] have mnp: "real (2*n*m) > 0" 
      by (simp add: mult_commute real_of_int_mult[symmetric] del: real_of_int_mult)
    from tnb snb have stnb: "numbound0 ?st" by simp
  have st: "(?N t / real n + ?N s / real m)/2 = ?N ?st / real (2*n*m)"
   using mp np by (simp add: algebra_simps add_divide_distrib)
  from tnU smU UU' have "?g ((t,n),(s,m)) \<in> ?f ` U'" by blast
  hence "\<exists> (t',n') \<in> U'. ?g ((t,n),(s,m)) = ?f (t',n')"
    by auto (rule_tac x="(a,b)" in bexI, auto)
  then obtain t' n' where tnU': "(t',n') \<in> U'" and th: "?g ((t,n),(s,m)) = ?f (t',n')" by blast
  from U' tnU' have tnb': "numbound0 t'" and np': "real n' > 0" by auto
  from \<upsilon>_I[OF lp mnp stnb, where bs="bs" and x="x"] Pst 
  have Pst2: "Ifm (Inum (x # bs) (Add (Mul m t) (Mul n s)) / real (2 * n * m) # bs) p" by simp
  from conjunct1[OF \<upsilon>_I[OF lp np' tnb', where bs="bs" and x="x"], symmetric] th[simplified split_def fst_conv snd_conv,symmetric] Pst2[simplified st[symmetric]]
  have "Ifm (x # bs) (\<upsilon> p (t', n')) " by (simp only: st) 
  then show ?rhs using tnU' by auto 
next
  assume ?rhs
  then obtain t' n' where tnU': "(t',n') \<in> U'" and Pt': "Ifm (x # bs) (\<upsilon> p (t', n'))" 
    by blast
  from tnU' UU' have "?f (t',n') \<in> ?g ` (U\<times>U)" by blast
  hence "\<exists> ((t,n),(s,m)) \<in> (U\<times>U). ?f (t',n') = ?g ((t,n),(s,m))" 
    by auto (rule_tac x="(a,b)" in bexI, auto)
  then obtain t n s m where tnU: "(t,n) \<in> U" and smU:"(s,m) \<in> U" and 
    th: "?f (t',n') = ?g((t,n),(s,m)) "by blast
    let ?N = "\<lambda> t. Inum (x#bs) t"
  from tnU smU U have tnb: "numbound0 t" and np: "n > 0" 
    and snb: "numbound0 s" and mp:"m > 0"  by auto
  let ?st= "Add (Mul m t) (Mul n s)"
  from mult_pos_pos[OF np mp] have mnp: "real (2*n*m) > 0" 
      by (simp add: mult_commute real_of_int_mult[symmetric] del: real_of_int_mult)
    from tnb snb have stnb: "numbound0 ?st" by simp
  have st: "(?N t / real n + ?N s / real m)/2 = ?N ?st / real (2*n*m)"
   using mp np by (simp add: algebra_simps add_divide_distrib)
  from U' tnU' have tnb': "numbound0 t'" and np': "real n' > 0" by auto
  from \<upsilon>_I[OF lp np' tnb', where bs="bs" and x="x",simplified th[simplified split_def fst_conv snd_conv] st] Pt'
  have Pst2: "Ifm (Inum (x # bs) (Add (Mul m t) (Mul n s)) / real (2 * n * m) # bs) p" by simp
  with \<upsilon>_I[OF lp mnp stnb, where x="x" and bs="bs"] tnU smU show ?lhs by blast
qed
  
lemma ferrack01: 
  assumes qf: "qfree p"
  shows "((\<exists> x. Ifm (x#bs) (And (And (Ge(CN 0 1 (C 0))) (Lt (CN 0 1 (C (- 1))))) p)) = (Ifm bs (ferrack01 p))) \<and> qfree (ferrack01 p)" (is "(?lhs = ?rhs) \<and> _")
proof-
  let ?I = "\<lambda> x p. Ifm (x#bs) p"
  fix x
  let ?N = "\<lambda> t. Inum (x#bs) t"
  let ?q = "rlfm (And (And (Ge(CN 0 1 (C 0))) (Lt (CN 0 1 (C (- 1))))) p)"
  let ?U = "\<Upsilon> ?q"
  let ?Up = "alluopairs ?U"
  let ?g = "\<lambda> ((t,n),(s,m)). (Add (Mul m t) (Mul n s) , 2*n*m)"
  let ?S = "map ?g ?Up"
  let ?SS = "map simp_num_pair ?S"
  let ?Y = "remdups ?SS"
  let ?f= "(\<lambda> (t,n). ?N t / real n)"
  let ?h = "\<lambda> ((t,n),(s,m)). (?N t/real n + ?N s/ real m) /2"
  let ?F = "\<lambda> p. \<exists> a \<in> set (\<Upsilon> p). \<exists> b \<in> set (\<Upsilon> p). ?I x (\<upsilon> p (?g(a,b)))"
  let ?ep = "evaldjf (\<upsilon> ?q) ?Y"
  from rlfm_l[OF qf] have lq: "isrlfm ?q" 
    by (simp add: rsplit_def lt_def ge_def conj_def disj_def Let_def reducecoeff_def numgcd_def)
  from alluopairs_set1[where xs="?U"] have UpU: "set ?Up \<le> (set ?U \<times> set ?U)" by simp
  from \<Upsilon>_l[OF lq] have U_l: "\<forall> (t,n) \<in> set ?U. numbound0 t \<and> n > 0" .
  from U_l UpU 
  have Up_: "\<forall> ((t,n),(s,m)) \<in> set ?Up. numbound0 t \<and> n> 0 \<and> numbound0 s \<and> m > 0" by auto
  hence Snb: "\<forall> (t,n) \<in> set ?S. numbound0 t \<and> n > 0 "
    by (auto simp add: mult_pos_pos)
  have Y_l: "\<forall> (t,n) \<in> set ?Y. numbound0 t \<and> n > 0" 
  proof-
    { fix t n assume tnY: "(t,n) \<in> set ?Y" 
      hence "(t,n) \<in> set ?SS" by simp
      hence "\<exists> (t',n') \<in> set ?S. simp_num_pair (t',n') = (t,n)"
        by (auto simp add: split_def simp del: map_map)
           (rule_tac x="((aa,ba),(ab,bb))" in bexI, simp_all)
      then obtain t' n' where tn'S: "(t',n') \<in> set ?S" and tns: "simp_num_pair (t',n') = (t,n)" by blast
      from tn'S Snb have tnb: "numbound0 t'" and np: "n' > 0" by auto
      from simp_num_pair_l[OF tnb np tns]
      have "numbound0 t \<and> n > 0" . }
    thus ?thesis by blast
  qed

  have YU: "(?f ` set ?Y) = (?h ` (set ?U \<times> set ?U))"
  proof-
     from simp_num_pair_ci[where bs="x#bs"] have 
    "\<forall>x. (?f o simp_num_pair) x = ?f x" by auto
     hence th: "?f o simp_num_pair = ?f" using ext by blast
    have "(?f ` set ?Y) = ((?f o simp_num_pair) ` set ?S)" by (simp add: image_compose)
    also have "\<dots> = (?f ` set ?S)" by (simp add: th)
    also have "\<dots> = ((?f o ?g) ` set ?Up)" 
      by (simp only: set_map o_def image_compose[symmetric])
    also have "\<dots> = (?h ` (set ?U \<times> set ?U))"
      using \<Upsilon>_cong_aux[OF U_l, where x="x" and bs="bs", simplified set_map image_compose[symmetric]] by blast
    finally show ?thesis .
  qed
  have "\<forall> (t,n) \<in> set ?Y. bound0 (\<upsilon> ?q (t,n))"
  proof-
    { fix t n assume tnY: "(t,n) \<in> set ?Y"
      with Y_l have tnb: "numbound0 t" and np: "real n > 0" by auto
      from \<upsilon>_I[OF lq np tnb]
    have "bound0 (\<upsilon> ?q (t,n))"  by simp}
    thus ?thesis by blast
  qed
  hence ep_nb: "bound0 ?ep"  using evaldjf_bound0[where xs="?Y" and f="\<upsilon> ?q"]
    by auto

  from fr_eq_01[OF qf, where bs="bs" and x="x"] have "?lhs = ?F ?q"
    by (simp only: split_def fst_conv snd_conv)
  also have "\<dots> = (\<exists> (t,n) \<in> set ?Y. ?I x (\<upsilon> ?q (t,n)))" using \<Upsilon>_cong[OF lq YU U_l Y_l]
    by (simp only: split_def fst_conv snd_conv) 
  also have "\<dots> = (Ifm (x#bs) ?ep)" 
    using evaldjf_ex[where ps="?Y" and bs = "x#bs" and f="\<upsilon> ?q",symmetric]
    by (simp only: split_def pair_collapse)
  also have "\<dots> = (Ifm bs (decr ?ep))" using decr[OF ep_nb] by blast
  finally have lr: "?lhs = ?rhs" by (simp only: ferrack01_def Let_def)
  from decr_qf[OF ep_nb] have "qfree (ferrack01 p)" by (simp only: Let_def ferrack01_def)
  with lr show ?thesis by blast
qed

lemma cp_thm': 
  assumes lp: "iszlfm p (real (i::int)#bs)"
  and up: "d\<beta> p 1" and dd: "d\<delta> p d" and dp: "d > 0"
  shows "(\<exists> (x::int). Ifm (real x#bs) p) = ((\<exists> j\<in> {1 .. d}. Ifm (real j#bs) (minusinf p)) \<or> (\<exists> j\<in> {1.. d}. \<exists> b\<in> (Inum (real i#bs)) ` set (\<beta> p). Ifm ((b+real j)#bs) p))"
  using cp_thm[OF lp up dd dp] by auto

definition unit :: "fm \<Rightarrow> fm \<times> num list \<times> int" where
  "unit p \<equiv> (let p' = zlfm p ; l = \<zeta> p' ; q = And (Dvd l (CN 0 1 (C 0))) (a\<beta> p' l); d = \<delta> q;
             B = remdups (map simpnum (\<beta> q)) ; a = remdups (map simpnum (\<alpha> q))
             in if length B \<le> length a then (q,B,d) else (mirror q, a,d))"

lemma unit: assumes qf: "qfree p"
  shows "\<And> q B d. unit p = (q,B,d) \<Longrightarrow> ((\<exists> (x::int). Ifm (real x#bs) p) = (\<exists> (x::int). Ifm (real x#bs) q)) \<and> (Inum (real i#bs)) ` set B = (Inum (real i#bs)) ` set (\<beta> q) \<and> d\<beta> q 1 \<and> d\<delta> q d \<and> d >0 \<and> iszlfm q (real (i::int)#bs) \<and> (\<forall> b\<in> set B. numbound0 b)"
proof-
  fix q B d 
  assume qBd: "unit p = (q,B,d)"
  let ?thes = "((\<exists> (x::int). Ifm (real x#bs) p) = (\<exists> (x::int). Ifm (real x#bs) q)) \<and>
    Inum (real i#bs) ` set B = Inum (real i#bs) ` set (\<beta> q) \<and>
    d\<beta> q 1 \<and> d\<delta> q d \<and> 0 < d \<and> iszlfm q (real i # bs) \<and> (\<forall> b\<in> set B. numbound0 b)"
  let ?I = "\<lambda> (x::int) p. Ifm (real x#bs) p"
  let ?p' = "zlfm p"
  let ?l = "\<zeta> ?p'"
  let ?q = "And (Dvd ?l (CN 0 1 (C 0))) (a\<beta> ?p' ?l)"
  let ?d = "\<delta> ?q"
  let ?B = "set (\<beta> ?q)"
  let ?B'= "remdups (map simpnum (\<beta> ?q))"
  let ?A = "set (\<alpha> ?q)"
  let ?A'= "remdups (map simpnum (\<alpha> ?q))"
  from conjunct1[OF zlfm_I[OF qf, where bs="bs"]] 
  have pp': "\<forall> i. ?I i ?p' = ?I i p" by auto
  from iszlfm_gen[OF conjunct2[OF zlfm_I[OF qf, where bs="bs" and i="i"]]]
  have lp': "\<forall> (i::int). iszlfm ?p' (real i#bs)" by simp 
  hence lp'': "iszlfm ?p' (real (i::int)#bs)" by simp
  from lp' \<zeta>[where p="?p'" and bs="bs"] have lp: "?l >0" and dl: "d\<beta> ?p' ?l" by auto
  from a\<beta>_ex[where p="?p'" and l="?l" and bs="bs", OF lp'' dl lp] pp'
  have pq_ex:"(\<exists> (x::int). ?I x p) = (\<exists> x. ?I x ?q)" by (simp add: int_rdvd_iff) 
  from lp'' lp a\<beta>[OF lp'' dl lp] have lq:"iszlfm ?q (real i#bs)" and uq: "d\<beta> ?q 1" 
    by (auto simp add: isint_def)
  from \<delta>[OF lq] have dp:"?d >0" and dd: "d\<delta> ?q ?d" by blast+
  let ?N = "\<lambda> t. Inum (real (i::int)#bs) t"
  have "?N ` set ?B' = ((?N o simpnum) ` ?B)" by (simp add:image_compose) 
  also have "\<dots> = ?N ` ?B" using simpnum_ci[where bs="real i #bs"] by auto
  finally have BB': "?N ` set ?B' = ?N ` ?B" .
  have "?N ` set ?A' = ((?N o simpnum) ` ?A)" by (simp add:image_compose) 
  also have "\<dots> = ?N ` ?A" using simpnum_ci[where bs="real i #bs"] by auto
  finally have AA': "?N ` set ?A' = ?N ` ?A" .
  from \<beta>_numbound0[OF lq] have B_nb:"\<forall> b\<in> set ?B'. numbound0 b"
    by (simp add: simpnum_numbound0)
  from \<alpha>_l[OF lq] have A_nb: "\<forall> b\<in> set ?A'. numbound0 b"
    by (simp add: simpnum_numbound0)
    {assume "length ?B' \<le> length ?A'"
    hence q:"q=?q" and "B = ?B'" and d:"d = ?d"
      using qBd by (auto simp add: Let_def unit_def)
    with BB' B_nb have b: "?N ` (set B) = ?N ` set (\<beta> q)" 
      and bn: "\<forall>b\<in> set B. numbound0 b" by simp+ 
  with pq_ex dp uq dd lq q d have ?thes by simp}
  moreover 
  {assume "\<not> (length ?B' \<le> length ?A')"
    hence q:"q=mirror ?q" and "B = ?A'" and d:"d = ?d"
      using qBd by (auto simp add: Let_def unit_def)
    with AA' mirror\<alpha>\<beta>[OF lq] A_nb have b:"?N ` (set B) = ?N ` set (\<beta> q)" 
      and bn: "\<forall>b\<in> set B. numbound0 b" by simp+
    from mirror_ex[OF lq] pq_ex q 
    have pqm_eq:"(\<exists> (x::int). ?I x p) = (\<exists> (x::int). ?I x q)" by simp
    from lq uq q mirror_d\<beta> [where p="?q" and bs="bs" and a="real i"]
    have lq': "iszlfm q (real i#bs)" and uq: "d\<beta> q 1" by auto
    from \<delta>[OF lq'] mirror_\<delta>[OF lq] q d have dq:"d\<delta> q d " by auto
    from pqm_eq b bn uq lq' dp dq q dp d have ?thes by simp
  }
  ultimately show ?thes by blast
qed
    (* Cooper's Algorithm *)

definition cooper :: "fm \<Rightarrow> fm" where
  "cooper p \<equiv> 
  (let (q,B,d) = unit p; js = [1..d];
       mq = simpfm (minusinf q);
       md = evaldjf (\<lambda> j. simpfm (subst0 (C j) mq)) js
   in if md = T then T else
    (let qd = evaldjf (\<lambda> t. simpfm (subst0 t q)) 
                               (remdups (map (\<lambda> (b,j). simpnum (Add b (C j))) 
                                            [(b,j). b\<leftarrow>B,j\<leftarrow>js]))
     in decr (disj md qd)))"
lemma cooper: assumes qf: "qfree p"
  shows "((\<exists> (x::int). Ifm (real x#bs) p) = (Ifm bs (cooper p))) \<and> qfree (cooper p)" 
  (is "(?lhs = ?rhs) \<and> _")
proof-

  let ?I = "\<lambda> (x::int) p. Ifm (real x#bs) p"
  let ?q = "fst (unit p)"
  let ?B = "fst (snd(unit p))"
  let ?d = "snd (snd (unit p))"
  let ?js = "[1..?d]"
  let ?mq = "minusinf ?q"
  let ?smq = "simpfm ?mq"
  let ?md = "evaldjf (\<lambda> j. simpfm (subst0 (C j) ?smq)) ?js"
  fix i
  let ?N = "\<lambda> t. Inum (real (i::int)#bs) t"
  let ?bjs = "[(b,j). b\<leftarrow>?B,j\<leftarrow>?js]"
  let ?sbjs = "map (\<lambda> (b,j). simpnum (Add b (C j))) ?bjs"
  let ?qd = "evaldjf (\<lambda> t. simpfm (subst0 t ?q)) (remdups ?sbjs)"
  have qbf:"unit p = (?q,?B,?d)" by simp
  from unit[OF qf qbf] have pq_ex: "(\<exists>(x::int). ?I x p) = (\<exists> (x::int). ?I x ?q)" and 
    B:"?N ` set ?B = ?N ` set (\<beta> ?q)" and 
    uq:"d\<beta> ?q 1" and dd: "d\<delta> ?q ?d" and dp: "?d > 0" and 
    lq: "iszlfm ?q (real i#bs)" and 
    Bn: "\<forall> b\<in> set ?B. numbound0 b" by auto
  from zlin_qfree[OF lq] have qfq: "qfree ?q" .
  from simpfm_qf[OF minusinf_qfree[OF qfq]] have qfmq: "qfree ?smq".
  have jsnb: "\<forall> j \<in> set ?js. numbound0 (C j)" by simp
  hence "\<forall> j\<in> set ?js. bound0 (subst0 (C j) ?smq)" 
    by (auto simp only: subst0_bound0[OF qfmq])
  hence th: "\<forall> j\<in> set ?js. bound0 (simpfm (subst0 (C j) ?smq))"
    by (auto simp add: simpfm_bound0)
  from evaldjf_bound0[OF th] have mdb: "bound0 ?md" by simp 
  from Bn jsnb have "\<forall> (b,j) \<in> set ?bjs. numbound0 (Add b (C j))"
    by simp
  hence "\<forall> (b,j) \<in> set ?bjs. numbound0 (simpnum (Add b (C j)))"
    using simpnum_numbound0 by blast
  hence "\<forall> t \<in> set ?sbjs. numbound0 t" by simp
  hence "\<forall> t \<in> set (remdups ?sbjs). bound0 (subst0 t ?q)"
    using subst0_bound0[OF qfq] by auto 
  hence th': "\<forall> t \<in> set (remdups ?sbjs). bound0 (simpfm (subst0 t ?q))"
    using simpfm_bound0 by blast
  from evaldjf_bound0 [OF th'] have qdb: "bound0 ?qd" by simp
  from mdb qdb 
  have mdqdb: "bound0 (disj ?md ?qd)" by (simp only: disj_def, cases "?md=T \<or> ?qd=T", simp_all)
  from trans [OF pq_ex cp_thm'[OF lq uq dd dp]] B
  have "?lhs = (\<exists> j\<in> {1.. ?d}. ?I j ?mq \<or> (\<exists> b\<in> ?N ` set ?B. Ifm ((b+ real j)#bs) ?q))" by auto
  also have "\<dots> = ((\<exists> j\<in> set ?js. ?I j ?smq) \<or> (\<exists> (b,j) \<in> (?N ` set ?B \<times> set ?js). Ifm ((b+ real j)#bs) ?q))" by auto
  also have "\<dots>= ((\<exists> j\<in> set ?js. ?I j ?smq) \<or> (\<exists> t \<in> (\<lambda> (b,j). ?N (Add b (C j))) ` set ?bjs. Ifm (t #bs) ?q))" by simp
  also have "\<dots>= ((\<exists> j\<in> set ?js. ?I j ?smq) \<or> (\<exists> t \<in> (\<lambda> (b,j). ?N (simpnum (Add b (C j)))) ` set ?bjs. Ifm (t #bs) ?q))" by (simp only: simpnum_ci)
  also  have "\<dots>= ((\<exists> j\<in> set ?js. ?I j ?smq) \<or> (\<exists> t \<in> set ?sbjs. Ifm (?N t #bs) ?q))" 
    by (auto simp add: split_def) 
  also have "\<dots> = ((\<exists> j\<in> set ?js. (\<lambda> j. ?I i (simpfm (subst0 (C j) ?smq))) j) \<or> (\<exists> t \<in> set (remdups ?sbjs). (\<lambda> t. ?I i (simpfm (subst0 t ?q))) t))" by (simp only: simpfm subst0_I[OF qfq] simpfm Inum.simps subst0_I[OF qfmq] set_remdups)
  also have "\<dots> = ((?I i (evaldjf (\<lambda> j. simpfm (subst0 (C j) ?smq)) ?js)) \<or> (?I i (evaldjf (\<lambda> t. simpfm (subst0 t ?q)) (remdups ?sbjs))))" by (simp only: evaldjf_ex)
  finally have mdqd: "?lhs = (?I i (disj ?md ?qd))" by (simp add: disj) 
  hence mdqd2: "?lhs = (Ifm bs (decr (disj ?md ?qd)))" using decr [OF mdqdb] by simp
  {assume mdT: "?md = T"
    hence cT:"cooper p = T" 
      by (simp only: cooper_def unit_def split_def Let_def if_True) simp
    from mdT mdqd have lhs:"?lhs" by (auto simp add: disj)
    from mdT have "?rhs" by (simp add: cooper_def unit_def split_def)
    with lhs cT have ?thesis by simp }
  moreover
  {assume mdT: "?md \<noteq> T" hence "cooper p = decr (disj ?md ?qd)" 
      by (simp only: cooper_def unit_def split_def Let_def if_False) 
    with mdqd2 decr_qf[OF mdqdb] have ?thesis by simp }
  ultimately show ?thesis by blast
qed

lemma DJcooper: 
  assumes qf: "qfree p"
  shows "((\<exists> (x::int). Ifm (real x#bs) p) = (Ifm bs (DJ cooper p))) \<and> qfree (DJ cooper p)"
proof-
  from cooper have cqf: "\<forall> p. qfree p \<longrightarrow> qfree (cooper p)" by  blast
  from DJ_qf[OF cqf] qf have thqf:"qfree (DJ cooper p)" by blast
  have "Ifm bs (DJ cooper p) = (\<exists> q\<in> set (disjuncts p). Ifm bs (cooper q))" 
     by (simp add: DJ_def evaldjf_ex)
  also have "\<dots> = (\<exists> q \<in> set(disjuncts p). \<exists> (x::int). Ifm (real x#bs)  q)" 
    using cooper disjuncts_qf[OF qf] by blast
  also have "\<dots> = (\<exists> (x::int). Ifm (real x#bs) p)" by (induct p rule: disjuncts.induct, auto)
  finally show ?thesis using thqf by blast
qed

    (* Redy and Loveland *)

lemma \<sigma>\<rho>_cong: assumes lp: "iszlfm p (a#bs)" and tt': "Inum (a#bs) t = Inum (a#bs) t'"
  shows "Ifm (a#bs) (\<sigma>\<rho> p (t,c)) = Ifm (a#bs) (\<sigma>\<rho> p (t',c))"
  using lp 
  by (induct p rule: iszlfm.induct, auto simp add: tt')

lemma \<sigma>_cong: assumes lp: "iszlfm p (a#bs)" and tt': "Inum (a#bs) t = Inum (a#bs) t'"
  shows "Ifm (a#bs) (\<sigma> p c t) = Ifm (a#bs) (\<sigma> p c t')"
  by (simp add: \<sigma>_def tt' \<sigma>\<rho>_cong[OF lp tt'])

lemma \<rho>_cong: assumes lp: "iszlfm p (a#bs)" 
  and RR: "(\<lambda>(b,k). (Inum (a#bs) b,k)) ` R =  (\<lambda>(b,k). (Inum (a#bs) b,k)) ` set (\<rho> p)"
  shows "(\<exists> (e,c) \<in> R. \<exists> j\<in> {1.. c*(\<delta> p)}. Ifm (a#bs) (\<sigma> p c (Add e (C j)))) = (\<exists> (e,c) \<in> set (\<rho> p). \<exists> j\<in> {1.. c*(\<delta> p)}. Ifm (a#bs) (\<sigma> p c (Add e (C j))))"
  (is "?lhs = ?rhs")
proof
  let ?d = "\<delta> p"
  assume ?lhs then obtain e c j where ecR: "(e,c) \<in> R" and jD:"j \<in> {1 .. c*?d}" 
    and px: "Ifm (a#bs) (\<sigma> p c (Add e (C j)))" (is "?sp c e j") by blast
  from ecR have "(Inum (a#bs) e,c) \<in> (\<lambda>(b,k). (Inum (a#bs) b,k)) ` R" by auto
  hence "(Inum (a#bs) e,c) \<in> (\<lambda>(b,k). (Inum (a#bs) b,k)) ` set (\<rho> p)" using RR by simp
  hence "\<exists> (e',c') \<in> set (\<rho> p). Inum (a#bs) e = Inum (a#bs) e' \<and> c = c'" by auto
  then obtain e' c' where ecRo:"(e',c') \<in> set (\<rho> p)" and ee':"Inum (a#bs) e = Inum (a#bs) e'"
    and cc':"c = c'" by blast
  from ee' have tt': "Inum (a#bs) (Add e (C j)) = Inum (a#bs) (Add e' (C j))" by simp
  
  from \<sigma>_cong[OF lp tt', where c="c"] px have px':"?sp c e' j" by simp
  from ecRo jD px' cc'  show ?rhs apply auto 
    by (rule_tac x="(e', c')" in bexI,simp_all)
  (rule_tac x="j" in bexI, simp_all add: cc'[symmetric])
next
  let ?d = "\<delta> p"
  assume ?rhs then obtain e c j where ecR: "(e,c) \<in> set (\<rho> p)" and jD:"j \<in> {1 .. c*?d}" 
    and px: "Ifm (a#bs) (\<sigma> p c (Add e (C j)))" (is "?sp c e j") by blast
  from ecR have "(Inum (a#bs) e,c) \<in> (\<lambda>(b,k). (Inum (a#bs) b,k)) ` set (\<rho> p)" by auto
  hence "(Inum (a#bs) e,c) \<in> (\<lambda>(b,k). (Inum (a#bs) b,k)) ` R" using RR by simp
  hence "\<exists> (e',c') \<in> R. Inum (a#bs) e = Inum (a#bs) e' \<and> c = c'" by auto
  then obtain e' c' where ecRo:"(e',c') \<in> R" and ee':"Inum (a#bs) e = Inum (a#bs) e'"
    and cc':"c = c'" by blast
  from ee' have tt': "Inum (a#bs) (Add e (C j)) = Inum (a#bs) (Add e' (C j))" by simp
  from \<sigma>_cong[OF lp tt', where c="c"] px have px':"?sp c e' j" by simp
  from ecRo jD px' cc'  show ?lhs apply auto 
    by (rule_tac x="(e', c')" in bexI,simp_all)
  (rule_tac x="j" in bexI, simp_all add: cc'[symmetric])
qed

lemma rl_thm': 
  assumes lp: "iszlfm p (real (i::int)#bs)" 
  and R: "(\<lambda>(b,k). (Inum (a#bs) b,k)) ` R =  (\<lambda>(b,k). (Inum (a#bs) b,k)) ` set (\<rho> p)"
  shows "(\<exists> (x::int). Ifm (real x#bs) p) = ((\<exists> j\<in> {1 .. \<delta> p}. Ifm (real j#bs) (minusinf p)) \<or> (\<exists> (e,c) \<in> R. \<exists> j\<in> {1.. c*(\<delta> p)}. Ifm (a#bs) (\<sigma> p c (Add e (C j)))))"
  using rl_thm[OF lp] \<rho>_cong[OF iszlfm_gen[OF lp, rule_format, where y="a"] R] by simp 

definition chooset :: "fm \<Rightarrow> fm \<times> ((num\<times>int) list) \<times> int" where
  "chooset p \<equiv> (let q = zlfm p ; d = \<delta> q;
             B = remdups (map (\<lambda> (t,k). (simpnum t,k)) (\<rho> q)) ; 
             a = remdups (map (\<lambda> (t,k). (simpnum t,k)) (\<alpha>\<rho> q))
             in if length B \<le> length a then (q,B,d) else (mirror q, a,d))"

lemma chooset: assumes qf: "qfree p"
  shows "\<And> q B d. chooset p = (q,B,d) \<Longrightarrow> ((\<exists> (x::int). Ifm (real x#bs) p) = (\<exists> (x::int). Ifm (real x#bs) q)) \<and> ((\<lambda>(t,k). (Inum (real i#bs) t,k)) ` set B = (\<lambda>(t,k). (Inum (real i#bs) t,k)) ` set (\<rho> q)) \<and> (\<delta> q = d) \<and> d >0 \<and> iszlfm q (real (i::int)#bs) \<and> (\<forall> (e,c)\<in> set B. numbound0 e \<and> c>0)"
proof-
  fix q B d 
  assume qBd: "chooset p = (q,B,d)"
  let ?thes = "((\<exists> (x::int). Ifm (real x#bs) p) = (\<exists> (x::int). Ifm (real x#bs) q)) \<and> ((\<lambda>(t,k). (Inum (real i#bs) t,k)) ` set B = (\<lambda>(t,k). (Inum (real i#bs) t,k)) ` set (\<rho> q)) \<and> (\<delta> q = d) \<and> d >0 \<and> iszlfm q (real (i::int)#bs) \<and> (\<forall> (e,c)\<in> set B. numbound0 e \<and> c>0)" 
  let ?I = "\<lambda> (x::int) p. Ifm (real x#bs) p"
  let ?q = "zlfm p"
  let ?d = "\<delta> ?q"
  let ?B = "set (\<rho> ?q)"
  let ?f = "\<lambda> (t,k). (simpnum t,k)"
  let ?B'= "remdups (map ?f (\<rho> ?q))"
  let ?A = "set (\<alpha>\<rho> ?q)"
  let ?A'= "remdups (map ?f (\<alpha>\<rho> ?q))"
  from conjunct1[OF zlfm_I[OF qf, where bs="bs"]] 
  have pp': "\<forall> i. ?I i ?q = ?I i p" by auto
  hence pq_ex:"(\<exists> (x::int). ?I x p) = (\<exists> x. ?I x ?q)" by simp 
  from iszlfm_gen[OF conjunct2[OF zlfm_I[OF qf, where bs="bs" and i="i"]], rule_format, where y="real i"]
  have lq: "iszlfm ?q (real (i::int)#bs)" . 
  from \<delta>[OF lq] have dp:"?d >0" by blast
  let ?N = "\<lambda> (t,c). (Inum (real (i::int)#bs) t,c)"
  have "?N ` set ?B' = ((?N o ?f) ` ?B)" by (simp add: split_def image_compose)
  also have "\<dots> = ?N ` ?B"
    by(simp add: split_def image_compose simpnum_ci[where bs="real i #bs"] image_def)
  finally have BB': "?N ` set ?B' = ?N ` ?B" .
  have "?N ` set ?A' = ((?N o ?f) ` ?A)" by (simp add: split_def image_compose) 
  also have "\<dots> = ?N ` ?A" using simpnum_ci[where bs="real i #bs"]
    by(simp add: split_def image_compose simpnum_ci[where bs="real i #bs"] image_def) 
  finally have AA': "?N ` set ?A' = ?N ` ?A" .
  from \<rho>_l[OF lq] have B_nb:"\<forall> (e,c)\<in> set ?B'. numbound0 e \<and> c > 0"
    by (simp add: simpnum_numbound0 split_def)
  from \<alpha>\<rho>_l[OF lq] have A_nb: "\<forall> (e,c)\<in> set ?A'. numbound0 e \<and> c > 0"
    by (simp add: simpnum_numbound0 split_def)
    {assume "length ?B' \<le> length ?A'"
    hence q:"q=?q" and "B = ?B'" and d:"d = ?d"
      using qBd by (auto simp add: Let_def chooset_def)
    with BB' B_nb have b: "?N ` (set B) = ?N ` set (\<rho> q)" 
      and bn: "\<forall>(e,c)\<in> set B. numbound0 e \<and> c > 0" by auto
  with pq_ex dp lq q d have ?thes by simp}
  moreover 
  {assume "\<not> (length ?B' \<le> length ?A')"
    hence q:"q=mirror ?q" and "B = ?A'" and d:"d = ?d"
      using qBd by (auto simp add: Let_def chooset_def)
    with AA' mirror_\<alpha>\<rho>[OF lq] A_nb have b:"?N ` (set B) = ?N ` set (\<rho> q)" 
      and bn: "\<forall>(e,c)\<in> set B. numbound0 e \<and> c > 0" by auto 
    from mirror_ex[OF lq] pq_ex q 
    have pqm_eq:"(\<exists> (x::int). ?I x p) = (\<exists> (x::int). ?I x q)" by simp
    from lq q mirror_l [where p="?q" and bs="bs" and a="real i"]
    have lq': "iszlfm q (real i#bs)" by auto
    from mirror_\<delta>[OF lq] pqm_eq b bn lq' dp q dp d have ?thes by simp
  }
  ultimately show ?thes by blast
qed

definition stage :: "fm \<Rightarrow> int \<Rightarrow> (num \<times> int) \<Rightarrow> fm" where
  "stage p d \<equiv> (\<lambda> (e,c). evaldjf (\<lambda> j. simpfm (\<sigma> p c (Add e (C j)))) [1..c*d])"
lemma stage:
  shows "Ifm bs (stage p d (e,c)) = (\<exists> j\<in>{1 .. c*d}. Ifm bs (\<sigma> p c (Add e (C j))))"
  by (unfold stage_def split_def ,simp only: evaldjf_ex simpfm) simp

lemma stage_nb: assumes lp: "iszlfm p (a#bs)" and cp: "c >0" and nb:"numbound0 e"
  shows "bound0 (stage p d (e,c))"
proof-
  let ?f = "\<lambda> j. simpfm (\<sigma> p c (Add e (C j)))"
  have th: "\<forall> j\<in> set [1..c*d]. bound0 (?f j)"
  proof
    fix j
    from nb have nb':"numbound0 (Add e (C j))" by simp
    from simpfm_bound0[OF \<sigma>_nb[OF lp nb', where k="c"]]
    show "bound0 (simpfm (\<sigma> p c (Add e (C j))))" .
  qed
  from evaldjf_bound0[OF th] show ?thesis by (unfold stage_def split_def) simp
qed

definition redlove :: "fm \<Rightarrow> fm" where
  "redlove p \<equiv> 
  (let (q,B,d) = chooset p;
       mq = simpfm (minusinf q);
       md = evaldjf (\<lambda> j. simpfm (subst0 (C j) mq)) [1..d]
   in if md = T then T else
    (let qd = evaldjf (stage q d) B
     in decr (disj md qd)))"

lemma redlove: assumes qf: "qfree p"
  shows "((\<exists> (x::int). Ifm (real x#bs) p) = (Ifm bs (redlove p))) \<and> qfree (redlove p)" 
  (is "(?lhs = ?rhs) \<and> _")
proof-

  let ?I = "\<lambda> (x::int) p. Ifm (real x#bs) p"
  let ?q = "fst (chooset p)"
  let ?B = "fst (snd(chooset p))"
  let ?d = "snd (snd (chooset p))"
  let ?js = "[1..?d]"
  let ?mq = "minusinf ?q"
  let ?smq = "simpfm ?mq"
  let ?md = "evaldjf (\<lambda> j. simpfm (subst0 (C j) ?smq)) ?js"
  fix i
  let ?N = "\<lambda> (t,k). (Inum (real (i::int)#bs) t,k)"
  let ?qd = "evaldjf (stage ?q ?d) ?B"
  have qbf:"chooset p = (?q,?B,?d)" by simp
  from chooset[OF qf qbf] have pq_ex: "(\<exists>(x::int). ?I x p) = (\<exists> (x::int). ?I x ?q)" and 
    B:"?N ` set ?B = ?N ` set (\<rho> ?q)" and dd: "\<delta> ?q = ?d" and dp: "?d > 0" and 
    lq: "iszlfm ?q (real i#bs)" and 
    Bn: "\<forall> (e,c)\<in> set ?B. numbound0 e \<and> c > 0" by auto
  from zlin_qfree[OF lq] have qfq: "qfree ?q" .
  from simpfm_qf[OF minusinf_qfree[OF qfq]] have qfmq: "qfree ?smq".
  have jsnb: "\<forall> j \<in> set ?js. numbound0 (C j)" by simp
  hence "\<forall> j\<in> set ?js. bound0 (subst0 (C j) ?smq)" 
    by (auto simp only: subst0_bound0[OF qfmq])
  hence th: "\<forall> j\<in> set ?js. bound0 (simpfm (subst0 (C j) ?smq))"
    by (auto simp add: simpfm_bound0)
  from evaldjf_bound0[OF th] have mdb: "bound0 ?md" by simp 
  from Bn stage_nb[OF lq] have th:"\<forall> x \<in> set ?B. bound0 (stage ?q ?d x)" by auto
  from evaldjf_bound0[OF th]  have qdb: "bound0 ?qd" .
  from mdb qdb 
  have mdqdb: "bound0 (disj ?md ?qd)" by (simp only: disj_def, cases "?md=T \<or> ?qd=T", simp_all)
  from trans [OF pq_ex rl_thm'[OF lq B]] dd
  have "?lhs = ((\<exists> j\<in> {1.. ?d}. ?I j ?mq) \<or> (\<exists> (e,c)\<in> set ?B. \<exists> j\<in> {1 .. c*?d}. Ifm (real i#bs) (\<sigma> ?q c (Add e (C j)))))" by auto
  also have "\<dots> = ((\<exists> j\<in> {1.. ?d}. ?I j ?smq) \<or> (\<exists> (e,c)\<in> set ?B. ?I i (stage ?q ?d (e,c) )))" 
    by (simp add: simpfm stage split_def)
  also have "\<dots> = ((\<exists> j\<in> {1 .. ?d}. ?I i (subst0 (C j) ?smq))  \<or> ?I i ?qd)"
    by (simp add: evaldjf_ex subst0_I[OF qfmq])
  finally have mdqd:"?lhs = (?I i ?md \<or> ?I i ?qd)" by (simp only: evaldjf_ex set_upto simpfm) 
  also have "\<dots> = (?I i (disj ?md ?qd))" by (simp add: disj)
  also have "\<dots> = (Ifm bs (decr (disj ?md ?qd)))" by (simp only: decr [OF mdqdb]) 
  finally have mdqd2: "?lhs = (Ifm bs (decr (disj ?md ?qd)))" . 
  {assume mdT: "?md = T"
    hence cT:"redlove p = T" by (simp add: redlove_def Let_def chooset_def split_def)
    from mdT have lhs:"?lhs" using mdqd by simp 
    from mdT have "?rhs" by (simp add: redlove_def chooset_def split_def)
    with lhs cT have ?thesis by simp }
  moreover
  {assume mdT: "?md \<noteq> T" hence "redlove p = decr (disj ?md ?qd)" 
      by (simp add: redlove_def chooset_def split_def Let_def)
    with mdqd2 decr_qf[OF mdqdb] have ?thesis by simp }
  ultimately show ?thesis by blast
qed

lemma DJredlove: 
  assumes qf: "qfree p"
  shows "((\<exists> (x::int). Ifm (real x#bs) p) = (Ifm bs (DJ redlove p))) \<and> qfree (DJ redlove p)"
proof-
  from redlove have cqf: "\<forall> p. qfree p \<longrightarrow> qfree (redlove p)" by  blast
  from DJ_qf[OF cqf] qf have thqf:"qfree (DJ redlove p)" by blast
  have "Ifm bs (DJ redlove p) = (\<exists> q\<in> set (disjuncts p). Ifm bs (redlove q))" 
     by (simp add: DJ_def evaldjf_ex)
  also have "\<dots> = (\<exists> q \<in> set(disjuncts p). \<exists> (x::int). Ifm (real x#bs)  q)" 
    using redlove disjuncts_qf[OF qf] by blast
  also have "\<dots> = (\<exists> (x::int). Ifm (real x#bs) p)" by (induct p rule: disjuncts.induct, auto)
  finally show ?thesis using thqf by blast
qed


lemma exsplit_qf: assumes qf: "qfree p"
  shows "qfree (exsplit p)"
using qf by (induct p rule: exsplit.induct, auto)

definition mircfr :: "fm \<Rightarrow> fm" where
  "mircfr = DJ cooper o ferrack01 o simpfm o exsplit"

definition mirlfr :: "fm \<Rightarrow> fm" where
  "mirlfr = DJ redlove o ferrack01 o simpfm o exsplit"

lemma mircfr: "\<forall> bs p. qfree p \<longrightarrow> qfree (mircfr p) \<and> Ifm bs (mircfr p) = Ifm bs (E p)"
proof(clarsimp simp del: Ifm.simps)
  fix bs p
  assume qf: "qfree p"
  show "qfree (mircfr p)\<and>(Ifm bs (mircfr p) = Ifm bs (E p))" (is "_ \<and> (?lhs = ?rhs)")
  proof-
    let ?es = "(And (And (Ge (CN 0 1 (C 0))) (Lt (CN 0 1 (C (- 1))))) (simpfm (exsplit p)))"
    have "?rhs = (\<exists> (i::int). \<exists> x. Ifm (x#real i#bs) ?es)" 
      using splitex[OF qf] by simp
    with ferrack01[OF simpfm_qf[OF exsplit_qf[OF qf]]] have th1: "?rhs = (\<exists> (i::int). Ifm (real i#bs) (ferrack01 (simpfm (exsplit p))))" and qf':"qfree (ferrack01 (simpfm (exsplit p)))" by simp+
    with DJcooper[OF qf'] show ?thesis by (simp add: mircfr_def)
  qed
qed
  
lemma mirlfr: "\<forall> bs p. qfree p \<longrightarrow> qfree(mirlfr p) \<and> Ifm bs (mirlfr p) = Ifm bs (E p)"
proof(clarsimp simp del: Ifm.simps)
  fix bs p
  assume qf: "qfree p"
  show "qfree (mirlfr p)\<and>(Ifm bs (mirlfr p) = Ifm bs (E p))" (is "_ \<and> (?lhs = ?rhs)")
  proof-
    let ?es = "(And (And (Ge (CN 0 1 (C 0))) (Lt (CN 0 1 (C (- 1))))) (simpfm (exsplit p)))"
    have "?rhs = (\<exists> (i::int). \<exists> x. Ifm (x#real i#bs) ?es)" 
      using splitex[OF qf] by simp
    with ferrack01[OF simpfm_qf[OF exsplit_qf[OF qf]]] have th1: "?rhs = (\<exists> (i::int). Ifm (real i#bs) (ferrack01 (simpfm (exsplit p))))" and qf':"qfree (ferrack01 (simpfm (exsplit p)))" by simp+
    with DJredlove[OF qf'] show ?thesis by (simp add: mirlfr_def)
  qed
qed
  
definition mircfrqe:: "fm \<Rightarrow> fm" where
  "mircfrqe p = qelim (prep p) mircfr"

definition mirlfrqe:: "fm \<Rightarrow> fm" where
  "mirlfrqe p = qelim (prep p) mirlfr"

theorem mircfrqe: "(Ifm bs (mircfrqe p) = Ifm bs p) \<and> qfree (mircfrqe p)"
  using qelim_ci[OF mircfr] prep by (auto simp add: mircfrqe_def)

theorem mirlfrqe: "(Ifm bs (mirlfrqe p) = Ifm bs p) \<and> qfree (mirlfrqe p)"
  using qelim_ci[OF mirlfr] prep by (auto simp add: mirlfrqe_def)

definition
  "problem1 = A (And (Le (Sub (Floor (Bound 0)) (Bound 0))) (Le (Add (Bound 0) (Floor (Neg (Bound 0))))))"

definition
  "problem2 = A (Iff (Eq (Add (Floor (Bound 0)) (Floor (Neg (Bound 0))))) (Eq (Sub (Floor (Bound 0)) (Bound 0))))"

definition
  "problem3 = A (And (Le (Sub (Floor (Bound 0)) (Bound 0))) (Le (Add (Bound 0) (Floor (Neg (Bound 0))))))"

definition
  "problem4 = E (And (Ge (Sub (Bound 1) (Bound 0))) (Eq (Add (Floor (Bound 1)) (Floor (Neg (Bound 0))))))"

ML {*
  Par_List.map (fn e => e ())
   [fn () => @{code mircfrqe} @{code problem1},
    fn () => @{code mirlfrqe} @{code problem1},
    fn () => @{code mircfrqe} @{code problem2},
    fn () => @{code mirlfrqe} @{code problem2},
    fn () => @{code mircfrqe} @{code problem3},
    fn () => @{code mirlfrqe} @{code problem3},
    fn () => @{code mircfrqe} @{code problem4},
    fn () => @{code mirlfrqe} @{code problem4}]
*}

(*code_reflect Mir
  functions mircfrqe mirlfrqe
  file "mir.ML"*)

oracle mirfr_oracle = {* fn (proofs, ct) =>
let

fun num_of_term vs (t as Free (xn, xT)) = (case AList.lookup (op =) vs t
     of NONE => error "Variable not found in the list!"
      | SOME n => @{code Bound} n)
  | num_of_term vs @{term "real (0::int)"} = @{code C} 0
  | num_of_term vs @{term "real (1::int)"} = @{code C} 1
  | num_of_term vs @{term "0::real"} = @{code C} 0
  | num_of_term vs @{term "1::real"} = @{code C} 1
  | num_of_term vs (Bound i) = @{code Bound} i
  | num_of_term vs (@{term "uminus :: real \<Rightarrow> real"} $ t') = @{code Neg} (num_of_term vs t')
  | num_of_term vs (@{term "op + :: real \<Rightarrow> real \<Rightarrow> real"} $ t1 $ t2) =
      @{code Add} (num_of_term vs t1, num_of_term vs t2)
  | num_of_term vs (@{term "op - :: real \<Rightarrow> real \<Rightarrow> real"} $ t1 $ t2) =
      @{code Sub} (num_of_term vs t1, num_of_term vs t2)
  | num_of_term vs (@{term "op * :: real \<Rightarrow> real \<Rightarrow> real"} $ t1 $ t2) =
      (case (num_of_term vs t1)
       of @{code C} i => @{code Mul} (i, num_of_term vs t2)
        | _ => error "num_of_term: unsupported Multiplication")
  | num_of_term vs (@{term "real :: int \<Rightarrow> real"} $ (@{term "numeral :: _ \<Rightarrow> int"} $ t')) =
      @{code C} (HOLogic.dest_num t')
  | num_of_term vs (@{term "real :: int \<Rightarrow> real"} $ (@{term "neg_numeral :: _ \<Rightarrow> int"} $ t')) =
      @{code C} (~ (HOLogic.dest_num t'))
  | num_of_term vs (@{term "real :: int \<Rightarrow> real"} $ (@{term "floor :: real \<Rightarrow> int"} $ t')) =
      @{code Floor} (num_of_term vs t')
  | num_of_term vs (@{term "real :: int \<Rightarrow> real"} $ (@{term "ceiling :: real \<Rightarrow> int"} $ t')) =
      @{code Neg} (@{code Floor} (@{code Neg} (num_of_term vs t')))
  | num_of_term vs (@{term "numeral :: _ \<Rightarrow> real"} $ t') =
      @{code C} (HOLogic.dest_num t')
  | num_of_term vs (@{term "neg_numeral :: _ \<Rightarrow> real"} $ t') =
      @{code C} (~ (HOLogic.dest_num t'))
  | num_of_term vs t = error ("num_of_term: unknown term " ^ Syntax.string_of_term @{context} t);

fun fm_of_term vs @{term True} = @{code T}
  | fm_of_term vs @{term False} = @{code F}
  | fm_of_term vs (@{term "op < :: real \<Rightarrow> real \<Rightarrow> bool"} $ t1 $ t2) =
      @{code Lt} (@{code Sub} (num_of_term vs t1, num_of_term vs t2))
  | fm_of_term vs (@{term "op \<le> :: real \<Rightarrow> real \<Rightarrow> bool"} $ t1 $ t2) =
      @{code Le} (@{code Sub} (num_of_term vs t1, num_of_term vs t2))
  | fm_of_term vs (@{term "op = :: real \<Rightarrow> real \<Rightarrow> bool"} $ t1 $ t2) =
      @{code Eq} (@{code Sub} (num_of_term vs t1, num_of_term vs t2)) 
  | fm_of_term vs (@{term "op rdvd"} $ (@{term "real :: int \<Rightarrow> real"} $ (@{term "numeral :: _ \<Rightarrow> int"} $ t1)) $ t2) =
      @{code Dvd} (HOLogic.dest_num t1, num_of_term vs t2)
  | fm_of_term vs (@{term "op rdvd"} $ (@{term "real :: int \<Rightarrow> real"} $ (@{term "neg_numeral :: _ \<Rightarrow> int"} $ t1)) $ t2) =
      @{code Dvd} (~ (HOLogic.dest_num t1), num_of_term vs t2)
  | fm_of_term vs (@{term "op = :: bool \<Rightarrow> bool \<Rightarrow> bool"} $ t1 $ t2) =
      @{code Iff} (fm_of_term vs t1, fm_of_term vs t2)
  | fm_of_term vs (@{term HOL.conj} $ t1 $ t2) =
      @{code And} (fm_of_term vs t1, fm_of_term vs t2)
  | fm_of_term vs (@{term HOL.disj} $ t1 $ t2) =
      @{code Or} (fm_of_term vs t1, fm_of_term vs t2)
  | fm_of_term vs (@{term HOL.implies} $ t1 $ t2) =
      @{code Imp} (fm_of_term vs t1, fm_of_term vs t2)
  | fm_of_term vs (@{term "Not"} $ t') =
      @{code NOT} (fm_of_term vs t')
  | fm_of_term vs (Const (@{const_name Ex}, _) $ Abs (xn, xT, p)) =
      @{code E} (fm_of_term (map (fn (v, n) => (v, n + 1)) vs) p)
  | fm_of_term vs (Const (@{const_name All}, _) $ Abs (xn, xT, p)) =
      @{code A} (fm_of_term (map (fn (v, n) => (v, n + 1)) vs) p)
  | fm_of_term vs t = error ("fm_of_term : unknown term " ^ Syntax.string_of_term @{context} t);

fun term_of_num vs (@{code C} i) = @{term "real :: int \<Rightarrow> real"} $ HOLogic.mk_number HOLogic.intT i
  | term_of_num vs (@{code Bound} n) = fst (the (find_first (fn (_, m) => n = m) vs))
  | term_of_num vs (@{code Neg} (@{code Floor} (@{code Neg} t'))) =
      @{term "real :: int \<Rightarrow> real"} $ (@{term "ceiling :: real \<Rightarrow> int"} $ term_of_num vs t')
  | term_of_num vs (@{code Neg} t') = @{term "uminus :: real \<Rightarrow> real"} $ term_of_num vs t'
  | term_of_num vs (@{code Add} (t1, t2)) = @{term "op + :: real \<Rightarrow> real \<Rightarrow> real"} $
      term_of_num vs t1 $ term_of_num vs t2
  | term_of_num vs (@{code Sub} (t1, t2)) = @{term "op - :: real \<Rightarrow> real \<Rightarrow> real"} $
      term_of_num vs t1 $ term_of_num vs t2
  | term_of_num vs (@{code Mul} (i, t2)) = @{term "op * :: real \<Rightarrow> real \<Rightarrow> real"} $
      term_of_num vs (@{code C} i) $ term_of_num vs t2
  | term_of_num vs (@{code Floor} t) = @{term "real :: int \<Rightarrow> real"} $ (@{term "floor :: real \<Rightarrow> int"} $ term_of_num vs t)
  | term_of_num vs (@{code CN} (n, i, t)) = term_of_num vs (@{code Add} (@{code Mul} (i, @{code Bound} n), t))
  | term_of_num vs (@{code CF} (c, t, s)) = term_of_num vs (@{code Add} (@{code Mul} (c, @{code Floor} t), s));

fun term_of_fm vs @{code T} = @{term True} 
  | term_of_fm vs @{code F} = @{term False}
  | term_of_fm vs (@{code Lt} t) =
      @{term "op < :: real \<Rightarrow> real \<Rightarrow> bool"} $ term_of_num vs t $ @{term "0::real"}
  | term_of_fm vs (@{code Le} t) =
      @{term "op \<le> :: real \<Rightarrow> real \<Rightarrow> bool"} $ term_of_num vs t $ @{term "0::real"}
  | term_of_fm vs (@{code Gt} t) =
      @{term "op < :: real \<Rightarrow> real \<Rightarrow> bool"} $ @{term "0::real"} $ term_of_num vs t
  | term_of_fm vs (@{code Ge} t) =
      @{term "op \<le> :: real \<Rightarrow> real \<Rightarrow> bool"} $ @{term "0::real"} $ term_of_num vs t
  | term_of_fm vs (@{code Eq} t) =
      @{term "op = :: real \<Rightarrow> real \<Rightarrow> bool"} $ term_of_num vs t $ @{term "0::real"}
  | term_of_fm vs (@{code NEq} t) =
      term_of_fm vs (@{code NOT} (@{code Eq} t))
  | term_of_fm vs (@{code Dvd} (i, t)) =
      @{term "op rdvd"} $ term_of_num vs (@{code C} i) $ term_of_num vs t
  | term_of_fm vs (@{code NDvd} (i, t)) =
      term_of_fm vs (@{code NOT} (@{code Dvd} (i, t)))
  | term_of_fm vs (@{code NOT} t') =
      HOLogic.Not $ term_of_fm vs t'
  | term_of_fm vs (@{code And} (t1, t2)) =
      HOLogic.conj $ term_of_fm vs t1 $ term_of_fm vs t2
  | term_of_fm vs (@{code Or} (t1, t2)) =
      HOLogic.disj $ term_of_fm vs t1 $ term_of_fm vs t2
  | term_of_fm vs (@{code Imp}  (t1, t2)) =
      HOLogic.imp $ term_of_fm vs t1 $ term_of_fm vs t2
  | term_of_fm vs (@{code Iff} (t1, t2)) =
      @{term "op = :: bool \<Rightarrow> bool \<Rightarrow> bool"} $ term_of_fm vs t1 $ term_of_fm vs t2;

in
  let 
    val thy = Thm.theory_of_cterm ct;
    val t = Thm.term_of ct;
    val fs = Misc_Legacy.term_frees t;
    val vs = map_index swap fs;
    val qe = if proofs then @{code mirlfrqe} else @{code mircfrqe};
    val t' = (term_of_fm vs o qe o fm_of_term vs) t;
  in (cterm_of thy o HOLogic.mk_Trueprop o HOLogic.mk_eq) (t, t') end
end;
*}

ML_file "mir_tac.ML"

method_setup mir = {*
  Args.mode "no_quantify" >>
    (fn q => fn ctxt => SIMPLE_METHOD' (Mir_Tac.mir_tac ctxt (not q)))
*} "decision procedure for MIR arithmetic"


lemma "ALL (x::real). (\<lfloor>x\<rfloor> = \<lceil>x\<rceil> = (x = real \<lfloor>x\<rfloor>))"
  by mir

lemma "ALL (x::real). real (2::int)*x - (real (1::int)) < real \<lfloor>x\<rfloor> + real \<lceil>x\<rceil> \<and> real \<lfloor>x\<rfloor> + real \<lceil>x\<rceil>  \<le> real (2::int)*x + (real (1::int))"
  by mir

lemma "ALL (x::real). 2*\<lfloor>x\<rfloor> \<le> \<lfloor>2*x\<rfloor> \<and> \<lfloor>2*x\<rfloor> \<le> 2*\<lfloor>x+1\<rfloor>"
  by mir 

lemma "ALL (x::real). \<exists>y \<le> x. (\<lfloor>x\<rfloor> = \<lceil>y\<rceil>)"
  by mir

lemma "ALL (x::real) (y::real). \<lfloor>x\<rfloor> = \<lfloor>y\<rfloor> \<longrightarrow> 0 \<le> abs (y - x) \<and> abs (y - x) \<le> 1"
  by mir

end
