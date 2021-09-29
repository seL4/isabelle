(*  Title:      HOL/Decision_Procs/MIR.thy
    Author:     Amine Chaieb
*)

theory MIR
imports Complex_Main Dense_Linear_Order DP_Library
  "HOL-Library.Code_Target_Numeral" "HOL-Library.Old_Recdef"
begin

section \<open>Prelude\<close>

abbreviation (input) UNION :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set"
  where "UNION A f \<equiv> \<Union> (f ` A)" \<comment> \<open>legacy\<close>


section \<open>Quantifier elimination for \<open>\<real> (0, 1, +, floor, <)\<close>\<close>

declare of_int_floor_cancel [simp del]

lemma myle:
  fixes a b :: "'a::{ordered_ab_group_add}"
  shows "(a \<le> b) = (0 \<le> b - a)"
  by (metis add_0_left add_le_cancel_right diff_add_cancel)

lemma myless:
  fixes a b :: "'a::{ordered_ab_group_add}"
  shows "(a < b) = (0 < b - a)"
  by (metis le_iff_diff_le_0 less_le_not_le myle)

(* Periodicity of dvd *)
lemmas dvd_period = zdvd_period

(* The Divisibility relation between reals *)
definition rdvd:: "real \<Rightarrow> real \<Rightarrow> bool" (infixl "rdvd" 50)
  where "x rdvd y \<longleftrightarrow> (\<exists>k::int. y = x * real_of_int k)"

lemma int_rdvd_real:
  "real_of_int (i::int) rdvd x = (i dvd \<lfloor>x\<rfloor> \<and> real_of_int \<lfloor>x\<rfloor> = x)" (is "?l = ?r")
proof
  assume "?l"
  hence th: "\<exists> k. x=real_of_int (i*k)" by (simp add: rdvd_def)
  hence th': "real_of_int \<lfloor>x\<rfloor> = x" by (auto simp del: of_int_mult)
  with th have "\<exists> k. real_of_int \<lfloor>x\<rfloor> = real_of_int (i*k)" by simp
  hence "\<exists>k. \<lfloor>x\<rfloor> = i*k" by presburger
  thus ?r using th' by (simp add: dvd_def)
next
  assume "?r" hence "(i::int) dvd \<lfloor>x::real\<rfloor>" ..
  hence "\<exists>k. real_of_int \<lfloor>x\<rfloor> = real_of_int (i*k)"
    by (metis (no_types) dvd_def)
  thus ?l using \<open>?r\<close> by (simp add: rdvd_def)
qed

lemma int_rdvd_iff: "(real_of_int (i::int) rdvd real_of_int t) = (i dvd t)"
  by (auto simp add: rdvd_def dvd_def) (rule_tac x="k" in exI, simp only: of_int_mult[symmetric])


lemma rdvd_abs1: "(\<bar>real_of_int d\<bar> rdvd t) = (real_of_int (d ::int) rdvd t)"
proof
  assume d: "real_of_int d rdvd t"
  from d int_rdvd_real have d2: "d dvd \<lfloor>t\<rfloor>" and ti: "real_of_int \<lfloor>t\<rfloor> = t"
    by auto

  from iffD2[OF abs_dvd_iff] d2 have "\<bar>d\<bar> dvd \<lfloor>t\<rfloor>" by blast
  with ti int_rdvd_real[symmetric] have "real_of_int \<bar>d\<bar> rdvd t" by blast
  thus "\<bar>real_of_int d\<bar> rdvd t" by simp
next
  assume "\<bar>real_of_int d\<bar> rdvd t" hence "real_of_int \<bar>d\<bar> rdvd t" by simp
  with int_rdvd_real[where i="\<bar>d\<bar>" and x="t"]
  have d2: "\<bar>d\<bar> dvd \<lfloor>t\<rfloor>" and ti: "real_of_int \<lfloor>t\<rfloor> = t"
    by auto
  from iffD1[OF abs_dvd_iff] d2 have "d dvd \<lfloor>t\<rfloor>" by blast
  with ti int_rdvd_real[symmetric] show "real_of_int d rdvd t" by blast
qed

lemma rdvd_minus: "(real_of_int (d::int) rdvd t) = (real_of_int d rdvd -t)"
  apply (auto simp add: rdvd_def)
  apply (rule_tac x="-k" in exI, simp)
  apply (rule_tac x="-k" in exI, simp)
  done

lemma rdvd_left_0_eq: "(0 rdvd t) = (t=0)"
  by (auto simp add: rdvd_def)

lemma rdvd_mult:
  assumes knz: "k\<noteq>0"
  shows "(real_of_int (n::int) * real_of_int (k::int) rdvd x * real_of_int k) = (real_of_int n rdvd x)"
  using knz by (simp add: rdvd_def)

  (*********************************************************************************)
  (****                            SHADOW SYNTAX AND SEMANTICS                  ****)
  (*********************************************************************************)

datatype (plugins del: size) num = C int | Bound nat | CN nat int num
  | Neg num | Add num num | Sub num num
  | Mul int num | Floor num | CF int num num

instantiation num :: size
begin

primrec size_num :: "num \<Rightarrow> nat"
where
  "size_num (C c) = 1"
| "size_num (Bound n) = 1"
| "size_num (Neg a) = 1 + size_num a"
| "size_num (Add a b) = 1 + size_num a + size_num b"
| "size_num (Sub a b) = 3 + size_num a + size_num b"
| "size_num (CN n c a) = 4 + size_num a "
| "size_num (CF c a b) = 4 + size_num a + size_num b"
| "size_num (Mul c a) = 1 + size_num a"
| "size_num (Floor a) = 1 + size_num a"

instance ..

end

  (* Semantics of numeral terms (num) *)
primrec Inum :: "real list \<Rightarrow> num \<Rightarrow> real"
where
  "Inum bs (C c) = (real_of_int c)"
| "Inum bs (Bound n) = bs!n"
| "Inum bs (CN n c a) = (real_of_int c) * (bs!n) + (Inum bs a)"
| "Inum bs (Neg a) = -(Inum bs a)"
| "Inum bs (Add a b) = Inum bs a + Inum bs b"
| "Inum bs (Sub a b) = Inum bs a - Inum bs b"
| "Inum bs (Mul c a) = (real_of_int c) * Inum bs a"
| "Inum bs (Floor a) = real_of_int \<lfloor>Inum bs a\<rfloor>"
| "Inum bs (CF c a b) = real_of_int c * real_of_int \<lfloor>Inum bs a\<rfloor> + Inum bs b"
definition "isint t bs \<equiv> real_of_int \<lfloor>Inum bs t\<rfloor> = Inum bs t"

lemma isint_iff: "isint n bs = (real_of_int \<lfloor>Inum bs n\<rfloor> = Inum bs n)"
  by (simp add: isint_def)

lemma isint_Floor: "isint (Floor n) bs"
  by (simp add: isint_iff)

lemma isint_Mul: "isint e bs \<Longrightarrow> isint (Mul c e) bs"
proof-
  let ?e = "Inum bs e"
  assume be: "isint e bs" hence efe:"real_of_int \<lfloor>?e\<rfloor> = ?e" by (simp add: isint_iff)
  have "real_of_int \<lfloor>Inum bs (Mul c e)\<rfloor> = real_of_int \<lfloor>real_of_int (c * \<lfloor>?e\<rfloor>)\<rfloor>"
    using efe by simp
  also have "\<dots> = real_of_int (c* \<lfloor>?e\<rfloor>)" by (metis floor_of_int)
  also have "\<dots> = real_of_int c * ?e" using efe by simp
  finally show ?thesis using isint_iff by simp
qed

lemma isint_neg: "isint e bs \<Longrightarrow> isint (Neg e) bs"
proof-
  let ?I = "\<lambda> t. Inum bs t"
  assume ie: "isint e bs"
  hence th: "real_of_int \<lfloor>?I e\<rfloor> = ?I e" by (simp add: isint_def)
  have "real_of_int \<lfloor>?I (Neg e)\<rfloor> = real_of_int \<lfloor>- (real_of_int \<lfloor>?I e\<rfloor>)\<rfloor>"
    by (simp add: th)
  also have "\<dots> = - real_of_int \<lfloor>?I e\<rfloor>" by simp
  finally show "isint (Neg e) bs" by (simp add: isint_def th)
qed

lemma isint_sub:
  assumes ie: "isint e bs" shows "isint (Sub (C c) e) bs"
proof-
  let ?I = "\<lambda> t. Inum bs t"
  from ie have th: "real_of_int \<lfloor>?I e\<rfloor> = ?I e" by (simp add: isint_def)
  have "real_of_int \<lfloor>?I (Sub (C c) e)\<rfloor> = real_of_int \<lfloor>real_of_int (c - \<lfloor>?I e\<rfloor>)\<rfloor>"
    by (simp add: th)
  also have "\<dots> = real_of_int (c - \<lfloor>?I e\<rfloor>)" by simp
  finally show "isint (Sub (C c) e) bs" by (simp add: isint_def th)
qed

lemma isint_add:
  assumes ai: "isint a bs" and bi: "isint b bs"
  shows "isint (Add a b) bs"
proof-
  let ?a = "Inum bs a"
  let ?b = "Inum bs b"
  from ai bi isint_iff have "real_of_int \<lfloor>?a + ?b\<rfloor> = real_of_int \<lfloor>real_of_int \<lfloor>?a\<rfloor> + real_of_int \<lfloor>?b\<rfloor>\<rfloor>"
    by simp
  also have "\<dots> = real_of_int \<lfloor>?a\<rfloor> + real_of_int \<lfloor>?b\<rfloor>" by simp
  also have "\<dots> = ?a + ?b" using ai bi isint_iff by simp
  finally show "isint (Add a b) bs" by (simp add: isint_iff)
qed

lemma isint_c: "isint (C j) bs"
  by (simp add: isint_iff)


    (* FORMULAE *)
datatype (plugins del: size) fm =
  T | F | Lt num | Le num | Gt num | Ge num | Eq num | NEq num |
  Dvd int num | NDvd int num |
  Not fm | And fm fm |  Or fm fm | Imp fm fm | Iff fm fm | E fm | A fm

instantiation fm :: size
begin

primrec size_fm :: "fm \<Rightarrow> nat"
where
  "size_fm (Not p) = 1 + size_fm p"
| "size_fm (And p q) = 1 + size_fm p + size_fm q"
| "size_fm (Or p q) = 1 + size_fm p + size_fm q"
| "size_fm (Imp p q) = 3 + size_fm p + size_fm q"
| "size_fm (Iff p q) = 3 + 2 * (size_fm p + size_fm q)"
| "size_fm (E p) = 1 + size_fm p"
| "size_fm (A p) = 4 + size_fm p"
| "size_fm (Dvd i t) = 2"
| "size_fm (NDvd i t) = 2"
| "size_fm T = 1"
| "size_fm F = 1"
| "size_fm (Lt _) = 1"
| "size_fm (Le _) = 1"
| "size_fm (Gt _) = 1"
| "size_fm (Ge _) = 1"
| "size_fm (Eq _) = 1"
| "size_fm (NEq _) = 1"

instance ..

end

lemma size_fm_pos [simp]: "size p > 0" for p :: fm
  by (induct p) simp_all

  (* Semantics of formulae (fm) *)
primrec Ifm ::"real list \<Rightarrow> fm \<Rightarrow> bool"
where
  "Ifm bs T \<longleftrightarrow> True"
| "Ifm bs F \<longleftrightarrow> False"
| "Ifm bs (Lt a) \<longleftrightarrow> Inum bs a < 0"
| "Ifm bs (Gt a) \<longleftrightarrow> Inum bs a > 0"
| "Ifm bs (Le a) \<longleftrightarrow> Inum bs a \<le> 0"
| "Ifm bs (Ge a) \<longleftrightarrow> Inum bs a \<ge> 0"
| "Ifm bs (Eq a) \<longleftrightarrow> Inum bs a = 0"
| "Ifm bs (NEq a) \<longleftrightarrow> Inum bs a \<noteq> 0"
| "Ifm bs (Dvd i b) \<longleftrightarrow> real_of_int i rdvd Inum bs b"
| "Ifm bs (NDvd i b) \<longleftrightarrow> \<not> (real_of_int i rdvd Inum bs b)"
| "Ifm bs (Not p) \<longleftrightarrow> \<not> (Ifm bs p)"
| "Ifm bs (And p q) \<longleftrightarrow> Ifm bs p \<and> Ifm bs q"
| "Ifm bs (Or p q) \<longleftrightarrow> Ifm bs p \<or> Ifm bs q"
| "Ifm bs (Imp p q) \<longleftrightarrow> (Ifm bs p \<longrightarrow> Ifm bs q)"
| "Ifm bs (Iff p q) \<longleftrightarrow> (Ifm bs p \<longleftrightarrow> Ifm bs q)"
| "Ifm bs (E p) \<longleftrightarrow> (\<exists>x. Ifm (x # bs) p)"
| "Ifm bs (A p) \<longleftrightarrow> (\<forall>x. Ifm (x # bs) p)"

fun prep :: "fm \<Rightarrow> fm"
where
  "prep (E T) = T"
| "prep (E F) = F"
| "prep (E (Or p q)) = Or (prep (E p)) (prep (E q))"
| "prep (E (Imp p q)) = Or (prep (E (Not p))) (prep (E q))"
| "prep (E (Iff p q)) = Or (prep (E (And p q))) (prep (E (And (Not p) (Not q))))"
| "prep (E (Not (And p q))) = Or (prep (E (Not p))) (prep (E(Not q)))"
| "prep (E (Not (Imp p q))) = prep (E (And p (Not q)))"
| "prep (E (Not (Iff p q))) = Or (prep (E (And p (Not q)))) (prep (E(And (Not p) q)))"
| "prep (E p) = E (prep p)"
| "prep (A (And p q)) = And (prep (A p)) (prep (A q))"
| "prep (A p) = prep (Not (E (Not p)))"
| "prep (Not (Not p)) = prep p"
| "prep (Not (And p q)) = Or (prep (Not p)) (prep (Not q))"
| "prep (Not (A p)) = prep (E (Not p))"
| "prep (Not (Or p q)) = And (prep (Not p)) (prep (Not q))"
| "prep (Not (Imp p q)) = And (prep p) (prep (Not q))"
| "prep (Not (Iff p q)) = Or (prep (And p (Not q))) (prep (And (Not p) q))"
| "prep (Not p) = Not (prep p)"
| "prep (Or p q) = Or (prep p) (prep q)"
| "prep (And p q) = And (prep p) (prep q)"
| "prep (Imp p q) = prep (Or (Not p) q)"
| "prep (Iff p q) = Or (prep (And p q)) (prep (And (Not p) (Not q)))"
| "prep p = p"

lemma prep: "\<And> bs. Ifm bs (prep p) = Ifm bs p"
  by (induct p rule: prep.induct) auto


  (* Quantifier freeness *)
fun qfree:: "fm \<Rightarrow> bool"
where
  "qfree (E p) = False"
| "qfree (A p) = False"
| "qfree (Not p) = qfree p"
| "qfree (And p q) = (qfree p \<and> qfree q)"
| "qfree (Or  p q) = (qfree p \<and> qfree q)"
| "qfree (Imp p q) = (qfree p \<and> qfree q)"
| "qfree (Iff p q) = (qfree p \<and> qfree q)"
| "qfree p = True"

  (* Boundedness and substitution *)
primrec numbound0 :: "num \<Rightarrow> bool" (* a num is INDEPENDENT of Bound 0 *)
where
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

primrec bound0:: "fm \<Rightarrow> bool" (* A Formula is independent of Bound 0 *)
where
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
| "bound0 (Not p) = bound0 p"
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

primrec numsubst0:: "num \<Rightarrow> num \<Rightarrow> num" (* substitute a num into a num for Bound 0 *)
where
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

primrec subst0:: "num \<Rightarrow> fm \<Rightarrow> fm" (* substitue a num into a formula for Bound 0 *)
where
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
| "subst0 t (Not p) = Not (subst0 t p)"
| "subst0 t (And p q) = And (subst0 t p) (subst0 t q)"
| "subst0 t (Or p q) = Or (subst0 t p) (subst0 t q)"
| "subst0 t (Imp p q) = Imp (subst0 t p) (subst0 t q)"
| "subst0 t (Iff p q) = Iff (subst0 t p) (subst0 t q)"

lemma subst0_I: assumes qfp: "qfree p"
  shows "Ifm (b#bs) (subst0 a p) = Ifm ((Inum (b#bs) a)#bs) p"
  using qfp numsubst0_I[where b="b" and bs="bs" and a="a"]
  by (induct p) simp_all

fun decrnum:: "num \<Rightarrow> num"
where
  "decrnum (Bound n) = Bound (n - 1)"
| "decrnum (Neg a) = Neg (decrnum a)"
| "decrnum (Add a b) = Add (decrnum a) (decrnum b)"
| "decrnum (Sub a b) = Sub (decrnum a) (decrnum b)"
| "decrnum (Mul c a) = Mul c (decrnum a)"
| "decrnum (Floor a) = Floor (decrnum a)"
| "decrnum (CN n c a) = CN (n - 1) c (decrnum a)"
| "decrnum (CF c a b) = CF c (decrnum a) (decrnum b)"
| "decrnum a = a"

fun decr :: "fm \<Rightarrow> fm"
where
  "decr (Lt a) = Lt (decrnum a)"
| "decr (Le a) = Le (decrnum a)"
| "decr (Gt a) = Gt (decrnum a)"
| "decr (Ge a) = Ge (decrnum a)"
| "decr (Eq a) = Eq (decrnum a)"
| "decr (NEq a) = NEq (decrnum a)"
| "decr (Dvd i a) = Dvd i (decrnum a)"
| "decr (NDvd i a) = NDvd i (decrnum a)"
| "decr (Not p) = Not (decr p)"
| "decr (And p q) = And (decr p) (decr q)"
| "decr (Or p q) = Or (decr p) (decr q)"
| "decr (Imp p q) = Imp (decr p) (decr q)"
| "decr (Iff p q) = Iff (decr p) (decr q)"
| "decr p = p"

lemma decrnum: assumes nb: "numbound0 t"
  shows "Inum (x#bs) t = Inum bs (decrnum t)"
  using nb by (induct t rule: decrnum.induct) simp_all

lemma decr: assumes nb: "bound0 p"
  shows "Ifm (x#bs) p = Ifm bs (decr p)"
  using nb by (induct p rule: decr.induct) (simp_all add: decrnum)

lemma decr_qf: "bound0 p \<Longrightarrow> qfree (decr p)"
  by (induct p) simp_all

fun isatom :: "fm \<Rightarrow> bool" (* test for atomicity *)
where
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

lemma numsubst0_numbound0:
  assumes nb: "numbound0 t"
  shows "numbound0 (numsubst0 t a)"
  using nb by (induct a) auto

lemma subst0_bound0:
  assumes qf: "qfree p" and nb: "numbound0 t"
  shows "bound0 (subst0 t p)"
  using qf numsubst0_numbound0[OF nb] by (induct p) auto

lemma bound0_qf: "bound0 p \<Longrightarrow> qfree p"
  by (induct p) simp_all


definition djf:: "('a \<Rightarrow> fm) \<Rightarrow> 'a \<Rightarrow> fm \<Rightarrow> fm" where
  "djf f p q = (if q=T then T else if q=F then f p else
  (let fp = f p in case fp of T \<Rightarrow> T | F \<Rightarrow> q | _ \<Rightarrow> Or fp q))"

definition evaldjf:: "('a \<Rightarrow> fm) \<Rightarrow> 'a list \<Rightarrow> fm" where
  "evaldjf f ps = foldr (djf f) ps F"

lemma djf_Or: "Ifm bs (djf f p q) = Ifm bs (Or (f p) q)"
  by (cases "q=T", simp add: djf_def,cases "q=F",simp add: djf_def)
  (cases "f p", simp_all add: Let_def djf_def)

lemma evaldjf_ex: "Ifm bs (evaldjf f ps) = (\<exists> p \<in> set ps. Ifm bs (f p))"
  by (induct ps) (simp_all add: evaldjf_def djf_Or)

lemma evaldjf_bound0:
  assumes nb: "\<forall> x\<in> set xs. bound0 (f x)"
  shows "bound0 (evaldjf f xs)"
  using nb
  apply (induct xs)
  apply (auto simp add: evaldjf_def djf_def Let_def)
  apply (case_tac "f a")
  apply auto
  done

lemma evaldjf_qf:
  assumes nb: "\<forall> x\<in> set xs. qfree (f x)"
  shows "qfree (evaldjf f xs)"
  using nb
  apply (induct xs)
  apply (auto simp add: evaldjf_def djf_def Let_def)
  apply (case_tac "f a")
  apply auto
  done

fun disjuncts :: "fm \<Rightarrow> fm list"
where
  "disjuncts (Or p q) = (disjuncts p) @ (disjuncts q)"
| "disjuncts F = []"
| "disjuncts p = [p]"

fun conjuncts :: "fm \<Rightarrow> fm list"
where
  "conjuncts (And p q) = (conjuncts p) @ (conjuncts q)"
| "conjuncts T = []"
| "conjuncts p = [p]"

lemma conjuncts: "(\<forall> q\<in> set (conjuncts p). Ifm bs q) = Ifm bs p"
  by (induct p rule: conjuncts.induct) auto

lemma disjuncts_qf: "qfree p \<Longrightarrow> \<forall> q\<in> set (disjuncts p). qfree q"
proof -
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
proof -
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
fun bnds:: "num \<Rightarrow> nat list"
where
  "bnds (Bound n) = [n]"
| "bnds (CN n c a) = n#(bnds a)"
| "bnds (Neg a) = bnds a"
| "bnds (Add a b) = (bnds a)@(bnds b)"
| "bnds (Sub a b) = (bnds a)@(bnds b)"
| "bnds (Mul i a) = bnds a"
| "bnds (Floor a) = bnds a"
| "bnds (CF c a b) = (bnds a)@(bnds b)"
| "bnds a = []"

fun lex_ns:: "nat list \<Rightarrow> nat list \<Rightarrow> bool"
where
  "lex_ns [] ms = True"
| "lex_ns ns [] = False"
| "lex_ns (n#ns) (m#ms) = (n<m \<or> ((n = m) \<and> lex_ns ns ms)) "
definition lex_bnd :: "num \<Rightarrow> num \<Rightarrow> bool" where
  "lex_bnd t s \<equiv> lex_ns (bnds t) (bnds s)"

fun maxcoeff:: "num \<Rightarrow> int"
where
  "maxcoeff (C i) = \<bar>i\<bar>"
| "maxcoeff (CN n c t) = max \<bar>c\<bar> (maxcoeff t)"
| "maxcoeff (CF c t s) = max \<bar>c\<bar> (maxcoeff s)"
| "maxcoeff t = 1"

lemma maxcoeff_pos: "maxcoeff t \<ge> 0"
  by (induct t rule: maxcoeff.induct) auto

fun numgcdh:: "num \<Rightarrow> int \<Rightarrow> int"
where
  "numgcdh (C i) = (\<lambda>g. gcd i g)"
| "numgcdh (CN n c t) = (\<lambda>g. gcd c (numgcdh t g))"
| "numgcdh (CF c s t) = (\<lambda>g. gcd c (numgcdh t g))"
| "numgcdh t = (\<lambda>g. 1)"

definition numgcd :: "num \<Rightarrow> int"
  where "numgcd t = numgcdh t (maxcoeff t)"

fun reducecoeffh:: "num \<Rightarrow> int \<Rightarrow> num"
where
  "reducecoeffh (C i) = (\<lambda> g. C (i div g))"
| "reducecoeffh (CN n c t) = (\<lambda> g. CN n (c div g) (reducecoeffh t g))"
| "reducecoeffh (CF c s t) = (\<lambda> g. CF (c div g)  s (reducecoeffh t g))"
| "reducecoeffh t = (\<lambda>g. t)"

definition reducecoeff :: "num \<Rightarrow> num"
where
  "reducecoeff t =
    (let g = numgcd t in
     if g = 0 then C 0 else if g=1 then t else reducecoeffh t g)"

fun dvdnumcoeff:: "num \<Rightarrow> int \<Rightarrow> bool"
where
  "dvdnumcoeff (C i) = (\<lambda> g. g dvd i)"
| "dvdnumcoeff (CN n c t) = (\<lambda> g. g dvd c \<and> (dvdnumcoeff t g))"
| "dvdnumcoeff (CF c s t) = (\<lambda> g. g dvd c \<and> (dvdnumcoeff t g))"
| "dvdnumcoeff t = (\<lambda>g. False)"

lemma dvdnumcoeff_trans:
  assumes gdg: "g dvd g'" and dgt':"dvdnumcoeff t g'"
  shows "dvdnumcoeff t g"
  using dgt' gdg
  by (induct t rule: dvdnumcoeff.induct) (simp_all add: gdg dvd_trans[OF gdg])

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
  using gp by (induct t rule: numgcdh.induct) auto

lemma numgcd_pos: "numgcd t \<ge>0"
  by (simp add: numgcd_def numgcdh_pos maxcoeff_pos)

lemma reducecoeffh:
  assumes gt: "dvdnumcoeff t g" and gp: "g > 0"
  shows "real_of_int g *(Inum bs (reducecoeffh t g)) = Inum bs t"
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

fun ismaxcoeff:: "num \<Rightarrow> int \<Rightarrow> bool"
where
  "ismaxcoeff (C i) = (\<lambda> x. \<bar>i\<bar> \<le> x)"
| "ismaxcoeff (CN n c t) = (\<lambda>x. \<bar>c\<bar> \<le> x \<and> (ismaxcoeff t x))"
| "ismaxcoeff (CF c s t) = (\<lambda>x. \<bar>c\<bar> \<le> x \<and> (ismaxcoeff t x))"
| "ismaxcoeff t = (\<lambda>x. True)"

lemma ismaxcoeff_mono: "ismaxcoeff t c \<Longrightarrow> c \<le> c' \<Longrightarrow> ismaxcoeff t c'"
  by (induct t rule: ismaxcoeff.induct) auto

lemma maxcoeff_ismaxcoeff: "ismaxcoeff t (maxcoeff t)"
proof (induct t rule: maxcoeff.induct)
  case (2 n c t)
  hence H:"ismaxcoeff t (maxcoeff t)" .
  have thh: "maxcoeff t \<le> max \<bar>c\<bar> (maxcoeff t)" by simp
  from ismaxcoeff_mono[OF H thh] show ?case by simp
next
  case (3 c t s)
  hence H1:"ismaxcoeff s (maxcoeff s)" by auto
  have thh1: "maxcoeff s \<le> max \<bar>c\<bar> (maxcoeff s)" by (simp add: max_def)
  from ismaxcoeff_mono[OF H1 thh1] show ?case by simp
qed simp_all

lemma zgcd_gt1:
  "\<bar>i\<bar> > 1 \<and> \<bar>j\<bar> > 1 \<or> \<bar>i\<bar> = 0 \<and> \<bar>j\<bar> > 1 \<or> \<bar>i\<bar> > 1 \<and> \<bar>j\<bar> = 0"
  if "gcd i j > 1" for i j :: int
proof -
  have "\<bar>k\<bar> \<le> 1 \<longleftrightarrow> k = - 1 \<or> k = 0 \<or> k = 1" for k :: int
    by auto
  with that show ?thesis
    by (auto simp add: not_less)
qed

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
  have "(\<bar>c\<bar> > 1 \<and> ?g > 1) \<or> (\<bar>c\<bar> = 0 \<and> ?g > 1) \<or> (\<bar>c\<bar> > 1 \<and> ?g = 0)" by simp
  moreover {assume "\<bar>c\<bar> > 1" and gp: "?g > 1" with 2
    have th: "dvdnumcoeff t ?g" by simp
    have th': "gcd c ?g dvd ?g" by simp
    from dvdnumcoeff_trans[OF th' th] have ?case by simp }
  moreover {assume "\<bar>c\<bar> = 0 \<and> ?g > 1"
    with 2 have th: "dvdnumcoeff t ?g" by simp
    have th': "gcd c ?g dvd ?g" by simp
    from dvdnumcoeff_trans[OF th' th] have ?case by simp
    hence ?case by simp }
  moreover {assume "\<bar>c\<bar> > 1" and g0:"?g = 0"
    from numgcdh0[OF g0] have "m=0". with 2 g0 have ?case by simp }
  ultimately show ?case by blast
next
  case (3 c s t)
  let ?g = "numgcdh t m"
  from 3 have th:"gcd c ?g > 1" by simp
  from zgcd_gt1[OF th] numgcdh_pos[OF mp, where t="t"]
  have "(\<bar>c\<bar> > 1 \<and> ?g > 1) \<or> (\<bar>c\<bar> = 0 \<and> ?g > 1) \<or> (\<bar>c\<bar> > 1 \<and> ?g = 0)" by simp
  moreover {assume "\<bar>c\<bar> > 1" and gp: "?g > 1" with 3
    have th: "dvdnumcoeff t ?g" by simp
    have th': "gcd c ?g dvd ?g" by simp
    from dvdnumcoeff_trans[OF th' th] have ?case by simp }
  moreover {assume "\<bar>c\<bar> = 0 \<and> ?g > 1"
    with 3 have th: "dvdnumcoeff t ?g" by simp
    have th': "gcd c ?g dvd ?g" by simp
    from dvdnumcoeff_trans[OF th' th] have ?case by simp
    hence ?case by simp }
  moreover {assume "\<bar>c\<bar> > 1" and g0:"?g = 0"
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

lemma reducecoeff: "real_of_int (numgcd t) * (Inum bs (reducecoeff t)) = Inum bs t"
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
  by (induct t rule: reducecoeffh.induct) auto

lemma reducecoeff_numbound0: "numbound0 t \<Longrightarrow> numbound0 (reducecoeff t)"
  using reducecoeffh_numbound0 by (simp add: reducecoeff_def Let_def)

consts numadd:: "num \<times> num \<Rightarrow> num"
recdef numadd "measure (\<lambda>(t, s). size t + size s)"
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

lemma numadd [simp]: "Inum bs (numadd (t, s)) = Inum bs (Add t s)"
  by (induct t s rule: numadd.induct) (simp_all add: Let_def algebra_simps add_eq_0_iff)

lemma numadd_nb [simp]: "numbound0 t \<Longrightarrow> numbound0 s \<Longrightarrow> numbound0 (numadd (t, s))"
  by (induct t s rule: numadd.induct) (simp_all add: Let_def)

fun nummul:: "num \<Rightarrow> int \<Rightarrow> num"
where
  "nummul (C j) = (\<lambda> i. C (i*j))"
| "nummul (CN n c t) = (\<lambda> i. CN n (c*i) (nummul t i))"
| "nummul (CF c t s) = (\<lambda> i. CF (c*i) t (nummul s i))"
| "nummul (Mul c t) = (\<lambda> i. nummul t (i*c))"
| "nummul t = (\<lambda> i. Mul i t)"

lemma nummul[simp]: "\<And> i. Inum bs (nummul t i) = Inum bs (Mul i t)"
  by (induct t rule: nummul.induct) (auto simp add: algebra_simps)

lemma nummul_nb[simp]: "\<And> i. numbound0 t \<Longrightarrow> numbound0 (nummul t i)"
  by (induct t rule: nummul.induct) auto

definition numneg :: "num \<Rightarrow> num"
  where "numneg t \<equiv> nummul t (- 1)"

definition numsub :: "num \<Rightarrow> num \<Rightarrow> num"
  where "numsub s t \<equiv> (if s = t then C 0 else numadd (s,numneg t))"

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

fun split_int:: "num \<Rightarrow> num \<times> num"
where
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
      by (cases ?tv) (auto simp add: numfloor_def Let_def split_def)
    from split_int[OF tvti] have "?N (Floor t) = ?N (Floor(Add ?tv ?ti))" and tii:"isint ?ti bs" by simp+
    hence "?N (Floor t) = real_of_int \<lfloor>?N (Add ?tv ?ti)\<rfloor>" by simp
    also have "\<dots> = real_of_int (\<lfloor>?N ?tv\<rfloor> + \<lfloor>?N ?ti\<rfloor>)"
      by (simp,subst tii[simplified isint_iff, symmetric]) simp
    also have "\<dots> = ?N (Add (Floor ?tv) ?ti)" by (simp add: tii[simplified isint_iff])
    finally have ?thesis using th1 by simp}
  moreover {fix v assume H:"?tv = C v"
    from split_int[OF tvti] have "?N (Floor t) = ?N (Floor(Add ?tv ?ti))" and tii:"isint ?ti bs" by simp+
    hence "?N (Floor t) = real_of_int \<lfloor>?N (Add ?tv ?ti)\<rfloor>" by simp
    also have "\<dots> = real_of_int (\<lfloor>?N ?tv\<rfloor> + \<lfloor>?N ?ti\<rfloor>)"
      by (simp,subst tii[simplified isint_iff, symmetric]) simp
    also have "\<dots> = ?N (Add (Floor ?tv) ?ti)" by (simp add: tii[simplified isint_iff])
    finally have ?thesis by (simp add: H numfloor_def Let_def split_def) }
  ultimately show ?thesis by auto
qed

lemma numfloor_nb[simp]: "numbound0 t \<Longrightarrow> numbound0 (numfloor t)"
  using split_int_nb[where t="t"]
  by (cases "fst (split_int t)") (auto simp add: numfloor_def Let_def split_def)

fun simpnum:: "num \<Rightarrow> num"
where
  "simpnum (C j) = C j"
| "simpnum (Bound n) = CN n 1 (C 0)"
| "simpnum (Neg t) = numneg (simpnum t)"
| "simpnum (Add t s) = numadd (simpnum t,simpnum s)"
| "simpnum (Sub t s) = numsub (simpnum t) (simpnum s)"
| "simpnum (Mul i t) = (if i = 0 then (C 0) else nummul (simpnum t) i)"
| "simpnum (Floor t) = numfloor (simpnum t)"
| "simpnum (CN n c t) = (if c=0 then simpnum t else CN n c (simpnum t))"
| "simpnum (CF c t s) = simpnum(Add (Mul c (Floor t)) s)"

lemma simpnum_ci[simp]: "Inum bs (simpnum t) = Inum bs t"
  by (induct t rule: simpnum.induct) auto

lemma simpnum_numbound0[simp]: "numbound0 t \<Longrightarrow> numbound0 (simpnum t)"
  by (induct t rule: simpnum.induct) auto

fun nozerocoeff:: "num \<Rightarrow> bool"
where
  "nozerocoeff (C c) = True"
| "nozerocoeff (CN n c t) = (c\<noteq>0 \<and> nozerocoeff t)"
| "nozerocoeff (CF c s t) = (c \<noteq> 0 \<and> nozerocoeff t)"
| "nozerocoeff (Mul c t) = (c\<noteq>0 \<and> nozerocoeff t)"
| "nozerocoeff t = True"

lemma numadd_nz : "nozerocoeff a \<Longrightarrow> nozerocoeff b \<Longrightarrow> nozerocoeff (numadd (a,b))"
  by (induct a b rule: numadd.induct) (auto simp add: Let_def)

lemma nummul_nz : "\<And> i. i\<noteq>0 \<Longrightarrow> nozerocoeff a \<Longrightarrow> nozerocoeff (nummul a i)"
  by (induct a rule: nummul.induct) (auto simp add: Let_def numadd_nz)

lemma numneg_nz : "nozerocoeff a \<Longrightarrow> nozerocoeff (numneg a)"
  by (simp add: numneg_def nummul_nz)

lemma numsub_nz: "nozerocoeff a \<Longrightarrow> nozerocoeff b \<Longrightarrow> nozerocoeff (numsub a b)"
  by (simp add: numsub_def numneg_nz numadd_nz)

lemma split_int_nz: "nozerocoeff t \<Longrightarrow> nozerocoeff (fst (split_int t)) \<and> nozerocoeff (snd (split_int t))"
  by (induct t rule: split_int.induct) (auto simp add: Let_def split_def)

lemma numfloor_nz: "nozerocoeff t \<Longrightarrow> nozerocoeff (numfloor t)"
  by (simp add: numfloor_def Let_def split_def)
    (cases "fst (split_int t)", simp_all add: split_int_nz numadd_nz)

lemma simpnum_nz: "nozerocoeff (simpnum t)"
  by (induct t rule: simpnum.induct)
    (auto simp add: numadd_nz numneg_nz numsub_nz nummul_nz numfloor_nz)

lemma maxcoeff_nz: "nozerocoeff t \<Longrightarrow> maxcoeff t = 0 \<Longrightarrow> t = C 0"
proof (induct t rule: maxcoeff.induct)
  case (2 n c t)
  hence cnz: "c \<noteq>0" and mx: "max \<bar>c\<bar> (maxcoeff t) = 0" by simp+
  have "max \<bar>c\<bar> (maxcoeff t) \<ge> \<bar>c\<bar>" by simp
  with cnz have "max \<bar>c\<bar> (maxcoeff t) > 0" by arith
  with 2 show ?case by simp
next
  case (3 c s t)
  hence cnz: "c \<noteq>0" and mx: "max \<bar>c\<bar> (maxcoeff t) = 0" by simp+
  have "max \<bar>c\<bar> (maxcoeff t) \<ge> \<bar>c\<bar>" by simp
  with cnz have "max \<bar>c\<bar> (maxcoeff t) > 0" by arith
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
  shows "((\<lambda> (t,n). Inum bs t / real_of_int n) (simp_num_pair (t,n))) = ((\<lambda> (t,n). Inum bs t / real_of_int n) (t,n))"
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
        have th2:"real_of_int ?g' * ?t = Inum bs ?t'" by simp
        from nnz g1 g'1 have "?lhs = ?t / real_of_int (n div ?g')" by (simp add: simp_num_pair_def Let_def)
        also have "\<dots> = (real_of_int ?g' * ?t) / (real_of_int ?g' * (real_of_int (n div ?g')))" by simp
        also have "\<dots> = (Inum bs ?t' / real_of_int n)"
          using real_of_int_div[OF gpdd] th2 gp0 by simp
        finally have "?lhs = Inum bs t / real_of_int n" by simp
        then have ?thesis using nnz g1 g'1 by (simp add: simp_num_pair_def) }
      ultimately have ?thesis by auto }
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
      ultimately have ?thesis by auto }
    ultimately have ?thesis by blast }
  ultimately show ?thesis by blast
qed

fun not:: "fm \<Rightarrow> fm"
where
  "not (Not p) = p"
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
| "not p = Not p"
lemma not[simp]: "Ifm bs (not p) = Ifm bs (Not p)"
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
  by (unfold iff_def,cases "p=q", simp,cases "p=not q", simp)  (cases "not p= q", auto)

lemma iff_qf[simp]: "\<lbrakk>qfree p ; qfree q\<rbrakk> \<Longrightarrow> qfree (iff p q)"
  by (unfold iff_def,cases "p=q", auto)

fun check_int:: "num \<Rightarrow> bool"
where
  "check_int (C i) = True"
| "check_int (Floor t) = True"
| "check_int (Mul i t) = check_int t"
| "check_int (Add t s) = (check_int t \<and> check_int s)"
| "check_int (Neg t) = check_int t"
| "check_int (CF c t s) = check_int s"
| "check_int t = False"
lemma check_int: "check_int t \<Longrightarrow> isint t bs"
  by (induct t) (auto simp add: isint_add isint_Floor isint_Mul isint_neg isint_c isint_CF)

lemma rdvd_left1_int: "real_of_int \<lfloor>t\<rfloor> = t \<Longrightarrow> 1 rdvd t"
  by (simp add: rdvd_def,rule_tac x="\<lfloor>t\<rfloor>" in exI) simp

lemma rdvd_reduce:
  assumes gd:"g dvd d" and gc:"g dvd c" and gp: "g > 0"
  shows "real_of_int (d::int) rdvd real_of_int (c::int)*t = (real_of_int (d div g) rdvd real_of_int (c div g)*t)"
proof
  assume d: "real_of_int d rdvd real_of_int c * t"
  from d rdvd_def obtain k where k_def: "real_of_int c * t = real_of_int d* real_of_int (k::int)" by auto
  from gd dvd_def obtain kd where kd_def: "d = g * kd" by auto
  from gc dvd_def obtain kc where kc_def: "c = g * kc" by auto
  from k_def kd_def kc_def have "real_of_int g * real_of_int kc * t = real_of_int g * real_of_int kd * real_of_int k" by simp
  hence "real_of_int kc * t = real_of_int kd * real_of_int k" using gp by simp
  hence th:"real_of_int kd rdvd real_of_int kc * t" using rdvd_def by blast
  from kd_def gp have th':"kd = d div g" by simp
  from kc_def gp have "kc = c div g" by simp
  with th th' show "real_of_int (d div g) rdvd real_of_int (c div g) * t" by simp
next
  assume d: "real_of_int (d div g) rdvd real_of_int (c div g) * t"
  from gp have gnz: "g \<noteq> 0" by simp
  thus "real_of_int d rdvd real_of_int c * t" using d rdvd_mult[OF gnz, where n="d div g" and x="real_of_int (c div g) * t"] real_of_int_div[OF gd] real_of_int_div[OF gc] by simp
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
      have th2:"real_of_int ?g' * ?t = Inum bs t" by simp
      from assms g1 g0 g'1
      have "Ifm bs (Dvd (fst (simpdvd d t)) (snd(simpdvd d t))) = Ifm bs (Dvd (d div ?g') ?tt)"
        by (simp add: simpdvd_def Let_def)
      also have "\<dots> = (real_of_int d rdvd (Inum bs t))"
        using rdvd_reduce[OF gpdd gpdgp g'p, where t="?t", simplified div_self[OF gp0]]
          th2[symmetric] by simp
      finally have ?thesis by simp  }
    ultimately have ?thesis by auto
  }
  ultimately show ?thesis by blast
qed

fun simpfm :: "fm \<Rightarrow> fm"
where
  "simpfm (And p q) = conj (simpfm p) (simpfm q)"
| "simpfm (Or p q) = disj (simpfm p) (simpfm q)"
| "simpfm (Imp p q) = imp (simpfm p) (simpfm q)"
| "simpfm (Iff p q) = iff (simpfm p) (simpfm q)"
| "simpfm (Not p) = not (simpfm p)"
| "simpfm (Lt a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v < 0) then T else F
    | _ \<Rightarrow> Lt (reducecoeff a'))"
| "simpfm (Le a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v \<le> 0)  then T else F | _ \<Rightarrow> Le (reducecoeff a'))"
| "simpfm (Gt a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v > 0)  then T else F | _ \<Rightarrow> Gt (reducecoeff a'))"
| "simpfm (Ge a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v \<ge> 0)  then T else F | _ \<Rightarrow> Ge (reducecoeff a'))"
| "simpfm (Eq a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v = 0)  then T else F | _ \<Rightarrow> Eq (reducecoeff a'))"
| "simpfm (NEq a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v \<noteq> 0)  then T else F | _ \<Rightarrow> NEq (reducecoeff a'))"
| "simpfm (Dvd i a) = (if i=0 then simpfm (Eq a)
             else if (\<bar>i\<bar> = 1) \<and> check_int a then T
             else let a' = simpnum a in case a' of C v \<Rightarrow> if (i dvd v)  then T else F | _ \<Rightarrow> (let (d,t) = simpdvd i a' in Dvd d t))"
| "simpfm (NDvd i a) = (if i=0 then simpfm (NEq a)
             else if (\<bar>i\<bar> = 1) \<and> check_int a then F
             else let a' = simpnum a in case a' of C v \<Rightarrow> if (\<not>(i dvd v)) then T else F | _ \<Rightarrow> (let (d,t) = simpdvd i a' in NDvd d t))"
| "simpfm p = p"

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
    hence gp: "real_of_int ?g > 0" by simp
    have "Inum bs ?sa = real_of_int ?g* ?r" by (simp add: reducecoeff)
    with sa have "Inum bs a < 0 = (real_of_int ?g * ?r < real_of_int ?g * 0)" by simp
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
    hence gp: "real_of_int ?g > 0" by simp
    have "Inum bs ?sa = real_of_int ?g* ?r" by (simp add: reducecoeff)
    with sa have "Inum bs a \<le> 0 = (real_of_int ?g * ?r \<le> real_of_int ?g * 0)" by simp
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
    hence gp: "real_of_int ?g > 0" by simp
    have "Inum bs ?sa = real_of_int ?g* ?r" by (simp add: reducecoeff)
    with sa have "Inum bs a > 0 = (real_of_int ?g * ?r > real_of_int ?g * 0)" by simp
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
    hence gp: "real_of_int ?g > 0" by simp
    have "Inum bs ?sa = real_of_int ?g* ?r" by (simp add: reducecoeff)
    with sa have "Inum bs a \<ge> 0 = (real_of_int ?g * ?r \<ge> real_of_int ?g * 0)" by simp
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
    hence gp: "real_of_int ?g > 0" by simp
    have "Inum bs ?sa = real_of_int ?g* ?r" by (simp add: reducecoeff)
    with sa have "Inum bs a = 0 = (real_of_int ?g * ?r = 0)" by simp
    also have "\<dots> = (?r = 0)" using gp
      by simp
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
    hence gp: "real_of_int ?g > 0" by simp
    have "Inum bs ?sa = real_of_int ?g* ?r" by (simp add: reducecoeff)
    with sa have "Inum bs a \<noteq> 0 = (real_of_int ?g * ?r \<noteq> 0)" by simp
    also have "\<dots> = (?r \<noteq> 0)" using gp
      by simp
    finally have ?case using H by (cases "?sa") (simp_all add: Let_def) }
  ultimately show ?case by blast
next
  case (12 i a)  let ?sa = "simpnum a"   have sa: "Inum bs ?sa = Inum bs a" by simp
  have "i=0 \<or> (\<bar>i\<bar> = 1 \<and> check_int a) \<or> (i\<noteq>0 \<and> ((\<bar>i\<bar> \<noteq> 1) \<or> (\<not> check_int a)))" by auto
  {assume "i=0" hence ?case using "12.hyps" by (simp add: rdvd_left_0_eq Let_def)}
  moreover
  {assume ai1: "\<bar>i\<bar> = 1" and ai: "check_int a"
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
  {assume inz: "i\<noteq>0" and cond: "(\<bar>i\<bar> \<noteq> 1) \<or> (\<not> check_int a)"
    {fix v assume "?sa = C v" hence ?case using sa[symmetric] inz cond
        by (cases "\<bar>i\<bar> = 1", auto simp add: int_rdvd_iff) }
    moreover {assume H:"\<not> (\<exists> v. ?sa = C v)"
      hence th: "simpfm (Dvd i a) = Dvd (fst (simpdvd i ?sa)) (snd (simpdvd i ?sa))" using inz cond by (cases ?sa, auto simp add: Let_def split_def)
      from simpnum_nz have nz:"nozerocoeff ?sa" by simp
      from simpdvd [OF nz inz] th have ?case using sa by simp}
    ultimately have ?case by blast}
  ultimately show ?case by blast
next
  case (13 i a)  let ?sa = "simpnum a"   have sa: "Inum bs ?sa = Inum bs a" by simp
  have "i=0 \<or> (\<bar>i\<bar> = 1 \<and> check_int a) \<or> (i\<noteq>0 \<and> ((\<bar>i\<bar> \<noteq> 1) \<or> (\<not> check_int a)))" by auto
  {assume "i=0" hence ?case using "13.hyps" by (simp add: rdvd_left_0_eq Let_def)}
  moreover
  {assume ai1: "\<bar>i\<bar> = 1" and ai: "check_int a"
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
  {assume inz: "i\<noteq>0" and cond: "(\<bar>i\<bar> \<noteq> 1) \<or> (\<not> check_int a)"
    {fix v assume "?sa = C v" hence ?case using sa[symmetric] inz cond
        by (cases "\<bar>i\<bar> = 1", auto simp add: int_rdvd_iff) }
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
    by (simp add: CJNB_def Let_def split_def)
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

fun qelim :: "fm \<Rightarrow> (fm \<Rightarrow> fm) \<Rightarrow> fm"
where
  "qelim (E p) = (\<lambda> qe. DJ (CJNB qe) (qelim p qe))"
| "qelim (A p) = (\<lambda> qe. not (qe ((qelim (Not p) qe))))"
| "qelim (Not p) = (\<lambda> qe. not (qelim p qe))"
| "qelim (And p q) = (\<lambda> qe. conj (qelim p qe) (qelim q qe))"
| "qelim (Or  p q) = (\<lambda> qe. disj (qelim p qe) (qelim q qe))"
| "qelim (Imp p q) = (\<lambda> qe. disj (qelim (Not p) qe) (qelim q qe))"
| "qelim (Iff p q) = (\<lambda> qe. iff (qelim p qe) (qelim q qe))"
| "qelim p = (\<lambda> y. simpfm p)"

lemma qelim_ci:
  assumes qe_inv: "\<forall> bs p. qfree p \<longrightarrow> qfree (qe p) \<and> (Ifm bs (qe p) = Ifm bs (E p))"
  shows "\<And> bs. qfree (qelim p qe) \<and> (Ifm bs (qelim p qe) = Ifm bs p)"
  using qe_inv DJ_qe[OF CJNB_qe[OF qe_inv]]
  by (induct p rule: qelim.induct) (auto simp del: simpfm.simps)


text \<open>The \<open>\<int>\<close> Part\<close>
text\<open>Linearity for fm where Bound 0 ranges over \<open>\<int>\<close>\<close>

fun zsplit0 :: "num \<Rightarrow> int \<times> num" (* splits the bounded from the unbounded part*)
where
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

lemma zsplit0_I:
  shows "\<And> n a. zsplit0 t = (n,a) \<Longrightarrow> (Inum ((real_of_int (x::int)) #bs) (CN 0 n a) = Inum (real_of_int x #bs) t) \<and> numbound0 a"
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
  from 6 have "(\<exists> x y. (x,y) = zsplit0 s) \<longrightarrow> (\<forall>xa xb. zsplit0 t = (xa, xb) \<longrightarrow> Inum (real_of_int x # bs) (CN 0 xa xb) = Inum (real_of_int x # bs) t \<and> numbound0 xb)" by blast (*FIXME*)
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
  from 7 have "(\<exists> x y. (x,y) = zsplit0 s) \<longrightarrow> (\<forall>xa xb. zsplit0 t = (xa, xb) \<longrightarrow> Inum (real_of_int x # bs) (CN 0 xa xb) = Inum (real_of_int x # bs) t \<and> numbound0 xb)" by blast (*FIXME*)
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
  hence "?I x (Mul i t) = (real_of_int i) * ?I x (CN 0 ?nt ?at)" by simp
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
  have th': "(real_of_int ?nt)*(real_of_int x) = real_of_int (?nt * x)" by simp
  have "?I x (Floor t) = ?I x (Floor (CN 0 ?nt ?at))" using th2 by simp
  also have "\<dots> = real_of_int \<lfloor>real_of_int ?nt * real_of_int x + ?I x ?at\<rfloor>" by simp
  also have "\<dots> = real_of_int \<lfloor>?I x ?at + real_of_int (?nt * x)\<rfloor>" by (simp add: ac_simps)
  also have "\<dots> = real_of_int (\<lfloor>?I x ?at\<rfloor> + (?nt * x))"
    by (simp add: of_int_mult[symmetric] del: of_int_mult)
  also have "\<dots> = real_of_int (?nt)*(real_of_int x) + real_of_int \<lfloor>?I x ?at\<rfloor>" by (simp add: ac_simps)
  finally have "?I x (Floor t) = ?I x (CN 0 n a)" using th by simp
  with na show ?case by simp
qed

fun iszlfm :: "fm \<Rightarrow> real list \<Rightarrow> bool"   (* Linearity test for fm *)
where
  "iszlfm (And p q) = (\<lambda> bs. iszlfm p bs \<and> iszlfm q bs)"
| "iszlfm (Or p q) = (\<lambda> bs. iszlfm p bs \<and> iszlfm q bs)"
| "iszlfm (Eq  (CN 0 c e)) = (\<lambda> bs. c>0 \<and> numbound0 e \<and> isint e bs)"
| "iszlfm (NEq (CN 0 c e)) = (\<lambda> bs. c>0 \<and> numbound0 e \<and> isint e bs)"
| "iszlfm (Lt  (CN 0 c e)) = (\<lambda> bs. c>0 \<and> numbound0 e \<and> isint e bs)"
| "iszlfm (Le  (CN 0 c e)) = (\<lambda> bs. c>0 \<and> numbound0 e \<and> isint e bs)"
| "iszlfm (Gt  (CN 0 c e)) = (\<lambda> bs. c>0 \<and> numbound0 e \<and> isint e bs)"
| "iszlfm (Ge  (CN 0 c e)) = (\<lambda> bs. c>0 \<and> numbound0 e \<and> isint e bs)"
| "iszlfm (Dvd i (CN 0 c e)) =
                 (\<lambda> bs. c>0 \<and> i>0 \<and> numbound0 e \<and> isint e bs)"
| "iszlfm (NDvd i (CN 0 c e))=
                 (\<lambda> bs. c>0 \<and> i>0 \<and> numbound0 e \<and> isint e bs)"
| "iszlfm p = (\<lambda> bs. isatom p \<and> (bound0 p))"

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

fun zlfm :: "fm \<Rightarrow> fm"       (* Linearity transformation for fm *)
where
  "zlfm (And p q) = conj (zlfm p) (zlfm q)"
| "zlfm (Or p q) = disj (zlfm p) (zlfm q)"
| "zlfm (Imp p q) = disj (zlfm (Not p)) (zlfm q)"
| "zlfm (Iff p q) = disj (conj (zlfm p) (zlfm q)) (conj (zlfm (Not p)) (zlfm (Not q)))"
| "zlfm (Lt a) = (let (c,r) = zsplit0 a in
     if c=0 then Lt r else
     if c>0 then Or (Lt (CN 0 c (Neg (Floor (Neg r))))) (And (Eq (CN 0 c (Neg (Floor (Neg r))))) (Lt (Add (Floor (Neg r)) r)))
     else Or (Gt (CN 0 (-c) (Floor(Neg r)))) (And (Eq(CN 0 (-c) (Floor(Neg r)))) (Lt (Add (Floor (Neg r)) r))))"
| "zlfm (Le a) = (let (c,r) = zsplit0 a in
     if c=0 then Le r else
     if c>0 then Or (Le (CN 0 c (Neg (Floor (Neg r))))) (And (Eq (CN 0 c (Neg (Floor (Neg r))))) (Lt (Add (Floor (Neg r)) r)))
     else Or (Ge (CN 0 (-c) (Floor(Neg r)))) (And (Eq(CN 0 (-c) (Floor(Neg r)))) (Lt (Add (Floor (Neg r)) r))))"
| "zlfm (Gt a) = (let (c,r) = zsplit0 a in
     if c=0 then Gt r else
     if c>0 then Or (Gt (CN 0 c (Floor r))) (And (Eq (CN 0 c (Floor r))) (Lt (Sub (Floor r) r)))
     else Or (Lt (CN 0 (-c) (Neg (Floor r)))) (And (Eq(CN 0 (-c) (Neg (Floor r)))) (Lt (Sub (Floor r) r))))"
| "zlfm (Ge a) = (let (c,r) = zsplit0 a in
     if c=0 then Ge r else
     if c>0 then Or (Ge (CN 0 c (Floor r))) (And (Eq (CN 0 c (Floor r))) (Lt (Sub (Floor r) r)))
     else Or (Le (CN 0 (-c) (Neg (Floor r)))) (And (Eq(CN 0 (-c) (Neg (Floor r)))) (Lt (Sub (Floor r) r))))"
| "zlfm (Eq a) = (let (c,r) = zsplit0 a in
              if c=0 then Eq r else
      if c>0 then (And (Eq (CN 0 c (Neg (Floor (Neg r))))) (Eq (Add (Floor (Neg r)) r)))
      else (And (Eq (CN 0 (-c) (Floor (Neg r)))) (Eq (Add (Floor (Neg r)) r))))"
| "zlfm (NEq a) = (let (c,r) = zsplit0 a in
              if c=0 then NEq r else
      if c>0 then (Or (NEq (CN 0 c (Neg (Floor (Neg r))))) (NEq (Add (Floor (Neg r)) r)))
      else (Or (NEq (CN 0 (-c) (Floor (Neg r)))) (NEq (Add (Floor (Neg r)) r))))"
| "zlfm (Dvd i a) = (if i=0 then zlfm (Eq a)
  else (let (c,r) = zsplit0 a in
              if c=0 then Dvd \<bar>i\<bar> r else
      if c>0 then And (Eq (Sub (Floor r) r)) (Dvd \<bar>i\<bar> (CN 0 c (Floor r)))
      else And (Eq (Sub (Floor r) r)) (Dvd \<bar>i\<bar> (CN 0 (-c) (Neg (Floor r))))))"
| "zlfm (NDvd i a) = (if i=0 then zlfm (NEq a)
  else (let (c,r) = zsplit0 a in
              if c=0 then NDvd \<bar>i\<bar> r else
      if c>0 then Or (NEq (Sub (Floor r) r)) (NDvd \<bar>i\<bar> (CN 0 c (Floor r)))
      else Or (NEq (Sub (Floor r) r)) (NDvd \<bar>i\<bar> (CN 0 (-c) (Neg (Floor r))))))"
| "zlfm (Not (And p q)) = disj (zlfm (Not p)) (zlfm (Not q))"
| "zlfm (Not (Or p q)) = conj (zlfm (Not p)) (zlfm (Not q))"
| "zlfm (Not (Imp p q)) = conj (zlfm p) (zlfm (Not q))"
| "zlfm (Not (Iff p q)) = disj (conj(zlfm p) (zlfm(Not q))) (conj (zlfm(Not p)) (zlfm q))"
| "zlfm (Not (Not p)) = zlfm p"
| "zlfm (Not T) = F"
| "zlfm (Not F) = T"
| "zlfm (Not (Lt a)) = zlfm (Ge a)"
| "zlfm (Not (Le a)) = zlfm (Gt a)"
| "zlfm (Not (Gt a)) = zlfm (Le a)"
| "zlfm (Not (Ge a)) = zlfm (Lt a)"
| "zlfm (Not (Eq a)) = zlfm (NEq a)"
| "zlfm (Not (NEq a)) = zlfm (Eq a)"
| "zlfm (Not (Dvd i a)) = zlfm (NDvd i a)"
| "zlfm (Not (NDvd i a)) = zlfm (Dvd i a)"
| "zlfm p = p"

lemma split_int_less_real:
  "(real_of_int (a::int) < b) = (a < \<lfloor>b\<rfloor> \<or> (a = \<lfloor>b\<rfloor> \<and> real_of_int \<lfloor>b\<rfloor> < b))"
proof( auto)
  assume alb: "real_of_int a < b" and agb: "\<not> a < \<lfloor>b\<rfloor>"
  from agb have "\<lfloor>b\<rfloor> \<le> a" by simp
  hence th: "b < real_of_int a + 1" by (simp only: floor_le_iff)
  from floor_eq[OF alb th] show "a = \<lfloor>b\<rfloor>" by simp
next
  assume alb: "a < \<lfloor>b\<rfloor>"
  hence "real_of_int a < real_of_int \<lfloor>b\<rfloor>" by simp
  moreover have "real_of_int \<lfloor>b\<rfloor> \<le> b" by simp
  ultimately show  "real_of_int a < b" by arith
qed

lemma split_int_less_real':
  "(real_of_int (a::int) + b < 0) = (real_of_int a - real_of_int \<lfloor>- b\<rfloor> < 0 \<or> (real_of_int a - real_of_int \<lfloor>- b\<rfloor> = 0 \<and> real_of_int \<lfloor>- b\<rfloor> + b < 0))"
proof-
  have "(real_of_int a + b <0) = (real_of_int a < -b)" by arith
  with split_int_less_real[where a="a" and b="-b"] show ?thesis by arith
qed

lemma split_int_gt_real':
  "(real_of_int (a::int) + b > 0) = (real_of_int a + real_of_int \<lfloor>b\<rfloor> > 0 \<or> (real_of_int a + real_of_int \<lfloor>b\<rfloor> = 0 \<and> real_of_int \<lfloor>b\<rfloor> - b < 0))"
proof-
  have th: "(real_of_int a + b >0) = (real_of_int (-a) + (-b)< 0)" by arith
  show ?thesis 
    by (simp only:th split_int_less_real'[where a="-a" and b="-b"]) (auto simp add: algebra_simps)
qed

lemma split_int_le_real:
  "(real_of_int (a::int) \<le> b) = (a \<le> \<lfloor>b\<rfloor> \<or> (a = \<lfloor>b\<rfloor> \<and> real_of_int \<lfloor>b\<rfloor> < b))"
proof( auto)
  assume alb: "real_of_int a \<le> b" and agb: "\<not> a \<le> \<lfloor>b\<rfloor>"
  from alb have "\<lfloor>real_of_int a\<rfloor> \<le> \<lfloor>b\<rfloor>" by (simp only: floor_mono)
  hence "a \<le> \<lfloor>b\<rfloor>" by simp with agb show "False" by simp
next
  assume alb: "a \<le> \<lfloor>b\<rfloor>"
  hence "real_of_int a \<le> real_of_int \<lfloor>b\<rfloor>" by (simp only: floor_mono)
  also have "\<dots>\<le> b" by simp  finally show  "real_of_int a \<le> b" .
qed

lemma split_int_le_real':
  "(real_of_int (a::int) + b \<le> 0) = (real_of_int a - real_of_int \<lfloor>- b\<rfloor> \<le> 0 \<or> (real_of_int a - real_of_int \<lfloor>- b\<rfloor> = 0 \<and> real_of_int \<lfloor>- b\<rfloor> + b < 0))"
proof-
  have "(real_of_int a + b \<le>0) = (real_of_int a \<le> -b)" by arith
  with split_int_le_real[where a="a" and b="-b"] show ?thesis by arith
qed

lemma split_int_ge_real':
  "(real_of_int (a::int) + b \<ge> 0) = (real_of_int a + real_of_int \<lfloor>b\<rfloor> \<ge> 0 \<or> (real_of_int a + real_of_int \<lfloor>b\<rfloor> = 0 \<and> real_of_int \<lfloor>b\<rfloor> - b < 0))"
proof-
  have th: "(real_of_int a + b \<ge>0) = (real_of_int (-a) + (-b) \<le> 0)" by arith
  show ?thesis by (simp only: th split_int_le_real'[where a="-a" and b="-b"])
    (simp add: algebra_simps ,arith)
qed

lemma split_int_eq_real: "(real_of_int (a::int) = b) = ( a = \<lfloor>b\<rfloor> \<and> b = real_of_int \<lfloor>b\<rfloor>)" (is "?l = ?r")
by auto

lemma split_int_eq_real': "(real_of_int (a::int) + b = 0) = ( a - \<lfloor>- b\<rfloor> = 0 \<and> real_of_int \<lfloor>- b\<rfloor> + b = 0)" (is "?l = ?r")
proof-
  have "?l = (real_of_int a = -b)" by arith
  with split_int_eq_real[where a="a" and b="-b"] show ?thesis by simp arith
qed

lemma zlfm_I:
  assumes qfp: "qfree p"
  shows "(Ifm (real_of_int i #bs) (zlfm p) = Ifm (real_of_int i# bs) p) \<and> iszlfm (zlfm p) (real_of_int (i::int) #bs)"
  (is "(?I (?l p) = ?I p) \<and> ?L (?l p)")
using qfp
proof(induct p rule: zlfm.induct)
  case (5 a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c,?r)" by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"]
  have Ia:"Inum (real_of_int i # bs) a = Inum (real_of_int i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r" by auto
  let ?N = "\<lambda> t. Inum (real_of_int i#bs) t"
  have "?c = 0 \<or> (?c >0 \<and> ?c\<noteq>0) \<or> (?c<0 \<and> ?c\<noteq>0)" by arith
  moreover
  {assume "?c=0" hence ?case using zsplit0_I[OF spl, where x="i" and bs="bs"]
      by (cases "?r", simp_all add: Let_def split_def,rename_tac nat a b,case_tac "nat", simp_all)}
  moreover
  {assume cp: "?c > 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Lt a))"
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Lt a) = (real_of_int (?c * i) + (?N ?r) < 0)" using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (?I (?l (Lt a)))" apply (simp only: split_int_less_real'[where a="?c*i" and b="?N ?r"]) by (simp add: Ia cp cnz Let_def split_def)
    finally have ?case using l by simp}
  moreover
  {assume cn: "?c < 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Lt a))"
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Lt a) = (real_of_int (?c * i) + (?N ?r) < 0)" using Ia by (simp add: Let_def split_def)
    also from cn cnz have "\<dots> = (?I (?l (Lt a)))" by (simp only: split_int_less_real'[where a="?c*i" and b="?N ?r"]) (simp add: Ia Let_def split_def ac_simps, arith)
    finally have ?case using l by simp}
  ultimately show ?case by blast
next
  case (6 a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c,?r)" by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"]
  have Ia:"Inum (real_of_int i # bs) a = Inum (real_of_int i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r" by auto
  let ?N = "\<lambda> t. Inum (real_of_int i#bs) t"
  have "?c = 0 \<or> (?c >0 \<and> ?c\<noteq>0) \<or> (?c<0 \<and> ?c\<noteq>0)" by arith
  moreover
  {assume "?c=0" hence ?case using zsplit0_I[OF spl, where x="i" and bs="bs"]
      by (cases "?r", simp_all add: Let_def split_def, rename_tac nat a b, case_tac "nat",simp_all)}
  moreover
  {assume cp: "?c > 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Le a))"
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Le a) = (real_of_int (?c * i) + (?N ?r) \<le> 0)" using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (?I (?l (Le a)))" by (simp only: split_int_le_real'[where a="?c*i" and b="?N ?r"]) (simp add: Ia cp cnz Let_def split_def)
    finally have ?case using l by simp}
  moreover
  {assume cn: "?c < 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Le a))"
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Le a) = (real_of_int (?c * i) + (?N ?r) \<le> 0)" using Ia by (simp add: Let_def split_def)
    also from cn cnz have "\<dots> = (?I (?l (Le a)))" by (simp only: split_int_le_real'[where a="?c*i" and b="?N ?r"]) (simp add: Ia Let_def split_def ac_simps, arith)
    finally have ?case using l by simp}
  ultimately show ?case by blast
next
  case (7 a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c,?r)" by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"]
  have Ia:"Inum (real_of_int i # bs) a = Inum (real_of_int i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r" by auto
  let ?N = "\<lambda> t. Inum (real_of_int i#bs) t"
  have "?c = 0 \<or> (?c >0 \<and> ?c\<noteq>0) \<or> (?c<0 \<and> ?c\<noteq>0)" by arith
  moreover
  {assume "?c=0" hence ?case using zsplit0_I[OF spl, where x="i" and bs="bs"]
      by (cases "?r", simp_all add: Let_def split_def, rename_tac nat a b, case_tac "nat", simp_all)}
  moreover
  {assume cp: "?c > 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Gt a))"
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Gt a) = (real_of_int (?c * i) + (?N ?r) > 0)" using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (?I (?l (Gt a)))" by (simp only: split_int_gt_real'[where a="?c*i" and b="?N ?r"]) (simp add: Ia cp cnz Let_def split_def)
    finally have ?case using l by simp}
  moreover
  {assume cn: "?c < 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Gt a))"
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Gt a) = (real_of_int (?c * i) + (?N ?r) > 0)" using Ia by (simp add: Let_def split_def)
    also from cn cnz have "\<dots> = (?I (?l (Gt a)))" by (simp only: split_int_gt_real'[where a="?c*i" and b="?N ?r"]) (simp add: Ia Let_def split_def ac_simps, arith)
    finally have ?case using l by simp}
  ultimately show ?case by blast
next
  case (8 a)
   let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c,?r)" by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"]
  have Ia:"Inum (real_of_int i # bs) a = Inum (real_of_int i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r" by auto
  let ?N = "\<lambda> t. Inum (real_of_int i#bs) t"
  have "?c = 0 \<or> (?c >0 \<and> ?c\<noteq>0) \<or> (?c<0 \<and> ?c\<noteq>0)" by arith
  moreover
  {assume "?c=0" hence ?case using zsplit0_I[OF spl, where x="i" and bs="bs"]
      by (cases "?r", simp_all add: Let_def split_def, rename_tac nat a b, case_tac "nat", simp_all)}
  moreover
  {assume cp: "?c > 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Ge a))"
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Ge a) = (real_of_int (?c * i) + (?N ?r) \<ge> 0)" using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (?I (?l (Ge a)))" by (simp only: split_int_ge_real'[where a="?c*i" and b="?N ?r"]) (simp add: Ia cp cnz Let_def split_def)
    finally have ?case using l by simp}
  moreover
  {assume cn: "?c < 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Ge a))"
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Ge a) = (real_of_int (?c * i) + (?N ?r) \<ge> 0)" using Ia by (simp add: Let_def split_def)
    also from cn cnz have "\<dots> = (?I (?l (Ge a)))" by (simp only: split_int_ge_real'[where a="?c*i" and b="?N ?r"]) (simp add: Ia Let_def split_def ac_simps, arith)
    finally have ?case using l by simp}
  ultimately show ?case by blast
next
  case (9 a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c,?r)" by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"]
  have Ia:"Inum (real_of_int i # bs) a = Inum (real_of_int i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r" by auto
  let ?N = "\<lambda> t. Inum (real_of_int i#bs) t"
  have "?c = 0 \<or> (?c >0 \<and> ?c\<noteq>0) \<or> (?c<0 \<and> ?c\<noteq>0)" by arith
  moreover
  {assume "?c=0" hence ?case using zsplit0_I[OF spl, where x="i" and bs="bs"]
      by (cases "?r", simp_all add: Let_def split_def, rename_tac nat a b, case_tac "nat", simp_all)}
  moreover
  {assume cp: "?c > 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Eq a))"
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Eq a) = (real_of_int (?c * i) + (?N ?r) = 0)" using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (?I (?l (Eq a)))" using cp cnz  by (simp only: split_int_eq_real'[where a="?c*i" and b="?N ?r"]) (simp add: Let_def split_def Ia of_int_mult[symmetric] del: of_int_mult)
    finally have ?case using l by simp}
  moreover
  {assume cn: "?c < 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (Eq a))"
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Eq a) = (real_of_int (?c * i) + (?N ?r) = 0)" using Ia by (simp add: Let_def split_def)
    also from cn cnz have "\<dots> = (?I (?l (Eq a)))" by (simp only: split_int_eq_real'[where a="?c*i" and b="?N ?r"]) (simp add: Let_def split_def Ia of_int_mult[symmetric] del: of_int_mult,arith)
    finally have ?case using l by simp}
  ultimately show ?case by blast
next
  case (10 a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c,?r)" by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"]
  have Ia:"Inum (real_of_int i # bs) a = Inum (real_of_int i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r" by auto
  let ?N = "\<lambda> t. Inum (real_of_int i#bs) t"
  have "?c = 0 \<or> (?c >0 \<and> ?c\<noteq>0) \<or> (?c<0 \<and> ?c\<noteq>0)" by arith
  moreover
  {assume "?c=0" hence ?case using zsplit0_I[OF spl, where x="i" and bs="bs"]
      by (cases "?r", simp_all add: Let_def split_def, rename_tac nat a b, case_tac "nat", simp_all)}
  moreover
  {assume cp: "?c > 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (NEq a))"
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (NEq a) = (real_of_int (?c * i) + (?N ?r) \<noteq> 0)" using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (?I (?l (NEq a)))" using cp cnz  by (simp only: split_int_eq_real'[where a="?c*i" and b="?N ?r"]) (simp add: Let_def split_def Ia of_int_mult[symmetric] del: of_int_mult)
    finally have ?case using l by simp}
  moreover
  {assume cn: "?c < 0" and cnz: "?c\<noteq>0" hence l: "?L (?l (NEq a))"
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (NEq a) = (real_of_int (?c * i) + (?N ?r) \<noteq> 0)" using Ia by (simp add: Let_def split_def)
    also from cn cnz have "\<dots> = (?I (?l (NEq a)))" by (simp only: split_int_eq_real'[where a="?c*i" and b="?N ?r"]) (simp add: Let_def split_def Ia of_int_mult[symmetric] del: of_int_mult,arith)
    finally have ?case using l by simp}
  ultimately show ?case by blast
next
  case (11 j a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c,?r)" by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"]
  have Ia:"Inum (real_of_int i # bs) a = Inum (real_of_int i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r" by auto
  let ?N = "\<lambda> t. Inum (real_of_int i#bs) t"
  have "j=0 \<or> (j\<noteq>0 \<and> ?c = 0) \<or> (j\<noteq>0 \<and> ?c >0 \<and> ?c\<noteq>0) \<or> (j\<noteq> 0 \<and> ?c<0 \<and> ?c\<noteq>0)" by arith
  moreover
  { assume j: "j=0" hence z: "zlfm (Dvd j a) = (zlfm (Eq a))" by (simp add: Let_def)
    hence ?case using 11 j by (simp del: zlfm.simps add: rdvd_left_0_eq)}
  moreover
  {assume "?c=0" and "j\<noteq>0" hence ?case
      using zsplit0_I[OF spl, where x="i" and bs="bs"] rdvd_abs1[where d="j"]
      by (cases "?r", simp_all add: Let_def split_def, rename_tac nat a b, case_tac "nat", simp_all)}
  moreover
  {assume cp: "?c > 0" and cnz: "?c\<noteq>0" and jnz: "j\<noteq>0" hence l: "?L (?l (Dvd j a))"
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Dvd j a) = (real_of_int j rdvd (real_of_int (?c * i) + (?N ?r)))"
      using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (real_of_int \<bar>j\<bar> rdvd real_of_int (?c*i) + (?N ?r))"
      by (simp only: rdvd_abs1[where d="j" and t="real_of_int (?c*i) + ?N ?r", symmetric]) simp
    also have "\<dots> = (\<bar>j\<bar> dvd \<lfloor>(?N ?r) + real_of_int (?c*i)\<rfloor> \<and>
       (real_of_int \<lfloor>(?N ?r) + real_of_int (?c*i)\<rfloor> = (real_of_int (?c*i) + (?N ?r))))"
      by(simp only: int_rdvd_real[where i="\<bar>j\<bar>" and x="real_of_int (?c*i) + (?N ?r)"]) (simp only: ac_simps)
    also have "\<dots> = (?I (?l (Dvd j a)))" using cp cnz jnz
      by (simp add: Let_def split_def int_rdvd_iff[symmetric]
        del: of_int_mult) (auto simp add: ac_simps)
    finally have ?case using l jnz  by simp }
  moreover
  {assume cn: "?c < 0" and cnz: "?c\<noteq>0" and jnz: "j\<noteq>0" hence l: "?L (?l (Dvd j a))"
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (Dvd j a) = (real_of_int j rdvd (real_of_int (?c * i) + (?N ?r)))"
      using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (real_of_int \<bar>j\<bar> rdvd real_of_int (?c*i) + (?N ?r))"
      by (simp only: rdvd_abs1[where d="j" and t="real_of_int (?c*i) + ?N ?r", symmetric]) simp
    also have "\<dots> = (\<bar>j\<bar> dvd \<lfloor>(?N ?r) + real_of_int (?c*i)\<rfloor> \<and>
       (real_of_int \<lfloor>(?N ?r) + real_of_int (?c*i)\<rfloor> = (real_of_int (?c*i) + (?N ?r))))"
      by(simp only: int_rdvd_real[where i="\<bar>j\<bar>" and x="real_of_int (?c*i) + (?N ?r)"]) (simp only: ac_simps)
    also have "\<dots> = (?I (?l (Dvd j a)))" using cn cnz jnz
      using rdvd_minus [where d="\<bar>j\<bar>" and t="real_of_int (?c*i + \<lfloor>?N ?r\<rfloor>)", simplified, symmetric]
      by (simp add: Let_def split_def int_rdvd_iff[symmetric]
        del: of_int_mult) (auto simp add: ac_simps)
    finally have ?case using l jnz by blast }
  ultimately show ?case by blast
next
  case (12 j a)
  let ?c = "fst (zsplit0 a)"
  let ?r = "snd (zsplit0 a)"
  have spl: "zsplit0 a = (?c,?r)" by simp
  from zsplit0_I[OF spl, where x="i" and bs="bs"]
  have Ia:"Inum (real_of_int i # bs) a = Inum (real_of_int i #bs) (CN 0 ?c ?r)" and nb: "numbound0 ?r" by auto
  let ?N = "\<lambda> t. Inum (real_of_int i#bs) t"
  have "j=0 \<or> (j\<noteq>0 \<and> ?c = 0) \<or> (j\<noteq>0 \<and> ?c >0 \<and> ?c\<noteq>0) \<or> (j\<noteq> 0 \<and> ?c<0 \<and> ?c\<noteq>0)" by arith
  moreover
  {assume j: "j=0" hence z: "zlfm (NDvd j a) = (zlfm (NEq a))" by (simp add: Let_def)
    hence ?case using 12 j by (simp del: zlfm.simps add: rdvd_left_0_eq)}
  moreover
  {assume "?c=0" and "j\<noteq>0" hence ?case
      using zsplit0_I[OF spl, where x="i" and bs="bs"] rdvd_abs1[where d="j"]
      by (cases "?r", simp_all add: Let_def split_def, rename_tac nat a b, case_tac "nat", simp_all)}
  moreover
  {assume cp: "?c > 0" and cnz: "?c\<noteq>0" and jnz: "j\<noteq>0" hence l: "?L (?l (NDvd j a))"
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (NDvd j a) = (\<not> (real_of_int j rdvd (real_of_int (?c * i) + (?N ?r))))"
      using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (\<not> (real_of_int \<bar>j\<bar> rdvd real_of_int (?c*i) + (?N ?r)))"
      by (simp only: rdvd_abs1[where d="j" and t="real_of_int (?c*i) + ?N ?r", symmetric]) simp
    also have "\<dots> = (\<not> (\<bar>j\<bar> dvd \<lfloor>(?N ?r) + real_of_int (?c*i)\<rfloor> \<and>
       (real_of_int \<lfloor>(?N ?r) + real_of_int (?c*i)\<rfloor> = (real_of_int (?c*i) + (?N ?r)))))"
      by(simp only: int_rdvd_real[where i="\<bar>j\<bar>" and x="real_of_int (?c*i) + (?N ?r)"]) (simp only: ac_simps)
    also have "\<dots> = (?I (?l (NDvd j a)))" using cp cnz jnz
      by (simp add: Let_def split_def int_rdvd_iff[symmetric]
        del: of_int_mult) (auto simp add: ac_simps)
    finally have ?case using l jnz  by simp }
  moreover
  {assume cn: "?c < 0" and cnz: "?c\<noteq>0" and jnz: "j\<noteq>0" hence l: "?L (?l (NDvd j a))"
      by (simp add: nb Let_def split_def isint_Floor isint_neg)
    have "?I (NDvd j a) = (\<not> (real_of_int j rdvd (real_of_int (?c * i) + (?N ?r))))"
      using Ia by (simp add: Let_def split_def)
    also have "\<dots> = (\<not> (real_of_int \<bar>j\<bar> rdvd real_of_int (?c*i) + (?N ?r)))"
      by (simp only: rdvd_abs1[where d="j" and t="real_of_int (?c*i) + ?N ?r", symmetric]) simp
    also have "\<dots> = (\<not> (\<bar>j\<bar> dvd \<lfloor>(?N ?r) + real_of_int (?c*i)\<rfloor> \<and>
       (real_of_int \<lfloor>(?N ?r) + real_of_int (?c*i)\<rfloor> = (real_of_int (?c*i) + (?N ?r)))))"
      by(simp only: int_rdvd_real[where i="\<bar>j\<bar>" and x="real_of_int (?c*i) + (?N ?r)"]) (simp only: ac_simps)
    also have "\<dots> = (?I (?l (NDvd j a)))" using cn cnz jnz
      using rdvd_minus [where d="\<bar>j\<bar>" and t="real_of_int (?c*i + \<lfloor>?N ?r\<rfloor>)", simplified, symmetric]
      by (simp add: Let_def split_def int_rdvd_iff[symmetric]
        del: of_int_mult) (auto simp add: ac_simps)
    finally have ?case using l jnz by blast }
  ultimately show ?case by blast
qed auto

text\<open>plusinf : Virtual substitution of \<open>+\<infinity>\<close>
       minusinf: Virtual substitution of \<open>-\<infinity>\<close>
       \<open>\<delta>\<close> Compute lcm \<open>d| Dvd d  c*x+t \<in> p\<close>
       \<open>d_\<delta>\<close> checks if a given l divides all the ds above\<close>

fun minusinf:: "fm \<Rightarrow> fm"
where
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

fun plusinf:: "fm \<Rightarrow> fm"
where
  "plusinf (And p q) = conj (plusinf p) (plusinf q)"
| "plusinf (Or p q) = disj (plusinf p) (plusinf q)"
| "plusinf (Eq  (CN 0 c e)) = F"
| "plusinf (NEq (CN 0 c e)) = T"
| "plusinf (Lt  (CN 0 c e)) = F"
| "plusinf (Le  (CN 0 c e)) = F"
| "plusinf (Gt  (CN 0 c e)) = T"
| "plusinf (Ge  (CN 0 c e)) = T"
| "plusinf p = p"

fun \<delta> :: "fm \<Rightarrow> int"
where
  "\<delta> (And p q) = lcm (\<delta> p) (\<delta> q)"
| "\<delta> (Or p q) = lcm (\<delta> p) (\<delta> q)"
| "\<delta> (Dvd i (CN 0 c e)) = i"
| "\<delta> (NDvd i (CN 0 c e)) = i"
| "\<delta> p = 1"

fun d_\<delta> :: "fm \<Rightarrow> int \<Rightarrow> bool"
where
  "d_\<delta> (And p q) = (\<lambda> d. d_\<delta> p d \<and> d_\<delta> q d)"
| "d_\<delta> (Or p q) = (\<lambda> d. d_\<delta> p d \<and> d_\<delta> q d)"
| "d_\<delta> (Dvd i (CN 0 c e)) = (\<lambda> d. i dvd d)"
| "d_\<delta> (NDvd i (CN 0 c e)) = (\<lambda> d. i dvd d)"
| "d_\<delta> p = (\<lambda> d. True)"

lemma delta_mono:
  assumes lin: "iszlfm p bs"
  and d: "d dvd d'"
  and ad: "d_\<delta> p d"
  shows "d_\<delta> p d'"
  using lin ad d
proof(induct p rule: iszlfm.induct)
  case (9 i c e)  thus ?case using d
    by (simp add: dvd_trans[of "i" "d" "d'"])
next
  case (10 i c e) thus ?case using d
    by (simp add: dvd_trans[of "i" "d" "d'"])
qed simp_all

lemma \<delta> : assumes lin:"iszlfm p bs"
  shows "d_\<delta> p (\<delta> p) \<and> \<delta> p >0"
using lin
proof (induct p rule: iszlfm.induct)
  case (1 p q)
  let ?d = "\<delta> (And p q)"
  from 1 lcm_pos_int have dp: "?d >0" by simp
  have d1: "\<delta> p dvd \<delta> (And p q)" using 1 by simp
  hence th: "d_\<delta> p ?d"
    using delta_mono 1 by (simp only: iszlfm.simps) blast
  have "\<delta> q dvd \<delta> (And p q)" using 1 by simp
  hence th': "d_\<delta> q ?d" using delta_mono 1 by (simp only: iszlfm.simps) blast
  from th th' dp show ?case by simp
next
  case (2 p q)
  let ?d = "\<delta> (And p q)"
  from 2 lcm_pos_int have dp: "?d >0" by simp
  have "\<delta> p dvd \<delta> (And p q)" using 2 by simp
  hence th: "d_\<delta> p ?d" using delta_mono 2 by (simp only: iszlfm.simps) blast
  have "\<delta> q dvd \<delta> (And p q)" using 2 by simp
  hence th': "d_\<delta> q ?d" using delta_mono 2 by (simp only: iszlfm.simps) blast
  from th th' dp show ?case by simp
qed simp_all


lemma minusinf_inf:
  assumes linp: "iszlfm p (a # bs)"
  shows "\<exists> (z::int). \<forall> x < z. Ifm ((real_of_int x)#bs) (minusinf p) = Ifm ((real_of_int x)#bs) p"
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
  hence rcpos: "real_of_int c > 0" by simp
  from 3 have nbe: "numbound0 e" by simp
  fix y
  have "\<forall> x < \<lfloor>- (Inum (y#bs) e) / (real_of_int c)\<rfloor>. ?I x (?M (Eq (CN 0 c e))) = ?I x (Eq (CN 0 c e))"
  proof (simp add: less_floor_iff , rule allI, rule impI)
    fix x :: int
    assume A: "real_of_int x + 1 \<le> - (Inum (y # bs) e / real_of_int c)"
    hence th1:"real_of_int x < - (Inum (y # bs) e / real_of_int c)" by simp
    with rcpos  have "(real_of_int c)*(real_of_int  x) < (real_of_int c)*(- (Inum (y # bs) e / real_of_int c))"
      by (simp only: mult_strict_left_mono [OF th1 rcpos])
    hence "real_of_int c * real_of_int x + Inum (y # bs) e \<noteq> 0"using rcpos  by simp
    thus "real_of_int c * real_of_int x + Inum (real_of_int x # bs) e \<noteq> 0"
      using numbound0_I[OF nbe, where b="y" and bs="bs" and b'="real_of_int x"]  by simp
  qed
  thus ?case by blast
next
  case (4 c e)
  then have "c > 0" by simp hence rcpos: "real_of_int c > 0" by simp
  from 4 have nbe: "numbound0 e" by simp
  fix y
  have "\<forall> x < \<lfloor>- (Inum (y#bs) e) / (real_of_int c)\<rfloor>. ?I x (?M (NEq (CN 0 c e))) = ?I x (NEq (CN 0 c e))"
  proof (simp add: less_floor_iff , rule allI, rule impI)
    fix x :: int
    assume A: "real_of_int x + 1 \<le> - (Inum (y # bs) e / real_of_int c)"
    hence th1:"real_of_int x < - (Inum (y # bs) e / real_of_int c)" by simp
    with rcpos  have "(real_of_int c)*(real_of_int x) < (real_of_int c)*(- (Inum (y # bs) e / real_of_int c))"
      by (simp only: mult_strict_left_mono [OF th1 rcpos])
    hence "real_of_int c * real_of_int x + Inum (y # bs) e \<noteq> 0"using rcpos  by simp
    thus "real_of_int c * real_of_int x + Inum (real_of_int x # bs) e \<noteq> 0"
      using numbound0_I[OF nbe, where b="y" and bs="bs" and b'="real_of_int x"]  by simp
  qed
  thus ?case by blast
next
  case (5 c e)
  then have "c > 0" by simp hence rcpos: "real_of_int c > 0" by simp
  from 5 have nbe: "numbound0 e" by simp
  fix y
  have "\<forall> x < \<lfloor>- (Inum (y#bs) e) / (real_of_int c)\<rfloor>. ?I x (?M (Lt (CN 0 c e))) = ?I x (Lt (CN 0 c e))"
  proof (simp add: less_floor_iff , rule allI, rule impI)
    fix x :: int
    assume A: "real_of_int x + 1 \<le> - (Inum (y # bs) e / real_of_int c)"
    hence th1:"real_of_int x < - (Inum (y # bs) e / real_of_int c)" by simp
    with rcpos  have "(real_of_int c)*(real_of_int x) < (real_of_int c)*(- (Inum (y # bs) e / real_of_int c))"
      by (simp only: mult_strict_left_mono [OF th1 rcpos])
    thus "real_of_int c * real_of_int x + Inum (real_of_int x # bs) e < 0"
      using numbound0_I[OF nbe, where b="y" and bs="bs" and b'="real_of_int x"] rcpos by simp
  qed
  thus ?case by blast
next
  case (6 c e)
  then have "c > 0" by simp hence rcpos: "real_of_int c > 0" by simp
  from 6 have nbe: "numbound0 e" by simp
  fix y
  have "\<forall> x < \<lfloor>- (Inum (y#bs) e) / (real_of_int c)\<rfloor>. ?I x (?M (Le (CN 0 c e))) = ?I x (Le (CN 0 c e))"
  proof (simp add: less_floor_iff , rule allI, rule impI)
    fix x :: int
    assume A: "real_of_int x + 1 \<le> - (Inum (y # bs) e / real_of_int c)"
    hence th1:"real_of_int x < - (Inum (y # bs) e / real_of_int c)" by simp
    with rcpos  have "(real_of_int c)*(real_of_int x) < (real_of_int c)*(- (Inum (y # bs) e / real_of_int c))"
      by (simp only: mult_strict_left_mono [OF th1 rcpos])
    thus "real_of_int c * real_of_int x + Inum (real_of_int x # bs) e \<le> 0"
      using numbound0_I[OF nbe, where b="y" and bs="bs" and b'="real_of_int x"] rcpos by simp
  qed
  thus ?case by blast
next
  case (7 c e)
  then have "c > 0" by simp hence rcpos: "real_of_int c > 0" by simp
  from 7 have nbe: "numbound0 e" by simp
  fix y
  have "\<forall> x < \<lfloor>- (Inum (y#bs) e) / (real_of_int c)\<rfloor>. ?I x (?M (Gt (CN 0 c e))) = ?I x (Gt (CN 0 c e))"
  proof (simp add: less_floor_iff , rule allI, rule impI)
    fix x :: int
    assume A: "real_of_int x + 1 \<le> - (Inum (y # bs) e / real_of_int c)"
    hence th1:"real_of_int x < - (Inum (y # bs) e / real_of_int c)" by simp
    with rcpos  have "(real_of_int c)*(real_of_int x) < (real_of_int c)*(- (Inum (y # bs) e / real_of_int c))"
      by (simp only: mult_strict_left_mono [OF th1 rcpos])
    thus "\<not> (real_of_int c * real_of_int x + Inum (real_of_int x # bs) e>0)"
      using numbound0_I[OF nbe, where b="y" and bs="bs" and b'="real_of_int x"] rcpos by simp
  qed
  thus ?case by blast
next
  case (8 c e)
  then have "c > 0" by simp hence rcpos: "real_of_int c > 0" by simp
  from 8 have nbe: "numbound0 e" by simp
  fix y
  have "\<forall> x < \<lfloor>- (Inum (y#bs) e) / (real_of_int c)\<rfloor>. ?I x (?M (Ge (CN 0 c e))) = ?I x (Ge (CN 0 c e))"
  proof (simp add: less_floor_iff , rule allI, rule impI)
    fix x :: int
    assume A: "real_of_int x + 1 \<le> - (Inum (y # bs) e / real_of_int c)"
    hence th1:"real_of_int x < - (Inum (y # bs) e / real_of_int c)" by simp
    with rcpos  have "(real_of_int c)*(real_of_int x) < (real_of_int c)*(- (Inum (y # bs) e / real_of_int c))"
      by (simp only: mult_strict_left_mono [OF th1 rcpos])
    thus "\<not> real_of_int c * real_of_int x + Inum (real_of_int x # bs) e \<ge> 0"
      using numbound0_I[OF nbe, where b="y" and bs="bs" and b'="real_of_int x"] rcpos by simp
  qed
  thus ?case by blast
qed simp_all

lemma minusinf_repeats:
  assumes d: "d_\<delta> p d" and linp: "iszlfm p (a # bs)"
  shows "Ifm ((real_of_int(x - k*d))#bs) (minusinf p) = Ifm (real_of_int x #bs) (minusinf p)"
using linp d
proof(induct p rule: iszlfm.induct)
  case (9 i c e) hence nbe: "numbound0 e"  and id: "i dvd d" by simp+
    hence "\<exists> k. d=i*k" by (simp add: dvd_def)
    then obtain "di" where di_def: "d=i*di" by blast
    show ?case
    proof(simp add: numbound0_I[OF nbe,where bs="bs" and b="real_of_int x - real_of_int k * real_of_int d" and b'="real_of_int x"] right_diff_distrib, rule iffI)
      assume
        "real_of_int i rdvd real_of_int c * real_of_int x - real_of_int c * (real_of_int k * real_of_int d) + Inum (real_of_int x # bs) e"
      (is "?ri rdvd ?rc*?rx - ?rc*(?rk*?rd) + ?I x e" is "?ri rdvd ?rt")
      hence "\<exists> (l::int). ?rt = ?ri * (real_of_int l)" by (simp add: rdvd_def)
      hence "\<exists> (l::int). ?rc*?rx+ ?I x e = ?ri*(real_of_int l)+?rc*(?rk * (real_of_int i) * (real_of_int di))"
        by (simp add: algebra_simps di_def)
      hence "\<exists> (l::int). ?rc*?rx+ ?I x e = ?ri*(real_of_int (l + c*k*di))"
        by (simp add: algebra_simps)
      hence "\<exists> (l::int). ?rc*?rx+ ?I x e = ?ri* (real_of_int l)" by blast
      thus "real_of_int i rdvd real_of_int c * real_of_int x + Inum (real_of_int x # bs) e" using rdvd_def by simp
    next
      assume
        "real_of_int i rdvd real_of_int c * real_of_int x + Inum (real_of_int x # bs) e" (is "?ri rdvd ?rc*?rx+?e")
      hence "\<exists> (l::int). ?rc*?rx+?e = ?ri * (real_of_int l)" by (simp add: rdvd_def)
      hence "\<exists> (l::int). ?rc*?rx - real_of_int c * (real_of_int k * real_of_int d) +?e = ?ri * (real_of_int l) - real_of_int c * (real_of_int k * real_of_int d)" by simp
      hence "\<exists> (l::int). ?rc*?rx - real_of_int c * (real_of_int k * real_of_int d) +?e = ?ri * (real_of_int l) - real_of_int c * (real_of_int k * real_of_int i * real_of_int di)" by (simp add: di_def)
      hence "\<exists> (l::int). ?rc*?rx - real_of_int c * (real_of_int k * real_of_int d) +?e = ?ri * (real_of_int (l - c*k*di))" by (simp add: algebra_simps)
      hence "\<exists> (l::int). ?rc*?rx - real_of_int c * (real_of_int k * real_of_int d) +?e = ?ri * (real_of_int l)"
        by blast
      thus "real_of_int i rdvd real_of_int c * real_of_int x - real_of_int c * (real_of_int k * real_of_int d) + Inum (real_of_int x # bs) e" using rdvd_def by simp
    qed
next
  case (10 i c e) hence nbe: "numbound0 e"  and id: "i dvd d" by simp+
    hence "\<exists> k. d=i*k" by (simp add: dvd_def)
    then obtain "di" where di_def: "d=i*di" by blast
    show ?case
    proof(simp add: numbound0_I[OF nbe,where bs="bs" and b="real_of_int x - real_of_int k * real_of_int d" and b'="real_of_int x"] right_diff_distrib, rule iffI)
      assume
        "real_of_int i rdvd real_of_int c * real_of_int x - real_of_int c * (real_of_int k * real_of_int d) + Inum (real_of_int x # bs) e"
      (is "?ri rdvd ?rc*?rx - ?rc*(?rk*?rd) + ?I x e" is "?ri rdvd ?rt")
      hence "\<exists> (l::int). ?rt = ?ri * (real_of_int l)" by (simp add: rdvd_def)
      hence "\<exists> (l::int). ?rc*?rx+ ?I x e = ?ri*(real_of_int l)+?rc*(?rk * (real_of_int i) * (real_of_int di))"
        by (simp add: algebra_simps di_def)
      hence "\<exists> (l::int). ?rc*?rx+ ?I x e = ?ri*(real_of_int (l + c*k*di))"
        by (simp add: algebra_simps)
      hence "\<exists> (l::int). ?rc*?rx+ ?I x e = ?ri* (real_of_int l)" by blast
      thus "real_of_int i rdvd real_of_int c * real_of_int x + Inum (real_of_int x # bs) e" using rdvd_def by simp
    next
      assume
        "real_of_int i rdvd real_of_int c * real_of_int x + Inum (real_of_int x # bs) e" (is "?ri rdvd ?rc*?rx+?e")
      hence "\<exists> (l::int). ?rc*?rx+?e = ?ri * (real_of_int l)"
        by (simp add: rdvd_def)
      hence "\<exists> (l::int). ?rc*?rx - real_of_int c * (real_of_int k * real_of_int d) +?e = ?ri * (real_of_int l) - real_of_int c * (real_of_int k * real_of_int d)"
        by simp
      hence "\<exists> (l::int). ?rc*?rx - real_of_int c * (real_of_int k * real_of_int d) +?e = ?ri * (real_of_int l) - real_of_int c * (real_of_int k * real_of_int i * real_of_int di)"
        by (simp add: di_def)
      hence "\<exists> (l::int). ?rc*?rx - real_of_int c * (real_of_int k * real_of_int d) +?e = ?ri * (real_of_int (l - c*k*di))"
        by (simp add: algebra_simps)
      hence "\<exists> (l::int). ?rc*?rx - real_of_int c * (real_of_int k * real_of_int d) +?e = ?ri * (real_of_int l)"
        by blast
      thus "real_of_int i rdvd real_of_int c * real_of_int x - real_of_int c * (real_of_int k * real_of_int d) + Inum (real_of_int x # bs) e"
        using rdvd_def by simp
    qed
qed (auto simp add: numbound0_I[where bs="bs" and b="real_of_int(x - k*d)" and b'="real_of_int x"] simp del: of_int_mult of_int_diff)

lemma minusinf_ex:
  assumes lin: "iszlfm p (real_of_int (a::int) #bs)"
  and exmi: "\<exists> (x::int). Ifm (real_of_int x#bs) (minusinf p)" (is "\<exists> x. ?P1 x")
  shows "\<exists> (x::int). Ifm (real_of_int x#bs) p" (is "\<exists> x. ?P x")
proof-
  let ?d = "\<delta> p"
  from \<delta> [OF lin] have dpos: "?d >0" by simp
  from \<delta> [OF lin] have alld: "d_\<delta> p ?d" by simp
  from minusinf_repeats[OF alld lin] have th1:"\<forall> x k. ?P1 x = ?P1 (x - (k * ?d))" by simp
  from minusinf_inf[OF lin] have th2:"\<exists> z. \<forall> x. x<z \<longrightarrow> (?P x = ?P1 x)" by blast
  from minusinfinity [OF dpos th1 th2] exmi show ?thesis by blast
qed

lemma minusinf_bex:
  assumes lin: "iszlfm p (real_of_int (a::int) #bs)"
  shows "(\<exists> (x::int). Ifm (real_of_int x#bs) (minusinf p)) =
         (\<exists> (x::int)\<in> {1..\<delta> p}. Ifm (real_of_int x#bs) (minusinf p))"
  (is "(\<exists> x. ?P x) = _")
proof-
  let ?d = "\<delta> p"
  from \<delta> [OF lin] have dpos: "?d >0" by simp
  from \<delta> [OF lin] have alld: "d_\<delta> p ?d" by simp
  from minusinf_repeats[OF alld lin] have th1:"\<forall> x k. ?P x = ?P (x - (k * ?d))" by simp
  from periodic_finite_ex[OF dpos th1] show ?thesis by blast
qed

lemma dvd1_eq1: "x > 0 \<Longrightarrow> is_unit x \<longleftrightarrow> x = 1" for x :: int
  by simp

fun a_\<beta> :: "fm \<Rightarrow> int \<Rightarrow> fm" (* adjusts the coefficients of a formula *)
where
  "a_\<beta> (And p q) = (\<lambda> k. And (a_\<beta> p k) (a_\<beta> q k))"
| "a_\<beta> (Or p q) = (\<lambda> k. Or (a_\<beta> p k) (a_\<beta> q k))"
| "a_\<beta> (Eq  (CN 0 c e)) = (\<lambda> k. Eq (CN 0 1 (Mul (k div c) e)))"
| "a_\<beta> (NEq (CN 0 c e)) = (\<lambda> k. NEq (CN 0 1 (Mul (k div c) e)))"
| "a_\<beta> (Lt  (CN 0 c e)) = (\<lambda> k. Lt (CN 0 1 (Mul (k div c) e)))"
| "a_\<beta> (Le  (CN 0 c e)) = (\<lambda> k. Le (CN 0 1 (Mul (k div c) e)))"
| "a_\<beta> (Gt  (CN 0 c e)) = (\<lambda> k. Gt (CN 0 1 (Mul (k div c) e)))"
| "a_\<beta> (Ge  (CN 0 c e)) = (\<lambda> k. Ge (CN 0 1 (Mul (k div c) e)))"
| "a_\<beta> (Dvd i (CN 0 c e)) =(\<lambda> k. Dvd ((k div c)*i) (CN 0 1 (Mul (k div c) e)))"
| "a_\<beta> (NDvd i (CN 0 c e))=(\<lambda> k. NDvd ((k div c)*i) (CN 0 1 (Mul (k div c) e)))"
| "a_\<beta> p = (\<lambda> k. p)"

fun d_\<beta> :: "fm \<Rightarrow> int \<Rightarrow> bool" (* tests if all coeffs c of c divide a given l*)
where
  "d_\<beta> (And p q) = (\<lambda> k. (d_\<beta> p k) \<and> (d_\<beta> q k))"
| "d_\<beta> (Or p q) = (\<lambda> k. (d_\<beta> p k) \<and> (d_\<beta> q k))"
| "d_\<beta> (Eq  (CN 0 c e)) = (\<lambda> k. c dvd k)"
| "d_\<beta> (NEq (CN 0 c e)) = (\<lambda> k. c dvd k)"
| "d_\<beta> (Lt  (CN 0 c e)) = (\<lambda> k. c dvd k)"
| "d_\<beta> (Le  (CN 0 c e)) = (\<lambda> k. c dvd k)"
| "d_\<beta> (Gt  (CN 0 c e)) = (\<lambda> k. c dvd k)"
| "d_\<beta> (Ge  (CN 0 c e)) = (\<lambda> k. c dvd k)"
| "d_\<beta> (Dvd i (CN 0 c e)) =(\<lambda> k. c dvd k)"
| "d_\<beta> (NDvd i (CN 0 c e))=(\<lambda> k. c dvd k)"
| "d_\<beta> p = (\<lambda> k. True)"

fun \<zeta>  :: "fm \<Rightarrow> int" (* computes the lcm of all coefficients of x*)
where
  "\<zeta> (And p q) = lcm (\<zeta> p) (\<zeta> q)"
| "\<zeta> (Or p q) = lcm (\<zeta> p) (\<zeta> q)"
| "\<zeta> (Eq  (CN 0 c e)) = c"
| "\<zeta> (NEq (CN 0 c e)) = c"
| "\<zeta> (Lt  (CN 0 c e)) = c"
| "\<zeta> (Le  (CN 0 c e)) = c"
| "\<zeta> (Gt  (CN 0 c e)) = c"
| "\<zeta> (Ge  (CN 0 c e)) = c"
| "\<zeta> (Dvd i (CN 0 c e)) = c"
| "\<zeta> (NDvd i (CN 0 c e))= c"
| "\<zeta> p = 1"

fun \<beta> :: "fm \<Rightarrow> num list"
where
  "\<beta> (And p q) = (\<beta> p @ \<beta> q)"
| "\<beta> (Or p q) = (\<beta> p @ \<beta> q)"
| "\<beta> (Eq  (CN 0 c e)) = [Sub (C (- 1)) e]"
| "\<beta> (NEq (CN 0 c e)) = [Neg e]"
| "\<beta> (Lt  (CN 0 c e)) = []"
| "\<beta> (Le  (CN 0 c e)) = []"
| "\<beta> (Gt  (CN 0 c e)) = [Neg e]"
| "\<beta> (Ge  (CN 0 c e)) = [Sub (C (- 1)) e]"
| "\<beta> p = []"

fun \<alpha> :: "fm \<Rightarrow> num list"
where
  "\<alpha> (And p q) = (\<alpha> p @ \<alpha> q)"
| "\<alpha> (Or p q) = (\<alpha> p @ \<alpha> q)"
| "\<alpha> (Eq  (CN 0 c e)) = [Add (C (- 1)) e]"
| "\<alpha> (NEq (CN 0 c e)) = [e]"
| "\<alpha> (Lt  (CN 0 c e)) = [e]"
| "\<alpha> (Le  (CN 0 c e)) = [Add (C (- 1)) e]"
| "\<alpha> (Gt  (CN 0 c e)) = []"
| "\<alpha> (Ge  (CN 0 c e)) = []"
| "\<alpha> p = []"

fun mirror :: "fm \<Rightarrow> fm"
where
  "mirror (And p q) = And (mirror p) (mirror q)"
| "mirror (Or p q) = Or (mirror p) (mirror q)"
| "mirror (Eq  (CN 0 c e)) = Eq (CN 0 c (Neg e))"
| "mirror (NEq (CN 0 c e)) = NEq (CN 0 c (Neg e))"
| "mirror (Lt  (CN 0 c e)) = Gt (CN 0 c (Neg e))"
| "mirror (Le  (CN 0 c e)) = Ge (CN 0 c (Neg e))"
| "mirror (Gt  (CN 0 c e)) = Lt (CN 0 c (Neg e))"
| "mirror (Ge  (CN 0 c e)) = Le (CN 0 c (Neg e))"
| "mirror (Dvd i (CN 0 c e)) = Dvd i (CN 0 c (Neg e))"
| "mirror (NDvd i (CN 0 c e)) = NDvd i (CN 0 c (Neg e))"
| "mirror p = p"

lemma mirror_\<alpha>_\<beta>:
  assumes lp: "iszlfm p (a#bs)"
  shows "(Inum (real_of_int (i::int)#bs)) ` set (\<alpha> p) = (Inum (real_of_int i#bs)) ` set (\<beta> (mirror p))"
  using lp by (induct p rule: mirror.induct) auto

lemma mirror:
  assumes lp: "iszlfm p (a#bs)"
  shows "Ifm (real_of_int (x::int)#bs) (mirror p) = Ifm (real_of_int (- x)#bs) p"
  using lp
proof(induct p rule: iszlfm.induct)
  case (9 j c e)
  have th: "(real_of_int j rdvd real_of_int c * real_of_int x - Inum (real_of_int x # bs) e) =
       (real_of_int j rdvd - (real_of_int c * real_of_int x - Inum (real_of_int x # bs) e))"
    by (simp only: rdvd_minus[symmetric])
  from 9 th show ?case
    by (simp add: algebra_simps
      numbound0_I[where bs="bs" and b'="real_of_int x" and b="- real_of_int x"])
next
  case (10 j c e)
  have th: "(real_of_int j rdvd real_of_int c * real_of_int x - Inum (real_of_int x # bs) e) =
       (real_of_int j rdvd - (real_of_int c * real_of_int x - Inum (real_of_int x # bs) e))"
    by (simp only: rdvd_minus[symmetric])
  from 10 th show  ?case
    by (simp add: algebra_simps
      numbound0_I[where bs="bs" and b'="real_of_int x" and b="- real_of_int x"])
qed (auto simp add: numbound0_I[where bs="bs" and b="real_of_int x" and b'="- real_of_int x"])

lemma mirror_l: "iszlfm p (a#bs) \<Longrightarrow> iszlfm (mirror p) (a#bs)"
  by (induct p rule: mirror.induct) (auto simp add: isint_neg)

lemma mirror_d_\<beta>: "iszlfm p (a#bs) \<and> d_\<beta> p 1
  \<Longrightarrow> iszlfm (mirror p) (a#bs) \<and> d_\<beta> (mirror p) 1"
  by (induct p rule: mirror.induct) (auto simp add: isint_neg)

lemma mirror_\<delta>: "iszlfm p (a#bs) \<Longrightarrow> \<delta> (mirror p) = \<delta> p"
  by (induct p rule: mirror.induct) auto


lemma mirror_ex:
  assumes lp: "iszlfm p (real_of_int (i::int)#bs)"
  shows "(\<exists> (x::int). Ifm (real_of_int x#bs) (mirror p)) = (\<exists> (x::int). Ifm (real_of_int x#bs) p)"
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

lemma d_\<beta>_mono:
  assumes linp: "iszlfm p (a #bs)"
  and dr: "d_\<beta> p l"
  and d: "l dvd l'"
  shows "d_\<beta> p l'"
using dr linp dvd_trans[of _ "l" "l'", simplified d]
by (induct p rule: iszlfm.induct) simp_all

lemma \<alpha>_l: assumes lp: "iszlfm p (a#bs)"
  shows "\<forall> b\<in> set (\<alpha> p). numbound0 b \<and> isint b (a#bs)"
using lp
by(induct p rule: \<alpha>.induct, auto simp add: isint_add isint_c)

lemma \<zeta>:
  assumes linp: "iszlfm p (a #bs)"
  shows "\<zeta> p > 0 \<and> d_\<beta> p (\<zeta> p)"
using linp
proof(induct p rule: iszlfm.induct)
  case (1 p q)
  then  have dl1: "\<zeta> p dvd lcm (\<zeta> p) (\<zeta> q)" by simp
  from 1 have dl2: "\<zeta> q dvd lcm (\<zeta> p) (\<zeta> q)" by simp
  from 1 d_\<beta>_mono[where p = "p" and l="\<zeta> p" and l'="lcm (\<zeta> p) (\<zeta> q)"]
    d_\<beta>_mono[where p = "q" and l="\<zeta> q" and l'="lcm (\<zeta> p) (\<zeta> q)"]
    dl1 dl2 show ?case by (auto simp add: lcm_pos_int)
next
  case (2 p q)
  then have dl1: "\<zeta> p dvd lcm (\<zeta> p) (\<zeta> q)" by simp
  from 2 have dl2: "\<zeta> q dvd lcm (\<zeta> p) (\<zeta> q)" by simp
  from 2 d_\<beta>_mono[where p = "p" and l="\<zeta> p" and l'="lcm (\<zeta> p) (\<zeta> q)"]
    d_\<beta>_mono[where p = "q" and l="\<zeta> q" and l'="lcm (\<zeta> p) (\<zeta> q)"]
    dl1 dl2 show ?case by (auto simp add: lcm_pos_int)
qed (auto simp add: lcm_pos_int)

lemma a_\<beta>: assumes linp: "iszlfm p (a #bs)" and d: "d_\<beta> p l" and lp: "l > 0"
  shows "iszlfm (a_\<beta> p l) (a #bs) \<and> d_\<beta> (a_\<beta> p l) 1 \<and> (Ifm (real_of_int (l * x) #bs) (a_\<beta> p l) = Ifm ((real_of_int x)#bs) p)"
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
    hence cl:"c * (l div c) =l" using mult_div_mod_eq [where a="l" and b="c"]
      by simp
    hence "(real_of_int l * real_of_int x + real_of_int (l div c) * Inum (real_of_int x # bs) e < (0::real)) =
          (real_of_int (c * (l div c)) * real_of_int x + real_of_int (l div c) * Inum (real_of_int x # bs) e < 0)"
      by simp
    also have "\<dots> = (real_of_int (l div c) * (real_of_int c * real_of_int x + Inum (real_of_int x # bs) e) < (real_of_int (l div c)) * 0)" by (simp add: algebra_simps)
    also have "\<dots> = (real_of_int c * real_of_int x + Inum (real_of_int x # bs) e < 0)"
    using mult_less_0_iff [where a="real_of_int (l div c)" and b="real_of_int c * real_of_int x + Inum (real_of_int x # bs) e"] ldcp by simp
  finally show ?case using numbound0_I[OF be,where b="real_of_int (l * x)" and b'="real_of_int x" and bs="bs"] be  isint_Mul[OF ei] by simp
next
  case (6 c e) hence cp: "c>0" and be: "numbound0 e" and ei:"isint e (a#bs)" and d': "c dvd l" by simp+
    from lp cp have clel: "c\<le>l" by (simp add: zdvd_imp_le [OF d' lp])
    from cp have cnz: "c \<noteq> 0" by simp
    have "c div c\<le> l div c"
      by (simp add: zdiv_mono1[OF clel cp])
    then have ldcp:"0 < l div c"
      by (simp add: div_self[OF cnz])
    have "c * (l div c) = c* (l div c) + l mod c" using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
    hence cl:"c * (l div c) =l" using mult_div_mod_eq [where a="l" and b="c"]
      by simp
    hence "(real_of_int l * real_of_int x + real_of_int (l div c) * Inum (real_of_int x # bs) e \<le> (0::real)) =
          (real_of_int (c * (l div c)) * real_of_int x + real_of_int (l div c) * Inum (real_of_int x # bs) e \<le> 0)"
      by simp
    also have "\<dots> = (real_of_int (l div c) * (real_of_int c * real_of_int x + Inum (real_of_int x # bs) e) \<le> (real_of_int (l div c)) * 0)" by (simp add: algebra_simps)
    also have "\<dots> = (real_of_int c * real_of_int x + Inum (real_of_int x # bs) e \<le> 0)"
    using mult_le_0_iff [where a="real_of_int (l div c)" and b="real_of_int c * real_of_int x + Inum (real_of_int x # bs) e"] ldcp by simp
  finally show ?case using numbound0_I[OF be,where b="real_of_int (l * x)" and b'="real_of_int x" and bs="bs"]  be  isint_Mul[OF ei] by simp
next
  case (7 c e) hence cp: "c>0" and be: "numbound0 e" and ei:"isint e (a#bs)" and d': "c dvd l" by simp+
    from lp cp have clel: "c\<le>l" by (simp add: zdvd_imp_le [OF d' lp])
    from cp have cnz: "c \<noteq> 0" by simp
    have "c div c\<le> l div c"
      by (simp add: zdiv_mono1[OF clel cp])
    then have ldcp:"0 < l div c"
      by (simp add: div_self[OF cnz])
    have "c * (l div c) = c* (l div c) + l mod c" using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
    hence cl:"c * (l div c) =l" using mult_div_mod_eq [where a="l" and b="c"]
      by simp
    hence "(real_of_int l * real_of_int x + real_of_int (l div c) * Inum (real_of_int x # bs) e > (0::real)) =
          (real_of_int (c * (l div c)) * real_of_int x + real_of_int (l div c) * Inum (real_of_int x # bs) e > 0)"
      by simp
    also have "\<dots> = (real_of_int (l div c) * (real_of_int c * real_of_int x + Inum (real_of_int x # bs) e) > (real_of_int (l div c)) * 0)" by (simp add: algebra_simps)
    also have "\<dots> = (real_of_int c * real_of_int x + Inum (real_of_int x # bs) e > 0)"
    using zero_less_mult_iff [where a="real_of_int (l div c)" and b="real_of_int c * real_of_int x + Inum (real_of_int x # bs) e"] ldcp by simp
  finally show ?case using numbound0_I[OF be,where b="real_of_int (l * x)" and b'="real_of_int x" and bs="bs"]  be  isint_Mul[OF ei] by simp
next
  case (8 c e) hence cp: "c>0" and be: "numbound0 e"  and ei:"isint e (a#bs)" and d': "c dvd l" by simp+
    from lp cp have clel: "c\<le>l" by (simp add: zdvd_imp_le [OF d' lp])
    from cp have cnz: "c \<noteq> 0" by simp
    have "c div c\<le> l div c"
      by (simp add: zdiv_mono1[OF clel cp])
    then have ldcp:"0 < l div c"
      by (simp add: div_self[OF cnz])
    have "c * (l div c) = c* (l div c) + l mod c" using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
    hence cl:"c * (l div c) =l" using mult_div_mod_eq [where a="l" and b="c"]
      by simp
    hence "(real_of_int l * real_of_int x + real_of_int (l div c) * Inum (real_of_int x # bs) e \<ge> (0::real)) =
          (real_of_int (c * (l div c)) * real_of_int x + real_of_int (l div c) * Inum (real_of_int x # bs) e \<ge> 0)"
      by simp
    also have "\<dots> = (real_of_int (l div c) * (real_of_int c * real_of_int x + Inum (real_of_int x # bs) e) \<ge> (real_of_int (l div c)) * 0)" by (simp add: algebra_simps)
    also have "\<dots> = (real_of_int c * real_of_int x + Inum (real_of_int x # bs) e \<ge> 0)"
    using zero_le_mult_iff [where a="real_of_int (l div c)" and b="real_of_int c * real_of_int x + Inum (real_of_int x # bs) e"] ldcp by simp
  finally show ?case using numbound0_I[OF be,where b="real_of_int (l * x)" and b'="real_of_int x" and bs="bs"]  be  isint_Mul[OF ei] by simp
next
  case (3 c e) hence cp: "c>0" and be: "numbound0 e" and ei:"isint e (a#bs)" and d': "c dvd l" by simp+
    from lp cp have clel: "c\<le>l" by (simp add: zdvd_imp_le [OF d' lp])
    from cp have cnz: "c \<noteq> 0" by simp
    have "c div c\<le> l div c"
      by (simp add: zdiv_mono1[OF clel cp])
    then have ldcp:"0 < l div c"
      by (simp add: div_self[OF cnz])
    have "c * (l div c) = c* (l div c) + l mod c" using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
    hence cl:"c * (l div c) =l" using mult_div_mod_eq [where a="l" and b="c"]
      by simp
    hence "(real_of_int l * real_of_int x + real_of_int (l div c) * Inum (real_of_int x # bs) e = (0::real)) =
          (real_of_int (c * (l div c)) * real_of_int x + real_of_int (l div c) * Inum (real_of_int x # bs) e = 0)"
      by simp
    also have "\<dots> = (real_of_int (l div c) * (real_of_int c * real_of_int x + Inum (real_of_int x # bs) e) = (real_of_int (l div c)) * 0)" by (simp add: algebra_simps)
    also have "\<dots> = (real_of_int c * real_of_int x + Inum (real_of_int x # bs) e = 0)"
    using mult_eq_0_iff [where a="real_of_int (l div c)" and b="real_of_int c * real_of_int x + Inum (real_of_int x # bs) e"] ldcp by simp
  finally show ?case using numbound0_I[OF be,where b="real_of_int (l * x)" and b'="real_of_int x" and bs="bs"]  be  isint_Mul[OF ei] by simp
next
  case (4 c e) hence cp: "c>0" and be: "numbound0 e" and ei:"isint e (a#bs)" and d': "c dvd l" by simp+
    from lp cp have clel: "c\<le>l" by (simp add: zdvd_imp_le [OF d' lp])
    from cp have cnz: "c \<noteq> 0" by simp
    have "c div c\<le> l div c"
      by (simp add: zdiv_mono1[OF clel cp])
    then have ldcp:"0 < l div c"
      by (simp add: div_self[OF cnz])
    have "c * (l div c) = c* (l div c) + l mod c" using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
    hence cl:"c * (l div c) =l" using mult_div_mod_eq [where a="l" and b="c"]
      by simp
    hence "(real_of_int l * real_of_int x + real_of_int (l div c) * Inum (real_of_int x # bs) e \<noteq> (0::real)) =
          (real_of_int (c * (l div c)) * real_of_int x + real_of_int (l div c) * Inum (real_of_int x # bs) e \<noteq> 0)"
      by simp
    also have "\<dots> = (real_of_int (l div c) * (real_of_int c * real_of_int x + Inum (real_of_int x # bs) e) \<noteq> (real_of_int (l div c)) * 0)" by (simp add: algebra_simps)
    also have "\<dots> = (real_of_int c * real_of_int x + Inum (real_of_int x # bs) e \<noteq> 0)"
    using zero_le_mult_iff [where a="real_of_int (l div c)" and b="real_of_int c * real_of_int x + Inum (real_of_int x # bs) e"] ldcp by simp
  finally show ?case using numbound0_I[OF be,where b="real_of_int (l * x)" and b'="real_of_int x" and bs="bs"]  be  isint_Mul[OF ei] by simp
next
  case (9 j c e) hence cp: "c>0" and be: "numbound0 e" and ei:"isint e (a#bs)" and jp: "j > 0" and d': "c dvd l" by simp+
    from lp cp have clel: "c\<le>l" by (simp add: zdvd_imp_le [OF d' lp])
    from cp have cnz: "c \<noteq> 0" by simp
    have "c div c\<le> l div c"
      by (simp add: zdiv_mono1[OF clel cp])
    then have ldcp:"0 < l div c"
      by (simp add: div_self[OF cnz])
    have "c * (l div c) = c* (l div c) + l mod c" using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
    hence cl:"c * (l div c) =l" using mult_div_mod_eq [where a="l" and b="c"]
      by simp
    hence "(\<exists> (k::int). real_of_int l * real_of_int x + real_of_int (l div c) * Inum (real_of_int x # bs) e = (real_of_int (l div c) * real_of_int j) * real_of_int k) = (\<exists> (k::int). real_of_int (c * (l div c)) * real_of_int x + real_of_int (l div c) * Inum (real_of_int x # bs) e = (real_of_int (l div c) * real_of_int j) * real_of_int k)"  by simp
    also have "\<dots> = (\<exists> (k::int). real_of_int (l div c) * (real_of_int c * real_of_int x + Inum (real_of_int x # bs) e - real_of_int j * real_of_int k) = real_of_int (l div c)*0)" by (simp add: algebra_simps)
    also fix k have "\<dots> = (\<exists> (k::int). real_of_int c * real_of_int x + Inum (real_of_int x # bs) e - real_of_int j * real_of_int k = 0)"
    using zero_le_mult_iff [where a="real_of_int (l div c)" and b="real_of_int c * real_of_int x + Inum (real_of_int x # bs) e - real_of_int j * real_of_int k"] ldcp by simp
  also have "\<dots> = (\<exists> (k::int). real_of_int c * real_of_int x + Inum (real_of_int x # bs) e = real_of_int j * real_of_int k)" by simp
  finally show ?case using numbound0_I[OF be,where b="real_of_int (l * x)" and b'="real_of_int x" and bs="bs"] rdvd_def  be  isint_Mul[OF ei] mult_strict_mono[OF ldcp jp ldcp ] by simp
next
  case (10 j c e) hence cp: "c>0" and be: "numbound0 e" and ei:"isint e (a#bs)" and jp: "j > 0" and d': "c dvd l" by simp+
    from lp cp have clel: "c\<le>l" by (simp add: zdvd_imp_le [OF d' lp])
    from cp have cnz: "c \<noteq> 0" by simp
    have "c div c\<le> l div c"
      by (simp add: zdiv_mono1[OF clel cp])
    then have ldcp:"0 < l div c"
      by (simp add: div_self[OF cnz])
    have "c * (l div c) = c* (l div c) + l mod c" using d' dvd_eq_mod_eq_0[of "c" "l"] by simp
    hence cl:"c * (l div c) =l" using mult_div_mod_eq [where a="l" and b="c"]
      by simp
    hence "(\<exists> (k::int). real_of_int l * real_of_int x + real_of_int (l div c) * Inum (real_of_int x # bs) e = (real_of_int (l div c) * real_of_int j) * real_of_int k) = (\<exists> (k::int). real_of_int (c * (l div c)) * real_of_int x + real_of_int (l div c) * Inum (real_of_int x # bs) e = (real_of_int (l div c) * real_of_int j) * real_of_int k)"  by simp
    also have "\<dots> = (\<exists> (k::int). real_of_int (l div c) * (real_of_int c * real_of_int x + Inum (real_of_int x # bs) e - real_of_int j * real_of_int k) = real_of_int (l div c)*0)" by (simp add: algebra_simps)
    also fix k have "\<dots> = (\<exists> (k::int). real_of_int c * real_of_int x + Inum (real_of_int x # bs) e - real_of_int j * real_of_int k = 0)"
    using zero_le_mult_iff [where a="real_of_int (l div c)" and b="real_of_int c * real_of_int x + Inum (real_of_int x # bs) e - real_of_int j * real_of_int k"] ldcp by simp
  also have "\<dots> = (\<exists> (k::int). real_of_int c * real_of_int x + Inum (real_of_int x # bs) e = real_of_int j * real_of_int k)" by simp
  finally show ?case using numbound0_I[OF be,where b="real_of_int (l * x)" and b'="real_of_int x" and bs="bs"] rdvd_def  be  isint_Mul[OF ei]  mult_strict_mono[OF ldcp jp ldcp ] by simp
qed (simp_all add: numbound0_I[where bs="bs" and b="real_of_int (l * x)" and b'="real_of_int x"] isint_Mul del: of_int_mult)

lemma a_\<beta>_ex: assumes linp: "iszlfm p (a#bs)" and d: "d_\<beta> p l" and lp: "l>0"
  shows "(\<exists> x. l dvd x \<and> Ifm (real_of_int x #bs) (a_\<beta> p l)) = (\<exists> (x::int). Ifm (real_of_int x#bs) p)"
  (is "(\<exists> x. l dvd x \<and> ?P x) = (\<exists> x. ?P' x)")
proof-
  have "(\<exists> x. l dvd x \<and> ?P x) = (\<exists> (x::int). ?P (l*x))"
    using unity_coeff_ex[where l="l" and P="?P", simplified] by simp
  also have "\<dots> = (\<exists> (x::int). ?P' x)" using a_\<beta>[OF linp d lp] by simp
  finally show ?thesis  .
qed

lemma \<beta>:
  assumes lp: "iszlfm p (a#bs)"
  and u: "d_\<beta> p 1"
  and d: "d_\<delta> p d"
  and dp: "d > 0"
  and nob: "\<not>(\<exists>(j::int) \<in> {1 .. d}. \<exists> b\<in> (Inum (a#bs)) ` set(\<beta> p). real_of_int x = b + real_of_int j)"
  and p: "Ifm (real_of_int x#bs) p" (is "?P x")
  shows "?P (x - d)"
using lp u d dp nob p
proof(induct p rule: iszlfm.induct)
  case (5 c e) hence c1: "c=1" and  bn:"numbound0 e" using dvd1_eq1[where x="c"] by simp_all
  with dp p c1 numbound0_I[OF bn,where b="real_of_int (x-d)" and b'="real_of_int x" and bs="bs"] 5
  show ?case by (simp del: of_int_minus)
next
  case (6 c e)  hence c1: "c=1" and  bn:"numbound0 e" using dvd1_eq1[where x="c"] by simp_all
  with dp p c1 numbound0_I[OF bn,where b="real_of_int (x-d)" and b'="real_of_int x" and bs="bs"] 6
  show ?case by (simp del: of_int_minus)
next
  case (7 c e) hence p: "Ifm (real_of_int x #bs) (Gt (CN 0 c e))" and c1: "c=1"
    and bn:"numbound0 e" and ie1:"isint e (a#bs)" using dvd1_eq1[where x="c"] by simp_all
  let ?e = "Inum (real_of_int x # bs) e"
  from ie1 have ie: "real_of_int \<lfloor>?e\<rfloor> = ?e" using isint_iff[where n="e" and bs="a#bs"]
      numbound0_I[OF bn,where b="a" and b'="real_of_int x" and bs="bs"]
    by (simp add: isint_iff)
    {assume "real_of_int (x-d) +?e > 0" hence ?case using c1
      numbound0_I[OF bn,where b="real_of_int (x-d)" and b'="real_of_int x" and bs="bs"]
        by (simp del: of_int_minus)}
    moreover
    {assume H: "\<not> real_of_int (x-d) + ?e > 0"
      let ?v="Neg e"
      have vb: "?v \<in> set (\<beta> (Gt (CN 0 c e)))" by simp
      from 7(5)[simplified simp_thms Inum.simps \<beta>.simps list.set bex_simps numbound0_I[OF bn,where b="a" and b'="real_of_int x" and bs="bs"]]
      have nob: "\<not> (\<exists> j\<in> {1 ..d}. real_of_int x =  - ?e + real_of_int j)" by auto
      from H p have "real_of_int x + ?e > 0 \<and> real_of_int x + ?e \<le> real_of_int d" by (simp add: c1)
      hence "real_of_int (x + \<lfloor>?e\<rfloor>) > real_of_int (0::int) \<and> real_of_int (x + \<lfloor>?e\<rfloor>) \<le> real_of_int d"
        using ie by simp
      hence "x + \<lfloor>?e\<rfloor> \<ge> 1 \<and> x + \<lfloor>?e\<rfloor> \<le> d"  by simp
      hence "\<exists> (j::int) \<in> {1 .. d}. j = x + \<lfloor>?e\<rfloor>" by simp
      hence "\<exists> (j::int) \<in> {1 .. d}. real_of_int x = real_of_int (- \<lfloor>?e\<rfloor> + j)" by force
      hence "\<exists> (j::int) \<in> {1 .. d}. real_of_int x = - ?e + real_of_int j"
        by (simp add: ie[simplified isint_iff])
      with nob have ?case by auto}
    ultimately show ?case by blast
next
  case (8 c e) hence p: "Ifm (real_of_int x #bs) (Ge (CN 0 c e))" and c1: "c=1" and bn:"numbound0 e"
    and ie1:"isint e (a #bs)" using dvd1_eq1[where x="c"] by simp+
    let ?e = "Inum (real_of_int x # bs) e"
    from ie1 have ie: "real_of_int \<lfloor>?e\<rfloor> = ?e" using numbound0_I[OF bn,where b="real_of_int x" and b'="a" and bs="bs"] isint_iff[where n="e" and bs="(real_of_int x)#bs"]
      by (simp add: isint_iff)
    {assume "real_of_int (x-d) +?e \<ge> 0" hence ?case using  c1
      numbound0_I[OF bn,where b="real_of_int (x-d)" and b'="real_of_int x" and bs="bs"]
        by (simp del: of_int_minus)}
    moreover
    {assume H: "\<not> real_of_int (x-d) + ?e \<ge> 0"
      let ?v="Sub (C (- 1)) e"
      have vb: "?v \<in> set (\<beta> (Ge (CN 0 c e)))" by simp
      from 8(5)[simplified simp_thms Inum.simps \<beta>.simps list.set bex_simps numbound0_I[OF bn,where b="a" and b'="real_of_int x" and bs="bs"]]
      have nob: "\<not> (\<exists> j\<in> {1 ..d}. real_of_int x =  - ?e - 1 + real_of_int j)" by auto
      from H p have "real_of_int x + ?e \<ge> 0 \<and> real_of_int x + ?e < real_of_int d" by (simp add: c1)
      hence "real_of_int (x + \<lfloor>?e\<rfloor>) \<ge> real_of_int (0::int) \<and> real_of_int (x + \<lfloor>?e\<rfloor>) < real_of_int d"
        using ie by simp
      hence "x + \<lfloor>?e\<rfloor> + 1 \<ge> 1 \<and> x + \<lfloor>?e\<rfloor> + 1 \<le> d" by simp
      hence "\<exists> (j::int) \<in> {1 .. d}. j = x + \<lfloor>?e\<rfloor> + 1" by simp
      hence "\<exists> (j::int) \<in> {1 .. d}. x= - \<lfloor>?e\<rfloor> - 1 + j" by (simp add: algebra_simps)
      hence "\<exists> (j::int) \<in> {1 .. d}. real_of_int x= real_of_int (- \<lfloor>?e\<rfloor> - 1 + j)" by presburger
      hence "\<exists> (j::int) \<in> {1 .. d}. real_of_int x= - ?e - 1 + real_of_int j"
        by (simp add: ie[simplified isint_iff])
      with nob have ?case by simp }
    ultimately show ?case by blast
next
  case (3 c e) hence p: "Ifm (real_of_int x #bs) (Eq (CN 0 c e))" (is "?p x") and c1: "c=1"
    and bn:"numbound0 e" and ie1: "isint e (a #bs)" using dvd1_eq1[where x="c"] by simp+
    let ?e = "Inum (real_of_int x # bs) e"
    let ?v="(Sub (C (- 1)) e)"
    have vb: "?v \<in> set (\<beta> (Eq (CN 0 c e)))" by simp
    from p have "real_of_int x= - ?e" by (simp add: c1) with 3(5) show ?case using dp
      by simp (erule ballE[where x="1"],
        simp_all add:algebra_simps numbound0_I[OF bn,where b="real_of_int x"and b'="a"and bs="bs"])
next
  case (4 c e)hence p: "Ifm (real_of_int x #bs) (NEq (CN 0 c e))" (is "?p x") and c1: "c=1"
    and bn:"numbound0 e" and ie1: "isint e (a #bs)" using dvd1_eq1[where x="c"] by simp+
    let ?e = "Inum (real_of_int x # bs) e"
    let ?v="Neg e"
    have vb: "?v \<in> set (\<beta> (NEq (CN 0 c e)))" by simp
    {assume "real_of_int x - real_of_int d + Inum ((real_of_int (x -d)) # bs) e \<noteq> 0"
      hence ?case by (simp add: c1)}
    moreover
    {assume H: "real_of_int x - real_of_int d + Inum ((real_of_int (x -d)) # bs) e = 0"
      hence "real_of_int x = - Inum ((real_of_int (x -d)) # bs) e + real_of_int d" by simp
      hence "real_of_int x = - Inum (a # bs) e + real_of_int d"
        by (simp add: numbound0_I[OF bn,where b="real_of_int x - real_of_int d"and b'="a"and bs="bs"])
       with 4(5) have ?case using dp by simp}
  ultimately show ?case by blast
next
  case (9 j c e) hence p: "Ifm (real_of_int x #bs) (Dvd j (CN 0 c e))" (is "?p x") and c1: "c=1"
    and bn:"numbound0 e" using dvd1_eq1[where x="c"] by simp+
  let ?e = "Inum (real_of_int x # bs) e"
  from 9 have "isint e (a #bs)"  by simp
  hence ie: "real_of_int \<lfloor>?e\<rfloor> = ?e" using isint_iff[where n="e" and bs="(real_of_int x)#bs"] numbound0_I[OF bn,where b="real_of_int x" and b'="a" and bs="bs"]
    by (simp add: isint_iff)
  from 9 have id: "j dvd d" by simp
  from c1 ie[symmetric] have "?p x = (real_of_int j rdvd real_of_int (x + \<lfloor>?e\<rfloor>))" by simp
  also have "\<dots> = (j dvd x + \<lfloor>?e\<rfloor>)"
    using int_rdvd_real[where i="j" and x="real_of_int (x + \<lfloor>?e\<rfloor>)"] by simp
  also have "\<dots> = (j dvd x - d + \<lfloor>?e\<rfloor>)"
    using dvd_period[OF id, where x="x" and c="-1" and t="\<lfloor>?e\<rfloor>"] by simp
  also have "\<dots> = (real_of_int j rdvd real_of_int (x - d + \<lfloor>?e\<rfloor>))"
    using int_rdvd_real[where i="j" and x="real_of_int (x - d + \<lfloor>?e\<rfloor>)",symmetric, simplified]
      ie by simp
  also have "\<dots> = (real_of_int j rdvd real_of_int x - real_of_int d + ?e)"
    using ie by simp
  finally show ?case
    using numbound0_I[OF bn,where b="real_of_int (x-d)" and b'="real_of_int x" and bs="bs"] c1 p by simp
next
  case (10 j c e) hence p: "Ifm (real_of_int x #bs) (NDvd j (CN 0 c e))" (is "?p x") and c1: "c=1" and bn:"numbound0 e" using dvd1_eq1[where x="c"] by simp+
  let ?e = "Inum (real_of_int x # bs) e"
  from 10 have "isint e (a#bs)"  by simp
  hence ie: "real_of_int \<lfloor>?e\<rfloor> = ?e" using numbound0_I[OF bn,where b="real_of_int x" and b'="a" and bs="bs"] isint_iff[where n="e" and bs="(real_of_int x)#bs"]
    by (simp add: isint_iff)
  from 10 have id: "j dvd d" by simp
  from c1 ie[symmetric] have "?p x = (\<not> real_of_int j rdvd real_of_int (x + \<lfloor>?e\<rfloor>))" by simp
  also have "\<dots> = (\<not> j dvd x + \<lfloor>?e\<rfloor>)"
    using int_rdvd_real[where i="j" and x="real_of_int (x + \<lfloor>?e\<rfloor>)"] by simp
  also have "\<dots> = (\<not> j dvd x - d + \<lfloor>?e\<rfloor>)"
    using dvd_period[OF id, where x="x" and c="-1" and t="\<lfloor>?e\<rfloor>"] by simp
  also have "\<dots> = (\<not> real_of_int j rdvd real_of_int (x - d + \<lfloor>?e\<rfloor>))"
    using int_rdvd_real[where i="j" and x="real_of_int (x - d + \<lfloor>?e\<rfloor>)",symmetric, simplified]
      ie by simp
  also have "\<dots> = (\<not> real_of_int j rdvd real_of_int x - real_of_int d + ?e)"
    using ie by simp
  finally show ?case
    using numbound0_I[OF bn,where b="real_of_int (x-d)" and b'="real_of_int x" and bs="bs"] c1 p by simp
qed (auto simp add: numbound0_I[where bs="bs" and b="real_of_int (x - d)" and b'="real_of_int x"]
  simp del: of_int_diff)

lemma \<beta>':
  assumes lp: "iszlfm p (a #bs)"
  and u: "d_\<beta> p 1"
  and d: "d_\<delta> p d"
  and dp: "d > 0"
  shows "\<forall> x. \<not>(\<exists>(j::int) \<in> {1 .. d}. \<exists> b\<in> set(\<beta> p). Ifm ((Inum (a#bs) b + real_of_int j) #bs) p) \<longrightarrow> Ifm (real_of_int x#bs) p \<longrightarrow> Ifm (real_of_int (x - d)#bs) p" (is "\<forall> x. ?b \<longrightarrow> ?P x \<longrightarrow> ?P (x - d)")
proof(clarify)
  fix x
  assume nb:"?b" and px: "?P x"
  hence nb2: "\<not>(\<exists>(j::int) \<in> {1 .. d}. \<exists> b\<in> (Inum (a#bs)) ` set(\<beta> p). real_of_int x = b + real_of_int j)"
    by auto
  from  \<beta>[OF lp u d dp nb2 px] show "?P (x -d )" .
qed

lemma \<beta>_int: assumes lp: "iszlfm p bs"
  shows "\<forall> b\<in> set (\<beta> p). isint b bs"
using lp by (induct p rule: iszlfm.induct) (auto simp add: isint_neg isint_sub)

lemma cpmi_eq: "0 < D \<Longrightarrow> (\<exists>z::int. \<forall>x. x < z \<longrightarrow> (P x = P1 x))
\<Longrightarrow> \<forall>x. \<not>(\<exists>(j::int) \<in> {1..D}. \<exists>(b::int) \<in> B. P(b+j)) \<longrightarrow> P (x) \<longrightarrow> P (x - D)
\<Longrightarrow> (\<forall>(x::int). \<forall>(k::int). ((P1 x)= (P1 (x-k*D))))
\<Longrightarrow> (\<exists>(x::int). P(x)) = ((\<exists>(j::int) \<in> {1..D} . (P1(j))) | (\<exists>(j::int) \<in> {1..D}. \<exists>(b::int) \<in> B. P (b+j)))"
apply(rule iffI)
prefer 2
apply(drule minusinfinity)
apply assumption+
apply(fastforce)
apply clarsimp
apply(subgoal_tac "\<And>k. 0<=k \<Longrightarrow> \<forall>x. P x \<longrightarrow> P (x - k*D)")
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
  and u: "d_\<beta> p 1"
  and d: "d_\<delta> p d"
  and dp: "d > 0"
  shows "(\<exists> (x::int). Ifm (real_of_int x #bs) p) = (\<exists> j\<in> {1.. d}. Ifm (real_of_int j #bs) (minusinf p) \<or> (\<exists> b \<in> set (\<beta> p). Ifm ((Inum (a#bs) b + real_of_int j) #bs) p))"
  (is "(\<exists> (x::int). ?P (real_of_int x)) = (\<exists> j\<in> ?D. ?M j \<or> (\<exists> b\<in> ?B. ?P (?I b + real_of_int j)))")
proof-
  from minusinf_inf[OF lp]
  have th: "\<exists>(z::int). \<forall>x<z. ?P (real_of_int x) = ?M x" by blast
  let ?B' = "{\<lfloor>?I b\<rfloor> | b. b\<in> ?B}"
  from \<beta>_int[OF lp] isint_iff[where bs="a # bs"] have B: "\<forall> b\<in> ?B. real_of_int \<lfloor>?I b\<rfloor> = ?I b" by simp
  from B[rule_format]
  have "(\<exists>j\<in>?D. \<exists>b\<in> ?B. ?P (?I b + real_of_int j)) = (\<exists>j\<in>?D. \<exists>b\<in> ?B. ?P (real_of_int \<lfloor>?I b\<rfloor> + real_of_int j))"
    by simp
  also have "\<dots> = (\<exists>j\<in>?D. \<exists>b\<in> ?B. ?P (real_of_int (\<lfloor>?I b\<rfloor> + j)))" by simp
  also have"\<dots> = (\<exists> j \<in> ?D. \<exists> b \<in> ?B'. ?P (real_of_int (b + j)))"  by blast
  finally have BB':
    "(\<exists>j\<in>?D. \<exists>b\<in> ?B. ?P (?I b + real_of_int j)) = (\<exists> j \<in> ?D. \<exists> b \<in> ?B'. ?P (real_of_int (b + j)))"
    by blast
  hence th2: "\<forall> x. \<not> (\<exists> j \<in> ?D. \<exists> b \<in> ?B'. ?P (real_of_int (b + j))) \<longrightarrow> ?P (real_of_int x) \<longrightarrow> ?P (real_of_int (x - d))" using \<beta>'[OF lp u d dp] by blast
  from minusinf_repeats[OF d lp]
  have th3: "\<forall> x k. ?M x = ?M (x-k*d)" by simp
  from cpmi_eq[OF dp th th2 th3] BB' show ?thesis by blast
qed

    (* Reddy and Loveland *)


fun \<rho> :: "fm \<Rightarrow> (num \<times> int) list" (* Compute the Reddy and Loveland Bset*)
  where
  "\<rho> (And p q) = (\<rho> p @ \<rho> q)"
| "\<rho> (Or p q) = (\<rho> p @ \<rho> q)"
| "\<rho> (Eq  (CN 0 c e)) = [(Sub (C (- 1)) e,c)]"
| "\<rho> (NEq (CN 0 c e)) = [(Neg e,c)]"
| "\<rho> (Lt  (CN 0 c e)) = []"
| "\<rho> (Le  (CN 0 c e)) = []"
| "\<rho> (Gt  (CN 0 c e)) = [(Neg e, c)]"
| "\<rho> (Ge  (CN 0 c e)) = [(Sub (C (-1)) e, c)]"
| "\<rho> p = []"

fun \<sigma>_\<rho>:: "fm \<Rightarrow> num \<times> int \<Rightarrow> fm" (* Performs the modified substitution of Reddy and Loveland*)
where
  "\<sigma>_\<rho> (And p q) = (\<lambda> (t,k). And (\<sigma>_\<rho> p (t,k)) (\<sigma>_\<rho> q (t,k)))"
| "\<sigma>_\<rho> (Or p q) = (\<lambda> (t,k). Or (\<sigma>_\<rho> p (t,k)) (\<sigma>_\<rho> q (t,k)))"
| "\<sigma>_\<rho> (Eq  (CN 0 c e)) = (\<lambda> (t,k). if k dvd c then (Eq (Add (Mul (c div k) t) e))
                                            else (Eq (Add (Mul c t) (Mul k e))))"
| "\<sigma>_\<rho> (NEq (CN 0 c e)) = (\<lambda> (t,k). if k dvd c then (NEq (Add (Mul (c div k) t) e))
                                            else (NEq (Add (Mul c t) (Mul k e))))"
| "\<sigma>_\<rho> (Lt  (CN 0 c e)) = (\<lambda> (t,k). if k dvd c then (Lt (Add (Mul (c div k) t) e))
                                            else (Lt (Add (Mul c t) (Mul k e))))"
| "\<sigma>_\<rho> (Le  (CN 0 c e)) = (\<lambda> (t,k). if k dvd c then (Le (Add (Mul (c div k) t) e))
                                            else (Le (Add (Mul c t) (Mul k e))))"
| "\<sigma>_\<rho> (Gt  (CN 0 c e)) = (\<lambda> (t,k). if k dvd c then (Gt (Add (Mul (c div k) t) e))
                                            else (Gt (Add (Mul c t) (Mul k e))))"
| "\<sigma>_\<rho> (Ge  (CN 0 c e)) = (\<lambda> (t,k). if k dvd c then (Ge (Add (Mul (c div k) t) e))
                                            else (Ge (Add (Mul c t) (Mul k e))))"
| "\<sigma>_\<rho> (Dvd i (CN 0 c e)) =(\<lambda> (t,k). if k dvd c then (Dvd i (Add (Mul (c div k) t) e))
                                            else (Dvd (i*k) (Add (Mul c t) (Mul k e))))"
| "\<sigma>_\<rho> (NDvd i (CN 0 c e))=(\<lambda> (t,k). if k dvd c then (NDvd i (Add (Mul (c div k) t) e))
                                            else (NDvd (i*k) (Add (Mul c t) (Mul k e))))"
| "\<sigma>_\<rho> p = (\<lambda> (t,k). p)"

fun \<alpha>_\<rho> :: "fm \<Rightarrow> (num \<times> int) list"
where
  "\<alpha>_\<rho> (And p q) = (\<alpha>_\<rho> p @ \<alpha>_\<rho> q)"
| "\<alpha>_\<rho> (Or p q) = (\<alpha>_\<rho> p @ \<alpha>_\<rho> q)"
| "\<alpha>_\<rho> (Eq  (CN 0 c e)) = [(Add (C (- 1)) e,c)]"
| "\<alpha>_\<rho> (NEq (CN 0 c e)) = [(e,c)]"
| "\<alpha>_\<rho> (Lt  (CN 0 c e)) = [(e,c)]"
| "\<alpha>_\<rho> (Le  (CN 0 c e)) = [(Add (C (- 1)) e,c)]"
| "\<alpha>_\<rho> p = []"

    (* Simulates normal substituion by modifying the formula see correctness theorem *)

definition \<sigma> :: "fm \<Rightarrow> int \<Rightarrow> num \<Rightarrow> fm" where
  "\<sigma> p k t \<equiv> And (Dvd k t) (\<sigma>_\<rho> p (t,k))"

lemma \<sigma>_\<rho>:
  assumes linp: "iszlfm p (real_of_int (x::int)#bs)"
  and kpos: "real_of_int k > 0"
  and tnb: "numbound0 t"
  and tint: "isint t (real_of_int x#bs)"
  and kdt: "k dvd \<lfloor>Inum (b'#bs) t\<rfloor>"
  shows "Ifm (real_of_int x#bs) (\<sigma>_\<rho> p (t,k)) = (Ifm ((real_of_int (\<lfloor>Inum (b'#bs) t\<rfloor> div k))#bs) p)"
  (is "?I (real_of_int x) (?s p) = (?I (real_of_int (\<lfloor>?N b' t\<rfloor> div k)) p)" is "_ = (?I ?tk p)")
using linp kpos tnb
proof(induct p rule: \<sigma>_\<rho>.induct)
  case (3 c e)
  from 3 have cp: "c > 0" and nb: "numbound0 e" by auto
  { assume kdc: "k dvd c"
    from tint have ti: "real_of_int \<lfloor>?N (real_of_int x) t\<rfloor> = ?N (real_of_int x) t" using isint_def by simp
    from kdc have ?case using real_of_int_div[OF kdc] real_of_int_div[OF kdt]
      numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
      numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"] by (simp add: ti) }
  moreover
  { assume *: "\<not> k dvd c"
    from kpos have knz': "real_of_int k \<noteq> 0" by simp
    from tint have ti: "real_of_int \<lfloor>?N (real_of_int x) t\<rfloor> = ?N (real_of_int x) t"
      using isint_def by simp
    from assms * have "?I (real_of_int x) (?s (Eq (CN 0 c e))) = ((real_of_int c * (?N (real_of_int x) t / real_of_int k) + ?N (real_of_int x) e)* real_of_int k = 0)"
      using real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"]
      by (simp add: ti algebra_simps)
      also have "\<dots> = (?I ?tk (Eq (CN 0 c e)))"
        using nonzero_eq_divide_eq[OF knz',
            where a="real_of_int c * (?N (real_of_int x) t / real_of_int k) + ?N (real_of_int x) e" and b="0", symmetric]
          real_of_int_div[OF kdt] numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
          numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"]
        by (simp add: ti)
      finally have ?case . }
    ultimately show ?case by blast
next
  case (4 c e)
  then have cp: "c > 0" and nb: "numbound0 e" by auto
  { assume kdc: "k dvd c"
    from tint have ti: "real_of_int \<lfloor>?N (real_of_int x) t\<rfloor> = ?N (real_of_int x) t" using isint_def by simp
    from kdc have  ?case using real_of_int_div[OF kdc] real_of_int_div[OF kdt]
      numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
      numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"] by (simp add: ti) }
  moreover
  { assume *: "\<not> k dvd c"
    from kpos have knz': "real_of_int k \<noteq> 0" by simp
    from tint have ti: "real_of_int \<lfloor>?N (real_of_int x) t\<rfloor> = ?N (real_of_int x) t" using isint_def by simp
    from assms * have "?I (real_of_int x) (?s (NEq (CN 0 c e))) = ((real_of_int c * (?N (real_of_int x) t / real_of_int k) + ?N (real_of_int x) e)* real_of_int k \<noteq> 0)"
      using real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"]
      by (simp add: ti algebra_simps)
    also have "\<dots> = (?I ?tk (NEq (CN 0 c e)))"
      using nonzero_eq_divide_eq[OF knz',
          where a="real_of_int c * (?N (real_of_int x) t / real_of_int k) + ?N (real_of_int x) e" and b="0", symmetric]
        real_of_int_div[OF kdt] numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"]
      by (simp add: ti)
    finally have ?case . }
  ultimately show ?case by blast
next
  case (5 c e)
  then have cp: "c > 0" and nb: "numbound0 e" by auto
  { assume kdc: "k dvd c"
    from tint have ti: "real_of_int \<lfloor>?N (real_of_int x) t\<rfloor> = ?N (real_of_int x) t" using isint_def by simp
    from kdc have  ?case using real_of_int_div[OF kdc] real_of_int_div[OF kdt]
      numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
      numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"] by (simp add: ti) }
  moreover
  { assume *: "\<not> k dvd c"
    from tint have ti: "real_of_int \<lfloor>?N (real_of_int x) t\<rfloor> = ?N (real_of_int x) t" using isint_def by simp
    from assms * have "?I (real_of_int x) (?s (Lt (CN 0 c e))) = ((real_of_int c * (?N (real_of_int x) t / real_of_int k) + ?N (real_of_int x) e)* real_of_int k < 0)"
      using real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"]
      by (simp add: ti algebra_simps)
    also have "\<dots> = (?I ?tk (Lt (CN 0 c e)))"
      using pos_less_divide_eq[OF kpos,
          where a="real_of_int c * (?N (real_of_int x) t / real_of_int k) + ?N (real_of_int x) e" and b="0", symmetric]
        real_of_int_div[OF kdt] numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"]
      by (simp add: ti)
    finally have ?case . }
  ultimately show ?case by blast
next
  case (6 c e)
  then have cp: "c > 0" and nb: "numbound0 e" by auto
  { assume kdc: "k dvd c"
    from tint have ti: "real_of_int \<lfloor>?N (real_of_int x) t\<rfloor> = ?N (real_of_int x) t" using isint_def by simp
    from kdc have  ?case using real_of_int_div[OF kdc] real_of_int_div[OF kdt]
      numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
      numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"] by (simp add: ti) }
  moreover
  { assume *: "\<not> k dvd c"
    from tint have ti: "real_of_int \<lfloor>?N (real_of_int x) t\<rfloor> = ?N (real_of_int x) t" using isint_def by simp
    from assms * have "?I (real_of_int x) (?s (Le (CN 0 c e))) = ((real_of_int c * (?N (real_of_int x) t / real_of_int k) + ?N (real_of_int x) e)* real_of_int k \<le> 0)"
      using real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"]
      by (simp add: ti algebra_simps)
    also have "\<dots> = (?I ?tk (Le (CN 0 c e)))"
      using pos_le_divide_eq[OF kpos,
          where a="real_of_int c * (?N (real_of_int x) t / real_of_int k) + ?N (real_of_int x) e" and b="0", symmetric]
        real_of_int_div[OF kdt] numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"]
      by (simp add: ti)
    finally have ?case . }
  ultimately show ?case by blast
next
  case (7 c e)
  then have cp: "c > 0" and nb: "numbound0 e" by auto
  { assume kdc: "k dvd c"
    from tint have ti: "real_of_int \<lfloor>?N (real_of_int x) t\<rfloor> = ?N (real_of_int x) t" using isint_def by simp
    from kdc have  ?case using real_of_int_div[OF kdc] real_of_int_div[OF kdt]
      numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
      numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"] by (simp add: ti) }
  moreover
  { assume *: "\<not> k dvd c"
    from tint have ti: "real_of_int \<lfloor>?N (real_of_int x) t\<rfloor> = ?N (real_of_int x) t" using isint_def by simp
    from assms * have "?I (real_of_int x) (?s (Gt (CN 0 c e))) = ((real_of_int c * (?N (real_of_int x) t / real_of_int k) + ?N (real_of_int x) e)* real_of_int k > 0)"
      using real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"]
      by (simp add: ti algebra_simps)
    also have "\<dots> = (?I ?tk (Gt (CN 0 c e)))"
      using pos_divide_less_eq[OF kpos,
          where a="real_of_int c * (?N (real_of_int x) t / real_of_int k) + ?N (real_of_int x) e" and b="0", symmetric]
        real_of_int_div[OF kdt] numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"]
      by (simp add: ti)
    finally have ?case . }
  ultimately show ?case by blast
next
  case (8 c e)
  then have cp: "c > 0" and nb: "numbound0 e" by auto
  { assume kdc: "k dvd c"
    from tint have ti: "real_of_int \<lfloor>?N (real_of_int x) t\<rfloor> = ?N (real_of_int x) t" using isint_def by simp
    from kdc have  ?case using real_of_int_div[OF kdc] real_of_int_div[OF kdt]
      numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
      numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"] by (simp add: ti) }
  moreover
  { assume *: "\<not> k dvd c"
    from tint have ti: "real_of_int \<lfloor>?N (real_of_int x) t\<rfloor> = ?N (real_of_int x) t" using isint_def by simp
    from assms * have "?I (real_of_int x) (?s (Ge (CN 0 c e))) = ((real_of_int c * (?N (real_of_int x) t / real_of_int k) + ?N (real_of_int x) e)* real_of_int k \<ge> 0)"
      using real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"]
      by (simp add: ti algebra_simps)
    also have "\<dots> = (?I ?tk (Ge (CN 0 c e)))"
      using pos_divide_le_eq[OF kpos,
          where a="real_of_int c * (?N (real_of_int x) t / real_of_int k) + ?N (real_of_int x) e" and b="0", symmetric]
        real_of_int_div[OF kdt] numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"]
      by (simp add: ti)
    finally have ?case . }
  ultimately show ?case by blast
next
  case (9 i c e)
  then have cp: "c > 0" and nb: "numbound0 e" by auto
  { assume kdc: "k dvd c"
    from tint have ti: "real_of_int \<lfloor>?N (real_of_int x) t\<rfloor> = ?N (real_of_int x) t" using isint_def by simp
    from kdc have ?case using real_of_int_div[OF kdc] real_of_int_div[OF kdt]
      numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
      numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"] by (simp add: ti) }
  moreover
  { assume *: "\<not> k dvd c"
    from kpos have knz: "k\<noteq>0" by simp hence knz': "real_of_int k \<noteq> 0" by simp
    from tint have ti: "real_of_int \<lfloor>?N (real_of_int x) t\<rfloor> = ?N (real_of_int x) t" using isint_def by simp
    from assms * have "?I (real_of_int x) (?s (Dvd i (CN 0 c e))) = (real_of_int i * real_of_int k rdvd (real_of_int c * (?N (real_of_int x) t / real_of_int k) + ?N (real_of_int x) e)* real_of_int k)"
      using real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"]
      by (simp add: ti algebra_simps)
    also have "\<dots> = (?I ?tk (Dvd i (CN 0 c e)))"
      using rdvd_mult[OF knz, where n="i"]
        real_of_int_div[OF kdt] numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"]
      by (simp add: ti)
    finally have ?case . }
  ultimately show ?case by blast
next
  case (10 i c e)
  then have cp: "c > 0" and nb: "numbound0 e" by auto
  { assume kdc: "k dvd c"
    from tint have ti: "real_of_int \<lfloor>?N (real_of_int x) t\<rfloor> = ?N (real_of_int x) t" using isint_def by simp
    from kdc have  ?case using real_of_int_div[OF kdc] real_of_int_div[OF kdt]
      numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
      numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"] by (simp add: ti) }
  moreover
  { assume *: "\<not> k dvd c"
    from kpos have knz: "k\<noteq>0" by simp hence knz': "real_of_int k \<noteq> 0" by simp
    from tint have ti: "real_of_int \<lfloor>?N (real_of_int x) t\<rfloor> = ?N (real_of_int x) t" using isint_def by simp
    from assms * have "?I (real_of_int x) (?s (NDvd i (CN 0 c e))) = (\<not> (real_of_int i * real_of_int k rdvd (real_of_int c * (?N (real_of_int x) t / real_of_int k) + ?N (real_of_int x) e)* real_of_int k))"
      using real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"]
      by (simp add: ti algebra_simps)
    also have "\<dots> = (?I ?tk (NDvd i (CN 0 c e)))"
      using rdvd_mult[OF knz, where n="i"] real_of_int_div[OF kdt]
        numbound0_I[OF tnb, where bs="bs" and b="b'" and b'="real_of_int x"]
        numbound0_I[OF nb, where bs="bs" and b="?tk" and b'="real_of_int x"]
      by (simp add: ti)
    finally have ?case . }
  ultimately show ?case by blast
qed (simp_all add: bound0_I[where bs="bs" and b="real_of_int (\<lfloor>?N b' t\<rfloor> div k)" and b'="real_of_int x"]
  numbound0_I[where bs="bs" and b="real_of_int (\<lfloor>?N b' t\<rfloor> div k)" and b'="real_of_int x"])


lemma \<sigma>_\<rho>_nb: assumes lp:"iszlfm p (a#bs)" and nb: "numbound0 t"
  shows "bound0 (\<sigma>_\<rho> p (t,k))"
  using lp
  by (induct p rule: iszlfm.induct, auto simp add: nb)

lemma \<rho>_l:
  assumes lp: "iszlfm p (real_of_int (i::int)#bs)"
  shows "\<forall> (b,k) \<in> set (\<rho> p). k >0 \<and> numbound0 b \<and> isint b (real_of_int i#bs)"
using lp by (induct p rule: \<rho>.induct, auto simp add: isint_sub isint_neg)

lemma \<alpha>_\<rho>_l:
  assumes lp: "iszlfm p (real_of_int (i::int)#bs)"
  shows "\<forall> (b,k) \<in> set (\<alpha>_\<rho> p). k >0 \<and> numbound0 b \<and> isint b (real_of_int i#bs)"
using lp isint_add [OF isint_c[where j="- 1"],where bs="real_of_int i#bs"]
 by (induct p rule: \<alpha>_\<rho>.induct, auto)

lemma \<rho>: assumes lp: "iszlfm p (real_of_int (i::int) #bs)"
  and pi: "Ifm (real_of_int i#bs) p"
  and d: "d_\<delta> p d"
  and dp: "d > 0"
  and nob: "\<forall>(e,c) \<in> set (\<rho> p). \<forall> j\<in> {1 .. c*d}. real_of_int (c*i) \<noteq> Inum (real_of_int i#bs) e + real_of_int j"
  (is "\<forall>(e,c) \<in> set (\<rho> p). \<forall> j\<in> {1 .. c*d}. _ \<noteq> ?N i e + _")
  shows "Ifm (real_of_int(i - d)#bs) p"
  using lp pi d nob
proof(induct p rule: iszlfm.induct)
  case (3 c e) hence cp: "c >0" and nb: "numbound0 e" and ei: "isint e (real_of_int i#bs)"
    and pi: "real_of_int (c*i) = - 1 -  ?N i e + real_of_int (1::int)" and nob: "\<forall> j\<in> {1 .. c*d}. real_of_int (c*i) \<noteq> -1 - ?N i e + real_of_int j"
    by simp+
  from mult_strict_left_mono[OF dp cp]  have one:"1 \<in> {1 .. c*d}" by auto
  from nob[rule_format, where j="1", OF one] pi show ?case by simp
next
  case (4 c e)
  hence cp: "c >0" and nb: "numbound0 e" and ei: "isint e (real_of_int i#bs)"
    and nob: "\<forall> j\<in> {1 .. c*d}. real_of_int (c*i) \<noteq> - ?N i e + real_of_int j"
    by simp+
  {assume "real_of_int (c*i) \<noteq> - ?N i e + real_of_int (c*d)"
    with numbound0_I[OF nb, where bs="bs" and b="real_of_int i - real_of_int d" and b'="real_of_int i"]
    have ?case by (simp add: algebra_simps)}
  moreover
  {assume pi: "real_of_int (c*i) = - ?N i e + real_of_int (c*d)"
    from mult_strict_left_mono[OF dp cp] have d: "(c*d) \<in> {1 .. c*d}" by simp
    from nob[rule_format, where j="c*d", OF d] pi have ?case by simp }
  ultimately show ?case by blast
next
  case (5 c e) hence cp: "c > 0" by simp
  from 5 mult_strict_left_mono[OF dp cp, simplified of_int_less_iff[symmetric]
    of_int_mult]
  show ?case using 5 dp
    apply (simp add: numbound0_I[where bs="bs" and b="real_of_int i - real_of_int d" and b'="real_of_int i"]
      algebra_simps del: mult_pos_pos)
     by (metis add.right_neutral of_int_0_less_iff of_int_mult pos_add_strict)
next
  case (6 c e) hence cp: "c > 0" by simp
  from 6 mult_strict_left_mono[OF dp cp, simplified of_int_less_iff[symmetric]
    of_int_mult]
  show ?case using 6 dp
    apply (simp add: numbound0_I[where bs="bs" and b="real_of_int i - real_of_int d" and b'="real_of_int i"]
      algebra_simps del: mult_pos_pos)
      using order_trans by fastforce
next
  case (7 c e) hence cp: "c >0" and nb: "numbound0 e" and ei: "isint e (real_of_int i#bs)"
    and nob: "\<forall> j\<in> {1 .. c*d}. real_of_int (c*i) \<noteq> - ?N i e + real_of_int j"
    and pi: "real_of_int (c*i) + ?N i e > 0" and cp': "real_of_int c >0"
    by simp+
  let ?fe = "\<lfloor>?N i e\<rfloor>"
  from pi cp have th:"(real_of_int i +?N i e / real_of_int c)*real_of_int c > 0" by (simp add: algebra_simps)
  from pi ei[simplified isint_iff] have "real_of_int (c*i + ?fe) > real_of_int (0::int)" by simp
  hence pi': "c*i + ?fe > 0" by (simp only: of_int_less_iff[symmetric])
  have "real_of_int (c*i) + ?N i e > real_of_int (c*d) \<or> real_of_int (c*i) + ?N i e \<le> real_of_int (c*d)" by auto
  moreover
  {assume "real_of_int (c*i) + ?N i e > real_of_int (c*d)" hence ?case
      by (simp add: algebra_simps
        numbound0_I[OF nb,where bs="bs" and b="real_of_int i - real_of_int d" and b'="real_of_int i"])}
  moreover
  {assume H:"real_of_int (c*i) + ?N i e \<le> real_of_int (c*d)"
    with ei[simplified isint_iff] have "real_of_int (c*i + ?fe) \<le> real_of_int (c*d)" by simp
    hence pid: "c*i + ?fe \<le> c*d" by (simp only: of_int_le_iff)
    with pi' have "\<exists> j1\<in> {1 .. c*d}. c*i + ?fe = j1" by auto
    hence "\<exists> j1\<in> {1 .. c*d}. real_of_int (c*i) = - ?N i e + real_of_int j1"
      unfolding Bex_def using ei[simplified isint_iff] by fastforce
    with nob  have ?case by blast }
  ultimately show ?case by blast
next
  case (8 c e)  hence cp: "c >0" and nb: "numbound0 e" and ei: "isint e (real_of_int i#bs)"
    and nob: "\<forall> j\<in> {1 .. c*d}. real_of_int (c*i) \<noteq> - 1 - ?N i e + real_of_int j"
    and pi: "real_of_int (c*i) + ?N i e \<ge> 0" and cp': "real_of_int c >0"
    by simp+
  let ?fe = "\<lfloor>?N i e\<rfloor>"
  from pi cp have th:"(real_of_int i +?N i e / real_of_int c)*real_of_int c \<ge> 0" by (simp add: algebra_simps)
  from pi ei[simplified isint_iff] have "real_of_int (c*i + ?fe) \<ge> real_of_int (0::int)" by simp
  hence pi': "c*i + 1 + ?fe \<ge> 1" by (simp only: of_int_le_iff[symmetric])
  have "real_of_int (c*i) + ?N i e \<ge> real_of_int (c*d) \<or> real_of_int (c*i) + ?N i e < real_of_int (c*d)" by auto
  moreover
  {assume "real_of_int (c*i) + ?N i e \<ge> real_of_int (c*d)" hence ?case
      by (simp add: algebra_simps
        numbound0_I[OF nb,where bs="bs" and b="real_of_int i - real_of_int d" and b'="real_of_int i"])}
  moreover
  {assume H:"real_of_int (c*i) + ?N i e < real_of_int (c*d)"
    with ei[simplified isint_iff] have "real_of_int (c*i + ?fe) < real_of_int (c*d)" by simp
    hence pid: "c*i + 1 + ?fe \<le> c*d" by (simp only: of_int_le_iff)
    with pi' have "\<exists> j1\<in> {1 .. c*d}. c*i + 1+ ?fe = j1" by auto
    hence "\<exists> j1\<in> {1 .. c*d}. real_of_int (c*i) + 1= - ?N i e + real_of_int j1"
      unfolding Bex_def using ei[simplified isint_iff] by fastforce
    hence "\<exists> j1\<in> {1 .. c*d}. real_of_int (c*i) = (- ?N i e + real_of_int j1) - 1"
      by (simp only: algebra_simps)
        hence "\<exists> j1\<in> {1 .. c*d}. real_of_int (c*i) = - 1 - ?N i e + real_of_int j1"
          by (simp add: algebra_simps)
    with nob  have ?case by blast }
  ultimately show ?case by blast
next
  case (9 j c e)  hence p: "real_of_int j rdvd real_of_int (c*i) + ?N i e" (is "?p x") and cp: "c > 0" and bn:"numbound0 e"  by simp+
  let ?e = "Inum (real_of_int i # bs) e"
  from 9 have "isint e (real_of_int i #bs)"  by simp
  hence ie: "real_of_int \<lfloor>?e\<rfloor> = ?e" using isint_iff[where n="e" and bs="(real_of_int i)#bs"] numbound0_I[OF bn,where b="real_of_int i" and b'="real_of_int i" and bs="bs"]
    by (simp add: isint_iff)
  from 9 have id: "j dvd d" by simp
  from ie[symmetric] have "?p i = (real_of_int j rdvd real_of_int (c*i + \<lfloor>?e\<rfloor>))" by simp
  also have "\<dots> = (j dvd c*i + \<lfloor>?e\<rfloor>)"
    using int_rdvd_iff [where i="j" and t="c*i + \<lfloor>?e\<rfloor>"] by simp
  also have "\<dots> = (j dvd c*i - c*d + \<lfloor>?e\<rfloor>)"
    using dvd_period[OF id, where x="c*i" and c="-c" and t="\<lfloor>?e\<rfloor>"] by simp
  also have "\<dots> = (real_of_int j rdvd real_of_int (c*i - c*d + \<lfloor>?e\<rfloor>))"
    using int_rdvd_iff[where i="j" and t="(c*i - c*d + \<lfloor>?e\<rfloor>)",symmetric, simplified]
      ie by simp
  also have "\<dots> = (real_of_int j rdvd real_of_int (c*(i - d)) + ?e)"
    using ie by (simp add:algebra_simps)
  finally show ?case
    using numbound0_I[OF bn,where b="real_of_int i - real_of_int d" and b'="real_of_int i" and bs="bs"] p
    by (simp add: algebra_simps)
next
  case (10 j c e)
  hence p: "\<not> (real_of_int j rdvd real_of_int (c*i) + ?N i e)" (is "?p x") and cp: "c > 0" and bn:"numbound0 e"
    by simp+
  let ?e = "Inum (real_of_int i # bs) e"
  from 10 have "isint e (real_of_int i #bs)"  by simp
  hence ie: "real_of_int \<lfloor>?e\<rfloor> = ?e"
    using isint_iff[where n="e" and bs="(real_of_int i)#bs"] numbound0_I[OF bn,where b="real_of_int i" and b'="real_of_int i" and bs="bs"]
    by (simp add: isint_iff)
  from 10 have id: "j dvd d" by simp
  from ie[symmetric] have "?p i = (\<not> (real_of_int j rdvd real_of_int (c*i + \<lfloor>?e\<rfloor>)))" by simp
  also have "\<dots> \<longleftrightarrow> \<not> (j dvd c*i + \<lfloor>?e\<rfloor>)"
    using int_rdvd_iff [where i="j" and t="c*i + \<lfloor>?e\<rfloor>"] by simp
  also have "\<dots> \<longleftrightarrow> \<not> (j dvd c*i - c*d + \<lfloor>?e\<rfloor>)"
    using dvd_period[OF id, where x="c*i" and c="-c" and t="\<lfloor>?e\<rfloor>"] by simp
  also have "\<dots> \<longleftrightarrow> \<not> (real_of_int j rdvd real_of_int (c*i - c*d + \<lfloor>?e\<rfloor>))"
    using int_rdvd_iff[where i="j" and t="(c*i - c*d + \<lfloor>?e\<rfloor>)",symmetric, simplified]
      ie by simp
  also have "\<dots> \<longleftrightarrow> \<not> (real_of_int j rdvd real_of_int (c*(i - d)) + ?e)"
    using ie by (simp add:algebra_simps)
  finally show ?case
    using numbound0_I[OF bn,where b="real_of_int i - real_of_int d" and b'="real_of_int i" and bs="bs"] p
    by (simp add: algebra_simps)
qed (auto simp add: numbound0_I[where bs="bs" and b="real_of_int i - real_of_int d" and b'="real_of_int i"])

lemma \<sigma>_nb: assumes lp: "iszlfm p (a#bs)" and nb: "numbound0 t"
  shows "bound0 (\<sigma> p k t)"
  using \<sigma>_\<rho>_nb[OF lp nb] nb by (simp add: \<sigma>_def)

lemma \<rho>':   assumes lp: "iszlfm p (a #bs)"
  and d: "d_\<delta> p d"
  and dp: "d > 0"
  shows "\<forall> x. \<not>(\<exists> (e,c) \<in> set(\<rho> p). \<exists>(j::int) \<in> {1 .. c*d}. Ifm (a #bs) (\<sigma> p c (Add e (C j)))) \<longrightarrow> Ifm (real_of_int x#bs) p \<longrightarrow> Ifm (real_of_int (x - d)#bs) p" (is "\<forall> x. ?b x \<longrightarrow> ?P x \<longrightarrow> ?P (x - d)")
proof(clarify)
  fix x
  assume nob1:"?b x" and px: "?P x"
  from iszlfm_gen[OF lp, rule_format, where y="real_of_int x"] have lp': "iszlfm p (real_of_int x#bs)".
  have nob: "\<forall>(e, c)\<in>set (\<rho> p). \<forall>j\<in>{1..c * d}. real_of_int (c * x) \<noteq> Inum (real_of_int x # bs) e + real_of_int j"
  proof(clarify)
    fix e c j assume ecR: "(e,c) \<in> set (\<rho> p)" and jD: "j\<in> {1 .. c*d}"
      and cx: "real_of_int (c*x) = Inum (real_of_int x#bs) e + real_of_int j"
    let ?e = "Inum (real_of_int x#bs) e"
    from \<rho>_l[OF lp'] ecR have ei:"isint e (real_of_int x#bs)" and cp:"c>0" and nb:"numbound0 e"
      by auto
    from numbound0_gen [OF nb ei, rule_format,where y="a"] have "isint e (a#bs)" .
    from cx ei[simplified isint_iff] have "real_of_int (c*x) = real_of_int (\<lfloor>?e\<rfloor> + j)" by simp
    hence cx: "c*x = \<lfloor>?e\<rfloor> + j" by (simp only: of_int_eq_iff)
    hence cdej:"c dvd \<lfloor>?e\<rfloor> + j" by (simp add: dvd_def) (rule_tac x="x" in exI, simp)
    hence "real_of_int c rdvd real_of_int (\<lfloor>?e\<rfloor> + j)" by (simp only: int_rdvd_iff)
    hence rcdej: "real_of_int c rdvd ?e + real_of_int j" by (simp add: ei[simplified isint_iff])
    from cx have "(c*x) div c = (\<lfloor>?e\<rfloor> + j) div c" by simp
    with cp have "x = (\<lfloor>?e\<rfloor> + j) div c" by simp
    with px have th: "?P ((\<lfloor>?e\<rfloor> + j) div c)" by auto
    from cp have cp': "real_of_int c > 0" by simp
    from cdej have cdej': "c dvd \<lfloor>Inum (real_of_int x#bs) (Add e (C j))\<rfloor>" by simp
    from nb have nb': "numbound0 (Add e (C j))" by simp
    have ji: "isint (C j) (real_of_int x#bs)" by (simp add: isint_def)
    from isint_add[OF ei ji] have ei':"isint (Add e (C j)) (real_of_int x#bs)" .
    from th \<sigma>_\<rho>[where b'="real_of_int x", OF lp' cp' nb' ei' cdej',symmetric]
    have "Ifm (real_of_int x#bs) (\<sigma>_\<rho> p (Add e (C j), c))" by simp
    with rcdej have th: "Ifm (real_of_int x#bs) (\<sigma> p c (Add e (C j)))" by (simp add: \<sigma>_def)
    from th bound0_I[OF \<sigma>_nb[OF lp nb', where k="c"],where bs="bs" and b="real_of_int x" and b'="a"]
    have "Ifm (a#bs) (\<sigma> p c (Add e (C j)))" by blast
      with ecR jD nob1    show "False" by blast
  qed
  from \<rho>[OF lp' px d dp nob] show "?P (x -d )" .
qed


lemma rl_thm:
  assumes lp: "iszlfm p (real_of_int (i::int)#bs)"
  shows "(\<exists> (x::int). Ifm (real_of_int x#bs) p) = ((\<exists> j\<in> {1 .. \<delta> p}. Ifm (real_of_int j#bs) (minusinf p)) \<or> (\<exists> (e,c) \<in> set (\<rho> p). \<exists> j\<in> {1 .. c*(\<delta> p)}. Ifm (a#bs) (\<sigma> p c (Add e (C j)))))"
  (is "(\<exists>(x::int). ?P x) = ((\<exists> j\<in> {1.. \<delta> p}. ?MP j)\<or>(\<exists> (e,c) \<in> ?R. \<exists> j\<in> _. ?SP c e j))"
    is "?lhs = (?MD \<or> ?RD)"  is "?lhs = ?rhs")
proof-
  let ?d= "\<delta> p"
  from \<delta>[OF lp] have d:"d_\<delta> p ?d" and dp: "?d > 0" by auto
  { assume H:"?MD" hence th:"\<exists> (x::int). ?MP x" by blast
    from H minusinf_ex[OF lp th] have ?thesis  by blast}
  moreover
  { fix e c j assume exR:"(e,c) \<in> ?R" and jD:"j\<in> {1 .. c*?d}" and spx:"?SP c e j"
    from exR \<rho>_l[OF lp] have nb: "numbound0 e" and ei:"isint e (real_of_int i#bs)" and cp: "c > 0"
      by auto
    have "isint (C j) (real_of_int i#bs)" by (simp add: isint_iff)
    with isint_add[OF numbound0_gen[OF nb ei,rule_format, where y="real_of_int i"]]
    have eji:"isint (Add e (C j)) (real_of_int i#bs)" by simp
    from nb have nb': "numbound0 (Add e (C j))" by simp
    from spx bound0_I[OF \<sigma>_nb[OF lp nb', where k="c"], where bs="bs" and b="a" and b'="real_of_int i"]
    have spx': "Ifm (real_of_int i # bs) (\<sigma> p c (Add e (C j)))" by blast
    from spx' have rcdej:"real_of_int c rdvd (Inum (real_of_int i#bs) (Add e (C j)))"
      and sr:"Ifm (real_of_int i#bs) (\<sigma>_\<rho> p (Add e (C j),c))" by (simp add: \<sigma>_def)+
    from rcdej eji[simplified isint_iff]
    have "real_of_int c rdvd real_of_int \<lfloor>Inum (real_of_int i#bs) (Add e (C j))\<rfloor>" by simp
    hence cdej:"c dvd \<lfloor>Inum (real_of_int i#bs) (Add e (C j))\<rfloor>" by (simp only: int_rdvd_iff)
    from cp have cp': "real_of_int c > 0" by simp
    from \<sigma>_\<rho>[OF lp cp' nb' eji cdej] spx' have "?P (\<lfloor>Inum (real_of_int i # bs) (Add e (C j))\<rfloor> div c)"
      by (simp add: \<sigma>_def)
    hence ?lhs by blast
    with exR jD spx have ?thesis by blast}
  moreover
  { fix x assume px: "?P x" and nob: "\<not> ?RD"
    from iszlfm_gen [OF lp,rule_format, where y="a"] have lp':"iszlfm p (a#bs)" .
    from \<rho>'[OF lp' d dp, rule_format, OF nob] have th:"\<forall> x. ?P x \<longrightarrow> ?P (x - ?d)" by blast
    from minusinf_inf[OF lp] obtain z where z:"\<forall> x<z. ?MP x = ?P x" by blast
    have zp: "\<bar>x - z\<bar> + 1 \<ge> 0" by arith
    from decr_lemma[OF dp,where x="x" and z="z"]
      decr_mult_lemma[OF dp th zp, rule_format, OF px] z have th:"\<exists> x. ?MP x" by auto
    with minusinf_bex[OF lp] px nob have ?thesis by blast}
  ultimately show ?thesis by blast
qed

lemma mirror_\<alpha>_\<rho>:   assumes lp: "iszlfm p (a#bs)"
  shows "(\<lambda> (t,k). (Inum (a#bs) t, k)) ` set (\<alpha>_\<rho> p) = (\<lambda> (t,k). (Inum (a#bs) t,k)) ` set (\<rho> (mirror p))"
  using lp
  by (induct p rule: mirror.induct) (simp_all add: split_def image_Un)

text \<open>The \<open>\<real>\<close> part\<close>

text\<open>Linearity for fm where Bound 0 ranges over \<open>\<real>\<close>\<close>
fun isrlfm :: "fm \<Rightarrow> bool"   (* Linearity test for fm *)
where
  "isrlfm (And p q) = (isrlfm p \<and> isrlfm q)"
| "isrlfm (Or p q) = (isrlfm p \<and> isrlfm q)"
| "isrlfm (Eq  (CN 0 c e)) = (c>0 \<and> numbound0 e)"
| "isrlfm (NEq (CN 0 c e)) = (c>0 \<and> numbound0 e)"
| "isrlfm (Lt  (CN 0 c e)) = (c>0 \<and> numbound0 e)"
| "isrlfm (Le  (CN 0 c e)) = (c>0 \<and> numbound0 e)"
| "isrlfm (Gt  (CN 0 c e)) = (c>0 \<and> numbound0 e)"
| "isrlfm (Ge  (CN 0 c e)) = (c>0 \<and> numbound0 e)"
| "isrlfm p = (isatom p \<and> (bound0 p))"

definition fp :: "fm \<Rightarrow> int \<Rightarrow> num \<Rightarrow> int \<Rightarrow> fm" where
  "fp p n s j \<equiv> (if n > 0 then
            (And p (And (Ge (CN 0 n (Sub s (Add (Floor s) (C j)))))
                        (Lt (CN 0 n (Sub s (Add (Floor s) (C (j+1))))))))
            else
            (And p (And (Le (CN 0 (-n) (Add (Neg s) (Add (Floor s) (C j)))))
                        (Gt (CN 0 (-n) (Add (Neg s) (Add (Floor s) (C (j + 1)))))))))"

  (* splits the bounded from the unbounded part*)
fun rsplit0 :: "num \<Rightarrow> (fm \<times> int \<times> num) list"
where
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
    thus "(\<Union>(a, b, c)\<in>M. set (f (a, b, c))) = (\<Union>(a, b, c)\<in>M. set (g a b c))"
      by (auto simp add: split_def)
  qed
  have U3': "\<forall> (p,n,s) \<in> {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0}. ?ff (p,n,s) = map (?f(p,n,s)) [n..0]"
    by auto
  hence U3: "(\<Union> ((\<lambda>(p,n,s). set (?ff (p,n,s))) ` {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0})) =
    (\<Union> ((\<lambda>(p,n,s). set (map (?f(p,n,s)) [n..0])) ` {(p,n,s). (p,n,s)\<in> ?SS a\<and>n<0}))"
  proof -
    fix M :: "('a\<times>'b\<times>'c) set" and f :: "('a\<times>'b\<times>'c) \<Rightarrow> 'd list" and g
    assume "\<forall> (a,b,c) \<in> M. f (a,b,c) = g a b c"
    thus "(\<Union>(a, b, c)\<in>M. set (f (a, b, c))) = (\<Union>(a, b, c)\<in>M. set (g a b c))"
      by (auto simp add: split_def)
  qed
  have "?SS (Floor a) = \<Union> ((\<lambda>x. set (?ff x)) ` ?SS a)"
    by auto
  also have "\<dots> = \<Union> ((\<lambda> (p,n,s). set (?ff (p,n,s))) ` ?SS a)"
    by blast
  also have "\<dots> =
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). set (?ff (p,n,s)))) Un
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). set (?ff (p,n,s)))) Un
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s). set (?ff (p,n,s)))))"
    by (auto split: if_splits)
  also have "\<dots> =
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). set [(p,0,Floor s)])) Un
   (UNION {(p,n,s). (p,n,s)\<in> ?SS a\<and>n>0} (\<lambda>(p,n,s). set(map(?f(p,n,s)) [0..n]))) Un
   (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s).
    set (map (?f(p,n,s)) [n..0]))))" by (simp only: U1 U2 U3)
  also have "\<dots> =
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). {(p,0,Floor s)})) Un
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). (?f(p,n,s)) ` {0 .. n})) Un
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s). (?f(p,n,s)) ` {n .. 0})))"
    by (simp only: set_map set_upto list.set)
  also have "\<dots> =
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). {(p,0,Floor s)})) Un
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). {?f(p,n,s) j| j. j\<in> {0 .. n}})) Un
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s).  {?f(p,n,s) j| j. j\<in> {n .. 0}})))"
    by blast
  finally
  have FS: "?SS (Floor a) =
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). {(p,0,Floor s)})) Un
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). {?f(p,n,s) j| j. j\<in> {0 .. n}})) Un
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s).  {?f(p,n,s) j| j. j\<in> {n .. 0}})))"
    by blast
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
      from 5 pns have H:"(Ifm ((x::real) # (bs::real list)) p' \<longrightarrow>
          Inum (x # bs) a = Inum (x # bs) (CN 0 n' s')) \<and>
          numbound0 s' \<and> isrlfm p'" by blast
      hence nb: "numbound0 s'" by simp
      from H have nf: "isrlfm (?p (p',n',s') j)" using fp_def np by simp
      let ?nxs = "CN 0 n' s'"
      let ?l = "\<lfloor>?N s'\<rfloor> + j"
      from H
      have "?I (?p (p',n',s') j) \<longrightarrow>
          (((?N ?nxs \<ge> real_of_int ?l) \<and> (?N ?nxs < real_of_int (?l + 1))) \<and> (?N a = ?N ?nxs ))"
        by (simp add: fp_def np algebra_simps)
      also have "\<dots> \<longrightarrow> \<lfloor>?N ?nxs\<rfloor> = ?l \<and> ?N a = ?N ?nxs"
        using floor_eq_iff[where x="?N ?nxs" and a="?l"] by simp
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
      from 5 pns have H:"(Ifm ((x::real) # (bs::real list)) p' \<longrightarrow>
          Inum (x # bs) a = Inum (x # bs) (CN 0 n' s')) \<and>
          numbound0 s' \<and> isrlfm p'" by blast
      hence nb: "numbound0 s'" by simp
      from H have nf: "isrlfm (?p (p',n',s') j)" using fp_def np by simp
      let ?nxs = "CN 0 n' s'"
      let ?l = "\<lfloor>?N s'\<rfloor> + j"
      from H
      have "?I (?p (p',n',s') j) \<longrightarrow>
          (((?N ?nxs \<ge> real_of_int ?l) \<and> (?N ?nxs < real_of_int (?l + 1))) \<and> (?N a = ?N ?nxs ))"
        by (simp add: np fp_def algebra_simps)
      also have "\<dots> \<longrightarrow> \<lfloor>?N ?nxs\<rfloor> = ?l \<and> ?N a = ?N ?nxs"
        using floor_eq_iff[where x="?N ?nxs" and a="?l"] by simp
      moreover
      have "\<dots> \<longrightarrow> (?N (Floor a) = ?N ((Add (Floor s') (C j))))"  by simp
      ultimately have "?I (?p (p',n',s') j) \<longrightarrow> (?N (Floor a) = ?N ((Add (Floor s') (C j))))"
        by blast
      with s_def n0 p_def nb nf have ?ths by auto}
    ultimately show ?ths by fastforce
  qed
next
  case (3 a b) then show ?case
    by auto
qed (auto simp add: Let_def split_def algebra_simps)

lemma real_in_int_intervals:
  assumes xb: "real_of_int m \<le> x \<and> x < real_of_int ((n::int) + 1)"
  shows "\<exists> j\<in> {m.. n}. real_of_int j \<le> x \<and> x < real_of_int (j+1)" (is "\<exists> j\<in> ?N. ?P j")
by (rule bexI[where P="?P" and x="\<lfloor>x\<rfloor>" and A="?N"])
(auto simp add: floor_less_iff[where x="x" and z="n+1", simplified]
  xb[simplified] floor_mono[where x="real_of_int m" and y="x", OF conjunct1[OF xb], simplified floor_of_int[where z="m"]])

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
    thus "(\<Union>(a, b, c)\<in>M. set (f (a, b, c))) = (\<Union>(a, b, c)\<in>M. set (g a b c))"
      by (auto simp add: split_def)
  qed
  have U3': "\<forall> (p,n,s) \<in> {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0}. ?ff (p,n,s) = map (?f(p,n,s)) [n..0]"
    by auto
  hence U3: "(UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s). set (?ff (p,n,s)))) = (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s). set (map (?f(p,n,s)) [n..0])))"
  proof-
    fix M :: "('a\<times>'b\<times>'c) set" and f :: "('a\<times>'b\<times>'c) \<Rightarrow> 'd list" and g
    assume "\<forall> (a,b,c) \<in> M. f (a,b,c) = g a b c"
    thus "(\<Union>(a, b, c)\<in>M. set (f (a, b, c))) = (\<Union>(a, b, c)\<in>M. set (g a b c))"
      by (auto simp add: split_def)
  qed

  have "?SS (Floor a) = \<Union> ((\<lambda>x. set (?ff x)) ` ?SS a)" by auto
  also have "\<dots> = \<Union> ((\<lambda> (p,n,s). set (?ff (p,n,s))) ` ?SS a)" by blast
  also have "\<dots> =
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). set (?ff (p,n,s)))) Un
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). set (?ff (p,n,s)))) Un
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s). set (?ff (p,n,s)))))"
    by (auto split: if_splits)
  also have "\<dots> =
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). set [(p,0,Floor s)])) Un
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). set (map (?f(p,n,s)) [0..n]))) Un
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s). set (map (?f(p,n,s)) [n..0]))))"
    by (simp only: U1 U2 U3)
  also have "\<dots> =
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). {(p,0,Floor s)})) Un
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). (?f(p,n,s)) ` {0 .. n})) Un
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s). (?f(p,n,s)) ` {n .. 0})))"
    by (simp only: set_map set_upto list.set)
  also have "\<dots> =
    ((UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n=0} (\<lambda> (p,n,s). {(p,0,Floor s)})) Un
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n>0} (\<lambda> (p,n,s). {?f(p,n,s) j| j. j\<in> {0 .. n}})) Un
    (UNION {(p,n,s). (p,n,s) \<in> ?SS a \<and> n<0} (\<lambda> (p,n,s).  {?f(p,n,s) j| j. j\<in> {n .. 0}})))"
    by blast
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
    from of_int_floor_le[of "?N s"] have "?N (Floor s) \<le> ?N s" by simp
    also from mult_left_mono[OF xp] np have "?N s \<le> real_of_int n * x + ?N s" by simp
    finally have "?N (Floor s) \<le> real_of_int n * x + ?N s" .
    moreover
    {from x1 np have "real_of_int n *x + ?N s < real_of_int n + ?N s" by simp
      also from real_of_int_floor_add_one_gt[where r="?N s"]
      have "\<dots> < real_of_int n + ?N (Floor s) + 1" by simp
      finally have "real_of_int n *x + ?N s < ?N (Floor s) + real_of_int (n+1)" by simp}
    ultimately have "?N (Floor s) \<le> real_of_int n *x + ?N s\<and> real_of_int n *x + ?N s < ?N (Floor s) + real_of_int (n+1)" by simp
    hence th: "0 \<le> real_of_int n *x + ?N s - ?N (Floor s) \<and> real_of_int n *x + ?N s - ?N (Floor s) < real_of_int (n+1)" by simp
    from real_in_int_intervals th have  "\<exists> j\<in> {0 .. n}. real_of_int j \<le> real_of_int n *x + ?N s - ?N (Floor s)\<and> real_of_int n *x + ?N s - ?N (Floor s) < real_of_int (j+1)" by simp

    hence "\<exists> j\<in> {0 .. n}. 0 \<le> real_of_int n *x + ?N s - ?N (Floor s) - real_of_int j \<and> real_of_int n *x + ?N s - ?N (Floor s) - real_of_int (j+1) < 0"
      by(simp only: myle[of _ "real_of_int n * x + Inum (x # bs) s - Inum (x # bs) (Floor s)"] less_iff_diff_less_0[where a="real_of_int n *x + ?N s - ?N (Floor s)"])
    hence "\<exists> j\<in> {0.. n}. ?I (?p (p,n,s) j)"
      using pns by (simp add: fp_def np algebra_simps)
    then obtain "j" where j_def: "j\<in> {0 .. n} \<and> ?I (?p (p,n,s) j)" by blast
    hence "\<exists>x \<in> {?p (p,n,s) j |j. 0\<le> j \<and> j \<le> n }. ?I x" by auto
    hence ?case using pns
      by (simp only: FS,simp add: bex_Un)
    (rule disjI2, rule disjI1,rule exI [where x="p"],
      rule exI [where x="n"],rule exI [where x="s"],simp_all add: np)
  }
  moreover
  { assume nn: "n < 0" hence np: "-n >0" by simp
    from of_int_floor_le[of "?N s"] have "?N (Floor s) + 1 > ?N s" by simp
    moreover from mult_left_mono_neg[OF xp] nn have "?N s \<ge> real_of_int n * x + ?N s" by simp
    ultimately have "?N (Floor s) + 1 > real_of_int n * x + ?N s" by arith
    moreover
    {from x1 nn have "real_of_int n *x + ?N s \<ge> real_of_int n + ?N s" by simp
      moreover from of_int_floor_le[of "?N s"]  have "real_of_int n + ?N s \<ge> real_of_int n + ?N (Floor s)" by simp
      ultimately have "real_of_int n *x + ?N s \<ge> ?N (Floor s) + real_of_int n"
        by (simp only: algebra_simps)}
    ultimately have "?N (Floor s) + real_of_int n \<le> real_of_int n *x + ?N s\<and> real_of_int n *x + ?N s < ?N (Floor s) + real_of_int (1::int)" by simp
    hence th: "real_of_int n \<le> real_of_int n *x + ?N s - ?N (Floor s) \<and> real_of_int n *x + ?N s - ?N (Floor s) < real_of_int (1::int)" by simp
    have th1: "\<forall> (a::real). (- a > 0) = (a < 0)" by auto
    have th2: "\<forall> (a::real). (0 \<ge> - a) = (a \<ge> 0)" by auto
    from real_in_int_intervals th  have  "\<exists> j\<in> {n .. 0}. real_of_int j \<le> real_of_int n *x + ?N s - ?N (Floor s)\<and> real_of_int n *x + ?N s - ?N (Floor s) < real_of_int (j+1)" by simp

    hence "\<exists> j\<in> {n .. 0}. 0 \<le> real_of_int n *x + ?N s - ?N (Floor s) - real_of_int j \<and> real_of_int n *x + ?N s - ?N (Floor s) - real_of_int (j+1) < 0"
      by(simp only: myle[of _ "real_of_int n * x + Inum (x # bs) s - Inum (x # bs) (Floor s)"] less_iff_diff_less_0[where a="real_of_int n *x + ?N s - ?N (Floor s)"])
    hence "\<exists> j\<in> {n .. 0}. 0 \<ge> - (real_of_int n *x + ?N s - ?N (Floor s) - real_of_int j) \<and> - (real_of_int n *x + ?N s - ?N (Floor s) - real_of_int (j+1)) > 0" by (simp only: th1[rule_format] th2[rule_format])
    hence "\<exists> j\<in> {n.. 0}. ?I (?p (p,n,s) j)"
      using pns by (simp add: fp_def nn algebra_simps
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
    case_tac s, simp_all, rename_tac nat a b, case_tac "nat", simp_all)

lemma le_mono: "\<forall> a n s. Inum (x#bs) a = Inum (x#bs) (CN 0 n s) \<and> numbound0 s \<longrightarrow> Ifm (x#bs) (le n s) = Ifm (x#bs) (Le a)" (is "\<forall> a n s. ?N a = ?N (CN 0 n s) \<and> _ \<longrightarrow> ?I (le n s) = ?I (Le a)")
proof(clarify)
  fix a n s
  assume H: "?N a = ?N (CN 0 n s)"
  show "?I (le n s) = ?I (Le a)" using H by (cases "n=0", (simp add: le_def))
  (cases "n > 0", simp_all add: le_def algebra_simps myle[of _ "0"])
qed

lemma le_l: "isrlfm (rsplit le a)"
  by (rule rsplit_l[where f="le" and a="a"], auto simp add: le_def)
(case_tac s, simp_all, rename_tac nat a b, case_tac "nat",simp_all)

lemma gt_mono: "\<forall> a n s. Inum (x#bs) a = Inum (x#bs) (CN 0 n s) \<and> numbound0 s \<longrightarrow> Ifm (x#bs) (gt n s) = Ifm (x#bs) (Gt a)" (is "\<forall> a n s. ?N a = ?N (CN 0 n s) \<and> _ \<longrightarrow> ?I (gt n s) = ?I (Gt a)")
proof(clarify)
  fix a n s
  assume H: "?N a = ?N (CN 0 n s)"
  show "?I (gt n s) = ?I (Gt a)" using H by (cases "n=0", (simp add: gt_def))
  (cases "n > 0", simp_all add: gt_def algebra_simps myless[of _ "0"])
qed
lemma gt_l: "isrlfm (rsplit gt a)"
  by (rule rsplit_l[where f="gt" and a="a"], auto simp add: gt_def)
(case_tac s, simp_all, rename_tac nat a b, case_tac "nat", simp_all)

lemma ge_mono: "\<forall> a n s. Inum (x#bs) a = Inum (x#bs) (CN 0 n s) \<and> numbound0 s \<longrightarrow> Ifm (x#bs) (ge n s) = Ifm (x#bs) (Ge a)" (is "\<forall> a n s . ?N a = ?N (CN 0 n s) \<and> _ \<longrightarrow> ?I (ge n s) = ?I (Ge a)")
proof(clarify)
  fix a n s
  assume H: "?N a = ?N (CN 0 n s)"
  show "?I (ge n s) = ?I (Ge a)" using H by (cases "n=0", (simp add: ge_def))
  (cases "n > 0", simp_all add: ge_def algebra_simps myle[of _ "0"])
qed
lemma ge_l: "isrlfm (rsplit ge a)"
  by (rule rsplit_l[where f="ge" and a="a"], auto simp add: ge_def)
(case_tac s, simp_all, rename_tac nat a b, case_tac "nat", simp_all)

lemma eq_mono: "\<forall> a n s. Inum (x#bs) a = Inum (x#bs) (CN 0 n s) \<and> numbound0 s \<longrightarrow> Ifm (x#bs) (eq n s) = Ifm (x#bs) (Eq a)" (is "\<forall> a n s. ?N a = ?N (CN 0 n s) \<and> _ \<longrightarrow> ?I (eq n s) = ?I (Eq a)")
proof(clarify)
  fix a n s
  assume H: "?N a = ?N (CN 0 n s)"
  show "?I (eq n s) = ?I (Eq a)" using H by (auto simp add: eq_def algebra_simps)
qed
lemma eq_l: "isrlfm (rsplit eq a)"
  by (rule rsplit_l[where f="eq" and a="a"], auto simp add: eq_def)
(case_tac s, simp_all, rename_tac nat a b, case_tac"nat", simp_all)

lemma neq_mono: "\<forall> a n s. Inum (x#bs) a = Inum (x#bs) (CN 0 n s) \<and> numbound0 s \<longrightarrow> Ifm (x#bs) (neq n s) = Ifm (x#bs) (NEq a)" (is "\<forall> a n s. ?N a = ?N (CN 0 n s) \<and> _ \<longrightarrow> ?I (neq n s) = ?I (NEq a)")
proof(clarify)
  fix a n s bs
  assume H: "?N a = ?N (CN 0 n s)"
  show "?I (neq n s) = ?I (NEq a)" using H by (auto simp add: neq_def algebra_simps)
qed

lemma neq_l: "isrlfm (rsplit neq a)"
  by (rule rsplit_l[where f="neq" and a="a"], auto simp add: neq_def)
(case_tac s, simp_all, rename_tac nat a b, case_tac"nat", simp_all)

lemma small_le:
  assumes u0:"0 \<le> u" and u1: "u < 1"
  shows "(-u \<le> real_of_int (n::int)) = (0 \<le> n)"
using u0 u1  by auto

lemma small_lt:
  assumes u0:"0 \<le> u" and u1: "u < 1"
  shows "(real_of_int (n::int) < real_of_int (m::int) - u) = (n < m)"
using u0 u1  by auto

lemma rdvd01_cs:
  assumes up: "u \<ge> 0" and u1: "u<1" and np: "real_of_int n > 0"
  shows "(real_of_int (i::int) rdvd real_of_int (n::int) * u - s) = (\<exists> j\<in> {0 .. n - 1}. real_of_int n * u = s - real_of_int \<lfloor>s\<rfloor> + real_of_int j \<and> real_of_int i rdvd real_of_int (j - \<lfloor>s\<rfloor>))" (is "?lhs = ?rhs")
proof-
  let ?ss = "s - real_of_int \<lfloor>s\<rfloor>"
  from real_of_int_floor_add_one_gt[where r="s", simplified myless[of "s"]]
    of_int_floor_le  have ss0:"?ss \<ge> 0" and ss1:"?ss < 1" by (auto simp: floor_less_cancel)
  from np have n0: "real_of_int n \<ge> 0" by simp
  from mult_left_mono[OF up n0] mult_strict_left_mono[OF u1 np]
  have nu0:"real_of_int n * u - s \<ge> -s" and nun:"real_of_int n * u -s < real_of_int n - s" by auto
  from int_rdvd_real[where i="i" and x="real_of_int (n::int) * u - s"]
  have "real_of_int i rdvd real_of_int n * u - s =
    (i dvd \<lfloor>real_of_int n * u - s\<rfloor> \<and> (real_of_int \<lfloor>real_of_int n * u - s\<rfloor> = real_of_int n * u - s ))"
    (is "_ = (?DE)" is "_ = (?D \<and> ?E)") by simp
  also have "\<dots> = (?DE \<and> real_of_int (\<lfloor>real_of_int n * u - s\<rfloor> + \<lfloor>s\<rfloor>) \<ge> -?ss
    \<and> real_of_int (\<lfloor>real_of_int n * u - s\<rfloor> + \<lfloor>s\<rfloor>) < real_of_int n - ?ss)" (is "_=(?DE \<and>real_of_int ?a \<ge> _ \<and> real_of_int ?a < _)")
    using nu0 nun  by auto
  also have "\<dots> = (?DE \<and> ?a \<ge> 0 \<and> ?a < n)" by(simp only: small_le[OF ss0 ss1] small_lt[OF ss0 ss1])
  also have "\<dots> = (?DE \<and> (\<exists> j\<in> {0 .. (n - 1)}. ?a = j))" by simp
  also have "\<dots> = (?DE \<and> (\<exists> j\<in> {0 .. (n - 1)}. real_of_int (\<lfloor>real_of_int n * u - s\<rfloor>) = real_of_int j - real_of_int \<lfloor>s\<rfloor> ))"
    by (simp only: algebra_simps of_int_diff[symmetric] of_int_eq_iff)
  also have "\<dots> = ((\<exists> j\<in> {0 .. (n - 1)}. real_of_int n * u - s = real_of_int j - real_of_int \<lfloor>s\<rfloor> \<and> real_of_int i rdvd real_of_int n * u - s))" using int_rdvd_iff[where i="i" and t="\<lfloor>real_of_int n * u - s\<rfloor>"]
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
  assumes xp:"x\<ge> 0" and x1: "x < 1" and np:"real_of_int n > 0"
  shows "Ifm (x#bs) (DVDJ i n s) = Ifm (x#bs) (Dvd i (CN 0 n s))"
proof-
  let ?f = "\<lambda> j. conj (Eq(CN 0 n (Add s (Sub(Floor (Neg s)) (C j))))) (Dvd i (Sub (C j) (Floor (Neg s))))"
  let ?s= "Inum (x#bs) s"
  from foldr_disj_map[where xs="[0..n - 1]" and bs="x#bs" and f="?f"]
  have "Ifm (x#bs) (DVDJ i n s) = (\<exists> j\<in> {0 .. (n - 1)}. Ifm (x#bs) (?f j))"
    by (simp add: np DVDJ_def)
  also have "\<dots> = (\<exists> j\<in> {0 .. (n - 1)}. real_of_int n * x = (- ?s) - real_of_int \<lfloor>- ?s\<rfloor> + real_of_int j \<and> real_of_int i rdvd real_of_int (j - \<lfloor>- ?s\<rfloor>))"
    by (simp add: algebra_simps)
  also from rdvd01_cs[OF xp x1 np, where i="i" and s="-?s"]
  have "\<dots> = (real_of_int i rdvd real_of_int n * x - (-?s))" by simp
  finally show ?thesis by simp
qed

lemma NDVDJ_NDVD:
  assumes xp:"x\<ge> 0" and x1: "x < 1" and np:"real_of_int n > 0"
  shows "Ifm (x#bs) (NDVDJ i n s) = Ifm (x#bs) (NDvd i (CN 0 n s))"
proof-
  let ?f = "\<lambda> j. disj(NEq(CN 0 n (Add s (Sub (Floor (Neg s)) (C j))))) (NDvd i (Sub (C j) (Floor(Neg s))))"
  let ?s= "Inum (x#bs) s"
  from foldr_conj_map[where xs="[0..n - 1]" and bs="x#bs" and f="?f"]
  have "Ifm (x#bs) (NDVDJ i n s) = (\<forall> j\<in> {0 .. (n - 1)}. Ifm (x#bs) (?f j))"
    by (simp add: np NDVDJ_def)
  also have "\<dots> = (\<not> (\<exists> j\<in> {0 .. (n - 1)}. real_of_int n * x = (- ?s) - real_of_int \<lfloor>- ?s\<rfloor> + real_of_int j \<and> real_of_int i rdvd real_of_int (j - \<lfloor>- ?s\<rfloor>)))"
    by (simp add: algebra_simps)
  also from rdvd01_cs[OF xp x1 np, where i="i" and s="-?s"]
  have "\<dots> = (\<not> (real_of_int i rdvd real_of_int n * x - (-?s)))" by simp
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
  if c = 0 then (Dvd i t) else if c >0 then DVDJ \<bar>i\<bar> c t else DVDJ \<bar>i\<bar> (-c) (Neg t))"

definition  NDVD :: "int \<Rightarrow> int \<Rightarrow> num \<Rightarrow> fm" where
  "NDVD i c t =
  (if i=0 then neq c t else
  if c = 0 then (NDvd i t) else if c >0 then NDVDJ \<bar>i\<bar> c t else NDVDJ \<bar>i\<bar> (-c) (Neg t))"

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
        rdvd_minus[where d="i" and t="real_of_int n * x + Inum (x # bs) s"]) }
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
        rdvd_minus[where d="i" and t="real_of_int n * x + Inum (x # bs) s"]) }
  moreover {assume inz: "i\<noteq>0" and "n>0" hence ?th
      by (simp add:NDVD_def H NDVDJ_NDVD[OF xp x1] rdvd_abs1)}
  ultimately show ?th by blast
qed

lemma DVD_l: "isrlfm (rsplit (DVD i) a)"
  by (rule rsplit_l[where f="DVD i" and a="a"], auto simp add: DVD_def eq_def DVDJ_l)
(case_tac s, simp_all, rename_tac nat a b, case_tac "nat", simp_all)

lemma NDVD_l: "isrlfm (rsplit (NDVD i) a)"
  by (rule rsplit_l[where f="NDVD i" and a="a"], auto simp add: NDVD_def neq_def NDVDJ_l)
(case_tac s, simp_all, rename_tac nat a b, case_tac "nat", simp_all)

fun rlfm :: "fm \<Rightarrow> fm"
where
  "rlfm (And p q) = conj (rlfm p) (rlfm q)"
| "rlfm (Or p q) = disj (rlfm p) (rlfm q)"
| "rlfm (Imp p q) = disj (rlfm (Not p)) (rlfm q)"
| "rlfm (Iff p q) = disj (conj(rlfm p) (rlfm q)) (conj(rlfm (Not p)) (rlfm (Not q)))"
| "rlfm (Lt a) = rsplit lt a"
| "rlfm (Le a) = rsplit le a"
| "rlfm (Gt a) = rsplit gt a"
| "rlfm (Ge a) = rsplit ge a"
| "rlfm (Eq a) = rsplit eq a"
| "rlfm (NEq a) = rsplit neq a"
| "rlfm (Dvd i a) = rsplit (\<lambda> t. DVD i t) a"
| "rlfm (NDvd i a) = rsplit (\<lambda> t. NDVD i t) a"
| "rlfm (Not (And p q)) = disj (rlfm (Not p)) (rlfm (Not q))"
| "rlfm (Not (Or p q)) = conj (rlfm (Not p)) (rlfm (Not q))"
| "rlfm (Not (Imp p q)) = conj (rlfm p) (rlfm (Not q))"
| "rlfm (Not (Iff p q)) = disj (conj(rlfm p) (rlfm(Not q))) (conj(rlfm(Not p)) (rlfm q))"
| "rlfm (Not (Not p)) = rlfm p"
| "rlfm (Not T) = F"
| "rlfm (Not F) = T"
| "rlfm (Not (Lt a)) = simpfm (rlfm (Ge a))"
| "rlfm (Not (Le a)) = simpfm (rlfm (Gt a))"
| "rlfm (Not (Gt a)) = simpfm (rlfm (Le a))"
| "rlfm (Not (Ge a)) = simpfm (rlfm (Lt a))"
| "rlfm (Not (Eq a)) = simpfm (rlfm (NEq a))"
| "rlfm (Not (NEq a)) = simpfm (rlfm (Eq a))"
| "rlfm (Not (Dvd i a)) = simpfm (rlfm (NDvd i a))"
| "rlfm (Not (NDvd i a)) = simpfm (rlfm (Dvd i a))"
| "rlfm p = p"

lemma bound0at_l : "\<lbrakk>isatom p ; bound0 p\<rbrakk> \<Longrightarrow> isrlfm p"
  by (induct p rule: isrlfm.induct, auto)

lemma simpfm_rl: "isrlfm p \<Longrightarrow> isrlfm (simpfm p)"
proof (induct p)
  case (Lt a)
  hence "bound0 (Lt a) \<or> (\<exists> c e. a = CN 0 c e \<and> c > 0 \<and> numbound0 e)"
    by (cases a,simp_all, rename_tac nat a b, case_tac "nat", simp_all)
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
      from \<open>c > 0\<close> have th:"numgcd (CN 0 c (simpnum e)) \<le> c"
        by (simp add: numgcd_def)
      from \<open>c > 0\<close> have th': "c\<noteq>0" by auto
      from \<open>c > 0\<close> have cp: "c \<ge> 0" by simp
      from zdiv_mono2[OF cp th1 th, simplified div_self[OF th']]
      have "0 < c div numgcd (CN 0 c (simpnum e))" by simp
    }
    with Lt a have ?case
      by (simp add: Let_def reducecoeff_def reducecoeffh_numbound0)}
  ultimately show ?case by blast
next
  case (Le a)
  hence "bound0 (Le a) \<or> (\<exists> c e. a = CN 0 c e \<and> c > 0 \<and> numbound0 e)"
    by (cases a,simp_all, rename_tac nat a b, case_tac "nat", simp_all)
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
      from \<open>c > 0\<close> have th:"numgcd (CN 0 c (simpnum e)) \<le> c"
        by (simp add: numgcd_def)
      from \<open>c > 0\<close> have th': "c\<noteq>0" by auto
      from \<open>c > 0\<close> have cp: "c \<ge> 0" by simp
      from zdiv_mono2[OF cp th1 th, simplified div_self[OF th']]
      have "0 < c div numgcd (CN 0 c (simpnum e))" by simp
    }
    with Le a have ?case
      by (simp add: Let_def reducecoeff_def reducecoeffh_numbound0)}
  ultimately show ?case by blast
next
  case (Gt a)
  hence "bound0 (Gt a) \<or> (\<exists> c e. a = CN 0 c e \<and> c > 0 \<and> numbound0 e)"
    by (cases a, simp_all, rename_tac nat a b,case_tac "nat", simp_all)
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
      from \<open>c > 0\<close> have th:"numgcd (CN 0 c (simpnum e)) \<le> c"
        by (simp add: numgcd_def)
      from \<open>c > 0\<close> have th': "c\<noteq>0" by auto
      from \<open>c > 0\<close> have cp: "c \<ge> 0" by simp
      from zdiv_mono2[OF cp th1 th, simplified div_self[OF th']]
      have "0 < c div numgcd (CN 0 c (simpnum e))" by simp
    }
    with Gt a have ?case
      by (simp add: Let_def reducecoeff_def reducecoeffh_numbound0)}
  ultimately show ?case by blast
next
  case (Ge a)
  hence "bound0 (Ge a) \<or> (\<exists> c e. a = CN 0 c e \<and> c > 0 \<and> numbound0 e)"
    by (cases a,simp_all, rename_tac nat a b, case_tac "nat", simp_all)
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
      from \<open>c > 0\<close> have th:"numgcd (CN 0 c (simpnum e)) \<le> c"
        by (simp add: numgcd_def)
      from \<open>c > 0\<close> have th': "c\<noteq>0" by auto
      from \<open>c > 0\<close> have cp: "c \<ge> 0" by simp
      from zdiv_mono2[OF cp th1 th, simplified div_self[OF th']]
      have "0 < c div numgcd (CN 0 c (simpnum e))" by simp
    }
    with Ge a have ?case
      by (simp add: Let_def reducecoeff_def reducecoeffh_numbound0)}
  ultimately show ?case by blast
next
  case (Eq a)
  hence "bound0 (Eq a) \<or> (\<exists> c e. a = CN 0 c e \<and> c > 0 \<and> numbound0 e)"
    by (cases a,simp_all, rename_tac nat a b, case_tac "nat", simp_all)
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
      from \<open>c > 0\<close> have th:"numgcd (CN 0 c (simpnum e)) \<le> c"
        by (simp add: numgcd_def)
      from \<open>c > 0\<close> have th': "c\<noteq>0" by auto
      from \<open>c > 0\<close> have cp: "c \<ge> 0" by simp
      from zdiv_mono2[OF cp th1 th, simplified div_self[OF th']]
      have "0 < c div numgcd (CN 0 c (simpnum e))" by simp
    }
    with Eq a have ?case
      by (simp add: Let_def reducecoeff_def reducecoeffh_numbound0)}
  ultimately show ?case by blast
next
  case (NEq a)
  hence "bound0 (NEq a) \<or> (\<exists> c e. a = CN 0 c e \<and> c > 0 \<and> numbound0 e)"
    by (cases a,simp_all, rename_tac nat a b, case_tac "nat", simp_all)
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
      from \<open>c > 0\<close> have th:"numgcd (CN 0 c (simpnum e)) \<le> c"
        by (simp add: numgcd_def)
      from \<open>c > 0\<close> have th': "c\<noteq>0" by auto
      from \<open>c > 0\<close> have cp: "c \<ge> 0" by simp
      from zdiv_mono2[OF cp th1 th, simplified div_self[OF th']]
      have "0 < c div numgcd (CN 0 c (simpnum e))" by simp
    }
    with NEq a have ?case
      by (simp add: Let_def reducecoeff_def reducecoeffh_numbound0)}
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
qed(auto simp add: conj_def imp_def disj_def iff_def Let_def)

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
by (induct p rule: rlfm.induct) (auto simp add: simpfm_rl)

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
  from 3 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {fix x
    assume xz: "x < ?z"
    hence "(real_of_int c * x < - ?e)"
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] ac_simps)
    hence "real_of_int c * x + ?e < 0" by arith
    hence "real_of_int c * x + ?e \<noteq> 0" by simp
    with xz have "?P ?z x (Eq (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp  }
  hence "\<forall> x < ?z. ?P ?z x (Eq (CN 0 c e))" by simp
  thus ?case by blast
next
  case (4 c e)
  from 4 have nb: "numbound0 e" by simp
  from 4 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {fix x
    assume xz: "x < ?z"
    hence "(real_of_int c * x < - ?e)"
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] ac_simps)
    hence "real_of_int c * x + ?e < 0" by arith
    hence "real_of_int c * x + ?e \<noteq> 0" by simp
    with xz have "?P ?z x (NEq (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp }
  hence "\<forall> x < ?z. ?P ?z x (NEq (CN 0 c e))" by simp
  thus ?case by blast
next
  case (5 c e)
  from 5 have nb: "numbound0 e" by simp
  from 5 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {fix x
    assume xz: "x < ?z"
    hence "(real_of_int c * x < - ?e)"
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] ac_simps)
    hence "real_of_int c * x + ?e < 0" by arith
    with xz have "?P ?z x (Lt (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"]  by simp }
  hence "\<forall> x < ?z. ?P ?z x (Lt (CN 0 c e))" by simp
  thus ?case by blast
next
  case (6 c e)
  from 6 have nb: "numbound0 e" by simp
  from 6 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {fix x
    assume xz: "x < ?z"
    hence "(real_of_int c * x < - ?e)"
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] ac_simps)
    hence "real_of_int c * x + ?e < 0" by arith
    with xz have "?P ?z x (Le (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp }
  hence "\<forall> x < ?z. ?P ?z x (Le (CN 0 c e))" by simp
  thus ?case by blast
next
  case (7 c e)
  from 7 have nb: "numbound0 e" by simp
  from 7 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {fix x
    assume xz: "x < ?z"
    hence "(real_of_int c * x < - ?e)"
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] ac_simps)
    hence "real_of_int c * x + ?e < 0" by arith
    with xz have "?P ?z x (Gt (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp }
  hence "\<forall> x < ?z. ?P ?z x (Gt (CN 0 c e))" by simp
  thus ?case by blast
next
  case (8 c e)
  from 8 have nb: "numbound0 e" by simp
  from 8 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {fix x
    assume xz: "x < ?z"
    hence "(real_of_int c * x < - ?e)"
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] ac_simps)
    hence "real_of_int c * x + ?e < 0" by arith
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
  from 3 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real_of_int c * x > - ?e)" by (simp add: ac_simps)
    hence "real_of_int c * x + ?e > 0" by arith
    hence "real_of_int c * x + ?e \<noteq> 0" by simp
    with xz have "?P ?z x (Eq (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp }
  hence "\<forall> x > ?z. ?P ?z x (Eq (CN 0 c e))" by simp
  thus ?case by blast
next
  case (4 c e)
  from 4 have nb: "numbound0 e" by simp
  from 4 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real_of_int c * x > - ?e)" by (simp add: ac_simps)
    hence "real_of_int c * x + ?e > 0" by arith
    hence "real_of_int c * x + ?e \<noteq> 0" by simp
    with xz have "?P ?z x (NEq (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp }
  hence "\<forall> x > ?z. ?P ?z x (NEq (CN 0 c e))" by simp
  thus ?case by blast
next
  case (5 c e)
  from 5 have nb: "numbound0 e" by simp
  from 5 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real_of_int c * x > - ?e)" by (simp add: ac_simps)
    hence "real_of_int c * x + ?e > 0" by arith
    with xz have "?P ?z x (Lt (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp }
  hence "\<forall> x > ?z. ?P ?z x (Lt (CN 0 c e))" by simp
  thus ?case by blast
next
  case (6 c e)
  from 6 have nb: "numbound0 e" by simp
  from 6 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real_of_int c * x > - ?e)" by (simp add: ac_simps)
    hence "real_of_int c * x + ?e > 0" by arith
    with xz have "?P ?z x (Le (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp }
  hence "\<forall> x > ?z. ?P ?z x (Le (CN 0 c e))" by simp
  thus ?case by blast
next
  case (7 c e)
  from 7 have nb: "numbound0 e" by simp
  from 7 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real_of_int c * x > - ?e)" by (simp add: ac_simps)
    hence "real_of_int c * x + ?e > 0" by arith
    with xz have "?P ?z x (Gt (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp }
  hence "\<forall> x > ?z. ?P ?z x (Gt (CN 0 c e))" by simp
  thus ?case by blast
next
  case (8 c e)
  from 8 have nb: "numbound0 e" by simp
  from 8 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real_of_int c * x > - ?e)" by (simp add: ac_simps)
    hence "real_of_int c * x + ?e > 0" by arith
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

fun \<Upsilon>:: "fm \<Rightarrow> (num \<times> int) list"
where
  "\<Upsilon> (And p q) = (\<Upsilon> p @ \<Upsilon> q)"
| "\<Upsilon> (Or p q) = (\<Upsilon> p @ \<Upsilon> q)"
| "\<Upsilon> (Eq  (CN 0 c e)) = [(Neg e,c)]"
| "\<Upsilon> (NEq (CN 0 c e)) = [(Neg e,c)]"
| "\<Upsilon> (Lt  (CN 0 c e)) = [(Neg e,c)]"
| "\<Upsilon> (Le  (CN 0 c e)) = [(Neg e,c)]"
| "\<Upsilon> (Gt  (CN 0 c e)) = [(Neg e,c)]"
| "\<Upsilon> (Ge  (CN 0 c e)) = [(Neg e,c)]"
| "\<Upsilon> p = []"

fun \<upsilon> :: "fm \<Rightarrow> num \<times> int \<Rightarrow> fm"
where
  "\<upsilon> (And p q) = (\<lambda> (t,n). And (\<upsilon> p (t,n)) (\<upsilon> q (t,n)))"
| "\<upsilon> (Or p q) = (\<lambda> (t,n). Or (\<upsilon> p (t,n)) (\<upsilon> q (t,n)))"
| "\<upsilon> (Eq (CN 0 c e)) = (\<lambda> (t,n). Eq (Add (Mul c t) (Mul n e)))"
| "\<upsilon> (NEq (CN 0 c e)) = (\<lambda> (t,n). NEq (Add (Mul c t) (Mul n e)))"
| "\<upsilon> (Lt (CN 0 c e)) = (\<lambda> (t,n). Lt (Add (Mul c t) (Mul n e)))"
| "\<upsilon> (Le (CN 0 c e)) = (\<lambda> (t,n). Le (Add (Mul c t) (Mul n e)))"
| "\<upsilon> (Gt (CN 0 c e)) = (\<lambda> (t,n). Gt (Add (Mul c t) (Mul n e)))"
| "\<upsilon> (Ge (CN 0 c e)) = (\<lambda> (t,n). Ge (Add (Mul c t) (Mul n e)))"
| "\<upsilon> p = (\<lambda> (t,n). p)"

lemma \<upsilon>_I: assumes lp: "isrlfm p"
  and np: "real_of_int n > 0" and nbt: "numbound0 t"
  shows "(Ifm (x#bs) (\<upsilon> p (t,n)) = Ifm (((Inum (x#bs) t)/(real_of_int n))#bs) p) \<and> bound0 (\<upsilon> p (t,n))" (is "(?I x (\<upsilon> p (t,n)) = ?I ?u p) \<and> ?B p" is "(_ = ?I (?t/?n) p) \<and> _" is "(_ = ?I (?N x t /_) p) \<and> _")
  using lp
proof(induct p rule: \<upsilon>.induct)
  case (5 c e)
  from 5 have cp: "c >0" and nb: "numbound0 e" by simp_all
  have "?I ?u (Lt (CN 0 c e)) = (real_of_int c *(?t/?n) + (?N x e) < 0)"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> = (?n*(real_of_int c *(?t/?n)) + ?n*(?N x e) < 0)"
    by (simp only: pos_less_divide_eq[OF np, where a="real_of_int c *(?t/?n) + (?N x e)"
      and b="0", simplified div_0]) (simp only: algebra_simps)
  also have "\<dots> = (real_of_int c *?t + ?n* (?N x e) < 0)"
    using np by simp
  finally show ?case using nbt nb by (simp add: algebra_simps)
next
  case (6 c e)
  from 6 have cp: "c >0" and nb: "numbound0 e" by simp_all
  have "?I ?u (Le (CN 0 c e)) = (real_of_int c *(?t/?n) + (?N x e) \<le> 0)"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> = (?n*(real_of_int c *(?t/?n)) + ?n*(?N x e) \<le> 0)"
    by (simp only: pos_le_divide_eq[OF np, where a="real_of_int c *(?t/?n) + (?N x e)"
      and b="0", simplified div_0]) (simp only: algebra_simps)
  also have "\<dots> = (real_of_int c *?t + ?n* (?N x e) \<le> 0)"
    using np by simp
  finally show ?case using nbt nb by (simp add: algebra_simps)
next
  case (7 c e)
  from 7 have cp: "c >0" and nb: "numbound0 e" by simp_all
  have "?I ?u (Gt (CN 0 c e)) = (real_of_int c *(?t/?n) + (?N x e) > 0)"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> = (?n*(real_of_int c *(?t/?n)) + ?n*(?N x e) > 0)"
    by (simp only: pos_divide_less_eq[OF np, where a="real_of_int c *(?t/?n) + (?N x e)"
      and b="0", simplified div_0]) (simp only: algebra_simps)
  also have "\<dots> = (real_of_int c *?t + ?n* (?N x e) > 0)"
    using np by simp
  finally show ?case using nbt nb by (simp add: algebra_simps)
next
  case (8 c e)
  from 8 have cp: "c >0" and nb: "numbound0 e" by simp_all
  have "?I ?u (Ge (CN 0 c e)) = (real_of_int c *(?t/?n) + (?N x e) \<ge> 0)"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> = (?n*(real_of_int c *(?t/?n)) + ?n*(?N x e) \<ge> 0)"
    by (simp only: pos_divide_le_eq[OF np, where a="real_of_int c *(?t/?n) + (?N x e)"
      and b="0", simplified div_0]) (simp only: algebra_simps)
  also have "\<dots> = (real_of_int c *?t + ?n* (?N x e) \<ge> 0)"
    using np by simp
  finally show ?case using nbt nb by (simp add: algebra_simps)
next
  case (3 c e)
  from 3 have cp: "c >0" and nb: "numbound0 e" by simp_all
  from np have np: "real_of_int n \<noteq> 0" by simp
  have "?I ?u (Eq (CN 0 c e)) = (real_of_int c *(?t/?n) + (?N x e) = 0)"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> = (?n*(real_of_int c *(?t/?n)) + ?n*(?N x e) = 0)"
    by (simp only: nonzero_eq_divide_eq[OF np, where a="real_of_int c *(?t/?n) + (?N x e)"
      and b="0", simplified div_0]) (simp only: algebra_simps)
  also have "\<dots> = (real_of_int c *?t + ?n* (?N x e) = 0)"
    using np by simp
  finally show ?case using nbt nb by (simp add: algebra_simps)
next
  case (4 c e)
  from 4 have cp: "c >0" and nb: "numbound0 e" by simp_all
  from np have np: "real_of_int n \<noteq> 0" by simp
  have "?I ?u (NEq (CN 0 c e)) = (real_of_int c *(?t/?n) + (?N x e) \<noteq> 0)"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> = (?n*(real_of_int c *(?t/?n)) + ?n*(?N x e) \<noteq> 0)"
    by (simp only: nonzero_eq_divide_eq[OF np, where a="real_of_int c *(?t/?n) + (?N x e)"
      and b="0", simplified div_0]) (simp only: algebra_simps)
  also have "\<dots> = (real_of_int c *?t + ?n* (?N x e) \<noteq> 0)"
    using np by simp
  finally show ?case using nbt nb by (simp add: algebra_simps)
qed(simp_all add: nbt numbound0_I[where bs ="bs" and b="(Inum (x#bs) t)/ real_of_int n" and b'="x"])

lemma \<Upsilon>_l:
  assumes lp: "isrlfm p"
  shows "\<forall> (t,k) \<in> set (\<Upsilon> p). numbound0 t \<and> k >0"
using lp
by(induct p rule: \<Upsilon>.induct)  auto

lemma rminusinf_\<Upsilon>:
  assumes lp: "isrlfm p"
  and nmi: "\<not> (Ifm (a#bs) (minusinf p))" (is "\<not> (Ifm (a#bs) (?M p))")
  and ex: "Ifm (x#bs) p" (is "?I x p")
  shows "\<exists> (s,m) \<in> set (\<Upsilon> p). x \<ge> Inum (a#bs) s / real_of_int m" (is "\<exists> (s,m) \<in> ?U p. x \<ge> ?N a s / real_of_int m")
proof-
  have "\<exists> (s,m) \<in> set (\<Upsilon> p). real_of_int m * x \<ge> Inum (a#bs) s " (is "\<exists> (s,m) \<in> ?U p. real_of_int m *x \<ge> ?N a s")
    using lp nmi ex
    by (induct p rule: minusinf.induct, auto simp add:numbound0_I[where bs="bs" and b="a" and b'="x"])
  then obtain s m where smU: "(s,m) \<in> set (\<Upsilon> p)" and mx: "real_of_int m * x \<ge> ?N a s" by blast
  from \<Upsilon>_l[OF lp] smU have mp: "real_of_int m > 0" by auto
  from pos_divide_le_eq[OF mp, where a="x" and b="?N a s", symmetric] mx have "x \<ge> ?N a s / real_of_int m"
    by (auto simp add: mult.commute)
  thus ?thesis using smU by auto
qed

lemma rplusinf_\<Upsilon>:
  assumes lp: "isrlfm p"
  and nmi: "\<not> (Ifm (a#bs) (plusinf p))" (is "\<not> (Ifm (a#bs) (?M p))")
  and ex: "Ifm (x#bs) p" (is "?I x p")
  shows "\<exists> (s,m) \<in> set (\<Upsilon> p). x \<le> Inum (a#bs) s / real_of_int m" (is "\<exists> (s,m) \<in> ?U p. x \<le> ?N a s / real_of_int m")
proof-
  have "\<exists> (s,m) \<in> set (\<Upsilon> p). real_of_int m * x \<le> Inum (a#bs) s " (is "\<exists> (s,m) \<in> ?U p. real_of_int m *x \<le> ?N a s")
    using lp nmi ex
    by (induct p rule: minusinf.induct, auto simp add:numbound0_I[where bs="bs" and b="a" and b'="x"])
  then obtain s m where smU: "(s,m) \<in> set (\<Upsilon> p)" and mx: "real_of_int m * x \<le> ?N a s" by blast
  from \<Upsilon>_l[OF lp] smU have mp: "real_of_int m > 0" by auto
  from pos_le_divide_eq[OF mp, where a="x" and b="?N a s", symmetric] mx have "x \<le> ?N a s / real_of_int m"
    by (auto simp add: mult.commute)
  thus ?thesis using smU by auto
qed

lemma lin_dense:
  assumes lp: "isrlfm p"
  and noS: "\<forall> t. l < t \<and> t< u \<longrightarrow> t \<notin> (\<lambda> (t,n). Inum (x#bs) t / real_of_int n) ` set (\<Upsilon> p)"
  (is "\<forall> t. _ \<and> _ \<longrightarrow> t \<notin> (\<lambda> (t,n). ?N x t / real_of_int n ) ` (?U p)")
  and lx: "l < x" and xu:"x < u" and px:" Ifm (x#bs) p"
  and ly: "l < y" and yu: "y < u"
  shows "Ifm (y#bs) p"
using lp px noS
proof (induct p rule: isrlfm.induct)
  case (5 c e) hence cp: "real_of_int c > 0" and nb: "numbound0 e" by simp_all
  from 5 have "x * real_of_int c + ?N x e < 0" by (simp add: algebra_simps)
  hence pxc: "x < (- ?N x e) / real_of_int c"
    by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="-?N x e"])
  from 5 have noSc:"\<forall> t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real_of_int c" by auto
  with ly yu have yne: "y \<noteq> - ?N x e / real_of_int c" by auto
  hence "y < (- ?N x e) / real_of_int c \<or> y > (-?N x e) / real_of_int c" by auto
  moreover {assume y: "y < (-?N x e)/ real_of_int c"
    hence "y * real_of_int c < - ?N x e"
      by (simp add: pos_less_divide_eq[OF cp, where a="y" and b="-?N x e", symmetric])
    hence "real_of_int c * y + ?N x e < 0" by (simp add: algebra_simps)
    hence ?case using numbound0_I[OF nb, where bs="bs" and b="x" and b'="y"] by simp}
  moreover {assume y: "y > (- ?N x e) / real_of_int c"
    with yu have eu: "u > (- ?N x e) / real_of_int c" by auto
    with noSc ly yu have "(- ?N x e) / real_of_int c \<le> l" by (cases "(- ?N x e) / real_of_int c > l", auto)
    with lx pxc have "False" by auto
    hence ?case by simp }
  ultimately show ?case by blast
next
  case (6 c e) hence cp: "real_of_int c > 0" and nb: "numbound0 e" by simp_all
  from 6 have "x * real_of_int c + ?N x e \<le> 0" by (simp add: algebra_simps)
  hence pxc: "x \<le> (- ?N x e) / real_of_int c"
    by (simp only: pos_le_divide_eq[OF cp, where a="x" and b="-?N x e"])
  from 6 have noSc:"\<forall> t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real_of_int c" by auto
  with ly yu have yne: "y \<noteq> - ?N x e / real_of_int c" by auto
  hence "y < (- ?N x e) / real_of_int c \<or> y > (-?N x e) / real_of_int c" by auto
  moreover {assume y: "y < (-?N x e)/ real_of_int c"
    hence "y * real_of_int c < - ?N x e"
      by (simp add: pos_less_divide_eq[OF cp, where a="y" and b="-?N x e", symmetric])
    hence "real_of_int c * y + ?N x e < 0" by (simp add: algebra_simps)
    hence ?case using numbound0_I[OF nb, where bs="bs" and b="x" and b'="y"] by simp}
  moreover {assume y: "y > (- ?N x e) / real_of_int c"
    with yu have eu: "u > (- ?N x e) / real_of_int c" by auto
    with noSc ly yu have "(- ?N x e) / real_of_int c \<le> l" by (cases "(- ?N x e) / real_of_int c > l", auto)
    with lx pxc have "False" by auto
    hence ?case by simp }
  ultimately show ?case by blast
next
  case (7 c e) hence cp: "real_of_int c > 0" and nb: "numbound0 e" by simp_all
  from 7 have "x * real_of_int c + ?N x e > 0" by (simp add: algebra_simps)
  hence pxc: "x > (- ?N x e) / real_of_int c"
    by (simp only: pos_divide_less_eq[OF cp, where a="x" and b="-?N x e"])
  from 7 have noSc:"\<forall> t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real_of_int c" by auto
  with ly yu have yne: "y \<noteq> - ?N x e / real_of_int c" by auto
  hence "y < (- ?N x e) / real_of_int c \<or> y > (-?N x e) / real_of_int c" by auto
  moreover {assume y: "y > (-?N x e)/ real_of_int c"
    hence "y * real_of_int c > - ?N x e"
      by (simp add: pos_divide_less_eq[OF cp, where a="y" and b="-?N x e", symmetric])
    hence "real_of_int c * y + ?N x e > 0" by (simp add: algebra_simps)
    hence ?case using numbound0_I[OF nb, where bs="bs" and b="x" and b'="y"] by simp}
  moreover {assume y: "y < (- ?N x e) / real_of_int c"
    with ly have eu: "l < (- ?N x e) / real_of_int c" by auto
    with noSc ly yu have "(- ?N x e) / real_of_int c \<ge> u" by (cases "(- ?N x e) / real_of_int c > l", auto)
    with xu pxc have "False" by auto
    hence ?case by simp }
  ultimately show ?case by blast
next
  case (8 c e) hence cp: "real_of_int c > 0" and nb: "numbound0 e" by simp_all
  from 8 have "x * real_of_int c + ?N x e \<ge> 0" by (simp add: algebra_simps)
  hence pxc: "x \<ge> (- ?N x e) / real_of_int c"
    by (simp only: pos_divide_le_eq[OF cp, where a="x" and b="-?N x e"])
  from 8 have noSc:"\<forall> t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real_of_int c" by auto
  with ly yu have yne: "y \<noteq> - ?N x e / real_of_int c" by auto
  hence "y < (- ?N x e) / real_of_int c \<or> y > (-?N x e) / real_of_int c" by auto
  moreover {assume y: "y > (-?N x e)/ real_of_int c"
    hence "y * real_of_int c > - ?N x e"
      by (simp add: pos_divide_less_eq[OF cp, where a="y" and b="-?N x e", symmetric])
    hence "real_of_int c * y + ?N x e > 0" by (simp add: algebra_simps)
    hence ?case using numbound0_I[OF nb, where bs="bs" and b="x" and b'="y"] by simp}
  moreover {assume y: "y < (- ?N x e) / real_of_int c"
    with ly have eu: "l < (- ?N x e) / real_of_int c" by auto
    with noSc ly yu have "(- ?N x e) / real_of_int c \<ge> u" by (cases "(- ?N x e) / real_of_int c > l", auto)
    with xu pxc have "False" by auto
    hence ?case by simp }
  ultimately show ?case by blast
next
  case (3 c e) hence cp: "real_of_int c > 0" and nb: "numbound0 e" by simp_all
  from cp have cnz: "real_of_int c \<noteq> 0" by simp
  from 3 have "x * real_of_int c + ?N x e = 0" by (simp add: algebra_simps)
  hence pxc: "x = (- ?N x e) / real_of_int c"
    by (simp only: nonzero_eq_divide_eq[OF cnz, where a="x" and b="-?N x e"])
  from 3 have noSc:"\<forall> t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real_of_int c" by auto
  with lx xu have yne: "x \<noteq> - ?N x e / real_of_int c" by auto
  with pxc show ?case by simp
next
  case (4 c e) hence cp: "real_of_int c > 0" and nb: "numbound0 e" by simp_all
  from cp have cnz: "real_of_int c \<noteq> 0" by simp
  from 4 have noSc:"\<forall> t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real_of_int c" by auto
  with ly yu have yne: "y \<noteq> - ?N x e / real_of_int c" by auto
  hence "y* real_of_int c \<noteq> -?N x e"
    by (simp only: nonzero_eq_divide_eq[OF cnz, where a="y" and b="-?N x e"]) simp
  hence "y* real_of_int c + ?N x e \<noteq> 0" by (simp add: algebra_simps)
  thus ?case using numbound0_I[OF nb, where bs="bs" and b="x" and b'="y"]
    by (simp add: algebra_simps)
qed (auto simp add: numbound0_I[where bs="bs" and b="y" and b'="x"])

lemma rinf_\<Upsilon>:
  assumes lp: "isrlfm p"
  and nmi: "\<not> (Ifm (x#bs) (minusinf p))" (is "\<not> (Ifm (x#bs) (?M p))")
  and npi: "\<not> (Ifm (x#bs) (plusinf p))" (is "\<not> (Ifm (x#bs) (?P p))")
  and ex: "\<exists> x.  Ifm (x#bs) p" (is "\<exists> x. ?I x p")
  shows "\<exists> (l,n) \<in> set (\<Upsilon> p). \<exists> (s,m) \<in> set (\<Upsilon> p).
    ?I ((Inum (x#bs) l / real_of_int n + Inum (x#bs) s / real_of_int m) / 2) p"
proof-
  let ?N = "\<lambda> x t. Inum (x#bs) t"
  let ?U = "set (\<Upsilon> p)"
  from ex obtain a where pa: "?I a p" by blast
  from bound0_I[OF rminusinf_bound0[OF lp], where bs="bs" and b="x" and b'="a"] nmi
  have nmi': "\<not> (?I a (?M p))" by simp
  from bound0_I[OF rplusinf_bound0[OF lp], where bs="bs" and b="x" and b'="a"] npi
  have npi': "\<not> (?I a (?P p))" by simp
  have "\<exists> (l,n) \<in> set (\<Upsilon> p). \<exists> (s,m) \<in> set (\<Upsilon> p). ?I ((?N a l/real_of_int n + ?N a s /real_of_int m) / 2) p"
  proof-
    let ?M = "(\<lambda> (t,c). ?N a t / real_of_int c) ` ?U"
    have fM: "finite ?M" by auto
    from rminusinf_\<Upsilon>[OF lp nmi pa] rplusinf_\<Upsilon>[OF lp npi pa]
    have "\<exists> (l,n) \<in> set (\<Upsilon> p). \<exists> (s,m) \<in> set (\<Upsilon> p). a \<le> ?N x l / real_of_int n \<and> a \<ge> ?N x s / real_of_int m" by blast
    then obtain "t" "n" "s" "m" where
      tnU: "(t,n) \<in> ?U" and smU: "(s,m) \<in> ?U"
      and xs1: "a \<le> ?N x s / real_of_int m" and tx1: "a \<ge> ?N x t / real_of_int n" by blast
    from \<Upsilon>_l[OF lp] tnU smU numbound0_I[where bs="bs" and b="x" and b'="a"] xs1 tx1 have xs: "a \<le> ?N a s / real_of_int m" and tx: "a \<ge> ?N a t / real_of_int n" by auto
    from tnU have Mne: "?M \<noteq> {}" by auto
    hence Une: "?U \<noteq> {}" by simp
    let ?l = "Min ?M"
    let ?u = "Max ?M"
    have linM: "?l \<in> ?M" using fM Mne by simp
    have uinM: "?u \<in> ?M" using fM Mne by simp
    have tnM: "?N a t / real_of_int n \<in> ?M" using tnU by auto
    have smM: "?N a s / real_of_int m \<in> ?M" using smU by auto
    have lM: "\<forall> t\<in> ?M. ?l \<le> t" using Mne fM by auto
    have Mu: "\<forall> t\<in> ?M. t \<le> ?u" using Mne fM by auto
    have "?l \<le> ?N a t / real_of_int n" using tnM Mne by simp hence lx: "?l \<le> a" using tx by simp
    have "?N a s / real_of_int m \<le> ?u" using smM Mne by simp hence xu: "a \<le> ?u" using xs by simp
    from finite_set_intervals2[where P="\<lambda> x. ?I x p",OF pa lx xu linM uinM fM lM Mu]
    have "(\<exists> s\<in> ?M. ?I s p) \<or>
      (\<exists> t1\<in> ?M. \<exists> t2 \<in> ?M. (\<forall> y. t1 < y \<and> y < t2 \<longrightarrow> y \<notin> ?M) \<and> t1 < a \<and> a < t2 \<and> ?I a p)" .
    moreover { fix u assume um: "u\<in> ?M" and pu: "?I u p"
      hence "\<exists> (tu,nu) \<in> ?U. u = ?N a tu / real_of_int nu" by auto
      then obtain "tu" "nu" where tuU: "(tu,nu) \<in> ?U" and tuu:"u= ?N a tu / real_of_int nu" by blast
      have "(u + u) / 2 = u" by auto with pu tuu
      have "?I (((?N a tu / real_of_int nu) + (?N a tu / real_of_int nu)) / 2) p" by simp
      with tuU have ?thesis by blast}
    moreover{
      assume "\<exists> t1\<in> ?M. \<exists> t2 \<in> ?M. (\<forall> y. t1 < y \<and> y < t2 \<longrightarrow> y \<notin> ?M) \<and> t1 < a \<and> a < t2 \<and> ?I a p"
      then obtain t1 and t2 where t1M: "t1 \<in> ?M" and t2M: "t2\<in> ?M"
        and noM: "\<forall> y. t1 < y \<and> y < t2 \<longrightarrow> y \<notin> ?M" and t1x: "t1 < a" and xt2: "a < t2" and px: "?I a p"
        by blast
      from t1M have "\<exists> (t1u,t1n) \<in> ?U. t1 = ?N a t1u / real_of_int t1n" by auto
      then obtain "t1u" "t1n" where t1uU: "(t1u,t1n) \<in> ?U" and t1u: "t1 = ?N a t1u / real_of_int t1n" by blast
      from t2M have "\<exists> (t2u,t2n) \<in> ?U. t2 = ?N a t2u / real_of_int t2n" by auto
      then obtain "t2u" "t2n" where t2uU: "(t2u,t2n) \<in> ?U" and t2u: "t2 = ?N a t2u / real_of_int t2n" by blast
      from t1x xt2 have t1t2: "t1 < t2" by simp
      let ?u = "(t1 + t2) / 2"
      from less_half_sum[OF t1t2] gt_half_sum[OF t1t2] have t1lu: "t1 < ?u" and ut2: "?u < t2" by auto
      from lin_dense[OF lp noM t1x xt2 px t1lu ut2] have "?I ?u p" .
      with t1uU t2uU t1u t2u have ?thesis by blast}
    ultimately show ?thesis by blast
  qed
  then obtain "l" "n" "s"  "m" where lnU: "(l,n) \<in> ?U" and smU:"(s,m) \<in> ?U"
    and pu: "?I ((?N a l / real_of_int n + ?N a s / real_of_int m) / 2) p" by blast
  from lnU smU \<Upsilon>_l[OF lp] have nbl: "numbound0 l" and nbs: "numbound0 s" by auto
  from numbound0_I[OF nbl, where bs="bs" and b="a" and b'="x"]
    numbound0_I[OF nbs, where bs="bs" and b="a" and b'="x"] pu
  have "?I ((?N x l / real_of_int n + ?N x s / real_of_int m) / 2) p" by simp
  with lnU smU
  show ?thesis by auto
qed
    (* The Ferrante - Rackoff Theorem *)

theorem fr_eq:
  assumes lp: "isrlfm p"
  shows "(\<exists> x. Ifm (x#bs) p) = ((Ifm (x#bs) (minusinf p)) \<or> (Ifm (x#bs) (plusinf p)) \<or> (\<exists> (t,n) \<in> set (\<Upsilon> p). \<exists> (s,m) \<in> set (\<Upsilon> p). Ifm ((((Inum (x#bs) t)/  real_of_int n + (Inum (x#bs) s) / real_of_int m) /2)#bs) p))"
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


lemma fr_eq_\<upsilon>:
  assumes lp: "isrlfm p"
  shows "(\<exists> x. Ifm (x#bs) p) = ((Ifm (x#bs) (minusinf p)) \<or> (Ifm (x#bs) (plusinf p)) \<or> (\<exists> (t,k) \<in> set (\<Upsilon> p). \<exists> (s,l) \<in> set (\<Upsilon> p). Ifm (x#bs) (\<upsilon> p (Add(Mul l t) (Mul k s) , 2*k*l))))"
  (is "(\<exists> x. ?I x p) = (?M \<or> ?P \<or> ?F)" is "?E = ?D")
proof
  assume px: "\<exists> x. ?I x p"
  have "?M \<or> ?P \<or> (\<not> ?M \<and> \<not> ?P)" by blast
  moreover {assume "?M \<or> ?P" hence "?D" by blast}
  moreover {assume nmi: "\<not> ?M" and npi: "\<not> ?P"
    let ?f ="\<lambda> (t,n). Inum (x#bs) t / real_of_int n"
    let ?N = "\<lambda> t. Inum (x#bs) t"
    {fix t n s m assume "(t,n)\<in> set (\<Upsilon> p)" and "(s,m) \<in> set (\<Upsilon> p)"
      with \<Upsilon>_l[OF lp] have tnb: "numbound0 t" and np:"real_of_int n > 0" and snb: "numbound0 s" and mp:"real_of_int m > 0"
        by auto
      let ?st = "Add (Mul m t) (Mul n s)"
      from np mp have mnp: "real_of_int (2*n*m) > 0" by (simp add: mult.commute)
      from tnb snb have st_nb: "numbound0 ?st" by simp
      have st: "(?N t / real_of_int n + ?N s / real_of_int m)/2 = ?N ?st / real_of_int (2*n*m)"
        using mnp mp np by (simp add: algebra_simps add_divide_distrib)
      from \<upsilon>_I[OF lp mnp st_nb, where x="x" and bs="bs"]
      have "?I x (\<upsilon> p (?st,2*n*m)) = ?I ((?N t / real_of_int n + ?N s / real_of_int m) /2) p" by (simp only: st[symmetric])}
    with rinf_\<Upsilon>[OF lp nmi npi px] have "?F" by blast hence "?D" by blast}
  ultimately show "?D" by blast
next
  assume "?D"
  moreover {assume m:"?M" from rminusinf_ex[OF lp m] have "?E" .}
  moreover {assume p: "?P" from rplusinf_ex[OF lp p] have "?E" . }
  moreover {fix t k s l assume "(t,k) \<in> set (\<Upsilon> p)" and "(s,l) \<in> set (\<Upsilon> p)"
    and px:"?I x (\<upsilon> p (Add (Mul l t) (Mul k s), 2*k*l))"
    with \<Upsilon>_l[OF lp] have tnb: "numbound0 t" and np:"real_of_int k > 0" and snb: "numbound0 s" and mp:"real_of_int l > 0" by auto
    let ?st = "Add (Mul l t) (Mul k s)"
    from np mp have mnp: "real_of_int (2*k*l) > 0" by (simp add: mult.commute)
    from tnb snb have st_nb: "numbound0 ?st" by simp
    from \<upsilon>_I[OF lp mnp st_nb, where bs="bs"] px have "?E" by auto}
  ultimately show "?E" by blast
qed

text\<open>The overall Part\<close>

lemma real_ex_int_real01:
  shows "(\<exists> (x::real). P x) = (\<exists> (i::int) (u::real). 0\<le> u \<and> u< 1 \<and> P (real_of_int i + u))"
proof(auto)
  fix x
  assume Px: "P x"
  let ?i = "\<lfloor>x\<rfloor>"
  let ?u = "x - real_of_int ?i"
  have "x = real_of_int ?i + ?u" by simp
  hence "P (real_of_int ?i + ?u)" using Px by simp
  moreover have "real_of_int ?i \<le> x" using of_int_floor_le by simp hence "0 \<le> ?u" by arith
  moreover have "?u < 1" using real_of_int_floor_add_one_gt[where r="x"] by arith
  ultimately show "(\<exists> (i::int) (u::real). 0\<le> u \<and> u< 1 \<and> P (real_of_int i + u))" by blast
qed

fun exsplitnum :: "num \<Rightarrow> num"
where
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

fun exsplit :: "fm \<Rightarrow> fm"
where
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
| "exsplit (Not p) = Not (exsplit p)"
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
  shows "(Ifm bs (E p)) = (\<exists> (i::int). Ifm (real_of_int i#bs) (E (And (And (Ge(CN 0 1 (C 0))) (Lt (CN 0 1 (C (- 1))))) (exsplit p))))" (is "?lhs = ?rhs")
proof-
  have "?rhs = (\<exists> (i::int). \<exists> x. 0\<le> x \<and> x < 1 \<and> Ifm (x#(real_of_int i)#bs) (exsplit p))"
    by auto
  also have "\<dots> = (\<exists> (i::int). \<exists> x. 0\<le> x \<and> x < 1 \<and> Ifm ((real_of_int i + x) #bs) p)"
    by (simp only: exsplit[OF qf] ac_simps)
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
    by (cases "rlfm p = And (Ge (CN 0 1 (C 0))) (Lt (CN 0 1 (C (- 1))))", simp_all)
  have PF: "?P = False" apply (simp add: Let_def reducecoeff_def numgcd_def rsplit_def ge_def lt_def conj_def disj_def)
    by (cases "rlfm p = And (Ge (CN 0 1 (C 0))) (Lt (CN 0 1 (C (- 1))))", simp_all)
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
    with lqx fr_eq_\<upsilon>[OF qfq] show "?M \<or> ?P \<or> ?F" by blast
  next
    assume D: "?D"
    let ?U = "set (\<Upsilon> ?rq )"
    from MF PF D have "?F" by auto
    then obtain t n s m where aU:"(t,n) \<in> ?U" and bU:"(s,m)\<in> ?U" and rqx: "?I x (\<upsilon> ?rq (Add (Mul m t) (Mul n s), 2*n*m))" by blast
    from qf have lrq:"isrlfm ?rq"using rlfm_l[OF qf]
      by (auto simp add: rsplit_def lt_def ge_def)
    from aU bU \<Upsilon>_l[OF lrq] have tnb: "numbound0 t" and np:"real_of_int n > 0" and snb: "numbound0 s" and mp:"real_of_int m > 0" by (auto simp add: split_def)
    let ?st = "Add (Mul m t) (Mul n s)"
    from tnb snb have stnb: "numbound0 ?st" by simp
    from np mp have mnp: "real_of_int (2*n*m) > 0" by (simp add: mult.commute)
    from conjunct1[OF \<upsilon>_I[OF lrq mnp stnb, where bs="bs" and x="x"], symmetric] rqx
    have "\<exists> x. ?I x ?rq" by auto
    thus "?E"
      using rlfm_I[OF qf] by (auto simp add: rsplit_def lt_def ge_def)
  qed
  with MF PF show ?thesis by blast
qed

lemma \<Upsilon>_cong_aux:
  assumes Ul: "\<forall> (t,n) \<in> set U. numbound0 t \<and> n >0"
  shows "((\<lambda> (t,n). Inum (x#bs) t /real_of_int n) ` (set (map (\<lambda> ((t,n),(s,m)). (Add (Mul m t) (Mul n s) , 2*n*m)) (alluopairs U)))) = ((\<lambda> ((t,n),(s,m)). (Inum (x#bs) t /real_of_int n + Inum (x#bs) s /real_of_int m)/2) ` (set U \<times> set U))"
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
  have st: "(?N t / real_of_int n + ?N s / real_of_int m)/2 = ?N ?st / real_of_int (2*n*m)"
   using mnz nnz by (simp add: algebra_simps add_divide_distrib)

  thus "(real_of_int m *  Inum (x # bs) t + real_of_int n * Inum (x # bs) s) /
       (2 * real_of_int n * real_of_int m)
       \<in> (\<lambda>((t, n), s, m).
             (Inum (x # bs) t / real_of_int n + Inum (x # bs) s / real_of_int m) / 2) `
         (set U \<times> set U)"using mnz nnz th
    apply (auto simp add: th add_divide_distrib algebra_simps split_def image_def)
    by (rule_tac x="(s,m)" in bexI,simp_all)
  (rule_tac x="(t,n)" in bexI,simp_all add: mult.commute)
next
  fix t n s m
  assume tnU: "(t,n) \<in> set U" and smU:"(s,m) \<in> set U"
  let ?N = "\<lambda> t. Inum (x#bs) t"
  let ?st= "Add (Mul m t) (Mul n s)"
  from Ul smU have mnz: "m \<noteq> 0" by auto
  from Ul tnU have  nnz: "n \<noteq> 0" by auto
  have st: "(?N t / real_of_int n + ?N s / real_of_int m)/2 = ?N ?st / real_of_int (2*n*m)"
   using mnz nnz by (simp add: algebra_simps add_divide_distrib)
 let ?P = "\<lambda> (t',n') (s',m'). (Inum (x # bs) t / real_of_int n + Inum (x # bs) s / real_of_int m)/2 = (Inum (x # bs) t' / real_of_int n' + Inum (x # bs) s' / real_of_int m')/2"
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
   have st': "(?N t' / real_of_int n' + ?N s' / real_of_int m')/2 = ?N ?st' / real_of_int (2*n'*m')"
   using mnz' nnz' by (simp add: algebra_simps add_divide_distrib)
 from Pts' have
   "(Inum (x # bs) t / real_of_int n + Inum (x # bs) s / real_of_int m)/2 = (Inum (x # bs) t' / real_of_int n' + Inum (x # bs) s' / real_of_int m')/2" by simp
 also have "\<dots> = ((\<lambda>(t, n). Inum (x # bs) t / real_of_int n) ((\<lambda>((t, n), s, m). (Add (Mul m t) (Mul n s), 2 * n * m)) ((t',n'),(s',m'))))" by (simp add: st')
 finally show "(Inum (x # bs) t / real_of_int n + Inum (x # bs) s / real_of_int m) / 2
          \<in> (\<lambda>(t, n). Inum (x # bs) t / real_of_int n) `
            (\<lambda>((t, n), s, m). (Add (Mul m t) (Mul n s), 2 * n * m)) `
            set (alluopairs U)"
   using ts'_U by blast
qed

lemma \<Upsilon>_cong:
  assumes lp: "isrlfm p"
  and UU': "((\<lambda> (t,n). Inum (x#bs) t /real_of_int n) ` U') = ((\<lambda> ((t,n),(s,m)). (Inum (x#bs) t /real_of_int n + Inum (x#bs) s /real_of_int m)/2) ` (U \<times> U))" (is "?f ` U' = ?g ` (U\<times>U)")
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
  from np mp have mnp: "real_of_int (2*n*m) > 0"
      by (simp add: mult.commute of_int_mult[symmetric] del: of_int_mult)
    from tnb snb have stnb: "numbound0 ?st" by simp
  have st: "(?N t / real_of_int n + ?N s / real_of_int m)/2 = ?N ?st / real_of_int (2*n*m)"
   using mp np by (simp add: algebra_simps add_divide_distrib)
  from tnU smU UU' have "?g ((t,n),(s,m)) \<in> ?f ` U'" by blast
  hence "\<exists> (t',n') \<in> U'. ?g ((t,n),(s,m)) = ?f (t',n')"
    by auto (rule_tac x="(a,b)" in bexI, auto)
  then obtain t' n' where tnU': "(t',n') \<in> U'" and th: "?g ((t,n),(s,m)) = ?f (t',n')" by blast
  from U' tnU' have tnb': "numbound0 t'" and np': "real_of_int n' > 0" by auto
  from \<upsilon>_I[OF lp mnp stnb, where bs="bs" and x="x"] Pst
  have Pst2: "Ifm (Inum (x # bs) (Add (Mul m t) (Mul n s)) / real_of_int (2 * n * m) # bs) p" by simp
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
  from np mp have mnp: "real_of_int (2*n*m) > 0"
      by (simp add: mult.commute of_int_mult[symmetric] del: of_int_mult)
    from tnb snb have stnb: "numbound0 ?st" by simp
  have st: "(?N t / real_of_int n + ?N s / real_of_int m)/2 = ?N ?st / real_of_int (2*n*m)"
   using mp np by (simp add: algebra_simps add_divide_distrib)
  from U' tnU' have tnb': "numbound0 t'" and np': "real_of_int n' > 0" by auto
  from \<upsilon>_I[OF lp np' tnb', where bs="bs" and x="x",simplified th[simplified split_def fst_conv snd_conv] st] Pt'
  have Pst2: "Ifm (Inum (x # bs) (Add (Mul m t) (Mul n s)) / real_of_int (2 * n * m) # bs) p" by simp
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
  let ?f= "(\<lambda> (t,n). ?N t / real_of_int n)"
  let ?h = "\<lambda> ((t,n),(s,m)). (?N t/real_of_int n + ?N s/ real_of_int m) /2"
  let ?F = "\<lambda> p. \<exists> a \<in> set (\<Upsilon> p). \<exists> b \<in> set (\<Upsilon> p). ?I x (\<upsilon> p (?g(a,b)))"
  let ?ep = "evaldjf (\<upsilon> ?q) ?Y"
  from rlfm_l[OF qf] have lq: "isrlfm ?q"
    by (simp add: rsplit_def lt_def ge_def conj_def disj_def Let_def reducecoeff_def numgcd_def)
  from alluopairs_set1[where xs="?U"] have UpU: "set ?Up \<le> (set ?U \<times> set ?U)" by simp
  from \<Upsilon>_l[OF lq] have U_l: "\<forall> (t,n) \<in> set ?U. numbound0 t \<and> n > 0" .
  from U_l UpU
  have "\<forall> ((t,n),(s,m)) \<in> set ?Up. numbound0 t \<and> n> 0 \<and> numbound0 s \<and> m > 0" by auto
  hence Snb: "\<forall> (t,n) \<in> set ?S. numbound0 t \<and> n > 0 "
    by (auto)
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
    have "(?f ` set ?Y) = ((?f o simp_num_pair) ` set ?S)" by (simp add: image_comp comp_assoc)
    also have "\<dots> = (?f ` set ?S)" by (simp add: th)
    also have "\<dots> = ((?f o ?g) ` set ?Up)"
      by (simp only: set_map o_def image_comp)
    also have "\<dots> = (?h ` (set ?U \<times> set ?U))"
      using \<Upsilon>_cong_aux[OF U_l, where x="x" and bs="bs", simplified set_map image_comp] by blast
    finally show ?thesis .
  qed
  have "\<forall> (t,n) \<in> set ?Y. bound0 (\<upsilon> ?q (t,n))"
  proof-
    { fix t n assume tnY: "(t,n) \<in> set ?Y"
      with Y_l have tnb: "numbound0 t" and np: "real_of_int n > 0" by auto
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
    by (simp only: split_def prod.collapse)
  also have "\<dots> = (Ifm bs (decr ?ep))" using decr[OF ep_nb] by blast
  finally have lr: "?lhs = ?rhs" by (simp only: ferrack01_def Let_def)
  from decr_qf[OF ep_nb] have "qfree (ferrack01 p)" by (simp only: Let_def ferrack01_def)
  with lr show ?thesis by blast
qed

lemma cp_thm':
  assumes lp: "iszlfm p (real_of_int (i::int)#bs)"
  and up: "d_\<beta> p 1" and dd: "d_\<delta> p d" and dp: "d > 0"
  shows "(\<exists> (x::int). Ifm (real_of_int x#bs) p) = ((\<exists> j\<in> {1 .. d}. Ifm (real_of_int j#bs) (minusinf p)) \<or> (\<exists> j\<in> {1.. d}. \<exists> b\<in> (Inum (real_of_int i#bs)) ` set (\<beta> p). Ifm ((b+real_of_int j)#bs) p))"
  using cp_thm[OF lp up dd dp] by auto

definition unit :: "fm \<Rightarrow> fm \<times> num list \<times> int" where
  "unit p \<equiv> (let p' = zlfm p ; l = \<zeta> p' ; q = And (Dvd l (CN 0 1 (C 0))) (a_\<beta> p' l); d = \<delta> q;
             B = remdups (map simpnum (\<beta> q)) ; a = remdups (map simpnum (\<alpha> q))
             in if length B \<le> length a then (q,B,d) else (mirror q, a,d))"

lemma unit: assumes qf: "qfree p"
  shows "\<And> q B d. unit p = (q,B,d) \<Longrightarrow>
      ((\<exists> (x::int). Ifm (real_of_int x#bs) p) =
       (\<exists> (x::int). Ifm (real_of_int x#bs) q)) \<and>
       (Inum (real_of_int i#bs)) ` set B = (Inum (real_of_int i#bs)) ` set (\<beta> q) \<and>
       d_\<beta> q 1 \<and> d_\<delta> q d \<and> d >0 \<and> iszlfm q (real_of_int (i::int)#bs) \<and> (\<forall> b\<in> set B. numbound0 b)"
proof-
  fix q B d
  assume qBd: "unit p = (q,B,d)"
  let ?thes = "((\<exists> (x::int). Ifm (real_of_int x#bs) p) = (\<exists> (x::int). Ifm (real_of_int x#bs) q)) \<and>
    Inum (real_of_int i#bs) ` set B = Inum (real_of_int i#bs) ` set (\<beta> q) \<and>
    d_\<beta> q 1 \<and> d_\<delta> q d \<and> 0 < d \<and> iszlfm q (real_of_int i # bs) \<and> (\<forall> b\<in> set B. numbound0 b)"
  let ?I = "\<lambda> (x::int) p. Ifm (real_of_int x#bs) p"
  let ?p' = "zlfm p"
  let ?l = "\<zeta> ?p'"
  let ?q = "And (Dvd ?l (CN 0 1 (C 0))) (a_\<beta> ?p' ?l)"
  let ?d = "\<delta> ?q"
  let ?B = "set (\<beta> ?q)"
  let ?B'= "remdups (map simpnum (\<beta> ?q))"
  let ?A = "set (\<alpha> ?q)"
  let ?A'= "remdups (map simpnum (\<alpha> ?q))"
  from conjunct1[OF zlfm_I[OF qf, where bs="bs"]]
  have pp': "\<forall> i. ?I i ?p' = ?I i p" by auto
  from iszlfm_gen[OF conjunct2[OF zlfm_I[OF qf, where bs="bs" and i="i"]]]
  have lp': "\<forall> (i::int). iszlfm ?p' (real_of_int i#bs)" by simp
  hence lp'': "iszlfm ?p' (real_of_int (i::int)#bs)" by simp
  from lp' \<zeta>[where p="?p'" and bs="bs"] have lp: "?l >0" and dl: "d_\<beta> ?p' ?l" by auto
  from a_\<beta>_ex[where p="?p'" and l="?l" and bs="bs", OF lp'' dl lp] pp'
  have pq_ex:"(\<exists> (x::int). ?I x p) = (\<exists> x. ?I x ?q)" by (simp add: int_rdvd_iff)
  from lp'' lp a_\<beta>[OF lp'' dl lp] have lq:"iszlfm ?q (real_of_int i#bs)" and uq: "d_\<beta> ?q 1"
    by (auto simp add: isint_def)
  from \<delta>[OF lq] have dp:"?d >0" and dd: "d_\<delta> ?q ?d" by blast+
  let ?N = "\<lambda> t. Inum (real_of_int (i::int)#bs) t"
  have "?N ` set ?B' = ((?N o simpnum) ` ?B)" by (simp add:image_comp)
  also have "\<dots> = ?N ` ?B" using simpnum_ci[where bs="real_of_int i #bs"] by auto
  finally have BB': "?N ` set ?B' = ?N ` ?B" .
  have "?N ` set ?A' = ((?N o simpnum) ` ?A)" by (simp add:image_comp)
  also have "\<dots> = ?N ` ?A" using simpnum_ci[where bs="real_of_int i #bs"] by auto
  finally have AA': "?N ` set ?A' = ?N ` ?A" .
  from \<beta>_numbound0[OF lq] have B_nb:"\<forall> b\<in> set ?B'. numbound0 b"
    by simp
  from \<alpha>_l[OF lq] have A_nb: "\<forall> b\<in> set ?A'. numbound0 b"
    by simp
  { assume "length ?B' \<le> length ?A'"
    hence q:"q=?q" and "B = ?B'" and d:"d = ?d"
      using qBd by (auto simp add: Let_def unit_def)
    with BB' B_nb have b: "?N ` (set B) = ?N ` set (\<beta> q)"
      and bn: "\<forall>b\<in> set B. numbound0 b" by simp+
    with pq_ex dp uq dd lq q d have ?thes by simp }
  moreover
  { assume "\<not> (length ?B' \<le> length ?A')"
    hence q:"q=mirror ?q" and "B = ?A'" and d:"d = ?d"
      using qBd by (auto simp add: Let_def unit_def)
    with AA' mirror_\<alpha>_\<beta>[OF lq] A_nb have b:"?N ` (set B) = ?N ` set (\<beta> q)"
      and bn: "\<forall>b\<in> set B. numbound0 b" by simp+
    from mirror_ex[OF lq] pq_ex q
    have pqm_eq:"(\<exists> (x::int). ?I x p) = (\<exists> (x::int). ?I x q)" by simp
    from lq uq q mirror_d_\<beta> [where p="?q" and bs="bs" and a="real_of_int i"]
    have lq': "iszlfm q (real_of_int i#bs)" and uq: "d_\<beta> q 1" by auto
    from \<delta>[OF lq'] mirror_\<delta>[OF lq] q d have dq:"d_\<delta> q d " by auto
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
  shows "((\<exists> (x::int). Ifm (real_of_int x#bs) p) = (Ifm bs (cooper p))) \<and> qfree (cooper p)"
  (is "(?lhs = ?rhs) \<and> _")
proof-

  let ?I = "\<lambda> (x::int) p. Ifm (real_of_int x#bs) p"
  let ?q = "fst (unit p)"
  let ?B = "fst (snd(unit p))"
  let ?d = "snd (snd (unit p))"
  let ?js = "[1..?d]"
  let ?mq = "minusinf ?q"
  let ?smq = "simpfm ?mq"
  let ?md = "evaldjf (\<lambda> j. simpfm (subst0 (C j) ?smq)) ?js"
  fix i
  let ?N = "\<lambda> t. Inum (real_of_int (i::int)#bs) t"
  let ?bjs = "[(b,j). b\<leftarrow>?B,j\<leftarrow>?js]"
  let ?sbjs = "map (\<lambda> (b,j). simpnum (Add b (C j))) ?bjs"
  let ?qd = "evaldjf (\<lambda> t. simpfm (subst0 t ?q)) (remdups ?sbjs)"
  have qbf:"unit p = (?q,?B,?d)" by simp
  from unit[OF qf qbf] have pq_ex: "(\<exists>(x::int). ?I x p) = (\<exists> (x::int). ?I x ?q)" and
    B:"?N ` set ?B = ?N ` set (\<beta> ?q)" and
    uq:"d_\<beta> ?q 1" and dd: "d_\<delta> ?q ?d" and dp: "?d > 0" and
    lq: "iszlfm ?q (real_of_int i#bs)" and
    Bn: "\<forall> b\<in> set ?B. numbound0 b" by auto
  from zlin_qfree[OF lq] have qfq: "qfree ?q" .
  from simpfm_qf[OF minusinf_qfree[OF qfq]] have qfmq: "qfree ?smq".
  have jsnb: "\<forall> j \<in> set ?js. numbound0 (C j)" by simp
  hence "\<forall> j\<in> set ?js. bound0 (subst0 (C j) ?smq)"
    by (auto simp only: subst0_bound0[OF qfmq])
  hence th: "\<forall> j\<in> set ?js. bound0 (simpfm (subst0 (C j) ?smq))"
    by auto
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
  have "?lhs = (\<exists> j\<in> {1.. ?d}. ?I j ?mq \<or> (\<exists> b\<in> ?N ` set ?B. Ifm ((b+ real_of_int j)#bs) ?q))" by auto
  also have "\<dots> = ((\<exists> j\<in> set ?js. ?I j ?smq) \<or> (\<exists> (b,j) \<in> (?N ` set ?B \<times> set ?js). Ifm ((b+ real_of_int j)#bs) ?q))" by auto
  also have "\<dots>= ((\<exists> j\<in> set ?js. ?I j ?smq) \<or> (\<exists> t \<in> (\<lambda> (b,j). ?N (Add b (C j))) ` set ?bjs. Ifm (t #bs) ?q))" by simp
  also have "\<dots>= ((\<exists> j\<in> set ?js. ?I j ?smq) \<or> (\<exists> t \<in> (\<lambda> (b,j). ?N (simpnum (Add b (C j)))) ` set ?bjs. Ifm (t #bs) ?q))" by (simp only: simpnum_ci)
  also  have "\<dots>= ((\<exists> j\<in> set ?js. ?I j ?smq) \<or> (\<exists> t \<in> set ?sbjs. Ifm (?N t #bs) ?q))"
    by (auto simp add: split_def)
  also have "\<dots> = ((\<exists> j\<in> set ?js. (\<lambda> j. ?I i (simpfm (subst0 (C j) ?smq))) j) \<or> (\<exists> t \<in> set (remdups ?sbjs). (\<lambda> t. ?I i (simpfm (subst0 t ?q))) t))"
    by (simp only: simpfm subst0_I[OF qfq] Inum.simps subst0_I[OF qfmq] set_remdups)
  also have "\<dots> = ((?I i (evaldjf (\<lambda> j. simpfm (subst0 (C j) ?smq)) ?js)) \<or> (?I i (evaldjf (\<lambda> t. simpfm (subst0 t ?q)) (remdups ?sbjs))))" by (simp only: evaldjf_ex)
  finally have mdqd: "?lhs = (?I i (disj ?md ?qd))" by simp
  hence mdqd2: "?lhs = (Ifm bs (decr (disj ?md ?qd)))" using decr [OF mdqdb] by simp
  {assume mdT: "?md = T"
    hence cT:"cooper p = T"
      by (simp only: cooper_def unit_def split_def Let_def if_True) simp
    from mdT mdqd have lhs:"?lhs" by auto
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
  shows "((\<exists> (x::int). Ifm (real_of_int x#bs) p) = (Ifm bs (DJ cooper p))) \<and> qfree (DJ cooper p)"
proof-
  from cooper have cqf: "\<forall> p. qfree p \<longrightarrow> qfree (cooper p)" by  blast
  from DJ_qf[OF cqf] qf have thqf:"qfree (DJ cooper p)" by blast
  have "Ifm bs (DJ cooper p) = (\<exists> q\<in> set (disjuncts p). Ifm bs (cooper q))"
     by (simp add: DJ_def evaldjf_ex)
  also have "\<dots> = (\<exists> q \<in> set(disjuncts p). \<exists> (x::int). Ifm (real_of_int x#bs)  q)"
    using cooper disjuncts_qf[OF qf] by blast
  also have "\<dots> = (\<exists> (x::int). Ifm (real_of_int x#bs) p)" by (induct p rule: disjuncts.induct, auto)
  finally show ?thesis using thqf by blast
qed

    (* Redy and Loveland *)

lemma \<sigma>_\<rho>_cong: assumes lp: "iszlfm p (a#bs)" and tt': "Inum (a#bs) t = Inum (a#bs) t'"
  shows "Ifm (a#bs) (\<sigma>_\<rho> p (t,c)) = Ifm (a#bs) (\<sigma>_\<rho> p (t',c))"
  using lp
  by (induct p rule: iszlfm.induct, auto simp add: tt')

lemma \<sigma>_cong: assumes lp: "iszlfm p (a#bs)" and tt': "Inum (a#bs) t = Inum (a#bs) t'"
  shows "Ifm (a#bs) (\<sigma> p c t) = Ifm (a#bs) (\<sigma> p c t')"
  by (simp add: \<sigma>_def tt' \<sigma>_\<rho>_cong[OF lp tt'])

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
  from ecRo jD px' show ?rhs apply (auto simp: cc')
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
  from ecRo jD px' show ?lhs apply (auto simp: cc')
    by (rule_tac x="(e', c')" in bexI,simp_all)
  (rule_tac x="j" in bexI, simp_all add: cc'[symmetric])
qed

lemma rl_thm':
  assumes lp: "iszlfm p (real_of_int (i::int)#bs)"
  and R: "(\<lambda>(b,k). (Inum (a#bs) b,k)) ` R =  (\<lambda>(b,k). (Inum (a#bs) b,k)) ` set (\<rho> p)"
  shows "(\<exists> (x::int). Ifm (real_of_int x#bs) p) = ((\<exists> j\<in> {1 .. \<delta> p}. Ifm (real_of_int j#bs) (minusinf p)) \<or> (\<exists> (e,c) \<in> R. \<exists> j\<in> {1.. c*(\<delta> p)}. Ifm (a#bs) (\<sigma> p c (Add e (C j)))))"
  using rl_thm[OF lp] \<rho>_cong[OF iszlfm_gen[OF lp, rule_format, where y="a"] R] by simp

definition chooset :: "fm \<Rightarrow> fm \<times> ((num\<times>int) list) \<times> int" where
  "chooset p \<equiv> (let q = zlfm p ; d = \<delta> q;
             B = remdups (map (\<lambda> (t,k). (simpnum t,k)) (\<rho> q)) ;
             a = remdups (map (\<lambda> (t,k). (simpnum t,k)) (\<alpha>_\<rho> q))
             in if length B \<le> length a then (q,B,d) else (mirror q, a,d))"

lemma chooset: assumes qf: "qfree p"
  shows "\<And> q B d. chooset p = (q,B,d) \<Longrightarrow>
     ((\<exists> (x::int). Ifm (real_of_int x#bs) p) =
      (\<exists> (x::int). Ifm (real_of_int x#bs) q)) \<and>
      ((\<lambda>(t,k). (Inum (real_of_int i#bs) t,k)) ` set B = (\<lambda>(t,k). (Inum (real_of_int i#bs) t,k)) ` set (\<rho> q)) \<and>
      (\<delta> q = d) \<and> d >0 \<and> iszlfm q (real_of_int (i::int)#bs) \<and> (\<forall> (e,c)\<in> set B. numbound0 e \<and> c>0)"
proof-
  fix q B d
  assume qBd: "chooset p = (q,B,d)"
  let ?thes = "((\<exists> (x::int). Ifm (real_of_int x#bs) p) =
             (\<exists> (x::int). Ifm (real_of_int x#bs) q)) \<and> ((\<lambda>(t,k). (Inum (real_of_int i#bs) t,k)) ` set B = (\<lambda>(t,k). (Inum (real_of_int i#bs) t,k)) ` set (\<rho> q)) \<and>
             (\<delta> q = d) \<and> d >0 \<and> iszlfm q (real_of_int (i::int)#bs) \<and> (\<forall> (e,c)\<in> set B. numbound0 e \<and> c>0)"
  let ?I = "\<lambda> (x::int) p. Ifm (real_of_int x#bs) p"
  let ?q = "zlfm p"
  let ?d = "\<delta> ?q"
  let ?B = "set (\<rho> ?q)"
  let ?f = "\<lambda> (t,k). (simpnum t,k)"
  let ?B'= "remdups (map ?f (\<rho> ?q))"
  let ?A = "set (\<alpha>_\<rho> ?q)"
  let ?A'= "remdups (map ?f (\<alpha>_\<rho> ?q))"
  from conjunct1[OF zlfm_I[OF qf, where bs="bs"]]
  have pp': "\<forall> i. ?I i ?q = ?I i p" by auto
  hence pq_ex:"(\<exists> (x::int). ?I x p) = (\<exists> x. ?I x ?q)" by simp
  from iszlfm_gen[OF conjunct2[OF zlfm_I[OF qf, where bs="bs" and i="i"]], rule_format, where y="real_of_int i"]
  have lq: "iszlfm ?q (real_of_int (i::int)#bs)" .
  from \<delta>[OF lq] have dp:"?d >0" by blast
  let ?N = "\<lambda> (t,c). (Inum (real_of_int (i::int)#bs) t,c)"
  have "?N ` set ?B' = ((?N o ?f) ` ?B)" by (simp add: split_def image_comp)
  also have "\<dots> = ?N ` ?B"
    by(simp add: split_def image_comp simpnum_ci[where bs="real_of_int i #bs"] image_def)
  finally have BB': "?N ` set ?B' = ?N ` ?B" .
  have "?N ` set ?A' = ((?N o ?f) ` ?A)" by (simp add: split_def image_comp)
  also have "\<dots> = ?N ` ?A" using simpnum_ci[where bs="real_of_int i #bs"]
    by(simp add: split_def image_comp simpnum_ci[where bs="real_of_int i #bs"] image_def)
  finally have AA': "?N ` set ?A' = ?N ` ?A" .
  from \<rho>_l[OF lq] have B_nb:"\<forall> (e,c)\<in> set ?B'. numbound0 e \<and> c > 0"
    by (simp add: split_def)
  from \<alpha>_\<rho>_l[OF lq] have A_nb: "\<forall> (e,c)\<in> set ?A'. numbound0 e \<and> c > 0"
    by (simp add: split_def)
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
    with AA' mirror_\<alpha>_\<rho>[OF lq] A_nb have b:"?N ` (set B) = ?N ` set (\<rho> q)"
      and bn: "\<forall>(e,c)\<in> set B. numbound0 e \<and> c > 0" by auto
    from mirror_ex[OF lq] pq_ex q
    have pqm_eq:"(\<exists> (x::int). ?I x p) = (\<exists> (x::int). ?I x q)" by simp
    from lq q mirror_l [where p="?q" and bs="bs" and a="real_of_int i"]
    have lq': "iszlfm q (real_of_int i#bs)" by auto
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
  shows "((\<exists> (x::int). Ifm (real_of_int x#bs) p) = (Ifm bs (redlove p))) \<and> qfree (redlove p)"
  (is "(?lhs = ?rhs) \<and> _")
proof-

  let ?I = "\<lambda> (x::int) p. Ifm (real_of_int x#bs) p"
  let ?q = "fst (chooset p)"
  let ?B = "fst (snd(chooset p))"
  let ?d = "snd (snd (chooset p))"
  let ?js = "[1..?d]"
  let ?mq = "minusinf ?q"
  let ?smq = "simpfm ?mq"
  let ?md = "evaldjf (\<lambda> j. simpfm (subst0 (C j) ?smq)) ?js"
  fix i
  let ?N = "\<lambda> (t,k). (Inum (real_of_int (i::int)#bs) t,k)"
  let ?qd = "evaldjf (stage ?q ?d) ?B"
  have qbf:"chooset p = (?q,?B,?d)" by simp
  from chooset[OF qf qbf] have pq_ex: "(\<exists>(x::int). ?I x p) = (\<exists> (x::int). ?I x ?q)" and
    B:"?N ` set ?B = ?N ` set (\<rho> ?q)" and dd: "\<delta> ?q = ?d" and dp: "?d > 0" and
    lq: "iszlfm ?q (real_of_int i#bs)" and
    Bn: "\<forall> (e,c)\<in> set ?B. numbound0 e \<and> c > 0" by auto
  from zlin_qfree[OF lq] have qfq: "qfree ?q" .
  from simpfm_qf[OF minusinf_qfree[OF qfq]] have qfmq: "qfree ?smq".
  have jsnb: "\<forall> j \<in> set ?js. numbound0 (C j)" by simp
  hence "\<forall> j\<in> set ?js. bound0 (subst0 (C j) ?smq)"
    by (auto simp only: subst0_bound0[OF qfmq])
  hence th: "\<forall> j\<in> set ?js. bound0 (simpfm (subst0 (C j) ?smq))"
    by auto
  from evaldjf_bound0[OF th] have mdb: "bound0 ?md" by simp
  from Bn stage_nb[OF lq] have th:"\<forall> x \<in> set ?B. bound0 (stage ?q ?d x)" by auto
  from evaldjf_bound0[OF th]  have qdb: "bound0 ?qd" .
  from mdb qdb
  have mdqdb: "bound0 (disj ?md ?qd)" by (simp only: disj_def, cases "?md=T \<or> ?qd=T", simp_all)
  from trans [OF pq_ex rl_thm'[OF lq B]] dd
  have "?lhs = ((\<exists> j\<in> {1.. ?d}. ?I j ?mq) \<or> (\<exists> (e,c)\<in> set ?B. \<exists> j\<in> {1 .. c*?d}. Ifm (real_of_int i#bs) (\<sigma> ?q c (Add e (C j)))))" by auto
  also have "\<dots> = ((\<exists> j\<in> {1.. ?d}. ?I j ?smq) \<or> (\<exists> (e,c)\<in> set ?B. ?I i (stage ?q ?d (e,c) )))"
    by (simp add: stage split_def)
  also have "\<dots> = ((\<exists> j\<in> {1 .. ?d}. ?I i (subst0 (C j) ?smq))  \<or> ?I i ?qd)"
    by (simp add: evaldjf_ex subst0_I[OF qfmq])
  finally have mdqd:"?lhs = (?I i ?md \<or> ?I i ?qd)" by (simp only: evaldjf_ex set_upto simpfm)
  also have "\<dots> = (?I i (disj ?md ?qd))" by simp
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
  shows "((\<exists> (x::int). Ifm (real_of_int x#bs) p) = (Ifm bs (DJ redlove p))) \<and> qfree (DJ redlove p)"
proof-
  from redlove have cqf: "\<forall> p. qfree p \<longrightarrow> qfree (redlove p)" by  blast
  from DJ_qf[OF cqf] qf have thqf:"qfree (DJ redlove p)" by blast
  have "Ifm bs (DJ redlove p) = (\<exists> q\<in> set (disjuncts p). Ifm bs (redlove q))"
     by (simp add: DJ_def evaldjf_ex)
  also have "\<dots> = (\<exists> q \<in> set(disjuncts p). \<exists> (x::int). Ifm (real_of_int x#bs)  q)"
    using redlove disjuncts_qf[OF qf] by blast
  also have "\<dots> = (\<exists> (x::int). Ifm (real_of_int x#bs) p)" by (induct p rule: disjuncts.induct, auto)
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
    have "?rhs = (\<exists> (i::int). \<exists> x. Ifm (x#real_of_int i#bs) ?es)"
      using splitex[OF qf] by simp
    with ferrack01[OF simpfm_qf[OF exsplit_qf[OF qf]]] have th1: "?rhs = (\<exists> (i::int). Ifm (real_of_int i#bs) (ferrack01 (simpfm (exsplit p))))" and qf':"qfree (ferrack01 (simpfm (exsplit p)))" by simp+
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
    have "?rhs = (\<exists> (i::int). \<exists> x. Ifm (x#real_of_int i#bs) ?es)"
      using splitex[OF qf] by simp
    with ferrack01[OF simpfm_qf[OF exsplit_qf[OF qf]]] have th1: "?rhs = (\<exists> (i::int). Ifm (real_of_int i#bs) (ferrack01 (simpfm (exsplit p))))" and qf':"qfree (ferrack01 (simpfm (exsplit p)))" by simp+
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

ML_val \<open>@{code mircfrqe} @{code problem1}\<close>
ML_val \<open>@{code mirlfrqe} @{code problem1}\<close>
ML_val \<open>@{code mircfrqe} @{code problem2}\<close>
ML_val \<open>@{code mirlfrqe} @{code problem2}\<close>
ML_val \<open>@{code mircfrqe} @{code problem3}\<close>
ML_val \<open>@{code mirlfrqe} @{code problem3}\<close>
ML_val \<open>@{code mircfrqe} @{code problem4}\<close>
ML_val \<open>@{code mirlfrqe} @{code problem4}\<close>


(*code_reflect Mir
  functions mircfrqe mirlfrqe
  file "mir.ML"*)

oracle mirfr_oracle = \<open>
let

val mk_C = @{code C} o @{code int_of_integer};
val mk_Dvd = @{code Dvd} o apfst @{code int_of_integer};
val mk_Bound = @{code Bound} o @{code nat_of_integer};

fun num_of_term vs (t as Free (xn, xT)) = (case AList.lookup (=) vs t
     of NONE => error "Variable not found in the list!"
      | SOME n => mk_Bound n)
  | num_of_term vs \<^term>\<open>of_int (0::int)\<close> = mk_C 0
  | num_of_term vs \<^term>\<open>of_int (1::int)\<close> = mk_C 1
  | num_of_term vs \<^term>\<open>0::real\<close> = mk_C 0
  | num_of_term vs \<^term>\<open>1::real\<close> = mk_C 1
  | num_of_term vs \<^term>\<open>- 1::real\<close> = mk_C (~ 1)
  | num_of_term vs (Bound i) = mk_Bound i
  | num_of_term vs \<^Const_>\<open>uminus \<^Type>\<open>real\<close> for t'\<close> = @{code Neg} (num_of_term vs t')
  | num_of_term vs \<^Const_>\<open>plus \<^Type>\<open>real\<close> for t1 t2\<close> =
      @{code Add} (num_of_term vs t1, num_of_term vs t2)
  | num_of_term vs \<^Const_>\<open>minus \<^Type>\<open>real\<close> for t1 t2\<close> =
      @{code Sub} (num_of_term vs t1, num_of_term vs t2)
  | num_of_term vs \<^Const_>\<open>times \<^Type>\<open>real\<close> for t1 t2\<close> =
      (case num_of_term vs t1 of
        @{code C} i => @{code Mul} (i, num_of_term vs t2)
      | _ => error "num_of_term: unsupported Multiplication")
  | num_of_term vs \<^Const_>\<open>of_int \<^Type>\<open>real\<close> for \<^Const_>\<open>numeral \<^Type>\<open>int\<close> for t'\<close>\<close> =
      mk_C (HOLogic.dest_numeral t')
  | num_of_term vs (\<^Const_>\<open>of_int \<^Type>\<open>real\<close>\<close> $ (\<^term>\<open>- numeral :: _ \<Rightarrow> int\<close> $ t')) =  (* FIXME !? *)
      mk_C (~ (HOLogic.dest_numeral t'))
  | num_of_term vs \<^Const_>\<open>of_int \<^Type>\<open>real\<close> for \<^Const_>\<open>floor \<^Type>\<open>real\<close> for t'\<close>\<close> =
      @{code Floor} (num_of_term vs t')
  | num_of_term vs \<^Const_>\<open>of_int \<^Type>\<open>real\<close> for \<^Const_>\<open>ceiling \<^Type>\<open>real\<close> for t'\<close>\<close> =
      @{code Neg} (@{code Floor} (@{code Neg} (num_of_term vs t')))
  | num_of_term vs \<^Const_>\<open>numeral \<^Type>\<open>real\<close> for t'\<close> =
      mk_C (HOLogic.dest_numeral t')
  | num_of_term vs (\<^term>\<open>- numeral :: _ \<Rightarrow> real\<close> $ t') =  (* FIXME !? *)
      mk_C (~ (HOLogic.dest_numeral t'))
  | num_of_term vs t = error ("num_of_term: unknown term " ^ Syntax.string_of_term \<^context> t);

fun fm_of_term vs \<^Const_>\<open>True\<close> = @{code T}
  | fm_of_term vs \<^Const_>\<open>False\<close> = @{code F}
  | fm_of_term vs \<^Const_>\<open>less \<^Type>\<open>real\<close> for t1 t2\<close> =
      @{code Lt} (@{code Sub} (num_of_term vs t1, num_of_term vs t2))
  | fm_of_term vs \<^Const_>\<open>less_eq \<^Type>\<open>real\<close> for t1 t2\<close> =
      @{code Le} (@{code Sub} (num_of_term vs t1, num_of_term vs t2))
  | fm_of_term vs \<^Const_>\<open>HOL.eq \<^Type>\<open>real\<close> for t1 t2\<close> =
      @{code Eq} (@{code Sub} (num_of_term vs t1, num_of_term vs t2))
  | fm_of_term vs \<^Const_>\<open>rdvd for \<^Const_>\<open>of_int \<^Type>\<open>real\<close> for \<^Const_>\<open>numeral \<^Type>\<open>int\<close> for t1\<close>\<close> t2\<close> =
      mk_Dvd (HOLogic.dest_numeral t1, num_of_term vs t2)
  | fm_of_term vs \<^Const_>\<open>rdvd for \<^Const_>\<open>of_int \<^Type>\<open>real\<close> for \<open>(\<^term>\<open>- numeral :: _ \<Rightarrow> int\<close> $ t1)\<close>\<close> t2\<close> =  (* FIXME !? *)
      mk_Dvd (~ (HOLogic.dest_numeral t1), num_of_term vs t2)
  | fm_of_term vs \<^Const_>\<open>HOL.eq \<^Type>\<open>bool\<close> for t1 t2\<close> =
      @{code Iff} (fm_of_term vs t1, fm_of_term vs t2)
  | fm_of_term vs \<^Const_>\<open>HOL.conj for t1 t2\<close> =
      @{code And} (fm_of_term vs t1, fm_of_term vs t2)
  | fm_of_term vs \<^Const_>\<open>HOL.disj for t1 t2\<close> =
      @{code Or} (fm_of_term vs t1, fm_of_term vs t2)
  | fm_of_term vs \<^Const_>\<open>HOL.implies for t1 t2\<close> =
      @{code Imp} (fm_of_term vs t1, fm_of_term vs t2)
  | fm_of_term vs \<^Const_>\<open>HOL.Not for t'\<close> =
      @{code Not} (fm_of_term vs t')
  | fm_of_term vs \<^Const_>\<open>Ex _ for \<open>Abs (xn, xT, p)\<close>\<close> =
      @{code E} (fm_of_term (map (fn (v, n) => (v, n + 1)) vs) p)
  | fm_of_term vs \<^Const_>\<open>All _ for \<open>Abs (xn, xT, p)\<close>\<close> =
      @{code A} (fm_of_term (map (fn (v, n) => (v, n + 1)) vs) p)
  | fm_of_term vs t = error ("fm_of_term : unknown term " ^ Syntax.string_of_term \<^context> t);

fun term_of_num vs (@{code C} i) =
      \<^Const>\<open>of_int \<^Type>\<open>real\<close> for \<open>HOLogic.mk_number HOLogic.intT (@{code integer_of_int} i)\<close>\<close>
  | term_of_num vs (@{code Bound} n) =
      let
        val m = @{code integer_of_nat} n;
      in fst (the (find_first (fn (_, q) => m = q) vs)) end
  | term_of_num vs (@{code Neg} (@{code Floor} (@{code Neg} t'))) =
      \<^Const>\<open>of_int \<^Type>\<open>real\<close> for \<^Const>\<open>ceiling \<^Type>\<open>real\<close> for \<open>term_of_num vs t'\<close>\<close>\<close>
  | term_of_num vs (@{code Neg} t') = \<^Const>\<open>uminus \<^Type>\<open>real\<close> for \<open>term_of_num vs t'\<close>\<close>
  | term_of_num vs (@{code Add} (t1, t2)) =
      \<^Const>\<open>plus \<^Type>\<open>real\<close> for \<open>term_of_num vs t1\<close> \<open>term_of_num vs t2\<close>\<close>
  | term_of_num vs (@{code Sub} (t1, t2)) =
      \<^Const>\<open>minus \<^Type>\<open>real\<close> for \<open>term_of_num vs t1\<close> \<open>term_of_num vs t2\<close>\<close>
  | term_of_num vs (@{code Mul} (i, t2)) =
      \<^Const>\<open>times \<^Type>\<open>real\<close> for \<open>term_of_num vs (@{code C} i)\<close> \<open>term_of_num vs t2\<close>\<close>
  | term_of_num vs (@{code Floor} t) = \<^Const>\<open>of_int \<^Type>\<open>real\<close> for \<^Const>\<open>floor \<^Type>\<open>real\<close> for \<open>term_of_num vs t\<close>\<close>\<close>
  | term_of_num vs (@{code CN} (n, i, t)) = term_of_num vs (@{code Add} (@{code Mul} (i, @{code Bound} n), t))
  | term_of_num vs (@{code CF} (c, t, s)) = term_of_num vs (@{code Add} (@{code Mul} (c, @{code Floor} t), s));

fun term_of_fm vs @{code T} = \<^Const>\<open>True\<close>
  | term_of_fm vs @{code F} = \<^Const>\<open>False\<close>
  | term_of_fm vs (@{code Lt} t) =
      \<^Const>\<open>less \<^Type>\<open>real\<close> for \<open>term_of_num vs t\<close> \<^term>\<open>0::real\<close>\<close>
  | term_of_fm vs (@{code Le} t) =
      \<^Const>\<open>less_eq \<^Type>\<open>real\<close> for \<open>term_of_num vs t\<close> \<^term>\<open>0::real\<close>\<close>
  | term_of_fm vs (@{code Gt} t) =
      \<^Const>\<open>less \<^Type>\<open>real\<close> for \<^term>\<open>0::real\<close> \<open>term_of_num vs t\<close>\<close>
  | term_of_fm vs (@{code Ge} t) =
      \<^Const>\<open>less_eq \<^Type>\<open>real\<close> for \<^term>\<open>0::real\<close> \<open>term_of_num vs t\<close>\<close>
  | term_of_fm vs (@{code Eq} t) =
      \<^Const>\<open>HOL.eq \<^Type>\<open>real\<close> for \<open>term_of_num vs t\<close> \<^term>\<open>0::real\<close>\<close>
  | term_of_fm vs (@{code NEq} t) =
      term_of_fm vs (@{code Not} (@{code Eq} t))
  | term_of_fm vs (@{code Dvd} (i, t)) =
      \<^Const>\<open>rdvd for \<open>term_of_num vs (@{code C} i)\<close> \<open>term_of_num vs t\<close>\<close>
  | term_of_fm vs (@{code NDvd} (i, t)) =
      term_of_fm vs (@{code Not} (@{code Dvd} (i, t)))
  | term_of_fm vs (@{code Not} t') =
      HOLogic.Not $ term_of_fm vs t'
  | term_of_fm vs (@{code And} (t1, t2)) =
      HOLogic.conj $ term_of_fm vs t1 $ term_of_fm vs t2
  | term_of_fm vs (@{code Or} (t1, t2)) =
      HOLogic.disj $ term_of_fm vs t1 $ term_of_fm vs t2
  | term_of_fm vs (@{code Imp}  (t1, t2)) =
      HOLogic.imp $ term_of_fm vs t1 $ term_of_fm vs t2
  | term_of_fm vs (@{code Iff} (t1, t2)) =
      \<^Const>\<open>HOL.eq \<^Type>\<open>bool\<close> for \<open>term_of_fm vs t1\<close> \<open>term_of_fm vs t2\<close>\<close>;

in
  fn (ctxt, t) =>
  let
    val fs = Misc_Legacy.term_frees t;
    val vs = map_index swap fs;
    (*If quick_and_dirty then run without proof generation as oracle*)
    val qe = if Config.get ctxt quick_and_dirty then @{code mircfrqe} else @{code mirlfrqe};
    val t' = term_of_fm vs (qe (fm_of_term vs t));
  in Thm.cterm_of ctxt (HOLogic.mk_Trueprop (HOLogic.mk_eq (t, t'))) end
end
\<close>

lemmas iff_real_of_int = of_int_eq_iff [where 'a = real, symmetric]
                         of_int_less_iff [where 'a = real, symmetric]
                         of_int_le_iff [where 'a = real, symmetric]

ML_file \<open>mir_tac.ML\<close>

method_setup mir = \<open>
  Scan.lift (Args.mode "no_quantify") >>
    (fn q => fn ctxt => SIMPLE_METHOD' (Mir_Tac.mir_tac ctxt (not q)))
\<close> "decision procedure for MIR arithmetic"

lemma "\<forall>x::real. (\<lfloor>x\<rfloor> = \<lceil>x\<rceil> \<longleftrightarrow> (x = real_of_int \<lfloor>x\<rfloor>))"
  by mir

lemma "\<forall>x::real. real_of_int (2::int)*x - (real_of_int (1::int)) < real_of_int \<lfloor>x\<rfloor> + real_of_int \<lceil>x\<rceil> \<and> real_of_int \<lfloor>x\<rfloor> + real_of_int \<lceil>x\<rceil>  \<le> real_of_int (2::int)*x + (real_of_int (1::int))"
  by mir

lemma "\<forall>x::real. 2*\<lfloor>x\<rfloor> \<le> \<lfloor>2*x\<rfloor> \<and> \<lfloor>2*x\<rfloor> \<le> 2*\<lfloor>x+1\<rfloor>"
  by mir

lemma "\<forall>x::real. \<exists>y \<le> x. (\<lfloor>x\<rfloor> = \<lceil>y\<rceil>)"
  by mir

lemma "\<forall>(x::real) (y::real). \<lfloor>x\<rfloor> = \<lfloor>y\<rfloor> \<longrightarrow> 0 \<le> \<bar>y - x\<bar> \<and> \<bar>y - x\<bar> \<le> 1"
  by mir

end
