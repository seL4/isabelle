(*  Title:      HOL/Decision_Procs/Ferrack.thy
    Author:     Amine Chaieb
*)

theory Ferrack
imports Complex_Main Dense_Linear_Order DP_Library
  "HOL-Library.Code_Target_Numeral"
begin

section \<open>Quantifier elimination for \<open>\<real> (0, 1, +, <)\<close>\<close>

  (*********************************************************************************)
  (****                            SHADOW SYNTAX AND SEMANTICS                  ****)
  (*********************************************************************************)

datatype (plugins del: size) num = C int | Bound nat | CN nat int num | Neg num | Add num num| Sub num num
  | Mul int num

instantiation num :: size
begin

primrec size_num :: "num \<Rightarrow> nat"
where
  "size_num (C c) = 1"
| "size_num (Bound n) = 1"
| "size_num (Neg a) = 1 + size_num a"
| "size_num (Add a b) = 1 + size_num a + size_num b"
| "size_num (Sub a b) = 3 + size_num a + size_num b"
| "size_num (Mul c a) = 1 + size_num a"
| "size_num (CN n c a) = 3 + size_num a "

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
    (* FORMULAE *)
datatype (plugins del: size) fm  =
  T| F| Lt num| Le num| Gt num| Ge num| Eq num| NEq num|
  NOT fm| And fm fm|  Or fm fm| Imp fm fm| Iff fm fm| E fm| A fm

instantiation fm :: size
begin

primrec size_fm :: "fm \<Rightarrow> nat"
where
  "size_fm (NOT p) = 1 + size_fm p"
| "size_fm (And p q) = 1 + size_fm p + size_fm q"
| "size_fm (Or p q) = 1 + size_fm p + size_fm q"
| "size_fm (Imp p q) = 3 + size_fm p + size_fm q"
| "size_fm (Iff p q) = 3 + 2 * (size_fm p + size_fm q)"
| "size_fm (E p) = 1 + size_fm p"
| "size_fm (A p) = 4 + size_fm p"
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
  "Ifm bs T = True"
| "Ifm bs F = False"
| "Ifm bs (Lt a) = (Inum bs a < 0)"
| "Ifm bs (Gt a) = (Inum bs a > 0)"
| "Ifm bs (Le a) = (Inum bs a \<le> 0)"
| "Ifm bs (Ge a) = (Inum bs a \<ge> 0)"
| "Ifm bs (Eq a) = (Inum bs a = 0)"
| "Ifm bs (NEq a) = (Inum bs a \<noteq> 0)"
| "Ifm bs (NOT p) = (\<not> (Ifm bs p))"
| "Ifm bs (And p q) = (Ifm bs p \<and> Ifm bs q)"
| "Ifm bs (Or p q) = (Ifm bs p \<or> Ifm bs q)"
| "Ifm bs (Imp p q) = ((Ifm bs p) \<longrightarrow> (Ifm bs q))"
| "Ifm bs (Iff p q) = (Ifm bs p = Ifm bs q)"
| "Ifm bs (E p) = (\<exists>x. Ifm (x#bs) p)"
| "Ifm bs (A p) = (\<forall>x. Ifm (x#bs) p)"

lemma IfmLeSub: "\<lbrakk> Inum bs s = s' ; Inum bs t = t' \<rbrakk> \<Longrightarrow> Ifm bs (Le (Sub s t)) = (s' \<le> t')"
  by simp

lemma IfmLtSub: "\<lbrakk> Inum bs s = s' ; Inum bs t = t' \<rbrakk> \<Longrightarrow> Ifm bs (Lt (Sub s t)) = (s' < t')"
  by simp

lemma IfmEqSub: "\<lbrakk> Inum bs s = s' ; Inum bs t = t' \<rbrakk> \<Longrightarrow> Ifm bs (Eq (Sub s t)) = (s' = t')"
  by simp

lemma IfmNOT: " (Ifm bs p = P) \<Longrightarrow> (Ifm bs (NOT p) = (\<not>P))"
  by simp

lemma IfmAnd: " \<lbrakk> Ifm bs p = P ; Ifm bs q = Q\<rbrakk> \<Longrightarrow> (Ifm bs (And p q) = (P \<and> Q))"
  by simp

lemma IfmOr: " \<lbrakk> Ifm bs p = P ; Ifm bs q = Q\<rbrakk> \<Longrightarrow> (Ifm bs (Or p q) = (P \<or> Q))"
  by simp

lemma IfmImp: " \<lbrakk> Ifm bs p = P ; Ifm bs q = Q\<rbrakk> \<Longrightarrow> (Ifm bs (Imp p q) = (P \<longrightarrow> Q))"
  by simp

lemma IfmIff: " \<lbrakk> Ifm bs p = P ; Ifm bs q = Q\<rbrakk> \<Longrightarrow> (Ifm bs (Iff p q) = (P = Q))"
  by simp

lemma IfmE: " (!! x. Ifm (x#bs) p = P x) \<Longrightarrow> (Ifm bs (E p) = (\<exists>x. P x))"
  by simp

lemma IfmA: " (!! x. Ifm (x#bs) p = P x) \<Longrightarrow> (Ifm bs (A p) = (\<forall>x. P x))"
  by simp

fun not:: "fm \<Rightarrow> fm"
where
  "not (NOT p) = p"
| "not T = F"
| "not F = T"
| "not p = NOT p"

lemma not[simp]: "Ifm bs (not p) = Ifm bs (NOT p)"
  by (cases p) auto

definition conj :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "conj p q =
   (if p = F \<or> q = F then F
    else if p = T then q
    else if q = T then p
    else if p = q then p else And p q)"

lemma conj[simp]: "Ifm bs (conj p q) = Ifm bs (And p q)"
  by (cases "p = F \<or> q = F", simp_all add: conj_def) (cases p, simp_all)

definition disj :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "disj p q =
   (if p = T \<or> q = T then T
    else if p = F then q
    else if q = F then p
    else if p = q then p else Or p q)"

lemma disj[simp]: "Ifm bs (disj p q) = Ifm bs (Or p q)"
  by (cases "p = T \<or> q = T", simp_all add: disj_def) (cases p, simp_all)

definition imp :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "imp p q =
   (if p = F \<or> q = T \<or> p = q then T
    else if p = T then q
    else if q = F then not p
    else Imp p q)"

lemma imp[simp]: "Ifm bs (imp p q) = Ifm bs (Imp p q)"
  by (cases "p = F \<or> q = T") (simp_all add: imp_def)

definition iff :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "iff p q =
   (if p = q then T
    else if p = NOT q \<or> NOT p = q then F
    else if p = F then not q
    else if q = F then not p
    else if p = T then q
    else if q = T then p
    else Iff p q)"

lemma iff[simp]: "Ifm bs (iff p q) = Ifm bs (Iff p q)"
  by (unfold iff_def, cases "p = q", simp, cases "p = NOT q", simp) (cases "NOT p = q", auto)

lemma conj_simps:
  "conj F Q = F"
  "conj P F = F"
  "conj T Q = Q"
  "conj P T = P"
  "conj P P = P"
  "P \<noteq> T \<Longrightarrow> P \<noteq> F \<Longrightarrow> Q \<noteq> T \<Longrightarrow> Q \<noteq> F \<Longrightarrow> P \<noteq> Q \<Longrightarrow> conj P Q = And P Q"
  by (simp_all add: conj_def)

lemma disj_simps:
  "disj T Q = T"
  "disj P T = T"
  "disj F Q = Q"
  "disj P F = P"
  "disj P P = P"
  "P \<noteq> T \<Longrightarrow> P \<noteq> F \<Longrightarrow> Q \<noteq> T \<Longrightarrow> Q \<noteq> F \<Longrightarrow> P \<noteq> Q \<Longrightarrow> disj P Q = Or P Q"
  by (simp_all add: disj_def)

lemma imp_simps:
  "imp F Q = T"
  "imp P T = T"
  "imp T Q = Q"
  "imp P F = not P"
  "imp P P = T"
  "P \<noteq> T \<Longrightarrow> P \<noteq> F \<Longrightarrow> P \<noteq> Q \<Longrightarrow> Q \<noteq> T \<Longrightarrow> Q \<noteq> F \<Longrightarrow> imp P Q = Imp P Q"
  by (simp_all add: imp_def)

lemma trivNOT: "p \<noteq> NOT p" "NOT p \<noteq> p"
  by (induct p) auto

lemma iff_simps:
  "iff p p = T"
  "iff p (NOT p) = F"
  "iff (NOT p) p = F"
  "iff p F = not p"
  "iff F p = not p"
  "p \<noteq> NOT T \<Longrightarrow> iff T p = p"
  "p\<noteq> NOT T \<Longrightarrow> iff p T = p"
  "p\<noteq>q \<Longrightarrow> p\<noteq> NOT q \<Longrightarrow> q\<noteq> NOT p \<Longrightarrow> p\<noteq> F \<Longrightarrow> q\<noteq> F \<Longrightarrow> p \<noteq> T \<Longrightarrow> q \<noteq> T \<Longrightarrow> iff p q = Iff p q"
  using trivNOT
  by (simp_all add: iff_def, cases p, auto)

  (* Quantifier freeness *)
fun qfree:: "fm \<Rightarrow> bool"
where
  "qfree (E p) = False"
| "qfree (A p) = False"
| "qfree (NOT p) = qfree p"
| "qfree (And p q) = (qfree p \<and> qfree q)"
| "qfree (Or  p q) = (qfree p \<and> qfree q)"
| "qfree (Imp p q) = (qfree p \<and> qfree q)"
| "qfree (Iff p q) = (qfree p \<and> qfree q)"
| "qfree p = True"

  (* Boundedness and substitution *)
primrec numbound0:: "num \<Rightarrow> bool" (* a num is INDEPENDENT of Bound 0 *)
where
  "numbound0 (C c) = True"
| "numbound0 (Bound n) = (n > 0)"
| "numbound0 (CN n c a) = (n \<noteq> 0 \<and> numbound0 a)"
| "numbound0 (Neg a) = numbound0 a"
| "numbound0 (Add a b) = (numbound0 a \<and> numbound0 b)"
| "numbound0 (Sub a b) = (numbound0 a \<and> numbound0 b)"
| "numbound0 (Mul i a) = numbound0 a"

lemma numbound0_I:
  assumes nb: "numbound0 a"
  shows "Inum (b#bs) a = Inum (b'#bs) a"
  using nb by (induct a) simp_all

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
  using bp numbound0_I[where b="b" and bs="bs" and b'="b'"]
  by (induct p) auto

lemma not_qf[simp]: "qfree p \<Longrightarrow> qfree (not p)"
  by (cases p) auto

lemma not_bn[simp]: "bound0 p \<Longrightarrow> bound0 (not p)"
  by (cases p) auto


lemma conj_qf[simp]: "\<lbrakk>qfree p ; qfree q\<rbrakk> \<Longrightarrow> qfree (conj p q)"
  using conj_def by auto
lemma conj_nb[simp]: "\<lbrakk>bound0 p ; bound0 q\<rbrakk> \<Longrightarrow> bound0 (conj p q)"
  using conj_def by auto

lemma disj_qf[simp]: "\<lbrakk>qfree p ; qfree q\<rbrakk> \<Longrightarrow> qfree (disj p q)"
  using disj_def by auto
lemma disj_nb[simp]: "\<lbrakk>bound0 p ; bound0 q\<rbrakk> \<Longrightarrow> bound0 (disj p q)"
  using disj_def by auto

lemma imp_qf[simp]: "\<lbrakk>qfree p ; qfree q\<rbrakk> \<Longrightarrow> qfree (imp p q)"
  using imp_def by (cases "p=F \<or> q=T",simp_all add: imp_def)
lemma imp_nb[simp]: "\<lbrakk>bound0 p ; bound0 q\<rbrakk> \<Longrightarrow> bound0 (imp p q)"
  using imp_def by (cases "p=F \<or> q=T \<or> p=q",simp_all add: imp_def)

lemma iff_qf[simp]: "\<lbrakk>qfree p ; qfree q\<rbrakk> \<Longrightarrow> qfree (iff p q)"
  unfolding iff_def by (cases "p = q") auto
lemma iff_nb[simp]: "\<lbrakk>bound0 p ; bound0 q\<rbrakk> \<Longrightarrow> bound0 (iff p q)"
  using iff_def unfolding iff_def by (cases "p = q") auto

fun decrnum:: "num \<Rightarrow> num"
where
  "decrnum (Bound n) = Bound (n - 1)"
| "decrnum (Neg a) = Neg (decrnum a)"
| "decrnum (Add a b) = Add (decrnum a) (decrnum b)"
| "decrnum (Sub a b) = Sub (decrnum a) (decrnum b)"
| "decrnum (Mul c a) = Mul c (decrnum a)"
| "decrnum (CN n c a) = CN (n - 1) c (decrnum a)"
| "decrnum a = a"

fun decr :: "fm \<Rightarrow> fm"
where
  "decr (Lt a) = Lt (decrnum a)"
| "decr (Le a) = Le (decrnum a)"
| "decr (Gt a) = Gt (decrnum a)"
| "decr (Ge a) = Ge (decrnum a)"
| "decr (Eq a) = Eq (decrnum a)"
| "decr (NEq a) = NEq (decrnum a)"
| "decr (NOT p) = NOT (decr p)"
| "decr (And p q) = conj (decr p) (decr q)"
| "decr (Or p q) = disj (decr p) (decr q)"
| "decr (Imp p q) = imp (decr p) (decr q)"
| "decr (Iff p q) = iff (decr p) (decr q)"
| "decr p = p"

lemma decrnum:
  assumes nb: "numbound0 t"
  shows "Inum (x # bs) t = Inum bs (decrnum t)"
  using nb by (induct t rule: decrnum.induct) simp_all

lemma decr:
  assumes nb: "bound0 p"
  shows "Ifm (x # bs) p = Ifm bs (decr p)"
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
| "isatom p = False"

lemma bound0_qf: "bound0 p \<Longrightarrow> qfree p"
  by (induct p) simp_all

definition djf :: "('a \<Rightarrow> fm) \<Rightarrow> 'a \<Rightarrow> fm \<Rightarrow> fm"
where
  "djf f p q =
   (if q = T then T
    else if q = F then f p
    else (let fp = f p in case fp of T \<Rightarrow> T | F \<Rightarrow> q | _ \<Rightarrow> Or (f p) q))"

definition evaldjf :: "('a \<Rightarrow> fm) \<Rightarrow> 'a list \<Rightarrow> fm"
  where "evaldjf f ps = foldr (djf f) ps F"

lemma djf_Or: "Ifm bs (djf f p q) = Ifm bs (Or (f p) q)"
  by (cases "q = T", simp add: djf_def, cases "q = F", simp add: djf_def)
    (cases "f p", simp_all add: Let_def djf_def)


lemma djf_simps:
  "djf f p T = T"
  "djf f p F = f p"
  "q \<noteq> T \<Longrightarrow> q \<noteq> F \<Longrightarrow> djf f p q = (let fp = f p in case fp of T \<Rightarrow> T | F \<Rightarrow> q | _ \<Rightarrow> Or (f p) q)"
  by (simp_all add: djf_def)

lemma evaldjf_ex: "Ifm bs (evaldjf f ps) \<longleftrightarrow> (\<exists>p \<in> set ps. Ifm bs (f p))"
  by (induct ps) (simp_all add: evaldjf_def djf_Or)

lemma evaldjf_bound0:
  assumes nb: "\<forall>x\<in> set xs. bound0 (f x)"
  shows "bound0 (evaldjf f xs)"
  using nb by (induct xs, auto simp add: evaldjf_def djf_def Let_def) (case_tac "f a", auto)

lemma evaldjf_qf:
  assumes nb: "\<forall>x\<in> set xs. qfree (f x)"
  shows "qfree (evaldjf f xs)"
  using nb by (induct xs, auto simp add: evaldjf_def djf_def Let_def) (case_tac "f a", auto)

fun disjuncts :: "fm \<Rightarrow> fm list"
where
  "disjuncts (Or p q) = disjuncts p @ disjuncts q"
| "disjuncts F = []"
| "disjuncts p = [p]"

lemma disjuncts: "(\<exists>q\<in> set (disjuncts p). Ifm bs q) = Ifm bs p"
  by (induct p rule: disjuncts.induct) auto

lemma disjuncts_nb: "bound0 p \<Longrightarrow> \<forall>q\<in> set (disjuncts p). bound0 q"
proof -
  assume nb: "bound0 p"
  then have "list_all bound0 (disjuncts p)"
    by (induct p rule: disjuncts.induct) auto
  then show ?thesis
    by (simp only: list_all_iff)
qed

lemma disjuncts_qf: "qfree p \<Longrightarrow> \<forall>q\<in> set (disjuncts p). qfree q"
proof -
  assume qf: "qfree p"
  then have "list_all qfree (disjuncts p)"
    by (induct p rule: disjuncts.induct) auto
  then show ?thesis
    by (simp only: list_all_iff)
qed

definition DJ :: "(fm \<Rightarrow> fm) \<Rightarrow> fm \<Rightarrow> fm"
  where "DJ f p = evaldjf f (disjuncts p)"

lemma DJ:
  assumes fdj: "\<forall>p q. Ifm bs (f (Or p q)) = Ifm bs (Or (f p) (f q))"
    and fF: "f F = F"
  shows "Ifm bs (DJ f p) = Ifm bs (f p)"
proof -
  have "Ifm bs (DJ f p) = (\<exists>q \<in> set (disjuncts p). Ifm bs (f q))"
    by (simp add: DJ_def evaldjf_ex)
  also have "\<dots> = Ifm bs (f p)"
    using fdj fF by (induct p rule: disjuncts.induct) auto
  finally show ?thesis .
qed

lemma DJ_qf:
  assumes fqf: "\<forall>p. qfree p \<longrightarrow> qfree (f p)"
  shows "\<forall>p. qfree p \<longrightarrow> qfree (DJ f p) "
proof clarify
  fix p
  assume qf: "qfree p"
  have th: "DJ f p = evaldjf f (disjuncts p)"
    by (simp add: DJ_def)
  from disjuncts_qf[OF qf] have "\<forall>q\<in> set (disjuncts p). qfree q" .
  with fqf have th':"\<forall>q\<in> set (disjuncts p). qfree (f q)"
    by blast
  from evaldjf_qf[OF th'] th show "qfree (DJ f p)"
    by simp
qed

lemma DJ_qe:
  assumes qe: "\<forall>bs p. qfree p \<longrightarrow> qfree (qe p) \<and> (Ifm bs (qe p) = Ifm bs (E p))"
  shows "\<forall>bs p. qfree p \<longrightarrow> qfree (DJ qe p) \<and> (Ifm bs ((DJ qe p)) = Ifm bs (E p))"
proof clarify
  fix p :: fm
  fix bs
  assume qf: "qfree p"
  from qe have qth: "\<forall>p. qfree p \<longrightarrow> qfree (qe p)"
    by blast
  from DJ_qf[OF qth] qf have qfth: "qfree (DJ qe p)"
    by auto
  have "Ifm bs (DJ qe p) \<longleftrightarrow> (\<exists>q\<in> set (disjuncts p). Ifm bs (qe q))"
    by (simp add: DJ_def evaldjf_ex)
  also have "\<dots> \<longleftrightarrow> (\<exists>q \<in> set(disjuncts p). Ifm bs (E q))"
    using qe disjuncts_qf[OF qf] by auto
  also have "\<dots> = Ifm bs (E p)"
    by (induct p rule: disjuncts.induct) auto
  finally show "qfree (DJ qe p) \<and> Ifm bs (DJ qe p) = Ifm bs (E p)"
    using qfth by blast
qed

  (* Simplification *)

fun maxcoeff:: "num \<Rightarrow> int"
where
  "maxcoeff (C i) = \<bar>i\<bar>"
| "maxcoeff (CN n c t) = max \<bar>c\<bar> (maxcoeff t)"
| "maxcoeff t = 1"

lemma maxcoeff_pos: "maxcoeff t \<ge> 0"
  by (induct t rule: maxcoeff.induct, auto)

fun numgcdh:: "num \<Rightarrow> int \<Rightarrow> int"
where
  "numgcdh (C i) = (\<lambda>g. gcd i g)"
| "numgcdh (CN n c t) = (\<lambda>g. gcd c (numgcdh t g))"
| "numgcdh t = (\<lambda>g. 1)"

definition numgcd :: "num \<Rightarrow> int"
  where "numgcd t = numgcdh t (maxcoeff t)"

fun reducecoeffh:: "num \<Rightarrow> int \<Rightarrow> num"
where
  "reducecoeffh (C i) = (\<lambda>g. C (i div g))"
| "reducecoeffh (CN n c t) = (\<lambda>g. CN n (c div g) (reducecoeffh t g))"
| "reducecoeffh t = (\<lambda>g. t)"

definition reducecoeff :: "num \<Rightarrow> num"
where
  "reducecoeff t =
   (let g = numgcd t
    in if g = 0 then C 0 else if g = 1 then t else reducecoeffh t g)"

fun dvdnumcoeff:: "num \<Rightarrow> int \<Rightarrow> bool"
where
  "dvdnumcoeff (C i) = (\<lambda>g. g dvd i)"
| "dvdnumcoeff (CN n c t) = (\<lambda>g. g dvd c \<and> dvdnumcoeff t g)"
| "dvdnumcoeff t = (\<lambda>g. False)"

lemma dvdnumcoeff_trans:
  assumes gdg: "g dvd g'"
    and dgt':"dvdnumcoeff t g'"
  shows "dvdnumcoeff t g"
  using dgt' gdg
  by (induct t rule: dvdnumcoeff.induct) (simp_all add: gdg dvd_trans[OF gdg])

declare dvd_trans [trans add]

lemma natabs0: "nat \<bar>x\<bar> = 0 \<longleftrightarrow> x = 0"
  by arith

lemma numgcd0:
  assumes g0: "numgcd t = 0"
  shows "Inum bs t = 0"
  using g0[simplified numgcd_def]
  by (induct t rule: numgcdh.induct) (auto simp add: natabs0 maxcoeff_pos max.absorb2)

lemma numgcdh_pos:
  assumes gp: "g \<ge> 0"
  shows "numgcdh t g \<ge> 0"
  using gp by (induct t rule: numgcdh.induct) auto

lemma numgcd_pos: "numgcd t \<ge>0"
  by (simp add: numgcd_def numgcdh_pos maxcoeff_pos)

lemma reducecoeffh:
  assumes gt: "dvdnumcoeff t g"
    and gp: "g > 0"
  shows "real_of_int g *(Inum bs (reducecoeffh t g)) = Inum bs t"
  using gt
proof (induct t rule: reducecoeffh.induct)
  case (1 i)
  then have gd: "g dvd i"
    by simp
  with assms show ?case
    by (simp add: real_of_int_div[OF gd])
next
  case (2 n c t)
  then have gd: "g dvd c"
    by simp
  from assms 2 show ?case
    by (simp add: real_of_int_div[OF gd] algebra_simps)
qed (auto simp add: numgcd_def gp)

fun ismaxcoeff:: "num \<Rightarrow> int \<Rightarrow> bool"
where
  "ismaxcoeff (C i) = (\<lambda>x. \<bar>i\<bar> \<le> x)"
| "ismaxcoeff (CN n c t) = (\<lambda>x. \<bar>c\<bar> \<le> x \<and> ismaxcoeff t x)"
| "ismaxcoeff t = (\<lambda>x. True)"

lemma ismaxcoeff_mono: "ismaxcoeff t c \<Longrightarrow> c \<le> c' \<Longrightarrow> ismaxcoeff t c'"
  by (induct t rule: ismaxcoeff.induct) auto

lemma maxcoeff_ismaxcoeff: "ismaxcoeff t (maxcoeff t)"
proof (induct t rule: maxcoeff.induct)
  case (2 n c t)
  then have H:"ismaxcoeff t (maxcoeff t)" .
  have thh: "maxcoeff t \<le> max \<bar>c\<bar> (maxcoeff t)"
    by simp
  from ismaxcoeff_mono[OF H thh] show ?case
    by simp
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
  assumes "ismaxcoeff t m"
    and mp: "m \<ge> 0"
    and "numgcdh t m > 1"
  shows "dvdnumcoeff t (numgcdh t m)"
  using assms
proof (induct t rule: numgcdh.induct)
  case (2 n c t)
  let ?g = "numgcdh t m"
  from 2 have th: "gcd c ?g > 1"
    by simp
  from zgcd_gt1[OF th] numgcdh_pos[OF mp, where t="t"]
  consider "\<bar>c\<bar> > 1" "?g > 1" | "\<bar>c\<bar> = 0" "?g > 1" | "?g = 0"
    by auto
  then show ?case
  proof cases
    case 1
    with 2 have th: "dvdnumcoeff t ?g"
      by simp
    have th': "gcd c ?g dvd ?g"
      by simp
    from dvdnumcoeff_trans[OF th' th] show ?thesis
      by simp
  next
    case "2'": 2
    with 2 have th: "dvdnumcoeff t ?g"
      by simp
    have th': "gcd c ?g dvd ?g"
      by simp
    from dvdnumcoeff_trans[OF th' th] show ?thesis
      by simp
  next
    case 3
    then have "m = 0" by (rule numgcdh0)
    with 2 3 show ?thesis by simp
  qed
qed auto

lemma dvdnumcoeff_aux2:
  assumes "numgcd t > 1"
  shows "dvdnumcoeff t (numgcd t) \<and> numgcd t > 0"
  using assms
proof (simp add: numgcd_def)
  let ?mc = "maxcoeff t"
  let ?g = "numgcdh t ?mc"
  have th1: "ismaxcoeff t ?mc"
    by (rule maxcoeff_ismaxcoeff)
  have th2: "?mc \<ge> 0"
    by (rule maxcoeff_pos)
  assume H: "numgcdh t ?mc > 1"
  from dvdnumcoeff_aux[OF th1 th2 H] show "dvdnumcoeff t ?g" .
qed

lemma reducecoeff: "real_of_int (numgcd t) * (Inum bs (reducecoeff t)) = Inum bs t"
proof -
  let ?g = "numgcd t"
  have "?g \<ge> 0"
    by (simp add: numgcd_pos)
  then consider "?g = 0" | "?g = 1" | "?g > 1" by atomize_elim auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (simp add: numgcd0)
  next
    case 2
    then show ?thesis by (simp add: reducecoeff_def)
  next
    case g1: 3
    from dvdnumcoeff_aux2[OF g1] have th1: "dvdnumcoeff t ?g" and g0: "?g > 0"
      by blast+
    from reducecoeffh[OF th1 g0, where bs="bs"] g1 show ?thesis
      by (simp add: reducecoeff_def Let_def)
  qed
qed

lemma reducecoeffh_numbound0: "numbound0 t \<Longrightarrow> numbound0 (reducecoeffh t g)"
  by (induct t rule: reducecoeffh.induct) auto

lemma reducecoeff_numbound0: "numbound0 t \<Longrightarrow> numbound0 (reducecoeff t)"
  using reducecoeffh_numbound0 by (simp add: reducecoeff_def Let_def)

fun numadd:: "num \<Rightarrow> num \<Rightarrow> num"
where
  "numadd (CN n1 c1 r1) (CN n2 c2 r2) =
   (if n1 = n2 then
    (let c = c1 + c2
     in (if c = 0 then numadd r1 r2 else CN n1 c (numadd r1 r2)))
    else if n1 \<le> n2 then (CN n1 c1 (numadd r1 (CN n2 c2 r2)))
    else (CN n2 c2 (numadd (CN n1 c1 r1) r2)))"
| "numadd (CN n1 c1 r1) t = CN n1 c1 (numadd r1 t)"
| "numadd t (CN n2 c2 r2) = CN n2 c2 (numadd t r2)"
| "numadd (C b1) (C b2) = C (b1 + b2)"
| "numadd a b = Add a b"

lemma numadd [simp]: "Inum bs (numadd t s) = Inum bs (Add t s)"
  by (induct t s rule: numadd.induct) (simp_all add: Let_def algebra_simps add_eq_0_iff)

lemma numadd_nb [simp]: "numbound0 t \<Longrightarrow> numbound0 s \<Longrightarrow> numbound0 (numadd t s)"
  by (induct t s rule: numadd.induct) (simp_all add: Let_def)

fun nummul:: "num \<Rightarrow> int \<Rightarrow> num"
where
  "nummul (C j) = (\<lambda>i. C (i * j))"
| "nummul (CN n c a) = (\<lambda>i. CN n (i * c) (nummul a i))"
| "nummul t = (\<lambda>i. Mul i t)"

lemma nummul[simp]: "\<And>i. Inum bs (nummul t i) = Inum bs (Mul i t)"
  by (induct t rule: nummul.induct) (auto simp add: algebra_simps)

lemma nummul_nb[simp]: "\<And>i. numbound0 t \<Longrightarrow> numbound0 (nummul t i)"
  by (induct t rule: nummul.induct) auto

definition numneg :: "num \<Rightarrow> num"
  where "numneg t = nummul t (- 1)"

definition numsub :: "num \<Rightarrow> num \<Rightarrow> num"
  where "numsub s t = (if s = t then C 0 else numadd s (numneg t))"

lemma numneg[simp]: "Inum bs (numneg t) = Inum bs (Neg t)"
  using numneg_def by simp

lemma numneg_nb[simp]: "numbound0 t \<Longrightarrow> numbound0 (numneg t)"
  using numneg_def by simp

lemma numsub[simp]: "Inum bs (numsub a b) = Inum bs (Sub a b)"
  using numsub_def by simp

lemma numsub_nb[simp]: "\<lbrakk> numbound0 t ; numbound0 s\<rbrakk> \<Longrightarrow> numbound0 (numsub t s)"
  using numsub_def by simp

primrec simpnum:: "num \<Rightarrow> num"
where
  "simpnum (C j) = C j"
| "simpnum (Bound n) = CN n 1 (C 0)"
| "simpnum (Neg t) = numneg (simpnum t)"
| "simpnum (Add t s) = numadd (simpnum t) (simpnum s)"
| "simpnum (Sub t s) = numsub (simpnum t) (simpnum s)"
| "simpnum (Mul i t) = (if i = 0 then C 0 else nummul (simpnum t) i)"
| "simpnum (CN n c t) = (if c = 0 then simpnum t else numadd (CN n c (C 0)) (simpnum t))"

lemma simpnum_ci[simp]: "Inum bs (simpnum t) = Inum bs t"
  by (induct t) simp_all

lemma simpnum_numbound0[simp]: "numbound0 t \<Longrightarrow> numbound0 (simpnum t)"
  by (induct t) simp_all

fun nozerocoeff:: "num \<Rightarrow> bool"
where
  "nozerocoeff (C c) = True"
| "nozerocoeff (CN n c t) = (c \<noteq> 0 \<and> nozerocoeff t)"
| "nozerocoeff t = True"

lemma numadd_nz : "nozerocoeff a \<Longrightarrow> nozerocoeff b \<Longrightarrow> nozerocoeff (numadd a b)"
  by (induct a b rule: numadd.induct) (simp_all add: Let_def)

lemma nummul_nz : "\<And>i. i\<noteq>0 \<Longrightarrow> nozerocoeff a \<Longrightarrow> nozerocoeff (nummul a i)"
  by (induct a rule: nummul.induct) (auto simp add: Let_def numadd_nz)

lemma numneg_nz : "nozerocoeff a \<Longrightarrow> nozerocoeff (numneg a)"
  by (simp add: numneg_def nummul_nz)

lemma numsub_nz: "nozerocoeff a \<Longrightarrow> nozerocoeff b \<Longrightarrow> nozerocoeff (numsub a b)"
  by (simp add: numsub_def numneg_nz numadd_nz)

lemma simpnum_nz: "nozerocoeff (simpnum t)"
  by (induct t) (simp_all add: numadd_nz numneg_nz numsub_nz nummul_nz)

lemma maxcoeff_nz: "nozerocoeff t \<Longrightarrow> maxcoeff t = 0 \<Longrightarrow> t = C 0"
  by (induction t rule: maxcoeff.induct) auto

lemma numgcd_nz:
  assumes nz: "nozerocoeff t"
    and g0: "numgcd t = 0"
  shows "t = C 0"
proof -
  from g0 have th:"numgcdh t (maxcoeff t) = 0"
    by (simp add: numgcd_def)
  from numgcdh0[OF th] have th:"maxcoeff t = 0" .
  from maxcoeff_nz[OF nz th] show ?thesis .
qed

definition simp_num_pair :: "(num \<times> int) \<Rightarrow> num \<times> int"
where
  "simp_num_pair =
    (\<lambda>(t,n).
     (if n = 0 then (C 0, 0)
      else
       (let t' = simpnum t ; g = numgcd t' in
         if g > 1 then
          (let g' = gcd n g
           in if g' = 1 then (t', n) else (reducecoeffh t' g', n div g'))
         else (t', n))))"

lemma simp_num_pair_ci:
  shows "((\<lambda>(t,n). Inum bs t / real_of_int n) (simp_num_pair (t,n))) =
    ((\<lambda>(t,n). Inum bs t / real_of_int n) (t, n))"
  (is "?lhs = ?rhs")
proof -
  let ?t' = "simpnum t"
  let ?g = "numgcd ?t'"
  let ?g' = "gcd n ?g"
  show ?thesis
  proof (cases "n = 0")
    case True
    then show ?thesis
      by (simp add: Let_def simp_num_pair_def)
  next
    case nnz: False
    show ?thesis
    proof (cases "?g > 1")
      case False
      then show ?thesis by (simp add: Let_def simp_num_pair_def)
    next
      case g1: True
      then have g0: "?g > 0"
        by simp
      from g1 nnz have gp0: "?g' \<noteq> 0"
        by simp
      then have g'p: "?g' > 0"
        using gcd_ge_0_int[where x="n" and y="numgcd ?t'"] by arith
      then consider "?g' = 1" | "?g' > 1" by arith
      then show ?thesis
      proof cases
        case 1
        then show ?thesis
          by (simp add: Let_def simp_num_pair_def)
      next
        case g'1: 2
        from dvdnumcoeff_aux2[OF g1] have th1: "dvdnumcoeff ?t' ?g" ..
        let ?tt = "reducecoeffh ?t' ?g'"
        let ?t = "Inum bs ?tt"
        have gpdg: "?g' dvd ?g" by simp
        have gpdd: "?g' dvd n" by simp
        have gpdgp: "?g' dvd ?g'" by simp
        from reducecoeffh[OF dvdnumcoeff_trans[OF gpdg th1] g'p]
        have th2:"real_of_int ?g' * ?t = Inum bs ?t'"
          by simp
        from g1 g'1 have "?lhs = ?t / real_of_int (n div ?g')"
          by (simp add: simp_num_pair_def Let_def)
        also have "\<dots> = (real_of_int ?g' * ?t) / (real_of_int ?g' * (real_of_int (n div ?g')))"
          by simp
        also have "\<dots> = (Inum bs ?t' / real_of_int n)"
          using real_of_int_div[OF gpdd] th2 gp0 by simp
        finally have "?lhs = Inum bs t / real_of_int n"
          by simp
        then show ?thesis
          by (simp add: simp_num_pair_def)
      qed
    qed
  qed
qed

lemma simp_num_pair_l:
  assumes tnb: "numbound0 t"
    and np: "n > 0"
    and tn: "simp_num_pair (t, n) = (t', n')"
  shows "numbound0 t' \<and> n' > 0"
proof -
  let ?t' = "simpnum t"
  let ?g = "numgcd ?t'"
  let ?g' = "gcd n ?g"
  show ?thesis
  proof (cases "n = 0")
    case True
    then show ?thesis
      using assms by (simp add: Let_def simp_num_pair_def)
  next
    case nnz: False
    show ?thesis
    proof (cases "?g > 1")
      case False
      then show ?thesis
        using assms by (auto simp add: Let_def simp_num_pair_def)
    next
      case g1: True
      then have g0: "?g > 0" by simp
      from g1 nnz have gp0: "?g' \<noteq> 0" by simp
      then have g'p: "?g' > 0" using gcd_ge_0_int[where x="n" and y="numgcd ?t'"]
        by arith
      then consider "?g'= 1" | "?g' > 1" by arith
      then show ?thesis
      proof cases
        case 1
        then show ?thesis
          using assms g1 by (auto simp add: Let_def simp_num_pair_def)
      next
        case g'1: 2
        have gpdg: "?g' dvd ?g" by simp
        have gpdd: "?g' dvd n" by simp
        have gpdgp: "?g' dvd ?g'" by simp
        from zdvd_imp_le[OF gpdd np] have g'n: "?g' \<le> n" .
        from zdiv_mono1[OF g'n g'p, simplified div_self[OF gp0]] have "n div ?g' > 0"
          by simp
        then show ?thesis
          using assms g1 g'1
          by (auto simp add: simp_num_pair_def Let_def reducecoeffh_numbound0)
      qed
    qed
  qed
qed

fun simpfm :: "fm \<Rightarrow> fm"
where
  "simpfm (And p q) = conj (simpfm p) (simpfm q)"
| "simpfm (Or p q) = disj (simpfm p) (simpfm q)"
| "simpfm (Imp p q) = imp (simpfm p) (simpfm q)"
| "simpfm (Iff p q) = iff (simpfm p) (simpfm q)"
| "simpfm (NOT p) = not (simpfm p)"
| "simpfm (Lt a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v < 0) then T else F | _ \<Rightarrow> Lt a')"
| "simpfm (Le a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v \<le> 0)  then T else F | _ \<Rightarrow> Le a')"
| "simpfm (Gt a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v > 0)  then T else F | _ \<Rightarrow> Gt a')"
| "simpfm (Ge a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v \<ge> 0)  then T else F | _ \<Rightarrow> Ge a')"
| "simpfm (Eq a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v = 0)  then T else F | _ \<Rightarrow> Eq a')"
| "simpfm (NEq a) = (let a' = simpnum a in case a' of C v \<Rightarrow> if (v \<noteq> 0)  then T else F | _ \<Rightarrow> NEq a')"
| "simpfm p = p"

lemma simpfm: "Ifm bs (simpfm p) = Ifm bs p"
proof (induct p rule: simpfm.induct)
  case (6 a)
  let ?sa = "simpnum a"
  from simpnum_ci have sa: "Inum bs ?sa = Inum bs a"
    by simp
  consider v where "?sa = C v" | "\<not> (\<exists>v. ?sa = C v)" by blast
  then show ?case
  proof cases
    case 1
    then show ?thesis using sa by simp
  next
    case 2
    then show ?thesis using sa by (cases ?sa) (simp_all add: Let_def)
  qed
next
  case (7 a)
  let ?sa = "simpnum a"
  from simpnum_ci have sa: "Inum bs ?sa = Inum bs a"
    by simp
  consider v where "?sa = C v" | "\<not> (\<exists>v. ?sa = C v)" by blast
  then show ?case
  proof cases
    case 1
    then show ?thesis using sa by simp
  next
    case 2
    then show ?thesis using sa by (cases ?sa) (simp_all add: Let_def)
  qed
next
  case (8 a)
  let ?sa = "simpnum a"
  from simpnum_ci have sa: "Inum bs ?sa = Inum bs a"
    by simp
  consider v where "?sa = C v" | "\<not> (\<exists>v. ?sa = C v)" by blast
  then show ?case
  proof cases
    case 1
    then show ?thesis using sa by simp
  next
    case 2
    then show ?thesis using sa by (cases ?sa) (simp_all add: Let_def)
  qed
next
  case (9 a)
  let ?sa = "simpnum a"
  from simpnum_ci have sa: "Inum bs ?sa = Inum bs a"
    by simp
  consider v where "?sa = C v" | "\<not> (\<exists>v. ?sa = C v)" by blast
  then show ?case
  proof cases
    case 1
    then show ?thesis using sa by simp
  next
    case 2
    then show ?thesis using sa by (cases ?sa) (simp_all add: Let_def)
  qed
next
  case (10 a)
  let ?sa = "simpnum a"
  from simpnum_ci have sa: "Inum bs ?sa = Inum bs a"
    by simp
  consider v where "?sa = C v" | "\<not> (\<exists>v. ?sa = C v)" by blast
  then show ?case
  proof cases
    case 1
    then show ?thesis using sa by simp
  next
    case 2
    then show ?thesis using sa by (cases ?sa) (simp_all add: Let_def)
  qed
next
  case (11 a)
  let ?sa = "simpnum a"
  from simpnum_ci have sa: "Inum bs ?sa = Inum bs a"
    by simp
  consider v where "?sa = C v" | "\<not> (\<exists>v. ?sa = C v)" by blast
  then show ?case
  proof cases
    case 1
    then show ?thesis using sa by simp
  next
    case 2
    then show ?thesis using sa by (cases ?sa) (simp_all add: Let_def)
  qed
qed (induct p rule: simpfm.induct, simp_all)


lemma simpfm_bound0: "bound0 p \<Longrightarrow> bound0 (simpfm p)"
proof (induct p rule: simpfm.induct)
  case (6 a)
  then have nb: "numbound0 a" by simp
  then have "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  then show ?case by (cases "simpnum a") (auto simp add: Let_def)
next
  case (7 a)
  then have nb: "numbound0 a" by simp
  then have "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  then show ?case by (cases "simpnum a") (auto simp add: Let_def)
next
  case (8 a)
  then have nb: "numbound0 a" by simp
  then have "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  then show ?case by (cases "simpnum a") (auto simp add: Let_def)
next
  case (9 a)
  then have nb: "numbound0 a" by simp
  then have "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  then show ?case by (cases "simpnum a") (auto simp add: Let_def)
next
  case (10 a)
  then have nb: "numbound0 a" by simp
  then have "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  then show ?case by (cases "simpnum a") (auto simp add: Let_def)
next
  case (11 a)
  then have nb: "numbound0 a" by simp
  then have "numbound0 (simpnum a)" by (simp only: simpnum_numbound0[OF nb])
  then show ?case by (cases "simpnum a") (auto simp add: Let_def)
qed (auto simp add: disj_def imp_def iff_def conj_def)

lemma simpfm_qf: "qfree p \<Longrightarrow> qfree (simpfm p)"
  apply (induct p rule: simpfm.induct)
  apply (auto simp add: Let_def)
  apply (case_tac "simpnum a", auto)+
  done

fun prep :: "fm \<Rightarrow> fm"
where
  "prep (E T) = T"
| "prep (E F) = F"
| "prep (E (Or p q)) = disj (prep (E p)) (prep (E q))"
| "prep (E (Imp p q)) = disj (prep (E (NOT p))) (prep (E q))"
| "prep (E (Iff p q)) = disj (prep (E (And p q))) (prep (E (And (NOT p) (NOT q))))"
| "prep (E (NOT (And p q))) = disj (prep (E (NOT p))) (prep (E(NOT q)))"
| "prep (E (NOT (Imp p q))) = prep (E (And p (NOT q)))"
| "prep (E (NOT (Iff p q))) = disj (prep (E (And p (NOT q)))) (prep (E(And (NOT p) q)))"
| "prep (E p) = E (prep p)"
| "prep (A (And p q)) = conj (prep (A p)) (prep (A q))"
| "prep (A p) = prep (NOT (E (NOT p)))"
| "prep (NOT (NOT p)) = prep p"
| "prep (NOT (And p q)) = disj (prep (NOT p)) (prep (NOT q))"
| "prep (NOT (A p)) = prep (E (NOT p))"
| "prep (NOT (Or p q)) = conj (prep (NOT p)) (prep (NOT q))"
| "prep (NOT (Imp p q)) = conj (prep p) (prep (NOT q))"
| "prep (NOT (Iff p q)) = disj (prep (And p (NOT q))) (prep (And (NOT p) q))"
| "prep (NOT p) = not (prep p)"
| "prep (Or p q) = disj (prep p) (prep q)"
| "prep (And p q) = conj (prep p) (prep q)"
| "prep (Imp p q) = prep (Or (NOT p) q)"
| "prep (Iff p q) = disj (prep (And p q)) (prep (And (NOT p) (NOT q)))"
| "prep p = p"

lemma prep: "\<And>bs. Ifm bs (prep p) = Ifm bs p"
  by (induct p rule: prep.induct) auto

  (* Generic quantifier elimination *)
fun qelim :: "fm \<Rightarrow> (fm \<Rightarrow> fm) \<Rightarrow> fm"
where
  "qelim (E p) = (\<lambda>qe. DJ qe (qelim p qe))"
| "qelim (A p) = (\<lambda>qe. not (qe ((qelim (NOT p) qe))))"
| "qelim (NOT p) = (\<lambda>qe. not (qelim p qe))"
| "qelim (And p q) = (\<lambda>qe. conj (qelim p qe) (qelim q qe))"
| "qelim (Or  p q) = (\<lambda>qe. disj (qelim p qe) (qelim q qe))"
| "qelim (Imp p q) = (\<lambda>qe. imp (qelim p qe) (qelim q qe))"
| "qelim (Iff p q) = (\<lambda>qe. iff (qelim p qe) (qelim q qe))"
| "qelim p = (\<lambda>y. simpfm p)"

lemma qelim_ci:
  assumes qe_inv: "\<forall>bs p. qfree p \<longrightarrow> qfree (qe p) \<and> (Ifm bs (qe p) = Ifm bs (E p))"
  shows "\<And>bs. qfree (qelim p qe) \<and> (Ifm bs (qelim p qe) = Ifm bs p)"
  using qe_inv DJ_qe[OF qe_inv]
  by (induct p rule: qelim.induct)
    (auto simp add: simpfm simpfm_qf simp del: simpfm.simps)

fun minusinf:: "fm \<Rightarrow> fm" (* Virtual substitution of -\<infinity>*)
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

fun plusinf:: "fm \<Rightarrow> fm" (* Virtual substitution of +\<infinity>*)
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

  (* splits the bounded from the unbounded part*)
fun rsplit0 :: "num \<Rightarrow> int \<times> num"
where
  "rsplit0 (Bound 0) = (1,C 0)"
| "rsplit0 (Add a b) = (let (ca,ta) = rsplit0 a; (cb,tb) = rsplit0 b in (ca + cb, Add ta tb))"
| "rsplit0 (Sub a b) = rsplit0 (Add a (Neg b))"
| "rsplit0 (Neg a) = (let (c,t) = rsplit0 a in (- c, Neg t))"
| "rsplit0 (Mul c a) = (let (ca,ta) = rsplit0 a in (c * ca, Mul c ta))"
| "rsplit0 (CN 0 c a) = (let (ca,ta) = rsplit0 a in (c + ca, ta))"
| "rsplit0 (CN n c a) = (let (ca,ta) = rsplit0 a in (ca, CN n c ta))"
| "rsplit0 t = (0,t)"

lemma rsplit0: "Inum bs ((case_prod (CN 0)) (rsplit0 t)) = Inum bs t \<and> numbound0 (snd (rsplit0 t))"
proof (induct t rule: rsplit0.induct)
  case (2 a b)
  let ?sa = "rsplit0 a"
  let ?sb = "rsplit0 b"
  let ?ca = "fst ?sa"
  let ?cb = "fst ?sb"
  let ?ta = "snd ?sa"
  let ?tb = "snd ?sb"
  from 2 have nb: "numbound0 (snd(rsplit0 (Add a b)))"
    by (cases "rsplit0 a") (auto simp add: Let_def split_def)
  have "Inum bs ((case_prod (CN 0)) (rsplit0 (Add a b))) =
    Inum bs ((case_prod (CN 0)) ?sa)+Inum bs ((case_prod (CN 0)) ?sb)"
    by (simp add: Let_def split_def algebra_simps)
  also have "\<dots> = Inum bs a + Inum bs b"
    using 2 by (cases "rsplit0 a") auto
  finally show ?case
    using nb by simp
qed (auto simp add: Let_def split_def algebra_simps, simp add: distrib_left[symmetric])

    (* Linearize a formula*)
definition lt :: "int \<Rightarrow> num \<Rightarrow> fm"
where
  "lt c t = (if c = 0 then (Lt t) else if c > 0 then (Lt (CN 0 c t))
    else (Gt (CN 0 (-c) (Neg t))))"

definition le :: "int \<Rightarrow> num \<Rightarrow> fm"
where
  "le c t = (if c = 0 then (Le t) else if c > 0 then (Le (CN 0 c t))
    else (Ge (CN 0 (-c) (Neg t))))"

definition gt :: "int \<Rightarrow> num \<Rightarrow> fm"
where
  "gt c t = (if c = 0 then (Gt t) else if c > 0 then (Gt (CN 0 c t))
    else (Lt (CN 0 (-c) (Neg t))))"

definition ge :: "int \<Rightarrow> num \<Rightarrow> fm"
where
  "ge c t = (if c = 0 then (Ge t) else if c > 0 then (Ge (CN 0 c t))
    else (Le (CN 0 (-c) (Neg t))))"

definition eq :: "int \<Rightarrow> num \<Rightarrow> fm"
where
  "eq c t = (if c = 0 then (Eq t) else if c > 0 then (Eq (CN 0 c t))
    else (Eq (CN 0 (-c) (Neg t))))"

definition neq :: "int \<Rightarrow> num \<Rightarrow> fm"
where
  "neq c t = (if c = 0 then (NEq t) else if c > 0 then (NEq (CN 0 c t))
    else (NEq (CN 0 (-c) (Neg t))))"

lemma lt: "numnoabs t \<Longrightarrow> Ifm bs (case_prod lt (rsplit0 t)) =
  Ifm bs (Lt t) \<and> isrlfm (case_prod lt (rsplit0 t))"
  using rsplit0[where bs = "bs" and t="t"]
  by (auto simp add: lt_def split_def, cases "snd(rsplit0 t)", auto,
    rename_tac nat a b, case_tac "nat", auto)

lemma le: "numnoabs t \<Longrightarrow> Ifm bs (case_prod le (rsplit0 t)) =
  Ifm bs (Le t) \<and> isrlfm (case_prod le (rsplit0 t))"
  using rsplit0[where bs = "bs" and t="t"]
  by (auto simp add: le_def split_def, cases "snd(rsplit0 t)", auto,
    rename_tac nat a b, case_tac "nat", auto)

lemma gt: "numnoabs t \<Longrightarrow> Ifm bs (case_prod gt (rsplit0 t)) =
  Ifm bs (Gt t) \<and> isrlfm (case_prod gt (rsplit0 t))"
  using rsplit0[where bs = "bs" and t="t"]
  by (auto simp add: gt_def split_def, cases "snd(rsplit0 t)", auto,
    rename_tac nat a b, case_tac "nat", auto)

lemma ge: "numnoabs t \<Longrightarrow> Ifm bs (case_prod ge (rsplit0 t)) =
  Ifm bs (Ge t) \<and> isrlfm (case_prod ge (rsplit0 t))"
  using rsplit0[where bs = "bs" and t="t"]
  by (auto simp add: ge_def split_def, cases "snd(rsplit0 t)", auto,
    rename_tac nat a b, case_tac "nat", auto)

lemma eq: "numnoabs t \<Longrightarrow> Ifm bs (case_prod eq (rsplit0 t)) =
  Ifm bs (Eq t) \<and> isrlfm (case_prod eq (rsplit0 t))"
  using rsplit0[where bs = "bs" and t="t"]
  by (auto simp add: eq_def split_def, cases "snd(rsplit0 t)", auto,
    rename_tac nat a b, case_tac "nat", auto)

lemma neq: "numnoabs t \<Longrightarrow> Ifm bs (case_prod neq (rsplit0 t)) =
  Ifm bs (NEq t) \<and> isrlfm (case_prod neq (rsplit0 t))"
  using rsplit0[where bs = "bs" and t="t"]
  by (auto simp add: neq_def split_def, cases "snd(rsplit0 t)", auto,
    rename_tac nat a b, case_tac "nat", auto)

lemma conj_lin: "isrlfm p \<Longrightarrow> isrlfm q \<Longrightarrow> isrlfm (conj p q)"
  by (auto simp add: conj_def)

lemma disj_lin: "isrlfm p \<Longrightarrow> isrlfm q \<Longrightarrow> isrlfm (disj p q)"
  by (auto simp add: disj_def)

fun rlfm :: "fm \<Rightarrow> fm"
where
  "rlfm (And p q) = conj (rlfm p) (rlfm q)"
| "rlfm (Or p q) = disj (rlfm p) (rlfm q)"
| "rlfm (Imp p q) = disj (rlfm (NOT p)) (rlfm q)"
| "rlfm (Iff p q) = disj (conj (rlfm p) (rlfm q)) (conj (rlfm (NOT p)) (rlfm (NOT q)))"
| "rlfm (Lt a) = case_prod lt (rsplit0 a)"
| "rlfm (Le a) = case_prod le (rsplit0 a)"
| "rlfm (Gt a) = case_prod gt (rsplit0 a)"
| "rlfm (Ge a) = case_prod ge (rsplit0 a)"
| "rlfm (Eq a) = case_prod eq (rsplit0 a)"
| "rlfm (NEq a) = case_prod neq (rsplit0 a)"
| "rlfm (NOT (And p q)) = disj (rlfm (NOT p)) (rlfm (NOT q))"
| "rlfm (NOT (Or p q)) = conj (rlfm (NOT p)) (rlfm (NOT q))"
| "rlfm (NOT (Imp p q)) = conj (rlfm p) (rlfm (NOT q))"
| "rlfm (NOT (Iff p q)) = disj (conj(rlfm p) (rlfm(NOT q))) (conj(rlfm(NOT p)) (rlfm q))"
| "rlfm (NOT (NOT p)) = rlfm p"
| "rlfm (NOT T) = F"
| "rlfm (NOT F) = T"
| "rlfm (NOT (Lt a)) = rlfm (Ge a)"
| "rlfm (NOT (Le a)) = rlfm (Gt a)"
| "rlfm (NOT (Gt a)) = rlfm (Le a)"
| "rlfm (NOT (Ge a)) = rlfm (Lt a)"
| "rlfm (NOT (Eq a)) = rlfm (NEq a)"
| "rlfm (NOT (NEq a)) = rlfm (Eq a)"
| "rlfm p = p"

lemma rlfm_I:
  assumes qfp: "qfree p"
  shows "(Ifm bs (rlfm p) = Ifm bs p) \<and> isrlfm (rlfm p)"
  using qfp
  by (induct p rule: rlfm.induct) (auto simp add: lt le gt ge eq neq conj_lin disj_lin)

    (* Operations needed for Ferrante and Rackoff *)
lemma rminusinf_inf:
  assumes lp: "isrlfm p"
  shows "\<exists>z. \<forall>x < z. Ifm (x#bs) (minusinf p) = Ifm (x#bs) p" (is "\<exists>z. \<forall>x. ?P z x p")
  using lp
proof (induct p rule: minusinf.induct)
  case (1 p q)
  then show ?case
    apply auto
    apply (rule_tac x= "min z za" in exI)
    apply auto
    done
next
  case (2 p q)
  then show ?case
    apply auto
    apply (rule_tac x= "min z za" in exI)
    apply auto
    done
next
  case (3 c e)
  from 3 have nb: "numbound0 e" by simp
  from 3 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e = "Inum (a#bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {
    fix x
    assume xz: "x < ?z"
    then have "(real_of_int c * x < - ?e)"
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] ac_simps)
    then have "real_of_int c * x + ?e < 0" by arith
    then have "real_of_int c * x + ?e \<noteq> 0" by simp
    with xz have "?P ?z x (Eq (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp
  }
  then have "\<forall>x < ?z. ?P ?z x (Eq (CN 0 c e))" by simp
  then show ?case by blast
next
  case (4 c e)
  from 4 have nb: "numbound0 e" by simp
  from 4 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e = "Inum (a # bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {
    fix x
    assume xz: "x < ?z"
    then have "(real_of_int c * x < - ?e)"
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] ac_simps)
    then have "real_of_int c * x + ?e < 0" by arith
    then have "real_of_int c * x + ?e \<noteq> 0" by simp
    with xz have "?P ?z x (NEq (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp
  }
  then have "\<forall>x < ?z. ?P ?z x (NEq (CN 0 c e))" by simp
  then show ?case by blast
next
  case (5 c e)
  from 5 have nb: "numbound0 e" by simp
  from 5 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {
    fix x
    assume xz: "x < ?z"
    then have "(real_of_int c * x < - ?e)"
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] ac_simps)
    then have "real_of_int c * x + ?e < 0" by arith
    with xz have "?P ?z x (Lt (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"]  by simp
  }
  then have "\<forall>x < ?z. ?P ?z x (Lt (CN 0 c e))" by simp
  then show ?case by blast
next
  case (6 c e)
  from 6 have nb: "numbound0 e" by simp
  from lp 6 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e = "Inum (a # bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {
    fix x
    assume xz: "x < ?z"
    then have "(real_of_int c * x < - ?e)"
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] ac_simps)
    then have "real_of_int c * x + ?e < 0" by arith
    with xz have "?P ?z x (Le (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp
  }
  then have "\<forall>x < ?z. ?P ?z x (Le (CN 0 c e))" by simp
  then show ?case by blast
next
  case (7 c e)
  from 7 have nb: "numbound0 e" by simp
  from 7 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e = "Inum (a # bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {
    fix x
    assume xz: "x < ?z"
    then have "(real_of_int c * x < - ?e)"
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] ac_simps)
    then have "real_of_int c * x + ?e < 0" by arith
    with xz have "?P ?z x (Gt (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp
  }
  then have "\<forall>x < ?z. ?P ?z x (Gt (CN 0 c e))" by simp
  then show ?case by blast
next
  case (8 c e)
  from 8 have nb: "numbound0 e" by simp
  from 8 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {
    fix x
    assume xz: "x < ?z"
    then have "(real_of_int c * x < - ?e)"
      by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="- ?e"] ac_simps)
    then have "real_of_int c * x + ?e < 0" by arith
    with xz have "?P ?z x (Ge (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp
  }
  then have "\<forall>x < ?z. ?P ?z x (Ge (CN 0 c e))" by simp
  then show ?case by blast
qed simp_all

lemma rplusinf_inf:
  assumes lp: "isrlfm p"
  shows "\<exists>z. \<forall>x > z. Ifm (x#bs) (plusinf p) = Ifm (x#bs) p" (is "\<exists>z. \<forall>x. ?P z x p")
using lp
proof (induct p rule: isrlfm.induct)
  case (1 p q)
  then show ?case
    apply auto
    apply (rule_tac x= "max z za" in exI)
    apply auto
    done
next
  case (2 p q)
  then show ?case
    apply auto
    apply (rule_tac x= "max z za" in exI)
    apply auto
    done
next
  case (3 c e)
  from 3 have nb: "numbound0 e" by simp
  from 3 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e = "Inum (a # bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {
    fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real_of_int c * x > - ?e)" by (simp add: ac_simps)
    then have "real_of_int c * x + ?e > 0" by arith
    then have "real_of_int c * x + ?e \<noteq> 0" by simp
    with xz have "?P ?z x (Eq (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp
  }
  then have "\<forall>x > ?z. ?P ?z x (Eq (CN 0 c e))" by simp
  then show ?case by blast
next
  case (4 c e)
  from 4 have nb: "numbound0 e" by simp
  from 4 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e = "Inum (a # bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {
    fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real_of_int c * x > - ?e)" by (simp add: ac_simps)
    then have "real_of_int c * x + ?e > 0" by arith
    then have "real_of_int c * x + ?e \<noteq> 0" by simp
    with xz have "?P ?z x (NEq (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp
  }
  then have "\<forall>x > ?z. ?P ?z x (NEq (CN 0 c e))" by simp
  then show ?case by blast
next
  case (5 c e)
  from 5 have nb: "numbound0 e" by simp
  from 5 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e = "Inum (a # bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {
    fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real_of_int c * x > - ?e)" by (simp add: ac_simps)
    then have "real_of_int c * x + ?e > 0" by arith
    with xz have "?P ?z x (Lt (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp
  }
  then have "\<forall>x > ?z. ?P ?z x (Lt (CN 0 c e))" by simp
  then show ?case by blast
next
  case (6 c e)
  from 6 have nb: "numbound0 e" by simp
  from 6 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e = "Inum (a # bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {
    fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real_of_int c * x > - ?e)" by (simp add: ac_simps)
    then have "real_of_int c * x + ?e > 0" by arith
    with xz have "?P ?z x (Le (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp
  }
  then have "\<forall>x > ?z. ?P ?z x (Le (CN 0 c e))" by simp
  then show ?case by blast
next
  case (7 c e)
  from 7 have nb: "numbound0 e" by simp
  from 7 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e = "Inum (a # bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {
    fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real_of_int c * x > - ?e)" by (simp add: ac_simps)
    then have "real_of_int c * x + ?e > 0" by arith
    with xz have "?P ?z x (Gt (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp
  }
  then have "\<forall>x > ?z. ?P ?z x (Gt (CN 0 c e))" by simp
  then show ?case by blast
next
  case (8 c e)
  from 8 have nb: "numbound0 e" by simp
  from 8 have cp: "real_of_int c > 0" by simp
  fix a
  let ?e="Inum (a#bs) e"
  let ?z = "(- ?e) / real_of_int c"
  {
    fix x
    assume xz: "x > ?z"
    with mult_strict_right_mono [OF xz cp] cp
    have "(real_of_int c * x > - ?e)" by (simp add: ac_simps)
    then have "real_of_int c * x + ?e > 0" by arith
    with xz have "?P ?z x (Ge (CN 0 c e))"
      using numbound0_I[OF nb, where b="x" and bs="bs" and b'="a"] by simp
  }
  then have "\<forall>x > ?z. ?P ?z x (Ge (CN 0 c e))" by simp
  then show ?case by blast
qed simp_all

lemma rminusinf_bound0:
  assumes lp: "isrlfm p"
  shows "bound0 (minusinf p)"
  using lp by (induct p rule: minusinf.induct) simp_all

lemma rplusinf_bound0:
  assumes lp: "isrlfm p"
  shows "bound0 (plusinf p)"
  using lp by (induct p rule: plusinf.induct) simp_all

lemma rminusinf_ex:
  assumes lp: "isrlfm p"
    and ex: "Ifm (a#bs) (minusinf p)"
  shows "\<exists>x. Ifm (x#bs) p"
proof -
  from bound0_I [OF rminusinf_bound0[OF lp], where b="a" and bs ="bs"] ex
  have th: "\<forall>x. Ifm (x#bs) (minusinf p)" by auto
  from rminusinf_inf[OF lp, where bs="bs"]
  obtain z where z_def: "\<forall>x<z. Ifm (x # bs) (minusinf p) = Ifm (x # bs) p" by blast
  from th have "Ifm ((z - 1) # bs) (minusinf p)" by simp
  moreover have "z - 1 < z" by simp
  ultimately show ?thesis using z_def by auto
qed

lemma rplusinf_ex:
  assumes lp: "isrlfm p"
    and ex: "Ifm (a # bs) (plusinf p)"
  shows "\<exists>x. Ifm (x # bs) p"
proof -
  from bound0_I [OF rplusinf_bound0[OF lp], where b="a" and bs ="bs"] ex
  have th: "\<forall>x. Ifm (x # bs) (plusinf p)" by auto
  from rplusinf_inf[OF lp, where bs="bs"]
  obtain z where z_def: "\<forall>x>z. Ifm (x # bs) (plusinf p) = Ifm (x # bs) p" by blast
  from th have "Ifm ((z + 1) # bs) (plusinf p)" by simp
  moreover have "z + 1 > z" by simp
  ultimately show ?thesis using z_def by auto
qed

fun uset :: "fm \<Rightarrow> (num \<times> int) list"
where
  "uset (And p q) = (uset p @ uset q)"
| "uset (Or p q) = (uset p @ uset q)"
| "uset (Eq  (CN 0 c e)) = [(Neg e,c)]"
| "uset (NEq (CN 0 c e)) = [(Neg e,c)]"
| "uset (Lt  (CN 0 c e)) = [(Neg e,c)]"
| "uset (Le  (CN 0 c e)) = [(Neg e,c)]"
| "uset (Gt  (CN 0 c e)) = [(Neg e,c)]"
| "uset (Ge  (CN 0 c e)) = [(Neg e,c)]"
| "uset p = []"

fun usubst :: "fm \<Rightarrow> num \<times> int \<Rightarrow> fm"
where
  "usubst (And p q) = (\<lambda>(t,n). And (usubst p (t,n)) (usubst q (t,n)))"
| "usubst (Or p q) = (\<lambda>(t,n). Or (usubst p (t,n)) (usubst q (t,n)))"
| "usubst (Eq (CN 0 c e)) = (\<lambda>(t,n). Eq (Add (Mul c t) (Mul n e)))"
| "usubst (NEq (CN 0 c e)) = (\<lambda>(t,n). NEq (Add (Mul c t) (Mul n e)))"
| "usubst (Lt (CN 0 c e)) = (\<lambda>(t,n). Lt (Add (Mul c t) (Mul n e)))"
| "usubst (Le (CN 0 c e)) = (\<lambda>(t,n). Le (Add (Mul c t) (Mul n e)))"
| "usubst (Gt (CN 0 c e)) = (\<lambda>(t,n). Gt (Add (Mul c t) (Mul n e)))"
| "usubst (Ge (CN 0 c e)) = (\<lambda>(t,n). Ge (Add (Mul c t) (Mul n e)))"
| "usubst p = (\<lambda>(t, n). p)"

lemma usubst_I:
  assumes lp: "isrlfm p"
    and np: "real_of_int n > 0"
    and nbt: "numbound0 t"
  shows "(Ifm (x # bs) (usubst p (t,n)) =
    Ifm (((Inum (x # bs) t) / (real_of_int n)) # bs) p) \<and> bound0 (usubst p (t, n))"
  (is "(?I x (usubst p (t, n)) = ?I ?u p) \<and> ?B p"
   is "(_ = ?I (?t/?n) p) \<and> _"
   is "(_ = ?I (?N x t /_) p) \<and> _")
  using lp
proof (induct p rule: usubst.induct)
  case (5 c e)
  with assms have cp: "c > 0" and nb: "numbound0 e" by simp_all
  have "?I ?u (Lt (CN 0 c e)) \<longleftrightarrow> real_of_int c * (?t / ?n) + ?N x e < 0"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> \<longleftrightarrow> ?n * (real_of_int c * (?t / ?n)) + ?n*(?N x e) < 0"
    by (simp only: pos_less_divide_eq[OF np, where a="real_of_int c *(?t/?n) + (?N x e)"
      and b="0", simplified div_0]) (simp only: algebra_simps)
  also have "\<dots> \<longleftrightarrow> real_of_int c * ?t + ?n * (?N x e) < 0" using np by simp
  finally show ?case using nbt nb by (simp add: algebra_simps)
next
  case (6 c e)
  with assms have cp: "c > 0" and nb: "numbound0 e" by simp_all
  have "?I ?u (Le (CN 0 c e)) \<longleftrightarrow> real_of_int c * (?t / ?n) + ?N x e \<le> 0"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> = (?n*(real_of_int c *(?t/?n)) + ?n*(?N x e) \<le> 0)"
    by (simp only: pos_le_divide_eq[OF np, where a="real_of_int c *(?t/?n) + (?N x e)"
      and b="0", simplified div_0]) (simp only: algebra_simps)
  also have "\<dots> = (real_of_int c *?t + ?n* (?N x e) \<le> 0)" using np by simp
  finally show ?case using nbt nb by (simp add: algebra_simps)
next
  case (7 c e)
  with assms have cp: "c >0" and nb: "numbound0 e" by simp_all
  have "?I ?u (Gt (CN 0 c e)) \<longleftrightarrow> real_of_int c *(?t / ?n) + ?N x e > 0"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> \<longleftrightarrow> ?n * (real_of_int c * (?t / ?n)) + ?n * ?N x e > 0"
    by (simp only: pos_divide_less_eq[OF np, where a="real_of_int c *(?t/?n) + (?N x e)"
      and b="0", simplified div_0]) (simp only: algebra_simps)
  also have "\<dots> \<longleftrightarrow> real_of_int c * ?t + ?n * ?N x e > 0" using np by simp
  finally show ?case using nbt nb by (simp add: algebra_simps)
next
  case (8 c e)
  with assms have cp: "c > 0" and nb: "numbound0 e" by simp_all
  have "?I ?u (Ge (CN 0 c e)) \<longleftrightarrow> real_of_int c * (?t / ?n) + ?N x e \<ge> 0"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> \<longleftrightarrow> ?n * (real_of_int c * (?t / ?n)) + ?n * ?N x e \<ge> 0"
    by (simp only: pos_divide_le_eq[OF np, where a="real_of_int c *(?t/?n) + (?N x e)"
      and b="0", simplified div_0]) (simp only: algebra_simps)
  also have "\<dots> \<longleftrightarrow> real_of_int c * ?t + ?n * ?N x e \<ge> 0" using np by simp
  finally show ?case using nbt nb by (simp add: algebra_simps)
next
  case (3 c e)
  with assms have cp: "c > 0" and nb: "numbound0 e" by simp_all
  from np have np: "real_of_int n \<noteq> 0" by simp
  have "?I ?u (Eq (CN 0 c e)) \<longleftrightarrow> real_of_int c * (?t / ?n) + ?N x e = 0"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> \<longleftrightarrow> ?n * (real_of_int c * (?t / ?n)) + ?n * ?N x e = 0"
    by (simp only: nonzero_eq_divide_eq[OF np, where a="real_of_int c *(?t/?n) + (?N x e)"
      and b="0", simplified div_0]) (simp only: algebra_simps)
  also have "\<dots> \<longleftrightarrow> real_of_int c * ?t + ?n * ?N x e = 0" using np by simp
  finally show ?case using nbt nb by (simp add: algebra_simps)
next
  case (4 c e) with assms have cp: "c >0" and nb: "numbound0 e" by simp_all
  from np have np: "real_of_int n \<noteq> 0" by simp
  have "?I ?u (NEq (CN 0 c e)) \<longleftrightarrow> real_of_int c * (?t / ?n) + ?N x e \<noteq> 0"
    using numbound0_I[OF nb, where bs="bs" and b="?u" and b'="x"] by simp
  also have "\<dots> \<longleftrightarrow> ?n * (real_of_int c * (?t / ?n)) + ?n * ?N x e \<noteq> 0"
    by (simp only: nonzero_eq_divide_eq[OF np, where a="real_of_int c *(?t/?n) + (?N x e)"
      and b="0", simplified div_0]) (simp only: algebra_simps)
  also have "\<dots> \<longleftrightarrow> real_of_int c * ?t + ?n * ?N x e \<noteq> 0" using np by simp
  finally show ?case using nbt nb by (simp add: algebra_simps)
qed(simp_all add: nbt numbound0_I[where bs ="bs" and b="(Inum (x#bs) t)/ real_of_int n" and b'="x"])

lemma uset_l:
  assumes lp: "isrlfm p"
  shows "\<forall>(t,k) \<in> set (uset p). numbound0 t \<and> k > 0"
  using lp by (induct p rule: uset.induct) auto

lemma rminusinf_uset:
  assumes lp: "isrlfm p"
    and nmi: "\<not> (Ifm (a # bs) (minusinf p))" (is "\<not> (Ifm (a # bs) (?M p))")
    and ex: "Ifm (x#bs) p" (is "?I x p")
  shows "\<exists>(s,m) \<in> set (uset p). x \<ge> Inum (a#bs) s / real_of_int m"
    (is "\<exists>(s,m) \<in> ?U p. x \<ge> ?N a s / real_of_int m")
proof -
  have "\<exists>(s,m) \<in> set (uset p). real_of_int m * x \<ge> Inum (a#bs) s"
    (is "\<exists>(s,m) \<in> ?U p. real_of_int m *x \<ge> ?N a s")
    using lp nmi ex
    by (induct p rule: minusinf.induct) (auto simp add:numbound0_I[where bs="bs" and b="a" and b'="x"])
  then obtain s m where smU: "(s,m) \<in> set (uset p)" and mx: "real_of_int m * x \<ge> ?N a s"
    by blast
  from uset_l[OF lp] smU have mp: "real_of_int m > 0"
    by auto
  from pos_divide_le_eq[OF mp, where a="x" and b="?N a s", symmetric] mx have "x \<ge> ?N a s / real_of_int m"
    by (auto simp add: mult.commute)
  then show ?thesis
    using smU by auto
qed

lemma rplusinf_uset:
  assumes lp: "isrlfm p"
    and nmi: "\<not> (Ifm (a # bs) (plusinf p))" (is "\<not> (Ifm (a # bs) (?M p))")
    and ex: "Ifm (x # bs) p" (is "?I x p")
  shows "\<exists>(s,m) \<in> set (uset p). x \<le> Inum (a#bs) s / real_of_int m"
    (is "\<exists>(s,m) \<in> ?U p. x \<le> ?N a s / real_of_int m")
proof -
  have "\<exists>(s,m) \<in> set (uset p). real_of_int m * x \<le> Inum (a#bs) s"
    (is "\<exists>(s,m) \<in> ?U p. real_of_int m *x \<le> ?N a s")
    using lp nmi ex
    by (induct p rule: minusinf.induct)
      (auto simp add:numbound0_I[where bs="bs" and b="a" and b'="x"])
  then obtain s m where smU: "(s,m) \<in> set (uset p)" and mx: "real_of_int m * x \<le> ?N a s"
    by blast
  from uset_l[OF lp] smU have mp: "real_of_int m > 0"
    by auto
  from pos_le_divide_eq[OF mp, where a="x" and b="?N a s", symmetric] mx have "x \<le> ?N a s / real_of_int m"
    by (auto simp add: mult.commute)
  then show ?thesis
    using smU by auto
qed

lemma lin_dense:
  assumes lp: "isrlfm p"
    and noS: "\<forall>t. l < t \<and> t< u \<longrightarrow> t \<notin> (\<lambda>(t,n). Inum (x#bs) t / real_of_int n) ` set (uset p)"
      (is "\<forall>t. _ \<and> _ \<longrightarrow> t \<notin> (\<lambda>(t,n). ?N x t / real_of_int n ) ` (?U p)")
    and lx: "l < x"
    and xu:"x < u"
    and px:" Ifm (x#bs) p"
    and ly: "l < y" and yu: "y < u"
  shows "Ifm (y#bs) p"
  using lp px noS
proof (induct p rule: isrlfm.induct)
  case (5 c e)
  then have cp: "real_of_int c > 0" and nb: "numbound0 e"
    by simp_all
  from 5 have "x * real_of_int c + ?N x e < 0"
    by (simp add: algebra_simps)
  then have pxc: "x < (- ?N x e) / real_of_int c"
    by (simp only: pos_less_divide_eq[OF cp, where a="x" and b="-?N x e"])
  from 5 have noSc:"\<forall>t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real_of_int c"
    by auto
  with ly yu have yne: "y \<noteq> - ?N x e / real_of_int c"
    by auto
  then consider "y < (-?N x e)/ real_of_int c" | "y > (- ?N x e) / real_of_int c"
    by atomize_elim auto
  then show ?case
  proof cases
    case 1
    then have "y * real_of_int c < - ?N x e"
      by (simp add: pos_less_divide_eq[OF cp, where a="y" and b="-?N x e", symmetric])
    then have "real_of_int c * y + ?N x e < 0"
      by (simp add: algebra_simps)
    then show ?thesis
      using numbound0_I[OF nb, where bs="bs" and b="x" and b'="y"] by simp
  next
    case 2
    with yu have eu: "u > (- ?N x e) / real_of_int c"
      by auto
    with noSc ly yu have "(- ?N x e) / real_of_int c \<le> l"
      by (cases "(- ?N x e) / real_of_int c > l") auto
    with lx pxc have False
      by auto
    then show ?thesis ..
  qed
next
  case (6 c e)
  then have cp: "real_of_int c > 0" and nb: "numbound0 e"
    by simp_all
  from 6 have "x * real_of_int c + ?N x e \<le> 0"
    by (simp add: algebra_simps)
  then have pxc: "x \<le> (- ?N x e) / real_of_int c"
    by (simp only: pos_le_divide_eq[OF cp, where a="x" and b="-?N x e"])
  from 6 have noSc:"\<forall>t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real_of_int c"
    by auto
  with ly yu have yne: "y \<noteq> - ?N x e / real_of_int c"
    by auto
  then consider "y < (- ?N x e) / real_of_int c" | "y > (-?N x e) / real_of_int c"
    by atomize_elim auto
  then show ?case
  proof cases
    case 1
    then have "y * real_of_int c < - ?N x e"
      by (simp add: pos_less_divide_eq[OF cp, where a="y" and b="-?N x e", symmetric])
    then have "real_of_int c * y + ?N x e < 0"
      by (simp add: algebra_simps)
    then show ?thesis
      using numbound0_I[OF nb, where bs="bs" and b="x" and b'="y"] by simp
  next
    case 2
    with yu have eu: "u > (- ?N x e) / real_of_int c"
      by auto
    with noSc ly yu have "(- ?N x e) / real_of_int c \<le> l"
      by (cases "(- ?N x e) / real_of_int c > l") auto
    with lx pxc have False
      by auto
    then show ?thesis ..
  qed
next
  case (7 c e)
  then have cp: "real_of_int c > 0" and nb: "numbound0 e"
    by simp_all
  from 7 have "x * real_of_int c + ?N x e > 0"
    by (simp add: algebra_simps)
  then have pxc: "x > (- ?N x e) / real_of_int c"
    by (simp only: pos_divide_less_eq[OF cp, where a="x" and b="-?N x e"])
  from 7 have noSc: "\<forall>t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real_of_int c"
    by auto
  with ly yu have yne: "y \<noteq> - ?N x e / real_of_int c"
    by auto
  then consider "y > (- ?N x e) / real_of_int c" | "y < (-?N x e) / real_of_int c"
    by atomize_elim auto
  then show ?case
  proof cases
    case 1
    then have "y * real_of_int c > - ?N x e"
      by (simp add: pos_divide_less_eq[OF cp, where a="y" and b="-?N x e", symmetric])
    then have "real_of_int c * y + ?N x e > 0"
      by (simp add: algebra_simps)
    then show ?thesis
      using numbound0_I[OF nb, where bs="bs" and b="x" and b'="y"] by simp
  next
    case 2
    with ly have eu: "l < (- ?N x e) / real_of_int c"
      by auto
    with noSc ly yu have "(- ?N x e) / real_of_int c \<ge> u"
      by (cases "(- ?N x e) / real_of_int c > l") auto
    with xu pxc have False by auto
    then show ?thesis ..
  qed
next
  case (8 c e)
  then have cp: "real_of_int c > 0" and nb: "numbound0 e"
    by simp_all
  from 8 have "x * real_of_int c + ?N x e \<ge> 0"
    by (simp add: algebra_simps)
  then have pxc: "x \<ge> (- ?N x e) / real_of_int c"
    by (simp only: pos_divide_le_eq[OF cp, where a="x" and b="-?N x e"])
  from 8 have noSc:"\<forall>t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real_of_int c"
    by auto
  with ly yu have yne: "y \<noteq> - ?N x e / real_of_int c"
    by auto
  then consider "y > (- ?N x e) / real_of_int c" | "y < (-?N x e) / real_of_int c"
    by atomize_elim auto
  then show ?case
  proof cases
    case 1
    then have "y * real_of_int c > - ?N x e"
      by (simp add: pos_divide_less_eq[OF cp, where a="y" and b="-?N x e", symmetric])
    then have "real_of_int c * y + ?N x e > 0" by (simp add: algebra_simps)
    then show ?thesis
      using numbound0_I[OF nb, where bs="bs" and b="x" and b'="y"] by simp
  next
    case 2
    with ly have eu: "l < (- ?N x e) / real_of_int c"
      by auto
    with noSc ly yu have "(- ?N x e) / real_of_int c \<ge> u"
      by (cases "(- ?N x e) / real_of_int c > l") auto
    with xu pxc have False
      by auto
    then show ?thesis ..
  qed
next
  case (3 c e)
  then have cp: "real_of_int c > 0" and nb: "numbound0 e"
    by simp_all
  from cp have cnz: "real_of_int c \<noteq> 0"
    by simp
  from 3 have "x * real_of_int c + ?N x e = 0"
    by (simp add: algebra_simps)
  then have pxc: "x = (- ?N x e) / real_of_int c"
    by (simp only: nonzero_eq_divide_eq[OF cnz, where a="x" and b="-?N x e"])
  from 3 have noSc:"\<forall>t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real_of_int c"
    by auto
  with lx xu have yne: "x \<noteq> - ?N x e / real_of_int c"
    by auto
  with pxc show ?case
    by simp
next
  case (4 c e)
  then have cp: "real_of_int c > 0" and nb: "numbound0 e"
    by simp_all
  from cp have cnz: "real_of_int c \<noteq> 0"
    by simp
  from 4 have noSc:"\<forall>t. l < t \<and> t < u \<longrightarrow> t \<noteq> (- ?N x e) / real_of_int c"
    by auto
  with ly yu have yne: "y \<noteq> - ?N x e / real_of_int c"
    by auto
  then have "y* real_of_int c \<noteq> -?N x e"
    by (simp only: nonzero_eq_divide_eq[OF cnz, where a="y" and b="-?N x e"]) simp
  then have "y* real_of_int c + ?N x e \<noteq> 0"
    by (simp add: algebra_simps)
  then show ?case using numbound0_I[OF nb, where bs="bs" and b="x" and b'="y"]
    by (simp add: algebra_simps)
qed (auto simp add: numbound0_I[where bs="bs" and b="y" and b'="x"])

lemma finite_set_intervals:
  fixes x :: real
  assumes px: "P x"
    and lx: "l \<le> x"
    and xu: "x \<le> u"
    and linS: "l\<in> S"
    and uinS: "u \<in> S"
    and fS: "finite S"
    and lS: "\<forall>x\<in> S. l \<le> x"
    and Su: "\<forall>x\<in> S. x \<le> u"
  shows "\<exists>a \<in> S. \<exists>b \<in> S. (\<forall>y. a < y \<and> y < b \<longrightarrow> y \<notin> S) \<and> a \<le> x \<and> x \<le> b \<and> P x"
proof -
  let ?Mx = "{y. y\<in> S \<and> y \<le> x}"
  let ?xM = "{y. y\<in> S \<and> x \<le> y}"
  let ?a = "Max ?Mx"
  let ?b = "Min ?xM"
  have MxS: "?Mx \<subseteq> S"
    by blast
  then have fMx: "finite ?Mx"
    using fS finite_subset by auto
  from lx linS have linMx: "l \<in> ?Mx"
    by blast
  then have Mxne: "?Mx \<noteq> {}"
    by blast
  have xMS: "?xM \<subseteq> S"
    by blast
  then have fxM: "finite ?xM"
    using fS finite_subset by auto
  from xu uinS have linxM: "u \<in> ?xM"
    by blast
  then have xMne: "?xM \<noteq> {}"
    by blast
  have ax:"?a \<le> x"
    using Mxne fMx by auto
  have xb:"x \<le> ?b"
    using xMne fxM by auto
  have "?a \<in> ?Mx"
    using Max_in[OF fMx Mxne] by simp
  then have ainS: "?a \<in> S"
    using MxS by blast
  have "?b \<in> ?xM"
    using Min_in[OF fxM xMne] by simp
  then have binS: "?b \<in> S"
    using xMS by blast
  have noy: "\<forall>y. ?a < y \<and> y < ?b \<longrightarrow> y \<notin> S"
  proof clarsimp
    fix y
    assume ay: "?a < y" and yb: "y < ?b" and yS: "y \<in> S"
    from yS consider "y \<in> ?Mx" | "y \<in> ?xM"
      by atomize_elim auto
    then show False
    proof cases
      case 1
      then have "y \<le> ?a"
        using Mxne fMx by auto
      with ay show ?thesis by simp
    next
      case 2
      then have "y \<ge> ?b"
        using xMne fxM by auto
      with yb show ?thesis by simp
    qed
  qed
  from ainS binS noy ax xb px show ?thesis
    by blast
qed

lemma rinf_uset:
  assumes lp: "isrlfm p"
    and nmi: "\<not> (Ifm (x # bs) (minusinf p))"  (is "\<not> (Ifm (x # bs) (?M p))")
    and npi: "\<not> (Ifm (x # bs) (plusinf p))"  (is "\<not> (Ifm (x # bs) (?P p))")
    and ex: "\<exists>x. Ifm (x # bs) p"  (is "\<exists>x. ?I x p")
  shows "\<exists>(l,n) \<in> set (uset p). \<exists>(s,m) \<in> set (uset p).
    ?I ((Inum (x#bs) l / real_of_int n + Inum (x#bs) s / real_of_int m) / 2) p"
proof -
  let ?N = "\<lambda>x t. Inum (x # bs) t"
  let ?U = "set (uset p)"
  from ex obtain a where pa: "?I a p"
    by blast
  from bound0_I[OF rminusinf_bound0[OF lp], where bs="bs" and b="x" and b'="a"] nmi
  have nmi': "\<not> (?I a (?M p))"
    by simp
  from bound0_I[OF rplusinf_bound0[OF lp], where bs="bs" and b="x" and b'="a"] npi
  have npi': "\<not> (?I a (?P p))"
    by simp
  have "\<exists>(l,n) \<in> set (uset p). \<exists>(s,m) \<in> set (uset p). ?I ((?N a l/real_of_int n + ?N a s /real_of_int m) / 2) p"
  proof -
    let ?M = "(\<lambda>(t,c). ?N a t / real_of_int c) ` ?U"
    have fM: "finite ?M"
      by auto
    from rminusinf_uset[OF lp nmi pa] rplusinf_uset[OF lp npi pa]
    have "\<exists>(l,n) \<in> set (uset p). \<exists>(s,m) \<in> set (uset p). a \<le> ?N x l / real_of_int n \<and> a \<ge> ?N x s / real_of_int m"
      by blast
    then obtain "t" "n" "s" "m"
      where tnU: "(t,n) \<in> ?U"
        and smU: "(s,m) \<in> ?U"
        and xs1: "a \<le> ?N x s / real_of_int m"
        and tx1: "a \<ge> ?N x t / real_of_int n"
      by blast
    from uset_l[OF lp] tnU smU numbound0_I[where bs="bs" and b="x" and b'="a"] xs1 tx1
    have xs: "a \<le> ?N a s / real_of_int m" and tx: "a \<ge> ?N a t / real_of_int n"
      by auto
    from tnU have Mne: "?M \<noteq> {}"
      by auto
    then have Une: "?U \<noteq> {}"
      by simp
    let ?l = "Min ?M"
    let ?u = "Max ?M"
    have linM: "?l \<in> ?M"
      using fM Mne by simp
    have uinM: "?u \<in> ?M"
      using fM Mne by simp
    have tnM: "?N a t / real_of_int n \<in> ?M"
      using tnU by auto
    have smM: "?N a s / real_of_int m \<in> ?M"
      using smU by auto
    have lM: "\<forall>t\<in> ?M. ?l \<le> t"
      using Mne fM by auto
    have Mu: "\<forall>t\<in> ?M. t \<le> ?u"
      using Mne fM by auto
    have "?l \<le> ?N a t / real_of_int n"
      using tnM Mne by simp
    then have lx: "?l \<le> a"
      using tx by simp
    have "?N a s / real_of_int m \<le> ?u"
      using smM Mne by simp
    then have xu: "a \<le> ?u"
      using xs by simp
    from finite_set_intervals2[where P="\<lambda>x. ?I x p",OF pa lx xu linM uinM fM lM Mu]
    consider u where "u \<in> ?M" "?I u p"
      | t1 t2 where "t1 \<in> ?M" "t2 \<in> ?M" "\<forall>y. t1 < y \<and> y < t2 \<longrightarrow> y \<notin> ?M" "t1 < a" "a < t2" "?I a p"
      by blast
    then show ?thesis
    proof cases
      case 1
      note um = \<open>u \<in> ?M\<close> and pu = \<open>?I u p\<close>
      then have "\<exists>(tu,nu) \<in> ?U. u = ?N a tu / real_of_int nu"
        by auto
      then obtain tu nu where tuU: "(tu, nu) \<in> ?U" and tuu: "u= ?N a tu / real_of_int nu"
        by blast
      have "(u + u) / 2 = u"
        by auto
      with pu tuu have "?I (((?N a tu / real_of_int nu) + (?N a tu / real_of_int nu)) / 2) p"
        by simp
      with tuU show ?thesis by blast
    next
      case 2
      note t1M = \<open>t1 \<in> ?M\<close> and t2M = \<open>t2\<in> ?M\<close>
        and noM = \<open>\<forall>y. t1 < y \<and> y < t2 \<longrightarrow> y \<notin> ?M\<close>
        and t1x = \<open>t1 < a\<close> and xt2 = \<open>a < t2\<close> and px = \<open>?I a p\<close>
      from t1M have "\<exists>(t1u,t1n) \<in> ?U. t1 = ?N a t1u / real_of_int t1n"
        by auto
      then obtain t1u t1n where t1uU: "(t1u, t1n) \<in> ?U" and t1u: "t1 = ?N a t1u / real_of_int t1n"
        by blast
      from t2M have "\<exists>(t2u,t2n) \<in> ?U. t2 = ?N a t2u / real_of_int t2n"
        by auto
      then obtain t2u t2n where t2uU: "(t2u, t2n) \<in> ?U" and t2u: "t2 = ?N a t2u / real_of_int t2n"
        by blast
      from t1x xt2 have t1t2: "t1 < t2"
        by simp
      let ?u = "(t1 + t2) / 2"
      from less_half_sum[OF t1t2] gt_half_sum[OF t1t2] have t1lu: "t1 < ?u" and ut2: "?u < t2"
        by auto
      from lin_dense[OF lp noM t1x xt2 px t1lu ut2] have "?I ?u p" .
      with t1uU t2uU t1u t2u show ?thesis
        by blast
    qed
  qed
  then obtain l n s m where lnU: "(l, n) \<in> ?U" and smU:"(s, m) \<in> ?U"
    and pu: "?I ((?N a l / real_of_int n + ?N a s / real_of_int m) / 2) p"
    by blast
  from lnU smU uset_l[OF lp] have nbl: "numbound0 l" and nbs: "numbound0 s"
    by auto
  from numbound0_I[OF nbl, where bs="bs" and b="a" and b'="x"]
    numbound0_I[OF nbs, where bs="bs" and b="a" and b'="x"] pu
  have "?I ((?N x l / real_of_int n + ?N x s / real_of_int m) / 2) p"
    by simp
  with lnU smU show ?thesis
    by auto
qed


    (* The Ferrante - Rackoff Theorem *)

theorem fr_eq:
  assumes lp: "isrlfm p"
  shows "(\<exists>x. Ifm (x#bs) p) \<longleftrightarrow>
    Ifm (x # bs) (minusinf p) \<or> Ifm (x # bs) (plusinf p) \<or>
      (\<exists>(t,n) \<in> set (uset p). \<exists>(s,m) \<in> set (uset p).
        Ifm ((((Inum (x # bs) t) / real_of_int n + (Inum (x # bs) s) / real_of_int m) / 2) # bs) p)"
  (is "(\<exists>x. ?I x p) \<longleftrightarrow> (?M \<or> ?P \<or> ?F)" is "?E = ?D")
proof
  assume px: "\<exists>x. ?I x p"
  consider "?M \<or> ?P" | "\<not> ?M" "\<not> ?P" by blast
  then show ?D
  proof cases
    case 1
    then show ?thesis by blast
  next
    case 2
    from rinf_uset[OF lp this] have ?F
      using px by blast
    then show ?thesis by blast
  qed
next
  assume ?D
  then consider ?M | ?P | ?F by blast
  then show ?E
  proof cases
    case 1
    from rminusinf_ex[OF lp this] show ?thesis .
  next
    case 2
    from rplusinf_ex[OF lp this] show ?thesis .
  next
    case 3
    then show ?thesis by blast
  qed
qed


lemma fr_equsubst:
  assumes lp: "isrlfm p"
  shows "(\<exists>x. Ifm (x # bs) p) \<longleftrightarrow>
    (Ifm (x # bs) (minusinf p) \<or> Ifm (x # bs) (plusinf p) \<or>
      (\<exists>(t,k) \<in> set (uset p). \<exists>(s,l) \<in> set (uset p).
        Ifm (x#bs) (usubst p (Add (Mul l t) (Mul k s), 2 * k * l))))"
  (is "(\<exists>x. ?I x p) \<longleftrightarrow> ?M \<or> ?P \<or> ?F" is "?E = ?D")
proof
  assume px: "\<exists>x. ?I x p"
  consider "?M \<or> ?P" | "\<not> ?M" "\<not> ?P" by blast
  then show ?D
  proof cases
    case 1
    then show ?thesis by blast
  next
    case 2
    let ?f = "\<lambda>(t,n). Inum (x # bs) t / real_of_int n"
    let ?N = "\<lambda>t. Inum (x # bs) t"
    {
      fix t n s m
      assume "(t, n) \<in> set (uset p)" and "(s, m) \<in> set (uset p)"
      with uset_l[OF lp] have tnb: "numbound0 t"
        and np: "real_of_int n > 0" and snb: "numbound0 s" and mp: "real_of_int m > 0"
        by auto
      let ?st = "Add (Mul m t) (Mul n s)"
      from np mp have mnp: "real_of_int (2 * n * m) > 0"
        by (simp add: mult.commute)
      from tnb snb have st_nb: "numbound0 ?st"
        by simp
      have st: "(?N t / real_of_int n + ?N s / real_of_int m) / 2 = ?N ?st / real_of_int (2 * n * m)"
        using mnp mp np by (simp add: algebra_simps add_divide_distrib)
      from usubst_I[OF lp mnp st_nb, where x="x" and bs="bs"]
      have "?I x (usubst p (?st, 2 * n * m)) = ?I ((?N t / real_of_int n + ?N s / real_of_int m) / 2) p"
        by (simp only: st[symmetric])
    }
    with rinf_uset[OF lp 2 px] have ?F
      by blast
    then show ?thesis
      by blast
  qed
next
  assume ?D
  then consider ?M | ?P | t k s l where "(t, k) \<in> set (uset p)" "(s, l) \<in> set (uset p)"
    "?I x (usubst p (Add (Mul l t) (Mul k s), 2 * k * l))"
    by blast
  then show ?E
  proof cases
    case 1
    from rminusinf_ex[OF lp this] show ?thesis .
  next
    case 2
    from rplusinf_ex[OF lp this] show ?thesis .
  next
    case 3
    with uset_l[OF lp] have tnb: "numbound0 t" and np: "real_of_int k > 0"
      and snb: "numbound0 s" and mp: "real_of_int l > 0"
      by auto
    let ?st = "Add (Mul l t) (Mul k s)"
    from np mp have mnp: "real_of_int (2 * k * l) > 0"
      by (simp add: mult.commute)
    from tnb snb have st_nb: "numbound0 ?st"
      by simp
    from usubst_I[OF lp mnp st_nb, where bs="bs"]
      \<open>?I x (usubst p (Add (Mul l t) (Mul k s), 2 * k * l))\<close> show ?thesis
      by auto
  qed
qed


    (* Implement the right hand side of Ferrante and Rackoff's Theorem. *)
definition ferrack :: "fm \<Rightarrow> fm"
where
  "ferrack p =
   (let
      p' = rlfm (simpfm p);
      mp = minusinf p';
      pp = plusinf p'
    in
      if mp = T \<or> pp = T then T
      else
       (let U = remdups (map simp_num_pair
         (map (\<lambda>((t,n),(s,m)). (Add (Mul m t) (Mul n s) , 2 * n * m))
               (alluopairs (uset p'))))
        in decr (disj mp (disj pp (evaldjf (simpfm \<circ> usubst p') U)))))"

lemma uset_cong_aux:
  assumes Ul: "\<forall>(t,n) \<in> set U. numbound0 t \<and> n > 0"
  shows "((\<lambda>(t,n). Inum (x # bs) t / real_of_int n) `
    (set (map (\<lambda>((t,n),(s,m)). (Add (Mul m t) (Mul n s), 2 * n * m)) (alluopairs U)))) =
    ((\<lambda>((t,n),(s,m)). (Inum (x # bs) t / real_of_int n + Inum (x # bs) s / real_of_int m) / 2) ` (set U \<times> set U))"
  (is "?lhs = ?rhs")
proof auto
  fix t n s m
  assume "((t, n), (s, m)) \<in> set (alluopairs U)"
  then have th: "((t, n), (s, m)) \<in> set U \<times> set U"
    using alluopairs_set1[where xs="U"] by blast
  let ?N = "\<lambda>t. Inum (x # bs) t"
  let ?st = "Add (Mul m t) (Mul n s)"
  from Ul th have mnz: "m \<noteq> 0"
    by auto
  from Ul th have nnz: "n \<noteq> 0"
    by auto
  have st: "(?N t / real_of_int n + ?N s / real_of_int m) / 2 = ?N ?st / real_of_int (2 * n * m)"
    using mnz nnz by (simp add: algebra_simps add_divide_distrib)
  then show "(real_of_int m *  Inum (x # bs) t + real_of_int n * Inum (x # bs) s) / (2 * real_of_int n * real_of_int m)
      \<in> (\<lambda>((t, n), s, m). (Inum (x # bs) t / real_of_int n + Inum (x # bs) s / real_of_int m) / 2) `
         (set U \<times> set U)"
    using mnz nnz th
    apply (auto simp add: th add_divide_distrib algebra_simps split_def image_def)
    apply (rule_tac x="(s,m)" in bexI)
    apply simp_all
    apply (rule_tac x="(t,n)" in bexI)
    apply (simp_all add: mult.commute)
    done
next
  fix t n s m
  assume tnU: "(t, n) \<in> set U" and smU: "(s, m) \<in> set U"
  let ?N = "\<lambda>t. Inum (x # bs) t"
  let ?st = "Add (Mul m t) (Mul n s)"
  from Ul smU have mnz: "m \<noteq> 0"
    by auto
  from Ul tnU have nnz: "n \<noteq> 0"
    by auto
  have st: "(?N t / real_of_int n + ?N s / real_of_int m) / 2 = ?N ?st / real_of_int (2 * n * m)"
    using mnz nnz by (simp add: algebra_simps add_divide_distrib)
  let ?P = "\<lambda>(t',n') (s',m'). (Inum (x # bs) t / real_of_int n + Inum (x # bs) s / real_of_int m)/2 =
    (Inum (x # bs) t' / real_of_int n' + Inum (x # bs) s' / real_of_int m') / 2"
  have Pc:"\<forall>a b. ?P a b = ?P b a"
    by auto
  from Ul alluopairs_set1 have Up:"\<forall>((t,n),(s,m)) \<in> set (alluopairs U). n \<noteq> 0 \<and> m \<noteq> 0"
    by blast
  from alluopairs_ex[OF Pc, where xs="U"] tnU smU
  have th':"\<exists>((t',n'),(s',m')) \<in> set (alluopairs U). ?P (t',n') (s',m')"
    by blast
  then obtain t' n' s' m' where ts'_U: "((t',n'),(s',m')) \<in> set (alluopairs U)"
    and Pts': "?P (t', n') (s', m')"
    by blast
  from ts'_U Up have mnz': "m' \<noteq> 0" and nnz': "n'\<noteq> 0"
    by auto
  let ?st' = "Add (Mul m' t') (Mul n' s')"
  have st': "(?N t' / real_of_int n' + ?N s' / real_of_int m') / 2 = ?N ?st' / real_of_int (2 * n' * m')"
    using mnz' nnz' by (simp add: algebra_simps add_divide_distrib)
  from Pts' have "(Inum (x # bs) t / real_of_int n + Inum (x # bs) s / real_of_int m) / 2 =
    (Inum (x # bs) t' / real_of_int n' + Inum (x # bs) s' / real_of_int m') / 2"
    by simp
  also have "\<dots> = (\<lambda>(t, n). Inum (x # bs) t / real_of_int n)
      ((\<lambda>((t, n), s, m). (Add (Mul m t) (Mul n s), 2 * n * m)) ((t', n'), (s', m')))"
    by (simp add: st')
  finally show "(Inum (x # bs) t / real_of_int n + Inum (x # bs) s / real_of_int m) / 2
    \<in> (\<lambda>(t, n). Inum (x # bs) t / real_of_int n) `
      (\<lambda>((t, n), s, m). (Add (Mul m t) (Mul n s), 2 * n * m)) ` set (alluopairs U)"
    using ts'_U by blast
qed

lemma uset_cong:
  assumes lp: "isrlfm p"
    and UU': "((\<lambda>(t,n). Inum (x # bs) t / real_of_int n) ` U') =
      ((\<lambda>((t,n),(s,m)). (Inum (x # bs) t / real_of_int n + Inum (x # bs) s / real_of_int m) / 2) ` (U \<times> U))"
      (is "?f ` U' = ?g ` (U \<times> U)")
    and U: "\<forall>(t,n) \<in> U. numbound0 t \<and> n > 0"
    and U': "\<forall>(t,n) \<in> U'. numbound0 t \<and> n > 0"
  shows "(\<exists>(t,n) \<in> U. \<exists>(s,m) \<in> U. Ifm (x # bs) (usubst p (Add (Mul m t) (Mul n s), 2 * n * m))) =
    (\<exists>(t,n) \<in> U'. Ifm (x # bs) (usubst p (t, n)))"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?rhs if ?lhs
  proof -
    from that obtain t n s m where tnU: "(t, n) \<in> U" and smU: "(s, m) \<in> U"
      and Pst: "Ifm (x # bs) (usubst p (Add (Mul m t) (Mul n s), 2 * n * m))"
      by blast
    let ?N = "\<lambda>t. Inum (x#bs) t"
    from tnU smU U have tnb: "numbound0 t" and np: "n > 0"
      and snb: "numbound0 s" and mp: "m > 0"
      by auto
    let ?st = "Add (Mul m t) (Mul n s)"
    from np mp have mnp: "real_of_int (2 * n * m) > 0"
      by (simp add: mult.commute of_int_mult[symmetric] del: of_int_mult)
    from tnb snb have stnb: "numbound0 ?st"
      by simp
    have st: "(?N t / real_of_int n + ?N s / real_of_int m) / 2 = ?N ?st / real_of_int (2 * n * m)"
      using mp np by (simp add: algebra_simps add_divide_distrib)
    from tnU smU UU' have "?g ((t, n), (s, m)) \<in> ?f ` U'"
      by blast
    then have "\<exists>(t',n') \<in> U'. ?g ((t, n), (s, m)) = ?f (t', n')"
      apply auto
      apply (rule_tac x="(a, b)" in bexI)
      apply auto
      done
    then obtain t' n' where tnU': "(t',n') \<in> U'" and th: "?g ((t, n), (s, m)) = ?f (t', n')"
      by blast
    from U' tnU' have tnb': "numbound0 t'" and np': "real_of_int n' > 0"
      by auto
    from usubst_I[OF lp mnp stnb, where bs="bs" and x="x"] Pst
    have Pst2: "Ifm (Inum (x # bs) (Add (Mul m t) (Mul n s)) / real_of_int (2 * n * m) # bs) p"
      by simp
    from conjunct1[OF usubst_I[OF lp np' tnb', where bs="bs" and x="x"], symmetric]
      th[simplified split_def fst_conv snd_conv,symmetric] Pst2[simplified st[symmetric]]
    have "Ifm (x # bs) (usubst p (t', n'))"
      by (simp only: st)
    then show ?thesis
      using tnU' by auto
  qed
  show ?lhs if ?rhs
  proof -
    from that obtain t' n' where tnU': "(t', n') \<in> U'" and Pt': "Ifm (x # bs) (usubst p (t', n'))"
      by blast
    from tnU' UU' have "?f (t', n') \<in> ?g ` (U \<times> U)"
      by blast
    then have "\<exists>((t,n),(s,m)) \<in> U \<times> U. ?f (t', n') = ?g ((t, n), (s, m))"
      apply auto
      apply (rule_tac x="(a,b)" in bexI)
      apply auto
      done
    then obtain t n s m where tnU: "(t, n) \<in> U" and smU: "(s, m) \<in> U" and
      th: "?f (t', n') = ?g ((t, n), (s, m))"
      by blast
    let ?N = "\<lambda>t. Inum (x # bs) t"
    from tnU smU U have tnb: "numbound0 t" and np: "n > 0"
      and snb: "numbound0 s" and mp: "m > 0"
      by auto
    let ?st = "Add (Mul m t) (Mul n s)"
    from np mp have mnp: "real_of_int (2 * n * m) > 0"
      by (simp add: mult.commute of_int_mult[symmetric] del: of_int_mult)
    from tnb snb have stnb: "numbound0 ?st"
      by simp
    have st: "(?N t / real_of_int n + ?N s / real_of_int m) / 2 = ?N ?st / real_of_int (2 * n * m)"
      using mp np by (simp add: algebra_simps add_divide_distrib)
    from U' tnU' have tnb': "numbound0 t'" and np': "real_of_int n' > 0"
      by auto
    from usubst_I[OF lp np' tnb', where bs="bs" and x="x",simplified
      th[simplified split_def fst_conv snd_conv] st] Pt'
    have Pst2: "Ifm (Inum (x # bs) (Add (Mul m t) (Mul n s)) / real_of_int (2 * n * m) # bs) p"
      by simp
    with usubst_I[OF lp mnp stnb, where x="x" and bs="bs"] tnU smU
    show ?thesis by blast
  qed
qed

lemma ferrack:
  assumes qf: "qfree p"
  shows "qfree (ferrack p) \<and> (Ifm bs (ferrack p) \<longleftrightarrow> (\<exists>x. Ifm (x # bs) p))"
  (is "_ \<and> (?rhs \<longleftrightarrow> ?lhs)")
proof -
  let ?I = "\<lambda>x p. Ifm (x # bs) p"
  fix x
  let ?N = "\<lambda>t. Inum (x # bs) t"
  let ?q = "rlfm (simpfm p)"
  let ?U = "uset ?q"
  let ?Up = "alluopairs ?U"
  let ?g = "\<lambda>((t,n),(s,m)). (Add (Mul m t) (Mul n s), 2 * n * m)"
  let ?S = "map ?g ?Up"
  let ?SS = "map simp_num_pair ?S"
  let ?Y = "remdups ?SS"
  let ?f = "\<lambda>(t,n). ?N t / real_of_int n"
  let ?h = "\<lambda>((t,n),(s,m)). (?N t / real_of_int n + ?N s / real_of_int m) / 2"
  let ?F = "\<lambda>p. \<exists>a \<in> set (uset p). \<exists>b \<in> set (uset p). ?I x (usubst p (?g (a, b)))"
  let ?ep = "evaldjf (simpfm \<circ> (usubst ?q)) ?Y"
  from rlfm_I[OF simpfm_qf[OF qf]] have lq: "isrlfm ?q"
    by blast
  from alluopairs_set1[where xs="?U"] have UpU: "set ?Up \<subseteq> set ?U \<times> set ?U"
    by simp
  from uset_l[OF lq] have U_l: "\<forall>(t,n) \<in> set ?U. numbound0 t \<and> n > 0" .
  from U_l UpU
  have "\<forall>((t,n),(s,m)) \<in> set ?Up. numbound0 t \<and> n> 0 \<and> numbound0 s \<and> m > 0"
    by auto
  then have Snb: "\<forall>(t,n) \<in> set ?S. numbound0 t \<and> n > 0 "
    by auto
  have Y_l: "\<forall>(t,n) \<in> set ?Y. numbound0 t \<and> n > 0"
  proof -
    have "numbound0 t \<and> n > 0" if tnY: "(t, n) \<in> set ?Y" for t n
    proof -
      from that have "(t,n) \<in> set ?SS"
        by simp
      then have "\<exists>(t',n') \<in> set ?S. simp_num_pair (t', n') = (t, n)"
        apply (auto simp add: split_def simp del: map_map)
        apply (rule_tac x="((aa,ba),(ab,bb))" in bexI)
        apply simp_all
        done
      then obtain t' n' where tn'S: "(t', n') \<in> set ?S" and tns: "simp_num_pair (t', n') = (t, n)"
        by blast
      from tn'S Snb have tnb: "numbound0 t'" and np: "n' > 0"
        by auto
      from simp_num_pair_l[OF tnb np tns] show ?thesis .
    qed
    then show ?thesis by blast
  qed

  have YU: "(?f ` set ?Y) = (?h ` (set ?U \<times> set ?U))"
  proof -
    from simp_num_pair_ci[where bs="x#bs"] have "\<forall>x. (?f \<circ> simp_num_pair) x = ?f x"
      by auto
    then have th: "?f \<circ> simp_num_pair = ?f"
      by auto
    have "(?f ` set ?Y) = ((?f \<circ> simp_num_pair) ` set ?S)"
      by (simp add: comp_assoc image_comp)
    also have "\<dots> = ?f ` set ?S"
      by (simp add: th)
    also have "\<dots> = (?f \<circ> ?g) ` set ?Up"
      by (simp only: set_map o_def image_comp)
    also have "\<dots> = ?h ` (set ?U \<times> set ?U)"
      using uset_cong_aux[OF U_l, where x="x" and bs="bs", simplified set_map image_comp]
      by blast
    finally show ?thesis .
  qed
  have "\<forall>(t,n) \<in> set ?Y. bound0 (simpfm (usubst ?q (t, n)))"
  proof -
    have "bound0 (simpfm (usubst ?q (t, n)))" if tnY: "(t,n) \<in> set ?Y" for t n
    proof -
      from Y_l that have tnb: "numbound0 t" and np: "real_of_int n > 0"
        by auto
      from usubst_I[OF lq np tnb] have "bound0 (usubst ?q (t, n))"
        by simp
      then show ?thesis
        using simpfm_bound0 by simp
    qed
    then show ?thesis by blast
  qed
  then have ep_nb: "bound0 ?ep"
    using evaldjf_bound0[where xs="?Y" and f="simpfm \<circ> (usubst ?q)"] by auto
  let ?mp = "minusinf ?q"
  let ?pp = "plusinf ?q"
  let ?M = "?I x ?mp"
  let ?P = "?I x ?pp"
  let ?res = "disj ?mp (disj ?pp ?ep)"
  from rminusinf_bound0[OF lq] rplusinf_bound0[OF lq] ep_nb have nbth: "bound0 ?res"
    by auto

  from conjunct1[OF rlfm_I[OF simpfm_qf[OF qf]]] simpfm have th: "?lhs = (\<exists>x. ?I x ?q)"
    by auto
  from th fr_equsubst[OF lq, where bs="bs" and x="x"] have lhfr: "?lhs = (?M \<or> ?P \<or> ?F ?q)"
    by (simp only: split_def fst_conv snd_conv)
  also have "\<dots> = (?M \<or> ?P \<or> (\<exists>(t,n) \<in> set ?Y. ?I x (simpfm (usubst ?q (t,n)))))"
    using uset_cong[OF lq YU U_l Y_l] by (simp only: split_def fst_conv snd_conv simpfm)
  also have "\<dots> = (Ifm (x#bs) ?res)"
    using evaldjf_ex[where ps="?Y" and bs = "x#bs" and f="simpfm \<circ> (usubst ?q)",symmetric]
    by (simp add: split_def prod.collapse)
  finally have lheq: "?lhs = Ifm bs (decr ?res)"
    using decr[OF nbth] by blast
  then have lr: "?lhs = ?rhs"
    unfolding ferrack_def Let_def
    by (cases "?mp = T \<or> ?pp = T", auto) (simp add: disj_def)+
  from decr_qf[OF nbth] have "qfree (ferrack p)"
    by (auto simp add: Let_def ferrack_def)
  with lr show ?thesis
    by blast
qed

definition linrqe:: "fm \<Rightarrow> fm"
  where "linrqe p = qelim (prep p) ferrack"

theorem linrqe: "Ifm bs (linrqe p) = Ifm bs p \<and> qfree (linrqe p)"
  using ferrack qelim_ci prep
  unfolding linrqe_def by auto

definition ferrack_test :: "unit \<Rightarrow> fm"
where
  "ferrack_test u =
    linrqe (A (A (Imp (Lt (Sub (Bound 1) (Bound 0)))
      (E (Eq (Sub (Add (Bound 0) (Bound 2)) (Bound 1)))))))"

ML_val \<open>@{code ferrack_test} ()\<close>

oracle linr_oracle = \<open>
let

val mk_C = @{code C} o @{code int_of_integer};
val mk_Bound = @{code Bound} o @{code nat_of_integer};

fun num_of_term vs (Free vT) = mk_Bound (find_index (fn vT' => vT = vT') vs)
  | num_of_term vs \<^term>\<open>real_of_int (0::int)\<close> = mk_C 0
  | num_of_term vs \<^term>\<open>real_of_int (1::int)\<close> = mk_C 1
  | num_of_term vs \<^term>\<open>0::real\<close> = mk_C 0
  | num_of_term vs \<^term>\<open>1::real\<close> = mk_C 1
  | num_of_term vs (Bound i) = mk_Bound i
  | num_of_term vs (\<^term>\<open>uminus :: real \<Rightarrow> real\<close> $ t') = @{code Neg} (num_of_term vs t')
  | num_of_term vs (\<^term>\<open>(+) :: real \<Rightarrow> real \<Rightarrow> real\<close> $ t1 $ t2) =
     @{code Add} (num_of_term vs t1, num_of_term vs t2)
  | num_of_term vs (\<^term>\<open>(-) :: real \<Rightarrow> real \<Rightarrow> real\<close> $ t1 $ t2) =
     @{code Sub} (num_of_term vs t1, num_of_term vs t2)
  | num_of_term vs (\<^term>\<open>(*) :: real \<Rightarrow> real \<Rightarrow> real\<close> $ t1 $ t2) = (case num_of_term vs t1
     of @{code C} i => @{code Mul} (i, num_of_term vs t2)
      | _ => error "num_of_term: unsupported multiplication")
  | num_of_term vs (\<^term>\<open>real_of_int :: int \<Rightarrow> real\<close> $ t') =
     (mk_C (snd (HOLogic.dest_number t'))
       handle TERM _ => error ("num_of_term: unknown term"))
  | num_of_term vs t' =
     (mk_C (snd (HOLogic.dest_number t'))
       handle TERM _ => error ("num_of_term: unknown term"));

fun fm_of_term vs \<^term>\<open>True\<close> = @{code T}
  | fm_of_term vs \<^term>\<open>False\<close> = @{code F}
  | fm_of_term vs (\<^term>\<open>(<) :: real \<Rightarrow> real \<Rightarrow> bool\<close> $ t1 $ t2) =
      @{code Lt} (@{code Sub} (num_of_term vs t1, num_of_term vs t2))
  | fm_of_term vs (\<^term>\<open>(\<le>) :: real \<Rightarrow> real \<Rightarrow> bool\<close> $ t1 $ t2) =
      @{code Le} (@{code Sub} (num_of_term vs t1, num_of_term vs t2))
  | fm_of_term vs (\<^term>\<open>(=) :: real \<Rightarrow> real \<Rightarrow> bool\<close> $ t1 $ t2) =
      @{code Eq} (@{code Sub} (num_of_term vs t1, num_of_term vs t2))
  | fm_of_term vs (\<^term>\<open>(\<longleftrightarrow>) :: bool \<Rightarrow> bool \<Rightarrow> bool\<close> $ t1 $ t2) =
      @{code Iff} (fm_of_term vs t1, fm_of_term vs t2)
  | fm_of_term vs (\<^term>\<open>HOL.conj\<close> $ t1 $ t2) = @{code And} (fm_of_term vs t1, fm_of_term vs t2)
  | fm_of_term vs (\<^term>\<open>HOL.disj\<close> $ t1 $ t2) = @{code Or} (fm_of_term vs t1, fm_of_term vs t2)
  | fm_of_term vs (\<^term>\<open>HOL.implies\<close> $ t1 $ t2) = @{code Imp} (fm_of_term vs t1, fm_of_term vs t2)
  | fm_of_term vs (\<^term>\<open>Not\<close> $ t') = @{code NOT} (fm_of_term vs t')
  | fm_of_term vs (Const (\<^const_name>\<open>Ex\<close>, _) $ Abs (xn, xT, p)) =
      @{code E} (fm_of_term (("", dummyT) :: vs) p)
  | fm_of_term vs (Const (\<^const_name>\<open>All\<close>, _) $ Abs (xn, xT, p)) =
      @{code A} (fm_of_term (("", dummyT) ::  vs) p)
  | fm_of_term vs t = error ("fm_of_term : unknown term " ^ Syntax.string_of_term \<^context> t);

fun term_of_num vs (@{code C} i) = \<^term>\<open>real_of_int :: int \<Rightarrow> real\<close> $
      HOLogic.mk_number HOLogic.intT (@{code integer_of_int} i)
  | term_of_num vs (@{code Bound} n) = Free (nth vs (@{code integer_of_nat} n))
  | term_of_num vs (@{code Neg} t') = \<^term>\<open>uminus :: real \<Rightarrow> real\<close> $ term_of_num vs t'
  | term_of_num vs (@{code Add} (t1, t2)) = \<^term>\<open>(+) :: real \<Rightarrow> real \<Rightarrow> real\<close> $
      term_of_num vs t1 $ term_of_num vs t2
  | term_of_num vs (@{code Sub} (t1, t2)) = \<^term>\<open>(-) :: real \<Rightarrow> real \<Rightarrow> real\<close> $
      term_of_num vs t1 $ term_of_num vs t2
  | term_of_num vs (@{code Mul} (i, t2)) = \<^term>\<open>(*) :: real \<Rightarrow> real \<Rightarrow> real\<close> $
      term_of_num vs (@{code C} i) $ term_of_num vs t2
  | term_of_num vs (@{code CN} (n, i, t)) = term_of_num vs (@{code Add} (@{code Mul} (i, @{code Bound} n), t));

fun term_of_fm vs @{code T} = \<^term>\<open>True\<close>
  | term_of_fm vs @{code F} = \<^term>\<open>False\<close>
  | term_of_fm vs (@{code Lt} t) = \<^term>\<open>(<) :: real \<Rightarrow> real \<Rightarrow> bool\<close> $
      term_of_num vs t $ \<^term>\<open>0::real\<close>
  | term_of_fm vs (@{code Le} t) = \<^term>\<open>(\<le>) :: real \<Rightarrow> real \<Rightarrow> bool\<close> $
      term_of_num vs t $ \<^term>\<open>0::real\<close>
  | term_of_fm vs (@{code Gt} t) = \<^term>\<open>(<) :: real \<Rightarrow> real \<Rightarrow> bool\<close> $
      \<^term>\<open>0::real\<close> $ term_of_num vs t
  | term_of_fm vs (@{code Ge} t) = \<^term>\<open>(\<le>) :: real \<Rightarrow> real \<Rightarrow> bool\<close> $
      \<^term>\<open>0::real\<close> $ term_of_num vs t
  | term_of_fm vs (@{code Eq} t) = \<^term>\<open>(=) :: real \<Rightarrow> real \<Rightarrow> bool\<close> $
      term_of_num vs t $ \<^term>\<open>0::real\<close>
  | term_of_fm vs (@{code NEq} t) = term_of_fm vs (@{code NOT} (@{code Eq} t))
  | term_of_fm vs (@{code NOT} t') = HOLogic.Not $ term_of_fm vs t'
  | term_of_fm vs (@{code And} (t1, t2)) = HOLogic.conj $ term_of_fm vs t1 $ term_of_fm vs t2
  | term_of_fm vs (@{code Or} (t1, t2)) = HOLogic.disj $ term_of_fm vs t1 $ term_of_fm vs t2
  | term_of_fm vs (@{code Imp}  (t1, t2)) = HOLogic.imp $ term_of_fm vs t1 $ term_of_fm vs t2
  | term_of_fm vs (@{code Iff} (t1, t2)) = \<^term>\<open>(\<longleftrightarrow>) :: bool \<Rightarrow> bool \<Rightarrow> bool\<close> $
      term_of_fm vs t1 $ term_of_fm vs t2;

in fn (ctxt, t) =>
  let
    val vs = Term.add_frees t [];
    val t' = (term_of_fm vs o @{code linrqe} o fm_of_term vs) t;
  in (Thm.cterm_of ctxt o HOLogic.mk_Trueprop o HOLogic.mk_eq) (t, t') end
end
\<close>

ML_file \<open>ferrack_tac.ML\<close>

method_setup rferrack = \<open>
  Scan.lift (Args.mode "no_quantify") >>
    (fn q => fn ctxt => SIMPLE_METHOD' (Ferrack_Tac.linr_tac ctxt (not q)))
\<close> "decision procedure for linear real arithmetic"


lemma
  fixes x :: real
  shows "2 * x \<le> 2 * x \<and> 2 * x \<le> 2 * x + 1"
  by rferrack

lemma
  fixes x :: real
  shows "\<exists>y \<le> x. x = y + 1"
  by rferrack

lemma
  fixes x :: real
  shows "\<not> (\<exists>z. x + z = x + z + 1)"
  by rferrack

end
