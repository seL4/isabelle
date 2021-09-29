(*  Title:      HOL/Decision_Procs/Parametric_Ferrante_Rackoff.thy
    Author:     Amine Chaieb
*)

section \<open>A formalization of Ferrante and Rackoff's procedure with polynomial parameters, see Paper in CALCULEMUS 2008\<close>

theory Parametric_Ferrante_Rackoff
imports
  Reflected_Multivariate_Polynomial
  Dense_Linear_Order
  DP_Library
  "HOL-Library.Code_Target_Numeral"
begin

subsection \<open>Terms\<close>

datatype (plugins del: size) tm = CP poly | Bound nat | Add tm tm | Mul poly tm
  | Neg tm | Sub tm tm | CNP nat poly tm

instantiation tm :: size
begin

primrec size_tm :: "tm \<Rightarrow> nat"
  where
    "size_tm (CP c) = polysize c"
  | "size_tm (Bound n) = 1"
  | "size_tm (Neg a) = 1 + size_tm a"
  | "size_tm (Add a b) = 1 + size_tm a + size_tm b"
  | "size_tm (Sub a b) = 3 + size_tm a + size_tm b"
  | "size_tm (Mul c a) = 1 + polysize c + size_tm a"
  | "size_tm (CNP n c a) = 3 + polysize c + size_tm a "

instance ..

end

text \<open>Semantics of terms tm.\<close>
primrec Itm :: "'a::field_char_0 list \<Rightarrow> 'a list \<Rightarrow> tm \<Rightarrow> 'a"
  where
    "Itm vs bs (CP c) = (Ipoly vs c)"
  | "Itm vs bs (Bound n) = bs!n"
  | "Itm vs bs (Neg a) = -(Itm vs bs a)"
  | "Itm vs bs (Add a b) = Itm vs bs a + Itm vs bs b"
  | "Itm vs bs (Sub a b) = Itm vs bs a - Itm vs bs b"
  | "Itm vs bs (Mul c a) = (Ipoly vs c) * Itm vs bs a"
  | "Itm vs bs (CNP n c t) = (Ipoly vs c)*(bs!n) + Itm vs bs t"

fun allpolys :: "(poly \<Rightarrow> bool) \<Rightarrow> tm \<Rightarrow> bool"
  where
    "allpolys P (CP c) = P c"
  | "allpolys P (CNP n c p) = (P c \<and> allpolys P p)"
  | "allpolys P (Mul c p) = (P c \<and> allpolys P p)"
  | "allpolys P (Neg p) = allpolys P p"
  | "allpolys P (Add p q) = (allpolys P p \<and> allpolys P q)"
  | "allpolys P (Sub p q) = (allpolys P p \<and> allpolys P q)"
  | "allpolys P p = True"

primrec tmboundslt :: "nat \<Rightarrow> tm \<Rightarrow> bool"
  where
    "tmboundslt n (CP c) = True"
  | "tmboundslt n (Bound m) = (m < n)"
  | "tmboundslt n (CNP m c a) = (m < n \<and> tmboundslt n a)"
  | "tmboundslt n (Neg a) = tmboundslt n a"
  | "tmboundslt n (Add a b) = (tmboundslt n a \<and> tmboundslt n b)"
  | "tmboundslt n (Sub a b) = (tmboundslt n a \<and> tmboundslt n b)"
  | "tmboundslt n (Mul i a) = tmboundslt n a"

primrec tmbound0 :: "tm \<Rightarrow> bool"  \<comment> \<open>a \<open>tm\<close> is \<^emph>\<open>independent\<close> of Bound 0\<close>
  where
    "tmbound0 (CP c) = True"
  | "tmbound0 (Bound n) = (n>0)"
  | "tmbound0 (CNP n c a) = (n\<noteq>0 \<and> tmbound0 a)"
  | "tmbound0 (Neg a) = tmbound0 a"
  | "tmbound0 (Add a b) = (tmbound0 a \<and> tmbound0 b)"
  | "tmbound0 (Sub a b) = (tmbound0 a \<and> tmbound0 b)"
  | "tmbound0 (Mul i a) = tmbound0 a"

lemma tmbound0_I:
  assumes "tmbound0 a"
  shows "Itm vs (b#bs) a = Itm vs (b'#bs) a"
  using assms by (induct a rule: tm.induct) auto

primrec tmbound :: "nat \<Rightarrow> tm \<Rightarrow> bool"  \<comment> \<open>a \<open>tm\<close> is \<^emph>\<open>independent\<close> of Bound n\<close>
  where
    "tmbound n (CP c) = True"
  | "tmbound n (Bound m) = (n \<noteq> m)"
  | "tmbound n (CNP m c a) = (n\<noteq>m \<and> tmbound n a)"
  | "tmbound n (Neg a) = tmbound n a"
  | "tmbound n (Add a b) = (tmbound n a \<and> tmbound n b)"
  | "tmbound n (Sub a b) = (tmbound n a \<and> tmbound n b)"
  | "tmbound n (Mul i a) = tmbound n a"

lemma tmbound0_tmbound_iff: "tmbound 0 t = tmbound0 t"
  by (induct t) auto

lemma tmbound_I:
  assumes bnd: "tmboundslt (length bs) t"
    and nb: "tmbound n t"
    and le: "n \<le> length bs"
  shows "Itm vs (bs[n:=x]) t = Itm vs bs t"
  using nb le bnd
  by (induct t rule: tm.induct) auto

fun decrtm0 :: "tm \<Rightarrow> tm"
  where
    "decrtm0 (Bound n) = Bound (n - 1)"
  | "decrtm0 (Neg a) = Neg (decrtm0 a)"
  | "decrtm0 (Add a b) = Add (decrtm0 a) (decrtm0 b)"
  | "decrtm0 (Sub a b) = Sub (decrtm0 a) (decrtm0 b)"
  | "decrtm0 (Mul c a) = Mul c (decrtm0 a)"
  | "decrtm0 (CNP n c a) = CNP (n - 1) c (decrtm0 a)"
  | "decrtm0 a = a"

fun incrtm0 :: "tm \<Rightarrow> tm"
  where
    "incrtm0 (Bound n) = Bound (n + 1)"
  | "incrtm0 (Neg a) = Neg (incrtm0 a)"
  | "incrtm0 (Add a b) = Add (incrtm0 a) (incrtm0 b)"
  | "incrtm0 (Sub a b) = Sub (incrtm0 a) (incrtm0 b)"
  | "incrtm0 (Mul c a) = Mul c (incrtm0 a)"
  | "incrtm0 (CNP n c a) = CNP (n + 1) c (incrtm0 a)"
  | "incrtm0 a = a"

lemma decrtm0:
  assumes nb: "tmbound0 t"
  shows "Itm vs (x # bs) t = Itm vs bs (decrtm0 t)"
  using nb by (induct t rule: decrtm0.induct) simp_all

lemma incrtm0: "Itm vs (x#bs) (incrtm0 t) = Itm vs bs t"
  by (induct t rule: decrtm0.induct) simp_all

primrec decrtm :: "nat \<Rightarrow> tm \<Rightarrow> tm"
  where
    "decrtm m (CP c) = (CP c)"
  | "decrtm m (Bound n) = (if n < m then Bound n else Bound (n - 1))"
  | "decrtm m (Neg a) = Neg (decrtm m a)"
  | "decrtm m (Add a b) = Add (decrtm m a) (decrtm m b)"
  | "decrtm m (Sub a b) = Sub (decrtm m a) (decrtm m b)"
  | "decrtm m (Mul c a) = Mul c (decrtm m a)"
  | "decrtm m (CNP n c a) = (if n < m then CNP n c (decrtm m a) else CNP (n - 1) c (decrtm m a))"

primrec removen :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "removen n [] = []"
  | "removen n (x#xs) = (if n=0 then xs else (x#(removen (n - 1) xs)))"

lemma removen_same: "n \<ge> length xs \<Longrightarrow> removen n xs = xs"
  by (induct xs arbitrary: n) auto

lemma nth_length_exceeds: "n \<ge> length xs \<Longrightarrow> xs!n = []!(n - length xs)"
  by (induct xs arbitrary: n) auto

lemma removen_length: "length (removen n xs) = (if n \<ge> length xs then length xs else length xs - 1)"
  by (induct xs arbitrary: n) auto

lemma removen_nth:
  "(removen n xs)!m =
    (if n \<ge> length xs then xs!m
     else if m < n then xs!m
     else if m \<le> length xs then xs!(Suc m)
     else []!(m - (length xs - 1)))"
proof (induct xs arbitrary: n m)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  let ?l = "length (x # xs)"
  consider "n \<ge> ?l" | "n < ?l" by arith
  then show ?case
  proof cases
    case 1
    with removen_same[OF this] show ?thesis by simp
  next
    case nl: 2
    consider "m < n" | "m \<ge> n" by arith
    then show ?thesis
    proof cases
      case 1
      then show ?thesis
        using Cons by (cases m) auto
    next
      case 2
      consider "m \<le> ?l" | "m > ?l" by arith
      then show ?thesis
      proof cases
        case 1
        then show ?thesis
          using Cons by (cases m) auto
      next
        case ml: 2
        have th: "length (removen n (x # xs)) = length xs"
          using removen_length[where n = n and xs= "x # xs"] nl by simp
        with ml have "m \<ge> length (removen n (x # xs))"
          by auto
        from th nth_length_exceeds[OF this] have "(removen n (x # xs))!m = [] ! (m - length xs)"
           by auto
        then have "(removen n (x # xs))!m = [] ! (m - (length (x # xs) - 1))"
          by auto
        then show ?thesis
          using ml nl by auto
      qed
    qed
  qed
qed

lemma decrtm:
  assumes bnd: "tmboundslt (length bs) t"
    and nb: "tmbound m t"
    and nle: "m \<le> length bs"
  shows "Itm vs (removen m bs) (decrtm m t) = Itm vs bs t"
  using bnd nb nle by (induct t rule: tm.induct) (auto simp add: removen_nth)

primrec tmsubst0:: "tm \<Rightarrow> tm \<Rightarrow> tm"
  where
    "tmsubst0 t (CP c) = CP c"
  | "tmsubst0 t (Bound n) = (if n=0 then t else Bound n)"
  | "tmsubst0 t (CNP n c a) = (if n=0 then Add (Mul c t) (tmsubst0 t a) else CNP n c (tmsubst0 t a))"
  | "tmsubst0 t (Neg a) = Neg (tmsubst0 t a)"
  | "tmsubst0 t (Add a b) = Add (tmsubst0 t a) (tmsubst0 t b)"
  | "tmsubst0 t (Sub a b) = Sub (tmsubst0 t a) (tmsubst0 t b)"
  | "tmsubst0 t (Mul i a) = Mul i (tmsubst0 t a)"

lemma tmsubst0: "Itm vs (x # bs) (tmsubst0 t a) = Itm vs (Itm vs (x # bs) t # bs) a"
  by (induct a rule: tm.induct) auto

lemma tmsubst0_nb: "tmbound0 t \<Longrightarrow> tmbound0 (tmsubst0 t a)"
  by (induct a rule: tm.induct) auto

primrec tmsubst:: "nat \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm"
  where
    "tmsubst n t (CP c) = CP c"
  | "tmsubst n t (Bound m) = (if n=m then t else Bound m)"
  | "tmsubst n t (CNP m c a) =
      (if n = m then Add (Mul c t) (tmsubst n t a) else CNP m c (tmsubst n t a))"
  | "tmsubst n t (Neg a) = Neg (tmsubst n t a)"
  | "tmsubst n t (Add a b) = Add (tmsubst n t a) (tmsubst n t b)"
  | "tmsubst n t (Sub a b) = Sub (tmsubst n t a) (tmsubst n t b)"
  | "tmsubst n t (Mul i a) = Mul i (tmsubst n t a)"

lemma tmsubst:
  assumes nb: "tmboundslt (length bs) a"
    and nlt: "n \<le> length bs"
  shows "Itm vs bs (tmsubst n t a) = Itm vs (bs[n:= Itm vs bs t]) a"
  using nb nlt
  by (induct a rule: tm.induct) auto

lemma tmsubst_nb0:
  assumes tnb: "tmbound0 t"
  shows "tmbound0 (tmsubst 0 t a)"
  using tnb
  by (induct a rule: tm.induct) auto

lemma tmsubst_nb:
  assumes tnb: "tmbound m t"
  shows "tmbound m (tmsubst m t a)"
  using tnb
  by (induct a rule: tm.induct) auto

lemma incrtm0_tmbound: "tmbound n t \<Longrightarrow> tmbound (Suc n) (incrtm0 t)"
  by (induct t) auto


text \<open>Simplification.\<close>

fun tmadd:: "tm \<Rightarrow> tm \<Rightarrow> tm"
  where
    "tmadd (CNP n1 c1 r1) (CNP n2 c2 r2) =
      (if n1 = n2 then
        let c = c1 +\<^sub>p c2
        in if c = 0\<^sub>p then tmadd r1 r2 else CNP n1 c (tmadd r1 r2)
      else if n1 \<le> n2 then (CNP n1 c1 (tmadd r1 (CNP n2 c2 r2)))
      else (CNP n2 c2 (tmadd (CNP n1 c1 r1) r2)))"
  | "tmadd (CNP n1 c1 r1) t = CNP n1 c1 (tmadd r1 t)"
  | "tmadd t (CNP n2 c2 r2) = CNP n2 c2 (tmadd t r2)"
  | "tmadd (CP b1) (CP b2) = CP (b1 +\<^sub>p b2)"
  | "tmadd a b = Add a b"

lemma tmadd [simp]: "Itm vs bs (tmadd t s) = Itm vs bs (Add t s)"
  apply (induct t s rule: tmadd.induct)
                      apply (simp_all add: Let_def)
  apply (case_tac "c1 +\<^sub>p c2 = 0\<^sub>p")
   apply (case_tac "n1 \<le> n2")
    apply simp_all
   apply (case_tac "n1 = n2")
    apply (simp_all add: algebra_simps)
  apply (simp only: distrib_left [symmetric] polyadd [symmetric])
  apply simp
  done

lemma tmadd_nb0[simp]: "tmbound0 t \<Longrightarrow> tmbound0 s \<Longrightarrow> tmbound0 (tmadd t s)"
  by (induct t s rule: tmadd.induct) (auto simp add: Let_def)

lemma tmadd_nb[simp]: "tmbound n t \<Longrightarrow> tmbound n s \<Longrightarrow> tmbound n (tmadd t s)"
  by (induct t s rule: tmadd.induct) (auto simp add: Let_def)

lemma tmadd_blt[simp]: "tmboundslt n t \<Longrightarrow> tmboundslt n s \<Longrightarrow> tmboundslt n (tmadd t s)"
  by (induct t s rule: tmadd.induct) (auto simp add: Let_def)

lemma tmadd_allpolys_npoly[simp]:
  "allpolys isnpoly t \<Longrightarrow> allpolys isnpoly s \<Longrightarrow> allpolys isnpoly (tmadd t s)"
  by (induct t s rule: tmadd.induct) (simp_all add: Let_def polyadd_norm)

fun tmmul:: "tm \<Rightarrow> poly \<Rightarrow> tm"
  where
    "tmmul (CP j) = (\<lambda>i. CP (i *\<^sub>p j))"
  | "tmmul (CNP n c a) = (\<lambda>i. CNP n (i *\<^sub>p c) (tmmul a i))"
  | "tmmul t = (\<lambda>i. Mul i t)"

lemma tmmul[simp]: "Itm vs bs (tmmul t i) = Itm vs bs (Mul i t)"
  by (induct t arbitrary: i rule: tmmul.induct) (simp_all add: field_simps)

lemma tmmul_nb0[simp]: "tmbound0 t \<Longrightarrow> tmbound0 (tmmul t i)"
  by (induct t arbitrary: i rule: tmmul.induct) auto

lemma tmmul_nb[simp]: "tmbound n t \<Longrightarrow> tmbound n (tmmul t i)"
  by (induct t arbitrary: n rule: tmmul.induct) auto

lemma tmmul_blt[simp]: "tmboundslt n t \<Longrightarrow> tmboundslt n (tmmul t i)"
  by (induct t arbitrary: i rule: tmmul.induct) (auto simp add: Let_def)

lemma tmmul_allpolys_npoly[simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "allpolys isnpoly t \<Longrightarrow> isnpoly c \<Longrightarrow> allpolys isnpoly (tmmul t c)"
  by (induct t rule: tmmul.induct) (simp_all add: Let_def polymul_norm)

definition tmneg :: "tm \<Rightarrow> tm"
  where "tmneg t \<equiv> tmmul t (C (- 1,1))"

definition tmsub :: "tm \<Rightarrow> tm \<Rightarrow> tm"
  where "tmsub s t \<equiv> (if s = t then CP 0\<^sub>p else tmadd s (tmneg t))"

lemma tmneg[simp]: "Itm vs bs (tmneg t) = Itm vs bs (Neg t)"
  using tmneg_def[of t] by simp

lemma tmneg_nb0[simp]: "tmbound0 t \<Longrightarrow> tmbound0 (tmneg t)"
  using tmneg_def by simp

lemma tmneg_nb[simp]: "tmbound n t \<Longrightarrow> tmbound n (tmneg t)"
  using tmneg_def by simp

lemma tmneg_blt[simp]: "tmboundslt n t \<Longrightarrow> tmboundslt n (tmneg t)"
  using tmneg_def by simp

lemma [simp]: "isnpoly (C (-1, 1))"
  by (simp add: isnpoly_def)

lemma tmneg_allpolys_npoly[simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "allpolys isnpoly t \<Longrightarrow> allpolys isnpoly (tmneg t)"
  by (auto simp: tmneg_def)

lemma tmsub[simp]: "Itm vs bs (tmsub a b) = Itm vs bs (Sub a b)"
  using tmsub_def by simp

lemma tmsub_nb0[simp]: "tmbound0 t \<Longrightarrow> tmbound0 s \<Longrightarrow> tmbound0 (tmsub t s)"
  using tmsub_def by simp

lemma tmsub_nb[simp]: "tmbound n t \<Longrightarrow> tmbound n s \<Longrightarrow> tmbound n (tmsub t s)"
  using tmsub_def by simp

lemma tmsub_blt[simp]: "tmboundslt n t \<Longrightarrow> tmboundslt n s \<Longrightarrow> tmboundslt n (tmsub t s)"
  using tmsub_def by simp

lemma tmsub_allpolys_npoly[simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "allpolys isnpoly t \<Longrightarrow> allpolys isnpoly s \<Longrightarrow> allpolys isnpoly (tmsub t s)"
  by (simp add: tmsub_def isnpoly_def)

fun simptm :: "tm \<Rightarrow> tm"
  where
    "simptm (CP j) = CP (polynate j)"
  | "simptm (Bound n) = CNP n (1)\<^sub>p (CP 0\<^sub>p)"
  | "simptm (Neg t) = tmneg (simptm t)"
  | "simptm (Add t s) = tmadd (simptm t) (simptm s)"
  | "simptm (Sub t s) = tmsub (simptm t) (simptm s)"
  | "simptm (Mul i t) =
      (let i' = polynate i in if i' = 0\<^sub>p then CP 0\<^sub>p else tmmul (simptm t) i')"
  | "simptm (CNP n c t) =
      (let c' = polynate c in if c' = 0\<^sub>p then simptm t else tmadd (CNP n c' (CP 0\<^sub>p)) (simptm t))"

lemma polynate_stupid:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "polynate t = 0\<^sub>p \<Longrightarrow> Ipoly bs t = (0::'a)"
  apply (subst polynate[symmetric])
  apply simp
  done

lemma simptm_ci[simp]: "Itm vs bs (simptm t) = Itm vs bs t"
  by (induct t rule: simptm.induct) (auto simp add: Let_def polynate_stupid)

lemma simptm_tmbound0[simp]: "tmbound0 t \<Longrightarrow> tmbound0 (simptm t)"
  by (induct t rule: simptm.induct) (auto simp add: Let_def)

lemma simptm_nb[simp]: "tmbound n t \<Longrightarrow> tmbound n (simptm t)"
  by (induct t rule: simptm.induct) (auto simp add: Let_def)

lemma simptm_nlt[simp]: "tmboundslt n t \<Longrightarrow> tmboundslt n (simptm t)"
  by (induct t rule: simptm.induct) (auto simp add: Let_def)

lemma [simp]: "isnpoly 0\<^sub>p"
  and [simp]: "isnpoly (C (1, 1))"
  by (simp_all add: isnpoly_def)

lemma simptm_allpolys_npoly[simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "allpolys isnpoly (simptm p)"
  by (induct p rule: simptm.induct) (auto simp add: Let_def)

declare let_cong[fundef_cong del]

fun split0 :: "tm \<Rightarrow> poly \<times> tm"
  where
    "split0 (Bound 0) = ((1)\<^sub>p, CP 0\<^sub>p)"
  | "split0 (CNP 0 c t) = (let (c', t') = split0 t in (c +\<^sub>p c', t'))"
  | "split0 (Neg t) = (let (c, t') = split0 t in (~\<^sub>p c, Neg t'))"
  | "split0 (CNP n c t) = (let (c', t') = split0 t in (c', CNP n c t'))"
  | "split0 (Add s t) = (let (c1, s') = split0 s; (c2, t') = split0 t in (c1 +\<^sub>p c2, Add s' t'))"
  | "split0 (Sub s t) = (let (c1, s') = split0 s; (c2, t') = split0 t in (c1 -\<^sub>p c2, Sub s' t'))"
  | "split0 (Mul c t) = (let (c', t') = split0 t in (c *\<^sub>p c', Mul c t'))"
  | "split0 t = (0\<^sub>p, t)"

declare let_cong[fundef_cong]

lemma split0_stupid[simp]: "\<exists>x y. (x, y) = split0 p"
  apply (rule exI[where x="fst (split0 p)"])
  apply (rule exI[where x="snd (split0 p)"])
  apply simp
  done

lemma split0:
  "tmbound 0 (snd (split0 t)) \<and> Itm vs bs (CNP 0 (fst (split0 t)) (snd (split0 t))) = Itm vs bs t"
  apply (induct t rule: split0.induct)
          apply simp
         apply (simp add: Let_def split_def field_simps)
        apply (simp add: Let_def split_def field_simps)
       apply (simp add: Let_def split_def field_simps)
      apply (simp add: Let_def split_def field_simps)
     apply (simp add: Let_def split_def field_simps)
    apply (simp add: Let_def split_def mult.assoc distrib_left[symmetric])
   apply (simp add: Let_def split_def field_simps)
  apply (simp add: Let_def split_def field_simps)
  done

lemma split0_ci: "split0 t = (c',t') \<Longrightarrow> Itm vs bs t = Itm vs bs (CNP 0 c' t')"
proof -
  fix c' t'
  assume "split0 t = (c', t')"
  then have "c' = fst (split0 t)" "t' = snd (split0 t)"
    by auto
  with split0[where t="t" and bs="bs"] show "Itm vs bs t = Itm vs bs (CNP 0 c' t')"
    by simp
qed

lemma split0_nb0:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "split0 t = (c',t') \<Longrightarrow>  tmbound 0 t'"
proof -
  fix c' t'
  assume "split0 t = (c', t')"
  then have "c' = fst (split0 t)" "t' = snd (split0 t)"
    by auto
  with conjunct1[OF split0[where t="t"]] show "tmbound 0 t'"
    by simp
qed

lemma split0_nb0'[simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "tmbound0 (snd (split0 t))"
  using split0_nb0[of t "fst (split0 t)" "snd (split0 t)"]
  by (simp add: tmbound0_tmbound_iff)

lemma split0_nb:
  assumes nb: "tmbound n t"
  shows "tmbound n (snd (split0 t))"
  using nb by (induct t rule: split0.induct) (auto simp add: Let_def split_def)

lemma split0_blt:
  assumes nb: "tmboundslt n t"
  shows "tmboundslt n (snd (split0 t))"
  using nb by (induct t rule: split0.induct) (auto simp add: Let_def split_def)

lemma tmbound_split0: "tmbound 0 t \<Longrightarrow> Ipoly vs (fst (split0 t)) = 0"
  by (induct t rule: split0.induct) (auto simp add: Let_def split_def)

lemma tmboundslt_split0: "tmboundslt n t \<Longrightarrow> Ipoly vs (fst (split0 t)) = 0 \<or> n > 0"
  by (induct t rule: split0.induct) (auto simp add: Let_def split_def)

lemma tmboundslt0_split0: "tmboundslt 0 t \<Longrightarrow> Ipoly vs (fst (split0 t)) = 0"
  by (induct t rule: split0.induct) (auto simp add: Let_def split_def)

lemma allpolys_split0: "allpolys isnpoly p \<Longrightarrow> allpolys isnpoly (snd (split0 p))"
  by (induct p rule: split0.induct) (auto simp  add: isnpoly_def Let_def split_def)

lemma isnpoly_fst_split0:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "allpolys isnpoly p \<Longrightarrow> isnpoly (fst (split0 p))"
  by (induct p rule: split0.induct)
    (auto simp  add: polyadd_norm polysub_norm polyneg_norm polymul_norm Let_def split_def)


subsection \<open>Formulae\<close>

datatype (plugins del: size) fm = T | F | Le tm | Lt tm | Eq tm | NEq tm |
  Not fm | And fm fm | Or fm fm | Imp fm fm | Iff fm fm | E fm | A fm

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
  | "size_fm T = 1"
  | "size_fm F = 1"
  | "size_fm (Le _) = 1"
  | "size_fm (Lt _) = 1"
  | "size_fm (Eq _) = 1"
  | "size_fm (NEq _) = 1"

instance ..

end

lemma fmsize_pos [simp]: "size p > 0" for p :: fm
  by (induct p) simp_all

text \<open>Semantics of formulae (fm).\<close>
primrec Ifm ::"'a::linordered_field list \<Rightarrow> 'a list \<Rightarrow> fm \<Rightarrow> bool"
  where
    "Ifm vs bs T = True"
  | "Ifm vs bs F = False"
  | "Ifm vs bs (Lt a) = (Itm vs bs a < 0)"
  | "Ifm vs bs (Le a) = (Itm vs bs a \<le> 0)"
  | "Ifm vs bs (Eq a) = (Itm vs bs a = 0)"
  | "Ifm vs bs (NEq a) = (Itm vs bs a \<noteq> 0)"
  | "Ifm vs bs (Not p) = (\<not> (Ifm vs bs p))"
  | "Ifm vs bs (And p q) = (Ifm vs bs p \<and> Ifm vs bs q)"
  | "Ifm vs bs (Or p q) = (Ifm vs bs p \<or> Ifm vs bs q)"
  | "Ifm vs bs (Imp p q) = ((Ifm vs bs p) \<longrightarrow> (Ifm vs bs q))"
  | "Ifm vs bs (Iff p q) = (Ifm vs bs p = Ifm vs bs q)"
  | "Ifm vs bs (E p) = (\<exists>x. Ifm vs (x#bs) p)"
  | "Ifm vs bs (A p) = (\<forall>x. Ifm vs (x#bs) p)"

fun not:: "fm \<Rightarrow> fm"
  where
    "not (Not (Not p)) = not p"
  | "not (Not p) = p"
  | "not T = F"
  | "not F = T"
  | "not (Lt t) = Le (tmneg t)"
  | "not (Le t) = Lt (tmneg t)"
  | "not (Eq t) = NEq t"
  | "not (NEq t) = Eq t"
  | "not p = Not p"

lemma not[simp]: "Ifm vs bs (not p) = Ifm vs bs (Not p)"
  by (induct p rule: not.induct) auto

definition conj :: "fm \<Rightarrow> fm \<Rightarrow> fm"
  where "conj p q \<equiv>
    (if p = F \<or> q = F then F
     else if p = T then q
     else if q = T then p
     else if p = q then p
     else And p q)"

lemma conj[simp]: "Ifm vs bs (conj p q) = Ifm vs bs (And p q)"
  by (cases "p=F \<or> q=F", simp_all add: conj_def) (cases p, simp_all)

definition disj :: "fm \<Rightarrow> fm \<Rightarrow> fm"
  where "disj p q \<equiv>
    (if (p = T \<or> q = T) then T
     else if p = F then q
     else if q = F then p
     else if p = q then p
     else Or p q)"

lemma disj[simp]: "Ifm vs bs (disj p q) = Ifm vs bs (Or p q)"
  by (cases "p = T \<or> q = T", simp_all add: disj_def) (cases p, simp_all)

definition imp :: "fm \<Rightarrow> fm \<Rightarrow> fm"
  where "imp p q \<equiv>
    (if p = F \<or> q = T \<or> p = q then T
     else if p = T then q
     else if q = F then not p
     else Imp p q)"

lemma imp[simp]: "Ifm vs bs (imp p q) = Ifm vs bs (Imp p q)"
  by (cases "p = F \<or> q = T") (simp_all add: imp_def)

definition iff :: "fm \<Rightarrow> fm \<Rightarrow> fm"
  where "iff p q \<equiv>
   (if p = q then T
    else if p = Not q \<or> Not p = q then F
    else if p = F then not q
    else if q = F then not p
    else if p = T then q
    else if q = T then p
    else Iff p q)"

lemma iff[simp]: "Ifm vs bs (iff p q) = Ifm vs bs (Iff p q)"
  by (unfold iff_def, cases "p = q", simp, cases "p = Not q", simp) (cases "Not p= q", auto)

text \<open>Quantifier freeness.\<close>
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

text \<open>Boundedness and substitution.\<close>
primrec boundslt :: "nat \<Rightarrow> fm \<Rightarrow> bool"
  where
    "boundslt n T = True"
  | "boundslt n F = True"
  | "boundslt n (Lt t) = tmboundslt n t"
  | "boundslt n (Le t) = tmboundslt n t"
  | "boundslt n (Eq t) = tmboundslt n t"
  | "boundslt n (NEq t) = tmboundslt n t"
  | "boundslt n (Not p) = boundslt n p"
  | "boundslt n (And p q) = (boundslt n p \<and> boundslt n q)"
  | "boundslt n (Or p q) = (boundslt n p \<and> boundslt n q)"
  | "boundslt n (Imp p q) = ((boundslt n p) \<and> (boundslt n q))"
  | "boundslt n (Iff p q) = (boundslt n p \<and> boundslt n q)"
  | "boundslt n (E p) = boundslt (Suc n) p"
  | "boundslt n (A p) = boundslt (Suc n) p"

fun bound0:: "fm \<Rightarrow> bool"  \<comment> \<open>a formula is independent of Bound 0\<close>
  where
    "bound0 T = True"
  | "bound0 F = True"
  | "bound0 (Lt a) = tmbound0 a"
  | "bound0 (Le a) = tmbound0 a"
  | "bound0 (Eq a) = tmbound0 a"
  | "bound0 (NEq a) = tmbound0 a"
  | "bound0 (Not p) = bound0 p"
  | "bound0 (And p q) = (bound0 p \<and> bound0 q)"
  | "bound0 (Or p q) = (bound0 p \<and> bound0 q)"
  | "bound0 (Imp p q) = ((bound0 p) \<and> (bound0 q))"
  | "bound0 (Iff p q) = (bound0 p \<and> bound0 q)"
  | "bound0 p = False"

lemma bound0_I:
  assumes bp: "bound0 p"
  shows "Ifm vs (b#bs) p = Ifm vs (b'#bs) p"
  using bp tmbound0_I[where b="b" and bs="bs" and b'="b'"]
  by (induct p rule: bound0.induct) auto

primrec bound:: "nat \<Rightarrow> fm \<Rightarrow> bool"  \<comment> \<open>a formula is independent of Bound n\<close>
  where
    "bound m T = True"
  | "bound m F = True"
  | "bound m (Lt t) = tmbound m t"
  | "bound m (Le t) = tmbound m t"
  | "bound m (Eq t) = tmbound m t"
  | "bound m (NEq t) = tmbound m t"
  | "bound m (Not p) = bound m p"
  | "bound m (And p q) = (bound m p \<and> bound m q)"
  | "bound m (Or p q) = (bound m p \<and> bound m q)"
  | "bound m (Imp p q) = ((bound m p) \<and> (bound m q))"
  | "bound m (Iff p q) = (bound m p \<and> bound m q)"
  | "bound m (E p) = bound (Suc m) p"
  | "bound m (A p) = bound (Suc m) p"

lemma bound_I:
  assumes bnd: "boundslt (length bs) p"
    and nb: "bound n p"
    and le: "n \<le> length bs"
  shows "Ifm vs (bs[n:=x]) p = Ifm vs bs p"
  using bnd nb le tmbound_I[where bs=bs and vs = vs]
proof (induct p arbitrary: bs n rule: fm.induct)
  case (E p bs n)
  have "Ifm vs ((y#bs)[Suc n:=x]) p = Ifm vs (y#bs) p" for y
  proof -
    from E have bnd: "boundslt (length (y#bs)) p"
      and nb: "bound (Suc n) p" and le: "Suc n \<le> length (y#bs)" by simp+
    from E.hyps[OF bnd nb le tmbound_I] show ?thesis .
  qed
  then show ?case by simp
next
  case (A p bs n)
  have "Ifm vs ((y#bs)[Suc n:=x]) p = Ifm vs (y#bs) p" for y
  proof -
    from A have bnd: "boundslt (length (y#bs)) p"
      and nb: "bound (Suc n) p"
      and le: "Suc n \<le> length (y#bs)"
      by simp_all
    from A.hyps[OF bnd nb le tmbound_I] show ?thesis .
  qed
  then show ?case by simp
qed auto

fun decr0 :: "fm \<Rightarrow> fm"
  where
    "decr0 (Lt a) = Lt (decrtm0 a)"
  | "decr0 (Le a) = Le (decrtm0 a)"
  | "decr0 (Eq a) = Eq (decrtm0 a)"
  | "decr0 (NEq a) = NEq (decrtm0 a)"
  | "decr0 (Not p) = Not (decr0 p)"
  | "decr0 (And p q) = conj (decr0 p) (decr0 q)"
  | "decr0 (Or p q) = disj (decr0 p) (decr0 q)"
  | "decr0 (Imp p q) = imp (decr0 p) (decr0 q)"
  | "decr0 (Iff p q) = iff (decr0 p) (decr0 q)"
  | "decr0 p = p"

lemma decr0:
  assumes "bound0 p"
  shows "Ifm vs (x#bs) p = Ifm vs bs (decr0 p)"
  using assms by (induct p rule: decr0.induct) (simp_all add: decrtm0)

primrec decr :: "nat \<Rightarrow> fm \<Rightarrow> fm"
  where
    "decr m T = T"
  | "decr m F = F"
  | "decr m (Lt t) = (Lt (decrtm m t))"
  | "decr m (Le t) = (Le (decrtm m t))"
  | "decr m (Eq t) = (Eq (decrtm m t))"
  | "decr m (NEq t) = (NEq (decrtm m t))"
  | "decr m (Not p) = Not (decr m p)"
  | "decr m (And p q) = conj (decr m p) (decr m q)"
  | "decr m (Or p q) = disj (decr m p) (decr m q)"
  | "decr m (Imp p q) = imp (decr m p) (decr m q)"
  | "decr m (Iff p q) = iff (decr m p) (decr m q)"
  | "decr m (E p) = E (decr (Suc m) p)"
  | "decr m (A p) = A (decr (Suc m) p)"

lemma decr:
  assumes bnd: "boundslt (length bs) p"
    and nb: "bound m p"
    and nle: "m < length bs"
  shows "Ifm vs (removen m bs) (decr m p) = Ifm vs bs p"
  using bnd nb nle
proof (induct p arbitrary: bs m rule: fm.induct)
  case (E p bs m)
  have "Ifm vs (removen (Suc m) (x#bs)) (decr (Suc m) p) = Ifm vs (x#bs) p" for x
  proof -
    from E
    have bnd: "boundslt (length (x#bs)) p"
      and nb: "bound (Suc m) p"
      and nle: "Suc m < length (x#bs)"
      by auto
    from E(1)[OF bnd nb nle] show ?thesis .
  qed
  then show ?case by auto
next
  case (A p bs m)
  have "Ifm vs (removen (Suc m) (x#bs)) (decr (Suc m) p) = Ifm vs (x#bs) p" for x
  proof -
    from A
    have bnd: "boundslt (length (x#bs)) p"
      and nb: "bound (Suc m) p"
      and nle: "Suc m < length (x#bs)"
      by auto
    from A(1)[OF bnd nb nle] show ?thesis .
  qed
  then show ?case by auto
qed (auto simp add: decrtm removen_nth)

primrec subst0 :: "tm \<Rightarrow> fm \<Rightarrow> fm"
  where
    "subst0 t T = T"
  | "subst0 t F = F"
  | "subst0 t (Lt a) = Lt (tmsubst0 t a)"
  | "subst0 t (Le a) = Le (tmsubst0 t a)"
  | "subst0 t (Eq a) = Eq (tmsubst0 t a)"
  | "subst0 t (NEq a) = NEq (tmsubst0 t a)"
  | "subst0 t (Not p) = Not (subst0 t p)"
  | "subst0 t (And p q) = And (subst0 t p) (subst0 t q)"
  | "subst0 t (Or p q) = Or (subst0 t p) (subst0 t q)"
  | "subst0 t (Imp p q) = Imp (subst0 t p)  (subst0 t q)"
  | "subst0 t (Iff p q) = Iff (subst0 t p) (subst0 t q)"
  | "subst0 t (E p) = E p"
  | "subst0 t (A p) = A p"

lemma subst0:
  assumes qf: "qfree p"
  shows "Ifm vs (x # bs) (subst0 t p) = Ifm vs ((Itm vs (x # bs) t) # bs) p"
  using qf tmsubst0[where x="x" and bs="bs" and t="t"]
  by (induct p rule: fm.induct) auto

lemma subst0_nb:
  assumes bp: "tmbound0 t"
    and qf: "qfree p"
  shows "bound0 (subst0 t p)"
  using qf tmsubst0_nb[OF bp] bp by (induct p rule: fm.induct) auto

primrec subst:: "nat \<Rightarrow> tm \<Rightarrow> fm \<Rightarrow> fm"
  where
    "subst n t T = T"
  | "subst n t F = F"
  | "subst n t (Lt a) = Lt (tmsubst n t a)"
  | "subst n t (Le a) = Le (tmsubst n t a)"
  | "subst n t (Eq a) = Eq (tmsubst n t a)"
  | "subst n t (NEq a) = NEq (tmsubst n t a)"
  | "subst n t (Not p) = Not (subst n t p)"
  | "subst n t (And p q) = And (subst n t p) (subst n t q)"
  | "subst n t (Or p q) = Or (subst n t p) (subst n t q)"
  | "subst n t (Imp p q) = Imp (subst n t p)  (subst n t q)"
  | "subst n t (Iff p q) = Iff (subst n t p) (subst n t q)"
  | "subst n t (E p) = E (subst (Suc n) (incrtm0 t) p)"
  | "subst n t (A p) = A (subst (Suc n) (incrtm0 t) p)"

lemma subst:
  assumes nb: "boundslt (length bs) p"
    and nlm: "n \<le> length bs"
  shows "Ifm vs bs (subst n t p) = Ifm vs (bs[n:= Itm vs bs t]) p"
  using nb nlm
proof (induct p arbitrary: bs n t rule: fm.induct)
  case (E p bs n)
  have "Ifm vs (x#bs) (subst (Suc n) (incrtm0 t) p) =
        Ifm vs (x#bs[n:= Itm vs bs t]) p" for x
  proof -
    from E have bn: "boundslt (length (x#bs)) p"
      by simp
    from E have nlm: "Suc n \<le> length (x#bs)"
      by simp
    from E(1)[OF bn nlm]
    have "Ifm vs (x#bs) (subst (Suc n) (incrtm0 t) p) =
        Ifm vs ((x#bs)[Suc n:= Itm vs (x#bs) (incrtm0 t)]) p"
      by simp
    then show ?thesis
      by (simp add: incrtm0[where x="x" and bs="bs" and t="t"])
  qed
  then show ?case by simp
next
  case (A p bs n)
  have "Ifm vs (x#bs) (subst (Suc n) (incrtm0 t) p) =
        Ifm vs (x#bs[n:= Itm vs bs t]) p" for x
  proof -
    from A have bn: "boundslt (length (x#bs)) p"
      by simp
    from A have nlm: "Suc n \<le> length (x#bs)"
      by simp
    from A(1)[OF bn nlm]
    have "Ifm vs (x#bs) (subst (Suc n) (incrtm0 t) p) =
        Ifm vs ((x#bs)[Suc n:= Itm vs (x#bs) (incrtm0 t)]) p"
      by simp
    then show ?thesis
      by (simp add: incrtm0[where x="x" and bs="bs" and t="t"])
  qed
  then show ?case by simp
qed (auto simp add: tmsubst)

lemma subst_nb:
  assumes "tmbound m t"
  shows "bound m (subst m t p)"
  using assms tmsubst_nb incrtm0_tmbound by (induct p arbitrary: m t rule: fm.induct) auto

lemma not_qf[simp]: "qfree p \<Longrightarrow> qfree (not p)"
  by (induct p rule: not.induct) auto
lemma not_bn0[simp]: "bound0 p \<Longrightarrow> bound0 (not p)"
  by (induct p rule: not.induct) auto
lemma not_nb[simp]: "bound n p \<Longrightarrow> bound n (not p)"
  by (induct p rule: not.induct) auto
lemma not_blt[simp]: "boundslt n p \<Longrightarrow> boundslt n (not p)"
  by (induct p rule: not.induct) auto

lemma conj_qf[simp]: "qfree p \<Longrightarrow> qfree q \<Longrightarrow> qfree (conj p q)"
  using conj_def by auto
lemma conj_nb0[simp]: "bound0 p \<Longrightarrow> bound0 q \<Longrightarrow> bound0 (conj p q)"
  using conj_def by auto
lemma conj_nb[simp]: "bound n p \<Longrightarrow> bound n q \<Longrightarrow> bound n (conj p q)"
  using conj_def by auto
lemma conj_blt[simp]: "boundslt n p \<Longrightarrow> boundslt n q \<Longrightarrow> boundslt n (conj p q)"
  using conj_def by auto

lemma disj_qf[simp]: "qfree p \<Longrightarrow> qfree q \<Longrightarrow> qfree (disj p q)"
  using disj_def by auto
lemma disj_nb0[simp]: "bound0 p \<Longrightarrow> bound0 q \<Longrightarrow> bound0 (disj p q)"
  using disj_def by auto
lemma disj_nb[simp]: "bound n p \<Longrightarrow> bound n q \<Longrightarrow> bound n (disj p q)"
  using disj_def by auto
lemma disj_blt[simp]: "boundslt n p \<Longrightarrow> boundslt n q \<Longrightarrow> boundslt n (disj p q)"
  using disj_def by auto

lemma imp_qf[simp]: "qfree p \<Longrightarrow> qfree q \<Longrightarrow> qfree (imp p q)"
  using imp_def by (cases "p = F \<or> q = T") (simp_all add: imp_def)
lemma imp_nb0[simp]: "bound0 p \<Longrightarrow> bound0 q \<Longrightarrow> bound0 (imp p q)"
  using imp_def by (cases "p = F \<or> q = T \<or> p = q") (simp_all add: imp_def)
lemma imp_nb[simp]: "bound n p \<Longrightarrow> bound n q \<Longrightarrow> bound n (imp p q)"
  using imp_def by (cases "p = F \<or> q = T \<or> p = q") (simp_all add: imp_def)
lemma imp_blt[simp]: "boundslt n p \<Longrightarrow> boundslt n q \<Longrightarrow> boundslt n (imp p q)"
  using imp_def by auto

lemma iff_qf[simp]: "qfree p \<Longrightarrow> qfree q \<Longrightarrow> qfree (iff p q)"
  unfolding iff_def by (cases "p = q") auto
lemma iff_nb0[simp]: "bound0 p \<Longrightarrow> bound0 q \<Longrightarrow> bound0 (iff p q)"
  using iff_def unfolding iff_def by (cases "p = q") auto
lemma iff_nb[simp]: "bound n p \<Longrightarrow> bound n q \<Longrightarrow> bound n (iff p q)"
  using iff_def unfolding iff_def by (cases "p = q") auto
lemma iff_blt[simp]: "boundslt n p \<Longrightarrow> boundslt n q \<Longrightarrow> boundslt n (iff p q)"
  using iff_def by auto
lemma decr0_qf: "bound0 p \<Longrightarrow> qfree (decr0 p)"
  by (induct p) simp_all

fun isatom :: "fm \<Rightarrow> bool"  \<comment> \<open>test for atomicity\<close>
  where
    "isatom T = True"
  | "isatom F = True"
  | "isatom (Lt a) = True"
  | "isatom (Le a) = True"
  | "isatom (Eq a) = True"
  | "isatom (NEq a) = True"
  | "isatom p = False"

lemma bound0_qf: "bound0 p \<Longrightarrow> qfree p"
  by (induct p) simp_all

definition djf :: "('a \<Rightarrow> fm) \<Rightarrow> 'a \<Rightarrow> fm \<Rightarrow> fm"
  where "djf f p q \<equiv>
    (if q = T then T
     else if q = F then f p
     else (let fp = f p in case fp of T \<Rightarrow> T | F \<Rightarrow> q | _ \<Rightarrow> Or (f p) q))"

definition evaldjf :: "('a \<Rightarrow> fm) \<Rightarrow> 'a list \<Rightarrow> fm"
  where "evaldjf f ps \<equiv> foldr (djf f) ps F"

lemma djf_Or: "Ifm vs bs (djf f p q) = Ifm vs bs (Or (f p) q)"
  apply (cases "q = T")
   apply (simp add: djf_def)
  apply (cases "q = F")
   apply (simp add: djf_def)
  apply (cases "f p")
              apply (simp_all add: Let_def djf_def)
  done

lemma evaldjf_ex: "Ifm vs bs (evaldjf f ps) \<longleftrightarrow> (\<exists>p \<in> set ps. Ifm vs bs (f p))"
  by (induct ps) (simp_all add: evaldjf_def djf_Or)

lemma evaldjf_bound0:
  assumes "\<forall>x\<in> set xs. bound0 (f x)"
  shows "bound0 (evaldjf f xs)"
  using assms
  apply (induct xs)
   apply (auto simp add: evaldjf_def djf_def Let_def)
  apply (case_tac "f a")
              apply auto
  done

lemma evaldjf_qf:
  assumes "\<forall>x\<in> set xs. qfree (f x)"
  shows "qfree (evaldjf f xs)"
  using assms
  apply (induct xs)
   apply (auto simp add: evaldjf_def djf_def Let_def)
  apply (case_tac "f a")
              apply auto
  done

fun disjuncts :: "fm \<Rightarrow> fm list"
  where
    "disjuncts (Or p q) = disjuncts p @ disjuncts q"
  | "disjuncts F = []"
  | "disjuncts p = [p]"

lemma disjuncts: "(\<exists>q \<in> set (disjuncts p). Ifm vs bs q) = Ifm vs bs p"
  by (induct p rule: disjuncts.induct) auto

lemma disjuncts_nb:
  assumes "bound0 p"
  shows "\<forall>q \<in> set (disjuncts p). bound0 q"
proof -
  from assms have "list_all bound0 (disjuncts p)"
    by (induct p rule: disjuncts.induct) auto
  then show ?thesis
    by (simp only: list_all_iff)
qed

lemma disjuncts_qf:
  assumes "qfree p"
  shows "\<forall>q \<in> set (disjuncts p). qfree q"
proof -
  from assms have "list_all qfree (disjuncts p)"
    by (induct p rule: disjuncts.induct) auto
  then show ?thesis
    by (simp only: list_all_iff)
qed

definition DJ :: "(fm \<Rightarrow> fm) \<Rightarrow> fm \<Rightarrow> fm"
  where "DJ f p \<equiv> evaldjf f (disjuncts p)"

lemma DJ:
  assumes fdj: "\<forall>p q. Ifm vs bs (f (Or p q)) = Ifm vs bs (Or (f p) (f q))"
    and fF: "f F = F"
  shows "Ifm vs bs (DJ f p) = Ifm vs bs (f p)"
proof -
  have "Ifm vs bs (DJ f p) = (\<exists>q \<in> set (disjuncts p). Ifm vs bs (f q))"
    by (simp add: DJ_def evaldjf_ex)
  also have "\<dots> = Ifm vs bs (f p)"
    using fdj fF by (induct p rule: disjuncts.induct) auto
  finally show ?thesis .
qed

lemma DJ_qf:
  assumes fqf: "\<forall>p. qfree p \<longrightarrow> qfree (f p)"
  shows "\<forall>p. qfree p \<longrightarrow> qfree (DJ f p)"
proof clarify
  fix  p
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
  assumes qe: "\<forall>bs p. qfree p \<longrightarrow> qfree (qe p) \<and> (Ifm vs bs (qe p) = Ifm vs bs (E p))"
  shows "\<forall>bs p. qfree p \<longrightarrow> qfree (DJ qe p) \<and> (Ifm vs bs ((DJ qe p)) = Ifm vs bs (E p))"
proof clarify
  fix p :: fm and bs
  assume qf: "qfree p"
  from qe have qth: "\<forall>p. qfree p \<longrightarrow> qfree (qe p)"
    by blast
  from DJ_qf[OF qth] qf have qfth:"qfree (DJ qe p)"
    by auto
  have "Ifm vs bs (DJ qe p) \<longleftrightarrow> (\<exists>q\<in> set (disjuncts p). Ifm vs bs (qe q))"
    by (simp add: DJ_def evaldjf_ex)
  also have "\<dots> = (\<exists>q \<in> set(disjuncts p). Ifm vs bs (E q))"
    using qe disjuncts_qf[OF qf] by auto
  also have "\<dots> = Ifm vs bs (E p)"
    by (induct p rule: disjuncts.induct) auto
  finally show "qfree (DJ qe p) \<and> Ifm vs bs (DJ qe p) = Ifm vs bs (E p)"
    using qfth by blast
qed

fun conjuncts :: "fm \<Rightarrow> fm list"
  where
    "conjuncts (And p q) = conjuncts p @ conjuncts q"
  | "conjuncts T = []"
  | "conjuncts p = [p]"

definition list_conj :: "fm list \<Rightarrow> fm"
  where "list_conj ps \<equiv> foldr conj ps T"

definition CJNB :: "(fm \<Rightarrow> fm) \<Rightarrow> fm \<Rightarrow> fm"
  where "CJNB f p \<equiv>
    (let cjs = conjuncts p;
      (yes, no) = partition bound0 cjs
     in conj (decr0 (list_conj yes)) (f (list_conj no)))"

lemma conjuncts_qf: "qfree p \<Longrightarrow> \<forall>q \<in> set (conjuncts p). qfree q"
proof -
  assume qf: "qfree p"
  then have "list_all qfree (conjuncts p)"
    by (induct p rule: conjuncts.induct) auto
  then show ?thesis
    by (simp only: list_all_iff)
qed

lemma conjuncts: "(\<forall>q\<in> set (conjuncts p). Ifm vs bs q) = Ifm vs bs p"
  by (induct p rule: conjuncts.induct) auto

lemma conjuncts_nb:
  assumes "bound0 p"
  shows "\<forall>q \<in> set (conjuncts p). bound0 q"
proof -
  from assms have "list_all bound0 (conjuncts p)"
    by (induct p rule:conjuncts.induct) auto
  then show ?thesis
    by (simp only: list_all_iff)
qed

fun islin :: "fm \<Rightarrow> bool"
  where
    "islin (And p q) = (islin p \<and> islin q \<and> p \<noteq> T \<and> p \<noteq> F \<and> q \<noteq> T \<and> q \<noteq> F)"
  | "islin (Or p q) = (islin p \<and> islin q \<and> p \<noteq> T \<and> p \<noteq> F \<and> q \<noteq> T \<and> q \<noteq> F)"
  | "islin (Eq (CNP 0 c s)) = (isnpoly c \<and> c \<noteq> 0\<^sub>p \<and> tmbound0 s \<and> allpolys isnpoly s)"
  | "islin (NEq (CNP 0 c s)) = (isnpoly c \<and> c \<noteq> 0\<^sub>p \<and> tmbound0 s \<and> allpolys isnpoly s)"
  | "islin (Lt (CNP 0 c s)) = (isnpoly c \<and> c \<noteq> 0\<^sub>p \<and> tmbound0 s \<and> allpolys isnpoly s)"
  | "islin (Le (CNP 0 c s)) = (isnpoly c \<and> c \<noteq> 0\<^sub>p \<and> tmbound0 s \<and> allpolys isnpoly s)"
  | "islin (Not p) = False"
  | "islin (Imp p q) = False"
  | "islin (Iff p q) = False"
  | "islin p = bound0 p"

lemma islin_stupid:
  assumes nb: "tmbound0 p"
  shows "islin (Lt p)"
    and "islin (Le p)"
    and "islin (Eq p)"
    and "islin (NEq p)"
  using nb by (cases p, auto, rename_tac nat a b, case_tac nat, auto)+

definition "lt p = (case p of CP (C c) \<Rightarrow> if 0>\<^sub>N c then T else F| _ \<Rightarrow> Lt p)"
definition "le p = (case p of CP (C c) \<Rightarrow> if 0\<ge>\<^sub>N c then T else F | _ \<Rightarrow> Le p)"
definition "eq p = (case p of CP (C c) \<Rightarrow> if c = 0\<^sub>N then T else F | _ \<Rightarrow> Eq p)"
definition "neq p = not (eq p)"

lemma lt: "allpolys isnpoly p \<Longrightarrow> Ifm vs bs (lt p) = Ifm vs bs (Lt p)"
  apply (simp add: lt_def)
  apply (cases p)
        apply simp_all
  apply (rename_tac poly, case_tac poly)
         apply (simp_all add: isnpoly_def)
  done

lemma le: "allpolys isnpoly p \<Longrightarrow> Ifm vs bs (le p) = Ifm vs bs (Le p)"
  apply (simp add: le_def)
  apply (cases p)
        apply simp_all
  apply (rename_tac poly, case_tac poly)
         apply (simp_all add: isnpoly_def)
  done

lemma eq: "allpolys isnpoly p \<Longrightarrow> Ifm vs bs (eq p) = Ifm vs bs (Eq p)"
  apply (simp add: eq_def)
  apply (cases p)
        apply simp_all
  apply (rename_tac poly, case_tac poly)
         apply (simp_all add: isnpoly_def)
  done

lemma neq: "allpolys isnpoly p \<Longrightarrow> Ifm vs bs (neq p) = Ifm vs bs (NEq p)"
  by (simp add: neq_def eq)

lemma lt_lin: "tmbound0 p \<Longrightarrow> islin (lt p)"
  apply (simp add: lt_def)
  apply (cases p)
        apply simp_all
   apply (rename_tac poly, case_tac poly)
          apply simp_all
  apply (rename_tac nat a b, case_tac nat)
   apply simp_all
  done

lemma le_lin: "tmbound0 p \<Longrightarrow> islin (le p)"
  apply (simp add: le_def)
  apply (cases p)
        apply simp_all
   apply (rename_tac poly, case_tac poly)
          apply simp_all
  apply (rename_tac nat a b, case_tac nat)
   apply simp_all
  done

lemma eq_lin: "tmbound0 p \<Longrightarrow> islin (eq p)"
  apply (simp add: eq_def)
  apply (cases p)
        apply simp_all
   apply (rename_tac poly, case_tac poly)
          apply simp_all
  apply (rename_tac nat a b, case_tac nat)
   apply simp_all
  done

lemma neq_lin: "tmbound0 p \<Longrightarrow> islin (neq p)"
  apply (simp add: neq_def eq_def)
  apply (cases p)
        apply simp_all
   apply (rename_tac poly, case_tac poly)
          apply simp_all
  apply (rename_tac nat a b, case_tac nat)
   apply simp_all
  done

definition "simplt t = (let (c,s) = split0 (simptm t) in if c= 0\<^sub>p then lt s else Lt (CNP 0 c s))"
definition "simple t = (let (c,s) = split0 (simptm t) in if c= 0\<^sub>p then le s else Le (CNP 0 c s))"
definition "simpeq t = (let (c,s) = split0 (simptm t) in if c= 0\<^sub>p then eq s else Eq (CNP 0 c s))"
definition "simpneq t = (let (c,s) = split0 (simptm t) in if c= 0\<^sub>p then neq s else NEq (CNP 0 c s))"

lemma simplt_islin [simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "islin (simplt t)"
  unfolding simplt_def
  using split0_nb0'
  by (auto simp add: lt_lin Let_def split_def isnpoly_fst_split0[OF simptm_allpolys_npoly]
      islin_stupid allpolys_split0[OF simptm_allpolys_npoly])

lemma simple_islin [simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "islin (simple t)"
  unfolding simple_def
  using split0_nb0'
  by (auto simp add: Let_def split_def isnpoly_fst_split0[OF simptm_allpolys_npoly]
      islin_stupid allpolys_split0[OF simptm_allpolys_npoly] le_lin)

lemma simpeq_islin [simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "islin (simpeq t)"
  unfolding simpeq_def
  using split0_nb0'
  by (auto simp add: Let_def split_def isnpoly_fst_split0[OF simptm_allpolys_npoly]
      islin_stupid allpolys_split0[OF simptm_allpolys_npoly] eq_lin)

lemma simpneq_islin [simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "islin (simpneq t)"
  unfolding simpneq_def
  using split0_nb0'
  by (auto simp add: Let_def split_def isnpoly_fst_split0[OF simptm_allpolys_npoly]
      islin_stupid allpolys_split0[OF simptm_allpolys_npoly] neq_lin)

lemma really_stupid: "\<not> (\<forall>c1 s'. (c1, s') \<noteq> split0 s)"
  by (cases "split0 s") auto

lemma split0_npoly:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
    and *: "allpolys isnpoly t"
  shows "isnpoly (fst (split0 t))"
    and "allpolys isnpoly (snd (split0 t))"
  using *
  by (induct t rule: split0.induct)
    (auto simp add: Let_def split_def polyadd_norm polymul_norm polyneg_norm
      polysub_norm really_stupid)

lemma simplt[simp]: "Ifm vs bs (simplt t) = Ifm vs bs (Lt t)"
proof -
  have *: "allpolys isnpoly (simptm t)"
    by simp
  let ?t = "simptm t"
  show ?thesis
  proof (cases "fst (split0 ?t) = 0\<^sub>p")
    case True
    then show ?thesis
      using split0[of "simptm t" vs bs] lt[OF split0_npoly(2)[OF *], of vs bs]
      by (simp add: simplt_def Let_def split_def lt)
  next
    case False
    then show ?thesis
      using split0[of "simptm t" vs bs]
      by (simp add: simplt_def Let_def split_def)
  qed
qed

lemma simple[simp]: "Ifm vs bs (simple t) = Ifm vs bs (Le t)"
proof -
  have *: "allpolys isnpoly (simptm t)"
    by simp
  let ?t = "simptm t"
  show ?thesis
  proof (cases "fst (split0 ?t) = 0\<^sub>p")
    case True
    then show ?thesis
      using split0[of "simptm t" vs bs] le[OF split0_npoly(2)[OF *], of vs bs]
      by (simp add: simple_def Let_def split_def le)
  next
    case False
    then show ?thesis
      using split0[of "simptm t" vs bs]
      by (simp add: simple_def Let_def split_def)
  qed
qed

lemma simpeq[simp]: "Ifm vs bs (simpeq t) = Ifm vs bs (Eq t)"
proof -
  have n: "allpolys isnpoly (simptm t)"
    by simp
  let ?t = "simptm t"
  show ?thesis
  proof (cases "fst (split0 ?t) = 0\<^sub>p")
    case True
    then show ?thesis
      using split0[of "simptm t" vs bs] eq[OF split0_npoly(2)[OF n], of vs bs]
      by (simp add: simpeq_def Let_def split_def)
  next
    case False
    then show ?thesis using  split0[of "simptm t" vs bs]
      by (simp add: simpeq_def Let_def split_def)
  qed
qed

lemma simpneq[simp]: "Ifm vs bs (simpneq t) = Ifm vs bs (NEq t)"
proof -
  have n: "allpolys isnpoly (simptm t)"
    by simp
  let ?t = "simptm t"
  show ?thesis
  proof (cases "fst (split0 ?t) = 0\<^sub>p")
    case True
    then show ?thesis
      using split0[of "simptm t" vs bs] neq[OF split0_npoly(2)[OF n], of vs bs]
      by (simp add: simpneq_def Let_def split_def)
  next
    case False
    then show ?thesis
      using split0[of "simptm t" vs bs] by (simp add: simpneq_def Let_def split_def)
  qed
qed

lemma lt_nb: "tmbound0 t \<Longrightarrow> bound0 (lt t)"
  apply (simp add: lt_def)
  apply (cases t)
        apply auto
  apply (rename_tac poly, case_tac poly)
         apply auto
  done

lemma le_nb: "tmbound0 t \<Longrightarrow> bound0 (le t)"
  apply (simp add: le_def)
  apply (cases t)
        apply auto
  apply (rename_tac poly, case_tac poly)
         apply auto
  done

lemma eq_nb: "tmbound0 t \<Longrightarrow> bound0 (eq t)"
  apply (simp add: eq_def)
  apply (cases t)
        apply auto
  apply (rename_tac poly, case_tac poly)
         apply auto
  done

lemma neq_nb: "tmbound0 t \<Longrightarrow> bound0 (neq t)"
  apply (simp add: neq_def eq_def)
  apply (cases t)
        apply auto
  apply (rename_tac poly, case_tac poly)
         apply auto
  done

lemma simplt_nb[simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "tmbound0 t \<Longrightarrow> bound0 (simplt t)"
proof (simp add: simplt_def Let_def split_def)
  assume "tmbound0 t"
  then have *: "tmbound0 (simptm t)"
    by simp
  let ?c = "fst (split0 (simptm t))"
  from tmbound_split0[OF *[unfolded tmbound0_tmbound_iff[symmetric]]]
  have th: "\<forall>bs. Ipoly bs ?c = Ipoly bs 0\<^sub>p"
    by auto
  from isnpoly_fst_split0[OF simptm_allpolys_npoly[of t]]
  have ths: "isnpolyh ?c 0" "isnpolyh 0\<^sub>p 0"
    by (simp_all add: isnpoly_def)
  from iffD1[OF isnpolyh_unique[OF ths] th]
  have "fst (split0 (simptm t)) = 0\<^sub>p" .
  then show "(fst (split0 (simptm t)) = 0\<^sub>p \<longrightarrow> bound0 (lt (snd (split0 (simptm t))))) \<and>
      fst (split0 (simptm t)) = 0\<^sub>p"
    by (simp add: simplt_def Let_def split_def lt_nb)
qed

lemma simple_nb[simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "tmbound0 t \<Longrightarrow> bound0 (simple t)"
proof(simp add: simple_def Let_def split_def)
  assume "tmbound0 t"
  then have *: "tmbound0 (simptm t)"
    by simp
  let ?c = "fst (split0 (simptm t))"
  from tmbound_split0[OF *[unfolded tmbound0_tmbound_iff[symmetric]]]
  have th: "\<forall>bs. Ipoly bs ?c = Ipoly bs 0\<^sub>p"
    by auto
  from isnpoly_fst_split0[OF simptm_allpolys_npoly[of t]]
  have ths: "isnpolyh ?c 0" "isnpolyh 0\<^sub>p 0"
    by (simp_all add: isnpoly_def)
  from iffD1[OF isnpolyh_unique[OF ths] th]
  have "fst (split0 (simptm t)) = 0\<^sub>p" .
  then show "(fst (split0 (simptm t)) = 0\<^sub>p \<longrightarrow> bound0 (le (snd (split0 (simptm t))))) \<and>
      fst (split0 (simptm t)) = 0\<^sub>p"
    by (simp add: simplt_def Let_def split_def le_nb)
qed

lemma simpeq_nb[simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "tmbound0 t \<Longrightarrow> bound0 (simpeq t)"
proof (simp add: simpeq_def Let_def split_def)
  assume "tmbound0 t"
  then have *: "tmbound0 (simptm t)"
    by simp
  let ?c = "fst (split0 (simptm t))"
  from tmbound_split0[OF *[unfolded tmbound0_tmbound_iff[symmetric]]]
  have th: "\<forall>bs. Ipoly bs ?c = Ipoly bs 0\<^sub>p"
    by auto
  from isnpoly_fst_split0[OF simptm_allpolys_npoly[of t]]
  have ths: "isnpolyh ?c 0" "isnpolyh 0\<^sub>p 0"
    by (simp_all add: isnpoly_def)
  from iffD1[OF isnpolyh_unique[OF ths] th]
  have "fst (split0 (simptm t)) = 0\<^sub>p" .
  then show "(fst (split0 (simptm t)) = 0\<^sub>p \<longrightarrow> bound0 (eq (snd (split0 (simptm t))))) \<and>
      fst (split0 (simptm t)) = 0\<^sub>p"
    by (simp add: simpeq_def Let_def split_def eq_nb)
qed

lemma simpneq_nb[simp]:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "tmbound0 t \<Longrightarrow> bound0 (simpneq t)"
proof (simp add: simpneq_def Let_def split_def)
  assume "tmbound0 t"
  then have *: "tmbound0 (simptm t)"
    by simp
  let ?c = "fst (split0 (simptm t))"
  from tmbound_split0[OF *[unfolded tmbound0_tmbound_iff[symmetric]]]
  have th: "\<forall>bs. Ipoly bs ?c = Ipoly bs 0\<^sub>p"
    by auto
  from isnpoly_fst_split0[OF simptm_allpolys_npoly[of t]]
  have ths: "isnpolyh ?c 0" "isnpolyh 0\<^sub>p 0"
    by (simp_all add: isnpoly_def)
  from iffD1[OF isnpolyh_unique[OF ths] th]
  have "fst (split0 (simptm t)) = 0\<^sub>p" .
  then show "(fst (split0 (simptm t)) = 0\<^sub>p \<longrightarrow> bound0 (neq (snd (split0 (simptm t))))) \<and>
      fst (split0 (simptm t)) = 0\<^sub>p"
    by (simp add: simpneq_def Let_def split_def neq_nb)
qed

fun conjs :: "fm \<Rightarrow> fm list"
  where
    "conjs (And p q) = conjs p @ conjs q"
  | "conjs T = []"
  | "conjs p = [p]"

lemma conjs_ci: "(\<forall>q \<in> set (conjs p). Ifm vs bs q) = Ifm vs bs p"
  by (induct p rule: conjs.induct) auto

definition list_disj :: "fm list \<Rightarrow> fm"
  where "list_disj ps \<equiv> foldr disj ps F"

lemma list_conj: "Ifm vs bs (list_conj ps) = (\<forall>p\<in> set ps. Ifm vs bs p)"
  by (induct ps) (auto simp add: list_conj_def)

lemma list_conj_qf: " \<forall>p\<in> set ps. qfree p \<Longrightarrow> qfree (list_conj ps)"
  by (induct ps) (auto simp add: list_conj_def)

lemma list_disj: "Ifm vs bs (list_disj ps) = (\<exists>p\<in> set ps. Ifm vs bs p)"
  by (induct ps) (auto simp add: list_disj_def)

lemma conj_boundslt: "boundslt n p \<Longrightarrow> boundslt n q \<Longrightarrow> boundslt n (conj p q)"
  unfolding conj_def by auto

lemma conjs_nb: "bound n p \<Longrightarrow> \<forall>q\<in> set (conjs p). bound n q"
  apply (induct p rule: conjs.induct)
              apply (unfold conjs.simps)
              apply (unfold set_append)
              apply (unfold ball_Un)
              apply (unfold bound.simps)
              apply auto
  done

lemma conjs_boundslt: "boundslt n p \<Longrightarrow> \<forall>q\<in> set (conjs p). boundslt n q"
  apply (induct p rule: conjs.induct)
              apply (unfold conjs.simps)
              apply (unfold set_append)
              apply (unfold ball_Un)
              apply (unfold boundslt.simps)
              apply blast
             apply simp_all
  done

lemma list_conj_boundslt: " \<forall>p\<in> set ps. boundslt n p \<Longrightarrow> boundslt n (list_conj ps)"
  by (induct ps) (auto simp: list_conj_def)

lemma list_conj_nb:
  assumes "\<forall>p\<in> set ps. bound n p"
  shows "bound n (list_conj ps)"
  using assms by (induct ps) (auto simp: list_conj_def)

lemma list_conj_nb': "\<forall>p\<in>set ps. bound0 p \<Longrightarrow> bound0 (list_conj ps)"
  by (induct ps) (auto simp: list_conj_def)

lemma CJNB_qe:
  assumes qe: "\<forall>bs p. qfree p \<longrightarrow> qfree (qe p) \<and> (Ifm vs bs (qe p) = Ifm vs bs (E p))"
  shows "\<forall>bs p. qfree p \<longrightarrow> qfree (CJNB qe p) \<and> (Ifm vs bs ((CJNB qe p)) = Ifm vs bs (E p))"
proof clarify
  fix bs p
  assume qfp: "qfree p"
  let ?cjs = "conjuncts p"
  let ?yes = "fst (partition bound0 ?cjs)"
  let ?no = "snd (partition bound0 ?cjs)"
  let ?cno = "list_conj ?no"
  let ?cyes = "list_conj ?yes"
  have part: "partition bound0 ?cjs = (?yes,?no)"
    by simp
  from partition_P[OF part] have "\<forall>q\<in> set ?yes. bound0 q"
    by blast
  then have yes_nb: "bound0 ?cyes"
    by (simp add: list_conj_nb')
  then have yes_qf: "qfree (decr0 ?cyes)"
    by (simp add: decr0_qf)
  from conjuncts_qf[OF qfp] partition_set[OF part]
  have " \<forall>q\<in> set ?no. qfree q"
    by auto
  then have no_qf: "qfree ?cno"
    by (simp add: list_conj_qf)
  with qe have cno_qf:"qfree (qe ?cno)"
    and noE: "Ifm vs bs (qe ?cno) = Ifm vs bs (E ?cno)"
    by blast+
  from cno_qf yes_qf have qf: "qfree (CJNB qe p)"
    by (simp add: CJNB_def Let_def split_def)
  have "Ifm vs bs p = ((Ifm vs bs ?cyes) \<and> (Ifm vs bs ?cno))" for bs
  proof -
    from conjuncts have "Ifm vs bs p = (\<forall>q\<in> set ?cjs. Ifm vs bs q)"
      by blast
    also have "\<dots> = ((\<forall>q\<in> set ?yes. Ifm vs bs q) \<and> (\<forall>q\<in> set ?no. Ifm vs bs q))"
      using partition_set[OF part] by auto
    finally show ?thesis
      using list_conj[of vs bs] by simp
  qed
  then have "Ifm vs bs (E p) = (\<exists>x. (Ifm vs (x#bs) ?cyes) \<and> (Ifm vs (x#bs) ?cno))"
    by simp
  also fix y have "\<dots> = (\<exists>x. (Ifm vs (y#bs) ?cyes) \<and> (Ifm vs (x#bs) ?cno))"
    using bound0_I[OF yes_nb, where bs="bs" and b'="y"] by blast
  also have "\<dots> = (Ifm vs bs (decr0 ?cyes) \<and> Ifm vs bs (E ?cno))"
    by (auto simp add: decr0[OF yes_nb] simp del: partition_filter_conv)
  also have "\<dots> = (Ifm vs bs (conj (decr0 ?cyes) (qe ?cno)))"
    using qe[rule_format, OF no_qf] by auto
  finally have "Ifm vs bs (E p) = Ifm vs bs (CJNB qe p)"
    by (simp add: Let_def CJNB_def split_def)
  with qf show "qfree (CJNB qe p) \<and> Ifm vs bs (CJNB qe p) = Ifm vs bs (E p)"
    by blast
qed

fun simpfm :: "fm \<Rightarrow> fm"
  where
    "simpfm (Lt t) = simplt (simptm t)"
  | "simpfm (Le t) = simple (simptm t)"
  | "simpfm (Eq t) = simpeq(simptm t)"
  | "simpfm (NEq t) = simpneq(simptm t)"
  | "simpfm (And p q) = conj (simpfm p) (simpfm q)"
  | "simpfm (Or p q) = disj (simpfm p) (simpfm q)"
  | "simpfm (Imp p q) = disj (simpfm (Not p)) (simpfm q)"
  | "simpfm (Iff p q) =
      disj (conj (simpfm p) (simpfm q)) (conj (simpfm (Not p)) (simpfm (Not q)))"
  | "simpfm (Not (And p q)) = disj (simpfm (Not p)) (simpfm (Not q))"
  | "simpfm (Not (Or p q)) = conj (simpfm (Not p)) (simpfm (Not q))"
  | "simpfm (Not (Imp p q)) = conj (simpfm p) (simpfm (Not q))"
  | "simpfm (Not (Iff p q)) =
      disj (conj (simpfm p) (simpfm (Not q))) (conj (simpfm (Not p)) (simpfm q))"
  | "simpfm (Not (Eq t)) = simpneq t"
  | "simpfm (Not (NEq t)) = simpeq t"
  | "simpfm (Not (Le t)) = simplt (Neg t)"
  | "simpfm (Not (Lt t)) = simple (Neg t)"
  | "simpfm (Not (Not p)) = simpfm p"
  | "simpfm (Not T) = F"
  | "simpfm (Not F) = T"
  | "simpfm p = p"

lemma simpfm[simp]: "Ifm vs bs (simpfm p) = Ifm vs bs p"
  by (induct p arbitrary: bs rule: simpfm.induct) auto

lemma simpfm_bound0:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "bound0 p \<Longrightarrow> bound0 (simpfm p)"
  by (induct p rule: simpfm.induct) auto

lemma lt_qf[simp]: "qfree (lt t)"
  apply (cases t)
        apply (auto simp add: lt_def)
  apply (rename_tac poly, case_tac poly)
         apply auto
  done

lemma le_qf[simp]: "qfree (le t)"
  apply (cases t)
        apply (auto simp add: le_def)
  apply (rename_tac poly, case_tac poly)
         apply auto
  done

lemma eq_qf[simp]: "qfree (eq t)"
  apply (cases t)
        apply (auto simp add: eq_def)
  apply (rename_tac poly, case_tac poly)
         apply auto
  done

lemma neq_qf[simp]: "qfree (neq t)"
  by (simp add: neq_def)

lemma simplt_qf[simp]: "qfree (simplt t)"
  by (simp add: simplt_def Let_def split_def)

lemma simple_qf[simp]: "qfree (simple t)"
  by (simp add: simple_def Let_def split_def)

lemma simpeq_qf[simp]: "qfree (simpeq t)"
  by (simp add: simpeq_def Let_def split_def)

lemma simpneq_qf[simp]: "qfree (simpneq t)"
  by (simp add: simpneq_def Let_def split_def)

lemma simpfm_qf[simp]: "qfree p \<Longrightarrow> qfree (simpfm p)"
  by (induct p rule: simpfm.induct) auto

lemma disj_lin: "islin p \<Longrightarrow> islin q \<Longrightarrow> islin (disj p q)"
  by (simp add: disj_def)

lemma conj_lin: "islin p \<Longrightarrow> islin q \<Longrightarrow> islin (conj p q)"
  by (simp add: conj_def)

lemma
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "qfree p \<Longrightarrow> islin (simpfm p)"
  by (induct p rule: simpfm.induct) (simp_all add: conj_lin disj_lin)

fun prep :: "fm \<Rightarrow> fm"
  where
    "prep (E T) = T"
  | "prep (E F) = F"
  | "prep (E (Or p q)) = disj (prep (E p)) (prep (E q))"
  | "prep (E (Imp p q)) = disj (prep (E (Not p))) (prep (E q))"
  | "prep (E (Iff p q)) = disj (prep (E (And p q))) (prep (E (And (Not p) (Not q))))"
  | "prep (E (Not (And p q))) = disj (prep (E (Not p))) (prep (E(Not q)))"
  | "prep (E (Not (Imp p q))) = prep (E (And p (Not q)))"
  | "prep (E (Not (Iff p q))) = disj (prep (E (And p (Not q)))) (prep (E(And (Not p) q)))"
  | "prep (E p) = E (prep p)"
  | "prep (A (And p q)) = conj (prep (A p)) (prep (A q))"
  | "prep (A p) = prep (Not (E (Not p)))"
  | "prep (Not (Not p)) = prep p"
  | "prep (Not (And p q)) = disj (prep (Not p)) (prep (Not q))"
  | "prep (Not (A p)) = prep (E (Not p))"
  | "prep (Not (Or p q)) = conj (prep (Not p)) (prep (Not q))"
  | "prep (Not (Imp p q)) = conj (prep p) (prep (Not q))"
  | "prep (Not (Iff p q)) = disj (prep (And p (Not q))) (prep (And (Not p) q))"
  | "prep (Not p) = not (prep p)"
  | "prep (Or p q) = disj (prep p) (prep q)"
  | "prep (And p q) = conj (prep p) (prep q)"
  | "prep (Imp p q) = prep (Or (Not p) q)"
  | "prep (Iff p q) = disj (prep (And p q)) (prep (And (Not p) (Not q)))"
  | "prep p = p"

lemma prep: "Ifm vs bs (prep p) = Ifm vs bs p"
  by (induct p arbitrary: bs rule: prep.induct) auto


text \<open>Generic quantifier elimination.\<close>
fun qelim :: "fm \<Rightarrow> (fm \<Rightarrow> fm) \<Rightarrow> fm"
  where
    "qelim (E p) = (\<lambda>qe. DJ (CJNB qe) (qelim p qe))"
  | "qelim (A p) = (\<lambda>qe. not (qe ((qelim (Not p) qe))))"
  | "qelim (Not p) = (\<lambda>qe. not (qelim p qe))"
  | "qelim (And p q) = (\<lambda>qe. conj (qelim p qe) (qelim q qe))"
  | "qelim (Or  p q) = (\<lambda>qe. disj (qelim p qe) (qelim q qe))"
  | "qelim (Imp p q) = (\<lambda>qe. imp (qelim p qe) (qelim q qe))"
  | "qelim (Iff p q) = (\<lambda>qe. iff (qelim p qe) (qelim q qe))"
  | "qelim p = (\<lambda>y. simpfm p)"

lemma qelim:
  assumes qe_inv: "\<forall>bs p. qfree p \<longrightarrow> qfree (qe p) \<and> (Ifm vs bs (qe p) = Ifm vs bs (E p))"
  shows "\<And> bs. qfree (qelim p qe) \<and> (Ifm vs bs (qelim p qe) = Ifm vs bs p)"
  using qe_inv DJ_qe[OF CJNB_qe[OF qe_inv]]
  by (induct p rule: qelim.induct) auto


subsection \<open>Core Procedure\<close>

fun minusinf:: "fm \<Rightarrow> fm"  \<comment> \<open>virtual substitution of \<open>-\<infinity>\<close>\<close>
  where
    "minusinf (And p q) = conj (minusinf p) (minusinf q)"
  | "minusinf (Or p q) = disj (minusinf p) (minusinf q)"
  | "minusinf (Eq  (CNP 0 c e)) = conj (eq (CP c)) (eq e)"
  | "minusinf (NEq (CNP 0 c e)) = disj (not (eq e)) (not (eq (CP c)))"
  | "minusinf (Lt  (CNP 0 c e)) = disj (conj (eq (CP c)) (lt e)) (lt (CP (~\<^sub>p c)))"
  | "minusinf (Le  (CNP 0 c e)) = disj (conj (eq (CP c)) (le e)) (lt (CP (~\<^sub>p c)))"
  | "minusinf p = p"

fun plusinf:: "fm \<Rightarrow> fm"  \<comment> \<open>virtual substitution of \<open>+\<infinity>\<close>\<close>
  where
    "plusinf (And p q) = conj (plusinf p) (plusinf q)"
  | "plusinf (Or p q) = disj (plusinf p) (plusinf q)"
  | "plusinf (Eq  (CNP 0 c e)) = conj (eq (CP c)) (eq e)"
  | "plusinf (NEq (CNP 0 c e)) = disj (not (eq e)) (not (eq (CP c)))"
  | "plusinf (Lt  (CNP 0 c e)) = disj (conj (eq (CP c)) (lt e)) (lt (CP c))"
  | "plusinf (Le  (CNP 0 c e)) = disj (conj (eq (CP c)) (le e)) (lt (CP c))"
  | "plusinf p = p"

lemma minusinf_inf:
  assumes "islin p"
  shows "\<exists>z. \<forall>x < z. Ifm vs (x#bs) (minusinf p) \<longleftrightarrow> Ifm vs (x#bs) p"
  using assms
proof (induct p rule: minusinf.induct)
  case 1
  then show ?case
    apply auto
    apply (rule_tac x="min z za" in exI)
    apply auto
    done
next
  case 2
  then show ?case
    apply auto
    apply (rule_tac x="min z za" in exI)
    apply auto
    done
next
  case (3 c e)
  then have nbe: "tmbound0 e"
    by simp
  from 3 have nc: "allpolys isnpoly (CP c)" "allpolys isnpoly e"
    by simp_all
  note eqs = eq[OF nc(1), where ?'a = 'a] eq[OF nc(2), where ?'a = 'a]
  let ?c = "Ipoly vs c"
  fix y
  let ?e = "Itm vs (y#bs) e"
  consider "?c = 0" | "?c > 0" | "?c < 0" by arith
  then show ?case
  proof cases
    case 1
    then show ?thesis
      using eq[OF nc(2), of vs] eq[OF nc(1), of vs] by auto
  next
    case c: 2
    have "Ifm vs (x#bs) (Eq (CNP 0 c e)) = Ifm vs (x#bs) (minusinf (Eq (CNP 0 c e)))"
      if "x < -?e / ?c" for x
    proof -
      from that have "?c * x < - ?e"
        using pos_less_divide_eq[OF c, where a="x" and b="-?e"]
        by (simp add: mult.commute)
      then have "?c * x + ?e < 0"
        by simp
      then show ?thesis
        using eqs tmbound0_I[OF nbe, where b="y" and b'="x" and vs=vs and bs=bs] by auto
    qed
    then show ?thesis by auto
  next
    case c: 3
    have "Ifm vs (x#bs) (Eq (CNP 0 c e)) = Ifm vs (x#bs) (minusinf (Eq (CNP 0 c e)))"
      if "x < -?e / ?c" for x
    proof -
      from that have "?c * x > - ?e"
        using neg_less_divide_eq[OF c, where a="x" and b="-?e"]
        by (simp add: mult.commute)
      then have "?c * x + ?e > 0"
        by simp
      then show ?thesis
        using tmbound0_I[OF nbe, where b="y" and b'="x"] eqs by auto
    qed
    then show ?thesis by auto
  qed
next
  case (4 c e)
  then have nbe: "tmbound0 e"
    by simp
  from 4 have nc: "allpolys isnpoly (CP c)" "allpolys isnpoly e"
    by simp_all
  note eqs = eq[OF nc(1), where ?'a = 'a] eq[OF nc(2), where ?'a = 'a]
  let ?c = "Ipoly vs c"
  fix y
  let ?e = "Itm vs (y#bs) e"
  consider "?c = 0" | "?c > 0" | "?c < 0"
    by arith
  then show ?case
  proof cases
    case 1
    then show ?thesis
      using eqs by auto
  next
    case c: 2
    have "Ifm vs (x#bs) (NEq (CNP 0 c e)) = Ifm vs (x#bs) (minusinf (NEq (CNP 0 c e)))"
      if "x < -?e / ?c" for x
    proof -
      from that have "?c * x < - ?e"
        using pos_less_divide_eq[OF c, where a="x" and b="-?e"]
        by (simp add: mult.commute)
      then have "?c * x + ?e < 0"
        by simp
      then show ?thesis
        using eqs tmbound0_I[OF nbe, where b="y" and b'="x"] by auto
    qed
    then show ?thesis by auto
  next
    case c: 3
    have "Ifm vs (x#bs) (NEq (CNP 0 c e)) = Ifm vs (x#bs) (minusinf (NEq (CNP 0 c e)))"
      if "x < -?e / ?c" for x
    proof -
      from that have "?c * x > - ?e"
        using neg_less_divide_eq[OF c, where a="x" and b="-?e"]
        by (simp add: mult.commute)
      then have "?c * x + ?e > 0"
        by simp
      then show ?thesis
        using eqs tmbound0_I[OF nbe, where b="y" and b'="x"] by auto
    qed
    then show ?thesis by auto
  qed
next
  case (5 c e)
  then have nbe: "tmbound0 e"
    by simp
  from 5 have nc: "allpolys isnpoly (CP c)" "allpolys isnpoly e"
    by simp_all
  then have nc': "allpolys isnpoly (CP (~\<^sub>p c))"
    by (simp add: polyneg_norm)
  note eqs = lt[OF nc', where ?'a = 'a] eq [OF nc(1), where ?'a = 'a] lt[OF nc(2), where ?'a = 'a]
  let ?c = "Ipoly vs c"
  fix y
  let ?e = "Itm vs (y#bs) e"
  consider "?c = 0" | "?c > 0" | "?c < 0"
    by arith
  then show ?case
  proof cases
    case 1
    then show ?thesis using eqs by auto
  next
    case c: 2
    have "Ifm vs (x#bs) (Lt (CNP 0 c e)) = Ifm vs (x#bs) (minusinf (Lt (CNP 0 c e)))"
      if "x < -?e / ?c" for x
    proof -
      from that have "?c * x < - ?e"
        using pos_less_divide_eq[OF c, where a="x" and b="-?e"]
        by (simp add: mult.commute)
      then have "?c * x + ?e < 0" by simp
      then show ?thesis
        using tmbound0_I[OF nbe, where b="y" and b'="x"] c eqs by auto
    qed
    then show ?thesis by auto
  next
    case c: 3
    have "Ifm vs (x#bs) (Lt (CNP 0 c e)) = Ifm vs (x#bs) (minusinf (Lt (CNP 0 c e)))"
      if "x < -?e / ?c" for x
    proof -
      from that have "?c * x > - ?e"
        using neg_less_divide_eq[OF c, where a="x" and b="-?e"]
        by (simp add: mult.commute)
      then have "?c * x + ?e > 0"
        by simp
      then show ?thesis
        using eqs tmbound0_I[OF nbe, where b="y" and b'="x"] c by auto
    qed
    then show ?thesis by auto
  qed
next
  case (6 c e)
  then have nbe: "tmbound0 e"
    by simp
  from 6 have nc: "allpolys isnpoly (CP c)" "allpolys isnpoly e"
    by simp_all
  then have nc': "allpolys isnpoly (CP (~\<^sub>p c))"
    by (simp add: polyneg_norm)
  note eqs = lt[OF nc', where ?'a = 'a] eq [OF nc(1), where ?'a = 'a] le[OF nc(2), where ?'a = 'a]
  let ?c = "Ipoly vs c"
  fix y
  let ?e = "Itm vs (y#bs) e"
  consider "?c = 0" | "?c > 0" | "?c < 0" by arith
  then show ?case
  proof cases
    case 1
    then show ?thesis using eqs by auto
  next
    case c: 2
    have "Ifm vs (x#bs) (Le (CNP 0 c e)) = Ifm vs (x#bs) (minusinf (Le (CNP 0 c e)))"
      if "x < -?e / ?c" for x
    proof -
      from that have "?c * x < - ?e"
        using pos_less_divide_eq[OF c, where a="x" and b="-?e"]
        by (simp add: mult.commute)
      then have "?c * x + ?e < 0"
        by simp
      then show ?thesis
        using tmbound0_I[OF nbe, where b="y" and b'="x"] c eqs
        by auto
    qed
    then show ?thesis by auto
  next
    case c: 3
    have "Ifm vs (x#bs) (Le (CNP 0 c e)) = Ifm vs (x#bs) (minusinf (Le (CNP 0 c e)))"
      if "x < -?e / ?c" for x
    proof -
      from that have "?c * x > - ?e"
        using neg_less_divide_eq[OF c, where a="x" and b="-?e"]
        by (simp add: mult.commute)
      then have "?c * x + ?e > 0"
        by simp
      then show ?thesis
        using tmbound0_I[OF nbe, where b="y" and b'="x"] c eqs
        by auto
    qed
    then show ?thesis by auto
  qed
qed auto

lemma plusinf_inf:
  assumes "islin p"
  shows "\<exists>z. \<forall>x > z. Ifm vs (x#bs) (plusinf p) \<longleftrightarrow> Ifm vs (x#bs) p"
  using assms
proof (induct p rule: plusinf.induct)
  case 1
  then show ?case
    apply auto
    apply (rule_tac x="max z za" in exI)
    apply auto
    done
next
  case 2
  then show ?case
    apply auto
    apply (rule_tac x="max z za" in exI)
    apply auto
    done
next
  case (3 c e)
  then have nbe: "tmbound0 e"
    by simp
  from 3 have nc: "allpolys isnpoly (CP c)" "allpolys isnpoly e"
    by simp_all
  note eqs = eq[OF nc(1), where ?'a = 'a] eq[OF nc(2), where ?'a = 'a]
  let ?c = "Ipoly vs c"
  fix y
  let ?e = "Itm vs (y#bs) e"
  consider "?c = 0" | "?c > 0" | "?c < 0" by arith
  then show ?case
  proof cases
    case 1
    then show ?thesis
      using eq[OF nc(2), of vs] eq[OF nc(1), of vs] by auto
  next
    case c: 2
    have "Ifm vs (x#bs) (Eq (CNP 0 c e)) = Ifm vs (x#bs) (plusinf (Eq (CNP 0 c e)))"
      if "x > -?e / ?c" for x
    proof -
      from that have "?c * x > - ?e"
        using pos_divide_less_eq[OF c, where a="x" and b="-?e"]
        by (simp add: mult.commute)
      then have "?c * x + ?e > 0"
        by simp
      then show ?thesis
        using eqs tmbound0_I[OF nbe, where b="y" and b'="x" and vs=vs and bs=bs] by auto
    qed
    then show ?thesis by auto
  next
    case c: 3
    have "Ifm vs (x#bs) (Eq (CNP 0 c e)) = Ifm vs (x#bs) (plusinf (Eq (CNP 0 c e)))"
      if "x > -?e / ?c" for x
    proof -
      from that have "?c * x < - ?e"
        using neg_divide_less_eq[OF c, where a="x" and b="-?e"]
        by (simp add: mult.commute)
      then have "?c * x + ?e < 0" by simp
      then show ?thesis
        using tmbound0_I[OF nbe, where b="y" and b'="x"] eqs by auto
    qed
    then show ?thesis by auto
  qed
next
  case (4 c e)
  then have nbe: "tmbound0 e"
    by simp
  from 4 have nc: "allpolys isnpoly (CP c)" "allpolys isnpoly e"
    by simp_all
  note eqs = eq[OF nc(1), where ?'a = 'a] eq[OF nc(2), where ?'a = 'a]
  let ?c = "Ipoly vs c"
  fix y
  let ?e = "Itm vs (y#bs) e"
  consider "?c = 0" | "?c > 0" | "?c < 0" by arith
  then show ?case
  proof cases
    case 1
    then show ?thesis using eqs by auto
  next
    case c: 2
    have "Ifm vs (x#bs) (NEq (CNP 0 c e)) = Ifm vs (x#bs) (plusinf (NEq (CNP 0 c e)))"
      if "x > -?e / ?c" for x
    proof -
      from that have "?c * x > - ?e"
        using pos_divide_less_eq[OF c, where a="x" and b="-?e"]
        by (simp add: mult.commute)
      then have "?c * x + ?e > 0"
        by simp
      then show ?thesis
        using eqs tmbound0_I[OF nbe, where b="y" and b'="x"] by auto
    qed
    then show ?thesis by auto
  next
    case c: 3
    have "Ifm vs (x#bs) (NEq (CNP 0 c e)) = Ifm vs (x#bs) (plusinf (NEq (CNP 0 c e)))"
      if "x > -?e / ?c" for x
    proof -
      from that have "?c * x < - ?e"
        using neg_divide_less_eq[OF c, where a="x" and b="-?e"]
        by (simp add: mult.commute)
      then have "?c * x + ?e < 0"
        by simp
      then show ?thesis
        using eqs tmbound0_I[OF nbe, where b="y" and b'="x"] by auto
    qed
    then show ?thesis by auto
  qed
next
  case (5 c e)
  then have nbe: "tmbound0 e"
    by simp
  from 5 have nc: "allpolys isnpoly (CP c)" "allpolys isnpoly e"
    by simp_all
  then have nc': "allpolys isnpoly (CP (~\<^sub>p c))"
    by (simp add: polyneg_norm)
  note eqs = lt[OF nc(1), where ?'a = 'a] lt[OF nc', where ?'a = 'a] eq [OF nc(1), where ?'a = 'a] lt[OF nc(2), where ?'a = 'a]
  let ?c = "Ipoly vs c"
  fix y
  let ?e = "Itm vs (y#bs) e"
  consider "?c = 0" | "?c > 0" | "?c < 0" by arith
  then show ?case
  proof cases
    case 1
    then show ?thesis using eqs by auto
  next
    case c: 2
    have "Ifm vs (x#bs) (Lt (CNP 0 c e)) = Ifm vs (x#bs) (plusinf (Lt (CNP 0 c e)))"
      if "x > -?e / ?c" for x
    proof -
      from that have "?c * x > - ?e"
        using pos_divide_less_eq[OF c, where a="x" and b="-?e"]
        by (simp add: mult.commute)
      then have "?c * x + ?e > 0"
        by simp
      then show ?thesis
        using tmbound0_I[OF nbe, where b="y" and b'="x"] c eqs by auto
    qed
    then show ?thesis by auto
  next
    case c: 3
    have "Ifm vs (x#bs) (Lt (CNP 0 c e)) = Ifm vs (x#bs) (plusinf (Lt (CNP 0 c e)))"
      if "x > -?e / ?c" for x
    proof -
      from that have "?c * x < - ?e"
        using neg_divide_less_eq[OF c, where a="x" and b="-?e"]
        by (simp add: mult.commute)
      then have "?c * x + ?e < 0"
        by simp
      then show ?thesis
        using eqs tmbound0_I[OF nbe, where b="y" and b'="x"] c by auto
    qed
    then show ?thesis by auto
  qed
next
  case (6 c e)
  then have nbe: "tmbound0 e"
    by simp
  from 6 have nc: "allpolys isnpoly (CP c)" "allpolys isnpoly e"
    by simp_all
  then have nc': "allpolys isnpoly (CP (~\<^sub>p c))"
    by (simp add: polyneg_norm)
  note eqs = lt[OF nc(1), where ?'a = 'a] eq [OF nc(1), where ?'a = 'a] le[OF nc(2), where ?'a = 'a]
  let ?c = "Ipoly vs c"
  fix y
  let ?e = "Itm vs (y#bs) e"
  consider "?c = 0" | "?c > 0" | "?c < 0" by arith
  then show ?case
  proof cases
    case 1
    then show ?thesis using eqs by auto
  next
    case c: 2
    have "Ifm vs (x#bs) (Le (CNP 0 c e)) = Ifm vs (x#bs) (plusinf (Le (CNP 0 c e)))"
      if "x > -?e / ?c" for x
    proof -
      from that have "?c * x > - ?e"
        using pos_divide_less_eq[OF c, where a="x" and b="-?e"]
        by (simp add: mult.commute)
      then have "?c * x + ?e > 0"
        by simp
      then show ?thesis
        using tmbound0_I[OF nbe, where b="y" and b'="x"] c eqs by auto
    qed
    then show ?thesis by auto
  next
    case c: 3
    have "Ifm vs (x#bs) (Le (CNP 0 c e)) = Ifm vs (x#bs) (plusinf (Le (CNP 0 c e)))"
      if "x > -?e / ?c" for x
    proof -
      from that have "?c * x < - ?e"
        using neg_divide_less_eq[OF c, where a="x" and b="-?e"]
        by (simp add: mult.commute)
      then have "?c * x + ?e < 0"
        by simp
      then show ?thesis
        using tmbound0_I[OF nbe, where b="y" and b'="x"] c eqs by auto
    qed
    then show ?thesis by auto
  qed
qed auto

lemma minusinf_nb: "islin p \<Longrightarrow> bound0 (minusinf p)"
  by (induct p rule: minusinf.induct) (auto simp add: eq_nb lt_nb le_nb)

lemma plusinf_nb: "islin p \<Longrightarrow> bound0 (plusinf p)"
  by (induct p rule: minusinf.induct) (auto simp add: eq_nb lt_nb le_nb)

lemma minusinf_ex:
  assumes lp: "islin p"
    and ex: "Ifm vs (x#bs) (minusinf p)"
  shows "\<exists>x. Ifm vs (x#bs) p"
proof -
  from bound0_I [OF minusinf_nb[OF lp], where bs ="bs"] ex
  have th: "\<forall>x. Ifm vs (x#bs) (minusinf p)"
    by auto
  from minusinf_inf[OF lp, where bs="bs"]
  obtain z where z: "\<forall>x<z. Ifm vs (x # bs) (minusinf p) = Ifm vs (x # bs) p"
    by blast
  from th have "Ifm vs ((z - 1)#bs) (minusinf p)"
    by simp
  moreover have "z - 1 < z"
    by simp
  ultimately show ?thesis
    using z by auto
qed

lemma plusinf_ex:
  assumes lp: "islin p"
    and ex: "Ifm vs (x#bs) (plusinf p)"
  shows "\<exists>x. Ifm vs (x#bs) p"
proof -
  from bound0_I [OF plusinf_nb[OF lp], where bs ="bs"] ex
  have th: "\<forall>x. Ifm vs (x#bs) (plusinf p)"
    by auto
  from plusinf_inf[OF lp, where bs="bs"]
  obtain z where z: "\<forall>x>z. Ifm vs (x # bs) (plusinf p) = Ifm vs (x # bs) p"
    by blast
  from th have "Ifm vs ((z + 1)#bs) (plusinf p)"
    by simp
  moreover have "z + 1 > z"
    by simp
  ultimately show ?thesis
    using z by auto
qed

fun uset :: "fm \<Rightarrow> (poly \<times> tm) list"
  where
    "uset (And p q) = uset p @ uset q"
  | "uset (Or p q) = uset p @ uset q"
  | "uset (Eq (CNP 0 a e)) = [(a, e)]"
  | "uset (Le (CNP 0 a e)) = [(a, e)]"
  | "uset (Lt (CNP 0 a e)) = [(a, e)]"
  | "uset (NEq (CNP 0 a e)) = [(a, e)]"
  | "uset p = []"

lemma uset_l:
  assumes lp: "islin p"
  shows "\<forall>(c,s) \<in> set (uset p). isnpoly c \<and> c \<noteq> 0\<^sub>p \<and> tmbound0 s \<and> allpolys isnpoly s"
  using lp by (induct p rule: uset.induct) auto

lemma minusinf_uset0:
  assumes lp: "islin p"
    and nmi: "\<not> (Ifm vs (x#bs) (minusinf p))"
    and ex: "Ifm vs (x#bs) p" (is "?I x p")
  shows "\<exists>(c, s) \<in> set (uset p). x \<ge> - Itm vs (x#bs) s / Ipoly vs c"
proof -
  have "\<exists>(c, s) \<in> set (uset p).
      Ipoly vs c < 0 \<and> Ipoly vs c * x \<le> - Itm vs (x#bs) s \<or>
      Ipoly vs c > 0 \<and> Ipoly vs c * x \<ge> - Itm vs (x#bs) s"
    using lp nmi ex
    apply (induct p rule: minusinf.induct)
                        apply (auto simp add: eq le lt polyneg_norm)
      apply (auto simp add: linorder_not_less order_le_less)
    done
  then obtain c s where csU: "(c, s) \<in> set (uset p)"
    and x: "(Ipoly vs c < 0 \<and> Ipoly vs c * x \<le> - Itm vs (x#bs) s) \<or>
      (Ipoly vs c > 0 \<and> Ipoly vs c * x \<ge> - Itm vs (x#bs) s)" by blast
  then have "x \<ge> (- Itm vs (x#bs) s) / Ipoly vs c"
    using divide_le_eq[of "- Itm vs (x#bs) s" "Ipoly vs c" x]
    by (auto simp add: mult.commute)
  then show ?thesis
    using csU by auto
qed

lemma minusinf_uset:
  assumes lp: "islin p"
    and nmi: "\<not> (Ifm vs (a#bs) (minusinf p))"
    and ex: "Ifm vs (x#bs) p" (is "?I x p")
  shows "\<exists>(c,s) \<in> set (uset p). x \<ge> - Itm vs (a#bs) s / Ipoly vs c"
proof -
  from nmi have nmi': "\<not> Ifm vs (x#bs) (minusinf p)"
    by (simp add: bound0_I[OF minusinf_nb[OF lp], where b=x and b'=a])
  from minusinf_uset0[OF lp nmi' ex]
  obtain c s where csU: "(c,s) \<in> set (uset p)"
    and th: "x \<ge> - Itm vs (x#bs) s / Ipoly vs c"
    by blast
  from uset_l[OF lp, rule_format, OF csU] have nb: "tmbound0 s"
    by simp
  from th tmbound0_I[OF nb, of vs x bs a] csU show ?thesis
    by auto
qed


lemma plusinf_uset0:
  assumes lp: "islin p"
    and nmi: "\<not> (Ifm vs (x#bs) (plusinf p))"
    and ex: "Ifm vs (x#bs) p" (is "?I x p")
  shows "\<exists>(c, s) \<in> set (uset p). x \<le> - Itm vs (x#bs) s / Ipoly vs c"
proof -
  have "\<exists>(c, s) \<in> set (uset p).
      Ipoly vs c < 0 \<and> Ipoly vs c * x \<ge> - Itm vs (x#bs) s \<or>
      Ipoly vs c > 0 \<and> Ipoly vs c * x \<le> - Itm vs (x#bs) s"
    using lp nmi ex
    apply (induct p rule: minusinf.induct)
                        apply (auto simp add: eq le lt polyneg_norm)
      apply (auto simp add: linorder_not_less order_le_less)
    done
  then obtain c s
    where c_s: "(c, s) \<in> set (uset p)"
      and "Ipoly vs c < 0 \<and> Ipoly vs c * x \<ge> - Itm vs (x#bs) s \<or>
        Ipoly vs c > 0 \<and> Ipoly vs c * x \<le> - Itm vs (x#bs) s"
    by blast
  then have "x \<le> (- Itm vs (x#bs) s) / Ipoly vs c"
    using le_divide_eq[of x "- Itm vs (x#bs) s" "Ipoly vs c"]
    by (auto simp add: mult.commute)
  then show ?thesis
    using c_s by auto
qed

lemma plusinf_uset:
  assumes lp: "islin p"
    and nmi: "\<not> (Ifm vs (a#bs) (plusinf p))"
    and ex: "Ifm vs (x#bs) p" (is "?I x p")
  shows "\<exists>(c,s) \<in> set (uset p). x \<le> - Itm vs (a#bs) s / Ipoly vs c"
proof -
  from nmi have nmi': "\<not> (Ifm vs (x#bs) (plusinf p))"
    by (simp add: bound0_I[OF plusinf_nb[OF lp], where b=x and b'=a])
  from plusinf_uset0[OF lp nmi' ex]
  obtain c s
    where c_s: "(c,s) \<in> set (uset p)"
      and x: "x \<le> - Itm vs (x#bs) s / Ipoly vs c"
    by blast
  from uset_l[OF lp, rule_format, OF c_s] have nb: "tmbound0 s"
    by simp
  from x tmbound0_I[OF nb, of vs x bs a] c_s show ?thesis
    by auto
qed

lemma lin_dense:
  assumes lp: "islin p"
    and noS: "\<forall>t. l < t \<and> t< u \<longrightarrow> t \<notin> (\<lambda>(c,t). - Itm vs (x#bs) t / Ipoly vs c) ` set (uset p)"
      (is "\<forall>t. _ \<and> _ \<longrightarrow> t \<notin> (\<lambda>(c,t). - ?Nt x t / ?N c) ` ?U p")
    and lx: "l < x" and xu: "x < u"
    and px: "Ifm vs (x # bs) p"
    and ly: "l < y" and yu: "y < u"
  shows "Ifm vs (y#bs) p"
  using lp px noS
proof (induct p rule: islin.induct)
  case (5 c s)
  from "5.prems"
  have lin: "isnpoly c" "c \<noteq> 0\<^sub>p" "tmbound0 s" "allpolys isnpoly s"
    and px: "Ifm vs (x # bs) (Lt (CNP 0 c s))"
    and noS: "\<forall>t. l < t \<and> t < u \<longrightarrow> t \<noteq> - Itm vs (x # bs) s / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>"
    by simp_all
  from ly yu noS have yne: "y \<noteq> - ?Nt x s / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>"
    by simp
  then have ycs: "y < - ?Nt x s / ?N c \<or> y > -?Nt x s / ?N c"
    by auto
  consider "?N c = 0" | "?N c > 0" | "?N c < 0" by arith
  then show ?case
  proof cases
    case 1
    then show ?thesis
      using px by (simp add: tmbound0_I[OF lin(3), where bs="bs" and b="x" and b'="y"])
  next
    case N: 2
    from px pos_less_divide_eq[OF N, where a="x" and b="-?Nt x s"]
    have px': "x < - ?Nt x s / ?N c"
      by (auto simp add: not_less field_simps)
    from ycs show ?thesis
    proof
      assume y: "y < - ?Nt x s / ?N c"
      then have "y * ?N c < - ?Nt x s"
        by (simp add: pos_less_divide_eq[OF N, where a="y" and b="-?Nt x s", symmetric])
      then have "?N c * y + ?Nt x s < 0"
        by (simp add: field_simps)
      then show ?thesis using tmbound0_I[OF lin(3), where bs="bs" and b="x" and b'="y"]
        by simp
    next
      assume y: "y > -?Nt x s / ?N c"
      with yu have eu: "u > - ?Nt x s / ?N c"
        by auto
      with noS ly yu have th: "- ?Nt x s / ?N c \<le> l"
        by (cases "- ?Nt x s / ?N c > l") auto
      with lx px' have False
        by simp
      then show ?thesis ..
    qed
  next
    case N: 3
    from px neg_divide_less_eq[OF N, where a="x" and b="-?Nt x s"]
    have px': "x > - ?Nt x s / ?N c"
      by (auto simp add: not_less field_simps)
    from ycs show ?thesis
    proof
      assume y: "y > - ?Nt x s / ?N c"
      then have "y * ?N c < - ?Nt x s"
        by (simp add: neg_divide_less_eq[OF N, where a="y" and b="-?Nt x s", symmetric])
      then have "?N c * y + ?Nt x s < 0"
        by (simp add: field_simps)
      then show ?thesis using tmbound0_I[OF lin(3), where bs="bs" and b="x" and b'="y"]
        by simp
    next
      assume y: "y < -?Nt x s / ?N c"
      with ly have eu: "l < - ?Nt x s / ?N c"
        by auto
      with noS ly yu have th: "- ?Nt x s / ?N c \<ge> u"
        by (cases "- ?Nt x s / ?N c < u") auto
      with xu px' have False
        by simp
      then show ?thesis ..
    qed
  qed
next
  case (6 c s)
  from "6.prems"
  have lin: "isnpoly c" "c \<noteq> 0\<^sub>p" "tmbound0 s" "allpolys isnpoly s"
    and px: "Ifm vs (x # bs) (Le (CNP 0 c s))"
    and noS: "\<forall>t. l < t \<and> t < u \<longrightarrow> t \<noteq> - Itm vs (x # bs) s / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>"
    by simp_all
  from ly yu noS have yne: "y \<noteq> - ?Nt x s / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>"
    by simp
  then have ycs: "y < - ?Nt x s / ?N c \<or> y > -?Nt x s / ?N c"
    by auto
  have ccs: "?N c = 0 \<or> ?N c < 0 \<or> ?N c > 0" by dlo
  consider "?N c = 0" | "?N c > 0" | "?N c < 0" by arith
  then show ?case
  proof cases
    case 1
    then show ?thesis
      using px by (simp add: tmbound0_I[OF lin(3), where bs="bs" and b="x" and b'="y"])
  next
    case N: 2
    from px pos_le_divide_eq[OF N, where a="x" and b="-?Nt x s"]
    have px': "x \<le> - ?Nt x s / ?N c"
      by (simp add: not_less field_simps)
    from ycs show ?thesis
    proof
      assume y: "y < - ?Nt x s / ?N c"
      then have "y * ?N c < - ?Nt x s"
        by (simp add: pos_less_divide_eq[OF N, where a="y" and b="-?Nt x s", symmetric])
      then have "?N c * y + ?Nt x s < 0"
        by (simp add: field_simps)
      then show ?thesis
        using tmbound0_I[OF lin(3), where bs="bs" and b="x" and b'="y"] by simp
    next
      assume y: "y > -?Nt x s / ?N c"
      with yu have eu: "u > - ?Nt x s / ?N c"
        by auto
      with noS ly yu have th: "- ?Nt x s / ?N c \<le> l"
        by (cases "- ?Nt x s / ?N c > l") auto
      with lx px' have False
        by simp
      then show ?thesis ..
    qed
  next
    case N: 3
    from px neg_divide_le_eq[OF N, where a="x" and b="-?Nt x s"]
    have px': "x \<ge> - ?Nt x s / ?N c"
      by (simp add: field_simps)
    from ycs show ?thesis
    proof
      assume y: "y > - ?Nt x s / ?N c"
      then have "y * ?N c < - ?Nt x s"
        by (simp add: neg_divide_less_eq[OF N, where a="y" and b="-?Nt x s", symmetric])
      then have "?N c * y + ?Nt x s < 0"
        by (simp add: field_simps)
      then show ?thesis
        using tmbound0_I[OF lin(3), where bs="bs" and b="x" and b'="y"] by simp
    next
      assume y: "y < -?Nt x s / ?N c"
      with ly have eu: "l < - ?Nt x s / ?N c"
        by auto
      with noS ly yu have th: "- ?Nt x s / ?N c \<ge> u"
        by (cases "- ?Nt x s / ?N c < u") auto
      with xu px' have False by simp
      then show ?thesis ..
    qed
  qed
next
  case (3 c s)
  from "3.prems"
  have lin: "isnpoly c" "c \<noteq> 0\<^sub>p" "tmbound0 s" "allpolys isnpoly s"
    and px: "Ifm vs (x # bs) (Eq (CNP 0 c s))"
    and noS: "\<forall>t. l < t \<and> t < u \<longrightarrow> t \<noteq> - Itm vs (x # bs) s / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>"
    by simp_all
  from ly yu noS have yne: "y \<noteq> - ?Nt x s / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>"
    by simp
  then have ycs: "y < - ?Nt x s / ?N c \<or> y > -?Nt x s / ?N c"
    by auto
  consider "?N c = 0" | "?N c < 0" | "?N c > 0" by arith
  then show ?case
  proof cases
    case 1
    then show ?thesis
      using px by (simp add: tmbound0_I[OF lin(3), where bs="bs" and b="x" and b'="y"])
  next
    case 2
    then have cnz: "?N c \<noteq> 0"
      by simp
    from px eq_divide_eq[of "x" "-?Nt x s" "?N c"] cnz
    have px': "x = - ?Nt x s / ?N c"
      by (simp add: field_simps)
    from ycs show ?thesis
    proof
      assume y: "y < -?Nt x s / ?N c"
      with ly have eu: "l < - ?Nt x s / ?N c"
        by auto
      with noS ly yu have th: "- ?Nt x s / ?N c \<ge> u"
        by (cases "- ?Nt x s / ?N c < u") auto
      with xu px' have False by simp
      then show ?thesis ..
    next
      assume y: "y > -?Nt x s / ?N c"
      with yu have eu: "u > - ?Nt x s / ?N c"
        by auto
      with noS ly yu have th: "- ?Nt x s / ?N c \<le> l"
        by (cases "- ?Nt x s / ?N c > l") auto
      with lx px' have False by simp
      then show ?thesis ..
    qed
  next
    case 3
    then have cnz: "?N c \<noteq> 0"
      by simp
    from px eq_divide_eq[of "x" "-?Nt x s" "?N c"] cnz
    have px': "x = - ?Nt x s / ?N c"
      by (simp add: field_simps)
    from ycs show ?thesis
    proof
      assume y: "y < -?Nt x s / ?N c"
      with ly have eu: "l < - ?Nt x s / ?N c"
        by auto
      with noS ly yu have th: "- ?Nt x s / ?N c \<ge> u"
        by (cases "- ?Nt x s / ?N c < u") auto
      with xu px' have False by simp
      then show ?thesis ..
    next
      assume y: "y > -?Nt x s / ?N c"
      with yu have eu: "u > - ?Nt x s / ?N c"
        by auto
      with noS ly yu have th: "- ?Nt x s / ?N c \<le> l"
        by (cases "- ?Nt x s / ?N c > l") auto
      with lx px' have False by simp
      then show ?thesis ..
    qed
  qed
next
  case (4 c s)
  from "4.prems"
  have lin: "isnpoly c" "c \<noteq> 0\<^sub>p" "tmbound0 s" "allpolys isnpoly s"
    and px: "Ifm vs (x # bs) (NEq (CNP 0 c s))"
    and noS: "\<forall>t. l < t \<and> t < u \<longrightarrow> t \<noteq> - Itm vs (x # bs) s / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>"
    by simp_all
  from ly yu noS have yne: "y \<noteq> - ?Nt x s / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>"
    by simp
  then have ycs: "y < - ?Nt x s / ?N c \<or> y > -?Nt x s / ?N c"
    by auto
  show ?case
  proof (cases "?N c = 0")
    case True
    then show ?thesis
      using px by (simp add: tmbound0_I[OF lin(3), where bs="bs" and b="x" and b'="y"])
  next
    case False
    with yne eq_divide_eq[of "y" "- ?Nt x s" "?N c"]
    show ?thesis
      by (simp add: field_simps tmbound0_I[OF lin(3), of vs x bs y] sum_eq[symmetric])
  qed
qed (auto simp add: tmbound0_I[where vs=vs and bs="bs" and b="y" and b'="x"]
  bound0_I[where vs=vs and bs="bs" and b="y" and b'="x"])

lemma inf_uset:
  assumes lp: "islin p"
    and nmi: "\<not> (Ifm vs (x#bs) (minusinf p))" (is "\<not> (Ifm vs (x#bs) (?M p))")
    and npi: "\<not> (Ifm vs (x#bs) (plusinf p))" (is "\<not> (Ifm vs (x#bs) (?P p))")
    and ex: "\<exists>x.  Ifm vs (x#bs) p" (is "\<exists>x. ?I x p")
  shows "\<exists>(c, t) \<in> set (uset p). \<exists>(d, s) \<in> set (uset p).
    ?I ((- Itm vs (x#bs) t / Ipoly vs c + - Itm vs (x#bs) s / Ipoly vs d) / 2) p"
proof -
  let ?Nt = "\<lambda>x t. Itm vs (x#bs) t"
  let ?N = "Ipoly vs"
  let ?U = "set (uset p)"
  from ex obtain a where pa: "?I a p"
    by blast
  from bound0_I[OF minusinf_nb[OF lp], where bs="bs" and b="x" and b'="a"] nmi
  have nmi': "\<not> (?I a (?M p))"
    by simp
  from bound0_I[OF plusinf_nb[OF lp], where bs="bs" and b="x" and b'="a"] npi
  have npi': "\<not> (?I a (?P p))"
    by simp
  have "\<exists>(c,t) \<in> set (uset p). \<exists>(d,s) \<in> set (uset p). ?I ((- ?Nt a t/?N c + - ?Nt a s /?N d) / 2) p"
  proof -
    let ?M = "(\<lambda>(c,t). - ?Nt a t / ?N c) ` ?U"
    have fM: "finite ?M"
      by auto
    from minusinf_uset[OF lp nmi pa] plusinf_uset[OF lp npi pa]
    have "\<exists>(c, t) \<in> set (uset p). \<exists>(d, s) \<in> set (uset p).
        a \<le> - ?Nt x t / ?N c \<and> a \<ge> - ?Nt x s / ?N d"
      by blast
    then obtain c t d s
      where ctU: "(c, t) \<in> ?U"
        and dsU: "(d, s) \<in> ?U"
        and xs1: "a \<le> - ?Nt x s / ?N d"
        and tx1: "a \<ge> - ?Nt x t / ?N c"
      by blast
    from uset_l[OF lp] ctU dsU tmbound0_I[where bs="bs" and b="x" and b'="a"] xs1 tx1
    have xs: "a \<le> - ?Nt a s / ?N d" and tx: "a \<ge> - ?Nt a t / ?N c"
      by auto
    from ctU have Mne: "?M \<noteq> {}" by auto
    then have Une: "?U \<noteq> {}" by simp
    let ?l = "Min ?M"
    let ?u = "Max ?M"
    have linM: "?l \<in> ?M"
      using fM Mne by simp
    have uinM: "?u \<in> ?M"
      using fM Mne by simp
    have ctM: "- ?Nt a t / ?N c \<in> ?M"
      using ctU by auto
    have dsM: "- ?Nt a s / ?N d \<in> ?M"
      using dsU by auto
    have lM: "\<forall>t\<in> ?M. ?l \<le> t"
      using Mne fM by auto
    have Mu: "\<forall>t\<in> ?M. t \<le> ?u"
      using Mne fM by auto
    have "?l \<le> - ?Nt a t / ?N c"
      using ctM Mne by simp
    then have lx: "?l \<le> a"
      using tx by simp
    have "- ?Nt a s / ?N d \<le> ?u"
      using dsM Mne by simp
    then have xu: "a \<le> ?u"
      using xs by simp
    from finite_set_intervals2[where P="\<lambda>x. ?I x p",OF pa lx xu linM uinM fM lM Mu]
    consider u where "u \<in> ?M" "?I u p"
      | t1 t2 where "t1 \<in> ?M" "t2\<in> ?M" "\<forall>y. t1 < y \<and> y < t2 \<longrightarrow> y \<notin> ?M" "t1 < a" "a < t2" "?I a p"
      by blast
    then show ?thesis
    proof cases
      case 1
      then have "\<exists>(nu,tu) \<in> ?U. u = - ?Nt a tu / ?N nu"
        by auto
      then obtain tu nu where tuU: "(nu, tu) \<in> ?U" and tuu: "u = - ?Nt a tu / ?N nu"
        by blast
      have "?I (((- ?Nt a tu / ?N nu) + (- ?Nt a tu / ?N nu)) / 2) p"
        using \<open>?I u p\<close> tuu by simp
      with tuU show ?thesis by blast
    next
      case 2
      have "\<exists>(t1n, t1u) \<in> ?U. t1 = - ?Nt a t1u / ?N t1n"
        using \<open>t1 \<in> ?M\<close> by auto
      then obtain t1u t1n where t1uU: "(t1n, t1u) \<in> ?U"
        and t1u: "t1 = - ?Nt a t1u / ?N t1n"
        by blast
      have "\<exists>(t2n, t2u) \<in> ?U. t2 = - ?Nt a t2u / ?N t2n"
        using \<open>t2 \<in> ?M\<close> by auto
      then obtain t2u t2n where t2uU: "(t2n, t2u) \<in> ?U"
        and t2u: "t2 = - ?Nt a t2u / ?N t2n"
        by blast
      have "t1 < t2"
        using \<open>t1 < a\<close> \<open>a < t2\<close> by simp
      let ?u = "(t1 + t2) / 2"
      have "t1 < ?u"
        using less_half_sum [OF \<open>t1 < t2\<close>] by auto
      have "?u < t2"
        using gt_half_sum [OF \<open>t1 < t2\<close>] by auto
      have "?I ?u p"
        using lp \<open>\<forall>y. t1 < y \<and> y < t2 \<longrightarrow> y \<notin> ?M\<close> \<open>t1 < a\<close> \<open>a < t2\<close> \<open>?I a p\<close> \<open>t1 < ?u\<close> \<open>?u < t2\<close>
        by (rule lin_dense)
      with t1uU t2uU t1u t2u show ?thesis by blast
    qed
  qed
  then obtain l n s  m
    where lnU: "(n, l) \<in> ?U"
      and smU:"(m,s) \<in> ?U"
      and pu: "?I ((- ?Nt a l / ?N n + - ?Nt a s / ?N m) / 2) p"
    by blast
  from lnU smU uset_l[OF lp] have nbl: "tmbound0 l" and nbs: "tmbound0 s"
    by auto
  from tmbound0_I[OF nbl, where bs="bs" and b="a" and b'="x"]
    tmbound0_I[OF nbs, where bs="bs" and b="a" and b'="x"] pu
  have "?I ((- ?Nt x l / ?N n + - ?Nt x s / ?N m) / 2) p"
    by simp
  with lnU smU show ?thesis by auto
qed


section \<open>The Ferrante - Rackoff Theorem\<close>

theorem fr_eq:
  assumes lp: "islin p"
  shows "(\<exists>x. Ifm vs (x#bs) p) \<longleftrightarrow>
    (Ifm vs (x#bs) (minusinf p) \<or>
     Ifm vs (x#bs) (plusinf p) \<or>
     (\<exists>(n, t) \<in> set (uset p). \<exists>(m, s) \<in> set (uset p).
       Ifm vs (((- Itm vs (x#bs) t /  Ipoly vs n + - Itm vs (x#bs) s / Ipoly vs m) / 2)#bs) p))"
  (is "(\<exists>x. ?I x p) \<longleftrightarrow> ?M \<or> ?P \<or> ?F" is "?E \<longleftrightarrow> ?D")
proof
  show ?D if ?E
  proof -
    consider "?M \<or> ?P" | "\<not> ?M" "\<not> ?P" by blast
    then show ?thesis
    proof cases
      case 1
      then show ?thesis by blast
    next
      case 2
      from inf_uset[OF lp this] have ?F
        using \<open>?E\<close> by blast
      then show ?thesis by blast
    qed
  qed
  show ?E if ?D
  proof -
    from that consider ?M | ?P | ?F by blast
    then show ?thesis
    proof cases
      case 1
      from minusinf_ex[OF lp this] show ?thesis .
    next
      case 2
      from plusinf_ex[OF lp this] show ?thesis .
    next
      case 3
      then show ?thesis by blast
    qed
  qed
qed


section \<open>First implementation : Naive by encoding all case splits locally\<close>

definition "msubsteq c t d s a r =
  evaldjf (case_prod conj)
  [(let cd = c *\<^sub>p d
    in (NEq (CP cd), Eq (Add (Mul (~\<^sub>p a) (Add (Mul d t) (Mul c s))) (Mul ((2)\<^sub>p *\<^sub>p cd) r)))),
   (conj (Eq (CP c)) (NEq (CP d)), Eq (Add (Mul (~\<^sub>p a) s) (Mul ((2)\<^sub>p *\<^sub>p d) r))),
   (conj (NEq (CP c)) (Eq (CP d)), Eq (Add (Mul (~\<^sub>p a) t) (Mul ((2)\<^sub>p *\<^sub>p c) r))),
   (conj (Eq (CP c)) (Eq (CP d)), Eq r)]"

lemma msubsteq_nb:
  assumes lp: "islin (Eq (CNP 0 a r))"
    and t: "tmbound0 t"
    and s: "tmbound0 s"
  shows "bound0 (msubsteq c t d s a r)"
proof -
  have th: "\<forall>x \<in> set
    [(let cd = c *\<^sub>p d
      in (NEq (CP cd), Eq (Add (Mul (~\<^sub>p a) (Add (Mul d t) (Mul c s))) (Mul ((2)\<^sub>p *\<^sub>p cd) r)))),
     (conj (Eq (CP c)) (NEq (CP d)), Eq (Add (Mul (~\<^sub>p a) s) (Mul ((2)\<^sub>p *\<^sub>p d) r))),
     (conj (NEq (CP c)) (Eq (CP d)), Eq (Add (Mul (~\<^sub>p a) t) (Mul ((2)\<^sub>p *\<^sub>p c) r))),
     (conj (Eq (CP c)) (Eq (CP d)), Eq r)]. bound0 (case_prod conj x)"
    using lp by (simp add: Let_def t s)
  from evaldjf_bound0[OF th] show ?thesis
    by (simp add: msubsteq_def)
qed

lemma msubsteq:
  assumes lp: "islin (Eq (CNP 0 a r))"
  shows "Ifm vs (x#bs) (msubsteq c t d s a r) =
    Ifm vs (((- Itm vs (x#bs) t /  Ipoly vs c + - Itm vs (x#bs) s / Ipoly vs d) / 2)#bs) (Eq (CNP 0 a r))"
  (is "?lhs = ?rhs")
proof -
  let ?Nt = "\<lambda>x t. Itm vs (x#bs) t"
  let ?N = "\<lambda>p. Ipoly vs p"
  let ?c = "?N c"
  let ?d = "?N d"
  let ?t = "?Nt x t"
  let ?s = "?Nt x s"
  let ?a = "?N a"
  let ?r = "?Nt x r"
  from lp have lin:"isnpoly a" "a \<noteq> 0\<^sub>p" "tmbound0 r" "allpolys isnpoly r"
    by simp_all
  note r = tmbound0_I[OF lin(3), of vs _ bs x]
  consider "?c = 0" "?d = 0" | "?c = 0" "?d \<noteq> 0" | "?c \<noteq> 0" "?d = 0" | "?c \<noteq> 0" "?d \<noteq> 0"
    by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by (simp add: r[of 0] msubsteq_def Let_def evaldjf_ex)
  next
    case cd: 2
    then have th: "(- ?t / ?c + - ?s / ?d)/2 = -?s / (2*?d)"
      by simp
    have "?rhs = Ifm vs (-?s / (2*?d) # bs) (Eq (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a * (-?s / (2*?d)) + ?r = 0"
      by (simp add: r[of "- (Itm vs (x # bs) s / (2 * \<lparr>d\<rparr>\<^sub>p\<^bsup>vs\<^esup>))"])
    also have "\<dots> \<longleftrightarrow> 2 * ?d * (?a * (-?s / (2*?d)) + ?r) = 0"
      using cd(2) mult_cancel_left[of "2*?d" "(?a * (-?s / (2*?d)) + ?r)" 0] by simp
    also have "\<dots> \<longleftrightarrow> (- ?a * ?s) * (2*?d / (2*?d)) + 2 * ?d * ?r= 0"
      by (simp add: field_simps distrib_left [of "2*?d"])
    also have "\<dots> \<longleftrightarrow> - (?a * ?s) + 2*?d*?r = 0"
      using cd(2) by simp
    finally show ?thesis
      using cd
      by (simp add: r[of "- (Itm vs (x # bs) s / (2 * \<lparr>d\<rparr>\<^sub>p\<^bsup>vs\<^esup>))"] msubsteq_def Let_def evaldjf_ex)
  next
    case cd: 3
    from cd(2) have th: "(- ?t / ?c + - ?s / ?d)/2 = -?t / (2 * ?c)"
      by simp
    have "?rhs = Ifm vs (-?t / (2*?c) # bs) (Eq (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a * (-?t / (2*?c)) + ?r = 0"
      by (simp add: r[of "- (?t/ (2 * ?c))"])
    also have "\<dots> \<longleftrightarrow> 2 * ?c * (?a * (-?t / (2 * ?c)) + ?r) = 0"
      using cd(1) mult_cancel_left[of "2 * ?c" "(?a * (-?t / (2 * ?c)) + ?r)" 0] by simp
    also have "\<dots> \<longleftrightarrow> (?a * -?t)* (2 * ?c) / (2 * ?c) + 2 * ?c * ?r= 0"
      by (simp add: field_simps distrib_left [of "2 * ?c"])
    also have "\<dots> \<longleftrightarrow> - (?a * ?t) + 2 * ?c * ?r = 0"
      using cd(1) by simp
    finally show ?thesis using cd
      by (simp add: r[of "- (?t/ (2 * ?c))"] msubsteq_def Let_def evaldjf_ex)
  next
    case cd: 4
    then have cd2: "?c * ?d * 2 \<noteq> 0"
      by simp
    from add_frac_eq[OF cd, of "- ?t" "- ?s"]
    have th: "(- ?t / ?c + - ?s / ?d)/2 = - (?d * ?t + ?c* ?s )/ (2 * ?c * ?d)"
      by (simp add: field_simps)
    have "?rhs \<longleftrightarrow> Ifm vs (- (?d * ?t + ?c* ?s )/ (2*?c*?d) # bs) (Eq (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a * (- (?d * ?t + ?c* ?s )/ (2*?c*?d)) + ?r = 0"
      by (simp add: r [of "(- (?d * ?t) - (?c *?s)) / (2 * ?c * ?d)"])
    also have "\<dots> \<longleftrightarrow> (2 * ?c * ?d) * (?a * (- (?d * ?t + ?c* ?s )/ (2*?c*?d)) + ?r) = 0"
      using cd mult_cancel_left[of "2 * ?c * ?d" "?a * (- (?d * ?t + ?c* ?s)/ (2 * ?c * ?d)) + ?r" 0]
      by simp
    also have "\<dots> \<longleftrightarrow> ?a * (- (?d * ?t + ?c* ?s )) + 2 * ?c * ?d * ?r = 0"
      using nonzero_mult_div_cancel_left [OF cd2] cd
      by (simp add: algebra_simps diff_divide_distrib del: distrib_right)
    finally show ?thesis
      using cd
      by (simp add: r[of "(- (?d * ?t) + - (?c *?s)) / (2 * ?c * ?d)"]
          msubsteq_def Let_def evaldjf_ex field_simps)
  qed
qed


definition "msubstneq c t d s a r =
  evaldjf (case_prod conj)
  [(let cd = c *\<^sub>p d
    in (NEq (CP cd), NEq (Add (Mul (~\<^sub>p a) (Add (Mul d t) (Mul c s))) (Mul ((2)\<^sub>p *\<^sub>p cd) r)))),
   (conj (Eq (CP c)) (NEq (CP d)), NEq (Add (Mul (~\<^sub>p a) s) (Mul ((2)\<^sub>p *\<^sub>p d) r))),
   (conj (NEq (CP c)) (Eq (CP d)), NEq (Add (Mul (~\<^sub>p a) t) (Mul ((2)\<^sub>p *\<^sub>p c) r))),
   (conj (Eq (CP c)) (Eq (CP d)), NEq r)]"

lemma msubstneq_nb:
  assumes lp: "islin (NEq (CNP 0 a r))"
    and t: "tmbound0 t"
    and s: "tmbound0 s"
  shows "bound0 (msubstneq c t d s a r)"
proof -
  have th: "\<forall>x\<in> set
   [(let cd = c *\<^sub>p d
     in (NEq (CP cd), NEq (Add (Mul (~\<^sub>p a) (Add (Mul d t) (Mul c s))) (Mul ((2)\<^sub>p *\<^sub>p cd) r)))),
    (conj (Eq (CP c)) (NEq (CP d)), NEq (Add (Mul (~\<^sub>p a) s) (Mul ((2)\<^sub>p *\<^sub>p d) r))),
    (conj (NEq (CP c)) (Eq (CP d)), NEq (Add (Mul (~\<^sub>p a) t) (Mul ((2)\<^sub>p *\<^sub>p c) r))),
    (conj (Eq (CP c)) (Eq (CP d)), NEq r)]. bound0 (case_prod conj x)"
    using lp by (simp add: Let_def t s)
  from evaldjf_bound0[OF th] show ?thesis
    by (simp add: msubstneq_def)
qed

lemma msubstneq:
  assumes lp: "islin (Eq (CNP 0 a r))"
  shows "Ifm vs (x#bs) (msubstneq c t d s a r) =
    Ifm vs (((- Itm vs (x#bs) t /  Ipoly vs c + - Itm vs (x#bs) s / Ipoly vs d) /2)#bs) (NEq (CNP 0 a r))"
  (is "?lhs = ?rhs")
proof -
  let ?Nt = "\<lambda>x t. Itm vs (x#bs) t"
  let ?N = "\<lambda>p. Ipoly vs p"
  let ?c = "?N c"
  let ?d = "?N d"
  let ?t = "?Nt x t"
  let ?s = "?Nt x s"
  let ?a = "?N a"
  let ?r = "?Nt x r"
  from lp have lin:"isnpoly a" "a \<noteq> 0\<^sub>p" "tmbound0 r" "allpolys isnpoly r"
    by simp_all
  note r = tmbound0_I[OF lin(3), of vs _ bs x]
  consider "?c = 0" "?d = 0" | "?c = 0" "?d \<noteq> 0" | "?c \<noteq> 0" "?d = 0" | "?c \<noteq> 0" "?d \<noteq> 0"
    by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      by (simp add: r[of 0] msubstneq_def Let_def evaldjf_ex)
  next
    case cd: 2
    from cd(1) have th: "(- ?t / ?c + - ?s / ?d)/2 = -?s / (2 * ?d)"
      by simp
    have "?rhs = Ifm vs (-?s / (2*?d) # bs) (NEq (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a * (-?s / (2*?d)) + ?r \<noteq> 0"
      by (simp add: r[of "- (Itm vs (x # bs) s / (2 * \<lparr>d\<rparr>\<^sub>p\<^bsup>vs\<^esup>))"])
    also have "\<dots> \<longleftrightarrow> 2*?d * (?a * (-?s / (2*?d)) + ?r) \<noteq> 0"
      using cd(2) mult_cancel_left[of "2*?d" "(?a * (-?s / (2*?d)) + ?r)" 0] by simp
    also have "\<dots> \<longleftrightarrow> (- ?a * ?s) * (2*?d / (2*?d)) + 2*?d*?r\<noteq> 0"
      by (simp add: field_simps distrib_left[of "2*?d"] del: distrib_left)
    also have "\<dots> \<longleftrightarrow> - (?a * ?s) + 2*?d*?r \<noteq> 0"
      using cd(2) by simp
    finally show ?thesis
      using cd
      by (simp add: r[of "- (Itm vs (x # bs) s / (2 * \<lparr>d\<rparr>\<^sub>p\<^bsup>vs\<^esup>))"] msubstneq_def Let_def evaldjf_ex)
  next
    case cd: 3
    from cd(2) have th: "(- ?t / ?c + - ?s / ?d)/2 = -?t / (2*?c)"
      by simp
    have "?rhs = Ifm vs (-?t / (2*?c) # bs) (NEq (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a * (-?t / (2*?c)) + ?r \<noteq> 0"
      by (simp add: r[of "- (?t/ (2 * ?c))"])
    also have "\<dots> \<longleftrightarrow> 2*?c * (?a * (-?t / (2*?c)) + ?r) \<noteq> 0"
      using cd(1) mult_cancel_left[of "2*?c" "(?a * (-?t / (2*?c)) + ?r)" 0] by simp
    also have "\<dots> \<longleftrightarrow> (?a * -?t)* (2*?c) / (2*?c) + 2*?c*?r \<noteq> 0"
      by (simp add: field_simps distrib_left[of "2*?c"] del: distrib_left)
    also have "\<dots> \<longleftrightarrow> - (?a * ?t) + 2*?c*?r \<noteq> 0"
      using cd(1) by simp
    finally show ?thesis
      using cd by (simp add: r[of "- (?t/ (2*?c))"] msubstneq_def Let_def evaldjf_ex)
  next
    case cd: 4
    then have cd2: "?c * ?d * 2 \<noteq> 0"
      by simp
    from add_frac_eq[OF cd, of "- ?t" "- ?s"]
    have th: "(- ?t / ?c + - ?s / ?d)/2 = - (?d * ?t + ?c * ?s )/ (2 * ?c * ?d)"
      by (simp add: field_simps)
    have "?rhs \<longleftrightarrow> Ifm vs (- (?d * ?t + ?c* ?s )/ (2*?c*?d) # bs) (NEq (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a * (- (?d * ?t + ?c* ?s )/ (2*?c*?d)) + ?r \<noteq> 0"
      by (simp add: r [of "(- (?d * ?t) - (?c *?s)) / (2 * ?c * ?d)"])
    also have "\<dots> \<longleftrightarrow> (2 * ?c * ?d) * (?a * (- (?d * ?t + ?c* ?s )/ (2*?c*?d)) + ?r) \<noteq> 0"
      using cd mult_cancel_left[of "2 * ?c * ?d" "?a * (- (?d * ?t + ?c* ?s)/ (2*?c*?d)) + ?r" 0]
      by simp
    also have "\<dots> \<longleftrightarrow> ?a * (- (?d * ?t + ?c* ?s )) + 2*?c*?d*?r \<noteq> 0"
      using nonzero_mult_div_cancel_left[OF cd2] cd
      by (simp add: algebra_simps diff_divide_distrib del: distrib_right)
    finally show ?thesis
      using cd
      by (simp add: r[of "(- (?d * ?t) + - (?c *?s)) / (2 * ?c * ?d)"]
          msubstneq_def Let_def evaldjf_ex field_simps)
  qed
qed

definition "msubstlt c t d s a r =
  evaldjf (case_prod conj)
  [(let cd = c *\<^sub>p d
    in (lt (CP (~\<^sub>p cd)), Lt (Add (Mul (~\<^sub>p a) (Add (Mul d t) (Mul c s))) (Mul ((2)\<^sub>p *\<^sub>p cd) r)))),
   (let cd = c *\<^sub>p d
    in (lt (CP cd), Lt (Sub (Mul a (Add (Mul d t) (Mul c s))) (Mul ((2)\<^sub>p *\<^sub>p cd) r)))),
   (conj (lt (CP (~\<^sub>p c))) (Eq (CP d)), Lt (Add (Mul (~\<^sub>p a) t) (Mul ((2)\<^sub>p *\<^sub>p c) r))),
   (conj (lt (CP c)) (Eq (CP d)), Lt (Sub (Mul a t) (Mul ((2)\<^sub>p *\<^sub>p c) r))),
   (conj (lt (CP (~\<^sub>p d))) (Eq (CP c)), Lt (Add (Mul (~\<^sub>p a) s) (Mul ((2)\<^sub>p *\<^sub>p d) r))),
   (conj (lt (CP d)) (Eq (CP c)), Lt (Sub (Mul a s) (Mul ((2)\<^sub>p *\<^sub>p d) r))),
   (conj (Eq (CP c)) (Eq (CP d)), Lt r)]"

lemma msubstlt_nb:
  assumes lp: "islin (Lt (CNP 0 a r))"
    and t: "tmbound0 t"
    and s: "tmbound0 s"
  shows "bound0 (msubstlt c t d s a r)"
proof -
  have th: "\<forall>x\<in> set
  [(let cd = c *\<^sub>p d
    in (lt (CP (~\<^sub>p cd)), Lt (Add (Mul (~\<^sub>p a) (Add (Mul d t) (Mul c s))) (Mul ((2)\<^sub>p *\<^sub>p cd) r)))),
   (let cd = c *\<^sub>p d
    in (lt (CP cd), Lt (Sub (Mul a (Add (Mul d t) (Mul c s))) (Mul ((2)\<^sub>p *\<^sub>p cd) r)))),
   (conj (lt (CP (~\<^sub>p c))) (Eq (CP d)), Lt (Add (Mul (~\<^sub>p a) t) (Mul ((2)\<^sub>p *\<^sub>p c) r))),
   (conj (lt (CP c)) (Eq (CP d)), Lt (Sub (Mul a t) (Mul ((2)\<^sub>p *\<^sub>p c) r))),
   (conj (lt (CP (~\<^sub>p d))) (Eq (CP c)), Lt (Add (Mul (~\<^sub>p a) s) (Mul ((2)\<^sub>p *\<^sub>p d) r))),
   (conj (lt (CP d)) (Eq (CP c)), Lt (Sub (Mul a s) (Mul ((2)\<^sub>p *\<^sub>p d) r))),
   (conj (Eq (CP c)) (Eq (CP d)), Lt r)]. bound0 (case_prod conj x)"
    using lp by (simp add: Let_def t s lt_nb)
  from evaldjf_bound0[OF th] show ?thesis
    by (simp add: msubstlt_def)
qed

lemma msubstlt:
  assumes nc: "isnpoly c"
    and nd: "isnpoly d"
    and lp: "islin (Lt (CNP 0 a r))"
  shows "Ifm vs (x#bs) (msubstlt c t d s a r) \<longleftrightarrow>
    Ifm vs (((- Itm vs (x#bs) t /  Ipoly vs c + - Itm vs (x#bs) s / Ipoly vs d) /2)#bs) (Lt (CNP 0 a r))"
  (is "?lhs = ?rhs")
proof -
  let ?Nt = "\<lambda>x t. Itm vs (x#bs) t"
  let ?N = "\<lambda>p. Ipoly vs p"
  let ?c = "?N c"
  let ?d = "?N d"
  let ?t = "?Nt x t"
  let ?s = "?Nt x s"
  let ?a = "?N a"
  let ?r = "?Nt x r"
  from lp have lin:"isnpoly a" "a \<noteq> 0\<^sub>p" "tmbound0 r" "allpolys isnpoly r"
    by simp_all
  note r = tmbound0_I[OF lin(3), of vs _ bs x]
  consider "?c = 0" "?d = 0" | "?c * ?d > 0" | "?c * ?d < 0"
    | "?c > 0" "?d = 0" | "?c < 0" "?d = 0" | "?c = 0" "?d > 0" | "?c = 0" "?d < 0"
    by atomize_elim auto
  then show ?thesis
  proof cases
    case 1
    then show ?thesis
      using nc nd by (simp add: polyneg_norm lt r[of 0] msubstlt_def Let_def evaldjf_ex)
  next
    case cd: 2
    then have cd2: "2 * ?c * ?d > 0"
      by simp
    from cd have c: "?c \<noteq> 0" and d: "?d \<noteq> 0"
      by auto
    from cd2 have cd2': "\<not> 2 * ?c * ?d < 0" by simp
    from add_frac_eq[OF c d, of "- ?t" "- ?s"]
    have th: "(- ?t / ?c + - ?s / ?d)/2 = - (?d * ?t + ?c* ?s )/ (2 * ?c * ?d)"
      by (simp add: field_simps)
    have "?rhs \<longleftrightarrow> Ifm vs (- (?d * ?t + ?c* ?s )/ (2*?c*?d) # bs) (Lt (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a * (- (?d * ?t + ?c* ?s )/ (2*?c*?d)) + ?r < 0"
      by (simp add: r[of "(- (?d * ?t) - (?c *?s)) / (2 * ?c * ?d)"])
    also have "\<dots> \<longleftrightarrow> (2 * ?c * ?d) * (?a * (- (?d * ?t + ?c* ?s )/ (2*?c*?d)) + ?r) < 0"
      using cd2 cd2'
        mult_less_cancel_left_disj[of "2 * ?c * ?d" "?a * (- (?d * ?t + ?c* ?s)/ (2*?c*?d)) + ?r" 0]
      by simp
    also have "\<dots> \<longleftrightarrow> ?a * (- (?d * ?t + ?c* ?s )) + 2*?c*?d*?r < 0"
      using nonzero_mult_div_cancel_left[of "2*?c*?d"] c d
      by (simp add: algebra_simps diff_divide_distrib del: distrib_right)
    finally show ?thesis
      using cd c d nc nd cd2'
      by (simp add: r[of "(- (?d * ?t) + - (?c *?s)) / (2 * ?c * ?d)"]
          msubstlt_def Let_def evaldjf_ex field_simps lt polyneg_norm polymul_norm)
  next
    case cd: 3
    then have cd2: "2 * ?c * ?d < 0"
      by (simp add: mult_less_0_iff field_simps)
    from cd have c: "?c \<noteq> 0" and d: "?d \<noteq> 0"
      by auto
    from add_frac_eq[OF c d, of "- ?t" "- ?s"]
    have th: "(- ?t / ?c + - ?s / ?d)/2 = - (?d * ?t + ?c* ?s) / (2 * ?c * ?d)"
      by (simp add: field_simps)
    have "?rhs \<longleftrightarrow> Ifm vs (- (?d * ?t + ?c* ?s )/ (2 * ?c * ?d) # bs) (Lt (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a * (- (?d * ?t + ?c* ?s )/ (2 * ?c * ?d)) + ?r < 0"
      by (simp add: r[of "(- (?d * ?t) - (?c *?s)) / (2 * ?c * ?d)"])
    also have "\<dots> \<longleftrightarrow> (2 * ?c * ?d) * (?a * (- (?d * ?t + ?c * ?s )/ (2 * ?c * ?d)) + ?r) > 0"
      using cd2 order_less_not_sym[OF cd2]
        mult_less_cancel_left_disj[of "2 * ?c * ?d" 0 "?a * (- (?d * ?t + ?c* ?s)/ (2*?c*?d)) + ?r"]
      by simp
    also have "\<dots> \<longleftrightarrow> ?a * ((?d * ?t + ?c* ?s )) - 2 * ?c * ?d * ?r < 0"
      using nonzero_mult_div_cancel_left[of "2 * ?c * ?d"] c d
      by (simp add: algebra_simps diff_divide_distrib del: distrib_right)
    finally show ?thesis
      using cd c d nc nd
      by (simp add: r[of "(- (?d * ?t) + - (?c *?s)) / (2 * ?c * ?d)"]
          msubstlt_def Let_def evaldjf_ex field_simps lt polyneg_norm polymul_norm)
  next
    case cd: 4
    from cd(1) have c'': "2 * ?c > 0"
      by (simp add: zero_less_mult_iff)
    from cd(1) have c': "2 * ?c \<noteq> 0"
      by simp
    from cd(2) have th: "(- ?t / ?c + - ?s / ?d)/2 = - ?t / (2 * ?c)"
      by (simp add: field_simps)
    have "?rhs \<longleftrightarrow> Ifm vs (- ?t / (2 * ?c) # bs) (Lt (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a * (- ?t / (2 * ?c))+ ?r < 0"
      by (simp add: r[of "- (?t / (2 * ?c))"])
    also have "\<dots> \<longleftrightarrow> 2 * ?c * (?a * (- ?t / (2 * ?c))+ ?r) < 0"
      using cd(1) mult_less_cancel_left_disj[of "2 * ?c" "?a* (- ?t / (2*?c))+ ?r" 0] c' c''
        order_less_not_sym[OF c'']
      by simp
    also have "\<dots> \<longleftrightarrow> - ?a * ?t + 2 * ?c * ?r < 0"
      using nonzero_mult_div_cancel_left[OF c'] \<open>?c > 0\<close>
      by (simp add: algebra_simps diff_divide_distrib less_le del: distrib_right)
    finally show ?thesis
      using cd nc nd
      by (simp add: r[of "- (?t / (2*?c))"] msubstlt_def Let_def evaldjf_ex field_simps
          lt polyneg_norm polymul_norm)
  next
    case cd: 5
    from cd(1) have c': "2 * ?c \<noteq> 0"
      by simp
    from cd(1) have c'': "2 * ?c < 0"
      by (simp add: mult_less_0_iff)
    from cd(2) have th: "(- ?t / ?c + - ?s / ?d)/2 = - ?t / (2 * ?c)"
      by (simp add: field_simps)
    have "?rhs \<longleftrightarrow> Ifm vs (- ?t / (2*?c) # bs) (Lt (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a * (- ?t / (2*?c))+ ?r < 0"
      by (simp add: r[of "- (?t / (2*?c))"])
    also have "\<dots> \<longleftrightarrow> 2 * ?c * (?a * (- ?t / (2 * ?c))+ ?r) > 0"
      using cd(1) order_less_not_sym[OF c''] less_imp_neq[OF c''] c''
        mult_less_cancel_left_disj[of "2 * ?c" 0 "?a* (- ?t / (2*?c))+ ?r"]
      by simp
    also have "\<dots> \<longleftrightarrow> ?a*?t -  2*?c *?r < 0"
      using nonzero_mult_div_cancel_left[OF c'] cd(1) order_less_not_sym[OF c'']
          less_imp_neq[OF c''] c''
        by (simp add: algebra_simps diff_divide_distrib del: distrib_right)
    finally show ?thesis
      using cd nc nd
      by (simp add: r[of "- (?t / (2*?c))"] msubstlt_def Let_def evaldjf_ex field_simps
          lt polyneg_norm polymul_norm)
  next
    case cd: 6
    from cd(2) have d'': "2 * ?d > 0"
      by (simp add: zero_less_mult_iff)
    from cd(2) have d': "2 * ?d \<noteq> 0"
      by simp
    from cd(1) have th: "(- ?t / ?c + - ?s / ?d)/2 = - ?s / (2 * ?d)"
      by (simp add: field_simps)
    have "?rhs \<longleftrightarrow> Ifm vs (- ?s / (2 * ?d) # bs) (Lt (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a * (- ?s / (2 * ?d))+ ?r < 0"
      by (simp add: r[of "- (?s / (2 * ?d))"])
    also have "\<dots> \<longleftrightarrow> 2 * ?d * (?a * (- ?s / (2 * ?d))+ ?r) < 0"
      using cd(2) mult_less_cancel_left_disj[of "2 * ?d" "?a * (- ?s / (2 * ?d))+ ?r" 0] d' d''
        order_less_not_sym[OF d'']
      by simp
    also have "\<dots> \<longleftrightarrow> - ?a * ?s+  2 * ?d * ?r < 0"
      using nonzero_mult_div_cancel_left[OF d'] cd(2)
      by (simp add: algebra_simps diff_divide_distrib less_le del: distrib_right)
    finally show ?thesis
      using cd nc nd
      by (simp add: r[of "- (?s / (2*?d))"] msubstlt_def Let_def evaldjf_ex field_simps
          lt polyneg_norm polymul_norm)
  next
    case cd: 7
    from cd(2) have d': "2 * ?d \<noteq> 0"
      by simp
    from cd(2) have d'': "2 * ?d < 0"
      by (simp add: mult_less_0_iff)
    from cd(1) have th: "(- ?t / ?c + - ?s / ?d)/2 = - ?s / (2*?d)"
      by (simp add: field_simps)
    have "?rhs \<longleftrightarrow> Ifm vs (- ?s / (2 * ?d) # bs) (Lt (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a * (- ?s / (2 * ?d)) + ?r < 0"
      by (simp add: r[of "- (?s / (2 * ?d))"])
    also have "\<dots> \<longleftrightarrow> 2 * ?d * (?a * (- ?s / (2 * ?d)) + ?r) > 0"
      using cd(2) order_less_not_sym[OF d''] less_imp_neq[OF d''] d''
        mult_less_cancel_left_disj[of "2 * ?d" 0 "?a* (- ?s / (2*?d))+ ?r"]
      by simp
    also have "\<dots> \<longleftrightarrow> ?a * ?s -  2 * ?d * ?r < 0"
      using nonzero_mult_div_cancel_left[OF d'] cd(2) order_less_not_sym[OF d'']
          less_imp_neq[OF d''] d''
        by (simp add: algebra_simps diff_divide_distrib del: distrib_right)
    finally show ?thesis
      using cd nc nd
      by (simp add: r[of "- (?s / (2*?d))"] msubstlt_def Let_def evaldjf_ex field_simps
          lt polyneg_norm polymul_norm)
  qed
qed

definition "msubstle c t d s a r =
  evaldjf (case_prod conj)
   [(let cd = c *\<^sub>p d
     in (lt (CP (~\<^sub>p cd)), Le (Add (Mul (~\<^sub>p a) (Add (Mul d t) (Mul c s))) (Mul ((2)\<^sub>p *\<^sub>p cd) r)))),
    (let cd = c *\<^sub>p d
     in (lt (CP cd), Le (Sub (Mul a (Add (Mul d t) (Mul c s))) (Mul ((2)\<^sub>p *\<^sub>p cd) r)))),
    (conj (lt (CP (~\<^sub>p c))) (Eq (CP d)), Le (Add (Mul (~\<^sub>p a) t) (Mul ((2)\<^sub>p *\<^sub>p c) r))),
    (conj (lt (CP c)) (Eq (CP d)), Le (Sub (Mul a t) (Mul ((2)\<^sub>p *\<^sub>p c) r))),
    (conj (lt (CP (~\<^sub>p d))) (Eq (CP c)), Le (Add (Mul (~\<^sub>p a) s) (Mul ((2)\<^sub>p *\<^sub>p d) r))),
    (conj (lt (CP d)) (Eq (CP c)), Le (Sub (Mul a s) (Mul ((2)\<^sub>p *\<^sub>p d) r))),
    (conj (Eq (CP c)) (Eq (CP d)), Le r)]"

lemma msubstle_nb:
  assumes lp: "islin (Le (CNP 0 a r))"
    and t: "tmbound0 t"
    and s: "tmbound0 s"
  shows "bound0 (msubstle c t d s a r)"
proof -
  have th: "\<forall>x\<in> set
   [(let cd = c *\<^sub>p d
     in (lt (CP (~\<^sub>p cd)), Le (Add (Mul (~\<^sub>p a) (Add (Mul d t) (Mul c s))) (Mul ((2)\<^sub>p *\<^sub>p cd) r)))),
    (let cd = c *\<^sub>p d
     in (lt (CP cd), Le (Sub (Mul a (Add (Mul d t) (Mul c s))) (Mul ((2)\<^sub>p *\<^sub>p cd) r)))),
    (conj (lt (CP (~\<^sub>p c))) (Eq (CP d)) , Le (Add (Mul (~\<^sub>p a) t) (Mul ((2)\<^sub>p *\<^sub>p c) r))),
    (conj (lt (CP c)) (Eq (CP d)) , Le (Sub (Mul a t) (Mul ((2)\<^sub>p *\<^sub>p c) r))),
    (conj (lt (CP (~\<^sub>p d))) (Eq (CP c)) , Le (Add (Mul (~\<^sub>p a) s) (Mul ((2)\<^sub>p *\<^sub>p d) r))),
    (conj (lt (CP d)) (Eq (CP c)) , Le (Sub (Mul a s) (Mul ((2)\<^sub>p *\<^sub>p d) r))),
    (conj (Eq (CP c)) (Eq (CP d)) , Le r)]. bound0 (case_prod conj x)"
    using lp by (simp add: Let_def t s lt_nb)
  from evaldjf_bound0[OF th] show ?thesis
    by (simp add: msubstle_def)
qed

lemma msubstle:
  assumes nc: "isnpoly c"
    and nd: "isnpoly d"
    and lp: "islin (Le (CNP 0 a r))"
  shows "Ifm vs (x#bs) (msubstle c t d s a r) \<longleftrightarrow>
    Ifm vs (((- Itm vs (x#bs) t /  Ipoly vs c + - Itm vs (x#bs) s / Ipoly vs d) /2)#bs) (Le (CNP 0 a r))"
  (is "?lhs = ?rhs")
proof -
  let ?Nt = "\<lambda>x t. Itm vs (x#bs) t"
  let ?N = "\<lambda>p. Ipoly vs p"
  let ?c = "?N c"
  let ?d = "?N d"
  let ?t = "?Nt x t"
  let ?s = "?Nt x s"
  let ?a = "?N a"
  let ?r = "?Nt x r"
  from lp have lin:"isnpoly a" "a \<noteq> 0\<^sub>p" "tmbound0 r" "allpolys isnpoly r"
    by simp_all
  note r = tmbound0_I[OF lin(3), of vs _ bs x]
  have "?c * ?d < 0 \<or> ?c * ?d > 0 \<or> (?c = 0 \<and> ?d = 0) \<or> (?c = 0 \<and> ?d < 0) \<or> (?c = 0 \<and> ?d > 0) \<or> (?c < 0 \<and> ?d = 0) \<or> (?c > 0 \<and> ?d = 0)"
    by auto
  then consider "?c = 0" "?d = 0" | "?c * ?d > 0" | "?c * ?d < 0"
    | "?c > 0" "?d = 0" | "?c < 0" "?d = 0" | "?c = 0" "?d > 0" | "?c = 0" "?d < 0"
    by blast
  then show ?thesis
  proof cases
    case 1
    with nc nd show ?thesis
      by (simp add: polyneg_norm polymul_norm lt r[of 0] msubstle_def Let_def evaldjf_ex)
  next
    case dc: 2
    from dc have dc': "2 * ?c * ?d > 0"
      by simp
    then have c: "?c \<noteq> 0" and d: "?d \<noteq> 0"
      by auto
    from dc' have dc'': "\<not> 2 * ?c * ?d < 0"
      by simp
    from add_frac_eq[OF c d, of "- ?t" "- ?s"]
    have th: "(- ?t / ?c + - ?s / ?d)/2 = - (?d * ?t + ?c * ?s )/ (2 * ?c * ?d)"
      by (simp add: field_simps)
    have "?rhs \<longleftrightarrow> Ifm vs (- (?d * ?t + ?c* ?s )/ (2*?c*?d) # bs) (Le (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a * (- (?d * ?t + ?c* ?s )/ (2*?c*?d)) + ?r \<le> 0"
      by (simp add: r[of "(- (?d * ?t) - (?c *?s)) / (2 * ?c * ?d)"])
    also have "\<dots> \<longleftrightarrow> (2 * ?c * ?d) * (?a * (- (?d * ?t + ?c* ?s )/ (2*?c*?d)) + ?r) \<le> 0"
      using dc' dc''
        mult_le_cancel_left[of "2 * ?c * ?d" "?a * (- (?d * ?t + ?c* ?s)/ (2*?c*?d)) + ?r" 0]
      by simp
    also have "\<dots> \<longleftrightarrow> ?a * (- (?d * ?t + ?c* ?s )) + 2*?c*?d*?r \<le> 0"
      using nonzero_mult_div_cancel_left[of "2*?c*?d"] c d
      by (simp add: algebra_simps diff_divide_distrib del: distrib_right)
    finally show ?thesis
      using dc c d  nc nd dc'
      by (simp add: r[of "(- (?d * ?t) + - (?c *?s)) / (2 * ?c * ?d)"] msubstle_def
          Let_def evaldjf_ex field_simps lt polyneg_norm polymul_norm)
  next
    case dc: 3
    from dc have dc': "2 * ?c * ?d < 0"
      by (simp add: mult_less_0_iff field_simps add_neg_neg add_pos_pos)
    then have c: "?c \<noteq> 0" and d: "?d \<noteq> 0"
      by auto
    from add_frac_eq[OF c d, of "- ?t" "- ?s"]
    have th: "(- ?t / ?c + - ?s / ?d)/2 = - (?d * ?t + ?c* ?s )/ (2 * ?c * ?d)"
      by (simp add: field_simps)
    have "?rhs \<longleftrightarrow> Ifm vs (- (?d * ?t + ?c* ?s )/ (2*?c*?d) # bs) (Le (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a * (- (?d * ?t + ?c* ?s )/ (2*?c*?d)) + ?r \<le> 0"
      by (simp add: r[of "(- (?d * ?t) - (?c *?s)) / (2 * ?c * ?d)"])
    also have "\<dots> \<longleftrightarrow> (2 * ?c * ?d) * (?a * (- (?d * ?t + ?c* ?s )/ (2*?c*?d)) + ?r) \<ge> 0"
      using dc' order_less_not_sym[OF dc']
        mult_le_cancel_left[of "2 * ?c * ?d" 0 "?a * (- (?d * ?t + ?c* ?s)/ (2*?c*?d)) + ?r"]
      by simp
    also have "\<dots> \<longleftrightarrow> ?a * ((?d * ?t + ?c* ?s )) - 2 * ?c * ?d * ?r \<le> 0"
      using nonzero_mult_div_cancel_left[of "2 * ?c * ?d"] c d
      by (simp add: algebra_simps diff_divide_distrib del: distrib_right)
    finally show ?thesis
      using dc c d  nc nd
      by (simp add: r[of "(- (?d * ?t) + - (?c *?s)) / (2 * ?c * ?d)"] msubstle_def
          Let_def evaldjf_ex field_simps lt polyneg_norm polymul_norm)
  next
    case 4
    have c: "?c > 0" and d: "?d = 0" by fact+
    from c have c'': "2 * ?c > 0"
      by (simp add: zero_less_mult_iff)
    from c have c': "2 * ?c \<noteq> 0"
      by simp
    from d have th: "(- ?t / ?c + - ?s / ?d)/2 = - ?t / (2*?c)"
      by (simp add: field_simps)
    have "?rhs \<longleftrightarrow> Ifm vs (- ?t / (2 * ?c) # bs) (Le (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a * (- ?t / (2 * ?c))+ ?r \<le> 0"
      by (simp add: r[of "- (?t / (2 * ?c))"])
    also have "\<dots> \<longleftrightarrow> 2 * ?c * (?a * (- ?t / (2 * ?c))+ ?r) \<le> 0"
      using c mult_le_cancel_left[of "2 * ?c" "?a* (- ?t / (2*?c))+ ?r" 0] c' c''
        order_less_not_sym[OF c'']
      by simp
    also have "\<dots> \<longleftrightarrow> - ?a*?t+  2*?c *?r \<le> 0"
      using nonzero_mult_div_cancel_left[OF c'] c
      by (simp add: algebra_simps diff_divide_distrib less_le del: distrib_right)
    finally show ?thesis
      using c d nc nd
      by (simp add: r[of "- (?t / (2*?c))"] msubstle_def Let_def
          evaldjf_ex field_simps lt polyneg_norm polymul_norm)
  next
    case 5
    have c: "?c < 0" and d: "?d = 0" by fact+
    then have c': "2 * ?c \<noteq> 0"
      by simp
    from c have c'': "2 * ?c < 0"
      by (simp add: mult_less_0_iff)
    from d have th: "(- ?t / ?c + - ?s / ?d)/2 = - ?t / (2*?c)"
      by (simp add: field_simps)
    have "?rhs \<longleftrightarrow> Ifm vs (- ?t / (2 * ?c) # bs) (Le (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a * (- ?t / (2*?c))+ ?r \<le> 0"
      by (simp add: r[of "- (?t / (2*?c))"])
    also have "\<dots> \<longleftrightarrow> 2 * ?c * (?a * (- ?t / (2 * ?c))+ ?r) \<ge> 0"
      using c order_less_not_sym[OF c''] less_imp_neq[OF c''] c''
        mult_le_cancel_left[of "2 * ?c" 0 "?a* (- ?t / (2*?c))+ ?r"]
      by simp
    also have "\<dots> \<longleftrightarrow> ?a * ?t - 2 * ?c * ?r \<le> 0"
      using nonzero_mult_div_cancel_left[OF c'] c order_less_not_sym[OF c'']
          less_imp_neq[OF c''] c''
        by (simp add: algebra_simps diff_divide_distrib del: distrib_right)
    finally show ?thesis using c d nc nd
      by (simp add: r[of "- (?t / (2*?c))"] msubstle_def Let_def
          evaldjf_ex field_simps lt polyneg_norm polymul_norm)
  next
    case 6
    have c: "?c = 0" and d: "?d > 0" by fact+
    from d have d'': "2 * ?d > 0"
      by (simp add: zero_less_mult_iff)
    from d have d': "2 * ?d \<noteq> 0"
      by simp
    from c have th: "(- ?t / ?c + - ?s / ?d)/2 = - ?s / (2 * ?d)"
      by (simp add: field_simps)
    have "?rhs \<longleftrightarrow> Ifm vs (- ?s / (2 * ?d) # bs) (Le (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a * (- ?s / (2 * ?d))+ ?r \<le> 0"
      by (simp add: r[of "- (?s / (2*?d))"])
    also have "\<dots> \<longleftrightarrow> 2 * ?d * (?a * (- ?s / (2 * ?d)) + ?r) \<le> 0"
      using d mult_le_cancel_left[of "2 * ?d" "?a* (- ?s / (2*?d))+ ?r" 0] d' d''
        order_less_not_sym[OF d'']
      by simp
    also have "\<dots> \<longleftrightarrow> - ?a * ?s + 2 * ?d * ?r \<le> 0"
      using nonzero_mult_div_cancel_left[OF d'] d
      by (simp add: algebra_simps diff_divide_distrib less_le del: distrib_right)
    finally show ?thesis
      using c d nc nd
      by (simp add: r[of "- (?s / (2*?d))"] msubstle_def Let_def
          evaldjf_ex field_simps lt polyneg_norm polymul_norm)
  next
    case 7
    have c: "?c = 0" and d: "?d < 0" by fact+
    then have d': "2 * ?d \<noteq> 0"
      by simp
    from d have d'': "2 * ?d < 0"
      by (simp add: mult_less_0_iff)
    from c have th: "(- ?t / ?c + - ?s / ?d)/2 = - ?s / (2*?d)"
      by (simp add: field_simps)
    have "?rhs \<longleftrightarrow> Ifm vs (- ?s / (2*?d) # bs) (Le (CNP 0 a r))"
      by (simp only: th)
    also have "\<dots> \<longleftrightarrow> ?a* (- ?s / (2*?d))+ ?r \<le> 0"
      by (simp add: r[of "- (?s / (2*?d))"])
    also have "\<dots> \<longleftrightarrow> 2*?d * (?a* (- ?s / (2*?d))+ ?r) \<ge> 0"
      using d order_less_not_sym[OF d''] less_imp_neq[OF d''] d''
        mult_le_cancel_left[of "2 * ?d" 0 "?a* (- ?s / (2*?d))+ ?r"]
      by simp
    also have "\<dots> \<longleftrightarrow> ?a * ?s -  2 * ?d * ?r \<le> 0"
      using nonzero_mult_div_cancel_left[OF d'] d order_less_not_sym[OF d'']
        less_imp_neq[OF d''] d''
      by (simp add: algebra_simps diff_divide_distrib del: distrib_right)
    finally show ?thesis
      using c d nc nd
      by (simp add: r[of "- (?s / (2*?d))"] msubstle_def Let_def
          evaldjf_ex field_simps lt polyneg_norm polymul_norm)
  qed
qed

fun msubst :: "fm \<Rightarrow> (poly \<times> tm) \<times> (poly \<times> tm) \<Rightarrow> fm"
  where
    "msubst (And p q) ((c, t), (d, s)) = conj (msubst p ((c,t),(d,s))) (msubst q ((c, t), (d, s)))"
  | "msubst (Or p q) ((c, t), (d, s)) = disj (msubst p ((c,t),(d,s))) (msubst q ((c, t), (d, s)))"
  | "msubst (Eq (CNP 0 a r)) ((c, t), (d, s)) = msubsteq c t d s a r"
  | "msubst (NEq (CNP 0 a r)) ((c, t), (d, s)) = msubstneq c t d s a r"
  | "msubst (Lt (CNP 0 a r)) ((c, t), (d, s)) = msubstlt c t d s a r"
  | "msubst (Le (CNP 0 a r)) ((c, t), (d, s)) = msubstle c t d s a r"
  | "msubst p ((c, t), (d, s)) = p"

lemma msubst_I:
  assumes lp: "islin p"
    and nc: "isnpoly c"
    and nd: "isnpoly d"
  shows "Ifm vs (x#bs) (msubst p ((c,t),(d,s))) =
    Ifm vs (((- Itm vs (x#bs) t /  Ipoly vs c + - Itm vs (x#bs) s / Ipoly vs d) /2)#bs) p"
  using lp
  by (induct p rule: islin.induct)
    (auto simp add: tmbound0_I
      [where b = "(- (Itm vs (x # bs) t / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>) - (Itm vs (x # bs) s / \<lparr>d\<rparr>\<^sub>p\<^bsup>vs\<^esup>)) / 2"
        and b' = x and bs = bs and vs = vs]
      msubsteq msubstneq msubstlt [OF nc nd] msubstle [OF nc nd])

lemma msubst_nb:
  assumes "islin p"
    and "tmbound0 t"
    and "tmbound0 s"
  shows "bound0 (msubst p ((c,t),(d,s)))"
  using assms
  by (induct p rule: islin.induct) (auto simp add: msubsteq_nb msubstneq_nb msubstlt_nb msubstle_nb)

lemma fr_eq_msubst:
  assumes lp: "islin p"
  shows "(\<exists>x. Ifm vs (x#bs) p) \<longleftrightarrow>
    (Ifm vs (x#bs) (minusinf p) \<or>
     Ifm vs (x#bs) (plusinf p) \<or>
     (\<exists>(c, t) \<in> set (uset p). \<exists>(d, s) \<in> set (uset p).
      Ifm vs (x#bs) (msubst p ((c, t), (d, s)))))"
  (is "(\<exists>x. ?I x p) = (?M \<or> ?P \<or> ?F)" is "?E = ?D")
proof -
  from uset_l[OF lp] have *: "\<forall>(c, s)\<in>set (uset p). isnpoly c \<and> tmbound0 s"
    by blast
  {
    fix c t d s
    assume ctU: "(c, t) \<in>set (uset p)"
      and dsU: "(d,s) \<in>set (uset p)"
      and pts: "Ifm vs ((- Itm vs (x # bs) t / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup> + - Itm vs (x # bs) s / \<lparr>d\<rparr>\<^sub>p\<^bsup>vs\<^esup>) / 2 # bs) p"
    from *[rule_format, OF ctU] *[rule_format, OF dsU] have norm:"isnpoly c" "isnpoly d"
      by simp_all
    from msubst_I[OF lp norm, of vs x bs t s] pts
    have "Ifm vs (x # bs) (msubst p ((c, t), d, s))" ..
  }
  moreover
  {
    fix c t d s
    assume ctU: "(c, t) \<in> set (uset p)"
      and dsU: "(d,s) \<in>set (uset p)"
      and pts: "Ifm vs (x # bs) (msubst p ((c, t), d, s))"
    from *[rule_format, OF ctU] *[rule_format, OF dsU] have norm:"isnpoly c" "isnpoly d"
      by simp_all
    from msubst_I[OF lp norm, of vs x bs t s] pts
    have "Ifm vs ((- Itm vs (x # bs) t / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup> + - Itm vs (x # bs) s / \<lparr>d\<rparr>\<^sub>p\<^bsup>vs\<^esup>) / 2 # bs) p" ..
  }
  ultimately have **: "(\<exists>(c, t) \<in> set (uset p). \<exists>(d, s) \<in> set (uset p).
      Ifm vs ((- Itm vs (x # bs) t / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup> + - Itm vs (x # bs) s / \<lparr>d\<rparr>\<^sub>p\<^bsup>vs\<^esup>) / 2 # bs) p) \<longleftrightarrow> ?F"
    by blast
  from fr_eq[OF lp, of vs bs x, simplified **] show ?thesis .
qed

lemma simpfm_lin:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
  shows "qfree p \<Longrightarrow> islin (simpfm p)"
  by (induct p rule: simpfm.induct) (auto simp add: conj_lin disj_lin)

definition "ferrack p \<equiv>
  let
    q = simpfm p;
    mp = minusinf q;
    pp = plusinf q
  in
    if (mp = T \<or> pp = T) then T
    else
     (let U = alluopairs (remdups (uset  q))
      in decr0 (disj mp (disj pp (evaldjf (simpfm o (msubst q)) U ))))"

lemma ferrack:
  assumes qf: "qfree p"
  shows "qfree (ferrack p) \<and> Ifm vs bs (ferrack p) = Ifm vs bs (E p)"
  (is "_ \<and> ?rhs = ?lhs")
proof -
  let ?I = "\<lambda>x p. Ifm vs (x#bs) p"
  let ?N = "\<lambda>t. Ipoly vs t"
  let ?Nt = "\<lambda>x t. Itm vs (x#bs) t"
  let ?q = "simpfm p"
  let ?U = "remdups(uset ?q)"
  let ?Up = "alluopairs ?U"
  let ?mp = "minusinf ?q"
  let ?pp = "plusinf ?q"
  fix x
  let ?I = "\<lambda>p. Ifm vs (x#bs) p"
  from simpfm_lin[OF qf] simpfm_qf[OF qf] have lq: "islin ?q" and q_qf: "qfree ?q" .
  from minusinf_nb[OF lq] plusinf_nb[OF lq] have mp_nb: "bound0 ?mp" and pp_nb: "bound0 ?pp" .
  from bound0_qf[OF mp_nb] bound0_qf[OF pp_nb] have mp_qf: "qfree ?mp" and pp_qf: "qfree ?pp" .
  from uset_l[OF lq] have U_l: "\<forall>(c, s)\<in>set ?U. isnpoly c \<and> c \<noteq> 0\<^sub>p \<and> tmbound0 s \<and> allpolys isnpoly s"
    by simp
  {
    fix c t d s
    assume ctU: "(c, t) \<in> set ?U"
      and dsU: "(d,s) \<in> set ?U"
    from U_l ctU dsU have norm: "isnpoly c" "isnpoly d"
      by auto
    from msubst_I[OF lq norm, of vs x bs t s] msubst_I[OF lq norm(2,1), of vs x bs s t]
    have "?I (msubst ?q ((c,t),(d,s))) = ?I (msubst ?q ((d,s),(c,t)))"
      by (simp add: field_simps)
  }
  then have th0: "\<forall>x \<in> set ?U. \<forall>y \<in> set ?U. ?I (msubst ?q (x, y)) \<longleftrightarrow> ?I (msubst ?q (y, x))"
    by auto
  {
    fix x
    assume xUp: "x \<in> set ?Up"
    then obtain c t d s
      where ctU: "(c, t) \<in> set ?U"
        and dsU: "(d,s) \<in> set ?U"
        and x: "x = ((c, t),(d, s))"
      using alluopairs_set1[of ?U] by auto
    from U_l[rule_format, OF ctU] U_l[rule_format, OF dsU]
    have nbs: "tmbound0 t" "tmbound0 s" by simp_all
    from simpfm_bound0[OF msubst_nb[OF lq nbs, of c d]]
    have "bound0 ((simpfm o (msubst (simpfm p))) x)"
      using x by simp
  }
  with evaldjf_bound0[of ?Up "(simpfm o (msubst (simpfm p)))"]
  have "bound0 (evaldjf (simpfm o (msubst (simpfm p))) ?Up)" by blast
  with mp_nb pp_nb
  have th1: "bound0 (disj ?mp (disj ?pp (evaldjf (simpfm o (msubst ?q)) ?Up )))"
    by simp
  from decr0_qf[OF th1] have thqf: "qfree (ferrack p)"
    by (simp add: ferrack_def Let_def)
  have "?lhs \<longleftrightarrow> (\<exists>x. Ifm vs (x#bs) ?q)"
    by simp
  also have "\<dots> \<longleftrightarrow> ?I ?mp \<or> ?I ?pp \<or>
      (\<exists>(c, t)\<in>set ?U. \<exists>(d, s)\<in>set ?U. ?I (msubst (simpfm p) ((c, t), d, s)))"
    using fr_eq_msubst[OF lq, of vs bs x] by simp
  also have "\<dots> \<longleftrightarrow> ?I ?mp \<or> ?I ?pp \<or>
      (\<exists>(x, y) \<in> set ?Up. ?I ((simpfm \<circ> msubst ?q) (x, y)))"
    using alluopairs_bex[OF th0] by simp
  also have "\<dots> \<longleftrightarrow> ?I ?mp \<or> ?I ?pp \<or> ?I (evaldjf (simpfm \<circ> msubst ?q) ?Up)"
    by (simp add: evaldjf_ex)
  also have "\<dots> \<longleftrightarrow> ?I (disj ?mp (disj ?pp (evaldjf (simpfm \<circ> msubst ?q) ?Up)))"
    by simp
  also have "\<dots> \<longleftrightarrow> ?rhs"
    using decr0[OF th1, of vs x bs]
    apply (simp add: ferrack_def Let_def)
    apply (cases "?mp = T \<or> ?pp = T")
     apply auto
    done
  finally show ?thesis
    using thqf by blast
qed

definition "frpar p = simpfm (qelim p ferrack)"

lemma frpar: "qfree (frpar p) \<and> (Ifm vs bs (frpar p) \<longleftrightarrow> Ifm vs bs p)"
proof -
  from ferrack
  have th: "\<forall>bs p. qfree p \<longrightarrow> qfree (ferrack p) \<and> Ifm vs bs (ferrack p) = Ifm vs bs (E p)"
    by blast
  from qelim[OF th, of p bs] show ?thesis
    unfolding frpar_def by auto
qed


section \<open>Second implementation: case splits not local\<close>

lemma fr_eq2:
  assumes lp: "islin p"
  shows "(\<exists>x. Ifm vs (x#bs) p) \<longleftrightarrow>
   (Ifm vs (x#bs) (minusinf p) \<or>
    Ifm vs (x#bs) (plusinf p) \<or>
    Ifm vs (0#bs) p \<or>
    (\<exists>(n, t) \<in> set (uset p).
      Ipoly vs n \<noteq> 0 \<and> Ifm vs ((- Itm vs (x#bs) t /  (Ipoly vs n * 2))#bs) p) \<or>
      (\<exists>(n, t) \<in> set (uset p). \<exists>(m, s) \<in> set (uset p).
        Ipoly vs n \<noteq> 0 \<and>
        Ipoly vs m \<noteq> 0 \<and>
        Ifm vs (((- Itm vs (x#bs) t /  Ipoly vs n + - Itm vs (x#bs) s / Ipoly vs m) /2)#bs) p))"
  (is "(\<exists>x. ?I x p) = (?M \<or> ?P \<or> ?Z \<or> ?U \<or> ?F)" is "?E = ?D")
proof
  assume px: "\<exists>x. ?I x p"
  consider "?M \<or> ?P" | "\<not> ?M" "\<not> ?P" by blast
  then show ?D
  proof cases
    case 1
    then show ?thesis by blast
  next
    case 2
    have nmi: "\<not> ?M" and npi: "\<not> ?P" by fact+
    from inf_uset[OF lp nmi npi, OF px]
    obtain c t d s where ct:
      "(c, t) \<in> set (uset p)"
      "(d, s) \<in> set (uset p)"
      "?I ((- Itm vs (x # bs) t / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup> + - Itm vs (x # bs) s / \<lparr>d\<rparr>\<^sub>p\<^bsup>vs\<^esup>) / (1 + 1)) p"
      by auto
    let ?c = "\<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>"
    let ?d = "\<lparr>d\<rparr>\<^sub>p\<^bsup>vs\<^esup>"
    let ?s = "Itm vs (x # bs) s"
    let ?t = "Itm vs (x # bs) t"
    have eq2: "\<And>(x::'a). x + x = 2 * x"
      by (simp add: field_simps)
    consider "?c = 0" "?d = 0" | "?c = 0" "?d \<noteq> 0" | "?c \<noteq> 0" "?d = 0" | "?c \<noteq> 0" "?d \<noteq> 0"
      by auto
    then show ?thesis
    proof cases
      case 1
      with ct show ?thesis by simp
    next
      case 2
      with ct show ?thesis by auto
    next
      case 3
      with ct show ?thesis by auto
    next
      case z: 4
      from z have ?F
        using ct
        apply -
        apply (rule bexI[where x = "(c,t)"])
         apply simp_all
        apply (rule bexI[where x = "(d,s)"])
         apply simp_all
        done
      then show ?thesis by blast
    qed
  qed
next
  assume ?D
  then consider ?M | ?P | ?Z | ?U | ?F by blast
  then show ?E
  proof cases
    case 1
    show ?thesis by (rule minusinf_ex[OF lp \<open>?M\<close>])
  next
    case 2
    show ?thesis by (rule plusinf_ex[OF lp \<open>?P\<close>])
  qed blast+
qed

definition "msubsteq2 c t a b = Eq (Add (Mul a t) (Mul c b))"
definition "msubstltpos c t a b = Lt (Add (Mul a t) (Mul c b))"
definition "msubstlepos c t a b = Le (Add (Mul a t) (Mul c b))"
definition "msubstltneg c t a b = Lt (Neg (Add (Mul a t) (Mul c b)))"
definition "msubstleneg c t a b = Le (Neg (Add (Mul a t) (Mul c b)))"

lemma msubsteq2:
  assumes nz: "Ipoly vs c \<noteq> 0"
    and l: "islin (Eq (CNP 0 a b))"
  shows "Ifm vs (x#bs) (msubsteq2 c t a b) =
    Ifm vs (((Itm vs (x#bs) t /  Ipoly vs c ))#bs) (Eq (CNP 0 a b))"
  using nz l tmbound0_I[of b vs x bs "Itm vs (x # bs) t / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>", symmetric]
  by (simp add: msubsteq2_def field_simps)

lemma msubstltpos:
  assumes nz: "Ipoly vs c > 0"
    and l: "islin (Lt (CNP 0 a b))"
  shows "Ifm vs (x#bs) (msubstltpos c t a b) =
    Ifm vs (((Itm vs (x#bs) t / Ipoly vs c ))#bs) (Lt (CNP 0 a b))"
  using nz l tmbound0_I[of b vs x bs "Itm vs (x # bs) t / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>", symmetric]
  by (simp add: msubstltpos_def field_simps)

lemma msubstlepos:
  assumes nz: "Ipoly vs c > 0"
    and l: "islin (Le (CNP 0 a b))"
  shows "Ifm vs (x#bs) (msubstlepos c t a b) =
    Ifm vs (((Itm vs (x#bs) t /  Ipoly vs c ))#bs) (Le (CNP 0 a b))"
  using nz l tmbound0_I[of b vs x bs "Itm vs (x # bs) t / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>", symmetric]
  by (simp add: msubstlepos_def field_simps)

lemma msubstltneg:
  assumes nz: "Ipoly vs c < 0"
    and l: "islin (Lt (CNP 0 a b))"
  shows "Ifm vs (x#bs) (msubstltneg c t a b) =
    Ifm vs (((Itm vs (x#bs) t /  Ipoly vs c ))#bs) (Lt (CNP 0 a b))"
  using nz l tmbound0_I[of b vs x bs "Itm vs (x # bs) t / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>", symmetric]
  by (simp add: msubstltneg_def field_simps del: minus_add_distrib)

lemma msubstleneg:
  assumes nz: "Ipoly vs c < 0"
    and l: "islin (Le (CNP 0 a b))"
  shows "Ifm vs (x#bs) (msubstleneg c t a b) =
    Ifm vs (((Itm vs (x#bs) t /  Ipoly vs c ))#bs) (Le (CNP 0 a b))"
  using nz l tmbound0_I[of b vs x bs "Itm vs (x # bs) t / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>", symmetric]
  by (simp add: msubstleneg_def field_simps del: minus_add_distrib)

fun msubstpos :: "fm \<Rightarrow> poly \<Rightarrow> tm \<Rightarrow> fm"
  where
    "msubstpos (And p q) c t = And (msubstpos p c t) (msubstpos q c t)"
  | "msubstpos (Or p q) c t = Or (msubstpos p c t) (msubstpos q c t)"
  | "msubstpos (Eq (CNP 0 a r)) c t = msubsteq2 c t a r"
  | "msubstpos (NEq (CNP 0 a r)) c t = Not (msubsteq2 c t a r)"
  | "msubstpos (Lt (CNP 0 a r)) c t = msubstltpos c t a r"
  | "msubstpos (Le (CNP 0 a r)) c t = msubstlepos c t a r"
  | "msubstpos p c t = p"

lemma msubstpos_I:
  assumes lp: "islin p"
    and pos: "Ipoly vs c > 0"
  shows "Ifm vs (x#bs) (msubstpos p c t) =
    Ifm vs (Itm vs (x#bs) t /  Ipoly vs c #bs) p"
  using lp pos
  by (induct p rule: islin.induct)
    (auto simp add: msubsteq2 msubstltpos[OF pos] msubstlepos[OF pos]
      tmbound0_I[of _ vs "Itm vs (x # bs) t / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>" bs x]
      bound0_I[of _ vs "Itm vs (x # bs) t / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>" bs x] field_simps)

fun msubstneg :: "fm \<Rightarrow> poly \<Rightarrow> tm \<Rightarrow> fm"
  where
    "msubstneg (And p q) c t = And (msubstneg p c t) (msubstneg q c t)"
  | "msubstneg (Or p q) c t = Or (msubstneg p c t) (msubstneg q c t)"
  | "msubstneg (Eq (CNP 0 a r)) c t = msubsteq2 c t a r"
  | "msubstneg (NEq (CNP 0 a r)) c t = Not (msubsteq2 c t a r)"
  | "msubstneg (Lt (CNP 0 a r)) c t = msubstltneg c t a r"
  | "msubstneg (Le (CNP 0 a r)) c t = msubstleneg c t a r"
  | "msubstneg p c t = p"

lemma msubstneg_I:
  assumes lp: "islin p"
    and pos: "Ipoly vs c < 0"
  shows "Ifm vs (x#bs) (msubstneg p c t) = Ifm vs (Itm vs (x#bs) t /  Ipoly vs c #bs) p"
  using lp pos
  by (induct p rule: islin.induct)
    (auto simp add: msubsteq2 msubstltneg[OF pos] msubstleneg[OF pos]
      tmbound0_I[of _ vs "Itm vs (x # bs) t / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>" bs x]
      bound0_I[of _ vs "Itm vs (x # bs) t / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup>" bs x] field_simps)

definition "msubst2 p c t =
  disj (conj (lt (CP (polyneg c))) (simpfm (msubstpos p c t)))
    (conj (lt (CP c)) (simpfm (msubstneg p c t)))"

lemma msubst2:
  assumes lp: "islin p"
    and nc: "isnpoly c"
    and nz: "Ipoly vs c \<noteq> 0"
  shows "Ifm vs (x#bs) (msubst2 p c t) = Ifm vs (Itm vs (x#bs) t /  Ipoly vs c #bs) p"
proof -
  let ?c = "Ipoly vs c"
  from nc have anc: "allpolys isnpoly (CP c)" "allpolys isnpoly (CP (~\<^sub>p c))"
    by (simp_all add: polyneg_norm)
  from nz consider "?c < 0" | "?c > 0" by arith
  then show ?thesis
  proof cases
    case c: 1
    from c msubstneg_I[OF lp c, of x bs t] lt[OF anc(1), of vs "x#bs"] lt[OF anc(2), of vs "x#bs"]
    show ?thesis
      by (auto simp add: msubst2_def)
  next
    case c: 2
    from c msubstpos_I[OF lp c, of x bs t] lt[OF anc(1), of vs "x#bs"] lt[OF anc(2), of vs "x#bs"]
    show ?thesis
      by (auto simp add: msubst2_def)
  qed
qed

lemma msubsteq2_nb: "tmbound0 t \<Longrightarrow> islin (Eq (CNP 0 a r)) \<Longrightarrow> bound0 (msubsteq2 c t a r)"
  by (simp add: msubsteq2_def)

lemma msubstltpos_nb: "tmbound0 t \<Longrightarrow> islin (Lt (CNP 0 a r)) \<Longrightarrow> bound0 (msubstltpos c t a r)"
  by (simp add: msubstltpos_def)
lemma msubstltneg_nb: "tmbound0 t \<Longrightarrow> islin (Lt (CNP 0 a r)) \<Longrightarrow> bound0 (msubstltneg c t a r)"
  by (simp add: msubstltneg_def)

lemma msubstlepos_nb: "tmbound0 t \<Longrightarrow> islin (Le (CNP 0 a r)) \<Longrightarrow> bound0 (msubstlepos c t a r)"
  by (simp add: msubstlepos_def)
lemma msubstleneg_nb: "tmbound0 t \<Longrightarrow> islin (Le (CNP 0 a r)) \<Longrightarrow> bound0 (msubstleneg c t a r)"
  by (simp add: msubstleneg_def)

lemma msubstpos_nb:
  assumes lp: "islin p"
    and tnb: "tmbound0 t"
  shows "bound0 (msubstpos p c t)"
  using lp tnb
  by (induct p c t rule: msubstpos.induct)
    (auto simp add: msubsteq2_nb msubstltpos_nb msubstlepos_nb)

lemma msubstneg_nb:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
    and lp: "islin p"
    and tnb: "tmbound0 t"
  shows "bound0 (msubstneg p c t)"
  using lp tnb
  by (induct p c t rule: msubstneg.induct)
    (auto simp add: msubsteq2_nb msubstltneg_nb msubstleneg_nb)

lemma msubst2_nb:
  assumes "SORT_CONSTRAINT('a::field_char_0)"
    and lp: "islin p"
    and tnb: "tmbound0 t"
  shows "bound0 (msubst2 p c t)"
  using lp tnb
  by (simp add: msubst2_def msubstneg_nb msubstpos_nb lt_nb simpfm_bound0)

lemma mult_minus2_left: "-2 * x = - (2 * x)"
  for x :: "'a::comm_ring_1"
  by simp

lemma mult_minus2_right: "x * -2 = - (x * 2)"
  for x :: "'a::comm_ring_1"
  by simp

lemma islin_qf: "islin p \<Longrightarrow> qfree p"
  by (induct p rule: islin.induct) (auto simp add: bound0_qf)

lemma fr_eq_msubst2:
  assumes lp: "islin p"
  shows "(\<exists>x. Ifm vs (x#bs) p) \<longleftrightarrow>
    ((Ifm vs (x#bs) (minusinf p)) \<or>
     (Ifm vs (x#bs) (plusinf p)) \<or>
     Ifm vs (x#bs) (subst0 (CP 0\<^sub>p) p) \<or>
     (\<exists>(n, t) \<in> set (uset p).
      Ifm vs (x# bs) (msubst2 p (n *\<^sub>p (C (-2,1))) t)) \<or>
      (\<exists>(c, t) \<in> set (uset p). \<exists>(d, s) \<in> set (uset p).
        Ifm vs (x#bs) (msubst2 p (C (-2, 1) *\<^sub>p c*\<^sub>p d) (Add (Mul d t) (Mul c s)))))"
  (is "(\<exists>x. ?I x p) = (?M \<or> ?P \<or> ?Pz \<or> ?PU \<or> ?F)" is "?E = ?D")
proof -
  from uset_l[OF lp] have *: "\<forall>(c, s)\<in>set (uset p). isnpoly c \<and> tmbound0 s"
    by blast
  let ?I = "\<lambda>p. Ifm vs (x#bs) p"
  have n2: "isnpoly (C (-2,1))"
    by (simp add: isnpoly_def)
  note eq0 = subst0[OF islin_qf[OF lp], of vs x bs "CP 0\<^sub>p", simplified]

  have eq1: "(\<exists>(n, t) \<in> set (uset p). ?I (msubst2 p (n *\<^sub>p (C (-2,1))) t)) \<longleftrightarrow>
    (\<exists>(n, t) \<in> set (uset p).
      \<lparr>n\<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0 \<and>
      Ifm vs (- Itm vs (x # bs) t / (\<lparr>n\<rparr>\<^sub>p\<^bsup>vs\<^esup> * 2) # bs) p)"
  proof -
    {
      fix n t
      assume H: "(n, t) \<in> set (uset p)" "?I(msubst2 p (n *\<^sub>p C (-2, 1)) t)"
      from H(1) * have "isnpoly n"
        by blast
      then have nn: "isnpoly (n *\<^sub>p (C (-2,1)))"
        by (simp_all add: polymul_norm n2)
      have nn': "allpolys isnpoly (CP (~\<^sub>p (n *\<^sub>p C (-2, 1))))"
        by (simp add: polyneg_norm nn)
      then have nn2: "\<lparr>n *\<^sub>p(C (-2,1)) \<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0" "\<lparr>n \<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0"
        using H(2) nn' nn
        by (auto simp add: msubst2_def lt zero_less_mult_iff mult_less_0_iff)
      from msubst2[OF lp nn nn2(1), of x bs t]
      have "\<lparr>n\<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0 \<and> Ifm vs (- Itm vs (x # bs) t / (\<lparr>n\<rparr>\<^sub>p\<^bsup>vs\<^esup> * 2) # bs) p"
        using H(2) nn2 by (simp add: mult_minus2_right)
    }
    moreover
    {
      fix n t
      assume H:
        "(n, t) \<in> set (uset p)" "\<lparr>n\<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0"
        "Ifm vs (- Itm vs (x # bs) t / (\<lparr>n\<rparr>\<^sub>p\<^bsup>vs\<^esup> * 2) # bs) p"
      from H(1) * have "isnpoly n"
        by blast
      then have nn: "isnpoly (n *\<^sub>p (C (-2,1)))" "\<lparr>n *\<^sub>p(C (-2,1)) \<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0"
        using H(2) by (simp_all add: polymul_norm n2)
      from msubst2[OF lp nn, of x bs t] have "?I (msubst2 p (n *\<^sub>p (C (-2,1))) t)"
        using H(2,3) by (simp add: mult_minus2_right)
    }
    ultimately show ?thesis by blast
  qed
  have eq2: "(\<exists>(c, t) \<in> set (uset p). \<exists>(d, s) \<in> set (uset p).
      Ifm vs (x#bs) (msubst2 p (C (-2, 1) *\<^sub>p c*\<^sub>p d) (Add (Mul d t) (Mul c s)))) \<longleftrightarrow>
    (\<exists>(n, t)\<in>set (uset p). \<exists>(m, s)\<in>set (uset p).
      \<lparr>n\<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0 \<and>
      \<lparr>m\<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0 \<and>
      Ifm vs ((- Itm vs (x # bs) t / \<lparr>n\<rparr>\<^sub>p\<^bsup>vs\<^esup> + - Itm vs (x # bs) s / \<lparr>m\<rparr>\<^sub>p\<^bsup>vs\<^esup>) / 2 # bs) p)"
  proof -
    {
      fix c t d s
      assume H:
        "(c,t) \<in> set (uset p)" "(d,s) \<in> set (uset p)"
        "Ifm vs (x#bs) (msubst2 p (C (-2, 1) *\<^sub>p c*\<^sub>p d) (Add (Mul d t) (Mul c s)))"
      from H(1,2) * have "isnpoly c" "isnpoly d"
        by blast+
      then have nn: "isnpoly (C (-2, 1) *\<^sub>p c*\<^sub>p d)"
        by (simp_all add: polymul_norm n2)
      have stupid:
          "allpolys isnpoly (CP (~\<^sub>p (C (-2, 1) *\<^sub>p c *\<^sub>p d)))"
          "allpolys isnpoly (CP ((C (-2, 1) *\<^sub>p c *\<^sub>p d)))"
        by (simp_all add: polyneg_norm nn)
      have nn': "\<lparr>(C (-2, 1) *\<^sub>p c*\<^sub>p d)\<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0" "\<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0" "\<lparr>d\<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0"
        using H(3)
        by (auto simp add: msubst2_def lt[OF stupid(1)]
            lt[OF stupid(2)] zero_less_mult_iff mult_less_0_iff)
      from msubst2[OF lp nn nn'(1), of x bs ] H(3) nn'
      have "\<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0 \<and> \<lparr>d\<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0 \<and>
          Ifm vs ((- Itm vs (x # bs) t / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup> + - Itm vs (x # bs) s / \<lparr>d\<rparr>\<^sub>p\<^bsup>vs\<^esup>) / 2 # bs) p"
        by (simp add: add_divide_distrib diff_divide_distrib mult_minus2_left mult.commute)
    }
    moreover
    {
      fix c t d s
      assume H:
        "(c, t) \<in> set (uset p)"
        "(d, s) \<in> set (uset p)"
        "\<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0"
        "\<lparr>d\<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0"
        "Ifm vs ((- Itm vs (x # bs) t / \<lparr>c\<rparr>\<^sub>p\<^bsup>vs\<^esup> + - Itm vs (x # bs) s / \<lparr>d\<rparr>\<^sub>p\<^bsup>vs\<^esup>) / 2 # bs) p"
      from H(1,2) * have "isnpoly c" "isnpoly d"
        by blast+
      then have nn: "isnpoly (C (-2, 1) *\<^sub>p c*\<^sub>p d)" "\<lparr>(C (-2, 1) *\<^sub>p c*\<^sub>p d)\<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0"
        using H(3,4) by (simp_all add: polymul_norm n2)
      from msubst2[OF lp nn, of x bs ] H(3,4,5)
      have "Ifm vs (x#bs) (msubst2 p (C (-2, 1) *\<^sub>p c*\<^sub>p d) (Add (Mul d t) (Mul c s)))"
        by (simp add: diff_divide_distrib add_divide_distrib mult_minus2_left mult.commute)
    }
    ultimately show ?thesis by blast
  qed
  from fr_eq2[OF lp, of vs bs x] show ?thesis
    unfolding eq0 eq1 eq2 by blast
qed

definition "ferrack2 p \<equiv>
  let
    q = simpfm p;
    mp = minusinf q;
    pp = plusinf q
  in
    if (mp = T \<or> pp = T) then T
    else
     (let U = remdups (uset  q)
      in
        decr0
          (list_disj
            [mp,
             pp,
             simpfm (subst0 (CP 0\<^sub>p) q),
             evaldjf (\<lambda>(c, t). msubst2 q (c *\<^sub>p C (-2, 1)) t) U,
             evaldjf (\<lambda>((b, a),(d, c)).
              msubst2 q (C (-2, 1) *\<^sub>p b*\<^sub>p d) (Add (Mul d a) (Mul b c))) (alluopairs U)]))"

definition "frpar2 p = simpfm (qelim (prep p) ferrack2)"

lemma ferrack2:
  assumes qf: "qfree p"
  shows "qfree (ferrack2 p) \<and> Ifm vs bs (ferrack2 p) = Ifm vs bs (E p)"
    (is "_ \<and> (?rhs = ?lhs)")
proof -
  let ?J = "\<lambda>x p. Ifm vs (x#bs) p"
  let ?N = "\<lambda>t. Ipoly vs t"
  let ?Nt = "\<lambda>x t. Itm vs (x#bs) t"
  let ?q = "simpfm p"
  let ?qz = "subst0 (CP 0\<^sub>p) ?q"
  let ?U = "remdups(uset ?q)"
  let ?Up = "alluopairs ?U"
  let ?mp = "minusinf ?q"
  let ?pp = "plusinf ?q"
  fix x
  let ?I = "\<lambda>p. Ifm vs (x#bs) p"
  from simpfm_lin[OF qf] simpfm_qf[OF qf] have lq: "islin ?q" and q_qf: "qfree ?q" .
  from minusinf_nb[OF lq] plusinf_nb[OF lq] have mp_nb: "bound0 ?mp" and pp_nb: "bound0 ?pp" .
  from bound0_qf[OF mp_nb] bound0_qf[OF pp_nb] have mp_qf: "qfree ?mp" and pp_qf: "qfree ?pp" .
  from uset_l[OF lq]
  have U_l: "\<forall>(c, s)\<in>set ?U. isnpoly c \<and> c \<noteq> 0\<^sub>p \<and> tmbound0 s \<and> allpolys isnpoly s"
    by simp
  have bnd0: "\<forall>x \<in> set ?U. bound0 ((\<lambda>(c,t). msubst2 ?q (c *\<^sub>p C (-2, 1)) t) x)"
  proof -
    have "bound0 ((\<lambda>(c,t). msubst2 ?q (c *\<^sub>p C (-2, 1)) t) (c,t))"
      if "(c, t) \<in> set ?U" for c t
    proof -
      from U_l that have "tmbound0 t" by blast
      from msubst2_nb[OF lq this] show ?thesis by simp
    qed
    then show ?thesis by auto
  qed
  have bnd1: "\<forall>x \<in> set ?Up. bound0 ((\<lambda>((b, a), (d, c)).
    msubst2 ?q (C (-2, 1) *\<^sub>p b*\<^sub>p d) (Add (Mul d a) (Mul b c))) x)"
  proof -
    have "bound0 ((\<lambda>((b, a),(d, c)).
      msubst2 ?q (C (-2, 1) *\<^sub>p b*\<^sub>p d) (Add (Mul d a) (Mul b c))) ((b,a),(d,c)))"
      if  "((b,a),(d,c)) \<in> set ?Up" for b a d c
    proof -
      from U_l alluopairs_set1[of ?U] that have this: "tmbound0 (Add (Mul d a) (Mul b c))"
        by auto
      from msubst2_nb[OF lq this] show ?thesis
        by simp
    qed
    then show ?thesis by auto
  qed
  have stupid: "bound0 F" by simp
  let ?R =
    "list_disj
     [?mp,
      ?pp,
      simpfm (subst0 (CP 0\<^sub>p) ?q),
      evaldjf (\<lambda>(c,t). msubst2 ?q (c *\<^sub>p C (-2, 1)) t) ?U,
      evaldjf (\<lambda>((b,a),(d,c)).
        msubst2 ?q (C (-2, 1) *\<^sub>p b*\<^sub>p d) (Add (Mul d a) (Mul b c))) (alluopairs ?U)]"
  from subst0_nb[of "CP 0\<^sub>p" ?q] q_qf
    evaldjf_bound0[OF bnd1] evaldjf_bound0[OF bnd0] mp_nb pp_nb stupid
  have nb: "bound0 ?R"
    by (simp add: list_disj_def simpfm_bound0)
  let ?s = "\<lambda>((b, a),(d, c)). msubst2 ?q (C (-2, 1) *\<^sub>p b*\<^sub>p d) (Add (Mul d a) (Mul b c))"

  {
    fix b a d c
    assume baU: "(b,a) \<in> set ?U" and dcU: "(d,c) \<in> set ?U"
    from U_l baU dcU have norm: "isnpoly b" "isnpoly d" "isnpoly (C (-2, 1))"
      by auto (simp add: isnpoly_def)
    have norm2: "isnpoly (C (-2, 1) *\<^sub>p b*\<^sub>p d)" "isnpoly (C (-2, 1) *\<^sub>p d*\<^sub>p b)"
      using norm by (simp_all add: polymul_norm)
    have stupid:
        "allpolys isnpoly (CP (C (-2, 1) *\<^sub>p b *\<^sub>p d))"
        "allpolys isnpoly (CP (C (-2, 1) *\<^sub>p d *\<^sub>p b))"
        "allpolys isnpoly (CP (~\<^sub>p(C (-2, 1) *\<^sub>p b *\<^sub>p d)))"
        "allpolys isnpoly (CP (~\<^sub>p(C (-2, 1) *\<^sub>p d*\<^sub>p b)))"
      by (simp_all add: polyneg_norm norm2)
    have "?I (msubst2 ?q (C (-2, 1) *\<^sub>p b*\<^sub>p d) (Add (Mul d a) (Mul b c))) =
        ?I (msubst2 ?q (C (-2, 1) *\<^sub>p d*\<^sub>p b) (Add (Mul b c) (Mul d a)))"
      (is "?lhs \<longleftrightarrow> ?rhs")
    proof
      assume H: ?lhs
      then have z: "\<lparr>C (-2, 1) *\<^sub>p b *\<^sub>p d\<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0" "\<lparr>C (-2, 1) *\<^sub>p d *\<^sub>p b\<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0"
        by (auto simp add: msubst2_def lt[OF stupid(3)] lt[OF stupid(1)]
            mult_less_0_iff zero_less_mult_iff)
      from msubst2[OF lq norm2(1) z(1), of x bs] msubst2[OF lq norm2(2) z(2), of x bs] H
      show ?rhs
        by (simp add: field_simps)
    next
      assume H: ?rhs
      then have z: "\<lparr>C (-2, 1) *\<^sub>p b *\<^sub>p d\<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0" "\<lparr>C (-2, 1) *\<^sub>p d *\<^sub>p b\<rparr>\<^sub>p\<^bsup>vs\<^esup> \<noteq> 0"
        by (auto simp add: msubst2_def lt[OF stupid(4)] lt[OF stupid(2)]
            mult_less_0_iff zero_less_mult_iff)
      from msubst2[OF lq norm2(1) z(1), of x bs] msubst2[OF lq norm2(2) z(2), of x bs] H
      show ?lhs
        by (simp add: field_simps)
    qed
  }
  then have th0: "\<forall>x \<in> set ?U. \<forall>y \<in> set ?U. ?I (?s (x, y)) \<longleftrightarrow> ?I (?s (y, x))"
    by auto

  have "?lhs \<longleftrightarrow> (\<exists>x. Ifm vs (x#bs) ?q)"
    by simp
  also have "\<dots> \<longleftrightarrow> ?I ?mp \<or> ?I ?pp \<or> ?I (subst0 (CP 0\<^sub>p) ?q) \<or>
      (\<exists>(n, t) \<in> set ?U. ?I (msubst2 ?q (n *\<^sub>p C (-2, 1)) t)) \<or>
      (\<exists>(b, a) \<in> set ?U. \<exists>(d, c) \<in> set ?U.
        ?I (msubst2 ?q (C (-2, 1) *\<^sub>p b*\<^sub>p d) (Add (Mul d a) (Mul b c))))"
    using fr_eq_msubst2[OF lq, of vs bs x] by simp
  also have "\<dots> \<longleftrightarrow> ?I ?mp \<or> ?I ?pp \<or> ?I (subst0 (CP 0\<^sub>p) ?q) \<or>
      (\<exists>(n, t) \<in> set ?U. ?I (msubst2 ?q (n *\<^sub>p C (-2, 1)) t)) \<or>
      (\<exists>x \<in> set ?U. \<exists>y \<in>set ?U. ?I (?s (x, y)))"
    by (simp add: split_def)
  also have "\<dots> \<longleftrightarrow> ?I ?mp \<or> ?I ?pp \<or> ?I (subst0 (CP 0\<^sub>p) ?q) \<or>
      (\<exists>(n, t) \<in> set ?U. ?I (msubst2 ?q (n *\<^sub>p C (-2, 1)) t)) \<or>
      (\<exists>(x, y) \<in> set ?Up. ?I (?s (x, y)))"
    using alluopairs_bex[OF th0] by simp
  also have "\<dots> \<longleftrightarrow> ?I ?R"
    by (simp add: list_disj_def evaldjf_ex split_def)
  also have "\<dots> \<longleftrightarrow> ?rhs"
    unfolding ferrack2_def
    apply (cases "?mp = T")
     apply (simp add: list_disj_def)
    apply (cases "?pp = T")
     apply (simp add: list_disj_def)
    apply (simp_all add: Let_def decr0[OF nb])
    done
  finally show ?thesis using decr0_qf[OF nb]
    by (simp add: ferrack2_def Let_def)
qed

lemma frpar2: "qfree (frpar2 p) \<and> (Ifm vs bs (frpar2 p) \<longleftrightarrow> Ifm vs bs p)"
proof -
  from ferrack2
  have this: "\<forall>bs p. qfree p \<longrightarrow> qfree (ferrack2 p) \<and> Ifm vs bs (ferrack2 p) = Ifm vs bs (E p)"
    by blast
  from qelim[OF this, of "prep p" bs] show ?thesis
    unfolding frpar2_def by (auto simp add: prep)
qed

oracle frpar_oracle =
\<open>
let

val mk_C = @{code C} o apply2 @{code int_of_integer};
val mk_poly_Bound = @{code poly.Bound} o @{code nat_of_integer};
val mk_Bound = @{code Bound} o @{code nat_of_integer};

val dest_num = snd o HOLogic.dest_number;

fun try_dest_num t = SOME ((snd o HOLogic.dest_number) t)
  handle TERM _ => NONE;

fun dest_nat (t as \<^Const_>\<open>Suc\<close>) = HOLogic.dest_nat t  (* FIXME !? *)
  | dest_nat t = dest_num t;

fun the_index ts t =
  let
    val k = find_index (fn t' => t aconv t') ts;
  in if k < 0 then raise General.Subscript else k end;

fun num_of_term ps \<^Const_>\<open>uminus _ for t\<close> = @{code poly.Neg} (num_of_term ps t)
  | num_of_term ps \<^Const_>\<open>plus _ for a b\<close> = @{code poly.Add} (num_of_term ps a, num_of_term ps b)
  | num_of_term ps \<^Const_>\<open>minus _ for a b\<close> = @{code poly.Sub} (num_of_term ps a, num_of_term ps b)
  | num_of_term ps \<^Const_>\<open>times _ for a b\<close> = @{code poly.Mul} (num_of_term ps a, num_of_term ps b)
  | num_of_term ps \<^Const_>\<open>power _ for a n\<close> =
      @{code poly.Pw} (num_of_term ps a, @{code nat_of_integer} (dest_nat n))
  | num_of_term ps \<^Const_>\<open>divide _ for a b\<close> = mk_C (dest_num a, dest_num b)
  | num_of_term ps t =
      (case try_dest_num t of
        SOME k => mk_C (k, 1)
      | NONE => mk_poly_Bound (the_index ps t));

fun tm_of_term fs ps \<^Const_>\<open>uminus _ for t\<close> = @{code Neg} (tm_of_term fs ps t)
  | tm_of_term fs ps \<^Const_>\<open>plus _ for a b\<close> = @{code Add} (tm_of_term fs ps a, tm_of_term fs ps b)
  | tm_of_term fs ps \<^Const_>\<open>minus _ for a b\<close> = @{code Sub} (tm_of_term fs ps a, tm_of_term fs ps b)
  | tm_of_term fs ps \<^Const_>\<open>times _ for a b\<close> = @{code Mul} (num_of_term ps a, tm_of_term fs ps b)
  | tm_of_term fs ps t = (@{code CP} (num_of_term ps t)
      handle TERM _ => mk_Bound (the_index fs t)
        | General.Subscript => mk_Bound (the_index fs t));

fun fm_of_term fs ps \<^Const_>\<open>True\<close> = @{code T}
  | fm_of_term fs ps \<^Const_>\<open>False\<close> = @{code F}
  | fm_of_term fs ps \<^Const_>\<open>HOL.Not for p\<close> = @{code Not} (fm_of_term fs ps p)
  | fm_of_term fs ps \<^Const_>\<open>HOL.conj for p q\<close> = @{code And} (fm_of_term fs ps p, fm_of_term fs ps q)
  | fm_of_term fs ps \<^Const_>\<open>HOL.disj for p q\<close> = @{code Or} (fm_of_term fs ps p, fm_of_term fs ps q)
  | fm_of_term fs ps \<^Const_>\<open>HOL.implies for p q\<close> =
      @{code Imp} (fm_of_term fs ps p, fm_of_term fs ps q)
  | fm_of_term fs ps \<^Const_>\<open>HOL.eq \<^Type>\<open>bool\<close> for p q\<close> =
      @{code Iff} (fm_of_term fs ps p, fm_of_term fs ps q)
  | fm_of_term fs ps \<^Const_>\<open>HOL.eq _ for p q\<close> =
      @{code Eq} (@{code Sub} (tm_of_term fs ps p, tm_of_term fs ps q))
  | fm_of_term fs ps \<^Const_>\<open>less _ for p q\<close> =
      @{code Lt} (@{code Sub} (tm_of_term fs ps p, tm_of_term fs ps q))
  | fm_of_term fs ps \<^Const_>\<open>less_eq _ for p q\<close> =
      @{code Le} (@{code Sub} (tm_of_term fs ps p, tm_of_term fs ps q))
  | fm_of_term fs ps (\<^Const_>\<open>Ex _\<close> $ Abs (abs as (_, xT, _))) =
      let
        val (xn', p') = Syntax_Trans.variant_abs abs;  (* FIXME !? *)
      in @{code E} (fm_of_term (Free (xn', xT) :: fs) ps p') end
  | fm_of_term fs ps (\<^Const_>\<open>All _\<close> $ Abs (abs as (_, xT, _))) =
      let
        val (xn', p') = Syntax_Trans.variant_abs abs;  (* FIXME !? *)
      in @{code A} (fm_of_term (Free (xn', xT) :: fs) ps p') end
  | fm_of_term fs ps _ = error "fm_of_term";

fun term_of_num T ps (@{code poly.C} (a, b)) =
      let
        val (c, d) = apply2 (@{code integer_of_int}) (a, b)
      in
        if d = 1 then HOLogic.mk_number T c
        else if d = 0 then \<^Const>\<open>zero_class.zero T\<close>
        else \<^Const>\<open>divide T for \<open>HOLogic.mk_number T c\<close> \<open>HOLogic.mk_number T d\<close>\<close>
      end
  | term_of_num T ps (@{code poly.Bound} i) = nth ps (@{code integer_of_nat} i)
  | term_of_num T ps (@{code poly.Add} (a, b)) =
      \<^Const>\<open>plus T for \<open>term_of_num T ps a\<close> \<open>term_of_num T ps b\<close>\<close>
  | term_of_num T ps (@{code poly.Mul} (a, b)) =
      \<^Const>\<open>times T for \<open>term_of_num T ps a\<close> \<open>term_of_num T ps b\<close>\<close>
  | term_of_num T ps (@{code poly.Sub} (a, b)) =
      \<^Const>\<open>minus T for \<open>term_of_num T ps a\<close> \<open>term_of_num T ps b\<close>\<close>
  | term_of_num T ps (@{code poly.Neg} a) =
      \<^Const>\<open>uminus T for \<open>term_of_num T ps a\<close>\<close>
  | term_of_num T ps (@{code poly.Pw} (a, n)) =
      \<^Const>\<open>power T for \<open>term_of_num T ps a\<close> \<open>HOLogic.mk_number \<^Type>\<open>nat\<close> (@{code integer_of_nat} n)\<close>\<close>
  | term_of_num T ps (@{code poly.CN} (c, n, p)) =
      term_of_num T ps (@{code poly.Add} (c, @{code poly.Mul} (@{code poly.Bound} n, p)));

fun term_of_tm T fs ps (@{code CP} p) = term_of_num T ps p
  | term_of_tm T fs ps (@{code Bound} i) = nth fs (@{code integer_of_nat} i)
  | term_of_tm T fs ps (@{code Add} (a, b)) =
      \<^Const>\<open>plus T for \<open>term_of_tm T fs ps a\<close> \<open>term_of_tm T fs ps b\<close>\<close>
  | term_of_tm T fs ps (@{code Mul} (a, b)) =
      \<^Const>\<open>times T for \<open>term_of_num T ps a\<close> \<open>term_of_tm T fs ps b\<close>\<close>
  | term_of_tm T fs ps (@{code Sub} (a, b)) =
      \<^Const>\<open>minus T for \<open>term_of_tm T fs ps a\<close> \<open>term_of_tm T fs ps b\<close>\<close>
  | term_of_tm T fs ps (@{code Neg} a) =
      \<^Const>\<open>uminus T for \<open>term_of_tm T fs ps a\<close>\<close>
  | term_of_tm T fs ps (@{code CNP} (n, c, p)) =
      term_of_tm T fs ps (@{code Add} (@{code Mul} (c, @{code Bound} n), p));

fun term_of_fm T fs ps @{code T} = \<^Const>\<open>True\<close>
  | term_of_fm T fs ps @{code F} = \<^Const>\<open>False\<close>
  | term_of_fm T fs ps (@{code Not} p) = \<^Const>\<open>HOL.Not for \<open>term_of_fm T fs ps p\<close>\<close>
  | term_of_fm T fs ps (@{code And} (p, q)) =
      \<^Const>\<open>HOL.conj for \<open>term_of_fm T fs ps p\<close> \<open>term_of_fm T fs ps q\<close>\<close>
  | term_of_fm T fs ps (@{code Or} (p, q)) =
      \<^Const>\<open>HOL.disj for \<open>term_of_fm T fs ps p\<close> \<open>term_of_fm T fs ps q\<close>\<close>
  | term_of_fm T fs ps (@{code Imp} (p, q)) =
      \<^Const>\<open>HOL.implies for \<open>term_of_fm T fs ps p\<close> \<open>term_of_fm T fs ps q\<close>\<close>
  | term_of_fm T fs ps (@{code Iff} (p, q)) =
      \<^Const>\<open>HOL.eq \<^Type>\<open>bool\<close> for \<open>term_of_fm T fs ps p\<close> \<open>term_of_fm T fs ps q\<close>\<close>
  | term_of_fm T fs ps (@{code Lt} p) =
      \<^Const>\<open>less T for \<open>term_of_tm T fs ps p\<close> \<^Const>\<open>zero_class.zero T\<close>\<close>
  | term_of_fm T fs ps (@{code Le} p) =
      \<^Const>\<open>less_eq T for \<open>term_of_tm T fs ps p\<close> \<^Const>\<open>zero_class.zero T\<close>\<close>
  | term_of_fm T fs ps (@{code Eq} p) =
      \<^Const>\<open>HOL.eq T for \<open>term_of_tm T fs ps p\<close> \<^Const>\<open>zero_class.zero T\<close>\<close>
  | term_of_fm T fs ps (@{code NEq} p) =
      \<^Const>\<open>Not for (* FIXME HOL.Not!? *)
        \<^Const>\<open>HOL.eq T for \<open>term_of_tm T fs ps p\<close> \<^Const>\<open>zero_class.zero T\<close>\<close>\<close>
  | term_of_fm T fs ps _ = error "term_of_fm: quantifiers";

fun frpar_procedure alternative T ps fm =
  let
    val frpar = if alternative then @{code frpar2} else @{code frpar};
    val fs = subtract (op aconv) (map Free (Term.add_frees fm [])) ps;
    val eval = term_of_fm T fs ps o frpar o fm_of_term fs ps;
    val t = HOLogic.dest_Trueprop fm;
  in HOLogic.mk_Trueprop (HOLogic.mk_eq (t, eval t)) end;

in

  fn (ctxt, alternative, ty, ps, ct) =>
    Thm.cterm_of ctxt
      (frpar_procedure alternative ty ps (Thm.term_of ct))

end
\<close>

ML \<open>
structure Parametric_Ferrante_Rackoff =
struct

fun tactic ctxt alternative T ps =
  Object_Logic.full_atomize_tac ctxt
  THEN' CSUBGOAL (fn (g, i) =>
    let
      val th = frpar_oracle (ctxt, alternative, T, ps, g);
    in resolve_tac ctxt [th RS iffD2] i end);

fun method alternative =
  let
    fun keyword k = Scan.lift (Args.$$$ k -- Args.colon) >> K ();
    val parsN = "pars";
    val typN = "type";
    val any_keyword = keyword parsN || keyword typN;
    val terms = Scan.repeat (Scan.unless any_keyword Args.term);
    val typ = Scan.unless any_keyword Args.typ;
  in
    (keyword typN |-- typ) -- (keyword parsN |-- terms) >>
      (fn (T, ps) => fn ctxt => SIMPLE_METHOD' (tactic ctxt alternative T ps))
  end;

end;
\<close>

method_setup frpar = \<open>
  Parametric_Ferrante_Rackoff.method false
\<close> "parametric QE for linear Arithmetic over fields"

method_setup frpar2 = \<open>
  Parametric_Ferrante_Rackoff.method true
\<close> "parametric QE for linear Arithmetic over fields, Version 2"

lemma "\<exists>(x::'a::linordered_field). y \<noteq> -1 \<longrightarrow> (y + 1) * x < 0"
  apply (frpar type: 'a pars: y)
  apply (simp add: field_simps)
  apply (rule spec[where x=y])
  apply (frpar type: 'a pars: "z::'a")
  apply simp
  done

lemma "\<exists>(x::'a::linordered_field). y \<noteq> -1 \<longrightarrow> (y + 1)*x < 0"
  apply (frpar2 type: 'a pars: y)
  apply (simp add: field_simps)
  apply (rule spec[where x=y])
  apply (frpar2 type: 'a pars: "z::'a")
  apply simp
  done

text \<open>Collins/Jones Problem\<close>
(*
lemma "\<exists>(r::'a::{linordered_field, number_ring}). 0 < r \<and> r < 1 \<and> 0 < (2 - 3*r) *(a^2 + b^2) + (2*a)*r \<and> (2 - 3*r) *(a^2 + b^2) + 4*a*r - 2*a - r < 0"
proof -
  have "(\<exists>(r::'a::{linordered_field, number_ring}). 0 < r \<and> r < 1 \<and> 0 < (2 - 3*r) *(a^2 + b^2) + (2*a)*r \<and> (2 - 3*r) *(a^2 + b^2) + 4*a*r - 2*a - r < 0) \<longleftrightarrow> (\<exists>(r::'a::{linordered_field, number_ring}). 0 < r \<and> r < 1 \<and> 0 < 2 *(a^2 + b^2) - (3*(a^2 + b^2)) * r + (2*a)*r \<and> 2*(a^2 + b^2) - (3*(a^2 + b^2) - 4*a + 1)*r - 2*a < 0)" (is "?lhs \<longleftrightarrow> ?rhs")
by (simp add: field_simps)
have "?rhs"

  apply (frpar type: "'a::{linordered_field, number_ring}" pars: "a::'a::{linordered_field, number_ring}" "b::'a::{linordered_field, number_ring}")
  apply (simp add: field_simps)
oops
*)
(*
lemma "ALL (x::'a::{linordered_field, number_ring}) y. (1 - t)*x \<le> (1+t)*y \<and> (1 - t)*y \<le> (1+t)*x --> 0 \<le> y"
apply (frpar type: "'a::{linordered_field, number_ring}" pars: "t::'a::{linordered_field, number_ring}")
oops
*)

text \<open>Collins/Jones Problem\<close>

(*
lemma "\<exists>(r::'a::{linordered_field, number_ring}). 0 < r \<and> r < 1 \<and> 0 < (2 - 3*r) *(a^2 + b^2) + (2*a)*r \<and> (2 - 3*r) *(a^2 + b^2) + 4*a*r - 2*a - r < 0"
proof -
  have "(\<exists>(r::'a::{linordered_field, number_ring}). 0 < r \<and> r < 1 \<and> 0 < (2 - 3*r) *(a^2 + b^2) + (2*a)*r \<and> (2 - 3*r) *(a^2 + b^2) + 4*a*r - 2*a - r < 0) \<longleftrightarrow> (\<exists>(r::'a::{linordered_field, number_ring}). 0 < r \<and> r < 1 \<and> 0 < 2 *(a^2 + b^2) - (3*(a^2 + b^2)) * r + (2*a)*r \<and> 2*(a^2 + b^2) - (3*(a^2 + b^2) - 4*a + 1)*r - 2*a < 0)" (is "?lhs \<longleftrightarrow> ?rhs")
by (simp add: field_simps)
have "?rhs"
  apply (frpar2 type: "'a::{linordered_field, number_ring}" pars: "a::'a::{linordered_field, number_ring}" "b::'a::{linordered_field, number_ring}")
  apply simp
oops
*)

(*
lemma "ALL (x::'a::{linordered_field, number_ring}) y. (1 - t)*x \<le> (1+t)*y \<and> (1 - t)*y \<le> (1+t)*x --> 0 \<le> y"
apply (frpar2 type: "'a::{linordered_field, number_ring}" pars: "t::'a::{linordered_field, number_ring}")
apply (simp add: field_simps linorder_neq_iff[symmetric])
apply ferrack
oops
*)
end
