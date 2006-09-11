(*
    ID:         $Id$
    Author:     Makarius
*)

header {* Abstract Natural Numbers with polymorphic recursion *}

theory Abstract_NAT
imports Main
begin

text {* Axiomatic Natural Numbers (Peano) -- a monomorphic theory. *}

locale NAT =
  fixes zero :: 'n
    and succ :: "'n \<Rightarrow> 'n"
  assumes succ_inject [simp]: "(succ m = succ n) = (m = n)"
    and succ_neq_zero [simp]: "succ m \<noteq> zero"
    and induct [case_names zero succ, induct type: 'n]:
      "P zero \<Longrightarrow> (\<And>n. P n \<Longrightarrow> P (succ n)) \<Longrightarrow> P n"

lemma (in NAT) zero_neq_succ [simp]: "zero \<noteq> succ m"
  by (rule succ_neq_zero [symmetric])


text {*
  Primitive recursion as a (functional) relation -- polymorphic!

  (We simulate a localized version of the inductive packages using
  explicit premises + parameters, and an abbreviation.) *}

consts
  REC :: "'n \<Rightarrow> ('n \<Rightarrow> 'n) \<Rightarrow> 'a \<Rightarrow> ('n \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('n * 'a) set"
inductive "REC zero succ e r"
  intros
    Rec_zero: "NAT zero succ \<Longrightarrow> (zero, e) \<in> REC zero succ e r"
    Rec_succ: "NAT zero succ \<Longrightarrow> (m, n) \<in> REC zero succ e r \<Longrightarrow>
      (succ m, r m n) \<in> REC zero succ e r"

abbreviation (in NAT)
  "Rec == REC zero succ"

lemma (in NAT) Rec_functional:
  fixes x :: 'n
  shows "\<exists>!y::'a. (x, y) \<in> Rec e r"  (is "\<exists>!y::'a. _ \<in> ?Rec")
proof (induct x)
  case zero
  show "\<exists>!y. (zero, y) \<in> ?Rec"
  proof
    show "(zero, e) \<in> ?Rec" by (rule Rec_zero)
    fix y assume "(zero, y) \<in> ?Rec"
    then show "y = e" by cases simp_all
  qed
next
  case (succ m)
  from `\<exists>!y. (m, y) \<in> ?Rec`
  obtain y where y: "(m, y) \<in> ?Rec"
    and yy': "\<And>y'. (m, y') \<in> ?Rec \<Longrightarrow> y = y'" by blast
  show "\<exists>!z. (succ m, z) \<in> ?Rec"
  proof
    from _ y show "(succ m, r m y) \<in> ?Rec" by (rule Rec_succ)
    fix z assume "(succ m, z) \<in> ?Rec"
    then obtain u where "z = r m u" and "(m, u) \<in> ?Rec" by cases simp_all
    with yy' show "z = r m y" by (simp only:)
  qed
qed


text {* The recursion operator -- polymorphic! *}

definition (in NAT)
  "rec e r x = (THE y. (x, y) \<in> Rec e r)"

lemma (in NAT) rec_eval:
  assumes Rec: "(x, y) \<in> Rec e r"
  shows "rec e r x = y"
  unfolding rec_def
  using Rec_functional and Rec by (rule the1_equality)

lemma (in NAT) rec_zero: "rec e r zero = e"
proof (rule rec_eval)
  show "(zero, e) \<in> Rec e r" by (rule Rec_zero)
qed

lemma (in NAT) rec_succ: "rec e r (succ m) = r m (rec e r m)"
proof (rule rec_eval)
  let ?Rec = "Rec e r"
  have "(m, rec e r m) \<in> ?Rec"
    unfolding rec_def
    using Rec_functional by (rule theI')
  with _ show "(succ m, r m (rec e r m)) \<in> ?Rec" by (rule Rec_succ)
qed


text {* Just see that our abstract specification makes sense \dots *}

interpretation NAT [0 Suc]
proof (rule NAT.intro)
  fix m n
  show "(Suc m = Suc n) = (m = n)" by simp
  show "Suc m \<noteq> 0" by simp
  fix P
  assume zero: "P 0"
    and succ: "\<And>n. P n \<Longrightarrow> P (Suc n)"
  show "P n"
  proof (induct n)
    case 0 show ?case by (rule zero)
  next
    case Suc then show ?case by (rule succ)
  qed
qed

end
