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
begin

lemma zero_neq_succ [simp]: "zero \<noteq> succ m"
  by (rule succ_neq_zero [symmetric])


text {* \medskip Primitive recursion as a (functional) relation -- polymorphic! *}

inductive2
  Rec :: "'a \<Rightarrow> ('n \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'n \<Rightarrow> 'a \<Rightarrow> bool"
  for e :: 'a and r :: "'n \<Rightarrow> 'a \<Rightarrow> 'a"
where
    Rec_zero: "Rec e r zero e"
  | Rec_succ: "Rec e r m n \<Longrightarrow> Rec e r (succ m) (r m n)"

lemma Rec_functional:
  fixes x :: 'n
  shows "\<exists>!y::'a. Rec e r x y"
proof -
  let ?R = "Rec e r"
  show ?thesis
  proof (induct x)
    case zero
    show "\<exists>!y. ?R zero y"
    proof
      show "?R zero e" ..
      fix y assume "?R zero y"
      then show "y = e" by cases simp_all
    qed
  next
    case (succ m)
    from `\<exists>!y. ?R m y`
    obtain y where y: "?R m y"
      and yy': "\<And>y'. ?R m y' \<Longrightarrow> y = y'" by blast
    show "\<exists>!z. ?R (succ m) z"
    proof
      from y show "?R (succ m) (r m y)" ..
      fix z assume "?R (succ m) z"
      then obtain u where "z = r m u" and "?R m u" by cases simp_all
      with yy' show "z = r m y" by (simp only:)
    qed
  qed
qed


text {* \medskip The recursion operator -- polymorphic! *}

definition
  rec :: "'a \<Rightarrow> ('n \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'n \<Rightarrow> 'a"
  "rec e r x = (THE y. Rec e r x y)"

lemma rec_eval:
  assumes Rec: "Rec e r x y"
  shows "rec e r x = y"
  unfolding rec_def
  using Rec_functional and Rec by (rule the1_equality)

lemma rec_zero [simp]: "rec e r zero = e"
proof (rule rec_eval)
  show "Rec e r zero e" ..
qed

lemma rec_succ [simp]: "rec e r (succ m) = r m (rec e r m)"
proof (rule rec_eval)
  let ?R = "Rec e r"
  have "?R m (rec e r m)"
    unfolding rec_def using Rec_functional by (rule theI')
  then show "?R (succ m) (r m (rec e r m))" ..
qed


text {* \medskip Example: addition (monomorphic) *}

definition
  add :: "'n \<Rightarrow> 'n \<Rightarrow> 'n"
  "add m n = rec n (\<lambda>_ k. succ k) m"

lemma add_zero [simp]: "add zero n = n"
  and add_succ [simp]: "add (succ m) n = succ (add m n)"
  unfolding add_def by simp_all

lemma add_assoc: "add (add k m) n = add k (add m n)"
  by (induct k) simp_all

lemma add_zero_right: "add m zero = m"
  by (induct m) simp_all

lemma add_succ_right: "add m (succ n) = succ (add m n)"
  by (induct m) simp_all

lemma "add (succ (succ (succ zero))) (succ (succ zero)) =
    succ (succ (succ (succ (succ zero))))"
  by simp


text {* \medskip Example: replication (polymorphic) *}

definition
  repl :: "'n \<Rightarrow> 'a \<Rightarrow> 'a list"
  "repl n x = rec [] (\<lambda>_ xs. x # xs) n"

lemma repl_zero [simp]: "repl zero x = []"
  and repl_succ [simp]: "repl (succ n) x = x # repl n x"
  unfolding repl_def by simp_all

lemma "repl (succ (succ (succ zero))) True = [True, True, True]"
  by simp

end


text {* \medskip Just see that our abstract specification makes sense \dots *}

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
