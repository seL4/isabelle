theory Lambda_Example
imports "HOL-Library.Code_Prolog"
begin

subsection \<open>Lambda\<close>

datatype type =
    Atom nat
  | Fun type type    (infixr \<open>\<Rightarrow>\<close> 200)

datatype dB =
    Var nat
  | App dB dB (infixl \<open>\<degree>\<close> 200)
  | Abs type dB

primrec
  nth_el :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" (\<open>_\<langle>_\<rangle>\<close> [90, 0] 91)
where
  "[]\<langle>i\<rangle> = None"
| "(x # xs)\<langle>i\<rangle> = (case i of 0 \<Rightarrow> Some x | Suc j \<Rightarrow> xs \<langle>j\<rangle>)"

inductive nth_el1 :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool"
where
  "nth_el1 (x # xs) 0 x"
| "nth_el1 xs i y \<Longrightarrow> nth_el1 (x # xs) (Suc i) y"

inductive typing :: "type list \<Rightarrow> dB \<Rightarrow> type \<Rightarrow> bool"  (\<open>_ \<turnstile> _ : _\<close> [50, 50, 50] 50)
  where
    Var [intro!]: "nth_el1 env x T \<Longrightarrow> env \<turnstile> Var x : T"
  | Abs [intro!]: "T # env \<turnstile> t : U \<Longrightarrow> env \<turnstile> Abs T t : (T \<Rightarrow> U)"
  | App [intro!]: "env \<turnstile> s : U \<Rightarrow> T \<Longrightarrow> env \<turnstile> t : T \<Longrightarrow> env \<turnstile> (s \<degree> t) : U"

primrec
  lift :: "[dB, nat] => dB"
where
    "lift (Var i) k = (if i < k then Var i else Var (i + 1))"
  | "lift (s \<degree> t) k = lift s k \<degree> lift t k"
  | "lift (Abs T s) k = Abs T (lift s (k + 1))"

primrec pred :: "nat => nat"
where
  "pred (Suc i) = i"

primrec
  subst :: "[dB, dB, nat] => dB"  (\<open>_[_'/_]\<close> [300, 0, 0] 300)
where
    subst_Var: "(Var i)[s/k] =
      (if k < i then Var (pred i) else if i = k then s else Var i)"
  | subst_App: "(t \<degree> u)[s/k] = t[s/k] \<degree> u[s/k]"
  | subst_Abs: "(Abs T t)[s/k] = Abs T (t[lift s 0 / k+1])"

inductive beta :: "[dB, dB] => bool"  (infixl \<open>\<rightarrow>\<^sub>\<beta>\<close> 50)
  where
    beta [simp, intro!]: "Abs T s \<degree> t \<rightarrow>\<^sub>\<beta> s[t/0]"
  | appL [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> s \<degree> u \<rightarrow>\<^sub>\<beta> t \<degree> u"
  | appR [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> u \<degree> s \<rightarrow>\<^sub>\<beta> u \<degree> t"
  | abs [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> Abs T s \<rightarrow>\<^sub>\<beta> Abs T t"

subsection \<open>Inductive definitions for ordering on naturals\<close>

inductive less_nat
where
  "less_nat 0 (Suc y)"
| "less_nat x y ==> less_nat (Suc x) (Suc y)"

lemma less_nat[code_pred_inline]:
  "x < y = less_nat x y"
apply (rule iffI)
apply (induct x arbitrary: y)
apply (case_tac y) apply (auto intro: less_nat.intros)
apply (case_tac y)
apply (auto intro: less_nat.intros)
apply (induct rule: less_nat.induct)
apply auto
done

lemma [code_pred_inline]: "(x::nat) + 1 = Suc x"
by simp

section \<open>Manual setup to find counterexample\<close>

setup \<open>
  Context.theory_map
    (Quickcheck.add_tester ("prolog", (Code_Prolog.active, Code_Prolog.test_goals)))
\<close>

setup \<open>Code_Prolog.map_code_options (K 
  { ensure_groundness = true,
    limit_globally = NONE,
    limited_types = [(\<^typ>\<open>nat\<close>, 1), (\<^typ>\<open>type\<close>, 1), (\<^typ>\<open>dB\<close>, 1), (\<^typ>\<open>type list\<close>, 1)],
    limited_predicates = [(["typing"], 2), (["nthel1"], 2)],
    replacing = [(("typing", "limited_typing"), "quickcheck"),
                 (("nthel1", "limited_nthel1"), "lim_typing")],
    manual_reorder = []})\<close>

lemma
  "\<Gamma> \<turnstile> t : U \<Longrightarrow> t \<rightarrow>\<^sub>\<beta> t' \<Longrightarrow> \<Gamma> \<turnstile> t' : U"
quickcheck[tester = prolog, iterations = 1, expect = counterexample]
oops

text \<open>Verifying that the found counterexample really is one by means of a proof\<close>

lemma
assumes
  "t' = Var 0"
  "U = Atom 0"
  "\<Gamma> = [Atom 1]"
  "t = App (Abs (Atom 0) (Var 1)) (Var 0)"
shows
  "\<Gamma> \<turnstile> t : U"
  "t \<rightarrow>\<^sub>\<beta> t'"
  "\<not> \<Gamma> \<turnstile> t' : U"
proof -
  from assms show "\<Gamma> \<turnstile> t : U"
    by (auto intro!: typing.intros nth_el1.intros)
next
  from assms have "t \<rightarrow>\<^sub>\<beta> (Var 1)[Var 0/0]"
    by (auto simp only: intro: beta.intros)
  moreover
  from assms have "(Var 1)[Var 0/0] = t'" by simp
  ultimately show "t \<rightarrow>\<^sub>\<beta> t'" by simp
next
  from assms show "\<not> \<Gamma> \<turnstile> t' : U"
    by (auto elim: typing.cases nth_el1.cases)
qed


end

