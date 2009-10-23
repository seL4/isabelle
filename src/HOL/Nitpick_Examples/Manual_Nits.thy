(*  Title:      HOL/Nitpick_Examples/Manual_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009

Examples from the Nitpick manual.
*)

header {* Examples from the Nitpick Manual *}

theory Manual_Nits
imports Main Coinductive_List RealDef
begin

chapter {* 3. First Steps *}

nitpick_params [sat_solver = MiniSatJNI, max_threads = 1]

subsection {* 3.1. Propositional Logic *}

lemma "P \<longleftrightarrow> Q"
nitpick
apply auto
nitpick 1
nitpick 2
oops

subsection {* 3.2. Type Variables *}

lemma "P x \<Longrightarrow> P (THE y. P y)"
nitpick [verbose]
oops

subsection {* 3.3. Constants *}

lemma "P x \<Longrightarrow> P (THE y. P y)"
nitpick [show_consts]
nitpick [full_descrs, show_consts]
nitpick [dont_specialize, full_descrs, show_consts]
oops

lemma "\<exists>!x. P x \<Longrightarrow> P (THE y. P y)"
nitpick
nitpick [card 'a = 1-50]
(* sledgehammer *)
apply (metis the_equality)
done

subsection {* 3.4. Skolemization *}

lemma "\<exists>g. \<forall>x. g (f x) = x \<Longrightarrow> \<forall>y. \<exists>x. y = f x"
nitpick
oops

lemma "\<exists>x. \<forall>f. f x = x"
nitpick
oops

lemma "refl r \<Longrightarrow> sym r"
nitpick
oops

subsection {* 3.5. Numbers *}

lemma "\<lbrakk>i \<le> j; n \<le> (m\<Colon>int)\<rbrakk> \<Longrightarrow> i * n + j * m \<le> i * m + j * n"
nitpick
oops

lemma "\<forall>n. Suc n \<noteq> n \<Longrightarrow> P"
nitpick [card nat = 100, check_potential]
oops

lemma "P Suc"
nitpick [card = 1-6]
oops

lemma "P (op +\<Colon>nat\<Rightarrow>nat\<Rightarrow>nat)"
nitpick [card nat = 1]
nitpick [card nat = 2]
oops

subsection {* 3.6. Inductive Datatypes *}

lemma "hd (xs @ [y, y]) = hd xs"
nitpick
nitpick [show_consts, show_datatypes]
oops

lemma "\<lbrakk>length xs = 1; length ys = 1\<rbrakk> \<Longrightarrow> xs = ys"
nitpick [show_datatypes]
oops

subsection {* 3.7. Typedefs, Records, Rationals, and Reals *}

typedef three = "{0\<Colon>nat, 1, 2}"
by blast

definition A :: three where "A \<equiv> Abs_three 0"
definition B :: three where "B \<equiv> Abs_three 1"
definition C :: three where "C \<equiv> Abs_three 2"

lemma "\<lbrakk>P A; P B\<rbrakk> \<Longrightarrow> P x"
nitpick [show_datatypes]
oops

record point =
  Xcoord :: int
  Ycoord :: int

lemma "Xcoord (p\<Colon>point) = Xcoord (q\<Colon>point)"
nitpick [show_datatypes]
oops

lemma "4 * x + 3 * (y\<Colon>real) \<noteq> 1 / 2"
nitpick [show_datatypes]
oops

subsection {* 3.8. Inductive and Coinductive Predicates *}

inductive even where
"even 0" |
"even n \<Longrightarrow> even (Suc (Suc n))"

lemma "\<exists>n. even n \<and> even (Suc n)"
nitpick [card nat = 100, verbose]
oops

lemma "\<exists>n \<le> 99. even n \<and> even (Suc n)"
nitpick [card nat = 100]
oops

inductive even' where
"even' (0\<Colon>nat)" |
"even' 2" |
"\<lbrakk>even' m; even' n\<rbrakk> \<Longrightarrow> even' (m + n)"

lemma "\<exists>n \<in> {0, 2, 4, 6, 8}. \<not> even' n"
nitpick [card nat = 10, verbose, show_consts]
oops

lemma "even' (n - 2) \<Longrightarrow> even' n"
nitpick [card nat = 10, show_consts]
oops

coinductive nats where
"nats (x\<Colon>nat) \<Longrightarrow> nats x"

lemma "nats = {0, 1, 2, 3, 4}"
nitpick [card nat = 10, show_consts]
oops

inductive odd where
"odd 1" |
"\<lbrakk>odd m; even n\<rbrakk> \<Longrightarrow> odd (m + n)"

lemma "odd n \<Longrightarrow> odd (n - 2)"
nitpick [card nat = 10, show_consts]
oops

subsection {* 3.9. Coinductive Datatypes *}

lemma "xs \<noteq> LCons a xs"
nitpick
oops

lemma "\<lbrakk>xs = LCons a xs; ys = iterates (\<lambda>b. a) b\<rbrakk> \<Longrightarrow> xs = ys"
nitpick [verbose]
nitpick [bisim_depth = -1, verbose]
oops

lemma "\<lbrakk>xs = LCons a xs; ys = LCons a ys\<rbrakk> \<Longrightarrow> xs = ys"
nitpick [bisim_depth = -1, show_datatypes]
nitpick
sorry

subsection {* 3.10. Boxing *}

datatype tm = Var nat | Lam tm | App tm tm

primrec lift where
"lift (Var j) k = Var (if j < k then j else j + 1)" |
"lift (Lam t) k = Lam (lift t (k + 1))" |
"lift (App t u) k = App (lift t k) (lift u k)"

primrec loose where
"loose (Var j) k = (j \<ge> k)" |
"loose (Lam t) k = loose t (Suc k)" |
"loose (App t u) k = (loose t k \<or> loose u k)"

primrec subst\<^isub>1 where
"subst\<^isub>1 \<sigma> (Var j) = \<sigma> j" |
"subst\<^isub>1 \<sigma> (Lam t) =
 Lam (subst\<^isub>1 (\<lambda>n. case n of 0 \<Rightarrow> Var 0 | Suc m \<Rightarrow> lift (\<sigma> m) 1) t)" |
"subst\<^isub>1 \<sigma> (App t u) = App (subst\<^isub>1 \<sigma> t) (subst\<^isub>1 \<sigma> u)"

lemma "\<not> loose t 0 \<Longrightarrow> subst\<^isub>1 \<sigma> t = t"
nitpick [verbose]
nitpick [eval = "subst\<^isub>1 \<sigma> t"]
nitpick [dont_box]
oops

primrec subst\<^isub>2 where
"subst\<^isub>2 \<sigma> (Var j) = \<sigma> j" |
"subst\<^isub>2 \<sigma> (Lam t) =
 Lam (subst\<^isub>2 (\<lambda>n. case n of 0 \<Rightarrow> Var 0 | Suc m \<Rightarrow> lift (\<sigma> m) 0) t)" |
"subst\<^isub>2 \<sigma> (App t u) = App (subst\<^isub>2 \<sigma> t) (subst\<^isub>2 \<sigma> u)"

lemma "\<not> loose t 0 \<Longrightarrow> subst\<^isub>2 \<sigma> t = t"
nitpick
sorry

subsection {* 3.11. Scope Monotonicity *}

lemma "length xs = length ys \<Longrightarrow> rev (zip xs ys) = zip xs (rev ys)"
nitpick [verbose]
nitpick [card = 8, verbose]
oops

lemma "\<exists>g. \<forall>x\<Colon>'b. g (f x) = x \<Longrightarrow> \<forall>y\<Colon>'a. \<exists>x. y = f x"
nitpick [mono]
nitpick
oops

section {* 4. Case Studies *}

nitpick_params [max_potential = 0, max_threads = 2]

subsection {* 4.1. A Context-Free Grammar *}

datatype alphabet = a | b

inductive_set S\<^isub>1 and A\<^isub>1 and B\<^isub>1 where
  "[] \<in> S\<^isub>1"
| "w \<in> A\<^isub>1 \<Longrightarrow> b # w \<in> S\<^isub>1"
| "w \<in> B\<^isub>1 \<Longrightarrow> a # w \<in> S\<^isub>1"
| "w \<in> S\<^isub>1 \<Longrightarrow> a # w \<in> A\<^isub>1"
| "w \<in> S\<^isub>1 \<Longrightarrow> b # w \<in> S\<^isub>1"
| "\<lbrakk>v \<in> B\<^isub>1; v \<in> B\<^isub>1\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>1"

theorem S\<^isub>1_sound:
"w \<in> S\<^isub>1 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
nitpick
oops

inductive_set S\<^isub>2 and A\<^isub>2 and B\<^isub>2 where
  "[] \<in> S\<^isub>2"
| "w \<in> A\<^isub>2 \<Longrightarrow> b # w \<in> S\<^isub>2"
| "w \<in> B\<^isub>2 \<Longrightarrow> a # w \<in> S\<^isub>2"
| "w \<in> S\<^isub>2 \<Longrightarrow> a # w \<in> A\<^isub>2"
| "w \<in> S\<^isub>2 \<Longrightarrow> b # w \<in> B\<^isub>2"
| "\<lbrakk>v \<in> B\<^isub>2; v \<in> B\<^isub>2\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>2"

theorem S\<^isub>2_sound:
"w \<in> S\<^isub>2 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
nitpick
oops

inductive_set S\<^isub>3 and A\<^isub>3 and B\<^isub>3 where
  "[] \<in> S\<^isub>3"
| "w \<in> A\<^isub>3 \<Longrightarrow> b # w \<in> S\<^isub>3"
| "w \<in> B\<^isub>3 \<Longrightarrow> a # w \<in> S\<^isub>3"
| "w \<in> S\<^isub>3 \<Longrightarrow> a # w \<in> A\<^isub>3"
| "w \<in> S\<^isub>3 \<Longrightarrow> b # w \<in> B\<^isub>3"
| "\<lbrakk>v \<in> B\<^isub>3; w \<in> B\<^isub>3\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>3"

theorem S\<^isub>3_sound:
"w \<in> S\<^isub>3 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
nitpick
sorry

theorem S\<^isub>3_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] \<longrightarrow> w \<in> S\<^isub>3"
nitpick
oops

inductive_set S\<^isub>4 and A\<^isub>4 and B\<^isub>4 where
  "[] \<in> S\<^isub>4"
| "w \<in> A\<^isub>4 \<Longrightarrow> b # w \<in> S\<^isub>4"
| "w \<in> B\<^isub>4 \<Longrightarrow> a # w \<in> S\<^isub>4"
| "w \<in> S\<^isub>4 \<Longrightarrow> a # w \<in> A\<^isub>4"
| "\<lbrakk>v \<in> A\<^isub>4; w \<in> A\<^isub>4\<rbrakk> \<Longrightarrow> b # v @ w \<in> A\<^isub>4"
| "w \<in> S\<^isub>4 \<Longrightarrow> b # w \<in> B\<^isub>4"
| "\<lbrakk>v \<in> B\<^isub>4; w \<in> B\<^isub>4\<rbrakk> \<Longrightarrow> a # v @ w \<in> B\<^isub>4"

theorem S\<^isub>4_sound:
"w \<in> S\<^isub>4 \<longrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
nitpick
sorry

theorem S\<^isub>4_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] \<longrightarrow> w \<in> S\<^isub>4"
nitpick
sorry

theorem S\<^isub>4_A\<^isub>4_B\<^isub>4_sound_and_complete:
"w \<in> S\<^isub>4 \<longleftrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
"w \<in> A\<^isub>4 \<longleftrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] + 1"
"w \<in> B\<^isub>4 \<longleftrightarrow> length [x \<leftarrow> w. x = b] = length [x \<leftarrow> w. x = a] + 1"
nitpick
sorry

subsection {* 4.2. AA Trees *}

datatype 'a tree = \<Lambda> | N "'a\<Colon>linorder" nat "'a tree" "'a tree"

primrec data where
"data \<Lambda> = undefined" |
"data (N x _ _ _) = x"

primrec dataset where
"dataset \<Lambda> = {}" |
"dataset (N x _ t u) = {x} \<union> dataset t \<union> dataset u"

primrec level where
"level \<Lambda> = 0" |
"level (N _ k _ _) = k"

primrec left where
"left \<Lambda> = \<Lambda>" |
"left (N _ _ t\<^isub>1 _) = t\<^isub>1"

primrec right where
"right \<Lambda> = \<Lambda>" |
"right (N _ _ _ t\<^isub>2) = t\<^isub>2"

fun wf where
"wf \<Lambda> = True" |
"wf (N _ k t u) =
 (if t = \<Lambda> then
    k = 1 \<and> (u = \<Lambda> \<or> (level u = 1 \<and> left u = \<Lambda> \<and> right u = \<Lambda>))
  else
    wf t \<and> wf u \<and> u \<noteq> \<Lambda> \<and> level t < k \<and> level u \<le> k \<and> level (right u) < k)"

fun skew where
"skew \<Lambda> = \<Lambda>" |
"skew (N x k t u) =
 (if t \<noteq> \<Lambda> \<and> k = level t then
    N (data t) k (left t) (N x k (right t) u)
  else
    N x k t u)"

fun split where
"split \<Lambda> = \<Lambda>" |
"split (N x k t u) =
 (if u \<noteq> \<Lambda> \<and> k = level (right u) then
    N (data u) (Suc k) (N x k t (left u)) (right u)
  else
    N x k t u)"

theorem dataset_skew_split:
"dataset (skew t) = dataset t"
"dataset (split t) = dataset t"
nitpick
sorry

theorem wf_skew_split:
"wf t \<Longrightarrow> skew t = t"
"wf t \<Longrightarrow> split t = t"
nitpick
sorry

primrec insort\<^isub>1 where
"insort\<^isub>1 \<Lambda> x = N x 1 \<Lambda> \<Lambda>" |
"insort\<^isub>1 (N y k t u) x =
 (* (split \<circ> skew) *) (N y k (if x < y then insort\<^isub>1 t x else t)
                             (if x > y then insort\<^isub>1 u x else u))"

theorem wf_insort\<^isub>1: "wf t \<Longrightarrow> wf (insort\<^isub>1 t x)"
nitpick
oops

theorem wf_insort\<^isub>1_nat: "wf t \<Longrightarrow> wf (insort\<^isub>1 t (x\<Colon>nat))"
nitpick [eval = "insort\<^isub>1 t x"]
oops

primrec insort\<^isub>2 where
"insort\<^isub>2 \<Lambda> x = N x 1 \<Lambda> \<Lambda>" |
"insort\<^isub>2 (N y k t u) x =
 (split \<circ> skew) (N y k (if x < y then insort\<^isub>2 t x else t)
                       (if x > y then insort\<^isub>2 u x else u))"

theorem wf_insort\<^isub>2: "wf t \<Longrightarrow> wf (insort\<^isub>2 t x)"
nitpick
sorry

theorem dataset_insort\<^isub>2: "dataset (insort\<^isub>2 t x) = {x} \<union> dataset t"
nitpick
sorry

end
