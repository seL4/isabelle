(*  Title:      HOL/Nitpick_Examples/Manual_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2011

Examples from the Nitpick manual.
*)

header {* Examples from the Nitpick Manual *}

(* The "expect" arguments to Nitpick in this theory and the other example
   theories are there so that the example can also serve as a regression test
   suite. *)

theory Manual_Nits
imports Main "~~/src/HOL/Library/Quotient_Product" RealDef
begin

chapter {* 2. First Steps *}

nitpick_params [sat_solver = MiniSat_JNI, max_threads = 1, timeout = 240]

subsection {* 2.1. Propositional Logic *}

lemma "P \<longleftrightarrow> Q"
nitpick [expect = genuine]
apply auto
nitpick [expect = genuine] 1
nitpick [expect = genuine] 2
oops

subsection {* 2.2. Type Variables *}

lemma "x \<in> A \<Longrightarrow> (THE y. y \<in> A) \<in> A"
nitpick [verbose, expect = genuine]
oops

subsection {* 2.3. Constants *}

lemma "x \<in> A \<Longrightarrow> (THE y. y \<in> A) \<in> A"
nitpick [show_consts, expect = genuine]
nitpick [dont_specialize, show_consts, expect = genuine]
oops

lemma "\<exists>!x. x \<in> A \<Longrightarrow> (THE y. y \<in> A) \<in> A"
nitpick [expect = none]
nitpick [card 'a = 1\<emdash>50, expect = none]
(* sledgehammer *)
sledgehammer
by (metis the_equality)

subsection {* 2.4. Skolemization *}

lemma "\<exists>g. \<forall>x. g (f x) = x \<Longrightarrow> \<forall>y. \<exists>x. y = f x"
nitpick [expect = genuine]
oops

lemma "\<exists>x. \<forall>f. f x = x"
nitpick [expect = genuine]
oops

lemma "refl r \<Longrightarrow> sym r"
nitpick [expect = genuine]
oops

subsection {* 2.5. Natural Numbers and Integers *}

lemma "\<lbrakk>i \<le> j; n \<le> (m\<Colon>int)\<rbrakk> \<Longrightarrow> i * n + j * m \<le> i * m + j * n"
nitpick [expect = genuine]
nitpick [binary_ints, bits = 16, expect = genuine]
oops

lemma "\<forall>n. Suc n \<noteq> n \<Longrightarrow> P"
nitpick [card nat = 100, check_potential, tac_timeout = 5, expect = genuine]
oops

lemma "P Suc"
nitpick [expect = none]
oops

lemma "P (op +\<Colon>nat\<Rightarrow>nat\<Rightarrow>nat)"
nitpick [card nat = 1, expect = genuine]
nitpick [card nat = 2, expect = none]
oops

subsection {* 2.6. Inductive Datatypes *}

lemma "hd (xs @ [y, y]) = hd xs"
nitpick [expect = genuine]
nitpick [show_consts, show_datatypes, expect = genuine]
oops

lemma "\<lbrakk>length xs = 1; length ys = 1\<rbrakk> \<Longrightarrow> xs = ys"
nitpick [show_datatypes, expect = genuine]
oops

subsection {* 2.7. Typedefs, Records, Rationals, and Reals *}

typedef three = "{0\<Colon>nat, 1, 2}"
by blast

definition A :: three where "A \<equiv> Abs_three 0"
definition B :: three where "B \<equiv> Abs_three 1"
definition C :: three where "C \<equiv> Abs_three 2"

lemma "\<lbrakk>A \<in> X; B \<in> X\<rbrakk> \<Longrightarrow> c \<in> X"
nitpick [show_datatypes, expect = genuine]
oops

fun my_int_rel where
"my_int_rel (x, y) (u, v) = (x + v = u + y)"

quotient_type my_int = "nat \<times> nat" / my_int_rel
by (auto simp add: equivp_def fun_eq_iff)

definition add_raw where
"add_raw \<equiv> \<lambda>(x, y) (u, v). (x + (u\<Colon>nat), y + (v\<Colon>nat))"

quotient_definition "add\<Colon>my_int \<Rightarrow> my_int \<Rightarrow> my_int" is add_raw

lemma "add x y = add x x"
nitpick [show_datatypes, expect = genuine]
oops

ML {*
fun my_int_postproc _ _ _ T (Const _ $ (Const _ $ t1 $ t2)) =
    HOLogic.mk_number T (snd (HOLogic.dest_number t1)
                         - snd (HOLogic.dest_number t2))
  | my_int_postproc _ _ _ _ t = t
*}

declaration {*
Nitpick_Model.register_term_postprocessor @{typ my_int} my_int_postproc
*}

lemma "add x y = add x x"
nitpick [show_datatypes]
oops

record point =
  Xcoord :: int
  Ycoord :: int

lemma "Xcoord (p\<Colon>point) = Xcoord (q\<Colon>point)"
nitpick [show_datatypes, expect = genuine]
oops

lemma "4 * x + 3 * (y\<Colon>real) \<noteq> 1 / 2"
nitpick [show_datatypes, expect = genuine]
oops

subsection {* 2.8. Inductive and Coinductive Predicates *}

inductive even where
"even 0" |
"even n \<Longrightarrow> even (Suc (Suc n))"

lemma "\<exists>n. even n \<and> even (Suc n)"
nitpick [card nat = 50, unary_ints, verbose, expect = potential]
oops

lemma "\<exists>n \<le> 49. even n \<and> even (Suc n)"
nitpick [card nat = 50, unary_ints, expect = genuine]
oops

inductive even' where
"even' (0\<Colon>nat)" |
"even' 2" |
"\<lbrakk>even' m; even' n\<rbrakk> \<Longrightarrow> even' (m + n)"

lemma "\<exists>n \<in> {0, 2, 4, 6, 8}. \<not> even' n"
nitpick [card nat = 10, unary_ints, verbose, show_consts, expect = genuine]
oops

lemma "even' (n - 2) \<Longrightarrow> even' n"
nitpick [card nat = 10, show_consts, expect = genuine]
oops

coinductive nats where
"nats (x\<Colon>nat) \<Longrightarrow> nats x"

lemma "nats = (\<lambda>n. n \<in> {0, 1, 2, 3, 4})"
nitpick [card nat = 10, show_consts, expect = genuine]
oops

inductive odd where
"odd 1" |
"\<lbrakk>odd m; even n\<rbrakk> \<Longrightarrow> odd (m + n)"

lemma "odd n \<Longrightarrow> odd (n - 2)"
nitpick [card nat = 10, show_consts, expect = genuine]
oops

subsection {* 2.9. Coinductive Datatypes *}

(* Lazy lists are defined in Andreas Lochbihler's "Coinductive" AFP entry. Since
   we cannot rely on its presence, we expediently provide our own
   axiomatization. The examples also work unchanged with Lochbihler's
   "Coinductive_List" theory. *)

definition "llist = (UNIV\<Colon>('a list + (nat \<Rightarrow> 'a)) set)"

typedef (open) 'a llist = "llist\<Colon>('a list + (nat \<Rightarrow> 'a)) set"
unfolding llist_def by auto

definition LNil where
"LNil = Abs_llist (Inl [])"
definition LCons where
"LCons y ys = Abs_llist (case Rep_llist ys of
                           Inl ys' \<Rightarrow> Inl (y # ys')
                         | Inr f \<Rightarrow> Inr (\<lambda>n. case n of 0 \<Rightarrow> y | Suc m \<Rightarrow> f m))"

axiomatization iterates :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a llist"

lemma iterates_def [nitpick_simp]:
"iterates f a = LCons a (iterates f (f a))"
sorry

declaration {*
Nitpick_HOL.register_codatatype @{typ "'a llist"} ""
    (map dest_Const [@{term LNil}, @{term LCons}])
*}

lemma "xs \<noteq> LCons a xs"
nitpick [expect = genuine]
oops

lemma "\<lbrakk>xs = LCons a xs; ys = iterates (\<lambda>b. a) b\<rbrakk> \<Longrightarrow> xs = ys"
nitpick [verbose, expect = genuine]
oops

lemma "\<lbrakk>xs = LCons a xs; ys = LCons a ys\<rbrakk> \<Longrightarrow> xs = ys"
nitpick [bisim_depth = -1, show_datatypes, expect = quasi_genuine]
nitpick [card = 1\<emdash>5, expect = none]
sorry

subsection {* 2.10. Boxing *}

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
nitpick [verbose, expect = genuine]
nitpick [eval = "subst\<^isub>1 \<sigma> t", expect = genuine]
(* nitpick [dont_box, expect = unknown] *)
oops

primrec subst\<^isub>2 where
"subst\<^isub>2 \<sigma> (Var j) = \<sigma> j" |
"subst\<^isub>2 \<sigma> (Lam t) =
 Lam (subst\<^isub>2 (\<lambda>n. case n of 0 \<Rightarrow> Var 0 | Suc m \<Rightarrow> lift (\<sigma> m) 0) t)" |
"subst\<^isub>2 \<sigma> (App t u) = App (subst\<^isub>2 \<sigma> t) (subst\<^isub>2 \<sigma> u)"

lemma "\<not> loose t 0 \<Longrightarrow> subst\<^isub>2 \<sigma> t = t"
nitpick [card = 1\<emdash>5, expect = none]
sorry

subsection {* 2.11. Scope Monotonicity *}

lemma "length xs = length ys \<Longrightarrow> rev (zip xs ys) = zip xs (rev ys)"
nitpick [verbose, expect = genuine]
oops

lemma "\<exists>g. \<forall>x\<Colon>'b. g (f x) = x \<Longrightarrow> \<forall>y\<Colon>'a. \<exists>x. y = f x"
nitpick [mono, expect = none]
nitpick [expect = genuine]
oops

subsection {* 2.12. Inductive Properties *}

inductive_set reach where
"(4\<Colon>nat) \<in> reach" |
"n \<in> reach \<Longrightarrow> n < 4 \<Longrightarrow> 3 * n + 1 \<in> reach" |
"n \<in> reach \<Longrightarrow> n + 2 \<in> reach"

lemma "n \<in> reach \<Longrightarrow> 2 dvd n"
(* nitpick *)
apply (induct set: reach)
  apply auto
 nitpick [card = 1\<emdash>4, bits = 1\<emdash>4, expect = none]
 apply (thin_tac "n \<in> reach")
 nitpick [expect = genuine]
oops

lemma "n \<in> reach \<Longrightarrow> 2 dvd n \<and> n \<noteq> 0"
(* nitpick *)
apply (induct set: reach)
  apply auto
 nitpick [card = 1\<emdash>4, bits = 1\<emdash>4, expect = none]
 apply (thin_tac "n \<in> reach")
 nitpick [expect = genuine]
oops

lemma "n \<in> reach \<Longrightarrow> 2 dvd n \<and> n \<ge> 4"
by (induct set: reach) arith+

datatype 'a bin_tree = Leaf 'a | Branch "'a bin_tree" "'a bin_tree"

primrec labels where
"labels (Leaf a) = {a}" |
"labels (Branch t u) = labels t \<union> labels u"

primrec swap where
"swap (Leaf c) a b =
 (if c = a then Leaf b else if c = b then Leaf a else Leaf c)" |
"swap (Branch t u) a b = Branch (swap t a b) (swap u a b)"

lemma "{a, b} \<subseteq> labels t \<Longrightarrow> labels (swap t a b) = labels t"
(* nitpick *)
proof (induct t)
  case Leaf thus ?case by simp
next
  case (Branch t u) thus ?case
  (* nitpick *)
  nitpick [non_std, show_all, expect = genuine]
oops

lemma "labels (swap t a b) =
       (if a \<in> labels t then
          if b \<in> labels t then labels t else (labels t - {a}) \<union> {b}
        else
          if b \<in> labels t then (labels t - {b}) \<union> {a} else labels t)"
(* nitpick *)
proof (induct t)
  case Leaf thus ?case by simp
next
  case (Branch t u) thus ?case
  nitpick [non_std, card = 1\<emdash>4, expect = none]
  by auto
qed

section {* 3. Case Studies *}

nitpick_params [max_potential = 0]

subsection {* 3.1. A Context-Free Grammar *}

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
nitpick [expect = genuine]
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
nitpick [expect = genuine]
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
nitpick [card = 1\<emdash>5, expect = none]
sorry

theorem S\<^isub>3_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] \<longrightarrow> w \<in> S\<^isub>3"
nitpick [expect = genuine]
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
nitpick [card = 1\<emdash>5, expect = none]
sorry

theorem S\<^isub>4_complete:
"length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] \<longrightarrow> w \<in> S\<^isub>4"
nitpick [card = 1\<emdash>5, expect = none]
sorry

theorem S\<^isub>4_A\<^isub>4_B\<^isub>4_sound_and_complete:
"w \<in> S\<^isub>4 \<longleftrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b]"
"w \<in> A\<^isub>4 \<longleftrightarrow> length [x \<leftarrow> w. x = a] = length [x \<leftarrow> w. x = b] + 1"
"w \<in> B\<^isub>4 \<longleftrightarrow> length [x \<leftarrow> w. x = b] = length [x \<leftarrow> w. x = a] + 1"
nitpick [card = 1\<emdash>5, expect = none]
sorry

subsection {* 3.2. AA Trees *}

datatype 'a aa_tree = \<Lambda> | N "'a\<Colon>linorder" nat "'a aa_tree" "'a aa_tree"

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
nitpick [card = 1\<emdash>5, expect = none]
sorry

theorem wf_skew_split:
"wf t \<Longrightarrow> skew t = t"
"wf t \<Longrightarrow> split t = t"
nitpick [card = 1\<emdash>5, expect = none]
sorry

primrec insort\<^isub>1 where
"insort\<^isub>1 \<Lambda> x = N x 1 \<Lambda> \<Lambda>" |
"insort\<^isub>1 (N y k t u) x =
 (* (split \<circ> skew) *) (N y k (if x < y then insort\<^isub>1 t x else t)
                             (if x > y then insort\<^isub>1 u x else u))"

theorem wf_insort\<^isub>1: "wf t \<Longrightarrow> wf (insort\<^isub>1 t x)"
nitpick [expect = genuine]
oops

theorem wf_insort\<^isub>1_nat: "wf t \<Longrightarrow> wf (insort\<^isub>1 t (x\<Colon>nat))"
nitpick [eval = "insort\<^isub>1 t x", expect = genuine]
oops

primrec insort\<^isub>2 where
"insort\<^isub>2 \<Lambda> x = N x 1 \<Lambda> \<Lambda>" |
"insort\<^isub>2 (N y k t u) x =
 (split \<circ> skew) (N y k (if x < y then insort\<^isub>2 t x else t)
                       (if x > y then insort\<^isub>2 u x else u))"

theorem wf_insort\<^isub>2: "wf t \<Longrightarrow> wf (insort\<^isub>2 t x)"
nitpick [card = 1\<emdash>5, expect = none]
sorry

theorem dataset_insort\<^isub>2: "dataset (insort\<^isub>2 t x) = {x} \<union> dataset t"
nitpick [card = 1\<emdash>5, expect = none]
sorry

end
