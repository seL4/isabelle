(*  Title:      HOL/Nitpick_Examples/Core_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2011

Examples featuring Nitpick's functional core.
*)

header {* Examples Featuring Nitpick's Functional Core *}

theory Core_Nits
imports Main
begin

nitpick_params [verbose, card = 1\<emdash>6, unary_ints, max_potential = 0,
                sat_solver = MiniSat_JNI, max_threads = 1, timeout = 240]

subsection {* Curry in a Hurry *}

lemma "(\<lambda>f x y. (curry o split) f x y) = (\<lambda>f x y. (\<lambda>x. x) f x y)"
nitpick [card = 1\<emdash>12, expect = none]
by auto

lemma "(\<lambda>f p. (split o curry) f p) = (\<lambda>f p. (\<lambda>x. x) f p)"
nitpick [card = 1\<emdash>12, expect = none]
by auto

lemma "split (curry f) = f"
nitpick [card = 1\<emdash>12, expect = none]
by auto

lemma "curry (split f) = f"
nitpick [card = 1\<emdash>12, expect = none]
by auto

lemma "split (\<lambda>x y. f (x, y)) = f"
nitpick [card = 1\<emdash>12, expect = none]
by auto

subsection {* Representations *}

lemma "\<exists>f. f = (\<lambda>x. x) \<and> f y = y"
nitpick [expect = none]
by auto

lemma "(\<exists>g. \<forall>x. g (f x) = x) \<longrightarrow> (\<forall>y. \<exists>x. y = f x)"
nitpick [card 'a = 25, card 'b = 24, expect = genuine]
nitpick [card = 1\<emdash>10, mono, expect = none]
oops

lemma "\<exists>f. f = (\<lambda>x. x) \<and> f y \<noteq> y"
nitpick [card = 1, expect = genuine]
oops

lemma "P (\<lambda>x. x)"
nitpick [card = 1, expect = genuine]
oops

lemma "{(a\<Colon>'a\<times>'a, b\<Colon>'b)}^-1 = {(b, a)}"
nitpick [card = 1\<emdash>12, expect = none]
by auto

lemma "fst (a, b) = a"
nitpick [card = 1\<emdash>20, expect = none]
by auto

lemma "\<exists>P. P = Id"
nitpick [card = 1\<emdash>20, expect = none]
by auto

lemma "(a\<Colon>'a\<Rightarrow>'b, a) \<in> Id\<^sup>*"
nitpick [card = 1\<emdash>3, expect = none]
by auto

lemma "(a\<Colon>'a\<times>'a, a) \<in> Id\<^sup>* \<union> {(a, b)}\<^sup>*"
nitpick [card = 1\<emdash>4, expect = none]
by auto

lemma "(a, a) \<in> Id"
nitpick [card = 1\<emdash>50, expect = none]
by (auto simp: Id_def)

lemma "((a\<Colon>'a, b\<Colon>'a), (a, b)) \<in> Id"
nitpick [card = 1\<emdash>10, expect = none]
by (auto simp: Id_def)

lemma "(x\<Colon>'a\<times>'a) \<in> UNIV"
nitpick [card = 1\<emdash>50, expect = none]
sorry

lemma "{} = A - A"
nitpick [card = 1\<emdash>100, expect = none]
by auto

lemma "g = Let (A \<or> B)"
nitpick [card = 1, expect = none]
nitpick [card = 12, expect = genuine]
oops

lemma "(let a_or_b = A \<or> B in a_or_b \<or> \<not> a_or_b)"
nitpick [expect = none]
by auto

lemma "A \<subseteq> B"
nitpick [card = 100, expect = genuine]
oops

lemma "A = {b}"
nitpick [card = 100, expect = genuine]
oops

lemma "{a, b} = {b}"
nitpick [card = 50, expect = genuine]
oops

lemma "(a\<Colon>'a\<times>'a, a\<Colon>'a\<times>'a) \<in> R"
nitpick [card = 1, expect = genuine]
nitpick [card = 10, expect = genuine]
nitpick [card = 5, dont_box, expect = genuine]
oops

lemma "f (g\<Colon>'a\<Rightarrow>'a) = x"
nitpick [card = 3, dont_box, expect = genuine]
nitpick [card = 8, expect = genuine]
oops

lemma "f (a, b) = x"
nitpick [card = 10, expect = genuine]
oops

lemma "f (a, a) = f (c, d)"
nitpick [card = 10, expect = genuine]
oops

lemma "(x\<Colon>'a) = (\<lambda>a. \<lambda>b. \<lambda>c. if c then a else b) x x True"
nitpick [card = 1\<emdash>10, expect = none]
by auto

lemma "\<exists>F. F a b = G a b"
nitpick [card = 2, expect = none]
by auto

lemma "f = split"
nitpick [card = 2, expect = genuine]
oops

lemma "(A\<Colon>'a\<times>'a, B\<Colon>'a\<times>'a) \<in> R \<Longrightarrow> (A, B) \<in> R"
nitpick [card = 15, expect = none]
by auto

lemma "(A, B) \<in> R \<or> (\<exists>C. (A, C) \<in> R \<and> (C, B) \<in> R) \<Longrightarrow> 
       A = B \<or> (A, B) \<in> R \<or> (\<exists>C. (A, C) \<in> R \<and> (C, B) \<in> R)"
nitpick [card = 1\<emdash>25, expect = none]
by auto

lemma "f = (\<lambda>x\<Colon>'a\<times>'b. x)"
nitpick [card = 8, expect = genuine]
oops

subsection {* Quantifiers *}

lemma "x = y"
nitpick [card 'a = 1, expect = none]
nitpick [card 'a = 100, expect = genuine]
oops

lemma "\<forall>x. x = y"
nitpick [card 'a = 1, expect = none]
nitpick [card 'a = 100, expect = genuine]
oops

lemma "\<forall>x\<Colon>'a \<Rightarrow> bool. x = y"
nitpick [card 'a = 1, expect = genuine]
nitpick [card 'a = 100, expect = genuine]
oops

lemma "\<exists>x\<Colon>'a \<Rightarrow> bool. x = y"
nitpick [card 'a = 1\<emdash>15, expect = none]
by auto

lemma "\<exists>x y\<Colon>'a \<Rightarrow> bool. x = y"
nitpick [card = 1\<emdash>15, expect = none]
by auto

lemma "\<forall>x. \<exists>y. f x y = f x (g x)"
nitpick [card = 1\<emdash>4, expect = none]
by auto

lemma "\<forall>u. \<exists>v. \<forall>w. \<exists>x. f u v w x = f u (g u) w (h u w)"
nitpick [card = 1\<emdash>4, expect = none]
by auto

lemma "\<forall>u. \<exists>v. \<forall>w. \<exists>x. f u v w x = f u (g u w) w (h u)"
nitpick [card = 3, expect = genuine]
oops

lemma "\<forall>u. \<exists>v. \<forall>w. \<exists>x. \<forall>y. \<exists>z.
       f u v w x y z = f u (g u) w (h u w) y (k u w y)"
nitpick [card = 1\<emdash>2, expect = none]
sorry

lemma "\<forall>u. \<exists>v. \<forall>w. \<exists>x. \<forall>y. \<exists>z.
       f u v w x y z = f u (g u) w (h u w y) y (k u w y)"
nitpick [card = 1\<emdash>2, expect = genuine]
oops

lemma "\<forall>u. \<exists>v. \<forall>w. \<exists>x. \<forall>y. \<exists>z.
       f u v w x y z = f u (g u w) w (h u w) y (k u w y)"
nitpick [card = 1\<emdash>2, expect = genuine]
oops

lemma "\<forall>u\<Colon>'a \<times> 'b. \<exists>v\<Colon>'c. \<forall>w\<Colon>'d. \<exists>x\<Colon>'e \<times> 'f.
       f u v w x = f u (g u) w (h u w)"
nitpick [card = 1\<emdash>2, expect = none]
sorry

lemma "\<forall>u\<Colon>'a \<times> 'b. \<exists>v\<Colon>'c. \<forall>w\<Colon>'d. \<exists>x\<Colon>'e \<times> 'f.
       f u v w x = f u (g u w) w (h u)"
nitpick [card = 1\<emdash>2, dont_box, expect = genuine]
oops

lemma "\<forall>u\<Colon>'a \<Rightarrow> 'b. \<exists>v\<Colon>'c. \<forall>w\<Colon>'d. \<exists>x\<Colon>'e \<Rightarrow> 'f.
       f u v w x = f u (g u) w (h u w)"
nitpick [card = 1\<emdash>2, dont_box, expect = none]
sorry

lemma "\<forall>u\<Colon>'a \<Rightarrow> 'b. \<exists>v\<Colon>'c. \<forall>w\<Colon>'d. \<exists>x\<Colon>'e \<Rightarrow> 'f.
       f u v w x = f u (g u w) w (h u)"
nitpick [card = 1\<emdash>2, dont_box, expect = genuine]
oops

lemma "\<forall>x. if (\<forall>y. x = y) then False else True"
nitpick [card = 1, expect = genuine]
nitpick [card = 2\<emdash>5, expect = none]
oops

lemma "\<forall>x\<Colon>'a\<times>'b. if (\<forall>y. x = y) then False else True"
nitpick [card = 1, expect = genuine]
nitpick [card = 2, expect = none]
oops

lemma "\<forall>x. if (\<exists>y. x = y) then True else False"
nitpick [expect = none]
sorry

lemma "(\<exists>x\<Colon>'a. \<forall>y. P x y) \<or> (\<exists>x\<Colon>'a \<times> 'a. \<forall>y. P y x)"
nitpick [card 'a = 1, expect = genuine]
oops

lemma "\<exists>x. if x = y then (\<forall>y. y = x \<or> y \<noteq> x)
           else (\<forall>y. y = (x, x) \<or> y \<noteq> (x, x))"
nitpick [expect = none]
by auto

lemma "\<exists>x. if x = y then (\<exists>y. y = x \<or> y \<noteq> x)
           else (\<exists>y. y = (x, x) \<or> y \<noteq> (x, x))"
nitpick [expect = none]
by auto

lemma "let x = (\<forall>x. P x) in if x then x else \<not> x"
nitpick [expect = none]
by auto

lemma "let x = (\<forall>x\<Colon>'a \<times> 'b. P x) in if x then x else \<not> x"
nitpick [expect = none]
by auto

subsection {* Schematic Variables *}

schematic_lemma "x = ?x"
nitpick [expect = none]
by auto

schematic_lemma "\<forall>x. x = ?x"
nitpick [expect = genuine]
oops

schematic_lemma "\<exists>x. x = ?x"
nitpick [expect = none]
by auto

schematic_lemma "\<exists>x\<Colon>'a \<Rightarrow> 'b. x = ?x"
nitpick [expect = none]
by auto

schematic_lemma "\<forall>x. ?x = ?y"
nitpick [expect = none]
by auto

schematic_lemma "\<exists>x. ?x = ?y"
nitpick [expect = none]
by auto

subsection {* Known Constants *}

lemma "x \<equiv> all \<Longrightarrow> False"
nitpick [card = 1, expect = genuine]
nitpick [card = 1, box "('a \<Rightarrow> prop) \<Rightarrow> prop", expect = genuine]
nitpick [card = 6, expect = genuine]
oops

lemma "\<And>x. f x y = f x y"
nitpick [expect = none]
oops

lemma "\<And>x. f x y = f y x"
nitpick [expect = genuine]
oops

lemma "all (\<lambda>x. Trueprop (f x y = f x y)) \<equiv> Trueprop True"
nitpick [expect = none]
by auto

lemma "all (\<lambda>x. Trueprop (f x y = f x y)) \<equiv> Trueprop False"
nitpick [expect = genuine]
oops

lemma "I = (\<lambda>x. x) \<Longrightarrow> all P \<equiv> all (\<lambda>x. P (I x))"
nitpick [expect = none]
by auto

lemma "x \<equiv> (op \<equiv>) \<Longrightarrow> False"
nitpick [card = 1, expect = genuine]
oops

lemma "P x \<equiv> P x"
nitpick [card = 1\<emdash>10, expect = none]
by auto

lemma "P x \<equiv> Q x \<Longrightarrow> P x = Q x"
nitpick [card = 1\<emdash>10, expect = none]
by auto

lemma "P x = Q x \<Longrightarrow> P x \<equiv> Q x"
nitpick [card = 1\<emdash>10, expect = none]
by auto

lemma "x \<equiv> (op \<Longrightarrow>) \<Longrightarrow> False"
nitpick [expect = genuine]
oops

lemma "I \<equiv> (\<lambda>x. x) \<Longrightarrow> (op \<Longrightarrow> x) \<equiv> (\<lambda>y. (op \<Longrightarrow> x (I y)))"
nitpick [expect = none]
by auto

lemma "P x \<Longrightarrow> P x"
nitpick [card = 1\<emdash>10, expect = none]
by auto

lemma "True \<Longrightarrow> True" "False \<Longrightarrow> True" "False \<Longrightarrow> False"
nitpick [expect = none]
by auto

lemma "True \<Longrightarrow> False"
nitpick [expect = genuine]
oops

lemma "x = Not"
nitpick [expect = genuine]
oops

lemma "I = (\<lambda>x. x) \<Longrightarrow> Not = (\<lambda>x. Not (I x))"
nitpick [expect = none]
by auto

lemma "x = True"
nitpick [expect = genuine]
oops

lemma "x = False"
nitpick [expect = genuine]
oops

lemma "x = undefined"
nitpick [expect = genuine]
oops

lemma "(False, ()) = undefined \<Longrightarrow> ((), False) = undefined"
nitpick [expect = genuine]
oops

lemma "undefined = undefined"
nitpick [expect = none]
by auto

lemma "f undefined = f undefined"
nitpick [expect = none]
by auto

lemma "f undefined = g undefined"
nitpick [card = 33, expect = genuine]
oops

lemma "\<exists>!x. x = undefined"
nitpick [card = 15, expect = none]
by auto

lemma "x = All \<Longrightarrow> False"
nitpick [card = 1, dont_box, expect = genuine]
oops

lemma "\<forall>x. f x y = f x y"
nitpick [expect = none]
oops

lemma "\<forall>x. f x y = f y x"
nitpick [expect = genuine]
oops

lemma "All (\<lambda>x. f x y = f x y) = True"
nitpick [expect = none]
by auto

lemma "All (\<lambda>x. f x y = f x y) = False"
nitpick [expect = genuine]
oops

lemma "x = Ex \<Longrightarrow> False"
nitpick [card = 1, dont_box, expect = genuine]
oops

lemma "\<exists>x. f x y = f x y"
nitpick [expect = none]
oops

lemma "\<exists>x. f x y = f y x"
nitpick [expect = none]
oops

lemma "Ex (\<lambda>x. f x y = f x y) = True"
nitpick [expect = none]
by auto

lemma "Ex (\<lambda>x. f x y = f y x) = True"
nitpick [expect = none]
by auto

lemma "Ex (\<lambda>x. f x y = f x y) = False"
nitpick [expect = genuine]
oops

lemma "Ex (\<lambda>x. f x y \<noteq> f x y) = False"
nitpick [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> Ex P = Ex (\<lambda>x. P (I x))"
nitpick [expect = none]
by auto

lemma "x = y \<Longrightarrow> y = x"
nitpick [expect = none]
by auto

lemma "x = y \<Longrightarrow> f x = f y"
nitpick [expect = none]
by auto

lemma "x = y \<and> y = z \<Longrightarrow> x = z"
nitpick [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> (op \<and>) = (\<lambda>x. op \<and> (I x))"
      "I = (\<lambda>x. x) \<Longrightarrow> (op \<and>) = (\<lambda>x y. x \<and> (I y))"
nitpick [expect = none]
by auto

lemma "(a \<and> b) = (\<not> (\<not> a \<or> \<not> b))"
nitpick [expect = none]
by auto

lemma "a \<and> b \<Longrightarrow> a" "a \<and> b \<Longrightarrow> b"
nitpick [expect = none]
by auto

lemma "(op \<longrightarrow>) = (\<lambda>x. op\<longrightarrow> x)" "(op\<longrightarrow> ) = (\<lambda>x y. x \<longrightarrow> y)"
nitpick [expect = none]
by auto

lemma "((if a then b else c) = d) = ((a \<longrightarrow> (b = d)) \<and> (\<not> a \<longrightarrow> (c = d)))"
nitpick [expect = none]
by auto

lemma "(if a then b else c) = (THE d. (a \<longrightarrow> (d = b)) \<and> (\<not> a \<longrightarrow> (d = c)))"
nitpick [expect = none]
by auto

lemma "fst (x, y) = x"
nitpick [expect = none]
by (simp add: fst_def)

lemma "snd (x, y) = y"
nitpick [expect = none]
by (simp add: snd_def)

lemma "fst (x\<Colon>'a\<Rightarrow>'b, y) = x"
nitpick [expect = none]
by (simp add: fst_def)

lemma "snd (x\<Colon>'a\<Rightarrow>'b, y) = y"
nitpick [expect = none]
by (simp add: snd_def)

lemma "fst (x, y\<Colon>'a\<Rightarrow>'b) = x"
nitpick [expect = none]
by (simp add: fst_def)

lemma "snd (x, y\<Colon>'a\<Rightarrow>'b) = y"
nitpick [expect = none]
by (simp add: snd_def)

lemma "fst (x\<Colon>'a\<times>'b, y) = x"
nitpick [expect = none]
by (simp add: fst_def)

lemma "snd (x\<Colon>'a\<times>'b, y) = y"
nitpick [expect = none]
by (simp add: snd_def)

lemma "fst (x, y\<Colon>'a\<times>'b) = x"
nitpick [expect = none]
by (simp add: fst_def)

lemma "snd (x, y\<Colon>'a\<times>'b) = y"
nitpick [expect = none]
by (simp add: snd_def)

lemma "I = (\<lambda>x. x) \<Longrightarrow> fst = (\<lambda>x. fst (I x))"
nitpick [expect = none]
by auto

lemma "fst (x, y) = snd (y, x)"
nitpick [expect = none]
by auto

lemma "(x, x) \<in> Id"
nitpick [expect = none]
by auto

lemma "(x, y) \<in> Id \<Longrightarrow> x = y"
nitpick [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> Id = {x. I x \<in> Id}"
nitpick [expect = none]
by auto

lemma "{} = {x. False}"
nitpick [expect = none]
by (metis empty_def)

lemma "x \<in> {}"
nitpick [expect = genuine]
oops

lemma "{a, b} = {b}"
nitpick [expect = genuine]
oops

lemma "{a, b} \<noteq> {b}"
nitpick [expect = genuine]
oops

lemma "{a} = {b}"
nitpick [expect = genuine]
oops

lemma "{a} \<noteq> {b}"
nitpick [expect = genuine]
oops

lemma "{a, b, c} = {c, b, a}"
nitpick [expect = none]
by auto

lemma "UNIV = {x. True}"
nitpick [expect = none]
by (simp only: UNIV_def)

lemma "x \<in> UNIV \<longleftrightarrow> True"
nitpick [expect = none]
by (simp only: UNIV_def mem_Collect_eq)

lemma "x \<notin> UNIV"
nitpick [expect = genuine]
oops

lemma "I = (\<lambda>x. x) \<Longrightarrow> op \<in> = (\<lambda>x. (op \<in> (I x)))"
nitpick [expect = none]
apply (rule ext)
apply (rule ext)
by simp

lemma "insert = (\<lambda>x y. insert x (y \<union> y))"
nitpick [expect = none]
by simp

lemma "I = (\<lambda>x. x) \<Longrightarrow> trancl = (\<lambda>x. trancl (I x))"
nitpick [card = 1\<emdash>2, expect = none]
by auto

lemma "rtrancl = (\<lambda>x. rtrancl x \<union> {(y, y)})"
nitpick [card = 1\<emdash>3, expect = none]
apply (rule ext)
by auto

lemma "(x, x) \<in> rtrancl {(y, y)}"
nitpick [expect = none]
by auto

lemma "((x, x), (x, x)) \<in> rtrancl {}"
nitpick [card = 1\<emdash>5, expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> op \<union> = (\<lambda>x. op \<union> (I x))"
nitpick [card = 1\<emdash>5, expect = none]
by auto

lemma "a \<in> A \<Longrightarrow> a \<in> (A \<union> B)" "b \<in> B \<Longrightarrow> b \<in> (A \<union> B)"
nitpick [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> op \<inter> = (\<lambda>x. op \<inter> (I x))"
nitpick [card = 1\<emdash>5, expect = none]
by auto

lemma "a \<notin> A \<Longrightarrow> a \<notin> (A \<inter> B)" "b \<notin> B \<Longrightarrow> b \<notin> (A \<inter> B)"
nitpick [card = 1\<emdash>5, expect = none]
by auto

lemma "x \<in> ((A\<Colon>'a set) - B) \<longleftrightarrow> x \<in> A \<and> x \<notin> B"
nitpick [card = 1\<emdash>5, expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> op \<subset> = (\<lambda>x. op \<subset> (I x))"
nitpick [card = 1\<emdash>5, expect = none]
by auto

lemma "A \<subset> B \<Longrightarrow> (\<forall>a \<in> A. a \<in> B) \<and> (\<exists>b \<in> B. b \<notin> A)"
nitpick [card = 1\<emdash>5, expect = none]
by auto

lemma "A \<subseteq> B \<Longrightarrow> \<forall>a \<in> A. a \<in> B"
nitpick [card = 1\<emdash>5, expect = none]
by auto

lemma "A \<subseteq> B \<Longrightarrow> A \<subset> B"
nitpick [card = 5, expect = genuine]
oops

lemma "A \<subset> B \<Longrightarrow> A \<subseteq> B"
nitpick [expect = none]
by auto

lemma "I = (\<lambda>x\<Colon>'a set. x) \<Longrightarrow> uminus = (\<lambda>x. uminus (I x))"
nitpick [card = 1\<emdash>7, expect = none]
by auto

lemma "A \<union> - A = UNIV"
nitpick [expect = none]
by auto

lemma "A \<inter> - A = {}"
nitpick [expect = none]
by auto

lemma "A = -(A\<Colon>'a set)"
nitpick [card 'a = 10, expect = genuine]
oops

lemma "finite A"
nitpick [expect = none]
oops

lemma "finite A \<Longrightarrow> finite B"
nitpick [expect = none]
oops

lemma "All finite"
nitpick [expect = none]
oops

subsection {* The and Eps *}

lemma "x = The"
nitpick [card = 5, expect = genuine]
oops

lemma "\<exists>x. x = The"
nitpick [card = 1\<emdash>3]
by auto

lemma "P x \<and> (\<forall>y. P y \<longrightarrow> y = x) \<longrightarrow> The P = x"
nitpick [expect = none]
by auto

lemma "P x \<and> P y \<and> x \<noteq> y \<longrightarrow> The P = z"
nitpick [expect = genuine]
oops

lemma "P x \<and> P y \<and> x \<noteq> y \<longrightarrow> The P = x \<or> The P = y"
nitpick [card = 2, expect = none]
nitpick [card = 3\<emdash>5, expect = genuine]
oops

lemma "P x \<Longrightarrow> P (The P)"
nitpick [card = 1\<emdash>2, expect = none]
nitpick [card = 8, expect = genuine]
oops

lemma "(\<forall>x. \<not> P x) \<longrightarrow> The P = y"
nitpick [expect = genuine]
oops

lemma "I = (\<lambda>x. x) \<Longrightarrow> The = (\<lambda>x. The (I x))"
nitpick [card = 1\<emdash>5, expect = none]
by auto

lemma "x = Eps"
nitpick [card = 5, expect = genuine]
oops

lemma "\<exists>x. x = Eps"
nitpick [card = 1\<emdash>3, expect = none]
by auto

lemma "P x \<and> (\<forall>y. P y \<longrightarrow> y = x) \<longrightarrow> Eps P = x"
nitpick [expect = none]
by auto

lemma "P x \<and> P y \<and> x \<noteq> y \<longrightarrow> Eps P = z"
nitpick [expect = genuine]
apply auto
oops

lemma "P x \<Longrightarrow> P (Eps P)"
nitpick [card = 1\<emdash>8, expect = none]
by (metis exE_some)

lemma "\<forall>x. \<not> P x \<longrightarrow> Eps P = y"
nitpick [expect = genuine]
oops

lemma "P (Eps P)"
nitpick [expect = genuine]
oops

lemma "Eps (\<lambda>x. x \<in> P) \<in> (P\<Colon>nat set)"
nitpick [expect = genuine]
oops

lemma "\<not> P (Eps P)"
nitpick [expect = genuine]
oops

lemma "\<not> (P \<Colon> nat \<Rightarrow> bool) (Eps P)"
nitpick [expect = genuine]
oops

lemma "P \<noteq> bot \<Longrightarrow> P (Eps P)"
nitpick [expect = none]
sorry

lemma "(P \<Colon> nat \<Rightarrow> bool) \<noteq> bot \<Longrightarrow> P (Eps P)"
nitpick [expect = none]
sorry

lemma "P (The P)"
nitpick [expect = genuine]
oops

lemma "(P \<Colon> nat \<Rightarrow> bool) (The P)"
nitpick [expect = genuine]
oops

lemma "\<not> P (The P)"
nitpick [expect = genuine]
oops

lemma "\<not> (P \<Colon> nat \<Rightarrow> bool) (The P)"
nitpick [expect = genuine]
oops

lemma "The P \<noteq> x"
nitpick [expect = genuine]
oops

lemma "The P \<noteq> (x\<Colon>nat)"
nitpick [expect = genuine]
oops

lemma "P x \<Longrightarrow> P (The P)"
nitpick [expect = genuine]
oops

lemma "P (x\<Colon>nat) \<Longrightarrow> P (The P)"
nitpick [expect = genuine]
oops

lemma "P = {x} \<Longrightarrow> (THE x. x \<in> P) \<in> P"
nitpick [expect = none]
oops

lemma "P = {x\<Colon>nat} \<Longrightarrow> (THE x. x \<in> P) \<in> P"
nitpick [expect = none]
oops

consts Q :: 'a

lemma "Q (Eps Q)"
nitpick [expect = genuine]
oops

lemma "(Q \<Colon> nat \<Rightarrow> bool) (Eps Q)"
nitpick [expect = none] (* unfortunate *)
oops

lemma "\<not> (Q \<Colon> nat \<Rightarrow> bool) (Eps Q)"
nitpick [expect = genuine]
oops

lemma "\<not> (Q \<Colon> nat \<Rightarrow> bool) (Eps Q)"
nitpick [expect = genuine]
oops

lemma "(Q \<Colon> 'a \<Rightarrow> bool) \<noteq> bot \<Longrightarrow> Q (Eps Q)"
nitpick [expect = none]
sorry

lemma "(Q \<Colon> nat \<Rightarrow> bool) \<noteq> top \<Longrightarrow> Q (Eps Q)"
nitpick [expect = none]
sorry

lemma "Q (The Q)"
nitpick [expect = genuine]
oops

lemma "(Q \<Colon> nat \<Rightarrow> bool) (The Q)"
nitpick [expect = genuine]
oops

lemma "\<not> Q (The Q)"
nitpick [expect = genuine]
oops

lemma "\<not> (Q \<Colon> nat \<Rightarrow> bool) (The Q)"
nitpick [expect = genuine]
oops

lemma "The Q \<noteq> x"
nitpick [expect = genuine]
oops

lemma "The Q \<noteq> (x\<Colon>nat)"
nitpick [expect = genuine]
oops

lemma "Q x \<Longrightarrow> Q (The Q)"
nitpick [expect = genuine]
oops

lemma "Q (x\<Colon>nat) \<Longrightarrow> Q (The Q)"
nitpick [expect = genuine]
oops

lemma "Q = {x\<Colon>'a} \<Longrightarrow> (The Q) \<in> (Q\<Colon>'a set)"
nitpick [expect = none]
sorry

lemma "Q = {x\<Colon>nat} \<Longrightarrow> (The Q) \<in> (Q\<Colon>nat set)"
nitpick [expect = none]
sorry

nitpick_params [max_potential = 1]

lemma "(THE j. j > Suc 2 \<and> j \<le> 3) \<noteq> 0"
nitpick [card nat = 2, expect = potential]
nitpick [card nat = 6, expect = potential] (* unfortunate *)
oops

lemma "(THE j. j > Suc 2 \<and> j \<le> 4) = x \<Longrightarrow> x \<noteq> 0"
nitpick [card nat = 2, expect = potential]
nitpick [card nat = 6, expect = none]
sorry

lemma "(THE j. j > Suc 2 \<and> j \<le> 4) = x \<Longrightarrow> x = 4"
nitpick [card nat = 2, expect = potential]
nitpick [card nat = 6, expect = none]
sorry

lemma "(THE j. j > Suc 2 \<and> j \<le> 5) = x \<Longrightarrow> x = 4"
nitpick [card nat = 6, expect = genuine]
oops

lemma "(THE j. j > Suc 2 \<and> j \<le> 5) = x \<Longrightarrow> x = 4 \<or> x = 5"
nitpick [card nat = 6, expect = genuine]
oops

lemma "(SOME j. j > Suc 2 \<and> j \<le> 3) \<noteq> 0"
nitpick [card nat = 2, expect = potential]
nitpick [card nat = 6, expect = genuine]
oops

lemma "(SOME j. j > Suc 2 \<and> j \<le> 4) = x \<Longrightarrow> x \<noteq> 0"
nitpick [card nat = 2, expect = potential]
nitpick [card nat = 6, expect = none]
oops

lemma "(SOME j. j > Suc 2 \<and> j \<le> 4) = x \<Longrightarrow> x = 4"
nitpick [card nat = 2, expect = potential]
nitpick [card nat = 6, expect = none]
sorry

lemma "(SOME j. j > Suc 2 \<and> j \<le> 5) = x \<Longrightarrow> x = 4"
nitpick [card nat = 6, expect = genuine]
oops

lemma "(SOME j. j > Suc 2 \<and> j \<le> 5) = x \<Longrightarrow> x = 4 \<or> x = 5"
nitpick [card nat = 6, expect = none]
sorry

nitpick_params [max_potential = 0]

subsection {* Destructors and Recursors *}

lemma "(x\<Colon>'a) = (case True of True \<Rightarrow> x | False \<Rightarrow> x)"
nitpick [card = 2, expect = none]
by auto

lemma "bool_rec x y True = x"
nitpick [card = 2, expect = none]
by auto

lemma "bool_rec x y False = y"
nitpick [card = 2, expect = none]
by auto

lemma "(x\<Colon>bool) = bool_rec x x True"
nitpick [card = 2, expect = none]
by auto

lemma "x = (case (x, y) of (x', y') \<Rightarrow> x')"
nitpick [expect = none]
sorry

end
