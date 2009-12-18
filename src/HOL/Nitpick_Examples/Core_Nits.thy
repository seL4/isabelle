(*  Title:      HOL/Nitpick_Examples/Core_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009

Examples featuring Nitpick's functional core.
*)

header {* Examples Featuring Nitpick's Functional Core *}

theory Core_Nits
imports Main
begin

nitpick_params [sat_solver = MiniSatJNI, max_threads = 1, timeout = 60 s]

subsection {* Curry in a Hurry *}

lemma "(\<lambda>f x y. (curry o split) f x y) = (\<lambda>f x y. (\<lambda>x. x) f x y)"
nitpick [card = 1\<midarrow>4, expect = none]
nitpick [card = 100, expect = none, timeout = none]
by auto

lemma "(\<lambda>f p. (split o curry) f p) = (\<lambda>f p. (\<lambda>x. x) f p)"
nitpick [card = 2]
nitpick [card = 1\<midarrow>4, expect = none]
nitpick [card = 10, expect = none]
by auto

lemma "split (curry f) = f"
nitpick [card = 1\<midarrow>4, expect = none]
nitpick [card = 10, expect = none]
nitpick [card = 40, expect = none]
by auto

lemma "curry (split f) = f"
nitpick [card = 1\<midarrow>4, expect = none]
nitpick [card = 40, expect = none]
by auto

lemma "(split o curry) f = f"
nitpick [card = 1\<midarrow>4, expect = none]
nitpick [card = 40, expect = none]
by auto

lemma "(curry o split) f = f"
nitpick [card = 1\<midarrow>4, expect = none]
nitpick [card = 1000, expect = none]
by auto

lemma "(split o curry) f = (\<lambda>x. x) f"
nitpick [card = 1\<midarrow>4, expect = none]
nitpick [card = 40, expect = none]
by auto

lemma "(curry o split) f = (\<lambda>x. x) f"
nitpick [card = 1\<midarrow>4, expect = none]
nitpick [card = 40, expect = none]
by auto

lemma "((split o curry) f) p = ((\<lambda>x. x) f) p"
nitpick [card = 1\<midarrow>4, expect = none]
nitpick [card = 40, expect = none]
by auto

lemma "((curry o split) f) x = ((\<lambda>x. x) f) x"
nitpick [card = 1\<midarrow>4, expect = none]
nitpick [card = 1000, expect = none]
by auto

lemma "((curry o split) f) x y = ((\<lambda>x. x) f) x y"
nitpick [card = 1\<midarrow>4, expect = none]
nitpick [card = 1000, expect = none]
by auto

lemma "split o curry = (\<lambda>x. x)"
nitpick [card = 1\<midarrow>4, expect = none]
nitpick [card = 40, expect = none]
apply (rule ext)+
by auto

lemma "curry o split = (\<lambda>x. x)"
nitpick [card = 1\<midarrow>4, expect = none]
nitpick [card = 100, expect = none]
apply (rule ext)+
by auto

lemma "split (\<lambda>x y. f (x, y)) = f"
nitpick [card = 1\<midarrow>4, expect = none]
nitpick [card = 40, expect = none]
by auto

subsection {* Representations *}

lemma "\<exists>f. f = (\<lambda>x. x) \<and> f y = y"
nitpick [expect = none]
by auto

lemma "(\<exists>g. \<forall>x. g (f x) = x) \<longrightarrow> (\<forall>y. \<exists>x. y = f x)"
nitpick [card 'a = 35, card 'b = 34, expect = genuine]
nitpick [card = 1\<midarrow>15, mono, expect = none]
oops

lemma "\<exists>f. f = (\<lambda>x. x) \<and> f y \<noteq> y"
nitpick [card = 1, expect = genuine]
nitpick [card = 2, expect = genuine]
nitpick [card = 5, expect = genuine]
oops

lemma "P (\<lambda>x. x)"
nitpick [card = 1, expect = genuine]
nitpick [card = 5, expect = genuine]
oops

lemma "{(a\<Colon>'a\<times>'a, b\<Colon>'b)}^-1 = {(b, a)}"
nitpick [card = 1\<midarrow>6, expect = none]
nitpick [card = 20, expect = none]
by auto

lemma "fst (a, b) = a"
nitpick [card = 1\<midarrow>20, expect = none]
by auto

lemma "\<exists>P. P = Id"
nitpick [card = 1\<midarrow>4, expect = none]
by auto

lemma "(a\<Colon>'a\<Rightarrow>'b, a) \<in> Id\<^sup>*"
nitpick [card = 1\<midarrow>3, expect = none]
by auto

lemma "(a\<Colon>'a\<times>'a, a) \<in> Id\<^sup>* \<union> {(a, b)}\<^sup>*"
nitpick [card = 1\<midarrow>6, expect = none]
by auto

lemma "Id (a, a)"
nitpick [card = 1\<midarrow>100, expect = none]
by (auto simp: Id_def Collect_def)

lemma "Id ((a\<Colon>'a, b\<Colon>'a), (a, b))"
nitpick [card = 1\<midarrow>10, expect = none]
by (auto simp: Id_def Collect_def)

lemma "UNIV (x\<Colon>'a\<times>'a)"
nitpick [card = 1\<midarrow>50, expect = none]
sorry

lemma "{} = A - A"
nitpick [card = 1\<midarrow>100, expect = none]
by auto

lemma "g = Let (A \<or> B)"
nitpick [card = 1, expect = none]
nitpick [card = 2, expect = genuine]
nitpick [card = 20, expect = genuine]
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
nitpick [card = 100, expect = genuine]
oops

lemma "(a\<Colon>'a\<times>'a, a\<Colon>'a\<times>'a) \<in> R"
nitpick [card = 1, expect = genuine]
nitpick [card = 2, expect = genuine]
nitpick [card = 4, expect = genuine]
nitpick [card = 20, expect = genuine]
nitpick [card = 10, dont_box, expect = genuine]
oops

lemma "f (g\<Colon>'a\<Rightarrow>'a) = x"
nitpick [card = 3, expect = genuine]
nitpick [card = 3, dont_box, expect = genuine]
nitpick [card = 5, expect = genuine]
nitpick [card = 10, expect = genuine]
oops

lemma "f (a, b) = x"
nitpick [card = 3, expect = genuine]
nitpick [card = 10, expect = genuine]
nitpick [card = 16, expect = genuine]
nitpick [card = 30, expect = genuine]
oops

lemma "f (a, a) = f (c, d)"
nitpick [card = 4, expect = genuine]
nitpick [card = 20, expect = genuine]
oops

lemma "(x\<Colon>'a) = (\<lambda>a. \<lambda>b. \<lambda>c. if c then a else b) x x True"
nitpick [card = 2, expect = none]
by auto

lemma "\<exists>F. F a b = G a b"
nitpick [card = 3, expect = none]
by auto

lemma "f = split"
nitpick [card = 1, expect = none]
nitpick [card = 2, expect = genuine]
oops

lemma "(A\<Colon>'a\<times>'a, B\<Colon>'a\<times>'a) \<in> R \<Longrightarrow> (A, B) \<in> R"
nitpick [card = 20, expect = none]
by auto

lemma "(A, B) \<in> R \<or> (\<exists>C. (A, C) \<in> R \<and> (C, B) \<in> R) \<Longrightarrow> 
       A = B \<or> (A, B) \<in> R \<or> (\<exists>C. (A, C) \<in> R \<and> (C, B) \<in> R)"
nitpick [card = 1\<midarrow>50, expect = none]
by auto

lemma "f = (\<lambda>x\<Colon>'a\<times>'b. x)"
nitpick [card = 3, expect = genuine]
nitpick [card = 4, expect = genuine]
nitpick [card = 8, expect = genuine]
oops

subsection {* Quantifiers *}

lemma "x = y"
nitpick [card 'a = 1, expect = none]
nitpick [card 'a = 2, expect = genuine]
nitpick [card 'a = 100, expect = genuine]
nitpick [card 'a = 1000, expect = genuine]
oops

lemma "\<forall>x. x = y"
nitpick [card 'a = 1, expect = none]
nitpick [card 'a = 2, expect = genuine]
nitpick [card 'a = 100, expect = genuine]
nitpick [card 'a = 1000, expect = genuine]
oops

lemma "\<forall>x\<Colon>'a \<Rightarrow> bool. x = y"
nitpick [card 'a = 1, expect = genuine]
nitpick [card 'a = 2, expect = genuine]
nitpick [card 'a = 100, expect = genuine]
nitpick [card 'a = 1000, expect = genuine]
oops

lemma "\<exists>x\<Colon>'a \<Rightarrow> bool. x = y"
nitpick [card 'a = 1\<midarrow>10, expect = none]
by auto

lemma "\<exists>x y\<Colon>'a \<Rightarrow> bool. x = y"
nitpick [card = 1\<midarrow>40, expect = none]
by auto

lemma "\<forall>x. \<exists>y. f x y = f x (g x)"
nitpick [card = 1\<midarrow>5, expect = none]
by auto

lemma "\<forall>u. \<exists>v. \<forall>w. \<exists>x. f u v w x = f u (g u) w (h u w)"
nitpick [card = 1\<midarrow>5, expect = none]
by auto

lemma "\<forall>u. \<exists>v. \<forall>w. \<exists>x. f u v w x = f u (g u w) w (h u)"
nitpick [card = 1\<midarrow>2, expect = genuine]
nitpick [card = 3, expect = genuine]
oops

lemma "\<forall>u. \<exists>v. \<forall>w. \<exists>x. \<forall>y. \<exists>z.
       f u v w x y z = f u (g u) w (h u w) y (k u w y)"
nitpick [card = 1\<midarrow>2, expect = none]
nitpick [card = 3, expect = none]
nitpick [card = 4, expect = none]
sorry

lemma "\<forall>u. \<exists>v. \<forall>w. \<exists>x. \<forall>y. \<exists>z.
       f u v w x y z = f u (g u) w (h u w y) y (k u w y)"
nitpick [card = 1\<midarrow>2, expect = genuine]
oops

lemma "\<forall>u. \<exists>v. \<forall>w. \<exists>x. \<forall>y. \<exists>z.
       f u v w x y z = f u (g u w) w (h u w) y (k u w y)"
nitpick [card = 1\<midarrow>2, expect = genuine]
oops

lemma "\<forall>u\<Colon>'a \<times> 'b. \<exists>v\<Colon>'c. \<forall>w\<Colon>'d. \<exists>x\<Colon>'e \<times> 'f.
       f u v w x = f u (g u) w (h u w)"
nitpick [card = 1\<midarrow>2, expect = none]
sorry

lemma "\<forall>u\<Colon>'a \<times> 'b. \<exists>v\<Colon>'c. \<forall>w\<Colon>'d. \<exists>x\<Colon>'e \<times> 'f.
       f u v w x = f u (g u w) w (h u)"
nitpick [card = 1\<midarrow>2, dont_box, expect = genuine]
oops

lemma "\<forall>u\<Colon>'a \<Rightarrow> 'b. \<exists>v\<Colon>'c. \<forall>w\<Colon>'d. \<exists>x\<Colon>'e \<Rightarrow> 'f.
       f u v w x = f u (g u) w (h u w)"
nitpick [card = 1\<midarrow>2, dont_box, expect = none]
sorry

lemma "\<forall>u\<Colon>'a \<Rightarrow> 'b. \<exists>v\<Colon>'c. \<forall>w\<Colon>'d. \<exists>x\<Colon>'e \<Rightarrow> 'f.
       f u v w x = f u (g u w) w (h u)"
nitpick [card = 1\<midarrow>2, dont_box, expect = genuine]
oops

lemma "\<forall>x. if (\<forall>y. x = y) then False else True"
nitpick [card = 1, expect = genuine]
nitpick [card = 2\<midarrow>5, expect = none]
oops

lemma "\<forall>x\<Colon>'a\<times>'b. if (\<forall>y. x = y) then False else True"
nitpick [card = 1, expect = genuine]
nitpick [card = 2, expect = none]
oops

lemma "\<forall>x. if (\<exists>y. x = y) then True else False"
nitpick [expect = none]
sorry

lemma "\<forall>x\<Colon>'a\<times>'b. if (\<exists>y. x = y) then True else False"
nitpick [expect = none]
sorry

lemma "(\<not> (\<exists>x. P x)) \<longleftrightarrow> (\<forall>x. \<not> P x)"
nitpick [expect = none]
by auto

lemma "(\<not> \<not> (\<exists>x. P x)) \<longleftrightarrow> (\<not> (\<forall>x. \<not> P x))"
nitpick [expect = none]
by auto

lemma "(\<exists>x\<Colon>'a. \<forall>y. P x y) \<or> (\<exists>x\<Colon>'a \<times> 'a. \<forall>y. P y x)"
nitpick [card 'a = 1, expect = genuine]
nitpick [card 'a = 2, expect = genuine]
nitpick [card 'a = 3, expect = genuine]
nitpick [card 'a = 4, expect = genuine]
nitpick [card 'a = 5, expect = genuine]
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

lemma "x = ?x"
nitpick [expect = none]
by auto

lemma "\<forall>x. x = ?x"
nitpick [expect = genuine]
oops

lemma "\<exists>x. x = ?x"
nitpick [expect = none]
by auto

lemma "\<exists>x\<Colon>'a \<Rightarrow> 'b. x = ?x"
nitpick [expect = none]
by auto

lemma "\<forall>x. ?x = ?y"
nitpick [expect = none]
by auto

lemma "\<exists>x. ?x = ?y"
nitpick [expect = none]
by auto

subsection {* Known Constants *}

lemma "x \<equiv> all \<Longrightarrow> False"
nitpick [card = 1, expect = genuine]
nitpick [card = 1, box "('a \<Rightarrow> prop) \<Rightarrow> prop", expect = genuine]
nitpick [card = 2, expect = genuine]
nitpick [card = 8, expect = genuine]
nitpick [card = 10, expect = unknown]
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
nitpick [card = 2, expect = genuine]
nitpick [card = 3, expect = genuine]
nitpick [card = 4, expect = genuine]
nitpick [card = 5, expect = genuine]
nitpick [card = 100, expect = genuine]
oops

lemma "I = (\<lambda>x. x) \<Longrightarrow> (op \<equiv> x) \<equiv> (\<lambda>y. (x \<equiv> I y))"
nitpick [expect = none]
by auto

lemma "P x \<equiv> P x"
nitpick [card = 1\<midarrow>10, expect = none]
by auto

lemma "P x \<equiv> Q x \<Longrightarrow> P x = Q x"
nitpick [card = 1\<midarrow>10, expect = none]
by auto

lemma "P x = Q x \<Longrightarrow> P x \<equiv> Q x"
nitpick [card = 1\<midarrow>10, expect = none]
by auto

lemma "x \<equiv> (op \<Longrightarrow>) \<Longrightarrow> False"
nitpick [expect = genuine]
oops

lemma "I \<equiv> (\<lambda>x. x) \<Longrightarrow> (op \<Longrightarrow> x) \<equiv> (\<lambda>y. (op \<Longrightarrow> x (I y)))"
nitpick [expect = none]
by auto

lemma "P x \<Longrightarrow> P x"
nitpick [card = 1\<midarrow>10, expect = none]
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
nitpick [card = 30, expect = none]
by auto

lemma "x = All \<Longrightarrow> False"
nitpick [card = 1, dont_box, expect = genuine]
nitpick [card = 2, dont_box, expect = genuine]
nitpick [card = 8, dont_box, expect = genuine]
nitpick [card = 10, dont_box, expect = unknown]
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

lemma "I = (\<lambda>x. x) \<Longrightarrow> All P = All (\<lambda>x. P (I x))"
nitpick [expect = none]
by auto

lemma "x = Ex \<Longrightarrow> False"
nitpick [card = 1, dont_box, expect = genuine]
nitpick [card = 2, dont_box, expect = genuine]
nitpick [card = 8, dont_box, expect = genuine]
nitpick [card = 10, dont_box, expect = unknown]
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

lemma "Ex (\<lambda>x. f x y = f y x) = False"
nitpick [expect = genuine]
oops

lemma "Ex (\<lambda>x. f x y \<noteq> f x y) = False"
nitpick [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> Ex P = Ex (\<lambda>x. P (I x))"
nitpick [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> (op =) = (\<lambda>x. (op= (I x)))"
      "I = (\<lambda>x. x) \<Longrightarrow> (op =) = (\<lambda>x y. x = (I y))"
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

lemma "I = (\<lambda>x. x) \<Longrightarrow> (op &) = (\<lambda>x. op & (I x))"
      "I = (\<lambda>x. x) \<Longrightarrow> (op &) = (\<lambda>x y. x & (I y))"
nitpick [expect = none]
by auto

lemma "(a \<and> b) = (\<not> (\<not> a \<or> \<not> b))"
nitpick [expect = none]
by auto

lemma "a \<and> b \<Longrightarrow> a" "a \<and> b \<Longrightarrow> b"
nitpick [expect = none]
by auto

lemma "\<not> a \<Longrightarrow> \<not> (a \<and> b)" "\<not> b \<Longrightarrow> \<not> (a \<and> b)"
nitpick [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> (op \<or>) = (\<lambda>x. op \<or> (I x))"
      "I = (\<lambda>x. x) \<Longrightarrow> (op \<or>) = (\<lambda>x y. x \<or> (I y))"
nitpick [expect = none]
by auto

lemma "a \<Longrightarrow> a \<or> b" "b \<Longrightarrow> a \<or> b"
nitpick [expect = none]
by auto

lemma "\<not> (a \<or> b) \<Longrightarrow> \<not> a" "\<not> (a \<or> b) \<Longrightarrow> \<not> b"
nitpick [expect = none]
by auto

lemma "(op \<longrightarrow>) = (\<lambda>x. op\<longrightarrow> x)" "(op\<longrightarrow> ) = (\<lambda>x y. x \<longrightarrow> y)"
nitpick [expect = none]
by auto

lemma "\<not>a \<Longrightarrow> a \<longrightarrow> b" "b \<Longrightarrow> a \<longrightarrow> b"
nitpick [expect = none]
by auto

lemma "\<lbrakk>a; \<not> b\<rbrakk> \<Longrightarrow> \<not> (a \<longrightarrow> b)"
nitpick [expect = none]
by auto

lemma "((if a then b else c) = d) = ((a \<longrightarrow> (b = d)) \<and> (\<not> a \<longrightarrow> (c = d)))"
nitpick [expect = none]
by auto

lemma "(if a then b else c) = (THE d. (a \<longrightarrow> (d = b)) \<and> (\<not> a \<longrightarrow> (d = c)))"
nitpick [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> If = (\<lambda>x. If (I x))"
      "J = (\<lambda>x. x) \<Longrightarrow> If = (\<lambda>x y. If x (J y))"
      "K = (\<lambda>x. x) \<Longrightarrow> If = (\<lambda>x y z. If x y (K z))"
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

lemma "fst p = (THE a. \<exists>b. p = Pair a b)"
nitpick [expect = none]
by (simp add: fst_def)

lemma "snd p = (THE b. \<exists>a. p = Pair a b)"
nitpick [expect = none]
by (simp add: snd_def)

lemma "I = (\<lambda>x. x) \<Longrightarrow> fst = (\<lambda>x. fst (I x))"
nitpick [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> snd = (\<lambda>x. snd (I x))"
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

lemma "I = (\<lambda>x. x) \<Longrightarrow> Id = (\<lambda>x. Id (I x))"
nitpick [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> curry Id = (\<lambda>x y. Id (x, I y))"
nitpick [expect = none]
by (simp add: curry_def)

lemma "{} = (\<lambda>x. False)"
nitpick [expect = none]
by (metis Collect_def empty_def)

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

lemma "UNIV = (\<lambda>x. True)"
nitpick [expect = none]
by (simp only: UNIV_def Collect_def)

lemma "UNIV x = True"
nitpick [expect = none]
by (simp only: UNIV_def Collect_def)

lemma "x \<notin> UNIV"
nitpick [expect = genuine]
oops

lemma "op \<in> = (\<lambda>x P. P x)"
nitpick [expect = none]
apply (rule ext)
apply (rule ext)
by (simp add: mem_def)

lemma "I = (\<lambda>x. x) \<Longrightarrow> op \<in> = (\<lambda>x. (op \<in> (I x)))"
nitpick [expect = none]
apply (rule ext)
apply (rule ext)
by (simp add: mem_def)

lemma "P x = (x \<in> P)"
nitpick [expect = none]
by (simp add: mem_def)

lemma "I = (\<lambda>x. x) \<Longrightarrow> insert = (\<lambda>x. insert (I x))"
nitpick [expect = none]
by simp

lemma "insert = (\<lambda>x y. insert x (y \<union> y))"
nitpick [expect = none]
by simp

lemma "I = (\<lambda>x. x) \<Longrightarrow> trancl = (\<lambda>x. trancl (I x))"
nitpick [card = 1\<midarrow>2, expect = none]
by auto

lemma "rtrancl = (\<lambda>x. rtrancl x \<union> {(y, y)})"
nitpick [card = 1\<midarrow>3, expect = none]
apply (rule ext)
by auto

lemma "(x, x) \<in> rtrancl {(y, y)}"
nitpick [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> rtrancl = (\<lambda>x. rtrancl (I x))"
nitpick [card = 1\<midarrow>2, expect = none]
by auto

lemma "((x, x), (x, x)) \<in> rtrancl {}"
nitpick [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> op \<union> = (\<lambda>x. op \<union> (I x))"
nitpick [card = 1\<midarrow>5, expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> op \<union> = (\<lambda>x y. op \<union> x (I y))"
nitpick [card = 1\<midarrow>5, expect = none]
by auto

lemma "a \<in> A \<Longrightarrow> a \<in> (A \<union> B)" "b \<in> B \<Longrightarrow> b \<in> (A \<union> B)"
nitpick [expect = none]
by auto

lemma "a \<in> (A \<union> B) \<Longrightarrow> a \<in> A \<or> a \<in> B"
nitpick [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> op \<inter> = (\<lambda>x. op \<inter> (I x))"
nitpick [card = 1\<midarrow>5, expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> op \<inter> = (\<lambda>x y. op \<inter> x (I y))"
nitpick [card = 1\<midarrow>5, expect = none]
by auto

lemma "a \<notin> A \<Longrightarrow> a \<notin> (A \<inter> B)" "b \<notin> B \<Longrightarrow> b \<notin> (A \<inter> B)"
nitpick [card = 1\<midarrow>5, expect = none]
by auto

lemma "a \<notin> (A \<inter> B) \<Longrightarrow> a \<notin> A \<or> a \<notin> B"
nitpick [expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> op - = (\<lambda>x\<Colon>'a set. op - (I x))"
nitpick [card = 1\<midarrow>5, expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> op - = (\<lambda>x y\<Colon>'a set. op - x (I y))"
nitpick [card = 1\<midarrow>5, expect = none]
by auto

lemma "x \<in> ((A\<Colon>'a set) - B) \<longleftrightarrow> x \<in> A \<and> x \<notin> B"
nitpick [card = 1\<midarrow>5, expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> op \<subset> = (\<lambda>x. op \<subset> (I x))"
nitpick [card = 1\<midarrow>5, expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> op \<subset> = (\<lambda>x y. op \<subset> x (I y))"
nitpick [card = 1\<midarrow>5, expect = none]
by auto

lemma "A \<subset> B \<Longrightarrow> (\<forall>a \<in> A. a \<in> B) \<and> (\<exists>b \<in> B. b \<notin> A)"
nitpick [card = 1\<midarrow>5, expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> op \<subseteq> = (\<lambda>x. op \<subseteq> (I x))"
nitpick [card = 1\<midarrow>5, expect = none]
by auto

lemma "I = (\<lambda>x. x) \<Longrightarrow> op \<subseteq> = (\<lambda>x y. op \<subseteq> x (I y))"
nitpick [card = 1\<midarrow>5, expect = none]
by auto

lemma "A \<subseteq> B \<Longrightarrow> \<forall>a \<in> A. a \<in> B"
nitpick [card = 1\<midarrow>5, expect = none]
by auto

lemma "A \<subseteq> B \<Longrightarrow> A \<subset> B"
nitpick [card = 5, expect = genuine]
oops

lemma "A \<subset> B \<Longrightarrow> A \<subseteq> B"
nitpick [expect = none]
by auto

lemma "I = (\<lambda>x\<Colon>'a set. x) \<Longrightarrow> uminus = (\<lambda>x. uminus (I x))"
nitpick [card = 1\<midarrow>7, expect = none]
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

lemma "I = (\<lambda>x. x) \<Longrightarrow> finite = (\<lambda>x. finite (I x))"
nitpick [card = 1\<midarrow>7, expect = none]
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
nitpick [card = 1\<midarrow>3]
by auto

lemma "P x \<and> (\<forall>y. P y \<longrightarrow> y = x) \<longrightarrow> The P = x"
nitpick [expect = none]
by auto

lemma "P x \<and> P y \<and> x \<noteq> y \<longrightarrow> The P = z"
nitpick [expect = genuine]
oops

lemma "P x \<and> P y \<and> x \<noteq> y \<longrightarrow> The P = x \<or> The P = y"
nitpick [card = 2, expect = none]
nitpick [card = 3\<midarrow>5, expect = genuine]
oops

lemma "P x \<Longrightarrow> P (The P)"
nitpick [card = 1, expect = none]
nitpick [card = 1\<midarrow>2, expect = none]
nitpick [card = 3\<midarrow>5, expect = genuine]
nitpick [card = 8, expect = genuine]
oops

lemma "(\<forall>x. \<not> P x) \<longrightarrow> The P = y"
nitpick [expect = genuine]
oops

lemma "I = (\<lambda>x. x) \<Longrightarrow> The = (\<lambda>x. The (I x))"
nitpick [card = 1\<midarrow>5, expect = none]
by auto

lemma "x = Eps"
nitpick [card = 5, expect = genuine]
oops

lemma "\<exists>x. x = Eps"
nitpick [card = 1\<midarrow>3, expect = none]
by auto

lemma "P x \<and> (\<forall>y. P y \<longrightarrow> y = x) \<longrightarrow> Eps P = x"
nitpick [expect = none]
by auto

lemma "P x \<and> P y \<and> x \<noteq> y \<longrightarrow> Eps P = z"
nitpick [expect = genuine]
apply auto
oops

lemma "P x \<Longrightarrow> P (Eps P)"
nitpick [card = 1\<midarrow>8, expect = none]
by (metis exE_some)

lemma "\<forall>x. \<not> P x \<longrightarrow> Eps P = y"
nitpick [expect = genuine]
oops

lemma "P (Eps P)"
nitpick [expect = genuine]
oops

lemma "(P\<Colon>nat set) (Eps P)"
nitpick [expect = genuine]
oops

lemma "\<not> P (Eps P)"
nitpick [expect = genuine]
oops

lemma "\<not> (P\<Colon>nat set) (Eps P)"
nitpick [expect = genuine]
oops

lemma "P \<noteq> {} \<Longrightarrow> P (Eps P)"
nitpick [expect = none]
sorry

lemma "(P\<Colon>nat set) \<noteq> {} \<Longrightarrow> P (Eps P)"
nitpick [expect = none]
sorry

lemma "P (The P)"
nitpick [expect = genuine]
oops

lemma "(P\<Colon>nat set) (The P)"
nitpick [expect = genuine]
oops

lemma "\<not> P (The P)"
nitpick [expect = genuine]
oops

lemma "\<not> (P\<Colon>nat set) (The P)"
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

lemma "P = {x} \<Longrightarrow> P (The P)"
nitpick [expect = none]
oops

lemma "P = {x\<Colon>nat} \<Longrightarrow> P (The P)"
nitpick [expect = none]
oops

consts Q :: 'a

lemma "Q (Eps Q)"
nitpick [expect = genuine]
oops

lemma "(Q\<Colon>nat set) (Eps Q)"
nitpick [expect = none]
oops

lemma "\<not> Q (Eps Q)"
nitpick [expect = genuine]
oops

lemma "\<not> (Q\<Colon>nat set) (Eps Q)"
nitpick [expect = genuine]
oops

lemma "(Q\<Colon>'a set) \<noteq> {} \<Longrightarrow> (Q\<Colon>'a set) (Eps Q)"
nitpick [expect = none]
sorry

lemma "(Q\<Colon>nat set) \<noteq> {} \<Longrightarrow> (Q\<Colon>nat set) (Eps Q)"
nitpick [expect = none]
sorry

lemma "Q (The Q)"
nitpick [expect = genuine]
oops

lemma "(Q\<Colon>nat set) (The Q)"
nitpick [expect = genuine]
oops

lemma "\<not> Q (The Q)"
nitpick [expect = genuine]
oops

lemma "\<not> (Q\<Colon>nat set) (The Q)"
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

lemma "Q = {x\<Colon>'a} \<Longrightarrow> (Q\<Colon>'a set) (The Q)"
nitpick [expect = none]
oops

lemma "Q = {x\<Colon>nat} \<Longrightarrow> (Q\<Colon>nat set) (The Q)"
nitpick [expect = none]
oops

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
