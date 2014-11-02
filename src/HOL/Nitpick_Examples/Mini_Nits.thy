(*  Title:      HOL/Nitpick_Examples/Mini_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2011

Examples featuring Minipick, the minimalistic version of Nitpick.
*)

section {* Examples Featuring Minipick, the Minimalistic Version of Nitpick *}

theory Mini_Nits
imports Main
begin

ML_file "minipick.ML"

nitpick_params [verbose, sat_solver = MiniSat_JNI, max_threads = 1,
  total_consts = smart]

ML {*
val check = Minipick.minipick @{context}
val expect = Minipick.minipick_expect @{context}
val none = expect "none"
val genuine = expect "genuine"
val unknown = expect "unknown"
*}

ML_val {* genuine 1 @{prop "x = Not"} *}
ML_val {* none 1 @{prop "\<exists>x. x = Not"} *}
ML_val {* none 1 @{prop "\<not> False"} *}
ML_val {* genuine 1 @{prop "\<not> True"} *}
ML_val {* none 1 @{prop "\<not> \<not> b \<longleftrightarrow> b"} *}
ML_val {* none 1 @{prop True} *}
ML_val {* genuine 1 @{prop False} *}
ML_val {* genuine 1 @{prop "True \<longleftrightarrow> False"} *}
ML_val {* none 1 @{prop "True \<longleftrightarrow> \<not> False"} *}
ML_val {* none 4 @{prop "\<forall>x. x = x"} *}
ML_val {* none 4 @{prop "\<exists>x. x = x"} *}
ML_val {* none 1 @{prop "\<forall>x. x = y"} *}
ML_val {* genuine 2 @{prop "\<forall>x. x = y"} *}
ML_val {* none 2 @{prop "\<exists>x. x = y"} *}
ML_val {* none 2 @{prop "\<forall>x\<Colon>'a \<times> 'a. x = x"} *}
ML_val {* none 2 @{prop "\<exists>x\<Colon>'a \<times> 'a. x = y"} *}
ML_val {* genuine 2 @{prop "\<forall>x\<Colon>'a \<times> 'a. x = y"} *}
ML_val {* none 2 @{prop "\<exists>x\<Colon>'a \<times> 'a. x = y"} *}
ML_val {* none 1 @{prop "All = Ex"} *}
ML_val {* genuine 2 @{prop "All = Ex"} *}
ML_val {* none 1 @{prop "All P = Ex P"} *}
ML_val {* genuine 2 @{prop "All P = Ex P"} *}
ML_val {* none 4 @{prop "x = y \<longrightarrow> P x = P y"} *}
ML_val {* none 4 @{prop "(x\<Colon>'a \<times> 'a) = y \<longrightarrow> P x = P y"} *}
ML_val {* none 2 @{prop "(x\<Colon>'a \<times> 'a) = y \<longrightarrow> P x y = P y x"} *}
ML_val {* none 4 @{prop "\<exists>x\<Colon>'a \<times> 'a. x = y \<longrightarrow> P x = P y"} *}
ML_val {* none 2 @{prop "(x\<Colon>'a \<Rightarrow> 'a) = y \<longrightarrow> P x = P y"} *}
ML_val {* none 2 @{prop "\<exists>x\<Colon>'a \<Rightarrow> 'a. x = y \<longrightarrow> P x = P y"} *}
ML_val {* genuine 1 @{prop "(op =) X = Ex"} *}
ML_val {* none 2 @{prop "\<forall>x::'a \<Rightarrow> 'a. x = x"} *}
ML_val {* none 1 @{prop "x = y"} *}
ML_val {* genuine 1 @{prop "x \<longleftrightarrow> y"} *}
ML_val {* genuine 2 @{prop "x = y"} *}
ML_val {* genuine 1 @{prop "X \<subseteq> Y"} *}
ML_val {* none 1 @{prop "P \<and> Q \<longleftrightarrow> Q \<and> P"} *}
ML_val {* none 1 @{prop "P \<and> Q \<longrightarrow> P"} *}
ML_val {* none 1 @{prop "P \<or> Q \<longleftrightarrow> Q \<or> P"} *}
ML_val {* genuine 1 @{prop "P \<or> Q \<longrightarrow> P"} *}
ML_val {* none 1 @{prop "(P \<longrightarrow> Q) \<longleftrightarrow> (\<not> P \<or> Q)"} *}
ML_val {* none 4 @{prop "{a} = {a, a}"} *}
ML_val {* genuine 2 @{prop "{a} = {a, b}"} *}
ML_val {* genuine 1 @{prop "{a} \<noteq> {a, b}"} *}
ML_val {* none 4 @{prop "{}\<^sup>+ = {}"} *}
ML_val {* none 4 @{prop "UNIV\<^sup>+ = UNIV"} *}
ML_val {* none 4 @{prop "(UNIV \<Colon> ('a \<times> 'b) set) - {} = UNIV"} *}
ML_val {* none 4 @{prop "{} - (UNIV \<Colon> ('a \<times> 'b) set) = {}"} *}
ML_val {* none 1 @{prop "{(a, b), (b, c)}\<^sup>+ = {(a, b), (a, c), (b, c)}"} *}
ML_val {* genuine 2 @{prop "{(a, b), (b, c)}\<^sup>+ = {(a, b), (a, c), (b, c)}"} *}
ML_val {* none 4 @{prop "a \<noteq> c \<Longrightarrow> {(a, b), (b, c)}\<^sup>+ = {(a, b), (a, c), (b, c)}"} *}
ML_val {* none 4 @{prop "A \<union> B = {x. x \<in> A \<or> x \<in> B}"} *}
ML_val {* none 4 @{prop "A \<inter> B = {x. x \<in> A \<and> x \<in> B}"} *}
ML_val {* none 4 @{prop "A - B = (\<lambda>x. A x \<and> \<not> B x)"} *}
ML_val {* none 4 @{prop "\<exists>a b. (a, b) = (b, a)"} *}
ML_val {* genuine 2 @{prop "(a, b) = (b, a)"} *}
ML_val {* genuine 2 @{prop "(a, b) \<noteq> (b, a)"} *}
ML_val {* none 4 @{prop "\<exists>a b\<Colon>'a \<times> 'a. (a, b) = (b, a)"} *}
ML_val {* genuine 2 @{prop "(a\<Colon>'a \<times> 'a, b) = (b, a)"} *}
ML_val {* none 4 @{prop "\<exists>a b\<Colon>'a \<times> 'a \<times> 'a. (a, b) = (b, a)"} *}
ML_val {* genuine 2 @{prop "(a\<Colon>'a \<times> 'a \<times> 'a, b) \<noteq> (b, a)"} *}
ML_val {* none 4 @{prop "\<exists>a b\<Colon>'a \<Rightarrow> 'a. (a, b) = (b, a)"} *}
ML_val {* genuine 1 @{prop "(a\<Colon>'a \<Rightarrow> 'a, b) \<noteq> (b, a)"} *}
ML_val {* none 4 @{prop "fst (a, b) = a"} *}
ML_val {* none 1 @{prop "fst (a, b) = b"} *}
ML_val {* genuine 2 @{prop "fst (a, b) = b"} *}
ML_val {* genuine 2 @{prop "fst (a, b) \<noteq> b"} *}
ML_val {* genuine 2 @{prop "f ((x, z), y) = (x, z)"} *}
ML_val {* none 2 @{prop "(ALL x. f x = fst x) \<longrightarrow> f ((x, z), y) = (x, z)"} *}
ML_val {* none 4 @{prop "snd (a, b) = b"} *}
ML_val {* none 1 @{prop "snd (a, b) = a"} *}
ML_val {* genuine 2 @{prop "snd (a, b) = a"} *}
ML_val {* genuine 2 @{prop "snd (a, b) \<noteq> a"} *}
ML_val {* genuine 1 @{prop P} *}
ML_val {* genuine 1 @{prop "(\<lambda>x. P) a"} *}
ML_val {* genuine 1 @{prop "(\<lambda>x y z. P y x z) a b c"} *}
ML_val {* none 4 @{prop "\<exists>f. f = (\<lambda>x. x) \<and> f y = y"} *}
ML_val {* genuine 1 @{prop "\<exists>f. f p \<noteq> p \<and> (\<forall>a b. f (a, b) = (a, b))"} *}
ML_val {* none 2 @{prop "\<exists>f. \<forall>a b. f (a, b) = (a, b)"} *}
ML_val {* none 3 @{prop "f = (\<lambda>a b. (b, a)) \<longrightarrow> f x y = (y, x)"} *}
ML_val {* genuine 2 @{prop "f = (\<lambda>a b. (b, a)) \<longrightarrow> f x y = (x, y)"} *}
ML_val {* none 4 @{prop "f = (\<lambda>x. f x)"} *}
ML_val {* none 4 @{prop "f = (\<lambda>x. f x\<Colon>'a \<Rightarrow> bool)"} *}
ML_val {* none 4 @{prop "f = (\<lambda>x y. f x y)"} *}
ML_val {* none 4 @{prop "f = (\<lambda>x y. f x y\<Colon>'a \<Rightarrow> bool)"} *}

end
