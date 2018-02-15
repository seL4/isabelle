(*  Title:      HOL/Nitpick_Examples/Mini_Nits.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009-2011

Examples featuring Minipick, the minimalistic version of Nitpick.
*)

section \<open>Examples Featuring Minipick, the Minimalistic Version of Nitpick\<close>

theory Mini_Nits
imports Main
begin

ML_file "minipick.ML"

nitpick_params [verbose, sat_solver = MiniSat_JNI, max_threads = 1,
  total_consts = smart]

ML \<open>
val check = Minipick.minipick @{context}
val expect = Minipick.minipick_expect @{context}
val none = expect "none"
val genuine = expect "genuine"
val unknown = expect "unknown"
\<close>

ML \<open>genuine 1 @{prop "x = Not"}\<close>
ML \<open>none 1 @{prop "\<exists>x. x = Not"}\<close>
ML \<open>none 1 @{prop "\<not> False"}\<close>
ML \<open>genuine 1 @{prop "\<not> True"}\<close>
ML \<open>none 1 @{prop "\<not> \<not> b \<longleftrightarrow> b"}\<close>
ML \<open>none 1 @{prop True}\<close>
ML \<open>genuine 1 @{prop False}\<close>
ML \<open>genuine 1 @{prop "True \<longleftrightarrow> False"}\<close>
ML \<open>none 1 @{prop "True \<longleftrightarrow> \<not> False"}\<close>
ML \<open>none 4 @{prop "\<forall>x. x = x"}\<close>
ML \<open>none 4 @{prop "\<exists>x. x = x"}\<close>
ML \<open>none 1 @{prop "\<forall>x. x = y"}\<close>
ML \<open>genuine 2 @{prop "\<forall>x. x = y"}\<close>
ML \<open>none 2 @{prop "\<exists>x. x = y"}\<close>
ML \<open>none 2 @{prop "\<forall>x::'a \<times> 'a. x = x"}\<close>
ML \<open>none 2 @{prop "\<exists>x::'a \<times> 'a. x = y"}\<close>
ML \<open>genuine 2 @{prop "\<forall>x::'a \<times> 'a. x = y"}\<close>
ML \<open>none 2 @{prop "\<exists>x::'a \<times> 'a. x = y"}\<close>
ML \<open>none 1 @{prop "All = Ex"}\<close>
ML \<open>genuine 2 @{prop "All = Ex"}\<close>
ML \<open>none 1 @{prop "All P = Ex P"}\<close>
ML \<open>genuine 2 @{prop "All P = Ex P"}\<close>
ML \<open>none 4 @{prop "x = y \<longrightarrow> P x = P y"}\<close>
ML \<open>none 4 @{prop "(x::'a \<times> 'a) = y \<longrightarrow> P x = P y"}\<close>
ML \<open>none 2 @{prop "(x::'a \<times> 'a) = y \<longrightarrow> P x y = P y x"}\<close>
ML \<open>none 4 @{prop "\<exists>x::'a \<times> 'a. x = y \<longrightarrow> P x = P y"}\<close>
ML \<open>none 2 @{prop "(x::'a \<Rightarrow> 'a) = y \<longrightarrow> P x = P y"}\<close>
ML \<open>none 2 @{prop "\<exists>x::'a \<Rightarrow> 'a. x = y \<longrightarrow> P x = P y"}\<close>
ML \<open>genuine 1 @{prop "(=) X = Ex"}\<close>
ML \<open>none 2 @{prop "\<forall>x::'a \<Rightarrow> 'a. x = x"}\<close>
ML \<open>none 1 @{prop "x = y"}\<close>
ML \<open>genuine 1 @{prop "x \<longleftrightarrow> y"}\<close>
ML \<open>genuine 2 @{prop "x = y"}\<close>
ML \<open>genuine 1 @{prop "X \<subseteq> Y"}\<close>
ML \<open>none 1 @{prop "P \<and> Q \<longleftrightarrow> Q \<and> P"}\<close>
ML \<open>none 1 @{prop "P \<and> Q \<longrightarrow> P"}\<close>
ML \<open>none 1 @{prop "P \<or> Q \<longleftrightarrow> Q \<or> P"}\<close>
ML \<open>genuine 1 @{prop "P \<or> Q \<longrightarrow> P"}\<close>
ML \<open>none 1 @{prop "(P \<longrightarrow> Q) \<longleftrightarrow> (\<not> P \<or> Q)"}\<close>
ML \<open>none 4 @{prop "{a} = {a, a}"}\<close>
ML \<open>genuine 2 @{prop "{a} = {a, b}"}\<close>
ML \<open>genuine 1 @{prop "{a} \<noteq> {a, b}"}\<close>
ML \<open>none 4 @{prop "{}\<^sup>+ = {}"}\<close>
ML \<open>none 4 @{prop "UNIV\<^sup>+ = UNIV"}\<close>
ML \<open>none 4 @{prop "(UNIV :: ('a \<times> 'b) set) - {} = UNIV"}\<close>
ML \<open>none 4 @{prop "{} - (UNIV :: ('a \<times> 'b) set) = {}"}\<close>
ML \<open>none 1 @{prop "{(a, b), (b, c)}\<^sup>+ = {(a, b), (a, c), (b, c)}"}\<close>
ML \<open>genuine 2 @{prop "{(a, b), (b, c)}\<^sup>+ = {(a, b), (a, c), (b, c)}"}\<close>
ML \<open>none 4 @{prop "a \<noteq> c \<Longrightarrow> {(a, b), (b, c)}\<^sup>+ = {(a, b), (a, c), (b, c)}"}\<close>
ML \<open>none 4 @{prop "A \<union> B = {x. x \<in> A \<or> x \<in> B}"}\<close>
ML \<open>none 4 @{prop "A \<inter> B = {x. x \<in> A \<and> x \<in> B}"}\<close>
ML \<open>none 4 @{prop "A - B = (\<lambda>x. A x \<and> \<not> B x)"}\<close>
ML \<open>none 4 @{prop "\<exists>a b. (a, b) = (b, a)"}\<close>
ML \<open>genuine 2 @{prop "(a, b) = (b, a)"}\<close>
ML \<open>genuine 2 @{prop "(a, b) \<noteq> (b, a)"}\<close>
ML \<open>none 4 @{prop "\<exists>a b::'a \<times> 'a. (a, b) = (b, a)"}\<close>
ML \<open>genuine 2 @{prop "(a::'a \<times> 'a, b) = (b, a)"}\<close>
ML \<open>none 4 @{prop "\<exists>a b::'a \<times> 'a \<times> 'a. (a, b) = (b, a)"}\<close>
ML \<open>genuine 2 @{prop "(a::'a \<times> 'a \<times> 'a, b) \<noteq> (b, a)"}\<close>
ML \<open>none 4 @{prop "\<exists>a b::'a \<Rightarrow> 'a. (a, b) = (b, a)"}\<close>
ML \<open>genuine 1 @{prop "(a::'a \<Rightarrow> 'a, b) \<noteq> (b, a)"}\<close>
ML \<open>none 4 @{prop "fst (a, b) = a"}\<close>
ML \<open>none 1 @{prop "fst (a, b) = b"}\<close>
ML \<open>genuine 2 @{prop "fst (a, b) = b"}\<close>
ML \<open>genuine 2 @{prop "fst (a, b) \<noteq> b"}\<close>
ML \<open>genuine 2 @{prop "f ((x, z), y) = (x, z)"}\<close>
ML \<open>none 2 @{prop "(\<forall>x. f x = fst x) \<longrightarrow> f ((x, z), y) = (x, z)"}\<close>
ML \<open>none 4 @{prop "snd (a, b) = b"}\<close>
ML \<open>none 1 @{prop "snd (a, b) = a"}\<close>
ML \<open>genuine 2 @{prop "snd (a, b) = a"}\<close>
ML \<open>genuine 2 @{prop "snd (a, b) \<noteq> a"}\<close>
ML \<open>genuine 1 @{prop P}\<close>
ML \<open>genuine 1 @{prop "(\<lambda>x. P) a"}\<close>
ML \<open>genuine 1 @{prop "(\<lambda>x y z. P y x z) a b c"}\<close>
ML \<open>none 4 @{prop "\<exists>f. f = (\<lambda>x. x) \<and> f y = y"}\<close>
ML \<open>genuine 1 @{prop "\<exists>f. f p \<noteq> p \<and> (\<forall>a b. f (a, b) = (a, b))"}\<close>
ML \<open>none 2 @{prop "\<exists>f. \<forall>a b. f (a, b) = (a, b)"}\<close>
ML \<open>none 3 @{prop "f = (\<lambda>a b. (b, a)) \<longrightarrow> f x y = (y, x)"}\<close>
ML \<open>genuine 2 @{prop "f = (\<lambda>a b. (b, a)) \<longrightarrow> f x y = (x, y)"}\<close>
ML \<open>none 4 @{prop "f = (\<lambda>x. f x)"}\<close>
ML \<open>none 4 @{prop "f = (\<lambda>x. f x::'a \<Rightarrow> bool)"}\<close>
ML \<open>none 4 @{prop "f = (\<lambda>x y. f x y)"}\<close>
ML \<open>none 4 @{prop "f = (\<lambda>x y. f x y::'a \<Rightarrow> bool)"}\<close>

end
