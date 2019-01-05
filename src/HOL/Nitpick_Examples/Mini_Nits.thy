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
val check = Minipick.minipick \<^context>
val expect = Minipick.minipick_expect \<^context>
val none = expect "none"
val genuine = expect "genuine"
val unknown = expect "unknown"
\<close>

ML \<open>genuine 1 \<^prop>\<open>x = Not\<close>\<close>
ML \<open>none 1 \<^prop>\<open>\<exists>x. x = Not\<close>\<close>
ML \<open>none 1 \<^prop>\<open>\<not> False\<close>\<close>
ML \<open>genuine 1 \<^prop>\<open>\<not> True\<close>\<close>
ML \<open>none 1 \<^prop>\<open>\<not> \<not> b \<longleftrightarrow> b\<close>\<close>
ML \<open>none 1 \<^prop>\<open>True\<close>\<close>
ML \<open>genuine 1 \<^prop>\<open>False\<close>\<close>
ML \<open>genuine 1 \<^prop>\<open>True \<longleftrightarrow> False\<close>\<close>
ML \<open>none 1 \<^prop>\<open>True \<longleftrightarrow> \<not> False\<close>\<close>
ML \<open>none 4 \<^prop>\<open>\<forall>x. x = x\<close>\<close>
ML \<open>none 4 \<^prop>\<open>\<exists>x. x = x\<close>\<close>
ML \<open>none 1 \<^prop>\<open>\<forall>x. x = y\<close>\<close>
ML \<open>genuine 2 \<^prop>\<open>\<forall>x. x = y\<close>\<close>
ML \<open>none 2 \<^prop>\<open>\<exists>x. x = y\<close>\<close>
ML \<open>none 2 \<^prop>\<open>\<forall>x::'a \<times> 'a. x = x\<close>\<close>
ML \<open>none 2 \<^prop>\<open>\<exists>x::'a \<times> 'a. x = y\<close>\<close>
ML \<open>genuine 2 \<^prop>\<open>\<forall>x::'a \<times> 'a. x = y\<close>\<close>
ML \<open>none 2 \<^prop>\<open>\<exists>x::'a \<times> 'a. x = y\<close>\<close>
ML \<open>none 1 \<^prop>\<open>All = Ex\<close>\<close>
ML \<open>genuine 2 \<^prop>\<open>All = Ex\<close>\<close>
ML \<open>none 1 \<^prop>\<open>All P = Ex P\<close>\<close>
ML \<open>genuine 2 \<^prop>\<open>All P = Ex P\<close>\<close>
ML \<open>none 4 \<^prop>\<open>x = y \<longrightarrow> P x = P y\<close>\<close>
ML \<open>none 4 \<^prop>\<open>(x::'a \<times> 'a) = y \<longrightarrow> P x = P y\<close>\<close>
ML \<open>none 2 \<^prop>\<open>(x::'a \<times> 'a) = y \<longrightarrow> P x y = P y x\<close>\<close>
ML \<open>none 4 \<^prop>\<open>\<exists>x::'a \<times> 'a. x = y \<longrightarrow> P x = P y\<close>\<close>
ML \<open>none 2 \<^prop>\<open>(x::'a \<Rightarrow> 'a) = y \<longrightarrow> P x = P y\<close>\<close>
ML \<open>none 2 \<^prop>\<open>\<exists>x::'a \<Rightarrow> 'a. x = y \<longrightarrow> P x = P y\<close>\<close>
ML \<open>genuine 1 \<^prop>\<open>(=) X = Ex\<close>\<close>
ML \<open>none 2 \<^prop>\<open>\<forall>x::'a \<Rightarrow> 'a. x = x\<close>\<close>
ML \<open>none 1 \<^prop>\<open>x = y\<close>\<close>
ML \<open>genuine 1 \<^prop>\<open>x \<longleftrightarrow> y\<close>\<close>
ML \<open>genuine 2 \<^prop>\<open>x = y\<close>\<close>
ML \<open>genuine 1 \<^prop>\<open>X \<subseteq> Y\<close>\<close>
ML \<open>none 1 \<^prop>\<open>P \<and> Q \<longleftrightarrow> Q \<and> P\<close>\<close>
ML \<open>none 1 \<^prop>\<open>P \<and> Q \<longrightarrow> P\<close>\<close>
ML \<open>none 1 \<^prop>\<open>P \<or> Q \<longleftrightarrow> Q \<or> P\<close>\<close>
ML \<open>genuine 1 \<^prop>\<open>P \<or> Q \<longrightarrow> P\<close>\<close>
ML \<open>none 1 \<^prop>\<open>(P \<longrightarrow> Q) \<longleftrightarrow> (\<not> P \<or> Q)\<close>\<close>
ML \<open>none 4 \<^prop>\<open>{a} = {a, a}\<close>\<close>
ML \<open>genuine 2 \<^prop>\<open>{a} = {a, b}\<close>\<close>
ML \<open>genuine 1 \<^prop>\<open>{a} \<noteq> {a, b}\<close>\<close>
ML \<open>none 4 \<^prop>\<open>{}\<^sup>+ = {}\<close>\<close>
ML \<open>none 4 \<^prop>\<open>UNIV\<^sup>+ = UNIV\<close>\<close>
ML \<open>none 4 \<^prop>\<open>(UNIV :: ('a \<times> 'b) set) - {} = UNIV\<close>\<close>
ML \<open>none 4 \<^prop>\<open>{} - (UNIV :: ('a \<times> 'b) set) = {}\<close>\<close>
ML \<open>none 1 \<^prop>\<open>{(a, b), (b, c)}\<^sup>+ = {(a, b), (a, c), (b, c)}\<close>\<close>
ML \<open>genuine 2 \<^prop>\<open>{(a, b), (b, c)}\<^sup>+ = {(a, b), (a, c), (b, c)}\<close>\<close>
ML \<open>none 4 \<^prop>\<open>a \<noteq> c \<Longrightarrow> {(a, b), (b, c)}\<^sup>+ = {(a, b), (a, c), (b, c)}\<close>\<close>
ML \<open>none 4 \<^prop>\<open>A \<union> B = {x. x \<in> A \<or> x \<in> B}\<close>\<close>
ML \<open>none 4 \<^prop>\<open>A \<inter> B = {x. x \<in> A \<and> x \<in> B}\<close>\<close>
ML \<open>none 4 \<^prop>\<open>A - B = (\<lambda>x. A x \<and> \<not> B x)\<close>\<close>
ML \<open>none 4 \<^prop>\<open>\<exists>a b. (a, b) = (b, a)\<close>\<close>
ML \<open>genuine 2 \<^prop>\<open>(a, b) = (b, a)\<close>\<close>
ML \<open>genuine 2 \<^prop>\<open>(a, b) \<noteq> (b, a)\<close>\<close>
ML \<open>none 4 \<^prop>\<open>\<exists>a b::'a \<times> 'a. (a, b) = (b, a)\<close>\<close>
ML \<open>genuine 2 \<^prop>\<open>(a::'a \<times> 'a, b) = (b, a)\<close>\<close>
ML \<open>none 4 \<^prop>\<open>\<exists>a b::'a \<times> 'a \<times> 'a. (a, b) = (b, a)\<close>\<close>
ML \<open>genuine 2 \<^prop>\<open>(a::'a \<times> 'a \<times> 'a, b) \<noteq> (b, a)\<close>\<close>
ML \<open>none 4 \<^prop>\<open>\<exists>a b::'a \<Rightarrow> 'a. (a, b) = (b, a)\<close>\<close>
ML \<open>genuine 1 \<^prop>\<open>(a::'a \<Rightarrow> 'a, b) \<noteq> (b, a)\<close>\<close>
ML \<open>none 4 \<^prop>\<open>fst (a, b) = a\<close>\<close>
ML \<open>none 1 \<^prop>\<open>fst (a, b) = b\<close>\<close>
ML \<open>genuine 2 \<^prop>\<open>fst (a, b) = b\<close>\<close>
ML \<open>genuine 2 \<^prop>\<open>fst (a, b) \<noteq> b\<close>\<close>
ML \<open>genuine 2 \<^prop>\<open>f ((x, z), y) = (x, z)\<close>\<close>
ML \<open>none 2 \<^prop>\<open>(\<forall>x. f x = fst x) \<longrightarrow> f ((x, z), y) = (x, z)\<close>\<close>
ML \<open>none 4 \<^prop>\<open>snd (a, b) = b\<close>\<close>
ML \<open>none 1 \<^prop>\<open>snd (a, b) = a\<close>\<close>
ML \<open>genuine 2 \<^prop>\<open>snd (a, b) = a\<close>\<close>
ML \<open>genuine 2 \<^prop>\<open>snd (a, b) \<noteq> a\<close>\<close>
ML \<open>genuine 1 \<^prop>\<open>P\<close>\<close>
ML \<open>genuine 1 \<^prop>\<open>(\<lambda>x. P) a\<close>\<close>
ML \<open>genuine 1 \<^prop>\<open>(\<lambda>x y z. P y x z) a b c\<close>\<close>
ML \<open>none 4 \<^prop>\<open>\<exists>f. f = (\<lambda>x. x) \<and> f y = y\<close>\<close>
ML \<open>genuine 1 \<^prop>\<open>\<exists>f. f p \<noteq> p \<and> (\<forall>a b. f (a, b) = (a, b))\<close>\<close>
ML \<open>none 2 \<^prop>\<open>\<exists>f. \<forall>a b. f (a, b) = (a, b)\<close>\<close>
ML \<open>none 3 \<^prop>\<open>f = (\<lambda>a b. (b, a)) \<longrightarrow> f x y = (y, x)\<close>\<close>
ML \<open>genuine 2 \<^prop>\<open>f = (\<lambda>a b. (b, a)) \<longrightarrow> f x y = (x, y)\<close>\<close>
ML \<open>none 4 \<^prop>\<open>f = (\<lambda>x. f x)\<close>\<close>
ML \<open>none 4 \<^prop>\<open>f = (\<lambda>x. f x::'a \<Rightarrow> bool)\<close>\<close>
ML \<open>none 4 \<^prop>\<open>f = (\<lambda>x y. f x y)\<close>\<close>
ML \<open>none 4 \<^prop>\<open>f = (\<lambda>x y. f x y::'a \<Rightarrow> bool)\<close>\<close>

end
