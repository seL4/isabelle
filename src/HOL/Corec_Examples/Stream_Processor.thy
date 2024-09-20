(*  Title:      HOL/Corec_Examples/Stream_Processor.thy
    Author:     Andreas Lochbihler, ETH Zuerich
    Author:     Dmitriy Traytel, ETH Zuerich
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2014, 2016

Stream processors---a syntactic representation of continuous functions on streams.
*)

section \<open>Stream Processors---A Syntactic Representation of Continuous Functions on Streams\<close>

theory Stream_Processor
imports "HOL-Library.BNF_Corec" "HOL-Library.Stream"
begin

datatype (discs_sels) ('a, 'b, 'c) sp\<^sub>\<mu> =
  Get "'a \<Rightarrow> ('a, 'b, 'c) sp\<^sub>\<mu>"
| Put "'b" "'c"

codatatype ('a, 'b) sp\<^sub>\<nu> =
  In (out: "('a, 'b, ('a, 'b) sp\<^sub>\<nu>) sp\<^sub>\<mu>")

definition "sub \<equiv> {(f a, Get f) | a f. True}"

lemma subI[intro]: "(f a, Get f) \<in> sub"
  unfolding sub_def by blast

lemma wf_sub[simp, intro]: "wf sub"
proof (rule wfUNIVI)
  fix P  :: "('a, 'b, 'c) sp\<^sub>\<mu> \<Rightarrow> bool" and x
  assume "\<forall>x. (\<forall>y. (y, x) \<in> sub \<longrightarrow> P y) \<longrightarrow> P x"
  hence I: "\<And>x. (\<forall>y. (\<exists>a f. y = f a \<and> x = Get f) \<longrightarrow> P y) \<Longrightarrow> P x" unfolding sub_def by blast
  show "P x" by (induct x) (auto intro: I)
qed

lemma Get_neq: "Get f \<noteq> f a"
  by (metis subI wf_not_sym wf_sub)

definition get where
  "get f = In (Get (\<lambda>a. out (f a)))"

corecursive run :: "('a, 'b) sp\<^sub>\<nu> \<Rightarrow> 'a stream \<Rightarrow> 'b stream" where
  "run sp s = (case out sp of
     Get f \<Rightarrow> run (In (f (shd s))) (stl s)
   | Put b sp \<Rightarrow> b ## run sp s)"
  by (relation "inv_image (map_prod In In ` sub) fst")
     (auto simp: inj_on_def out_def split: sp\<^sub>\<nu>.splits intro: wf_map_prod_image)

corec copy where
  "copy = In (Get (\<lambda>a. Put a copy))"

friend_of_corec get where
  "get f = In (Get (\<lambda>a. out (f a)))"
  by (auto simp: rel_fun_def get_def sp\<^sub>\<mu>.rel_map rel_prod.simps, metis sndI)

lemma run_simps [simp]:
  "run (In (Get f)) s = run (In (f (shd s))) (stl s)"
  "run (In (Put b sp)) s = b ## run sp s"
by(subst run.code; simp; fail)+

lemma copy_sel[simp]: "out copy = Get (\<lambda>a. Put a copy)"
  by (subst copy.code; simp)

corecursive sp_comp (infixl \<open>oo\<close> 65) where
  "sp oo sp' = (case (out sp, out sp') of
      (Put b sp, _) \<Rightarrow> In (Put b (sp oo sp'))
    | (Get f, Put b sp) \<Rightarrow> In (f b) oo sp
    | (_, Get g) \<Rightarrow> get (\<lambda>a. (sp oo In (g a))))"
  by (relation "map_prod In In ` sub <*lex*> map_prod In In ` sub")
    (auto simp: inj_on_def out_def split: sp\<^sub>\<nu>.splits intro: wf_map_prod_image)

lemma run_copy_unique:
    "(\<And>s. h s = shd s ## h (stl s)) \<Longrightarrow> h = run copy"
apply corec_unique
apply(rule ext)
apply(subst copy.code)
apply simp
done

end
