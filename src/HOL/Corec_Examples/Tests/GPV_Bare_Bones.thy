(*  Title:      HOL/Corec_Examples/Tests/GPV_Bare_Bones.thy
    Author:     Andreas Lochbihler, ETH Zuerich
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Copyright   2016

A bare bones version of generative probabilistic values (GPVs).
*)

section \<open>A Bare Bones Version of Generative Probabilistic Values (GPVs)\<close>

theory GPV_Bare_Bones
imports "HOL-Library.BNF_Corec"
begin

datatype 'a pmf = return_pmf 'a

type_synonym 'a spmf = "'a option pmf"

abbreviation map_spmf :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a spmf \<Rightarrow> 'b spmf"
where "map_spmf f \<equiv> map_pmf (map_option f)"

abbreviation return_spmf :: "'a \<Rightarrow> 'a spmf"
where "return_spmf x \<equiv> return_pmf (Some x)"

datatype (generat_pures: 'a, generat_outs: 'b, generat_conts: 'c) generat =
  Pure (result: 'a)
| IO ("output": 'b) (continuation: "'c")

codatatype (results'_gpv: 'a, outs'_gpv: 'out, 'in) gpv =
  GPV (the_gpv: "('a, 'out, 'in \<Rightarrow> ('a, 'out, 'in) gpv) generat spmf")

codatatype ('a, 'call, 'ret, 'x) gpv' =
  GPV' (the_gpv': "('a, 'call, 'ret \<Rightarrow> ('a, 'call, 'ret, 'x) gpv') generat spmf")

consts bind_gpv' :: "('a, 'call, 'ret) gpv \<Rightarrow> ('a \<Rightarrow> ('b, 'call, 'ret, 'a) gpv') \<Rightarrow> ('b, 'call, 'ret, 'a) gpv'"

definition bind_spmf :: "'a spmf \<Rightarrow> ('a \<Rightarrow> 'b spmf) \<Rightarrow> 'b spmf"
where "bind_spmf x f = undefined x (\<lambda>a. case a of None \<Rightarrow> return_pmf None | Some a' \<Rightarrow> f a')"

friend_of_corec bind_gpv'
where "bind_gpv' r f =
GPV' (map_spmf (map_generat id id ((\<circ>) (case_sum id (\<lambda>r. bind_gpv' r f))))
      (bind_spmf (the_gpv r)
        (case_generat (\<lambda>x. map_spmf (map_generat id id ((\<circ>) Inl)) (the_gpv' (f x)))
          (\<lambda>out c. return_spmf (IO out (\<lambda>input. Inr (c input)))))))"
  sorry

end
