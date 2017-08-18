theory Iterate_GPV imports
  "HOL-Library.BNF_Axiomatization"
  "HOL-Library.BNF_Corec"
begin

declare [[typedef_overloaded]]

datatype 'a spmf = return_spmf 'a

primrec (transfer) bind_spmf where
  "bind_spmf (return_spmf a) f = f a"

datatype (generat_pures: 'a, generat_outs: 'b, generat_conts: 'c) generat
  = Pure (result: 'a)
  | IO ("output": 'b) (continuation: "'c")

codatatype (results'_gpv: 'a, outs'_gpv: 'out, 'in) gpv
  = GPV (the_gpv: "('a, 'out, 'in \<Rightarrow> ('a, 'out, 'in) gpv) generat spmf")

declare gpv.rel_eq [relator_eq]

primcorec bind_gpv :: "('a, 'out, 'in) gpv \<Rightarrow> ('a \<Rightarrow> ('b, 'out, 'in) gpv) \<Rightarrow> ('b, 'out, 'in) gpv"
where
  "bind_gpv r f = GPV (map_spmf (map_generat id id (op \<circ> (case_sum id (\<lambda>r. bind_gpv r f))))
     (bind_spmf (the_gpv r)
      (case_generat
        (\<lambda>x. map_spmf (map_generat id id (op \<circ> Inl)) (the_gpv (f x)))
        (\<lambda>out c. return_spmf (IO out (\<lambda>input. Inr (c input)))))))"

context includes lifting_syntax begin

lemma bind_gpv_parametric [transfer_rule]:
  "(rel_gpv A C ===> (A ===> rel_gpv B C) ===> rel_gpv B C) bind_gpv bind_gpv"
unfolding bind_gpv_def by transfer_prover

end

lemma [friend_of_corec_simps]:
  "map_spmf f (bind_spmf x h) = bind_spmf x (map_spmf f o h)"
  by (cases x) auto

lemma [friend_of_corec_simps]:
  "bind_spmf (map_spmf f x) h = bind_spmf x (h o f)"
  by (cases x) auto

friend_of_corec bind_gpv :: "('a, 'out, 'in) gpv \<Rightarrow> ('a \<Rightarrow> ('a, 'out, 'in) gpv) \<Rightarrow> ('a, 'out, 'in) gpv"
where "bind_gpv r f = GPV (map_spmf (map_generat id id (op \<circ> (case_sum id (\<lambda>r. bind_gpv r f))))
     (bind_spmf (the_gpv r)
      (case_generat
        (\<lambda>x. map_spmf (map_generat id id (op \<circ> Inl)) (the_gpv (f x)))
        (\<lambda>out c. return_spmf (IO out (\<lambda>input. Inr (c input)))))))"
apply(rule bind_gpv.ctr)
apply transfer_prover
apply transfer_prover
done

end