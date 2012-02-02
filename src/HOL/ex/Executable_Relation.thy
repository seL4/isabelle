theory Executable_Relation
imports Main
begin

text {*
 Current problem: rtrancl is not executable on an infinite type. 
*}

lemma
  "(x, (y :: nat)) : rtrancl (R Un S) \<Longrightarrow> (x, y) : (rtrancl R) Un (rtrancl S)"
(* quickcheck[exhaustive] fails ! *)
oops

code_thms rtrancl

hide_const (open) rtrancl trancl

quotient_type 'a rel = "('a * 'a) set" / "(op =)"
morphisms set_of_rel rel_of_set by (metis identity_equivp)

lemma [simp]:
  "rel_of_set (set_of_rel S) = S"
by (rule Quotient_abs_rep[OF Quotient_rel])

lemma [simp]:
  "set_of_rel (rel_of_set R) = R"
by (rule Quotient_rep_abs[OF Quotient_rel]) (rule refl)

no_notation
   Set.member ("(_/ : _)" [50, 51] 50)

quotient_definition member :: "'a * 'a => 'a rel => bool" where
  "member" is "Set.member :: 'a * 'a => ('a * 'a) set => bool"

notation
   member  ("(_/ : _)" [50, 51] 50)

quotient_definition union :: "'a rel => 'a rel => 'a rel" where
  "union" is "Set.union :: ('a * 'a) set => ('a * 'a) set => ('a * 'a) set"

quotient_definition rtrancl :: "'a rel => 'a rel" where
  "rtrancl" is "Transitive_Closure.rtrancl :: ('a * 'a) set => ('a * 'a) set" 

definition reflcl_raw 
where "reflcl_raw R = R \<union> Id"

quotient_definition reflcl :: "('a * 'a) set => 'a rel" where
  "reflcl" is "reflcl_raw :: ('a * 'a) set => ('a * 'a) set"

code_datatype reflcl rel_of_set

lemma member_code[code]:
  "(x, y) : rel_of_set R = Set.member (x, y) R"
  "(x, y) : reflcl R = ((x = y) \<or> Set.member (x, y) R)"
unfolding member_def reflcl_def reflcl_raw_def map_fun_def_raw o_def id_def
by auto

lemma union_code[code]:
  "union (rel_of_set R) (rel_of_set S) = rel_of_set (Set.union R S)"
  "union (reflcl R) (rel_of_set S) = reflcl (Set.union R S)"
  "union (reflcl R) (reflcl S) = reflcl (Set.union R S)"
  "union (rel_of_set R) (reflcl S) = reflcl (Set.union R S)"
unfolding union_def reflcl_def reflcl_raw_def map_fun_def_raw o_def id_def
by (auto intro: arg_cong[where f=rel_of_set])

lemma rtrancl_code[code]:
  "rtrancl (rel_of_set R) = reflcl (Transitive_Closure.trancl R)"
  "rtrancl (reflcl R) = reflcl (Transitive_Closure.trancl R)"
unfolding rtrancl_def reflcl_def reflcl_raw_def map_fun_def_raw o_def id_def
by (auto intro: arg_cong[where f=rel_of_set])

quickcheck_generator rel constructors: rel_of_set

lemma
  "(x, (y :: nat)) : rtrancl (union R S) \<Longrightarrow> (x, y) : (union (rtrancl R) (rtrancl S))"
quickcheck[exhaustive]
oops

end
