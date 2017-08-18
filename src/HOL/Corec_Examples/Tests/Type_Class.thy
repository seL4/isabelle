(*  Title:      HOL/Corec_Examples/Tests/Type_Class.thy
    Author:     Andreas Lochbihler, ETH Zuerich
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Copyright   2016

Tests type class instances as friends.
*)

section \<open>Tests Type Class Instances as Friends\<close>

theory Type_Class
imports "HOL-Library.BNF_Corec" "HOL-Library.Stream"
begin

instantiation stream :: (plus) plus
begin

definition plus_stream where "plus_stream s1 s2 = smap (\<lambda>(x, y). x + y) (sproduct s1 s2)"

instance ..

end

friend_of_corec plus (* :: "'a stream \<Rightarrow> 'a stream \<Rightarrow> 'a stream" *) where
  "s1 + s2 = SCons (shd s1 + shd s2) (stl s1 + stl s2)"
  sorry

corec ff :: "('a::plus) stream \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
  "ff xs ys = SCons (shd xs + shd ys) (ff (stl xs) ys) + SCons (shd xs) (ff xs (stl ys))"

end
