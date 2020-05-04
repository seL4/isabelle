(*  Title:      HOL/Datatype_Examples/Simproc_Tests.thy
    Author:     Manuel Eberl, TU München
*)

section \<open>Tests of datatype-specific simprocs\<close>

theory Datatype_Simproc_Tests
imports Main
begin

(* datatype without parameters *)

datatype foo = X | Y foo foo

lemma "x \<noteq> Y x y" "x \<noteq> Y y x" "Y x y \<noteq> x" "Y y x \<noteq> x"
  by simp_all


(* datatype with parameters *)

datatype 'a mytree = A 'a | B "'a mytree" "'a mytree"

lemma "B l r \<noteq> l" and "B l r \<noteq> r" and "l \<noteq> B l r" and "r \<noteq> B l r"
  by simp_all

notepad
begin
  fix a b c d e f :: "nat mytree"
  define t where [simp]: "t = B (B (B a b) (B c d)) (B e f)"
  have "\<forall>x\<in>{a,b,c,d,e,f}. t \<noteq> x"
    by simp
  have "\<forall>x\<in>{a,b,c,d,e,f}. x \<noteq> t"
    by simp
end


(* mutual recursion *)

datatype 'a myty1 = A1 'a | B1 "'a myty1" "'a myty2"
     and 'a myty2 = A2 'a | B2 "'a myty2" "'a myty1"

lemma "B1 a (B2 b c) \<noteq> a" and "B1 a (B2 b c) \<noteq> c"
  by simp_all

lemma "B2 a (B1 b c) \<noteq> a" and "B2 a (B1 b c) \<noteq> c"
  by simp_all

end
