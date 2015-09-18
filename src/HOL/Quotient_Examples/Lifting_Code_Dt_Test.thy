(*  Title:      HOL/Quotient_Examples/Lifting_Code_Dt_Test.thy
    Author:     Ondrej Kuncar, TU Muenchen
    Copyright   2015

Miscellaneous lift_definition(code_dt) definitions (for testing purposes).
*)

theory Lifting_Code_Dt_Test
imports Main
begin

(* basic examples *)

typedef bool2 = "{x. x}" by auto

setup_lifting type_definition_bool2

lift_definition(code_dt) f1 :: "bool2 option" is "Some True" by simp

lift_definition(code_dt) f2 :: "bool2 list" is "[True]" by simp

lift_definition(code_dt) f3 :: "bool2 \<times> int" is "(True, 42)" by simp

lift_definition(code_dt) f4 :: "int + bool2" is "Inr True" by simp

lift_definition(code_dt) f5 :: "'a \<Rightarrow> (bool2 \<times> 'a) option" is "\<lambda>x. Some (True, x)" by simp

(* ugly (i.e., sensitive to rewriting done in my tactics) definition of T *)

typedef 'a T = "{ x::'a. \<forall>(y::'a) z::'a. \<exists>(w::'a). (z = z) \<and> eq_onp top y y 
  \<or> rel_prod (eq_onp top) (eq_onp top) (x, y) (x, y) \<longrightarrow> pred_prod top top (w, w) }"
  by auto

setup_lifting type_definition_T

lift_definition(code_dt) f6 :: "bool T option" is "Some True" by simp

lift_definition(code_dt) f7 :: "(bool T \<times> int) option" is "Some (True, 42)" by simp

lift_definition(code_dt) f8 :: "bool T \<Rightarrow> int \<Rightarrow> (bool T \<times> int) option" 
  is "\<lambda>x y. if x then Some (x, y) else None" by simp

lift_definition(code_dt) f9 :: "nat \<Rightarrow> ((bool T \<times> int) option) list \<times> nat" 
  is "\<lambda>x. ([Some (True, 42)], x)" by simp

(* complicated nested datatypes *)

(* stolen from Datatype_Examples *)
datatype 'a tree = Empty | Node 'a "'a tree list"

datatype 'a ttree = TEmpty | TNode 'a "'a ttree list tree"

datatype 'a tttree = TEmpty | TNode 'a "'a tttree list ttree list tree"

lift_definition(code_dt) f10 :: "int \<Rightarrow> int T tree" is "\<lambda>i. Node i [Node i Nil, Empty]" by simp

lift_definition(code_dt) f11 :: "int \<Rightarrow> int T ttree" 
  is "\<lambda>i. ttree.TNode i (Node [ttree.TNode i Empty] [])" by simp

lift_definition(code_dt) f12 :: "int \<Rightarrow> int T tttree" is "\<lambda>i. tttree.TNode i Empty" by simp

(* Phantom type variables *)

datatype 'a phantom = PH1 | PH2 

datatype ('a, 'b) phantom2 = PH21 'a | PH22 "'a option"

lift_definition(code_dt) f13 :: "int \<Rightarrow> int T phantom" is "\<lambda>i. PH1" by auto

lift_definition(code_dt) f14 :: "int \<Rightarrow> (int T, nat T) phantom2" is "\<lambda>i. PH22 (Some i)" by auto

(* Mutual datatypes *)

datatype 'a M1 = Empty 'a | CM "'a M2"
and 'a M2 = CM2 "'a M1"

lift_definition(code_dt) f15 :: "int \<Rightarrow> int T M1" is "\<lambda>i. Empty i" by auto

(* Codatatypes *)

codatatype 'a stream = S 'a "'a stream"

primcorec 
  sconst :: "'a \<Rightarrow> 'a stream" where
  "sconst a = S a (sconst a)"

lift_definition(code_dt) f16 :: "int \<Rightarrow> int T stream" is "\<lambda>i. sconst i"  unfolding pred_stream_def
by auto

(* Sort constraints *)

datatype ('a::finite, 'b::finite) F = F 'a | F2 'b

instance T :: (finite) finite by standard (transfer, auto)

lift_definition(code_dt) f17 :: "bool \<Rightarrow> (bool T, 'b::finite) F" is "\<lambda>b. F b" by auto

export_code f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 
  checking SML OCaml? Haskell? Scala? 

end
