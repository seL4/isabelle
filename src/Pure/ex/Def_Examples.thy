(*  Title:      Pure/ex/Def_Examples.thy
    Author:     Makarius

Some examples for primitive definitions.
*)

theory Def_Examples
  imports Def
begin

section \<open>Global definitions\<close>

def "I x \<equiv> x"
def "K x y \<equiv> x"
def "S x y z \<equiv> (x z) (y z)"

lemma "I (I x) \<equiv> x"
  by simp

lemma "K a x \<equiv> K a y"
  by simp

lemma "S K K \<equiv> I"
  by simp


section \<open>Locale definitions\<close>

locale const =
  fixes a :: 'a
begin

def "fun b \<equiv> a"

lemma "fun x \<equiv> fun y"
  by simp

end

lemma "const.fun a x \<equiv> const.fun a y"
  by simp

end
