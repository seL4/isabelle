(*  Title:      HOL/HOLCF/ex/Letrec.thy
    Author:     Brian Huffman
*)

section \<open>Recursive let bindings\<close>

theory Letrec
imports HOLCF
begin

definition
  CLetrec :: "('a::pcpo \<rightarrow> 'a \<times> 'b::pcpo) \<rightarrow> 'b" where
  "CLetrec = (\<Lambda> F. snd (F\<cdot>(\<mu> x. fst (F\<cdot>x))))"

nonterminal recbinds and recbindt and recbind

syntax
  "_recbind"  :: "[logic, logic] \<Rightarrow> recbind"         (\<open>(2_ =/ _)\<close> 10)
  ""          :: "recbind \<Rightarrow> recbindt"               (\<open>_\<close>)
  "_recbindt" :: "[recbind, recbindt] \<Rightarrow> recbindt"   (\<open>_,/ _\<close>)
  ""          :: "recbindt \<Rightarrow> recbinds"              (\<open>_\<close>)
  "_recbinds" :: "[recbindt, recbinds] \<Rightarrow> recbinds"  (\<open>_;/ _\<close>)
  "_Letrec"   :: "[recbinds, logic] \<Rightarrow> logic"        (\<open>(Letrec (_)/ in (_))\<close> 10)

syntax_consts
  "_recbind" "_recbinds" "_recbindt" "_Letrec" == CLetrec

translations
  (recbindt) "x = a, (y,ys) = (b,bs)" == (recbindt) "(x,y,ys) = (a,b,bs)"
  (recbindt) "x = a, y = b"          == (recbindt) "(x,y) = (a,b)"

translations
  "_Letrec (_recbinds b bs) e" == "_Letrec b (_Letrec bs e)"
  "Letrec xs = a in (e,es)"    == "CONST CLetrec\<cdot>(\<Lambda> xs. (a,e,es))"
  "Letrec xs = a in e"         == "CONST CLetrec\<cdot>(\<Lambda> xs. (a,e))"

end
