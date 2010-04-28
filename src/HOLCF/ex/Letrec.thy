(*  Title:      HOLCF/ex/Letrec.thy
    Author:     Brian Huffman
*)

header {* Recursive let bindings *}

theory Letrec
imports HOLCF
begin

default_sort pcpo

definition
  CLetrec :: "('a \<rightarrow> 'a \<times> 'b) \<rightarrow> 'b" where
  "CLetrec = (\<Lambda> F. snd (F\<cdot>(\<mu> x. fst (F\<cdot>x))))"

nonterminals
  recbinds recbindt recbind

syntax
  "_recbind"  :: "['a, 'a] \<Rightarrow> recbind"               ("(2_ =/ _)" 10)
  ""          :: "recbind \<Rightarrow> recbindt"               ("_")
  "_recbindt" :: "[recbind, recbindt] \<Rightarrow> recbindt"   ("_,/ _")
  ""          :: "recbindt \<Rightarrow> recbinds"              ("_")
  "_recbinds" :: "[recbindt, recbinds] \<Rightarrow> recbinds"  ("_;/ _")
  "_Letrec"   :: "[recbinds, 'a] \<Rightarrow> 'a"      ("(Letrec (_)/ in (_))" 10)

translations
  (recbindt) "x = a, (y,ys) = (b,bs)" == (recbindt) "(x,y,ys) = (a,b,bs)"
  (recbindt) "x = a, y = b"          == (recbindt) "(x,y) = (a,b)"

translations
  "_Letrec (_recbinds b bs) e" == "_Letrec b (_Letrec bs e)"
  "Letrec xs = a in (e,es)"    == "CONST CLetrec\<cdot>(\<Lambda> xs. (a,e,es))"
  "Letrec xs = a in e"         == "CONST CLetrec\<cdot>(\<Lambda> xs. (a,e))"

end
