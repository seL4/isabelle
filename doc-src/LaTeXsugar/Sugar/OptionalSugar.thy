theory OptionalSugar
imports LaTeXsugar
begin

(* append *)
syntax (latex output)
  "appendL" :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<^raw:\isacharat>" 65)
translations
  "appendL xs ys" <= "xs @ ys" 
  "appendL (appendL xs ys) zs" <= "appendL xs (appendL ys zs)"


(* and *)
syntax (latex output)
  "_andL" :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixl "\<^raw:\isasymand>" 35)
translations
  "_andL A B" <= "A \<and> B" 
  "_andL (_andL A B) C" <= "_andL A (_andL B C)"


(* aligning equations *)
syntax (tab output)
  "op =" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("(_) \<^raw:}\putisatab\isa{\ >=\<^raw:}\putisatab\isa{> (_)" [50,49] 50)
  "==" :: "prop \<Rightarrow> prop \<Rightarrow> prop" ("(_) \<^raw:}\putisatab\isa{\ >\<equiv>\<^raw:}\putisatab\isa{> (_)")

(* Let *)
translations 
  "_bind (p,DUMMY) e" <= "_bind p (fst e)"
  "_bind (DUMMY,p) e" <= "_bind p (snd e)"

  "_tuple_args x (_tuple_args y z)" ==
    "_tuple_args x (_tuple_arg (_tuple y z))"

  "_bind (Some p) e" <= "_bind p (the e)"
  "_bind (p#DUMMY) e" <= "_bind p (hd e)"
  "_bind (DUMMY#p) e" <= "_bind p (tl e)"


end