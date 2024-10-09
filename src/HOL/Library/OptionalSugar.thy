(*  Title:      HOL/Library/OptionalSugar.thy
    Author:     Gerwin Klein, Tobias Nipkow
    Copyright   2005 NICTA and TUM
*)
(*<*)
theory OptionalSugar
imports Complex_Main LaTeXsugar
begin

(* displaying theorems with conjunctions between premises: *)
translations
  ("prop") "P \<and> Q \<Longrightarrow> R" <= ("prop") "P \<Longrightarrow> Q \<Longrightarrow> R"

(* hiding set *)
translations
  "xs" <= "CONST set xs"

(* hiding numeric conversions - embeddings only *)
translations
  "n" <= "CONST of_nat n"
  "n" <= "CONST int n"
  "n" <= "CONST real n"
  "n" <= "CONST real_of_nat n"
  "n" <= "CONST real_of_int n"
  "n" <= "CONST of_real n"
  "n" <= "CONST complex_of_real n"

(* append *)
syntax (latex output)
  "_appendL" :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl \<open>\<^latex>\<open>\isacharat\<close>\<close> 65)
translations
  "_appendL xs ys" <= "xs @ ys" 
  "_appendL (_appendL xs ys) zs" <= "_appendL xs (_appendL ys zs)"


(* deprecated, use thm with style instead, will be removed *)
(* aligning equations *)
notation (tab output)
  "HOL.eq"  (\<open>(_) \<^latex>\<open>}\putisatab\isa{\ \<close>=\<^latex>\<open>}\putisatab\isa{\<close> (_)\<close> [50,49] 50) and
  "Pure.eq"  (\<open>(_) \<^latex>\<open>}\putisatab\isa{\ \<close>\<equiv>\<^latex>\<open>}\putisatab\isa{\<close> (_)\<close>)

(* Let *)
translations 
  "_bind (p, CONST DUMMY) e" <= "_bind p (CONST fst e)"
  "_bind (CONST DUMMY, p) e" <= "_bind p (CONST snd e)"

  "_tuple_args x (_tuple_args y z)" ==
    "_tuple_args x (_tuple_arg (_tuple y z))"

  "_bind (CONST Some p) e" <= "_bind p (CONST the e)"
  "_bind (p # CONST DUMMY) e" <= "_bind p (CONST hd e)"
  "_bind (CONST DUMMY # p) e" <= "_bind p (CONST tl e)"

unbundle constrain_space_syntax


(* sorts as intersections *)

syntax (output)
  "_topsort" :: "sort"  (\<open>\<top>\<close> 1000)
  "_sort" :: "classes => sort"  (\<open>'(_')\<close> 1000)
  "_classes" :: "id => classes => classes"  (\<open>_ \<inter> _\<close> 1000)
  "_classes" :: "longid => classes => classes"  (\<open>_ \<inter> _\<close> 1000)

end
(*>*)
