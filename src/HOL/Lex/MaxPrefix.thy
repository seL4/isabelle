(*  Title:      HOL/Lex/MaxPrefix.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

theory MaxPrefix = List_Prefix:

constdefs
 is_maxpref :: "('a list => bool) => 'a list => 'a list => bool"
"is_maxpref P xs ys ==
 xs <= ys & (xs=[] | P xs) & (!zs. zs <= ys & P zs --> zs <= xs)"

types 'a splitter = "'a list => 'a list * 'a list"

constdefs
 is_maxsplitter :: "('a list => bool) => 'a splitter => bool"
"is_maxsplitter P f ==
 (!xs ps qs. f xs = (ps,qs) = (xs=ps@qs & is_maxpref P ps xs))"

consts
 maxsplit :: "('a list => bool) => 'a list * 'a list => 'a list => 'a splitter"
primrec
"maxsplit P res ps []     = (if P ps then (ps,[]) else res)"
"maxsplit P res ps (q#qs) = maxsplit P (if P ps then (ps,q#qs) else res)
                                     (ps@[q]) qs"

declare split_if[split del]

lemma maxsplit_lemma: "!!(ps::'a list) res.
  (maxsplit P res ps qs = (xs,ys)) =
  (if EX us. us <= qs & P(ps@us) then xs@ys=ps@qs & is_maxpref P xs (ps@qs)
   else (xs,ys)=res)"
apply(unfold is_maxpref_def)
apply (induct "qs")
 apply (simp split: split_if)
 apply blast
apply simp
apply (erule thin_rl)
apply clarify
apply (case_tac "EX us. us <= list & P (ps @ a # us)")
 apply (subgoal_tac "EX us. us <= a # list & P (ps @ us)")
  apply simp
 apply (blast intro: prefix_Cons[THEN iffD2])
apply (subgoal_tac "~P(ps@[a])")
 prefer 2 apply blast
apply (simp (no_asm_simp))
apply (case_tac "EX us. us <= a#list & P (ps @ us)")
 apply simp
 apply clarify
 apply (case_tac "us")
  apply (rule iffI)
   apply (simp add: prefix_Cons prefix_append)
   apply blast
  apply (simp add: prefix_Cons prefix_append)
  apply clarify
  apply (erule disjE)
   apply (fast dest: order_antisym)
  apply clarify
  apply (erule disjE)
   apply clarify
   apply simp
  apply (erule disjE)
   apply clarify
   apply simp
  apply blast
 apply simp
apply (subgoal_tac "~P(ps)")
apply (simp (no_asm_simp))
apply fastsimp
done

declare split_if[split add]

lemma is_maxpref_Nil[simp]:
 "~(? us. us<=xs & P us) ==> is_maxpref P ps xs = (ps = [])"
apply(unfold is_maxpref_def)
apply blast
done

lemma is_maxsplitter_maxsplit:
 "is_maxsplitter P (%xs. maxsplit P ([],xs) [] xs)"
apply(unfold is_maxsplitter_def)
apply (simp add: maxsplit_lemma)
apply (fastsimp)
done

lemmas maxsplit_eq = is_maxsplitter_maxsplit[simplified is_maxsplitter_def]

end
