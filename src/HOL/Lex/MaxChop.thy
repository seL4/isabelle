(*  Title:      HOL/Lex/MaxChop.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

theory MaxChop = MaxPrefix:

types   'a chopper = "'a list => 'a list list * 'a list"

constdefs
 is_maxchopper :: "('a list => bool) => 'a chopper => bool"
"is_maxchopper P chopper ==
 !xs zs yss.
    (chopper(xs) = (yss,zs)) =
    (xs = concat yss @ zs & (!ys : set yss. ys ~= []) &
     (case yss of
        [] => is_maxpref P [] xs
      | us#uss => is_maxpref P us xs & chopper(concat(uss)@zs) = (uss,zs)))"

constdefs
 reducing :: "'a splitter => bool"
"reducing splitf ==
 !xs ys zs. splitf xs = (ys,zs) & ys ~= [] --> length zs < length xs"

consts
 chopr :: "'a splitter * 'a list => 'a list list * 'a list"
recdef (permissive) chopr "measure (length o snd)"
"chopr (splitf,xs) = (if reducing splitf
                      then let pp = splitf xs
                           in if fst(pp)=[] then ([],xs)
                           else let qq = chopr (splitf,snd pp)
                                in (fst pp # fst qq,snd qq)
                      else arbitrary)"

constdefs
 chop :: "'a splitter  => 'a chopper"
"chop splitf xs == chopr(splitf,xs)"

(* Termination of chop *)

lemma reducing_maxsplit: "reducing(%qs. maxsplit P ([],qs) [] qs)"
by (simp add: reducing_def maxsplit_eq)

recdef_tc chopr_tc: chopr
apply(unfold reducing_def)
apply(blast dest: sym)
done

lemmas chopr_rule = chopr.simps[OF chopr_tc]

lemma chop_rule: "reducing splitf ==>
  chop splitf xs = (let (pre,post) = splitf xs
                    in if pre=[] then ([],xs)
                       else let (xss,zs) = chop splitf post
                            in (pre#xss,zs))"
apply(simp add: chop_def chopr_rule)
apply(simp add: chop_def Let_def split: split_split)
done

lemma is_maxsplitter_reducing:
 "is_maxsplitter P splitf ==> reducing splitf";
by(simp add:is_maxsplitter_def reducing_def)

lemma chop_concat[rule_format]: "is_maxsplitter P splitf ==>
  (!yss zs. chop splitf xs = (yss,zs) --> xs = concat yss @ zs)"
apply (induct xs rule:length_induct)
apply (simp (no_asm_simp) split del: split_if
            add: chop_rule[OF is_maxsplitter_reducing])
apply (simp add: Let_def is_maxsplitter_def split: split_split)
done

lemma chop_nonempty: "is_maxsplitter P splitf ==>
  !yss zs. chop splitf xs = (yss,zs) --> (!ys : set yss. ys ~= [])"
apply (induct xs rule:length_induct)
apply (simp (no_asm_simp) add: chop_rule is_maxsplitter_reducing)
apply (simp add: Let_def is_maxsplitter_def split: split_split)
apply (intro allI impI)
apply (rule ballI)
apply (erule exE)
apply (erule allE)
apply auto
done

lemma is_maxchopper_chop:
 assumes prem: "is_maxsplitter P splitf" shows "is_maxchopper P (chop splitf)"
apply(unfold is_maxchopper_def)
apply clarify
apply (rule iffI)
 apply (rule conjI)
  apply (erule chop_concat[OF prem])
 apply (rule conjI)
  apply (erule prem[THEN chop_nonempty[THEN spec, THEN spec, THEN mp]])
 apply (erule rev_mp)
 apply (subst prem[THEN is_maxsplitter_reducing[THEN chop_rule]])
 apply (simp add: Let_def prem[simplified is_maxsplitter_def]
             split: split_split)
 apply clarify
 apply (rule conjI)
  apply (clarify)
 apply (clarify)
 apply simp
 apply (frule chop_concat[OF prem])
 apply (clarify)
apply (subst prem[THEN is_maxsplitter_reducing, THEN chop_rule])
apply (simp add: Let_def prem[simplified is_maxsplitter_def]
             split: split_split)
apply (clarify)
apply (rename_tac xs1 ys1 xss1 ys)
apply (simp split: list.split_asm)
 apply (simp add: is_maxpref_def)
 apply (blast intro: prefix_append[THEN iffD2])
apply (rule conjI)
 apply (clarify)
 apply (simp (no_asm_use) add: is_maxpref_def)
 apply (blast intro: prefix_append[THEN iffD2])
apply (clarify)
apply (rename_tac us uss)
apply (subgoal_tac "xs1=us")
 apply simp
apply simp
apply (simp (no_asm_use) add: is_maxpref_def)
apply (blast intro: prefix_append[THEN iffD2] order_antisym)
done

end
