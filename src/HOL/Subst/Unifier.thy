(*  ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

*)

header{*Definition of Most General Unifier*}

theory Unifier
imports Subst

begin

consts

  Unifier   :: "[('a * 'a uterm)list, 'a uterm, 'a uterm] => bool"
  ">>"      :: "[('a * 'a uterm)list, ('a * 'a uterm)list] => bool" (infixr 52)
  MGUnifier :: "[('a * 'a uterm)list, 'a uterm, 'a uterm] => bool"
  Idem      :: "('a * 'a uterm)list => bool"

defs

  Unifier_def:      "Unifier s t u == t <| s = u <| s"
  MoreGeneral_def:  "r >> s == ? q. s =$= r <> q"
  MGUnifier_def:    "MGUnifier s t u == Unifier s t u & 
                                        (!r. Unifier r t u --> s >> r)"
  Idem_def:         "Idem(s) == (s <> s) =$= s"



lemmas unify_defs = Unifier_def MoreGeneral_def MGUnifier_def


subsection{*Unifiers*}

lemma Unifier_Comb [iff]: "Unifier s (Comb t u) (Comb v w) = (Unifier s t v & Unifier s u w)"
by (simp add: Unifier_def)


lemma Cons_Unifier: "[| v ~: vars_of t; v ~: vars_of u; Unifier s t u |] ==> Unifier ((v,r)#s) t u"
by (simp add: Unifier_def repl_invariance)


subsection{* Most General Unifiers*}

lemma mgu_sym: "MGUnifier s t u = MGUnifier s u t"
by (simp add: unify_defs eq_commute)


lemma MoreGen_Nil [iff]: "[] >> s"
by (auto simp add: MoreGeneral_def)

lemma MGU_iff: "MGUnifier s t u = (ALL r. Unifier r t u = s >> r)"
apply (unfold unify_defs)
apply (auto intro: ssubst_subst2 subst_comp_Nil)
done

lemma MGUnifier_Var: "~ Var v <: t ==> MGUnifier [(v,t)] (Var v) t"
apply (simp (no_asm) add: MGU_iff Unifier_def MoreGeneral_def del: subst_Var)
apply safe
apply (rule exI)
apply (erule subst, rule Cons_trivial [THEN subst_sym])
apply (erule ssubst_subst2)
apply (simp (no_asm_simp) add: Var_not_occs)
done

declare MGUnifier_Var [intro!]


subsection{*Idempotence*}

lemma Idem_Nil [iff]: "Idem([])"
by (simp add: Idem_def)

lemma Idem_iff: "Idem(s) = (sdom(s) Int srange(s) = {})"
by (simp add: Idem_def subst_eq_iff invariance dom_range_disjoint)

lemma Var_Idem [intro!]: "~ (Var(v) <: t) ==> Idem([(v,t)])"
by (simp add: vars_iff_occseq Idem_iff srange_iff empty_iff_all_not)

lemma Unifier_Idem_subst: 
  "[| Idem(r); Unifier s (t<|r) (u<|r) |]  
   ==> Unifier (r <> s) (t <| r) (u <| r)"
by (simp add: Idem_def Unifier_def comp_subst_subst)

lemma Idem_comp:
     "[| Idem(r);  Unifier s (t <| r) (u <| r);  
         !!q. Unifier q (t <| r) (u <| r) ==> s <> q =$= q  
      |] ==> Idem(r <> s)"
apply (frule Unifier_Idem_subst, blast) 
apply (force simp add: Idem_def subst_eq_iff)
done


end
