(*  Title:      HOL/Induct/Term.thy
    ID:         $Id$
    Author:     Stefan Berghofer,  TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Terms over a given alphabet *}

theory Term = Main:

datatype ('a, 'b) "term" =
    Var 'a
  | App 'b "('a, 'b) term list"


text {* \medskip Substitution function on terms *}

consts
  subst_term :: "('a => ('a, 'b) term) => ('a, 'b) term => ('a, 'b) term"
  subst_term_list ::
    "('a => ('a, 'b) term) => ('a, 'b) term list => ('a, 'b) term list"

primrec
  "subst_term f (Var a) = f a"
  "subst_term f (App b ts) = App b (subst_term_list f ts)"

  "subst_term_list f [] = []"
  "subst_term_list f (t # ts) =
     subst_term f t # subst_term_list f ts"


text {* \medskip A simple theorem about composition of substitutions *}

lemma subst_comp:
  "(subst_term ((subst_term f1) \<circ> f2) t) =
    (subst_term f1 (subst_term f2 t)) \<and>
  (subst_term_list ((subst_term f1) \<circ> f2) ts) =
    (subst_term_list f1 (subst_term_list f2 ts))"
  apply (induct t and ts)
     apply simp_all
  done


text {* \medskip Alternative induction rule *}

lemma term_induct2:
  "(!!v. P (Var v)) ==>
    (!!f ts. list_all P ts ==> P (App f ts))
  ==> P t"
proof -
  case rule_context
  have "P t \<and> list_all P ts"
    apply (induct t and ts)
       apply (rule rule_context)
      apply (rule rule_context)
      apply assumption
     apply simp_all
    done
  thus ?thesis ..
qed

end
