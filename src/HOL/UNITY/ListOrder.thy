(*  Title:      HOL/UNITY/ListOrder
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Lists are partially ordered by Charpentier's Generalized Prefix Relation
   (xs,ys) : genPrefix(r)
     if ys = xs' @ zs where length xs = length xs'
     and corresponding elements of xs, xs' are pairwise related by r

Also overloads <= and < for lists!

Based on Lex/Prefix
*)

header {*The Prefix Ordering on Lists*}

theory ListOrder = Main:

consts
  genPrefix :: "('a * 'a)set => ('a list * 'a list)set"

inductive "genPrefix(r)"
 intros
   Nil:     "([],[]) : genPrefix(r)"

   prepend: "[| (xs,ys) : genPrefix(r);  (x,y) : r |] ==>
	     (x#xs, y#ys) : genPrefix(r)"

   append:  "(xs,ys) : genPrefix(r) ==> (xs, ys@zs) : genPrefix(r)"

instance list :: (type)ord ..

defs
  prefix_def:        "xs <= zs  ==  (xs,zs) : genPrefix Id"

  strict_prefix_def: "xs < zs  ==  xs <= zs & xs ~= (zs::'a list)"
  

(*Constants for the <= and >= relations, used below in translations*)
constdefs
  Le :: "(nat*nat) set"
    "Le == {(x,y). x <= y}"

  Ge :: "(nat*nat) set"
    "Ge == {(x,y). y <= x}"

syntax
  pfixLe :: "[nat list, nat list] => bool"          (infixl "pfixLe" 50)
  pfixGe :: "[nat list, nat list] => bool"          (infixl "pfixGe" 50)

translations
  "xs pfixLe ys" == "(xs,ys) : genPrefix Le"

  "xs pfixGe ys" == "(xs,ys) : genPrefix Ge"


subsection{*preliminary lemmas*}

lemma Nil_genPrefix [iff]: "([], xs) : genPrefix r"
by (cut_tac genPrefix.Nil [THEN genPrefix.append], auto)

lemma genPrefix_length_le: "(xs,ys) : genPrefix r ==> length xs <= length ys"
by (erule genPrefix.induct, auto)

lemma cdlemma:
     "[| (xs', ys'): genPrefix r |]  
      ==> (ALL x xs. xs' = x#xs --> (EX y ys. ys' = y#ys & (x,y) : r & (xs, ys) : genPrefix r))"
apply (erule genPrefix.induct, blast, blast)
apply (force intro: genPrefix.append)
done

(*As usual converting it to an elimination rule is tiresome*)
lemma cons_genPrefixE [elim!]: 
     "[| (x#xs, zs): genPrefix r;   
         !!y ys. [| zs = y#ys;  (x,y) : r;  (xs, ys) : genPrefix r |] ==> P  
      |] ==> P"
by (drule cdlemma, simp, blast)

lemma Cons_genPrefix_Cons [iff]:
     "((x#xs,y#ys) : genPrefix r) = ((x,y) : r & (xs,ys) : genPrefix r)"
by (blast intro: genPrefix.prepend)


subsection{*genPrefix is a partial order*}

lemma refl_genPrefix: "reflexive r ==> reflexive (genPrefix r)"

apply (unfold refl_def, auto)
apply (induct_tac "x")
prefer 2 apply (blast intro: genPrefix.prepend)
apply (blast intro: genPrefix.Nil)
done

lemma genPrefix_refl [simp]: "reflexive r ==> (l,l) : genPrefix r"
by (erule reflD [OF refl_genPrefix UNIV_I])

lemma genPrefix_mono: "r<=s ==> genPrefix r <= genPrefix s"
apply clarify
apply (erule genPrefix.induct)
apply (auto intro: genPrefix.append)
done


(** Transitivity **)

(*A lemma for proving genPrefix_trans_O*)
lemma append_genPrefix [rule_format]:
     "ALL zs. (xs @ ys, zs) : genPrefix r --> (xs, zs) : genPrefix r"
by (induct_tac "xs", auto)

(*Lemma proving transitivity and more*)
lemma genPrefix_trans_O [rule_format]: 
     "(x, y) : genPrefix r  
      ==> ALL z. (y,z) : genPrefix s --> (x, z) : genPrefix (s O r)"
apply (erule genPrefix.induct)
  prefer 3 apply (blast dest: append_genPrefix)
 prefer 2 apply (blast intro: genPrefix.prepend, blast)
done

lemma genPrefix_trans [rule_format]:
     "[| (x,y) : genPrefix r;  (y,z) : genPrefix r;  trans r |]  
      ==> (x,z) : genPrefix r"
apply (rule trans_O_subset [THEN genPrefix_mono, THEN subsetD])
 apply assumption
apply (blast intro: genPrefix_trans_O)
done

lemma prefix_genPrefix_trans [rule_format]: 
     "[| x<=y;  (y,z) : genPrefix r |] ==> (x, z) : genPrefix r"
apply (unfold prefix_def)
apply (subst R_O_Id [symmetric], erule genPrefix_trans_O, assumption)
done

lemma genPrefix_prefix_trans [rule_format]: 
     "[| (x,y) : genPrefix r;  y<=z |] ==> (x,z) : genPrefix r"
apply (unfold prefix_def)
apply (subst Id_O_R [symmetric], erule genPrefix_trans_O, assumption)
done

lemma trans_genPrefix: "trans r ==> trans (genPrefix r)"
by (blast intro: transI genPrefix_trans)


(** Antisymmetry **)

lemma genPrefix_antisym [rule_format]:
     "[| (xs,ys) : genPrefix r;  antisym r |]  
      ==> (ys,xs) : genPrefix r --> xs = ys"
apply (erule genPrefix.induct)
  txt{*Base case*}
  apply blast
 txt{*prepend case*}
 apply (simp add: antisym_def)
txt{*append case is the hardest*}
apply clarify
apply (subgoal_tac "length zs = 0", force)
apply (drule genPrefix_length_le)+
apply (simp del: length_0_conv)
done

lemma antisym_genPrefix: "antisym r ==> antisym (genPrefix r)"
by (blast intro: antisymI genPrefix_antisym)


subsection{*recursion equations*}

lemma genPrefix_Nil [simp]: "((xs, []) : genPrefix r) = (xs = [])"
apply (induct_tac "xs")
prefer 2 apply blast
apply simp
done

lemma same_genPrefix_genPrefix [simp]: 
    "reflexive r ==> ((xs@ys, xs@zs) : genPrefix r) = ((ys,zs) : genPrefix r)"
apply (unfold refl_def)
apply (induct_tac "xs")
apply (simp_all (no_asm_simp))
done

lemma genPrefix_Cons:
     "((xs, y#ys) : genPrefix r) =  
      (xs=[] | (EX z zs. xs=z#zs & (z,y) : r & (zs,ys) : genPrefix r))"
by (case_tac "xs", auto)

lemma genPrefix_take_append:
     "[| reflexive r;  (xs,ys) : genPrefix r |]  
      ==>  (xs@zs, take (length xs) ys @ zs) : genPrefix r"
apply (erule genPrefix.induct)
apply (frule_tac [3] genPrefix_length_le)
apply (simp_all (no_asm_simp) add: diff_is_0_eq [THEN iffD2])
done

lemma genPrefix_append_both:
     "[| reflexive r;  (xs,ys) : genPrefix r;  length xs = length ys |]  
      ==>  (xs@zs, ys @ zs) : genPrefix r"
apply (drule genPrefix_take_append, assumption)
apply (simp add: take_all)
done


(*NOT suitable for rewriting since [y] has the form y#ys*)
lemma append_cons_eq: "xs @ y # ys = (xs @ [y]) @ ys"
by auto

lemma aolemma:
     "[| (xs,ys) : genPrefix r;  reflexive r |]  
      ==> length xs < length ys --> (xs @ [ys ! length xs], ys) : genPrefix r"
apply (erule genPrefix.induct)
  apply blast
 apply simp
txt{*Append case is hardest*}
apply simp
apply (frule genPrefix_length_le [THEN le_imp_less_or_eq])
apply (erule disjE)
apply (simp_all (no_asm_simp) add: neq_Nil_conv nth_append)
apply (blast intro: genPrefix.append, auto)
apply (subst append_cons_eq)
apply (blast intro: genPrefix_append_both genPrefix.append)
done

lemma append_one_genPrefix:
     "[| (xs,ys) : genPrefix r;  length xs < length ys;  reflexive r |]  
      ==> (xs @ [ys ! length xs], ys) : genPrefix r"
by (blast intro: aolemma [THEN mp])


(** Proving the equivalence with Charpentier's definition **)

lemma genPrefix_imp_nth [rule_format]:
     "ALL i ys. i < length xs  
                --> (xs, ys) : genPrefix r --> (xs ! i, ys ! i) : r"
apply (induct_tac "xs", auto)
apply (case_tac "i", auto)
done

lemma nth_imp_genPrefix [rule_format]:
     "ALL ys. length xs <= length ys   
      --> (ALL i. i < length xs --> (xs ! i, ys ! i) : r)   
      --> (xs, ys) : genPrefix r"
apply (induct_tac "xs")
apply (simp_all (no_asm_simp) add: less_Suc_eq_0_disj all_conj_distrib)
apply clarify
apply (case_tac "ys")
apply (force+)
done

lemma genPrefix_iff_nth:
     "((xs,ys) : genPrefix r) =  
      (length xs <= length ys & (ALL i. i < length xs --> (xs!i, ys!i) : r))"
apply (blast intro: genPrefix_length_le genPrefix_imp_nth nth_imp_genPrefix)
done


subsection{*The type of lists is partially ordered*}

declare reflexive_Id [iff] 
        antisym_Id [iff] 
        trans_Id [iff]

lemma prefix_refl [iff]: "xs <= (xs::'a list)"
by (simp add: prefix_def)

lemma prefix_trans: "!!xs::'a list. [| xs <= ys; ys <= zs |] ==> xs <= zs"
apply (unfold prefix_def)
apply (blast intro: genPrefix_trans)
done

lemma prefix_antisym: "!!xs::'a list. [| xs <= ys; ys <= xs |] ==> xs = ys"
apply (unfold prefix_def)
apply (blast intro: genPrefix_antisym)
done

lemma prefix_less_le: "!!xs::'a list. (xs < zs) = (xs <= zs & xs ~= zs)"
by (unfold strict_prefix_def, auto)

instance list :: (type) order
  by (intro_classes,
      (assumption | rule prefix_refl prefix_trans prefix_antisym
                     prefix_less_le)+)

(*Monotonicity of "set" operator WRT prefix*)
lemma set_mono: "xs <= ys ==> set xs <= set ys"
apply (unfold prefix_def)
apply (erule genPrefix.induct, auto)
done


(** recursion equations **)

lemma Nil_prefix [iff]: "[] <= xs"
apply (unfold prefix_def)
apply (simp add: Nil_genPrefix)
done

lemma prefix_Nil [simp]: "(xs <= []) = (xs = [])"
apply (unfold prefix_def)
apply (simp add: genPrefix_Nil)
done

lemma Cons_prefix_Cons [simp]: "(x#xs <= y#ys) = (x=y & xs<=ys)"
by (simp add: prefix_def)

lemma same_prefix_prefix [simp]: "(xs@ys <= xs@zs) = (ys <= zs)"
by (simp add: prefix_def)

lemma append_prefix [iff]: "(xs@ys <= xs) = (ys <= [])"
by (insert same_prefix_prefix [of xs ys "[]"], simp)

lemma prefix_appendI [simp]: "xs <= ys ==> xs <= ys@zs"
apply (unfold prefix_def)
apply (erule genPrefix.append)
done

lemma prefix_Cons: 
   "(xs <= y#ys) = (xs=[] | (? zs. xs=y#zs & zs <= ys))"
by (simp add: prefix_def genPrefix_Cons)

lemma append_one_prefix: 
  "[| xs <= ys; length xs < length ys |] ==> xs @ [ys ! length xs] <= ys"
apply (unfold prefix_def)
apply (simp add: append_one_genPrefix)
done

lemma prefix_length_le: "xs <= ys ==> length xs <= length ys"
apply (unfold prefix_def)
apply (erule genPrefix_length_le)
done

lemma splemma: "xs<=ys ==> xs~=ys --> length xs < length ys"
apply (unfold prefix_def)
apply (erule genPrefix.induct, auto)
done

lemma strict_prefix_length_less: "xs < ys ==> length xs < length ys"
apply (unfold strict_prefix_def)
apply (blast intro: splemma [THEN mp])
done

lemma mono_length: "mono length"
by (blast intro: monoI prefix_length_le)

(*Equivalence to the definition used in Lex/Prefix.thy*)
lemma prefix_iff: "(xs <= zs) = (EX ys. zs = xs@ys)"
apply (unfold prefix_def)
apply (auto simp add: genPrefix_iff_nth nth_append)
apply (rule_tac x = "drop (length xs) zs" in exI)
apply (rule nth_equalityI)
apply (simp_all (no_asm_simp) add: nth_append)
done

lemma prefix_snoc [simp]: "(xs <= ys@[y]) = (xs = ys@[y] | xs <= ys)"
apply (simp add: prefix_iff)
apply (rule iffI)
 apply (erule exE)
 apply (rename_tac "zs")
 apply (rule_tac xs = zs in rev_exhaust)
  apply simp
 apply clarify
 apply (simp del: append_assoc add: append_assoc [symmetric], force)
done

lemma prefix_append_iff:
     "(xs <= ys@zs) = (xs <= ys | (? us. xs = ys@us & us <= zs))"
apply (rule_tac xs = zs in rev_induct)
 apply force
apply (simp del: append_assoc add: append_assoc [symmetric], force)
done

(*Although the prefix ordering is not linear, the prefixes of a list
  are linearly ordered.*)
lemma common_prefix_linear [rule_format]:
     "!!zs::'a list. xs <= zs --> ys <= zs --> xs <= ys | ys <= xs"
by (rule_tac xs = zs in rev_induct, auto)


subsection{*pfixLe, pfixGe: properties inherited from the translations*}

(** pfixLe **)

lemma reflexive_Le [iff]: "reflexive Le"
by (unfold refl_def Le_def, auto)

lemma antisym_Le [iff]: "antisym Le"
by (unfold antisym_def Le_def, auto)

lemma trans_Le [iff]: "trans Le"
by (unfold trans_def Le_def, auto)

lemma pfixLe_refl [iff]: "x pfixLe x"
by simp

lemma pfixLe_trans: "[| x pfixLe y; y pfixLe z |] ==> x pfixLe z"
by (blast intro: genPrefix_trans)

lemma pfixLe_antisym: "[| x pfixLe y; y pfixLe x |] ==> x = y"
by (blast intro: genPrefix_antisym)

lemma prefix_imp_pfixLe: "xs<=ys ==> xs pfixLe ys"
apply (unfold prefix_def Le_def)
apply (blast intro: genPrefix_mono [THEN [2] rev_subsetD])
done

lemma reflexive_Ge [iff]: "reflexive Ge"
by (unfold refl_def Ge_def, auto)

lemma antisym_Ge [iff]: "antisym Ge"
by (unfold antisym_def Ge_def, auto)

lemma trans_Ge [iff]: "trans Ge"
by (unfold trans_def Ge_def, auto)

lemma pfixGe_refl [iff]: "x pfixGe x"
by simp

lemma pfixGe_trans: "[| x pfixGe y; y pfixGe z |] ==> x pfixGe z"
by (blast intro: genPrefix_trans)

lemma pfixGe_antisym: "[| x pfixGe y; y pfixGe x |] ==> x = y"
by (blast intro: genPrefix_antisym)

lemma prefix_imp_pfixGe: "xs<=ys ==> xs pfixGe ys"
apply (unfold prefix_def Ge_def)
apply (blast intro: genPrefix_mono [THEN [2] rev_subsetD])
done

end
