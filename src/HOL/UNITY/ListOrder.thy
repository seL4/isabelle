(*  Title:      HOL/UNITY/ListOrder.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Lists are partially ordered by Charpentier's Generalized Prefix Relation
   (xs,ys) : genPrefix(r)
     if ys = xs' @ zs where length xs = length xs'
     and corresponding elements of xs, xs' are pairwise related by r

Also overloads <= and < for lists!
*)

header {*The Prefix Ordering on Lists*}

theory ListOrder
imports Main
begin

inductive_set
  genPrefix :: "('a * 'a)set => ('a list * 'a list)set"
  for r :: "('a * 'a)set"
 where
   Nil:     "([],[]) : genPrefix(r)"

 | prepend: "[| (xs,ys) : genPrefix(r);  (x,y) : r |] ==>
             (x#xs, y#ys) : genPrefix(r)"

 | append:  "(xs,ys) : genPrefix(r) ==> (xs, ys@zs) : genPrefix(r)"

instantiation list :: (type) ord 
begin

definition
  prefix_def:        "xs <= zs \<longleftrightarrow>  (xs, zs) : genPrefix Id"

definition
  strict_prefix_def: "xs < zs  \<longleftrightarrow>  xs \<le> zs \<and> \<not> zs \<le> (xs :: 'a list)"

instance ..  

(*Constants for the <= and >= relations, used below in translations*)

end

definition Le :: "(nat*nat) set" where
    "Le == {(x,y). x <= y}"

definition  Ge :: "(nat*nat) set" where
    "Ge == {(x,y). y <= x}"

abbreviation
  pfixLe :: "[nat list, nat list] => bool"  (infixl "pfixLe" 50)  where
  "xs pfixLe ys == (xs,ys) : genPrefix Le"

abbreviation
  pfixGe :: "[nat list, nat list] => bool"  (infixl "pfixGe" 50)  where
  "xs pfixGe ys == (xs,ys) : genPrefix Ge"


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

lemma refl_genPrefix: "refl r ==> refl (genPrefix r)"
apply (unfold refl_on_def, auto)
apply (induct_tac "x")
prefer 2 apply (blast intro: genPrefix.prepend)
apply (blast intro: genPrefix.Nil)
done

lemma genPrefix_refl [simp]: "refl r ==> (l,l) : genPrefix r"
by (erule refl_onD [OF refl_genPrefix UNIV_I])

lemma genPrefix_mono: "r<=s ==> genPrefix r <= genPrefix s"
apply clarify
apply (erule genPrefix.induct)
apply (auto intro: genPrefix.append)
done


(** Transitivity **)

(*A lemma for proving genPrefix_trans_O*)
lemma append_genPrefix:
     "(xs @ ys, zs) : genPrefix r \<Longrightarrow> (xs, zs) : genPrefix r"
  by (induct xs arbitrary: zs) auto

(*Lemma proving transitivity and more*)
lemma genPrefix_trans_O:
  assumes "(x, y) : genPrefix r"
  shows "\<And>z. (y, z) : genPrefix s \<Longrightarrow> (x, z) : genPrefix (r O s)"
  apply (atomize (full))
  using assms
  apply induct
    apply blast
   apply (blast intro: genPrefix.prepend)
  apply (blast dest: append_genPrefix)
  done

lemma genPrefix_trans:
  "(x, y) : genPrefix r \<Longrightarrow> (y, z) : genPrefix r \<Longrightarrow> trans r
    \<Longrightarrow> (x, z) : genPrefix r"
  apply (rule trans_O_subset [THEN genPrefix_mono, THEN subsetD])
   apply assumption
  apply (blast intro: genPrefix_trans_O)
  done

lemma prefix_genPrefix_trans:
  "[| x<=y;  (y,z) : genPrefix r |] ==> (x, z) : genPrefix r"
apply (unfold prefix_def)
apply (drule genPrefix_trans_O, assumption)
apply simp
done

lemma genPrefix_prefix_trans:
  "[| (x,y) : genPrefix r;  y<=z |] ==> (x,z) : genPrefix r"
apply (unfold prefix_def)
apply (drule genPrefix_trans_O, assumption)
apply simp
done

lemma trans_genPrefix: "trans r ==> trans (genPrefix r)"
by (blast intro: transI genPrefix_trans)


(** Antisymmetry **)

lemma genPrefix_antisym:
  assumes 1: "(xs, ys) : genPrefix r"
    and 2: "antisym r"
    and 3: "(ys, xs) : genPrefix r"
  shows "xs = ys"
  using 1 3
proof induct
  case Nil
  then show ?case by blast
next
  case prepend
  then show ?case using 2 by (simp add: antisym_def)
next
  case (append xs ys zs)
  then show ?case
    apply -
    apply (subgoal_tac "length zs = 0", force)
    apply (drule genPrefix_length_le)+
    apply (simp del: length_0_conv)
    done
qed

lemma antisym_genPrefix: "antisym r ==> antisym (genPrefix r)"
  by (blast intro: antisymI genPrefix_antisym)


subsection{*recursion equations*}

lemma genPrefix_Nil [simp]: "((xs, []) : genPrefix r) = (xs = [])"
  by (induct xs) auto

lemma same_genPrefix_genPrefix [simp]: 
    "refl r ==> ((xs@ys, xs@zs) : genPrefix r) = ((ys,zs) : genPrefix r)"
  by (induct xs) (simp_all add: refl_on_def)

lemma genPrefix_Cons:
     "((xs, y#ys) : genPrefix r) =  
      (xs=[] | (EX z zs. xs=z#zs & (z,y) : r & (zs,ys) : genPrefix r))"
  by (cases xs) auto

lemma genPrefix_take_append:
     "[| refl r;  (xs,ys) : genPrefix r |]  
      ==>  (xs@zs, take (length xs) ys @ zs) : genPrefix r"
apply (erule genPrefix.induct)
apply (frule_tac [3] genPrefix_length_le)
apply (simp_all (no_asm_simp) add: diff_is_0_eq [THEN iffD2])
done

lemma genPrefix_append_both:
     "[| refl r;  (xs,ys) : genPrefix r;  length xs = length ys |]  
      ==>  (xs@zs, ys @ zs) : genPrefix r"
apply (drule genPrefix_take_append, assumption)
apply simp
done


(*NOT suitable for rewriting since [y] has the form y#ys*)
lemma append_cons_eq: "xs @ y # ys = (xs @ [y]) @ ys"
by auto

lemma aolemma:
     "[| (xs,ys) : genPrefix r;  refl r |]  
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
apply (subst append_cons_eq, fast intro: genPrefix_append_both genPrefix.append)
done

lemma append_one_genPrefix:
     "[| (xs,ys) : genPrefix r;  length xs < length ys;  refl r |]  
      ==> (xs @ [ys ! length xs], ys) : genPrefix r"
by (blast intro: aolemma [THEN mp])


(** Proving the equivalence with Charpentier's definition **)

lemma genPrefix_imp_nth:
    "i < length xs \<Longrightarrow> (xs, ys) : genPrefix r \<Longrightarrow> (xs ! i, ys ! i) : r"
  apply (induct xs arbitrary: i ys)
   apply auto
  apply (case_tac i)
   apply auto
  done

lemma nth_imp_genPrefix:
  "length xs <= length ys \<Longrightarrow>
     (\<forall>i. i < length xs --> (xs ! i, ys ! i) : r) \<Longrightarrow>
     (xs, ys) : genPrefix r"
  apply (induct xs arbitrary: ys)
   apply (simp_all add: less_Suc_eq_0_disj all_conj_distrib)
  apply (case_tac ys)
   apply (force+)
  done

lemma genPrefix_iff_nth:
     "((xs,ys) : genPrefix r) =  
      (length xs <= length ys & (ALL i. i < length xs --> (xs!i, ys!i) : r))"
apply (blast intro: genPrefix_length_le genPrefix_imp_nth nth_imp_genPrefix)
done


subsection{*The type of lists is partially ordered*}

declare refl_Id [iff] 
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

lemma prefix_less_le_not_le: "!!xs::'a list. (xs < zs) = (xs <= zs & \<not> zs \<le> xs)"
by (unfold strict_prefix_def, auto)

instance list :: (type) order
  by (intro_classes,
      (assumption | rule prefix_refl prefix_trans prefix_antisym
                     prefix_less_le_not_le)+)

(*Monotonicity of "set" operator WRT prefix*)
lemma set_mono: "xs <= ys ==> set xs <= set ys"
apply (unfold prefix_def)
apply (erule genPrefix.induct, auto)
done


(** recursion equations **)

lemma Nil_prefix [iff]: "[] <= xs"
by (simp add: prefix_def)

lemma prefix_Nil [simp]: "(xs <= []) = (xs = [])"
by (simp add: prefix_def)

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
lemma common_prefix_linear:
  fixes xs ys zs :: "'a list"
  shows "xs <= zs \<Longrightarrow> ys <= zs \<Longrightarrow> xs <= ys | ys <= xs"
  by (induct zs rule: rev_induct) auto

subsection{*pfixLe, pfixGe: properties inherited from the translations*}

(** pfixLe **)

lemma refl_Le [iff]: "refl Le"
by (unfold refl_on_def Le_def, auto)

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

lemma refl_Ge [iff]: "refl Ge"
by (unfold refl_on_def Ge_def, auto)

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
