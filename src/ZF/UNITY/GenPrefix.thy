(*  Title:      ZF/UNITY/GenPrefix.thy
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

<xs,ys>:gen_prefix(r)
  if ys = xs' @ zs where length(xs) = length(xs')
  and corresponding elements of xs, xs' are pairwise related by r

Based on Lex/Prefix
*)

header{*Charpentier's Generalized Prefix Relation*}

theory GenPrefix
imports Main
begin

definition (*really belongs in ZF/Trancl*)
  part_order :: "[i, i] => o"  where
  "part_order(A, r) == refl(A,r) & trans[A](r) & antisym(r)"

consts
  gen_prefix :: "[i, i] => i"

inductive
  (* Parameter A is the domain of zs's elements *)

  domains "gen_prefix(A, r)" \<subseteq> "list(A)*list(A)"

  intros
    Nil:     "<[],[]>:gen_prefix(A, r)"

    prepend: "[| <xs,ys>:gen_prefix(A, r);  <x,y>:r; x \<in> A; y \<in> A |]
              ==> <Cons(x,xs), Cons(y,ys)>: gen_prefix(A, r)"

    append:  "[| <xs,ys>:gen_prefix(A, r); zs:list(A) |]
              ==> <xs, ys@zs>:gen_prefix(A, r)"
    type_intros app_type list.Nil list.Cons

definition
  prefix :: "i=>i"  where
  "prefix(A) == gen_prefix(A, id(A))"

definition
  strict_prefix :: "i=>i"  where
  "strict_prefix(A) == prefix(A) - id(list(A))"


(* less or equal and greater or equal over prefixes *)

abbreviation
  pfixLe :: "[i, i] => o"  (infixl "pfixLe" 50)  where
  "xs pfixLe ys == <xs, ys>:gen_prefix(nat, Le)"

abbreviation
  pfixGe :: "[i, i] => o"  (infixl "pfixGe" 50)  where
  "xs pfixGe ys == <xs, ys>:gen_prefix(nat, Ge)"


lemma reflD:
 "[| refl(A, r); x \<in> A |] ==> <x,x>:r"
apply (unfold refl_def, auto)
done

(*** preliminary lemmas ***)

lemma Nil_gen_prefix: "xs \<in> list(A) ==> <[], xs> \<in> gen_prefix(A, r)"
by (drule gen_prefix.append [OF gen_prefix.Nil], simp)
declare Nil_gen_prefix [simp]


lemma gen_prefix_length_le: "<xs,ys> \<in> gen_prefix(A, r) ==> length(xs) \<le> length(ys)"
apply (erule gen_prefix.induct)
apply (subgoal_tac [3] "ys \<in> list (A) ")
apply (auto dest: gen_prefix.dom_subset [THEN subsetD]
            intro: le_trans simp add: length_app)
done


lemma Cons_gen_prefix_aux:
  "[| <xs', ys'> \<in> gen_prefix(A, r) |]
   ==> (\<forall>x xs. x \<in> A \<longrightarrow> xs'= Cons(x,xs) \<longrightarrow>
       (\<exists>y ys. y \<in> A & ys' = Cons(y,ys) &
       <x,y>:r & <xs, ys> \<in> gen_prefix(A, r)))"
apply (erule gen_prefix.induct)
prefer 3 apply (force intro: gen_prefix.append, auto)
done

lemma Cons_gen_prefixE:
  "[| <Cons(x,xs), zs> \<in> gen_prefix(A, r);
    !!y ys. [|zs = Cons(y, ys); y \<in> A; x \<in> A; <x,y>:r;
      <xs,ys> \<in> gen_prefix(A, r) |] ==> P |] ==> P"
apply (frule gen_prefix.dom_subset [THEN subsetD], auto)
apply (blast dest: Cons_gen_prefix_aux)
done
declare Cons_gen_prefixE [elim!]

lemma Cons_gen_prefix_Cons:
"(<Cons(x,xs),Cons(y,ys)> \<in> gen_prefix(A, r))
  \<longleftrightarrow> (x \<in> A & y \<in> A & <x,y>:r & <xs,ys> \<in> gen_prefix(A, r))"
apply (auto intro: gen_prefix.prepend)
done
declare Cons_gen_prefix_Cons [iff]

(** Monotonicity of gen_prefix **)

lemma gen_prefix_mono2: "r<=s ==> gen_prefix(A, r) \<subseteq> gen_prefix(A, s)"
apply clarify
apply (frule gen_prefix.dom_subset [THEN subsetD], clarify)
apply (erule rev_mp)
apply (erule gen_prefix.induct)
apply (auto intro: gen_prefix.append)
done

lemma gen_prefix_mono1: "A<=B ==>gen_prefix(A, r) \<subseteq> gen_prefix(B, r)"
apply clarify
apply (frule gen_prefix.dom_subset [THEN subsetD], clarify)
apply (erule rev_mp)
apply (erule_tac P = "y \<in> list (A) " in rev_mp)
apply (erule_tac P = "xa \<in> list (A) " in rev_mp)
apply (erule gen_prefix.induct)
apply (simp (no_asm_simp))
apply clarify
apply (erule ConsE)+
apply (auto dest: gen_prefix.dom_subset [THEN subsetD]
            intro: gen_prefix.append list_mono [THEN subsetD])
done

lemma gen_prefix_mono: "[| A \<subseteq> B; r \<subseteq> s |] ==> gen_prefix(A, r) \<subseteq> gen_prefix(B, s)"
apply (rule subset_trans)
apply (rule gen_prefix_mono1)
apply (rule_tac [2] gen_prefix_mono2, auto)
done

(*** gen_prefix order ***)

(* reflexivity *)
lemma refl_gen_prefix: "refl(A, r) ==> refl(list(A), gen_prefix(A, r))"
apply (unfold refl_def, auto)
apply (induct_tac "x", auto)
done
declare refl_gen_prefix [THEN reflD, simp]

(* Transitivity *)
(* A lemma for proving gen_prefix_trans_comp *)

lemma append_gen_prefix [rule_format (no_asm)]: "xs \<in> list(A) ==>
   \<forall>zs. <xs @ ys, zs> \<in> gen_prefix(A, r) \<longrightarrow> <xs, zs>: gen_prefix(A, r)"
apply (erule list.induct)
apply (auto dest: gen_prefix.dom_subset [THEN subsetD])
done

(* Lemma proving transitivity and more*)

lemma gen_prefix_trans_comp [rule_format (no_asm)]:
     "<x, y>: gen_prefix(A, r) ==>
   (\<forall>z \<in> list(A). <y,z> \<in> gen_prefix(A, s)\<longrightarrow><x, z> \<in> gen_prefix(A, s O r))"
apply (erule gen_prefix.induct)
apply (auto elim: ConsE simp add: Nil_gen_prefix)
apply (subgoal_tac "ys \<in> list (A) ")
prefer 2 apply (blast dest: gen_prefix.dom_subset [THEN subsetD])
apply (drule_tac xs = ys and r = s in append_gen_prefix, auto)
done

lemma trans_comp_subset: "trans(r) ==> r O r \<subseteq> r"
by (auto dest: transD)

lemma trans_gen_prefix: "trans(r) ==> trans(gen_prefix(A,r))"
apply (simp (no_asm) add: trans_def)
apply clarify
apply (rule trans_comp_subset [THEN gen_prefix_mono2, THEN subsetD], assumption)
apply (rule gen_prefix_trans_comp)
apply (auto dest: gen_prefix.dom_subset [THEN subsetD])
done

lemma trans_on_gen_prefix:
 "trans(r) ==> trans[list(A)](gen_prefix(A, r))"
apply (drule_tac A = A in trans_gen_prefix)
apply (unfold trans_def trans_on_def, blast)
done

lemma prefix_gen_prefix_trans:
    "[| <x,y> \<in> prefix(A); <y, z> \<in> gen_prefix(A, r); r<=A*A |]
      ==>  <x, z> \<in> gen_prefix(A, r)"
apply (unfold prefix_def)
apply (rule_tac P = "%r. <x,z> \<in> gen_prefix (A, r) " in right_comp_id [THEN subst])
apply (blast dest: gen_prefix_trans_comp gen_prefix.dom_subset [THEN subsetD])+
done


lemma gen_prefix_prefix_trans:
"[| <x,y> \<in> gen_prefix(A,r); <y, z> \<in> prefix(A); r<=A*A |]
  ==>  <x, z> \<in> gen_prefix(A, r)"
apply (unfold prefix_def)
apply (rule_tac P = "%r. <x,z> \<in> gen_prefix (A, r) " in left_comp_id [THEN subst])
apply (blast dest: gen_prefix_trans_comp gen_prefix.dom_subset [THEN subsetD])+
done

(** Antisymmetry **)

lemma nat_le_lemma [rule_format]: "n \<in> nat ==> \<forall>b \<in> nat. n #+ b \<le> n \<longrightarrow> b = 0"
by (induct_tac "n", auto)

lemma antisym_gen_prefix: "antisym(r) ==> antisym(gen_prefix(A, r))"
apply (simp (no_asm) add: antisym_def)
apply (rule impI [THEN allI, THEN allI])
apply (erule gen_prefix.induct, blast)
apply (simp add: antisym_def, blast)
txt{*append case is hardest*}
apply clarify
apply (subgoal_tac "length (zs) = 0")
apply (subgoal_tac "ys \<in> list (A) ")
prefer 2 apply (blast dest: gen_prefix.dom_subset [THEN subsetD])
apply (drule_tac psi = "<ys @ zs, xs> \<in> gen_prefix (A,r) " in asm_rl)
apply simp
apply (subgoal_tac "length (ys @ zs) = length (ys) #+ length (zs) &ys \<in> list (A) &xs \<in> list (A) ")
prefer 2 apply (blast intro: length_app dest: gen_prefix.dom_subset [THEN subsetD])
apply (drule gen_prefix_length_le)+
apply clarify
apply simp
apply (drule_tac j = "length (xs) " in le_trans)
apply blast
apply (auto intro: nat_le_lemma)
done

(*** recursion equations ***)

lemma gen_prefix_Nil: "xs \<in> list(A) ==> <xs, []> \<in> gen_prefix(A,r) \<longleftrightarrow> (xs = [])"
by (induct_tac "xs", auto)
declare gen_prefix_Nil [simp]

lemma same_gen_prefix_gen_prefix:
 "[| refl(A, r);  xs \<in> list(A) |] ==>
    <xs@ys, xs@zs>: gen_prefix(A, r) \<longleftrightarrow> <ys,zs> \<in> gen_prefix(A, r)"
apply (unfold refl_def)
apply (induct_tac "xs")
apply (simp_all (no_asm_simp))
done
declare same_gen_prefix_gen_prefix [simp]

lemma gen_prefix_Cons: "[| xs \<in> list(A); ys \<in> list(A); y \<in> A |] ==>
    <xs, Cons(y,ys)> \<in> gen_prefix(A,r)  \<longleftrightarrow>
      (xs=[] | (\<exists>z zs. xs=Cons(z,zs) & z \<in> A & <z,y>:r & <zs,ys> \<in> gen_prefix(A,r)))"
apply (induct_tac "xs", auto)
done

lemma gen_prefix_take_append: "[| refl(A,r);  <xs,ys> \<in> gen_prefix(A, r); zs \<in> list(A) |]
      ==>  <xs@zs, take(length(xs), ys) @ zs> \<in> gen_prefix(A, r)"
apply (erule gen_prefix.induct)
apply (simp (no_asm_simp))
apply (frule_tac [!] gen_prefix.dom_subset [THEN subsetD], auto)
apply (frule gen_prefix_length_le)
apply (subgoal_tac "take (length (xs), ys) \<in> list (A) ")
apply (simp_all (no_asm_simp) add: diff_is_0_iff [THEN iffD2] take_type)
done

lemma gen_prefix_append_both: "[| refl(A, r);  <xs,ys> \<in> gen_prefix(A,r);
         length(xs) = length(ys); zs \<in> list(A) |]
      ==>  <xs@zs, ys @ zs> \<in> gen_prefix(A, r)"
apply (drule_tac zs = zs in gen_prefix_take_append, assumption+)
apply (subgoal_tac "take (length (xs), ys) =ys")
apply (auto intro!: take_all dest: gen_prefix.dom_subset [THEN subsetD])
done

(*NOT suitable for rewriting since [y] has the form y#ys*)
lemma append_cons_conv: "xs \<in> list(A) ==> xs @ Cons(y, ys) = (xs @ [y]) @ ys"
by (auto simp add: app_assoc)

lemma append_one_gen_prefix_lemma [rule_format]:
     "[| <xs,ys> \<in> gen_prefix(A, r);  refl(A, r) |]
      ==> length(xs) < length(ys) \<longrightarrow>
          <xs @ [nth(length(xs), ys)], ys> \<in> gen_prefix(A, r)"
apply (erule gen_prefix.induct, blast)
apply (frule gen_prefix.dom_subset [THEN subsetD], clarify)
apply (simp_all add: length_type)
(* Append case is hardest *)
apply (frule gen_prefix_length_le [THEN le_iff [THEN iffD1]])
apply (frule gen_prefix.dom_subset [THEN subsetD], clarify)
apply (subgoal_tac "length (xs) :nat&length (ys) :nat &length (zs) :nat")
prefer 2 apply (blast intro: length_type, clarify)
apply (simp_all add: nth_append length_type length_app)
apply (rule conjI)
apply (blast intro: gen_prefix.append)
apply (erule_tac V = "length (xs) < length (ys) \<longrightarrow>?u" in thin_rl)
apply (erule_tac a = zs in list.cases, auto)
apply (rule_tac P1 = "%x. <?u (x), ?v>:?w" in nat_diff_split [THEN iffD2])
apply auto
apply (simplesubst append_cons_conv)
apply (rule_tac [2] gen_prefix.append)
apply (auto elim: ConsE simp add: gen_prefix_append_both)
done

lemma append_one_gen_prefix: "[| <xs,ys>: gen_prefix(A, r);  length(xs) < length(ys);  refl(A, r) |]
      ==> <xs @ [nth(length(xs), ys)], ys> \<in> gen_prefix(A, r)"
apply (blast intro: append_one_gen_prefix_lemma)
done


(** Proving the equivalence with Charpentier's definition **)

lemma gen_prefix_imp_nth_lemma [rule_format]: "xs \<in> list(A) ==>
  \<forall>ys \<in> list(A). \<forall>i \<in> nat. i < length(xs)
          \<longrightarrow> <xs, ys>: gen_prefix(A, r) \<longrightarrow> <nth(i, xs), nth(i, ys)>:r"
apply (induct_tac "xs", simp, clarify)
apply simp
apply (erule natE, auto)
done

lemma gen_prefix_imp_nth: "[| <xs,ys> \<in> gen_prefix(A,r); i < length(xs)|]
      ==> <nth(i, xs), nth(i, ys)>:r"
apply (cut_tac A = A in gen_prefix.dom_subset)
apply (rule gen_prefix_imp_nth_lemma)
apply (auto simp add: lt_nat_in_nat)
done

lemma nth_imp_gen_prefix [rule_format]: "xs \<in> list(A) ==>
  \<forall>ys \<in> list(A). length(xs) \<le> length(ys)
      \<longrightarrow> (\<forall>i. i < length(xs) \<longrightarrow> <nth(i, xs), nth(i,ys)>:r)
      \<longrightarrow> <xs, ys> \<in> gen_prefix(A, r)"
apply (induct_tac "xs")
apply (simp_all (no_asm_simp))
apply clarify
apply (erule_tac a = ys in list.cases, simp)
apply (force intro!: nat_0_le simp add: lt_nat_in_nat)
done

lemma gen_prefix_iff_nth: "(<xs,ys> \<in> gen_prefix(A,r)) \<longleftrightarrow>
      (xs \<in> list(A) & ys \<in> list(A) & length(xs) \<le> length(ys) &
      (\<forall>i. i < length(xs) \<longrightarrow> <nth(i,xs), nth(i, ys)>: r))"
apply (rule iffI)
apply (frule gen_prefix.dom_subset [THEN subsetD])
apply (frule gen_prefix_length_le, auto)
apply (rule_tac [2] nth_imp_gen_prefix)
apply (drule gen_prefix_imp_nth)
apply (auto simp add: lt_nat_in_nat)
done

(** prefix is a partial order: **)

lemma refl_prefix: "refl(list(A), prefix(A))"
apply (unfold prefix_def)
apply (rule refl_gen_prefix)
apply (auto simp add: refl_def)
done
declare refl_prefix [THEN reflD, simp]

lemma trans_prefix: "trans(prefix(A))"
apply (unfold prefix_def)
apply (rule trans_gen_prefix)
apply (auto simp add: trans_def)
done

lemmas prefix_trans = trans_prefix [THEN transD]

lemma trans_on_prefix: "trans[list(A)](prefix(A))"
apply (unfold prefix_def)
apply (rule trans_on_gen_prefix)
apply (auto simp add: trans_def)
done

lemmas prefix_trans_on = trans_on_prefix [THEN trans_onD]

(* Monotonicity of "set" operator WRT prefix *)

lemma set_of_list_prefix_mono:
"<xs,ys> \<in> prefix(A) ==> set_of_list(xs) \<subseteq> set_of_list(ys)"

apply (unfold prefix_def)
apply (erule gen_prefix.induct)
apply (subgoal_tac [3] "xs \<in> list (A) &ys \<in> list (A) ")
prefer 4 apply (blast dest: gen_prefix.dom_subset [THEN subsetD])
apply (auto simp add: set_of_list_append)
done

(** recursion equations **)

lemma Nil_prefix: "xs \<in> list(A) ==> <[],xs> \<in> prefix(A)"

apply (unfold prefix_def)
apply (simp (no_asm_simp) add: Nil_gen_prefix)
done
declare Nil_prefix [simp]


lemma prefix_Nil: "<xs, []> \<in> prefix(A) \<longleftrightarrow> (xs = [])"

apply (unfold prefix_def, auto)
apply (frule gen_prefix.dom_subset [THEN subsetD])
apply (drule_tac psi = "<xs, []> \<in> gen_prefix (A, id (A))" in asm_rl)
apply (simp add: gen_prefix_Nil)
done
declare prefix_Nil [iff]

lemma Cons_prefix_Cons:
"<Cons(x,xs), Cons(y,ys)> \<in> prefix(A) \<longleftrightarrow> (x=y & <xs,ys> \<in> prefix(A) & y \<in> A)"
apply (unfold prefix_def, auto)
done
declare Cons_prefix_Cons [iff]

lemma same_prefix_prefix:
"xs \<in> list(A)==> <xs@ys,xs@zs> \<in> prefix(A) \<longleftrightarrow> (<ys,zs> \<in> prefix(A))"
apply (unfold prefix_def)
apply (subgoal_tac "refl (A,id (A))")
apply (simp (no_asm_simp))
apply (auto simp add: refl_def)
done
declare same_prefix_prefix [simp]

lemma same_prefix_prefix_Nil: "xs \<in> list(A) ==> <xs@ys,xs> \<in> prefix(A) \<longleftrightarrow> (<ys,[]> \<in> prefix(A))"
apply (rule_tac P = "%x. <?u, x>:?v \<longleftrightarrow> ?w (x) " in app_right_Nil [THEN subst])
apply (rule_tac [2] same_prefix_prefix, auto)
done
declare same_prefix_prefix_Nil [simp]

lemma prefix_appendI:
"[| <xs,ys> \<in> prefix(A); zs \<in> list(A) |] ==> <xs,ys@zs> \<in> prefix(A)"
apply (unfold prefix_def)
apply (erule gen_prefix.append, assumption)
done
declare prefix_appendI [simp]

lemma prefix_Cons:
"[| xs \<in> list(A); ys \<in> list(A); y \<in> A |] ==>
  <xs,Cons(y,ys)> \<in> prefix(A) \<longleftrightarrow>
  (xs=[] | (\<exists>zs. xs=Cons(y,zs) & <zs,ys> \<in> prefix(A)))"
apply (unfold prefix_def)
apply (auto simp add: gen_prefix_Cons)
done

lemma append_one_prefix:
  "[| <xs,ys> \<in> prefix(A); length(xs) < length(ys) |]
  ==> <xs @ [nth(length(xs),ys)], ys> \<in> prefix(A)"
apply (unfold prefix_def)
apply (subgoal_tac "refl (A, id (A))")
apply (simp (no_asm_simp) add: append_one_gen_prefix)
apply (auto simp add: refl_def)
done

lemma prefix_length_le:
"<xs,ys> \<in> prefix(A) ==> length(xs) \<le> length(ys)"
apply (unfold prefix_def)
apply (blast dest: gen_prefix_length_le)
done

lemma prefix_type: "prefix(A)<=list(A)*list(A)"
apply (unfold prefix_def)
apply (blast intro!: gen_prefix.dom_subset)
done

lemma strict_prefix_type:
"strict_prefix(A) \<subseteq> list(A)*list(A)"
apply (unfold strict_prefix_def)
apply (blast intro!: prefix_type [THEN subsetD])
done

lemma strict_prefix_length_lt_aux:
     "<xs,ys> \<in> prefix(A) ==> xs\<noteq>ys \<longrightarrow> length(xs) < length(ys)"
apply (unfold prefix_def)
apply (erule gen_prefix.induct, clarify)
apply (subgoal_tac [!] "ys \<in> list(A) & xs \<in> list(A)")
apply (auto dest: gen_prefix.dom_subset [THEN subsetD]
            simp add: length_type)
apply (subgoal_tac "length (zs) =0")
apply (drule_tac [2] not_lt_imp_le)
apply (rule_tac [5] j = "length (ys) " in lt_trans2)
apply auto
done

lemma strict_prefix_length_lt:
     "<xs,ys>:strict_prefix(A) ==> length(xs) < length(ys)"
apply (unfold strict_prefix_def)
apply (rule strict_prefix_length_lt_aux [THEN mp])
apply (auto dest: prefix_type [THEN subsetD])
done

(*Equivalence to the definition used in Lex/Prefix.thy*)
lemma prefix_iff:
    "<xs,zs> \<in> prefix(A) \<longleftrightarrow> (\<exists>ys \<in> list(A). zs = xs@ys) & xs \<in> list(A)"
apply (unfold prefix_def)
apply (auto simp add: gen_prefix_iff_nth lt_nat_in_nat nth_append nth_type app_type length_app)
apply (subgoal_tac "drop (length (xs), zs) \<in> list (A) ")
apply (rule_tac x = "drop (length (xs), zs) " in bexI)
apply safe
 prefer 2 apply (simp add: length_type drop_type)
apply (rule nth_equalityI)
apply (simp_all (no_asm_simp) add: nth_append app_type drop_type length_app length_drop)
apply (rule nat_diff_split [THEN iffD2], simp_all, clarify)
apply (drule_tac i = "length (zs) " in leI)
apply (force simp add: le_subset_iff, safe)
apply (subgoal_tac "length (xs) #+ (i #- length (xs)) = i")
apply (subst nth_drop)
apply (simp_all (no_asm_simp) add: leI split add: nat_diff_split)
done

lemma prefix_snoc:
"[|xs \<in> list(A); ys \<in> list(A); y \<in> A |] ==>
   <xs, ys@[y]> \<in> prefix(A) \<longleftrightarrow> (xs = ys@[y] | <xs,ys> \<in> prefix(A))"
apply (simp (no_asm) add: prefix_iff)
apply (rule iffI, clarify)
apply (erule_tac xs = ysa in rev_list_elim, simp)
apply (simp add: app_type app_assoc [symmetric])
apply (auto simp add: app_assoc app_type)
done
declare prefix_snoc [simp]

lemma prefix_append_iff [rule_format]: "zs \<in> list(A) ==> \<forall>xs \<in> list(A). \<forall>ys \<in> list(A).
   (<xs, ys@zs> \<in> prefix(A)) \<longleftrightarrow>
  (<xs,ys> \<in> prefix(A) | (\<exists>us. xs = ys@us & <us,zs> \<in> prefix(A)))"
apply (erule list_append_induct, force, clarify)
apply (rule iffI)
apply (simp add: add: app_assoc [symmetric])
apply (erule disjE)
apply (rule disjI2)
apply (rule_tac x = "y @ [x]" in exI)
apply (simp add: add: app_assoc [symmetric], force+)
done


(*Although the prefix ordering is not linear, the prefixes of a list
  are linearly ordered.*)
lemma common_prefix_linear_lemma [rule_format]: "[| zs \<in> list(A); xs \<in> list(A); ys \<in> list(A) |]
   ==> <xs, zs> \<in> prefix(A) \<longrightarrow> <ys,zs> \<in> prefix(A)
  \<longrightarrow><xs,ys> \<in> prefix(A) | <ys,xs> \<in> prefix(A)"
apply (erule list_append_induct, auto)
done

lemma common_prefix_linear: "[|<xs, zs> \<in> prefix(A); <ys,zs> \<in> prefix(A) |]
      ==> <xs,ys> \<in> prefix(A) | <ys,xs> \<in> prefix(A)"
apply (cut_tac prefix_type)
apply (blast del: disjCI intro: common_prefix_linear_lemma)
done


(*** pfixLe, pfixGe \<in> properties inherited from the translations ***)



(** pfixLe **)

lemma refl_Le: "refl(nat,Le)"

apply (unfold refl_def, auto)
done
declare refl_Le [simp]

lemma antisym_Le: "antisym(Le)"
apply (unfold antisym_def)
apply (auto intro: le_anti_sym)
done
declare antisym_Le [simp]

lemma trans_on_Le: "trans[nat](Le)"
apply (unfold trans_on_def, auto)
apply (blast intro: le_trans)
done
declare trans_on_Le [simp]

lemma trans_Le: "trans(Le)"
apply (unfold trans_def, auto)
apply (blast intro: le_trans)
done
declare trans_Le [simp]

lemma part_order_Le: "part_order(nat,Le)"
by (unfold part_order_def, auto)
declare part_order_Le [simp]

lemma pfixLe_refl: "x \<in> list(nat) ==> x pfixLe x"
by (blast intro: refl_gen_prefix [THEN reflD] refl_Le)
declare pfixLe_refl [simp]

lemma pfixLe_trans: "[| x pfixLe y; y pfixLe z |] ==> x pfixLe z"
by (blast intro: trans_gen_prefix [THEN transD] trans_Le)

lemma pfixLe_antisym: "[| x pfixLe y; y pfixLe x |] ==> x = y"
by (blast intro: antisym_gen_prefix [THEN antisymE] antisym_Le)


lemma prefix_imp_pfixLe:
"<xs,ys>:prefix(nat)==> xs pfixLe ys"

apply (unfold prefix_def)
apply (rule gen_prefix_mono [THEN subsetD], auto)
done

lemma refl_Ge: "refl(nat, Ge)"
by (unfold refl_def Ge_def, auto)
declare refl_Ge [iff]

lemma antisym_Ge: "antisym(Ge)"
apply (unfold antisym_def Ge_def)
apply (auto intro: le_anti_sym)
done
declare antisym_Ge [iff]

lemma trans_Ge: "trans(Ge)"
apply (unfold trans_def Ge_def)
apply (auto intro: le_trans)
done
declare trans_Ge [iff]

lemma pfixGe_refl: "x \<in> list(nat) ==> x pfixGe x"
by (blast intro: refl_gen_prefix [THEN reflD])
declare pfixGe_refl [simp]

lemma pfixGe_trans: "[| x pfixGe y; y pfixGe z |] ==> x pfixGe z"
by (blast intro: trans_gen_prefix [THEN transD])

lemma pfixGe_antisym: "[| x pfixGe y; y pfixGe x |] ==> x = y"
by (blast intro: antisym_gen_prefix [THEN antisymE])

lemma prefix_imp_pfixGe:
  "<xs,ys>:prefix(nat) ==> xs pfixGe ys"
apply (unfold prefix_def Ge_def)
apply (rule gen_prefix_mono [THEN subsetD], auto)
done
(* Added by Sidi \<in> prefix and take *)

lemma prefix_imp_take:
"<xs, ys> \<in> prefix(A) ==> xs = take(length(xs), ys)"

apply (unfold prefix_def)
apply (erule gen_prefix.induct)
apply (subgoal_tac [3] "length (xs) :nat")
apply (auto dest: gen_prefix.dom_subset [THEN subsetD] simp add: length_type)
apply (frule gen_prefix.dom_subset [THEN subsetD])
apply (frule gen_prefix_length_le)
apply (auto simp add: take_append)
apply (subgoal_tac "length (xs) #- length (ys) =0")
apply (simp_all (no_asm_simp) add: diff_is_0_iff)
done

lemma prefix_length_equal: "[|<xs,ys> \<in> prefix(A); length(xs)=length(ys)|] ==> xs = ys"
apply (cut_tac A = A in prefix_type)
apply (drule subsetD, auto)
apply (drule prefix_imp_take)
apply (erule trans, simp)
done

lemma prefix_length_le_equal: "[|<xs,ys> \<in> prefix(A); length(ys) \<le> length(xs)|] ==> xs = ys"
by (blast intro: prefix_length_equal le_anti_sym prefix_length_le)

lemma take_prefix [rule_format]: "xs \<in> list(A) ==> \<forall>n \<in> nat. <take(n, xs), xs> \<in> prefix(A)"
apply (unfold prefix_def)
apply (erule list.induct, simp, clarify)
apply (erule natE, auto)
done

lemma prefix_take_iff: "<xs,ys> \<in> prefix(A) \<longleftrightarrow> (xs=take(length(xs), ys) & xs \<in> list(A) & ys \<in> list(A))"
apply (rule iffI)
apply (frule prefix_type [THEN subsetD])
apply (blast intro: prefix_imp_take, clarify)
apply (erule ssubst)
apply (blast intro: take_prefix length_type)
done

lemma prefix_imp_nth: "[| <xs,ys> \<in> prefix(A); i < length(xs)|] ==> nth(i,xs) = nth(i,ys)"
by (auto dest!: gen_prefix_imp_nth simp add: prefix_def)

lemma nth_imp_prefix:
     "[|xs \<in> list(A); ys \<in> list(A); length(xs) \<le> length(ys);
        !!i. i < length(xs) ==> nth(i, xs) = nth(i,ys)|]
      ==> <xs,ys> \<in> prefix(A)"
apply (auto simp add: prefix_def nth_imp_gen_prefix)
apply (auto intro!: nth_imp_gen_prefix simp add: prefix_def)
apply (blast intro: nth_type lt_trans2)
done


lemma length_le_prefix_imp_prefix: "[|length(xs) \<le> length(ys);
        <xs,zs> \<in> prefix(A); <ys,zs> \<in> prefix(A)|] ==> <xs,ys> \<in> prefix(A)"
apply (cut_tac A = A in prefix_type)
apply (rule nth_imp_prefix, blast, blast)
 apply assumption
apply (rule_tac b = "nth (i,zs)" in trans)
 apply (blast intro: prefix_imp_nth)
apply (blast intro: sym prefix_imp_nth prefix_length_le lt_trans2)
done

end
