(*  Title:      ZF/UNITY/GenPrefix.thy
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

\<langle>xs,ys\<rangle>:gen_prefix(r)
  if ys = xs' @ zs where length(xs) = length(xs')
  and corresponding elements of xs, xs' are pairwise related by r

Based on Lex/Prefix
*)

section\<open>Charpentier's Generalized Prefix Relation\<close>

theory GenPrefix
imports ZF
begin

definition (*really belongs in ZF/Trancl*)
  part_order :: "[i, i] \<Rightarrow> o"  where
  "part_order(A, r) \<equiv> refl(A,r) \<and> trans[A](r) \<and> antisym(r)"

consts
  gen_prefix :: "[i, i] \<Rightarrow> i"

inductive
  (* Parameter A is the domain of zs's elements *)

  domains "gen_prefix(A, r)" \<subseteq> "list(A)*list(A)"

  intros
    Nil:     "<[],[]>:gen_prefix(A, r)"

    prepend: "\<lbrakk>\<langle>xs,ys\<rangle>:gen_prefix(A, r);  \<langle>x,y\<rangle>:r; x \<in> A; y \<in> A\<rbrakk>
              \<Longrightarrow> <Cons(x,xs), Cons(y,ys)>: gen_prefix(A, r)"

    append:  "\<lbrakk>\<langle>xs,ys\<rangle>:gen_prefix(A, r); zs:list(A)\<rbrakk>
              \<Longrightarrow> <xs, ys@zs>:gen_prefix(A, r)"
    type_intros app_type list.Nil list.Cons

definition
  prefix :: "i\<Rightarrow>i"  where
  "prefix(A) \<equiv> gen_prefix(A, id(A))"

definition
  strict_prefix :: "i\<Rightarrow>i"  where
  "strict_prefix(A) \<equiv> prefix(A) - id(list(A))"


(* less or equal and greater or equal over prefixes *)

abbreviation
  pfixLe :: "[i, i] \<Rightarrow> o"  (infixl \<open>pfixLe\<close> 50)  where
  "xs pfixLe ys \<equiv> \<langle>xs, ys\<rangle>:gen_prefix(nat, Le)"

abbreviation
  pfixGe :: "[i, i] \<Rightarrow> o"  (infixl \<open>pfixGe\<close> 50)  where
  "xs pfixGe ys \<equiv> \<langle>xs, ys\<rangle>:gen_prefix(nat, Ge)"


lemma reflD:
 "\<lbrakk>refl(A, r); x \<in> A\<rbrakk> \<Longrightarrow> \<langle>x,x\<rangle>:r"
apply (unfold refl_def, auto)
done

(*** preliminary lemmas ***)

lemma Nil_gen_prefix: "xs \<in> list(A) \<Longrightarrow> <[], xs> \<in> gen_prefix(A, r)"
by (drule gen_prefix.append [OF gen_prefix.Nil], simp)
declare Nil_gen_prefix [simp]


lemma gen_prefix_length_le: "\<langle>xs,ys\<rangle> \<in> gen_prefix(A, r) \<Longrightarrow> length(xs) \<le> length(ys)"
apply (erule gen_prefix.induct)
apply (subgoal_tac [3] "ys \<in> list (A) ")
apply (auto dest: gen_prefix.dom_subset [THEN subsetD]
            intro: le_trans simp add: length_app)
done


lemma Cons_gen_prefix_aux:
  "\<lbrakk><xs', ys'> \<in> gen_prefix(A, r)\<rbrakk>
   \<Longrightarrow> (\<forall>x xs. x \<in> A \<longrightarrow> xs'= Cons(x,xs) \<longrightarrow>
       (\<exists>y ys. y \<in> A \<and> ys' = Cons(y,ys) \<and>
       \<langle>x,y\<rangle>:r \<and> \<langle>xs, ys\<rangle> \<in> gen_prefix(A, r)))"
apply (erule gen_prefix.induct)
prefer 3 apply (force intro: gen_prefix.append, auto)
done

lemma Cons_gen_prefixE:
  "\<lbrakk><Cons(x,xs), zs> \<in> gen_prefix(A, r);
    \<And>y ys. \<lbrakk>zs = Cons(y, ys); y \<in> A; x \<in> A; \<langle>x,y\<rangle>:r;
      \<langle>xs,ys\<rangle> \<in> gen_prefix(A, r)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
apply (frule gen_prefix.dom_subset [THEN subsetD], auto)
apply (blast dest: Cons_gen_prefix_aux)
done
declare Cons_gen_prefixE [elim!]

lemma Cons_gen_prefix_Cons:
"(<Cons(x,xs),Cons(y,ys)> \<in> gen_prefix(A, r))
  \<longleftrightarrow> (x \<in> A \<and> y \<in> A \<and> \<langle>x,y\<rangle>:r \<and> \<langle>xs,ys\<rangle> \<in> gen_prefix(A, r))"
apply (auto intro: gen_prefix.prepend)
done
declare Cons_gen_prefix_Cons [iff]

(** Monotonicity of gen_prefix **)

lemma gen_prefix_mono2: "r<=s \<Longrightarrow> gen_prefix(A, r) \<subseteq> gen_prefix(A, s)"
apply clarify
apply (frule gen_prefix.dom_subset [THEN subsetD], clarify)
apply (erule rev_mp)
apply (erule gen_prefix.induct)
apply (auto intro: gen_prefix.append)
done

lemma gen_prefix_mono1: "A<=B \<Longrightarrow>gen_prefix(A, r) \<subseteq> gen_prefix(B, r)"
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

lemma gen_prefix_mono: "\<lbrakk>A \<subseteq> B; r \<subseteq> s\<rbrakk> \<Longrightarrow> gen_prefix(A, r) \<subseteq> gen_prefix(B, s)"
apply (rule subset_trans)
apply (rule gen_prefix_mono1)
apply (rule_tac [2] gen_prefix_mono2, auto)
done

(*** gen_prefix order ***)

(* reflexivity *)
lemma refl_gen_prefix: "refl(A, r) \<Longrightarrow> refl(list(A), gen_prefix(A, r))"
apply (unfold refl_def, auto)
apply (induct_tac "x", auto)
done
declare refl_gen_prefix [THEN reflD, simp]

(* Transitivity *)
(* A lemma for proving gen_prefix_trans_comp *)

lemma append_gen_prefix [rule_format (no_asm)]: "xs \<in> list(A) \<Longrightarrow>
   \<forall>zs. <xs @ ys, zs> \<in> gen_prefix(A, r) \<longrightarrow> \<langle>xs, zs\<rangle>: gen_prefix(A, r)"
apply (erule list.induct)
apply (auto dest: gen_prefix.dom_subset [THEN subsetD])
done

(* Lemma proving transitivity and more*)

lemma gen_prefix_trans_comp [rule_format (no_asm)]:
     "\<langle>x, y\<rangle>: gen_prefix(A, r) \<Longrightarrow>
   (\<forall>z \<in> list(A). \<langle>y,z\<rangle> \<in> gen_prefix(A, s)\<longrightarrow>\<langle>x, z\<rangle> \<in> gen_prefix(A, s O r))"
apply (erule gen_prefix.induct)
apply (auto elim: ConsE simp add: Nil_gen_prefix)
apply (subgoal_tac "ys \<in> list (A) ")
prefer 2 apply (blast dest: gen_prefix.dom_subset [THEN subsetD])
apply (drule_tac xs = ys and r = s in append_gen_prefix, auto)
done

lemma trans_comp_subset: "trans(r) \<Longrightarrow> r O r \<subseteq> r"
by (auto dest: transD)

lemma trans_gen_prefix: "trans(r) \<Longrightarrow> trans(gen_prefix(A,r))"
apply (simp (no_asm) add: trans_def)
apply clarify
apply (rule trans_comp_subset [THEN gen_prefix_mono2, THEN subsetD], assumption)
apply (rule gen_prefix_trans_comp)
apply (auto dest: gen_prefix.dom_subset [THEN subsetD])
done

lemma trans_on_gen_prefix:
 "trans(r) \<Longrightarrow> trans[list(A)](gen_prefix(A, r))"
apply (drule_tac A = A in trans_gen_prefix)
apply (unfold trans_def trans_on_def, blast)
done

lemma prefix_gen_prefix_trans:
    "\<lbrakk>\<langle>x,y\<rangle> \<in> prefix(A); \<langle>y, z\<rangle> \<in> gen_prefix(A, r); r<=A*A\<rbrakk>
      \<Longrightarrow>  \<langle>x, z\<rangle> \<in> gen_prefix(A, r)"
  unfolding prefix_def
apply (rule_tac P = "\<lambda>r. \<langle>x,z\<rangle> \<in> gen_prefix (A, r) " in right_comp_id [THEN subst])
apply (blast dest: gen_prefix_trans_comp gen_prefix.dom_subset [THEN subsetD])+
done


lemma gen_prefix_prefix_trans:
"\<lbrakk>\<langle>x,y\<rangle> \<in> gen_prefix(A,r); \<langle>y, z\<rangle> \<in> prefix(A); r<=A*A\<rbrakk>
  \<Longrightarrow>  \<langle>x, z\<rangle> \<in> gen_prefix(A, r)"
  unfolding prefix_def
apply (rule_tac P = "\<lambda>r. \<langle>x,z\<rangle> \<in> gen_prefix (A, r) " in left_comp_id [THEN subst])
apply (blast dest: gen_prefix_trans_comp gen_prefix.dom_subset [THEN subsetD])+
done

(** Antisymmetry **)

lemma nat_le_lemma [rule_format]: "n \<in> nat \<Longrightarrow> \<forall>b \<in> nat. n #+ b \<le> n \<longrightarrow> b = 0"
by (induct_tac "n", auto)

lemma antisym_gen_prefix: "antisym(r) \<Longrightarrow> antisym(gen_prefix(A, r))"
apply (simp (no_asm) add: antisym_def)
apply (rule impI [THEN allI, THEN allI])
apply (erule gen_prefix.induct, blast)
apply (simp add: antisym_def, blast)
txt\<open>append case is hardest\<close>
apply clarify
apply (subgoal_tac "length (zs) = 0")
apply (subgoal_tac "ys \<in> list (A) ")
prefer 2 apply (blast dest: gen_prefix.dom_subset [THEN subsetD])
apply (drule_tac psi = "<ys @ zs, xs> \<in> gen_prefix (A,r) " in asm_rl)
apply simp
apply (subgoal_tac "length (ys @ zs) = length (ys) #+ length (zs) \<and>ys \<in> list (A) \<and>xs \<in> list (A) ")
prefer 2 apply (blast intro: length_app dest: gen_prefix.dom_subset [THEN subsetD])
apply (drule gen_prefix_length_le)+
apply clarify
apply simp
apply (drule_tac j = "length (xs) " in le_trans)
apply blast
apply (auto intro: nat_le_lemma)
done

(*** recursion equations ***)

lemma gen_prefix_Nil: "xs \<in> list(A) \<Longrightarrow> <xs, []> \<in> gen_prefix(A,r) \<longleftrightarrow> (xs = [])"
by (induct_tac "xs", auto)
declare gen_prefix_Nil [simp]

lemma same_gen_prefix_gen_prefix:
 "\<lbrakk>refl(A, r);  xs \<in> list(A)\<rbrakk> \<Longrightarrow>
    <xs@ys, xs@zs>: gen_prefix(A, r) \<longleftrightarrow> \<langle>ys,zs\<rangle> \<in> gen_prefix(A, r)"
  unfolding refl_def
apply (induct_tac "xs")
apply (simp_all (no_asm_simp))
done
declare same_gen_prefix_gen_prefix [simp]

lemma gen_prefix_Cons: "\<lbrakk>xs \<in> list(A); ys \<in> list(A); y \<in> A\<rbrakk> \<Longrightarrow>
    <xs, Cons(y,ys)> \<in> gen_prefix(A,r)  \<longleftrightarrow>
      (xs=[] | (\<exists>z zs. xs=Cons(z,zs) \<and> z \<in> A \<and> \<langle>z,y\<rangle>:r \<and> \<langle>zs,ys\<rangle> \<in> gen_prefix(A,r)))"
apply (induct_tac "xs", auto)
done

lemma gen_prefix_take_append: "\<lbrakk>refl(A,r);  \<langle>xs,ys\<rangle> \<in> gen_prefix(A, r); zs \<in> list(A)\<rbrakk>
      \<Longrightarrow>  <xs@zs, take(length(xs), ys) @ zs> \<in> gen_prefix(A, r)"
apply (erule gen_prefix.induct)
apply (simp (no_asm_simp))
apply (frule_tac [!] gen_prefix.dom_subset [THEN subsetD], auto)
apply (frule gen_prefix_length_le)
apply (subgoal_tac "take (length (xs), ys) \<in> list (A) ")
apply (simp_all (no_asm_simp) add: diff_is_0_iff [THEN iffD2] take_type)
done

lemma gen_prefix_append_both: "\<lbrakk>refl(A, r);  \<langle>xs,ys\<rangle> \<in> gen_prefix(A,r);
         length(xs) = length(ys); zs \<in> list(A)\<rbrakk>
      \<Longrightarrow>  <xs@zs, ys @ zs> \<in> gen_prefix(A, r)"
apply (drule_tac zs = zs in gen_prefix_take_append, assumption+)
apply (subgoal_tac "take (length (xs), ys) =ys")
apply (auto intro!: take_all dest: gen_prefix.dom_subset [THEN subsetD])
done

(*NOT suitable for rewriting since [y] has the form y#ys*)
lemma append_cons_conv: "xs \<in> list(A) \<Longrightarrow> xs @ Cons(y, ys) = (xs @ [y]) @ ys"
by (auto simp add: app_assoc)

lemma append_one_gen_prefix_lemma [rule_format]:
     "\<lbrakk>\<langle>xs,ys\<rangle> \<in> gen_prefix(A, r);  refl(A, r)\<rbrakk>
      \<Longrightarrow> length(xs) < length(ys) \<longrightarrow>
          <xs @ [nth(length(xs), ys)], ys> \<in> gen_prefix(A, r)"
apply (erule gen_prefix.induct, blast)
apply (frule gen_prefix.dom_subset [THEN subsetD], clarify)
apply (simp_all add: length_type)
(* Append case is hardest *)
apply (frule gen_prefix_length_le [THEN le_iff [THEN iffD1]])
apply (frule gen_prefix.dom_subset [THEN subsetD], clarify)
apply (subgoal_tac "length (xs) :nat\<and>length (ys) :nat \<and>length (zs) :nat")
prefer 2 apply (blast intro: length_type, clarify)
apply (simp_all add: nth_append length_type length_app)
apply (rule conjI)
apply (blast intro: gen_prefix.append)
apply (erule_tac V = "length (xs) < length (ys) \<longrightarrow>u" for u in thin_rl)
apply (erule_tac a = zs in list.cases, auto)
apply (rule_tac P1 = "\<lambda>x. <u(x), v>:w" for u v w in nat_diff_split [THEN iffD2])
apply auto
apply (simplesubst append_cons_conv)
apply (rule_tac [2] gen_prefix.append)
apply (auto elim: ConsE simp add: gen_prefix_append_both)
done

lemma append_one_gen_prefix: "\<lbrakk>\<langle>xs,ys\<rangle>: gen_prefix(A, r);  length(xs) < length(ys);  refl(A, r)\<rbrakk>
      \<Longrightarrow> <xs @ [nth(length(xs), ys)], ys> \<in> gen_prefix(A, r)"
apply (blast intro: append_one_gen_prefix_lemma)
done


(** Proving the equivalence with Charpentier's definition **)

lemma gen_prefix_imp_nth_lemma [rule_format]: "xs \<in> list(A) \<Longrightarrow>
  \<forall>ys \<in> list(A). \<forall>i \<in> nat. i < length(xs)
          \<longrightarrow> \<langle>xs, ys\<rangle>: gen_prefix(A, r) \<longrightarrow> <nth(i, xs), nth(i, ys)>:r"
apply (induct_tac "xs", simp, clarify)
apply simp
apply (erule natE, auto)
done

lemma gen_prefix_imp_nth: "\<lbrakk>\<langle>xs,ys\<rangle> \<in> gen_prefix(A,r); i < length(xs)\<rbrakk>
      \<Longrightarrow> <nth(i, xs), nth(i, ys)>:r"
apply (cut_tac A = A in gen_prefix.dom_subset)
apply (rule gen_prefix_imp_nth_lemma)
apply (auto simp add: lt_nat_in_nat)
done

lemma nth_imp_gen_prefix [rule_format]: "xs \<in> list(A) \<Longrightarrow>
  \<forall>ys \<in> list(A). length(xs) \<le> length(ys)
      \<longrightarrow> (\<forall>i. i < length(xs) \<longrightarrow> <nth(i, xs), nth(i,ys)>:r)
      \<longrightarrow> \<langle>xs, ys\<rangle> \<in> gen_prefix(A, r)"
apply (induct_tac "xs")
apply (simp_all (no_asm_simp))
apply clarify
apply (erule_tac a = ys in list.cases, simp)
apply (force intro!: nat_0_le simp add: lt_nat_in_nat)
done

lemma gen_prefix_iff_nth: "(\<langle>xs,ys\<rangle> \<in> gen_prefix(A,r)) \<longleftrightarrow>
      (xs \<in> list(A) \<and> ys \<in> list(A) \<and> length(xs) \<le> length(ys) \<and>
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
  unfolding prefix_def
apply (rule refl_gen_prefix)
apply (auto simp add: refl_def)
done
declare refl_prefix [THEN reflD, simp]

lemma trans_prefix: "trans(prefix(A))"
  unfolding prefix_def
apply (rule trans_gen_prefix)
apply (auto simp add: trans_def)
done

lemmas prefix_trans = trans_prefix [THEN transD]

lemma trans_on_prefix: "trans[list(A)](prefix(A))"
  unfolding prefix_def
apply (rule trans_on_gen_prefix)
apply (auto simp add: trans_def)
done

lemmas prefix_trans_on = trans_on_prefix [THEN trans_onD]

(* Monotonicity of "set" operator WRT prefix *)

lemma set_of_list_prefix_mono:
"\<langle>xs,ys\<rangle> \<in> prefix(A) \<Longrightarrow> set_of_list(xs) \<subseteq> set_of_list(ys)"

  unfolding prefix_def
apply (erule gen_prefix.induct)
apply (subgoal_tac [3] "xs \<in> list (A) \<and>ys \<in> list (A) ")
prefer 4 apply (blast dest: gen_prefix.dom_subset [THEN subsetD])
apply (auto simp add: set_of_list_append)
done

(** recursion equations **)

lemma Nil_prefix: "xs \<in> list(A) \<Longrightarrow> <[],xs> \<in> prefix(A)"

  unfolding prefix_def
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
"<Cons(x,xs), Cons(y,ys)> \<in> prefix(A) \<longleftrightarrow> (x=y \<and> \<langle>xs,ys\<rangle> \<in> prefix(A) \<and> y \<in> A)"
apply (unfold prefix_def, auto)
done
declare Cons_prefix_Cons [iff]

lemma same_prefix_prefix:
"xs \<in> list(A)\<Longrightarrow> <xs@ys,xs@zs> \<in> prefix(A) \<longleftrightarrow> (\<langle>ys,zs\<rangle> \<in> prefix(A))"
  unfolding prefix_def
apply (subgoal_tac "refl (A,id (A))")
apply (simp (no_asm_simp))
apply (auto simp add: refl_def)
done
declare same_prefix_prefix [simp]

lemma same_prefix_prefix_Nil: "xs \<in> list(A) \<Longrightarrow> <xs@ys,xs> \<in> prefix(A) \<longleftrightarrow> (<ys,[]> \<in> prefix(A))"
apply (rule_tac P = "\<lambda>x. \<langle>u, x\<rangle>:v \<longleftrightarrow> w(x)" for u v w in app_right_Nil [THEN subst])
apply (rule_tac [2] same_prefix_prefix, auto)
done
declare same_prefix_prefix_Nil [simp]

lemma prefix_appendI:
"\<lbrakk>\<langle>xs,ys\<rangle> \<in> prefix(A); zs \<in> list(A)\<rbrakk> \<Longrightarrow> <xs,ys@zs> \<in> prefix(A)"
  unfolding prefix_def
apply (erule gen_prefix.append, assumption)
done
declare prefix_appendI [simp]

lemma prefix_Cons:
"\<lbrakk>xs \<in> list(A); ys \<in> list(A); y \<in> A\<rbrakk> \<Longrightarrow>
  <xs,Cons(y,ys)> \<in> prefix(A) \<longleftrightarrow>
  (xs=[] | (\<exists>zs. xs=Cons(y,zs) \<and> \<langle>zs,ys\<rangle> \<in> prefix(A)))"
  unfolding prefix_def
apply (auto simp add: gen_prefix_Cons)
done

lemma append_one_prefix:
  "\<lbrakk>\<langle>xs,ys\<rangle> \<in> prefix(A); length(xs) < length(ys)\<rbrakk>
  \<Longrightarrow> <xs @ [nth(length(xs),ys)], ys> \<in> prefix(A)"
  unfolding prefix_def
apply (subgoal_tac "refl (A, id (A))")
apply (simp (no_asm_simp) add: append_one_gen_prefix)
apply (auto simp add: refl_def)
done

lemma prefix_length_le:
"\<langle>xs,ys\<rangle> \<in> prefix(A) \<Longrightarrow> length(xs) \<le> length(ys)"
  unfolding prefix_def
apply (blast dest: gen_prefix_length_le)
done

lemma prefix_type: "prefix(A)<=list(A)*list(A)"
  unfolding prefix_def
apply (blast intro!: gen_prefix.dom_subset)
done

lemma strict_prefix_type:
"strict_prefix(A) \<subseteq> list(A)*list(A)"
  unfolding strict_prefix_def
apply (blast intro!: prefix_type [THEN subsetD])
done

lemma strict_prefix_length_lt_aux:
     "\<langle>xs,ys\<rangle> \<in> prefix(A) \<Longrightarrow> xs\<noteq>ys \<longrightarrow> length(xs) < length(ys)"
  unfolding prefix_def
apply (erule gen_prefix.induct, clarify)
apply (subgoal_tac [!] "ys \<in> list(A) \<and> xs \<in> list(A)")
apply (auto dest: gen_prefix.dom_subset [THEN subsetD]
            simp add: length_type)
apply (subgoal_tac "length (zs) =0")
apply (drule_tac [2] not_lt_imp_le)
apply (rule_tac [5] j = "length (ys) " in lt_trans2)
apply auto
done

lemma strict_prefix_length_lt:
     "\<langle>xs,ys\<rangle>:strict_prefix(A) \<Longrightarrow> length(xs) < length(ys)"
  unfolding strict_prefix_def
apply (rule strict_prefix_length_lt_aux [THEN mp])
apply (auto dest: prefix_type [THEN subsetD])
done

(*Equivalence to the definition used in Lex/Prefix.thy*)
lemma prefix_iff:
    "\<langle>xs,zs\<rangle> \<in> prefix(A) \<longleftrightarrow> (\<exists>ys \<in> list(A). zs = xs@ys) \<and> xs \<in> list(A)"
  unfolding prefix_def
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
apply (simp_all (no_asm_simp) add: leI split: nat_diff_split)
done

lemma prefix_snoc:
"\<lbrakk>xs \<in> list(A); ys \<in> list(A); y \<in> A\<rbrakk> \<Longrightarrow>
   <xs, ys@[y]> \<in> prefix(A) \<longleftrightarrow> (xs = ys@[y] | \<langle>xs,ys\<rangle> \<in> prefix(A))"
apply (simp (no_asm) add: prefix_iff)
apply (rule iffI, clarify)
apply (erule_tac xs = ysa in rev_list_elim, simp)
apply (simp add: app_type app_assoc [symmetric])
apply (auto simp add: app_assoc app_type)
done
declare prefix_snoc [simp]

lemma prefix_append_iff [rule_format]: "zs \<in> list(A) \<Longrightarrow> \<forall>xs \<in> list(A). \<forall>ys \<in> list(A).
   (<xs, ys@zs> \<in> prefix(A)) \<longleftrightarrow>
  (\<langle>xs,ys\<rangle> \<in> prefix(A) | (\<exists>us. xs = ys@us \<and> \<langle>us,zs\<rangle> \<in> prefix(A)))"
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
lemma common_prefix_linear_lemma [rule_format]: "\<lbrakk>zs \<in> list(A); xs \<in> list(A); ys \<in> list(A)\<rbrakk>
   \<Longrightarrow> \<langle>xs, zs\<rangle> \<in> prefix(A) \<longrightarrow> \<langle>ys,zs\<rangle> \<in> prefix(A)
  \<longrightarrow>\<langle>xs,ys\<rangle> \<in> prefix(A) | \<langle>ys,xs\<rangle> \<in> prefix(A)"
apply (erule list_append_induct, auto)
done

lemma common_prefix_linear: "\<lbrakk>\<langle>xs, zs\<rangle> \<in> prefix(A); \<langle>ys,zs\<rangle> \<in> prefix(A)\<rbrakk>
      \<Longrightarrow> \<langle>xs,ys\<rangle> \<in> prefix(A) | \<langle>ys,xs\<rangle> \<in> prefix(A)"
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
  unfolding antisym_def
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

lemma pfixLe_refl: "x \<in> list(nat) \<Longrightarrow> x pfixLe x"
by (blast intro: refl_gen_prefix [THEN reflD] refl_Le)
declare pfixLe_refl [simp]

lemma pfixLe_trans: "\<lbrakk>x pfixLe y; y pfixLe z\<rbrakk> \<Longrightarrow> x pfixLe z"
by (blast intro: trans_gen_prefix [THEN transD] trans_Le)

lemma pfixLe_antisym: "\<lbrakk>x pfixLe y; y pfixLe x\<rbrakk> \<Longrightarrow> x = y"
by (blast intro: antisym_gen_prefix [THEN antisymE] antisym_Le)


lemma prefix_imp_pfixLe:
"\<langle>xs,ys\<rangle>:prefix(nat)\<Longrightarrow> xs pfixLe ys"

  unfolding prefix_def
apply (rule gen_prefix_mono [THEN subsetD], auto)
done

lemma refl_Ge: "refl(nat, Ge)"
by (unfold refl_def Ge_def, auto)
declare refl_Ge [iff]

lemma antisym_Ge: "antisym(Ge)"
  unfolding antisym_def Ge_def
apply (auto intro: le_anti_sym)
done
declare antisym_Ge [iff]

lemma trans_Ge: "trans(Ge)"
  unfolding trans_def Ge_def
apply (auto intro: le_trans)
done
declare trans_Ge [iff]

lemma pfixGe_refl: "x \<in> list(nat) \<Longrightarrow> x pfixGe x"
by (blast intro: refl_gen_prefix [THEN reflD])
declare pfixGe_refl [simp]

lemma pfixGe_trans: "\<lbrakk>x pfixGe y; y pfixGe z\<rbrakk> \<Longrightarrow> x pfixGe z"
by (blast intro: trans_gen_prefix [THEN transD])

lemma pfixGe_antisym: "\<lbrakk>x pfixGe y; y pfixGe x\<rbrakk> \<Longrightarrow> x = y"
by (blast intro: antisym_gen_prefix [THEN antisymE])

lemma prefix_imp_pfixGe:
  "\<langle>xs,ys\<rangle>:prefix(nat) \<Longrightarrow> xs pfixGe ys"
  unfolding prefix_def Ge_def
apply (rule gen_prefix_mono [THEN subsetD], auto)
done
(* Added by Sidi \<in> prefix and take *)

lemma prefix_imp_take:
"\<langle>xs, ys\<rangle> \<in> prefix(A) \<Longrightarrow> xs = take(length(xs), ys)"

  unfolding prefix_def
apply (erule gen_prefix.induct)
apply (subgoal_tac [3] "length (xs) :nat")
apply (auto dest: gen_prefix.dom_subset [THEN subsetD] simp add: length_type)
apply (frule gen_prefix.dom_subset [THEN subsetD])
apply (frule gen_prefix_length_le)
apply (auto simp add: take_append)
apply (subgoal_tac "length (xs) #- length (ys) =0")
apply (simp_all (no_asm_simp) add: diff_is_0_iff)
done

lemma prefix_length_equal: "\<lbrakk>\<langle>xs,ys\<rangle> \<in> prefix(A); length(xs)=length(ys)\<rbrakk> \<Longrightarrow> xs = ys"
apply (cut_tac A = A in prefix_type)
apply (drule subsetD, auto)
apply (drule prefix_imp_take)
apply (erule trans, simp)
done

lemma prefix_length_le_equal: "\<lbrakk>\<langle>xs,ys\<rangle> \<in> prefix(A); length(ys) \<le> length(xs)\<rbrakk> \<Longrightarrow> xs = ys"
by (blast intro: prefix_length_equal le_anti_sym prefix_length_le)

lemma take_prefix [rule_format]: "xs \<in> list(A) \<Longrightarrow> \<forall>n \<in> nat. <take(n, xs), xs> \<in> prefix(A)"
  unfolding prefix_def
apply (erule list.induct, simp, clarify)
apply (erule natE, auto)
done

lemma prefix_take_iff: "\<langle>xs,ys\<rangle> \<in> prefix(A) \<longleftrightarrow> (xs=take(length(xs), ys) \<and> xs \<in> list(A) \<and> ys \<in> list(A))"
apply (rule iffI)
apply (frule prefix_type [THEN subsetD])
apply (blast intro: prefix_imp_take, clarify)
apply (erule ssubst)
apply (blast intro: take_prefix length_type)
done

lemma prefix_imp_nth: "\<lbrakk>\<langle>xs,ys\<rangle> \<in> prefix(A); i < length(xs)\<rbrakk> \<Longrightarrow> nth(i,xs) = nth(i,ys)"
by (auto dest!: gen_prefix_imp_nth simp add: prefix_def)

lemma nth_imp_prefix:
     "\<lbrakk>xs \<in> list(A); ys \<in> list(A); length(xs) \<le> length(ys);
        \<And>i. i < length(xs) \<Longrightarrow> nth(i, xs) = nth(i,ys)\<rbrakk>
      \<Longrightarrow> \<langle>xs,ys\<rangle> \<in> prefix(A)"
apply (auto simp add: prefix_def nth_imp_gen_prefix)
apply (auto intro!: nth_imp_gen_prefix simp add: prefix_def)
apply (blast intro: nth_type lt_trans2)
done


lemma length_le_prefix_imp_prefix: "\<lbrakk>length(xs) \<le> length(ys);
        \<langle>xs,zs\<rangle> \<in> prefix(A); \<langle>ys,zs\<rangle> \<in> prefix(A)\<rbrakk> \<Longrightarrow> \<langle>xs,ys\<rangle> \<in> prefix(A)"
apply (cut_tac A = A in prefix_type)
apply (rule nth_imp_prefix, blast, blast)
 apply assumption
apply (rule_tac b = "nth (i,zs)" in trans)
 apply (blast intro: prefix_imp_nth)
apply (blast intro: sym prefix_imp_nth prefix_length_le lt_trans2)
done

end
