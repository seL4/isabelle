(*  Title:      HOL/MicroJava/BV/Kildall.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Gerwin Klein
    Copyright   2000 TUM

Kildall's algorithm
*)

header {* \isaheader{Kildall's Algorithm}\label{sec:Kildall} *}

theory Kildall = SemilatAlg + While_Combinator:


consts
 iter :: "'s binop \<Rightarrow> 's step_type \<Rightarrow>
          's list \<Rightarrow> nat set \<Rightarrow> 's list \<times> nat set"
 propa :: "'s binop \<Rightarrow> (nat \<times> 's) list \<Rightarrow> 's list \<Rightarrow> nat set \<Rightarrow> 's list * nat set"

primrec
"propa f []      ss w = (ss,w)"
"propa f (q'#qs) ss w = (let (q,t) = q';
                             u = t +_f ss!q;
                             w' = (if u = ss!q then w else insert q w)
                         in propa f qs (ss[q := u]) w')"

defs iter_def:
"iter f step ss w ==
 while (%(ss,w). w \<noteq> {})
       (%(ss,w). let p = SOME p. p \<in> w
                 in propa f (step p (ss!p)) ss (w-{p}))
       (ss,w)"

constdefs
 unstables :: "'s ord \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> nat set"
"unstables r step ss == {p. p < size ss \<and> \<not>stable r step ss p}"

 kildall :: "'s ord \<Rightarrow> 's binop \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> 's list"
"kildall r f step ss == fst(iter f step ss (unstables r step ss))"

consts merges :: "'s binop \<Rightarrow> (nat \<times> 's) list \<Rightarrow> 's list \<Rightarrow> 's list"
primrec
"merges f []      ss = ss"
"merges f (p'#ps) ss = (let (p,s) = p' in merges f ps (ss[p := s +_f ss!p]))"


lemmas [simp] = Let_def semilat.le_iff_plus_unchanged [symmetric]


lemma (in semilat) nth_merges:
 "\<And>ss. \<lbrakk>p < length ss; ss \<in> list n A; \<forall>(p,t)\<in>set ps. p<n \<and> t\<in>A \<rbrakk> \<Longrightarrow>
  (merges f ps ss)!p = map snd [(p',t') \<in> ps. p'=p] ++_f ss!p"
  (is "\<And>ss. \<lbrakk>_; _; ?steptype ps\<rbrakk> \<Longrightarrow> ?P ss ps")
proof (induct ps)
  show "\<And>ss. ?P ss []" by simp

  fix ss p' ps'
  assume ss: "ss \<in> list n A"
  assume l:  "p < length ss"
  assume "?steptype (p'#ps')"
  then obtain a b where
    p': "p'=(a,b)" and ab: "a<n" "b\<in>A" and "?steptype ps'"
    by (cases p', auto)
  assume "\<And>ss. p< length ss \<Longrightarrow> ss \<in> list n A \<Longrightarrow> ?steptype ps' \<Longrightarrow> ?P ss ps'"
  hence IH: "\<And>ss. ss \<in> list n A \<Longrightarrow> p < length ss \<Longrightarrow> ?P ss ps'" .

  from ss ab
  have "ss[a := b +_f ss!a] \<in> list n A" by (simp add: closedD)
  moreover
  from calculation
  have "p < length (ss[a := b +_f ss!a])" by simp
  ultimately
  have "?P (ss[a := b +_f ss!a]) ps'" by (rule IH)
  with p' l
  show "?P ss (p'#ps')" by simp
qed


(** merges **)

lemma length_merges [rule_format, simp]:
  "\<forall>ss. size(merges f ps ss) = size ss"
  by (induct_tac ps, auto)


lemma (in semilat) merges_preserves_type_lemma:
shows "\<forall>xs. xs \<in> list n A \<longrightarrow> (\<forall>(p,x) \<in> set ps. p<n \<and> x\<in>A)
          \<longrightarrow> merges f ps xs \<in> list n A"
apply (insert closedI)
apply (unfold closed_def)
apply (induct_tac ps)
 apply simp
apply clarsimp
done

lemma (in semilat) merges_preserves_type [simp]:
 "\<lbrakk> xs \<in> list n A; \<forall>(p,x) \<in> set ps. p<n \<and> x\<in>A \<rbrakk>
  \<Longrightarrow> merges f ps xs \<in> list n A"
by (simp add: merges_preserves_type_lemma)

lemma (in semilat) merges_incr_lemma:
 "\<forall>xs. xs \<in> list n A \<longrightarrow> (\<forall>(p,x)\<in>set ps. p<size xs \<and> x \<in> A) \<longrightarrow> xs <=[r] merges f ps xs"
apply (induct_tac ps)
 apply simp
apply simp
apply clarify
apply (rule order_trans)
  apply simp
 apply (erule list_update_incr)
  apply simp
 apply simp
apply (blast intro!: listE_set intro: closedD listE_length [THEN nth_in])
done

lemma (in semilat) merges_incr:
 "\<lbrakk> xs \<in> list n A; \<forall>(p,x)\<in>set ps. p<size xs \<and> x \<in> A \<rbrakk> 
  \<Longrightarrow> xs <=[r] merges f ps xs"
  by (simp add: merges_incr_lemma)


lemma (in semilat) merges_same_conv [rule_format]:
 "(\<forall>xs. xs \<in> list n A \<longrightarrow> (\<forall>(p,x)\<in>set ps. p<size xs \<and> x\<in>A) \<longrightarrow> 
     (merges f ps xs = xs) = (\<forall>(p,x)\<in>set ps. x <=_r xs!p))"
  apply (induct_tac ps)
   apply simp
  apply clarsimp
  apply (rename_tac p x ps xs)
  apply (rule iffI)
   apply (rule context_conjI)
    apply (subgoal_tac "xs[p := x +_f xs!p] <=[r] xs")
     apply (force dest!: le_listD simp add: nth_list_update)
    apply (erule subst, rule merges_incr)
       apply (blast intro!: listE_set intro: closedD listE_length [THEN nth_in])
      apply clarify
      apply (rule conjI)
       apply simp
       apply (blast dest: boundedD)
      apply blast
   apply clarify
   apply (erule allE)
   apply (erule impE)
    apply assumption
   apply (drule bspec)
    apply assumption
   apply (simp add: le_iff_plus_unchanged [THEN iffD1] list_update_same_conv [THEN iffD2])
   apply blast
  apply clarify 
  apply (simp add: le_iff_plus_unchanged [THEN iffD1] list_update_same_conv [THEN iffD2])
  done


lemma (in semilat) list_update_le_listI [rule_format]:
  "set xs <= A \<longrightarrow> set ys <= A \<longrightarrow> xs <=[r] ys \<longrightarrow> p < size xs \<longrightarrow>  
   x <=_r ys!p \<longrightarrow> x\<in>A \<longrightarrow> xs[p := x +_f xs!p] <=[r] ys"
  apply(insert semilat)
  apply (unfold Listn.le_def lesub_def semilat_def)
  apply (simp add: list_all2_conv_all_nth nth_list_update)
  done

lemma (in semilat) merges_pres_le_ub:
shows "\<lbrakk> set ts <= A; set ss <= A;
         \<forall>(p,t)\<in>set ps. t <=_r ts!p \<and> t \<in> A \<and> p < size ts; ss <=[r] ts \<rbrakk>
  \<Longrightarrow> merges f ps ss <=[r] ts"
proof -
  { fix t ts ps
    have
    "\<And>qs. \<lbrakk>set ts <= A; \<forall>(p,t)\<in>set ps. t <=_r ts!p \<and> t \<in> A \<and> p< size ts \<rbrakk> \<Longrightarrow>
    set qs <= set ps  \<longrightarrow> 
    (\<forall>ss. set ss <= A \<longrightarrow> ss <=[r] ts \<longrightarrow> merges f qs ss <=[r] ts)"
    apply (induct_tac qs)
     apply simp
    apply (simp (no_asm_simp))
    apply clarify
    apply (rotate_tac -2)
    apply simp
    apply (erule allE, erule impE, erule_tac [2] mp)
     apply (drule bspec, assumption)
     apply (simp add: closedD)
    apply (drule bspec, assumption)
    apply (simp add: list_update_le_listI)
    done 
  } note this [dest]
  
  case rule_context
  thus ?thesis by blast
qed


(** propa **)


lemma decomp_propa:
  "\<And>ss w. (\<forall>(q,t)\<in>set qs. q < size ss) \<Longrightarrow> 
   propa f qs ss w = 
   (merges f qs ss, {q. \<exists>t. (q,t)\<in>set qs \<and> t +_f ss!q \<noteq> ss!q} Un w)"
  apply (induct qs)
   apply simp   
  apply (simp (no_asm))
  apply clarify  
  apply simp
  apply (rule conjI) 
   apply blast
  apply (simp add: nth_list_update)
  apply blast
  done 

(** iter **)

lemma (in semilat) stable_pres_lemma:
shows "\<lbrakk>pres_type step n A; bounded step n; 
     ss \<in> list n A; p \<in> w; \<forall>q\<in>w. q < n; 
     \<forall>q. q < n \<longrightarrow> q \<notin> w \<longrightarrow> stable r step ss q; q < n; 
     \<forall>s'. (q,s') \<in> set (step p (ss ! p)) \<longrightarrow> s' +_f ss ! q = ss ! q; 
     q \<notin> w \<or> q = p \<rbrakk> 
  \<Longrightarrow> stable r step (merges f (step p (ss!p)) ss) q"
  apply (unfold stable_def)
  apply (subgoal_tac "\<forall>s'. (q,s') \<in> set (step p (ss!p)) \<longrightarrow> s' : A")
   prefer 2
   apply clarify
   apply (erule pres_typeD)
    prefer 3 apply assumption
    apply (rule listE_nth_in)
     apply assumption
    apply simp
   apply simp
  apply simp
  apply clarify
  apply (subst nth_merges)
       apply simp
       apply (blast dest: boundedD)
      apply assumption
     apply clarify
     apply (rule conjI)
      apply (blast dest: boundedD)
     apply (erule pres_typeD)
       prefer 3 apply assumption
      apply simp
     apply simp
apply(subgoal_tac "q < length ss")
prefer 2 apply simp
  apply (frule nth_merges [of q _ _ "step p (ss!p)"]) (* fixme: why does method subst not work?? *)
apply assumption
  apply clarify
  apply (rule conjI)
   apply (blast dest: boundedD)
  apply (erule pres_typeD)
     prefer 3 apply assumption
    apply simp
   apply simp
  apply (drule_tac P = "\<lambda>x. (a, b) \<in> set (step q x)" in subst)
   apply assumption

 apply (simp add: plusplus_empty)
 apply (cases "q \<in> w")
  apply simp
  apply (rule ub1')
     apply assumption
    apply clarify
    apply (rule pres_typeD)
       apply assumption
      prefer 3 apply assumption
     apply (blast intro: listE_nth_in dest: boundedD)
    apply (blast intro: pres_typeD dest: boundedD)
   apply (blast intro: listE_nth_in dest: boundedD)
  apply assumption

 apply simp
 apply (erule allE, erule impE, assumption, erule impE, assumption)
 apply (rule order_trans)
   apply simp
  defer
 apply (rule pp_ub2)(*
    apply assumption*)
   apply simp
   apply clarify
   apply simp
   apply (rule pres_typeD)
      apply assumption
     prefer 3 apply assumption
    apply (blast intro: listE_nth_in dest: boundedD)
   apply (blast intro: pres_typeD dest: boundedD)
  apply (blast intro: listE_nth_in dest: boundedD)
 apply blast
 done


lemma (in semilat) merges_bounded_lemma:
 "\<lbrakk> mono r step n A; bounded step n; 
    \<forall>(p',s') \<in> set (step p (ss!p)). s' \<in> A; ss \<in> list n A; ts \<in> list n A; p < n; 
    ss <=[r] ts; \<forall>p. p < n \<longrightarrow> stable r step ts p \<rbrakk> 
  \<Longrightarrow> merges f (step p (ss!p)) ss <=[r] ts" 
  apply (unfold stable_def)
  apply (rule merges_pres_le_ub)
     apply simp
    apply simp
   prefer 2 apply assumption

  apply clarsimp
  apply (drule boundedD, assumption+)
  apply (erule allE, erule impE, assumption)
  apply (drule bspec, assumption)
  apply simp

  apply (drule monoD [of _ _ _ _ p "ss!p"  "ts!p"])
     apply assumption
    apply simp
   apply (simp add: le_listD)
  
  apply (drule lesub_step_typeD, assumption) 
  apply clarify
  apply (drule bspec, assumption)
  apply simp
  apply (blast intro: order_trans)
  done

lemma termination_lemma: includes semilat
shows "\<lbrakk> ss \<in> list n A; \<forall>(q,t)\<in>set qs. q<n \<and> t\<in>A; p\<in>w \<rbrakk> \<Longrightarrow> 
      ss <[r] merges f qs ss \<or> 
  merges f qs ss = ss \<and> {q. \<exists>t. (q,t)\<in>set qs \<and> t +_f ss!q \<noteq> ss!q} Un (w-{p}) < w"
apply(insert semilat)
  apply (unfold lesssub_def)
  apply (simp (no_asm_simp) add: merges_incr)
  apply (rule impI)
  apply (rule merges_same_conv [THEN iffD1, elim_format]) 
  apply assumption+
    defer
    apply (rule sym, assumption)
   defer apply simp
   apply (subgoal_tac "\<forall>q t. \<not>((q, t) \<in> set qs \<and> t +_f ss ! q \<noteq> ss ! q)")
   apply (blast intro!: psubsetI elim: equalityE)
   apply clarsimp
   apply (drule bspec, assumption) 
   apply (drule bspec, assumption)
   apply clarsimp
  done 

lemma iter_properties[rule_format]: includes semilat
shows "\<lbrakk> acc r ; pres_type step n A; mono r step n A;
     bounded step n; \<forall>p\<in>w0. p < n; ss0 \<in> list n A;
     \<forall>p<n. p \<notin> w0 \<longrightarrow> stable r step ss0 p \<rbrakk> \<Longrightarrow>
   iter f step ss0 w0 = (ss',w')
   \<longrightarrow>
   ss' \<in> list n A \<and> stables r step ss' \<and> ss0 <=[r] ss' \<and>
   (\<forall>ts\<in>list n A. ss0 <=[r] ts \<and> stables r step ts \<longrightarrow> ss' <=[r] ts)"
apply(insert semilat)
apply (unfold iter_def stables_def)
apply (rule_tac P = "%(ss,w).
 ss \<in> list n A \<and> (\<forall>p<n. p \<notin> w \<longrightarrow> stable r step ss p) \<and> ss0 <=[r] ss \<and>
 (\<forall>ts\<in>list n A. ss0 <=[r] ts \<and> stables r step ts \<longrightarrow> ss <=[r] ts) \<and>
 (\<forall>p\<in>w. p < n)" and
 r = "{(ss',ss) . ss <[r] ss'} <*lex*> finite_psubset"
       in while_rule)

-- "Invariant holds initially:"
apply (simp add:stables_def)

-- "Invariant is preserved:"
apply(simp add: stables_def split_paired_all)
apply(rename_tac ss w)
apply(subgoal_tac "(SOME p. p \<in> w) \<in> w")
 prefer 2; apply (fast intro: someI)
apply(subgoal_tac "\<forall>(q,t) \<in> set (step (SOME p. p \<in> w) (ss ! (SOME p. p \<in> w))). q < length ss \<and> t \<in> A")
 prefer 2
 apply clarify
 apply (rule conjI)
  apply(clarsimp, blast dest!: boundedD)
 apply (erule pres_typeD)
  prefer 3
  apply assumption
  apply (erule listE_nth_in)
  apply blast
 apply blast
apply (subst decomp_propa)
 apply blast
apply simp
apply (rule conjI)
 apply (rule merges_preserves_type)
 apply blast
 apply clarify
 apply (rule conjI)
  apply(clarsimp, blast dest!: boundedD)
 apply (erule pres_typeD)
  prefer 3
  apply assumption
  apply (erule listE_nth_in)
  apply blast
 apply blast
apply (rule conjI)
 apply clarify
 apply (blast intro!: stable_pres_lemma)
apply (rule conjI)
 apply (blast intro!: merges_incr intro: le_list_trans)
apply (rule conjI)
 apply clarsimp
 apply (blast intro!: merges_bounded_lemma)
apply (blast dest!: boundedD)


-- "Postcondition holds upon termination:"
apply(clarsimp simp add: stables_def split_paired_all)

-- "Well-foundedness of the termination relation:"
apply (rule wf_lex_prod)
 apply (insert orderI [THEN acc_le_listI])
 apply (simp only: acc_def lesssub_def)
apply (rule wf_finite_psubset) 

-- "Loop decreases along termination relation:"
apply(simp add: stables_def split_paired_all)
apply(rename_tac ss w)
apply(subgoal_tac "(SOME p. p \<in> w) \<in> w")
 prefer 2; apply (fast intro: someI)
apply(subgoal_tac "\<forall>(q,t) \<in> set (step (SOME p. p \<in> w) (ss ! (SOME p. p \<in> w))). q < length ss \<and> t \<in> A")
 prefer 2
 apply clarify
 apply (rule conjI)
  apply(clarsimp, blast dest!: boundedD)
 apply (erule pres_typeD)
  prefer 3
  apply assumption
  apply (erule listE_nth_in)
  apply blast
 apply blast
apply (subst decomp_propa)
 apply blast
apply clarify
apply (simp del: listE_length
    add: lex_prod_def finite_psubset_def 
         bounded_nat_set_is_finite)
apply (rule termination_lemma)
apply assumption+
defer
apply assumption
apply clarsimp
done


lemma kildall_properties: includes semilat
shows "\<lbrakk> acc r; pres_type step n A; mono r step n A;
     bounded step n; ss0 \<in> list n A \<rbrakk> \<Longrightarrow>
  kildall r f step ss0 \<in> list n A \<and>
  stables r step (kildall r f step ss0) \<and>
  ss0 <=[r] kildall r f step ss0 \<and>
  (\<forall>ts\<in>list n A. ss0 <=[r] ts \<and> stables r step ts \<longrightarrow>
                 kildall r f step ss0 <=[r] ts)"
apply (unfold kildall_def)
apply(case_tac "iter f step ss0 (unstables r step ss0)")
apply(simp)
apply (rule iter_properties)
by (simp_all add: unstables_def stable_def)


lemma is_bcv_kildall: includes semilat
shows "\<lbrakk> acc r; top r T; pres_type step n A; bounded step n; mono r step n A \<rbrakk>
  \<Longrightarrow> is_bcv r T step n A (kildall r f step)"
apply(unfold is_bcv_def wt_step_def)
apply(insert semilat kildall_properties[of A])
apply(simp add:stables_def)
apply clarify
apply(subgoal_tac "kildall r f step ss \<in> list n A")
 prefer 2 apply (simp(no_asm_simp))
apply (rule iffI)
 apply (rule_tac x = "kildall r f step ss" in bexI) 
  apply (rule conjI)
   apply (blast)
  apply (simp  (no_asm_simp))
 apply(assumption)
apply clarify
apply(subgoal_tac "kildall r f step ss!p <=_r ts!p")
 apply simp
apply (blast intro!: le_listD less_lengthI)
done

end
