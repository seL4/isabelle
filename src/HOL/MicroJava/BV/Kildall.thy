(*  Title:      HOL/MicroJava/BV/Kildall.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Gerwin Klein
    Copyright   2000 TUM

Kildall's algorithm
*)

header "Kildall's Algorithm"

theory Kildall = Typing_Framework + While_Combinator + Product:


syntax "@lesubstep_type" :: "(nat \<times> 's) list => 's ord => (nat \<times> 's) list => bool"
       ("(_ /<=|_| _)" [50, 0, 51] 50)
translations
 "x <=|r| y" == "x <=[(Product.le (op =) r)] y"
 

constdefs
 pres_type :: "'s step_type => nat => 's set => bool"
"pres_type step n A == \<forall>s\<in>A. \<forall>p<n. \<forall>(q,s')\<in>set (step p s). s' \<in> A"

 mono :: "'s ord => 's step_type => nat => 's set => bool"
"mono r step n A ==
 \<forall>s p t. s \<in> A \<and> p < n \<and> s <=_r t --> step p s <=|r| step p t"

consts
 iter :: "'s binop \<Rightarrow> 's step_type \<Rightarrow>
          's list \<Rightarrow> nat set \<Rightarrow> 's list \<times> nat set"
 propa :: "'s binop => (nat \<times> 's) list => 's list => nat set => 's list * nat set"

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
 unstables :: "'s ord => 's step_type => 's list => nat set"
"unstables r step ss == {p. p < size ss \<and> \<not>stable r step ss p}"

 kildall :: "'s ord => 's binop => 's step_type => 's list => 's list"
"kildall r f step ss == fst(iter f step ss (unstables r step ss))"

consts merges :: "'s binop => (nat \<times> 's) list => 's list => 's list"
primrec
"merges f []      ss = ss"
"merges f (p'#ps) ss = (let (p,s) = p' in merges f ps (ss[p := s +_f ss!p]))"


lemmas [simp] = Let_def le_iff_plus_unchanged [symmetric]


consts
 "@plusplussub" :: "'a list => ('a => 'a => 'a) => 'a => 'a" ("(_ /++'__ _)" [65, 1000, 66] 65)
primrec
  "[] ++_f y = y"
  "(x#xs) ++_f y = xs ++_f (x +_f y)"

lemma nth_merges:
  "!!ss. [| semilat (A, r, f); p < length ss; ss \<in> list n A; 
            \<forall>(p,t)\<in>set ps. p<n \<and> t\<in>A |] ==>
  (merges f ps ss)!p = map snd [(p',t') \<in> ps. p'=p] ++_f ss!p"
  (is "!!ss. _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?steptype ps \<Longrightarrow> ?P ss ps")
proof (induct ps)
  show "\<And>ss. ?P ss []" by simp

  fix ss p' ps'
  assume sl: "semilat (A, r, f)"
  assume ss: "ss \<in> list n A"
  assume l:  "p < length ss"
  assume "?steptype (p'#ps')"
  then obtain a b where
    p': "p'=(a,b)" and ab: "a<n" "b\<in>A" and "?steptype ps'"
    by (cases p', auto)
  assume "\<And>ss. semilat (A,r,f) \<Longrightarrow> p < length ss \<Longrightarrow> ss \<in> list n A \<Longrightarrow> ?steptype ps' \<Longrightarrow> ?P ss ps'"
  hence IH: "\<And>ss. ss \<in> list n A \<Longrightarrow> p < length ss \<Longrightarrow> ?P ss ps'" .

  from sl ss ab
  have "ss[a := b +_f ss!a] \<in> list n A" by (simp add: closedD)
  moreover
  from calculation
  have "p < length (ss[a := b +_f ss!a])" by simp
  ultimately
  have "?P (ss[a := b +_f ss!a]) ps'" by (rule IH)
  with p' l 
  show "?P ss (p'#ps')" by simp
qed


lemma pres_typeD:
  "[| pres_type step n A; s\<in>A; p<n; (q,s')\<in>set (step p s) |] ==> s' \<in> A"
  by (unfold pres_type_def, blast)

lemma boundedD: 
  "[| bounded step n; p < n; (q,t) : set (step p xs) |] ==> q < n" 
  by (unfold bounded_def, blast)

lemma monoD:
  "[| mono r step n A; p < n; s\<in>A; s <=_r t |] ==> step p s <=|r| step p t"
  by (unfold mono_def, blast)

(** merges **)

lemma length_merges [rule_format, simp]:
  "\<forall>ss. size(merges f ps ss) = size ss"
  by (induct_tac ps, auto)


lemma merges_preserves_type_lemma: 
  "[| semilat(A,r,f) |] ==>
     \<forall>xs. xs \<in> list n A --> (\<forall>(p,x) \<in> set ps. p<n \<and> x\<in>A)
          --> merges f ps xs \<in> list n A" 
  apply (frule semilatDclosedI) 
  apply (unfold closed_def) 
  apply (induct_tac ps)
   apply simp
  apply clarsimp
  done

lemma merges_preserves_type [simp]:
  "[| semilat(A,r,f); xs \<in> list n A; \<forall>(p,x) \<in> set ps. p<n \<and> x\<in>A |]
  ==> merges f ps xs \<in> list n A"
  by (simp add: merges_preserves_type_lemma)
  
lemma merges_incr_lemma:
  "[| semilat(A,r,f) |] ==> 
     \<forall>xs. xs \<in> list n A --> (\<forall>(p,x)\<in>set ps. p<size xs \<and> x \<in> A) --> xs <=[r] merges f ps xs"
  apply (induct_tac ps)
   apply simp
  apply simp
  apply clarify
  apply (rule order_trans)
    apply simp
   apply (erule list_update_incr)
     apply assumption
    apply simp
   apply simp
  apply (blast intro!: listE_set intro: closedD listE_length [THEN nth_in])
  done

lemma merges_incr:
  "[| semilat(A,r,f); xs \<in> list n A; \<forall>(p,x)\<in>set ps. p<size xs \<and> x \<in> A |] 
  ==> xs <=[r] merges f ps xs"
  by (simp add: merges_incr_lemma)


lemma merges_same_conv [rule_format]:
  "[| semilat(A,r,f) |] ==> 
     (\<forall>xs. xs \<in> list n A --> (\<forall>(p,x)\<in>set ps. p<size xs \<and> x\<in>A) --> 
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
        apply assumption
       apply (blast intro!: listE_set intro: closedD listE_length [THEN nth_in])
      apply clarify
      apply (rule conjI)
       apply simp
       apply (blast dest: boundedD)
      apply blast
   apply clarify
   apply (rotate_tac -2)
   apply (erule allE)
   apply (erule impE)
    apply assumption
   apply (erule impE)
    apply assumption
   apply (drule bspec)
    apply assumption
   apply (simp add: le_iff_plus_unchanged [THEN iffD1] list_update_same_conv [THEN iffD2])
   apply blast
  apply clarify 
  apply (simp add: le_iff_plus_unchanged [THEN iffD1] list_update_same_conv [THEN iffD2])
  done


lemma list_update_le_listI [rule_format]:
  "set xs <= A --> set ys <= A --> xs <=[r] ys --> p < size xs -->  
   x <=_r ys!p --> semilat(A,r,f) --> x\<in>A --> 
   xs[p := x +_f xs!p] <=[r] ys"
  apply (unfold Listn.le_def lesub_def semilat_def)
  apply (simp add: list_all2_conv_all_nth nth_list_update)
  done

lemma merges_pres_le_ub:
  "[| semilat(A,r,f); set ts <= A; set ss <= A; 
     \<forall>(p,t)\<in>set ps. t <=_r ts!p \<and> t \<in> A \<and> p < size ts; 
     ss <=[r] ts |] 
  ==> merges f ps ss <=[r] ts"
proof -
  { fix A r f t ts ps
    have
    "!!qs. [| semilat(A,r,f); set ts <= A; 
              \<forall>(p,t)\<in>set ps. t <=_r ts!p \<and> t \<in> A \<and> p < size ts |] ==> 
    set qs <= set ps  --> 
    (\<forall>ss. set ss <= A --> ss <=[r] ts --> merges f qs ss <=[r] ts)"
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
  "!!ss w. (\<forall>(q,t)\<in>set qs. q < size ss) \<Longrightarrow> 
   propa f qs ss w = 
   (merges f qs ss, {q. \<exists>t. (q,t)\<in>set qs \<and> t +_f ss!q \<noteq> ss!q} Un w)"
  apply (induct qs)
   apply simp   
  apply (simp (no_asm))
  apply clarify  
  apply simp
  apply (rule conjI) 
   apply (simp add: nth_list_update)
   apply blast
  apply (simp add: nth_list_update)
  apply blast
  done 

(** iter **)

lemma plusplus_closed: 
  "\<And>y. \<lbrakk>semilat (A, r, f); set x \<subseteq> A; y \<in> A\<rbrakk> \<Longrightarrow> x ++_f y \<in> A"
proof (induct x)
  show "\<And>y. y \<in> A \<Longrightarrow> [] ++_f y \<in> A" by simp
  fix y x xs
  assume sl: "semilat (A, r, f)" and y: "y \<in> A" and xs: "set (x#xs) \<subseteq> A"
  assume IH: "\<And>y. \<lbrakk>semilat (A, r, f); set xs \<subseteq> A; y \<in> A\<rbrakk> \<Longrightarrow> xs ++_f y \<in> A"
  from xs obtain x: "x \<in> A" and "set xs \<subseteq> A" by simp  
  from sl x y have "(x +_f y) \<in> A" by (simp add: closedD)
  with sl xs have "xs ++_f (x +_f y) \<in> A" by - (rule IH)
  thus "(x#xs) ++_f y \<in> A" by simp
qed

lemma ub2: "!!y. \<lbrakk>semilat (A, r, f); set x \<subseteq> A; y \<in> A\<rbrakk> \<Longrightarrow> y <=_r x ++_f y"
proof (induct x)
  show "\<And>y. semilat(A, r, f) \<Longrightarrow> y <=_r [] ++_f y" by simp 
  
  fix y a l
  assume sl: "semilat (A, r, f)"
  assume y:  "y \<in> A"
  assume "set (a#l) \<subseteq> A"
  then obtain a: "a \<in> A" and x: "set l \<subseteq> A" by simp 
  assume "\<And>y. \<lbrakk>semilat (A, r, f); set l \<subseteq> A; y \<in> A\<rbrakk> \<Longrightarrow> y <=_r l ++_f y"
  hence IH: "\<And>y. y \<in> A \<Longrightarrow> y <=_r l ++_f y" .

  from sl have "order r" .. note order_trans [OF this, trans]  
  
  from sl a y have "y <=_r a +_f y" by (rule semilat_ub2)
  also
  from sl a y have "a +_f y \<in> A" by (simp add: closedD)
  hence "(a +_f y) <=_r l ++_f (a +_f y)" by (rule IH)
  finally
  have "y <=_r l ++_f (a +_f y)" .
  thus "y <=_r (a#l) ++_f y" by simp
qed


lemma ub1: "\<And>y. \<lbrakk>semilat (A, r, f); set ls \<subseteq> A; y \<in> A; x \<in> set ls\<rbrakk> \<Longrightarrow> x <=_r ls ++_f y"
proof (induct ls)
  show "\<And>y. x \<in> set [] \<Longrightarrow> x <=_r [] ++_f y" by simp
  
  fix y s ls
  assume sl: "semilat (A, r, f)" 
  hence "order r" .. note order_trans [OF this, trans]
  assume "set (s#ls) \<subseteq> A"
  then obtain s: "s \<in> A" and ls: "set ls \<subseteq> A" by simp
  assume y: "y \<in> A" 

  assume "\<And>y. \<lbrakk>semilat (A, r, f); set ls \<subseteq> A; y \<in> A; x \<in> set ls\<rbrakk> \<Longrightarrow> x <=_r ls ++_f y"
  hence IH: "\<And>y. x \<in> set ls \<Longrightarrow> y \<in> A \<Longrightarrow> x <=_r ls ++_f y" .

  assume "x \<in> set (s#ls)"
  then obtain xls: "x = s \<or> x \<in> set ls" by simp
  moreover {
    assume xs: "x = s"
    from sl s y have "s <=_r s +_f y" by (rule semilat_ub1)
    also
    from sl s y have "s +_f y \<in> A" by (simp add: closedD)
    with sl ls have "(s +_f y) <=_r ls ++_f (s +_f y)" by (rule ub2)
    finally 
    have "s <=_r ls ++_f (s +_f y)" .
    with xs have "x <=_r ls ++_f (s +_f y)" by simp
  } 
  moreover {
    assume "x \<in> set ls"
    hence "\<And>y. y \<in> A \<Longrightarrow> x <=_r ls ++_f y" by (rule IH)
    moreover
    from sl s y
    have "s +_f y \<in> A" by (simp add: closedD)
    ultimately 
    have "x <=_r ls ++_f (s +_f y)" .
  }
  ultimately 
  have "x <=_r ls ++_f (s +_f y)" by blast
  thus "x <=_r (s#ls) ++_f y" by simp
qed


lemma ub1': 
  "\<lbrakk>semilat (A, r, f); \<forall>(p,s) \<in> set S. s \<in> A; y \<in> A; (a,b) \<in> set S\<rbrakk> 
  \<Longrightarrow> b <=_r map snd [(p', t')\<in>S. p' = a] ++_f y" 
proof -
  let "b <=_r ?map ++_f y" = ?thesis

  assume "semilat (A, r, f)" "y \<in> A"
  moreover
  assume "\<forall>(p,s) \<in> set S. s \<in> A"
  hence "set ?map \<subseteq> A" by auto
  moreover
  assume "(a,b) \<in> set S"
  hence "b \<in> set ?map" by (induct S, auto)
  ultimately
  show ?thesis by - (rule ub1)
qed
    
 

lemma plusplus_empty:  
  "\<forall>s'. (q, s') \<in> set S \<longrightarrow> s' +_f ss ! q = ss ! q \<Longrightarrow>
   (map snd [(p', t')\<in> S. p' = q] ++_f ss ! q) = ss ! q"
apply (induct S)
apply auto 
done


lemma stable_pres_lemma:
  "[| semilat (A,r,f); pres_type step n A; bounded step n; 
     ss \<in> list n A; p \<in> w; \<forall>q\<in>w. q < n; 
     \<forall>q. q < n \<longrightarrow> q \<notin> w \<longrightarrow> stable r step ss q; q < n; 
     \<forall>s'. (q,s') \<in> set (step p (ss ! p)) \<longrightarrow> s' +_f ss ! q = ss ! q; 
     q \<notin> w \<or> q = p |] 
  ==> stable r step (merges f (step p (ss!p)) ss) q"
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
        apply assumption
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
  apply (frule nth_merges [of _ _ _ q _ _ "step p (ss!p)"]) (* fixme: why does method subst not work?? *)
    prefer 2 apply assumption
   apply simp
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
 apply (rule ub2)
    apply assumption
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
 
  
lemma lesub_step_type:
  "!!b x y. a <=|r| b \<Longrightarrow> (x,y) \<in> set a \<Longrightarrow> \<exists>y'. (x, y') \<in> set b \<and> y <=_r y'"
apply (induct a)
 apply simp
apply simp
apply (case_tac b)
 apply simp
apply simp
apply (erule disjE)
 apply clarify
 apply (simp add: lesub_def)
 apply blast   
apply clarify
apply blast
done


lemma merges_bounded_lemma:
  "[| semilat (A,r,f); mono r step n A; bounded step n; 
     \<forall>(p',s') \<in> set (step p (ss!p)). s' \<in> A; ss \<in> list n A; ts \<in> list n A; p < n; 
     ss <=[r] ts; ! p. p < n --> stable r step ts p |] 
  ==> merges f (step p (ss!p)) ss <=[r] ts"
  apply (unfold stable_def)
  apply (rule merges_pres_le_ub)
      apply assumption
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
  
  apply (drule lesub_step_type, assumption) 
  apply clarify
  apply (drule bspec, assumption)
  apply simp
  apply (blast intro: order_trans)
  done

lemma termination_lemma:  
  "[| semilat(A,r,f); ss \<in> list n A; \<forall>(q,t)\<in>set qs. q<n \<and> t\<in>A; p\<in>w |] ==> 
      ss <[r] merges f qs ss \<or> 
  merges f qs ss = ss \<and> {q. \<exists>t. (q,t)\<in>set qs \<and> t +_f ss!q \<noteq> ss!q} Un (w-{p}) < w"
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

lemma iter_properties[rule_format]:
  "\<lbrakk> semilat(A,r,f); acc r ; pres_type step n A; mono r step n A;
     bounded step n; \<forall>p\<in>w0. p < n; ss0 \<in> list n A;
     \<forall>p<n. p \<notin> w0 \<longrightarrow> stable r step ss0 p \<rbrakk> \<Longrightarrow>
   iter f step ss0 w0 = (ss',w')
   \<longrightarrow>
   ss' \<in> list n A \<and> stables r step ss' \<and> ss0 <=[r] ss' \<and>
   (\<forall>ts\<in>list n A. ss0 <=[r] ts \<and> stables r step ts \<longrightarrow> ss' <=[r] ts)"
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
 apply (erule merges_preserves_type)
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
 apply (drule (1) semilatDorderI [THEN acc_le_listI])
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
apply (blast dest!: boundedD)
done   


lemma kildall_properties:
  "\<lbrakk> semilat(A,r,f); acc r; pres_type step n A; mono r step n A;
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
apply (simp_all add: unstables_def stable_def)
done

lemma is_bcv_kildall:
  "[| semilat(A,r,f); acc r; top r T; 
      pres_type step n A; bounded step n; 
      mono r step n A |]
  ==> is_bcv r T step n A (kildall r f step)"
apply(unfold is_bcv_def wt_step_def)
apply(insert kildall_properties[of A])
apply(simp add:stables_def)
apply clarify
apply(subgoal_tac "kildall r f step ss \<in> list n A")
 prefer 2 apply (simp(no_asm_simp))
apply (rule iffI)
 apply (rule_tac x = "kildall r f step ss" in bexI) 
  apply (rule conjI)
   apply blast
  apply (simp  (no_asm_simp))
 apply assumption
apply clarify
apply(subgoal_tac "kildall r f step ss!p <=_r ts!p")
 apply simp
apply (blast intro!: le_listD less_lengthI)
done

end