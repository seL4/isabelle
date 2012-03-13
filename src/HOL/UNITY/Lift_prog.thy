(*  Title:      HOL/UNITY/Lift_prog.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1999  University of Cambridge

lift_prog, etc: replication of components and arrays of processes. 
*)

header{*Replication of Components*}

theory Lift_prog imports Rename begin

definition insert_map :: "[nat, 'b, nat=>'b] => (nat=>'b)" where
    "insert_map i z f k == if k<i then f k
                           else if k=i then z
                           else f(k - 1)"

definition delete_map :: "[nat, nat=>'b] => (nat=>'b)" where
    "delete_map i g k == if k<i then g k else g (Suc k)"

definition lift_map :: "[nat, 'b * ((nat=>'b) * 'c)] => (nat=>'b) * 'c" where
    "lift_map i == %(s,(f,uu)). (insert_map i s f, uu)"

definition drop_map :: "[nat, (nat=>'b) * 'c] => 'b * ((nat=>'b) * 'c)" where
    "drop_map i == %(g, uu). (g i, (delete_map i g, uu))"

definition lift_set :: "[nat, ('b * ((nat=>'b) * 'c)) set] => ((nat=>'b) * 'c) set" where
    "lift_set i A == lift_map i ` A"

definition lift :: "[nat, ('b * ((nat=>'b) * 'c)) program] => ((nat=>'b) * 'c) program" where
    "lift i == rename (lift_map i)"

  (*simplifies the expression of specifications*)
definition sub :: "['a, 'a=>'b] => 'b" where
    "sub == %i f. f i"


declare insert_map_def [simp] delete_map_def [simp]

lemma insert_map_inverse: "delete_map i (insert_map i x f) = f"
by (rule ext, simp)

lemma insert_map_delete_map_eq: "(insert_map i x (delete_map i g)) = g(i:=x)"
apply (rule ext)
apply (auto split add: nat_diff_split)
done

subsection{*Injectiveness proof*}

lemma insert_map_inject1: "(insert_map i x f) = (insert_map i y g) ==> x=y"
by (drule_tac x = i in fun_cong, simp)

lemma insert_map_inject2: "(insert_map i x f) = (insert_map i y g) ==> f=g"
apply (drule_tac f = "delete_map i" in arg_cong)
apply (simp add: insert_map_inverse)
done

lemma insert_map_inject':
     "(insert_map i x f) = (insert_map i y g) ==> x=y & f=g"
by (blast dest: insert_map_inject1 insert_map_inject2)

lemmas insert_map_inject = insert_map_inject' [THEN conjE, elim!]

(*The general case: we don't assume i=i'*)
lemma lift_map_eq_iff [iff]: 
     "(lift_map i (s,(f,uu)) = lift_map i' (s',(f',uu')))  
      = (uu = uu' & insert_map i s f = insert_map i' s' f')"
by (unfold lift_map_def, auto)

(*The !!s allows the automatic splitting of the bound variable*)
lemma drop_map_lift_map_eq [simp]: "!!s. drop_map i (lift_map i s) = s"
apply (unfold lift_map_def drop_map_def)
apply (force intro: insert_map_inverse)
done

lemma inj_lift_map: "inj (lift_map i)"
apply (unfold lift_map_def)
apply (rule inj_onI, auto)
done

subsection{*Surjectiveness proof*}

lemma lift_map_drop_map_eq [simp]: "!!s. lift_map i (drop_map i s) = s"
apply (unfold lift_map_def drop_map_def)
apply (force simp add: insert_map_delete_map_eq)
done

lemma drop_map_inject [dest!]: "(drop_map i s) = (drop_map i s') ==> s=s'"
by (drule_tac f = "lift_map i" in arg_cong, simp)

lemma surj_lift_map: "surj (lift_map i)"
apply (rule surjI)
apply (rule lift_map_drop_map_eq)
done

lemma bij_lift_map [iff]: "bij (lift_map i)"
by (simp add: bij_def inj_lift_map surj_lift_map)

lemma inv_lift_map_eq [simp]: "inv (lift_map i) = drop_map i"
by (rule inv_equality, auto)

lemma inv_drop_map_eq [simp]: "inv (drop_map i) = lift_map i"
by (rule inv_equality, auto)

lemma bij_drop_map [iff]: "bij (drop_map i)"
by (simp del: inv_lift_map_eq add: inv_lift_map_eq [symmetric] bij_imp_bij_inv)

(*sub's main property!*)
lemma sub_apply [simp]: "sub i f = f i"
by (simp add: sub_def)

lemma all_total_lift: "all_total F ==> all_total (lift i F)"
by (simp add: lift_def rename_def Extend.all_total_extend)

lemma insert_map_upd_same: "(insert_map i t f)(i := s) = insert_map i s f"
by (rule ext, auto)

lemma insert_map_upd:
     "(insert_map j t f)(i := s) =  
      (if i=j then insert_map i s f  
       else if i<j then insert_map j t (f(i:=s))  
       else insert_map j t (f(i - Suc 0 := s)))"
apply (rule ext) 
apply (simp split add: nat_diff_split)
 txt{*This simplification is VERY slow*}
done

lemma insert_map_eq_diff:
     "[| insert_map i s f = insert_map j t g;  i\<noteq>j |]  
      ==> \<exists>g'. insert_map i s' f = insert_map j t g'"
apply (subst insert_map_upd_same [symmetric])
apply (erule ssubst)
apply (simp only: insert_map_upd if_False split: split_if, blast)
done

lemma lift_map_eq_diff: 
     "[| lift_map i (s,(f,uu)) = lift_map j (t,(g,vv));  i\<noteq>j |]  
      ==> \<exists>g'. lift_map i (s',(f,uu)) = lift_map j (t,(g',vv))"
apply (unfold lift_map_def, auto)
apply (blast dest: insert_map_eq_diff)
done


subsection{*The Operator @{term lift_set}*}

lemma lift_set_empty [simp]: "lift_set i {} = {}"
by (unfold lift_set_def, auto)

lemma lift_set_iff: "(lift_map i x \<in> lift_set i A) = (x \<in> A)"
apply (unfold lift_set_def)
apply (rule inj_lift_map [THEN inj_image_mem_iff])
done

(*Do we really need both this one and its predecessor?*)
lemma lift_set_iff2 [iff]:
     "((f,uu) \<in> lift_set i A) = ((f i, (delete_map i f, uu)) \<in> A)"
by (simp add: lift_set_def mem_rename_set_iff drop_map_def)


lemma lift_set_mono: "A \<subseteq> B ==> lift_set i A \<subseteq> lift_set i B"
apply (unfold lift_set_def)
apply (erule image_mono)
done

lemma lift_set_Un_distrib: "lift_set i (A \<union> B) = lift_set i A \<union> lift_set i B"
by (simp add: lift_set_def image_Un)

lemma lift_set_Diff_distrib: "lift_set i (A-B) = lift_set i A - lift_set i B"
apply (unfold lift_set_def)
apply (rule inj_lift_map [THEN image_set_diff])
done


subsection{*The Lattice Operations*}

lemma bij_lift [iff]: "bij (lift i)"
by (simp add: lift_def)

lemma lift_SKIP [simp]: "lift i SKIP = SKIP"
by (simp add: lift_def)

lemma lift_Join [simp]: "lift i (F Join G) = lift i F Join lift i G"
by (simp add: lift_def)

lemma lift_JN [simp]: "lift j (JOIN I F) = (\<Squnion>i \<in> I. lift j (F i))"
by (simp add: lift_def)

subsection{*Safety: constrains, stable, invariant*}

lemma lift_constrains: 
     "(lift i F \<in> (lift_set i A) co (lift_set i B)) = (F \<in> A co B)"
by (simp add: lift_def lift_set_def rename_constrains)

lemma lift_stable: 
     "(lift i F \<in> stable (lift_set i A)) = (F \<in> stable A)"
by (simp add: lift_def lift_set_def rename_stable)

lemma lift_invariant: 
     "(lift i F \<in> invariant (lift_set i A)) = (F \<in> invariant A)"
by (simp add: lift_def lift_set_def rename_invariant)

lemma lift_Constrains: 
     "(lift i F \<in> (lift_set i A) Co (lift_set i B)) = (F \<in> A Co B)"
by (simp add: lift_def lift_set_def rename_Constrains)

lemma lift_Stable: 
     "(lift i F \<in> Stable (lift_set i A)) = (F \<in> Stable A)"
by (simp add: lift_def lift_set_def rename_Stable)

lemma lift_Always: 
     "(lift i F \<in> Always (lift_set i A)) = (F \<in> Always A)"
by (simp add: lift_def lift_set_def rename_Always)

subsection{*Progress: transient, ensures*}

lemma lift_transient: 
     "(lift i F \<in> transient (lift_set i A)) = (F \<in> transient A)"
by (simp add: lift_def lift_set_def rename_transient)

lemma lift_ensures: 
     "(lift i F \<in> (lift_set i A) ensures (lift_set i B)) =  
      (F \<in> A ensures B)"
by (simp add: lift_def lift_set_def rename_ensures)

lemma lift_leadsTo: 
     "(lift i F \<in> (lift_set i A) leadsTo (lift_set i B)) =  
      (F \<in> A leadsTo B)"
by (simp add: lift_def lift_set_def rename_leadsTo)

lemma lift_LeadsTo: 
     "(lift i F \<in> (lift_set i A) LeadsTo (lift_set i B)) =   
      (F \<in> A LeadsTo B)"
by (simp add: lift_def lift_set_def rename_LeadsTo)


(** guarantees **)

lemma lift_lift_guarantees_eq: 
     "(lift i F \<in> (lift i ` X) guarantees (lift i ` Y)) =  
      (F \<in> X guarantees Y)"
apply (unfold lift_def)
apply (subst bij_lift_map [THEN rename_rename_guarantees_eq, symmetric])
apply (simp add: o_def)
done

lemma lift_guarantees_eq_lift_inv:
     "(lift i F \<in> X guarantees Y) =  
      (F \<in> (rename (drop_map i) ` X) guarantees (rename (drop_map i) ` Y))"
by (simp add: bij_lift_map [THEN rename_guarantees_eq_rename_inv] lift_def)


(*To preserve snd means that the second component is there just to allow
  guarantees properties to be stated.  Converse fails, for lift i F can 
  change function components other than i*)
lemma lift_preserves_snd_I: "F \<in> preserves snd ==> lift i F \<in> preserves snd"
apply (drule_tac w1=snd in subset_preserves_o [THEN subsetD])
apply (simp add: lift_def rename_preserves)
apply (simp add: lift_map_def o_def split_def)
done

lemma delete_map_eqE':
     "(delete_map i g) = (delete_map i g') ==> \<exists>x. g = g'(i:=x)"
apply (drule_tac f = "insert_map i (g i) " in arg_cong)
apply (simp add: insert_map_delete_map_eq)
apply (erule exI)
done

lemmas delete_map_eqE = delete_map_eqE' [THEN exE, elim!]

lemma delete_map_neq_apply:
     "[| delete_map j g = delete_map j g';  i\<noteq>j |] ==> g i = g' i"
by force

(*A set of the form (A <*> UNIV) ignores the second (dummy) state component*)

lemma vimage_o_fst_eq [simp]: "(f o fst) -` A = (f-`A) <*> UNIV"
by auto

lemma vimage_sub_eq_lift_set [simp]:
     "(sub i -`A) <*> UNIV = lift_set i (A <*> UNIV)"
by auto

lemma mem_lift_act_iff [iff]: 
     "((s,s') \<in> extend_act (%(x,u::unit). lift_map i x) act) =  
      ((drop_map i s, drop_map i s') \<in> act)"
apply (unfold extend_act_def, auto)
apply (rule bexI, auto)
done

lemma preserves_snd_lift_stable:
     "[| F \<in> preserves snd;  i\<noteq>j |]  
      ==> lift j F \<in> stable (lift_set i (A <*> UNIV))"
apply (auto simp add: lift_def lift_set_def stable_def constrains_def 
                      rename_def extend_def mem_rename_set_iff)
apply (auto dest!: preserves_imp_eq simp add: lift_map_def drop_map_def)
apply (drule_tac x = i in fun_cong, auto)
done

(*If i\<noteq>j then lift j F  does nothing to lift_set i, and the 
  premise ensures A \<subseteq> B.*)
lemma constrains_imp_lift_constrains:
    "[| F i \<in> (A <*> UNIV) co (B <*> UNIV);   
        F j \<in> preserves snd |]   
     ==> lift j (F j) \<in> (lift_set i (A <*> UNIV)) co (lift_set i (B <*> UNIV))"
apply (cases "i=j")
apply (simp add: lift_def lift_set_def rename_constrains)
apply (erule preserves_snd_lift_stable[THEN stableD, THEN constrains_weaken_R],
       assumption)
apply (erule constrains_imp_subset [THEN lift_set_mono])
done

(*USELESS??*)
lemma lift_map_image_Times:
     "lift_map i ` (A <*> UNIV) =  
      (\<Union>s \<in> A. \<Union>f. {insert_map i s f}) <*> UNIV"
apply (auto intro!: bexI image_eqI simp add: lift_map_def)
apply (rule split_conv [symmetric])
done

lemma lift_preserves_eq:
     "(lift i F \<in> preserves v) = (F \<in> preserves (v o lift_map i))"
by (simp add: lift_def rename_preserves)

(*A useful rewrite.  If o, sub have been rewritten out already then can also
  use it as   rewrite_rule [sub_def, o_def] lift_preserves_sub*)
lemma lift_preserves_sub:
     "F \<in> preserves snd  
      ==> lift i F \<in> preserves (v o sub j o fst) =  
          (if i=j then F \<in> preserves (v o fst) else True)"
apply (drule subset_preserves_o [THEN subsetD])
apply (simp add: lift_preserves_eq o_def)
apply (auto cong del: if_weak_cong 
       simp add: lift_map_def eq_commute split_def o_def)
done


subsection{*Lemmas to Handle Function Composition (o) More Consistently*}

(*Lets us prove one version of a theorem and store others*)
lemma o_equiv_assoc: "f o g = h ==> f' o f o g = f' o h"
by (simp add: fun_eq_iff o_def)

lemma o_equiv_apply: "f o g = h ==> \<forall>x. f(g x) = h x"
by (simp add: fun_eq_iff o_def)

lemma fst_o_lift_map: "sub i o fst o lift_map i = fst"
apply (rule ext)
apply (auto simp add: o_def lift_map_def sub_def)
done

lemma snd_o_lift_map: "snd o lift_map i = snd o snd"
apply (rule ext)
apply (auto simp add: o_def lift_map_def)
done


subsection{*More lemmas about extend and project*}

text{*They could be moved to theory Extend or Project*}

lemma extend_act_extend_act:
     "extend_act h' (extend_act h act) =  
      extend_act (%(x,(y,y')). h'(h(x,y),y')) act"
apply (auto elim!: rev_bexI simp add: extend_act_def, blast) 
done

lemma project_act_project_act:
     "project_act h (project_act h' act) =  
      project_act (%(x,(y,y')). h'(h(x,y),y')) act"
by (auto elim!: rev_bexI simp add: project_act_def)

lemma project_act_extend_act:
     "project_act h (extend_act h' act) =  
        {(x,x'). \<exists>s s' y y' z. (s,s') \<in> act &  
                 h(x,y) = h'(s,z) & h(x',y') = h'(s',z)}"
by (simp add: extend_act_def project_act_def, blast)


subsection{*OK and "lift"*}

lemma act_in_UNION_preserves_fst:
     "act \<subseteq> {(x,x'). fst x = fst x'} ==> act \<in> UNION (preserves fst) Acts"
apply (rule_tac a = "mk_program (UNIV,{act},UNIV) " in UN_I)
apply (auto simp add: preserves_def stable_def constrains_def)
done

lemma UNION_OK_lift_I:
     "[| \<forall>i \<in> I. F i \<in> preserves snd;   
         \<forall>i \<in> I. UNION (preserves fst) Acts \<subseteq> AllowedActs (F i) |]  
      ==> OK I (%i. lift i (F i))"
apply (auto simp add: OK_def lift_def rename_def Extend.Acts_extend)
apply (simp add: Extend.AllowedActs_extend project_act_extend_act)
apply (rename_tac "act")
apply (subgoal_tac
       "{(x, x'). \<exists>s f u s' f' u'. 
                    ((s, f, u), s', f', u') \<in> act & 
                    lift_map j x = lift_map i (s, f, u) & 
                    lift_map j x' = lift_map i (s', f', u') } 
                \<subseteq> { (x,x') . fst x = fst x'}")
apply (blast intro: act_in_UNION_preserves_fst, clarify)
apply (drule_tac x = j in fun_cong)+
apply (drule_tac x = i in bspec, assumption)
apply (frule preserves_imp_eq, auto)
done

lemma OK_lift_I:
     "[| \<forall>i \<in> I. F i \<in> preserves snd;   
         \<forall>i \<in> I. preserves fst \<subseteq> Allowed (F i) |]  
      ==> OK I (%i. lift i (F i))"
by (simp add: safety_prop_AllowedActs_iff_Allowed UNION_OK_lift_I)

lemma Allowed_lift [simp]: "Allowed (lift i F) = lift i ` (Allowed F)"
by (simp add: lift_def)

lemma lift_image_preserves:
     "lift i ` preserves v = preserves (v o drop_map i)"
by (simp add: rename_image_preserves lift_def)

end
