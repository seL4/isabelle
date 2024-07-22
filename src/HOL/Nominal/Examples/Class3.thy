theory Class3
  imports Class2
begin

text \<open>3rd Main Lemma\<close>

lemma Cut_a_redu_elim:
  assumes a: "Cut <a>.M (x).N \<longrightarrow>\<^sub>a R"
  shows "(\<exists>M'. R = Cut <a>.M' (x).N \<and> M \<longrightarrow>\<^sub>a M') \<or>
         (\<exists>N'. R = Cut <a>.M (x).N' \<and> N \<longrightarrow>\<^sub>a N') \<or>
         (Cut <a>.M (x).N \<longrightarrow>\<^sub>c R) \<or>
         (Cut <a>.M (x).N \<longrightarrow>\<^sub>l R)"
  using a
  apply(erule_tac a_redu.cases)
                  apply(simp_all)
   apply(simp_all add: trm.inject)
   apply(rule disjI1)
   apply(auto simp add: alpha)[1]
    apply(rule_tac x="[(a,aa)]\<bullet>M'" in exI)
    apply(perm_simp add: fresh_left calc_atm a_redu.eqvt fresh_a_redu)
   apply(rule_tac x="[(a,aa)]\<bullet>M'" in exI)
   apply(perm_simp add: fresh_left calc_atm a_redu.eqvt fresh_a_redu)
  apply(rule disjI2)
  apply(rule disjI1)
  apply(auto simp add: alpha)[1]
   apply(rule_tac x="[(x,xa)]\<bullet>N'" in exI)
   apply(perm_simp add: fresh_left calc_atm a_redu.eqvt fresh_a_redu)
  apply(rule_tac x="[(x,xa)]\<bullet>N'" in exI)
  apply(perm_simp add: fresh_left calc_atm a_redu.eqvt fresh_a_redu)
  done

lemma Cut_c_redu_elim:
  assumes a: "Cut <a>.M (x).N \<longrightarrow>\<^sub>c R"
  shows "(R = M{a:=(x).N} \<and> \<not>fic M a) \<or>
         (R = N{x:=<a>.M} \<and> \<not>fin N x)"
  using a
  apply(erule_tac c_redu.cases)
   apply(simp_all)
   apply(simp_all add: trm.inject)
   apply(rule disjI1)
   apply(auto simp add: alpha)[1]
       apply(simp add: subst_rename fresh_atm)
      apply(simp add: subst_rename fresh_atm)
     apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
     apply(perm_simp)
    apply(simp add: subst_rename fresh_atm fresh_prod)
   apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
   apply(perm_simp)
  apply(rule disjI2)
  apply(auto simp add: alpha)[1]
      apply(simp add: subst_rename fresh_atm)
     apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
     apply(perm_simp)
    apply(simp add: subst_rename fresh_atm fresh_prod)
   apply(simp add: subst_rename fresh_atm fresh_prod)
  apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
  apply(perm_simp)
  done

lemma not_fic_crename_aux:
  assumes a: "fic M c" "c\<sharp>(a,b)"
  shows "fic (M[a\<turnstile>c>b]) c" 
  using a
  apply(nominal_induct M avoiding: c a b rule: trm.strong_induct)
             apply(auto dest!: fic_elims intro!: fic.intros simp add: fresh_prod fresh_atm rename_fresh abs_fresh)
  done

lemma not_fic_crename:
  assumes a: "\<not>(fic (M[a\<turnstile>c>b]) c)" "c\<sharp>(a,b)"
  shows "\<not>(fic M c)" 
  using a
  apply(auto dest:  not_fic_crename_aux)
  done

lemma not_fin_crename_aux:
  assumes a: "fin M y"
  shows "fin (M[a\<turnstile>c>b]) y" 
  using a
  apply(nominal_induct M avoiding: a b rule: trm.strong_induct)
             apply(auto dest!: fin_elims intro!: fin.intros simp add: fresh_prod fresh_atm rename_fresh abs_fresh)
  done

lemma not_fin_crename:
  assumes a: "\<not>(fin (M[a\<turnstile>c>b]) y)" 
  shows "\<not>(fin M y)" 
  using a
  apply(auto dest:  not_fin_crename_aux)
  done

lemma crename_fresh_interesting1:
  fixes c::"coname"
  assumes a: "c\<sharp>(M[a\<turnstile>c>b])" "c\<sharp>(a,b)"
  shows "c\<sharp>M"
  using a
  apply(nominal_induct M avoiding: c a b rule: trm.strong_induct)
             apply(auto split: if_splits simp add: abs_fresh)
  done

lemma crename_fresh_interesting2:
  fixes x::"name"
  assumes a: "x\<sharp>(M[a\<turnstile>c>b])" 
  shows "x\<sharp>M"
  using a
  apply(nominal_induct M avoiding: x a b rule: trm.strong_induct)
             apply(auto split: if_splits simp add: abs_fresh abs_supp fin_supp fresh_atm)
  done


lemma fic_crename:
  assumes a: "fic (M[a\<turnstile>c>b]) c" "c\<sharp>(a,b)"
  shows "fic M c" 
  using a
  apply(nominal_induct M avoiding: c a b rule: trm.strong_induct)
             apply(auto dest!: fic_elims intro!: fic.intros simp add: fresh_prod fresh_atm rename_fresh abs_fresh
      split: if_splits)
       apply(auto dest: crename_fresh_interesting1 simp add: fresh_prod fresh_atm)
  done

lemma fin_crename:
  assumes a: "fin (M[a\<turnstile>c>b]) x"
  shows "fin M x" 
  using a
  apply(nominal_induct M avoiding: x a b rule: trm.strong_induct)
             apply(auto dest!: fin_elims intro!: fin.intros simp add: fresh_prod fresh_atm rename_fresh abs_fresh
      split: if_splits)
        apply(auto dest: crename_fresh_interesting2 simp add: fresh_prod fresh_atm)
  done

lemma crename_Cut:
  assumes a: "R[a\<turnstile>c>b] = Cut <c>.M (x).N" "c\<sharp>(a,b,N,R)" "x\<sharp>(M,R)"
  shows "\<exists>M' N'. R = Cut <c>.M' (x).N' \<and> M'[a\<turnstile>c>b] = M \<and> N'[a\<turnstile>c>b] = N \<and> c\<sharp>N' \<and> x\<sharp>M'"
  using a
  apply(nominal_induct R avoiding: a b c x M N rule: trm.strong_induct)
             apply(auto split: if_splits)
  apply(simp add: trm.inject)
  apply(auto simp add: alpha)
    apply(rule_tac x="[(name,x)]\<bullet>trm2" in exI)
    apply(perm_simp)
    apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
    apply(drule sym)
    apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
    apply(simp add: eqvts calc_atm)
   apply(rule_tac x="[(coname,c)]\<bullet>trm1" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
   apply(auto simp add: fresh_atm)[1]
  apply(rule_tac x="[(coname,c)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule_tac x="[(name,x)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  apply(auto simp add: fresh_atm)[1]
   apply(drule sym)
   apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_NotR:
  assumes a: "R[a\<turnstile>c>b] = NotR (x).N c" "x\<sharp>R" "c\<sharp>(a,b)"
  shows "\<exists>N'. (R = NotR (x).N' c) \<and> N'[a\<turnstile>c>b] = N" 
  using a
  apply(nominal_induct R avoiding: a b c x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(name,x)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_NotR':
  assumes a: "R[a\<turnstile>c>b] = NotR (x).N c" "x\<sharp>R" "c\<sharp>a"
  shows "(\<exists>N'. (R = NotR (x).N' c) \<and> N'[a\<turnstile>c>b] = N) \<or> (\<exists>N'. (R = NotR (x).N' a) \<and> b=c \<and> N'[a\<turnstile>c>b] = N)"
  using a
  apply(nominal_induct R avoiding: a b c x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm abs_fresh alpha trm.inject)
   apply(rule_tac x="[(name,x)]\<bullet>trm" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(name,x)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_NotR_aux:
  assumes a: "R[a\<turnstile>c>b] = NotR (x).N c" 
  shows "(a=c \<and> a=b) \<or> (a\<noteq>c)" 
  using a
  apply(nominal_induct R avoiding: a b c x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma crename_NotL:
  assumes a: "R[a\<turnstile>c>b] = NotL <c>.N y" "c\<sharp>(R,a,b)"
  shows "\<exists>N'. (R = NotL <c>.N' y) \<and> N'[a\<turnstile>c>b] = N" 
  using a
  apply(nominal_induct R avoiding: a b c y N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(coname,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_AndL1:
  assumes a: "R[a\<turnstile>c>b] = AndL1 (x).N y" "x\<sharp>R"
  shows "\<exists>N'. (R = AndL1 (x).N' y) \<and> N'[a\<turnstile>c>b] = N" 
  using a
  apply(nominal_induct R avoiding: a b x y N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(name1,x)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_AndL2:
  assumes a: "R[a\<turnstile>c>b] = AndL2 (x).N y" "x\<sharp>R"
  shows "\<exists>N'. (R = AndL2 (x).N' y) \<and> N'[a\<turnstile>c>b] = N" 
  using a
  apply(nominal_induct R avoiding: a b x y N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(name1,x)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_AndR_aux:
  assumes a: "R[a\<turnstile>c>b] = AndR <c>.M <d>.N e" 
  shows "(a=e \<and> a=b) \<or> (a\<noteq>e)" 
  using a
  apply(nominal_induct R avoiding: a b c d e M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma crename_AndR:
  assumes a: "R[a\<turnstile>c>b] = AndR <c>.M <d>.N e" "c\<sharp>(a,b,d,e,N,R)" "d\<sharp>(a,b,c,e,M,R)" "e\<sharp>(a,b)"
  shows "\<exists>M' N'. R = AndR <c>.M' <d>.N' e \<and> M'[a\<turnstile>c>b] = M \<and> N'[a\<turnstile>c>b] = N \<and> c\<sharp>N' \<and> d\<sharp>M'"
  using a
  apply(nominal_induct R avoiding: a b c d e M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: trm.inject alpha)
        apply(simp add: fresh_atm fresh_prod)
       apply(rule_tac x="[(coname2,d)]\<bullet>trm2" in exI)
       apply(perm_simp)
       apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
      apply(rule_tac x="[(coname1,c)]\<bullet>trm1" in exI)
      apply(perm_simp)
      apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
     apply(rule_tac x="[(coname1,c)]\<bullet>trm1" in exI)
     apply(perm_simp)
     apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
    apply(rule_tac x="[(coname2,d)]\<bullet>trm2" in exI)
    apply(perm_simp)
    apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(rule_tac x="[(coname1,c)]\<bullet>trm1" in exI)
   apply(perm_simp)
   apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(coname1,c)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(coname2,d)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule_tac s="trm2[a\<turnstile>c>b]" in  sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_AndR':
  assumes a: "R[a\<turnstile>c>b] = AndR <c>.M <d>.N e" "c\<sharp>(a,b,d,e,N,R)" "d\<sharp>(a,b,c,e,M,R)" "e\<sharp>a"
  shows "(\<exists>M' N'. R = AndR <c>.M' <d>.N' e \<and> M'[a\<turnstile>c>b] = M \<and> N'[a\<turnstile>c>b] = N \<and> c\<sharp>N' \<and> d\<sharp>M') \<or>
         (\<exists>M' N'. R = AndR <c>.M' <d>.N' a \<and> b=e \<and> M'[a\<turnstile>c>b] = M \<and> N'[a\<turnstile>c>b] = N \<and> c\<sharp>N' \<and> d\<sharp>M')"
  using a [[simproc del: defined_all]]
  apply(nominal_induct R avoiding: a b c d e M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: trm.inject alpha)[1]
            apply(auto split: if_splits simp add: trm.inject alpha)[1]
           apply(auto split: if_splits simp add: trm.inject alpha)[1]
          apply(auto split: if_splits simp add: trm.inject alpha)[1]
         apply(simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm trm.inject alpha)[1]
         apply(case_tac "coname3=a")
          apply(simp)
          apply(rule_tac x="[(coname1,c)]\<bullet>trm1" in exI)
          apply(perm_simp)
          apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
          apply(rule_tac x="[(coname2,d)]\<bullet>trm2" in exI)
          apply(perm_simp)
          apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm trm.inject alpha split: if_splits)[1]
           apply(drule sym)
           apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
           apply(simp add: eqvts calc_atm)
          apply(drule_tac s="trm2[a\<turnstile>c>e]" in  sym)
          apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
          apply(simp add: eqvts calc_atm)
         apply(simp)
         apply(rule_tac x="[(coname1,c)]\<bullet>trm1" in exI)
         apply(perm_simp)
         apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
         apply(rule_tac x="[(coname2,d)]\<bullet>trm2" in exI)
         apply(perm_simp)
         apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm trm.inject alpha split: if_splits)[1]
          apply(drule sym)
          apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
          apply(simp add: eqvts calc_atm)
         apply(drule_tac s="trm2[a\<turnstile>c>b]" in  sym)
         apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
         apply(simp add: eqvts calc_atm)
        apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma crename_OrR1_aux:
  assumes a: "R[a\<turnstile>c>b] = OrR1 <c>.M e" 
  shows "(a=e \<and> a=b) \<or> (a\<noteq>e)" 
  using a
  apply(nominal_induct R avoiding: a b c e M rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma crename_OrR1:
  assumes a: "R[a\<turnstile>c>b] = OrR1 <c>.N d" "c\<sharp>(R,a,b)" "d\<sharp>(a,b)"
  shows "\<exists>N'. (R = OrR1 <c>.N' d) \<and> N'[a\<turnstile>c>b] = N" 
  using a
  apply(nominal_induct R avoiding: a b c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(coname1,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_OrR1':
  assumes a: "R[a\<turnstile>c>b] = OrR1 <c>.N d" "c\<sharp>(R,a,b)" "d\<sharp>a"
  shows "(\<exists>N'. (R = OrR1 <c>.N' d) \<and> N'[a\<turnstile>c>b] = N) \<or>
         (\<exists>N'. (R = OrR1 <c>.N' a) \<and> b=d \<and> N'[a\<turnstile>c>b] = N)" 
  using a
  apply(nominal_induct R avoiding: a b c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
   apply(rule_tac x="[(coname1,c)]\<bullet>trm" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(coname1,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_OrR2_aux:
  assumes a: "R[a\<turnstile>c>b] = OrR2 <c>.M e" 
  shows "(a=e \<and> a=b) \<or> (a\<noteq>e)" 
  using a
  apply(nominal_induct R avoiding: a b c e M rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma crename_OrR2:
  assumes a: "R[a\<turnstile>c>b] = OrR2 <c>.N d" "c\<sharp>(R,a,b)" "d\<sharp>(a,b)"
  shows "\<exists>N'. (R = OrR2 <c>.N' d) \<and> N'[a\<turnstile>c>b] = N" 
  using a
  apply(nominal_induct R avoiding: a b c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(coname1,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_OrR2':
  assumes a: "R[a\<turnstile>c>b] = OrR2 <c>.N d" "c\<sharp>(R,a,b)" "d\<sharp>a"
  shows "(\<exists>N'. (R = OrR2 <c>.N' d) \<and> N'[a\<turnstile>c>b] = N) \<or>
         (\<exists>N'. (R = OrR2 <c>.N' a) \<and> b=d \<and> N'[a\<turnstile>c>b] = N)" 
  using a
  apply(nominal_induct R avoiding: a b c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
   apply(rule_tac x="[(coname1,c)]\<bullet>trm" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(coname1,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_OrL:
  assumes a: "R[a\<turnstile>c>b] = OrL (x).M (y).N z" "x\<sharp>(y,z,N,R)" "y\<sharp>(x,z,M,R)"
  shows "\<exists>M' N'. R = OrL (x).M' (y).N' z \<and> M'[a\<turnstile>c>b] = M \<and> N'[a\<turnstile>c>b] = N \<and> x\<sharp>N' \<and> y\<sharp>M'"
  using a
  apply(nominal_induct R avoiding: a b x y z M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: trm.inject alpha)
    apply(rule_tac x="[(name2,y)]\<bullet>trm2" in exI)
    apply(perm_simp)
    apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(rule_tac x="[(name1,x)]\<bullet>trm1" in exI)
   apply(perm_simp)
   apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(name1,x)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(name2,y)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(drule sym)
   apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule_tac s="trm2[a\<turnstile>c>b]" in  sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_ImpL:
  assumes a: "R[a\<turnstile>c>b] = ImpL <c>.M (y).N z" "c\<sharp>(a,b,N,R)" "y\<sharp>(z,M,R)"
  shows "\<exists>M' N'. R = ImpL <c>.M' (y).N' z \<and> M'[a\<turnstile>c>b] = M \<and> N'[a\<turnstile>c>b] = N \<and> c\<sharp>N' \<and> y\<sharp>M'"
  using a
  apply(nominal_induct R avoiding: a b c y z M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: trm.inject alpha)
    apply(rule_tac x="[(name1,y)]\<bullet>trm2" in exI)
    apply(perm_simp)
    apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(rule_tac x="[(coname,c)]\<bullet>trm1" in exI)
   apply(perm_simp)
   apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(coname,c)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(name1,y)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule_tac s="trm2[a\<turnstile>c>b]" in  sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_ImpR_aux:
  assumes a: "R[a\<turnstile>c>b] = ImpR (x).<c>.M e" 
  shows "(a=e \<and> a=b) \<or> (a\<noteq>e)" 
  using a
  apply(nominal_induct R avoiding: x a b c e M rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma crename_ImpR:
  assumes a: "R[a\<turnstile>c>b] = ImpR (x).<c>.N d" "c\<sharp>(R,a,b)" "d\<sharp>(a,b)" "x\<sharp>R" 
  shows "\<exists>N'. (R = ImpR (x).<c>.N' d) \<and> N'[a\<turnstile>c>b] = N" 
  using a
  apply(nominal_induct R avoiding: a b x c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm abs_perm alpha abs_fresh trm.inject)
   apply(rule_tac x="[(name,x)]\<bullet>trm" in exI)
   apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule_tac x="[(name,x)]\<bullet>[(coname1, c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_supp fin_supp abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_ImpR':
  assumes a: "R[a\<turnstile>c>b] = ImpR (x).<c>.N d" "c\<sharp>(R,a,b)" "x\<sharp>R" "d\<sharp>a"
  shows "(\<exists>N'. (R = ImpR (x).<c>.N' d) \<and> N'[a\<turnstile>c>b] = N) \<or>
         (\<exists>N'. (R = ImpR (x).<c>.N' a) \<and> b=d \<and> N'[a\<turnstile>c>b] = N)" 
  using a
  apply(nominal_induct R avoiding: x a b c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject abs_perm calc_atm)
   apply(rule_tac x="[(name,x)]\<bullet>[(coname1,c)]\<bullet>trm" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod abs_supp fin_supp)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(name,x)]\<bullet>[(coname1,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod abs_supp fin_supp)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma crename_ax2:
  assumes a: "N[a\<turnstile>c>b] = Ax x c"
  shows "\<exists>d. N = Ax x d"
  using a
  apply(nominal_induct N avoiding: a b rule: trm.strong_induct)
             apply(auto split: if_splits)
  apply(simp add: trm.inject)
  done

lemma crename_interesting1:
  assumes a: "distinct [a,b,c]"
  shows "M[a\<turnstile>c>c][c\<turnstile>c>b] = M[c\<turnstile>c>b][a\<turnstile>c>b]"
  using a
  apply(nominal_induct M avoiding: a c b rule: trm.strong_induct)
             apply(auto simp add: rename_fresh simp add: trm.inject alpha)
     apply(blast)
    apply(rotate_tac 12)
    apply(drule_tac x="a" in meta_spec)
    apply(rotate_tac 15)
    apply(drule_tac x="c" in meta_spec)
    apply(rotate_tac 15)
    apply(drule_tac x="b" in meta_spec)
    apply(blast)
   apply(blast)
  apply(blast)
  done

lemma crename_interesting2:
  assumes a: "a\<noteq>c" "a\<noteq>d" "a\<noteq>b" "c\<noteq>d" "b\<noteq>c"
  shows "M[a\<turnstile>c>b][c\<turnstile>c>d] = M[c\<turnstile>c>d][a\<turnstile>c>b]"
  using a
  apply(nominal_induct M avoiding: a c b d rule: trm.strong_induct)
             apply(auto simp add: rename_fresh simp add: trm.inject alpha)
  done

lemma crename_interesting3:
  shows "M[a\<turnstile>c>c][x\<turnstile>n>y] = M[x\<turnstile>n>y][a\<turnstile>c>c]"
  apply(nominal_induct M avoiding: a c x y rule: trm.strong_induct)
             apply(auto simp add: rename_fresh simp add: trm.inject alpha)
  done

lemma crename_credu:
  assumes a: "(M[a\<turnstile>c>b]) \<longrightarrow>\<^sub>c M'"
  shows "\<exists>M0. M0[a\<turnstile>c>b]=M' \<and> M \<longrightarrow>\<^sub>c M0"
  using a
  apply(nominal_induct M\<equiv>"M[a\<turnstile>c>b]" M' avoiding: M a b rule: c_redu.strong_induct)
   apply(drule sym)
   apply(drule crename_Cut)
     apply(simp)
    apply(simp)
   apply(auto)
   apply(rule_tac x="M'{a:=(x).N'}" in exI)
   apply(rule conjI)
    apply(simp add: fresh_atm abs_fresh subst_comm fresh_prod)
   apply(rule c_redu.intros)
     apply(auto dest: not_fic_crename)[1]
    apply(simp add: abs_fresh)
   apply(simp add: abs_fresh)
  apply(drule sym)
  apply(drule crename_Cut)
    apply(simp)
   apply(simp)
  apply(auto)
  apply(rule_tac x="N'{x:=<a>.M'}" in exI)
  apply(rule conjI)
   apply(simp add: fresh_atm abs_fresh subst_comm fresh_prod)
  apply(rule c_redu.intros)
    apply(auto dest: not_fin_crename)[1]
   apply(simp add: abs_fresh)
  apply(simp add: abs_fresh)
  done

lemma crename_lredu:
  assumes a: "(M[a\<turnstile>c>b]) \<longrightarrow>\<^sub>l M'"
  shows "\<exists>M0. M0[a\<turnstile>c>b]=M' \<and> M \<longrightarrow>\<^sub>l M0"
  using a
  apply(nominal_induct M\<equiv>"M[a\<turnstile>c>b]" M' avoiding: M a b rule: l_redu.strong_induct)
         apply(drule sym)
         apply(drule crename_Cut)
           apply(simp add: fresh_prod fresh_atm)
          apply(simp)
         apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
         apply(case_tac "aa=ba")
          apply(simp add: crename_id)
          apply(rule l_redu.intros)
            apply(simp)
           apply(simp add: fresh_atm)
          apply(assumption)
         apply(frule crename_ax2)
         apply(auto)[1]
         apply(case_tac "d=aa")
          apply(simp add: trm.inject)
          apply(rule_tac x="M'[a\<turnstile>c>aa]" in exI)
          apply(rule conjI)
           apply(rule crename_interesting1)
           apply(simp)
          apply(rule l_redu.intros)
            apply(simp)
           apply(simp add: fresh_atm)
          apply(auto dest: fic_crename simp add: fresh_prod fresh_atm)[1]
         apply(simp add: trm.inject)
         apply(rule_tac x="M'[a\<turnstile>c>b]" in exI)
         apply(rule conjI)
          apply(rule crename_interesting2)
              apply(simp)
             apply(simp)
            apply(simp)
           apply(simp)
          apply(simp)
         apply(rule l_redu.intros)
           apply(simp)
          apply(simp add: fresh_atm)
         apply(auto dest: fic_crename simp add: fresh_prod fresh_atm)[1]
        apply(drule sym)
        apply(drule crename_Cut)
          apply(simp add: fresh_prod fresh_atm)
         apply(simp add: fresh_prod fresh_atm)
        apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
        apply(case_tac "aa=b")
         apply(simp add: crename_id)
         apply(rule l_redu.intros)
           apply(simp)
          apply(simp add: fresh_atm)
         apply(assumption)
        apply(frule crename_ax2)
        apply(auto)[1]
        apply(case_tac "d=aa")
         apply(simp add: trm.inject)
        apply(simp add: trm.inject)
        apply(rule_tac x="N'[x\<turnstile>n>y]" in exI)
        apply(rule conjI)
         apply(rule sym)
         apply(rule crename_interesting3)
        apply(rule l_redu.intros)
          apply(simp)
         apply(simp add: fresh_atm)
        apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
    (* LNot *)
       apply(drule sym)
       apply(drule crename_Cut)
         apply(simp add: fresh_prod abs_fresh fresh_atm)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
       apply(drule crename_NotR)
         apply(simp add: fresh_prod abs_fresh fresh_atm)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
       apply(drule crename_NotL)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
       apply(rule_tac x="Cut <b>.N'b (x).N'a" in exI)
       apply(simp add: fresh_atm)[1]
       apply(rule l_redu.intros)
            apply(auto simp add: fresh_prod intro: crename_fresh_interesting2)[1]
           apply(auto simp add: fresh_atm fresh_prod intro: crename_fresh_interesting2)[1]
          apply(auto simp add: fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
         apply(auto simp add: fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
        apply(simp add: fresh_atm)
       apply(simp add: fresh_atm)
    (* LAnd1 *)
      apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
      apply(drule sym)
      apply(drule crename_Cut)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(auto)[1]
      apply(drule crename_AndR)
         apply(simp add: fresh_prod abs_fresh fresh_atm)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
      apply(drule crename_AndL1)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
      apply(rule_tac x="Cut <a1>.M'a (x).N'a" in exI)
      apply(simp add: fresh_atm)[1]
      apply(rule l_redu.intros)
           apply(auto simp add: fresh_atm abs_fresh fresh_prod intro: crename_fresh_interesting1)[1]
          apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: crename_fresh_interesting2)[1]
         apply(auto simp add: fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
        apply(auto simp add: fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
       apply(simp add: fresh_atm)
      apply(simp add: fresh_atm)
    (* LAnd2 *)
     apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
     apply(drule sym)
     apply(drule crename_Cut)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(auto)[1]
     apply(drule crename_AndR)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
     apply(drule crename_AndL2)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
     apply(rule_tac x="Cut <a2>.N'b (x).N'a" in exI)
     apply(simp add: fresh_atm)[1]
     apply(rule l_redu.intros)
          apply(auto simp add: fresh_atm abs_fresh fresh_prod intro: crename_fresh_interesting1)[1]
         apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: crename_fresh_interesting2)[1]
        apply(auto simp add: fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
       apply(auto simp add: fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
      apply(simp add: fresh_atm)
     apply(simp add: fresh_atm)
    (* LOr1 *)
    apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
    apply(drule sym)
    apply(drule crename_Cut)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(auto)[1]
    apply(drule crename_OrL)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
    apply(drule crename_OrR1)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
    apply(auto)
    apply(rule_tac x="Cut <a>.N' (x1).M'a" in exI)
    apply(rule conjI)
     apply(simp add: abs_fresh fresh_atm)[1]
    apply(rule l_redu.intros)
         apply(auto simp add: fresh_atm abs_fresh fresh_prod intro: crename_fresh_interesting1)[1]
        apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: crename_fresh_interesting2)[1]
       apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
      apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
     apply(simp add: fresh_atm)
    apply(simp add: fresh_atm)
    (* LOr2 *)
   apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
   apply(drule sym)
   apply(drule crename_Cut)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(auto)[1]
   apply(drule crename_OrL)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
   apply(drule crename_OrR2)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
   apply(auto)
   apply(rule_tac x="Cut <a>.N' (x2).N'a" in exI)
   apply(rule conjI)
    apply(simp add: abs_fresh fresh_atm)[1]
   apply(rule l_redu.intros)
        apply(auto simp add: fresh_atm abs_fresh fresh_prod intro: crename_fresh_interesting1)[1]
       apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: crename_fresh_interesting2)[1]
      apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
     apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: crename_fresh_interesting1)[1]
    apply(simp add: fresh_atm)
   apply(simp add: fresh_atm)
    (* ImpL *)
  apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
  apply(drule sym)
  apply(drule crename_Cut)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(simp add: fresh_prod abs_fresh fresh_atm abs_supp fin_supp)
  apply(auto)[1]
  apply(drule crename_ImpL)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(simp add: fresh_prod abs_fresh fresh_atm)
  apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
  apply(drule crename_ImpR)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(simp)
  apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
  apply(rule_tac x="Cut <a>.(Cut <c>.M'a (x).N') (y).N'a" in exI)
  apply(rule conjI)
   apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
  apply(rule l_redu.intros)
       apply(auto simp add: fresh_atm abs_fresh abs_supp fin_supp fresh_prod intro: crename_fresh_interesting2)[1]
      apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: crename_fresh_interesting1)[1]
     apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: crename_fresh_interesting2)[1]
    apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: crename_fresh_interesting1)[1]
   apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: crename_fresh_interesting1)[1]
  apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: crename_fresh_interesting1)[1]
  done

lemma crename_aredu:
  assumes a: "(M[a\<turnstile>c>b]) \<longrightarrow>\<^sub>a M'" "a\<noteq>b"
  shows "\<exists>M0. M0[a\<turnstile>c>b]=M' \<and> M \<longrightarrow>\<^sub>a M0"
  using a
  apply(nominal_induct "M[a\<turnstile>c>b]" M' avoiding: M a b rule: a_redu.strong_induct)
                  apply(drule  crename_lredu)
                  apply(blast)
                 apply(drule  crename_credu)
                 apply(blast)
    (* Cut *)
                apply(drule sym)
                apply(drule crename_Cut)
                  apply(simp)
                 apply(simp)
                apply(auto)[1]
                apply(drule_tac x="M'a" in meta_spec)
                apply(drule_tac x="aa" in meta_spec)
                apply(drule_tac x="b" in meta_spec)
                apply(auto)[1]
                apply(rule_tac x="Cut <a>.M0 (x).N'" in exI)
                apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
                apply(rule conjI)
                 apply(rule trans)
                  apply(rule crename.simps)
                   apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
                  apply(drule crename_fresh_interesting2)
                  apply(simp add: fresh_a_redu)
                 apply(simp)
                apply(auto)[1]
               apply(drule sym)
               apply(drule crename_Cut)
                 apply(simp)
                apply(simp)
               apply(auto)[1]
               apply(drule_tac x="N'a" in meta_spec)
               apply(drule_tac x="aa" in meta_spec)
               apply(drule_tac x="b" in meta_spec)
               apply(auto)[1]
               apply(rule_tac x="Cut <a>.M' (x).M0" in exI)
               apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
               apply(rule conjI)
                apply(rule trans)
                 apply(rule crename.simps)
                  apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
                  apply(drule crename_fresh_interesting1)
                   apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
                  apply(simp add: fresh_a_redu)
                 apply(simp)
                apply(simp)
               apply(auto)[1]
    (* NotL *)
              apply(drule sym)
              apply(drule crename_NotL)
               apply(simp)
              apply(auto)[1]
              apply(drule_tac x="N'" in meta_spec)
              apply(drule_tac x="aa" in meta_spec)
              apply(drule_tac x="b" in meta_spec)
              apply(auto)[1]
              apply(rule_tac x="NotL <a>.M0 x" in exI)
              apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
              apply(auto)[1]
    (* NotR *)
             apply(drule sym)
             apply(frule crename_NotR_aux)
             apply(erule disjE)
              apply(auto)[1]
             apply(drule crename_NotR')
               apply(simp)
              apply(simp add: fresh_atm)
             apply(erule disjE)
              apply(auto)[1]
              apply(drule_tac x="N'" in meta_spec)
              apply(drule_tac x="aa" in meta_spec)
              apply(drule_tac x="b" in meta_spec)
              apply(auto)[1]
              apply(rule_tac x="NotR (x).M0 a" in exI)
              apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
              apply(auto)[1]
             apply(auto)[1]
             apply(drule_tac x="N'" in meta_spec)
             apply(drule_tac x="aa" in meta_spec)
             apply(drule_tac x="a" in meta_spec)
             apply(auto)[1]
             apply(rule_tac x="NotR (x).M0 aa" in exI)
             apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
             apply(auto)[1]
    (* AndR *)
            apply(drule sym)
            apply(frule crename_AndR_aux)
            apply(erule disjE)
             apply(auto)[1]
            apply(drule crename_AndR')
               apply(simp add: fresh_prod fresh_atm)
              apply(simp add: fresh_atm)
             apply(simp add: fresh_atm)
            apply(erule disjE)
             apply(auto)[1]
             apply(drule_tac x="M'a" in meta_spec)
             apply(drule_tac x="aa" in meta_spec)
             apply(drule_tac x="ba" in meta_spec)
             apply(auto)[1]
             apply(rule_tac x="AndR <a>.M0 <b>.N' c" in exI)
             apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
             apply(auto)[1]
             apply(rule trans)
              apply(rule crename.simps)
                apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
               apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
               apply(auto intro: fresh_a_redu)[1]
              apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
             apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(auto)[1]
            apply(drule_tac x="M'a" in meta_spec)
            apply(drule_tac x="aa" in meta_spec)
            apply(drule_tac x="c" in meta_spec)
            apply(auto)[1]
            apply(rule_tac x="AndR <a>.M0 <b>.N' aa" in exI)
            apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(auto)[1]
            apply(rule trans)
             apply(rule crename.simps)
               apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
              apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
              apply(auto intro: fresh_a_redu)[1]
             apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
           apply(drule sym)
           apply(frule crename_AndR_aux)
           apply(erule disjE)
            apply(auto)[1]
           apply(drule crename_AndR')
              apply(simp add: fresh_prod fresh_atm)
             apply(simp add: fresh_atm)
            apply(simp add: fresh_atm)
           apply(erule disjE)
            apply(auto)[1]
            apply(drule_tac x="N'a" in meta_spec)
            apply(drule_tac x="aa" in meta_spec)
            apply(drule_tac x="ba" in meta_spec)
            apply(auto)[1]
            apply(rule_tac x="AndR <a>.M' <b>.M0 c" in exI)
            apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(auto)[1]
            apply(rule trans)
             apply(rule crename.simps)
               apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
               apply(auto intro: fresh_a_redu)[1]
              apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
             apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
           apply(auto)[1]
           apply(drule_tac x="N'a" in meta_spec)
           apply(drule_tac x="aa" in meta_spec)
           apply(drule_tac x="c" in meta_spec)
           apply(auto)[1]
           apply(rule_tac x="AndR <a>.M' <b>.M0 aa" in exI)
           apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
           apply(auto)[1]
           apply(rule trans)
            apply(rule crename.simps)
              apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
              apply(auto intro: fresh_a_redu)[1]
             apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
           apply(simp)
    (* AndL1 *)
          apply(drule sym)
          apply(drule crename_AndL1)
           apply(simp)
          apply(auto)[1]
          apply(drule_tac x="N'" in meta_spec)
          apply(drule_tac x="a" in meta_spec)
          apply(drule_tac x="b" in meta_spec)
          apply(auto)[1]
          apply(rule_tac x="AndL1 (x).M0 y" in exI)
          apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
          apply(auto)[1]
    (* AndL2 *)
         apply(drule sym)
         apply(drule crename_AndL2)
          apply(simp)
         apply(auto)[1]
         apply(drule_tac x="N'" in meta_spec)
         apply(drule_tac x="a" in meta_spec)
         apply(drule_tac x="b" in meta_spec)
         apply(auto)[1]
         apply(rule_tac x="AndL2 (x).M0 y" in exI)
         apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
         apply(auto)[1]
    (* OrL *)
        apply(drule sym)
        apply(drule crename_OrL)
          apply(simp)
          apply(auto simp add: fresh_atm fresh_prod)[1]
         apply(auto simp add: fresh_atm fresh_prod)[1]
        apply(auto)[1]
        apply(drule_tac x="M'a" in meta_spec)
        apply(drule_tac x="a" in meta_spec)
        apply(drule_tac x="b" in meta_spec)
        apply(auto)[1]
        apply(rule_tac x="OrL (x).M0 (y).N' z" in exI)
        apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(auto)[1]
        apply(rule trans)
         apply(rule crename.simps)
           apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
          apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
          apply(auto intro: fresh_a_redu)[1]
         apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(simp)
       apply(drule sym)
       apply(drule crename_OrL)
         apply(simp)
         apply(auto simp add: fresh_atm fresh_prod)[1]
        apply(auto simp add: fresh_atm fresh_prod)[1]
       apply(auto)[1]
       apply(drule_tac x="N'a" in meta_spec)
       apply(drule_tac x="a" in meta_spec)
       apply(drule_tac x="b" in meta_spec)
       apply(auto)[1]
       apply(rule_tac x="OrL (x).M' (y).M0 z" in exI)
       apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
       apply(auto)[1]
       apply(rule trans)
        apply(rule crename.simps)
          apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
          apply(auto intro: fresh_a_redu)[1]
         apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(simp)
       apply(simp)
    (* OrR1 *)
      apply(drule sym)
      apply(frule crename_OrR1_aux)
      apply(erule disjE)
       apply(auto)[1]
      apply(drule crename_OrR1')
        apply(simp)
       apply(simp add: fresh_atm)
      apply(erule disjE)
       apply(auto)[1]
       apply(drule_tac x="N'" in meta_spec)
       apply(drule_tac x="aa" in meta_spec)
       apply(drule_tac x="ba" in meta_spec)
       apply(auto)[1]
       apply(rule_tac x="OrR1 <a>.M0 b" in exI)
       apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
       apply(auto)[1]
      apply(auto)[1]
      apply(drule_tac x="N'" in meta_spec)
      apply(drule_tac x="aa" in meta_spec)
      apply(drule_tac x="b" in meta_spec)
      apply(auto)[1]
      apply(rule_tac x="OrR1 <a>.M0 aa" in exI)
      apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
      apply(auto)[1]
    (* OrR2 *)
     apply(drule sym)
     apply(frule crename_OrR2_aux)
     apply(erule disjE)
      apply(auto)[1]
     apply(drule crename_OrR2')
       apply(simp)
      apply(simp add: fresh_atm)
     apply(erule disjE)
      apply(auto)[1]
      apply(drule_tac x="N'" in meta_spec)
      apply(drule_tac x="aa" in meta_spec)
      apply(drule_tac x="ba" in meta_spec)
      apply(auto)[1]
      apply(rule_tac x="OrR2 <a>.M0 b" in exI)
      apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
      apply(auto)[1]
     apply(auto)[1]
     apply(drule_tac x="N'" in meta_spec)
     apply(drule_tac x="aa" in meta_spec)
     apply(drule_tac x="b" in meta_spec)
     apply(auto)[1]
     apply(rule_tac x="OrR2 <a>.M0 aa" in exI)
     apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
     apply(auto)[1]
    (* ImpL *)
    apply(drule sym)
    apply(drule crename_ImpL)
      apply(simp)
     apply(simp)
    apply(auto)[1]
    apply(drule_tac x="M'a" in meta_spec)
    apply(drule_tac x="aa" in meta_spec)
    apply(drule_tac x="b" in meta_spec)
    apply(auto)[1]
    apply(rule_tac x="ImpL <a>.M0 (x).N' y" in exI)
    apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
    apply(auto)[1]
    apply(rule trans)
     apply(rule crename.simps)
      apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
     apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
     apply(auto intro: fresh_a_redu)[1]
    apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
   apply(drule sym)
   apply(drule crename_ImpL)
     apply(simp)
    apply(simp)
   apply(auto)[1]
   apply(drule_tac x="N'a" in meta_spec)
   apply(drule_tac x="aa" in meta_spec)
   apply(drule_tac x="b" in meta_spec)
   apply(auto)[1]
   apply(rule_tac x="ImpL <a>.M' (x).M0 y" in exI)
   apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
   apply(auto)[1]
   apply(rule trans)
    apply(rule crename.simps)
     apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
     apply(auto intro: fresh_a_redu)[1]
    apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
   apply(simp)
    (* ImpR *)
  apply(drule sym)
  apply(frule crename_ImpR_aux)
  apply(erule disjE)
   apply(auto)[1]
  apply(drule crename_ImpR')
     apply(simp)
    apply(simp add: fresh_atm)
   apply(simp add: fresh_atm)
  apply(erule disjE)
   apply(auto)[1]
   apply(drule_tac x="N'" in meta_spec)
   apply(drule_tac x="aa" in meta_spec)
   apply(drule_tac x="ba" in meta_spec)
   apply(auto)[1]
   apply(rule_tac x="ImpR (x).<a>.M0 b" in exI)
   apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
   apply(auto)[1]
  apply(auto)[1]
  apply(drule_tac x="N'" in meta_spec)
  apply(drule_tac x="aa" in meta_spec)
  apply(drule_tac x="b" in meta_spec)
  apply(auto)[1]
  apply(rule_tac x="ImpR (x).<a>.M0 aa" in exI)
  apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
  apply(auto)[1]
  done

lemma SNa_preserved_renaming1:
  assumes a: "SNa M"
  shows "SNa (M[a\<turnstile>c>b])"
  using a
  apply(induct rule: SNa_induct)
  apply(case_tac "a=b")
   apply(simp add: crename_id)
  apply(rule SNaI)
  apply(drule crename_aredu)
   apply(blast)+
  done

lemma nrename_interesting1:
  assumes a: "distinct [x,y,z]"
  shows "M[x\<turnstile>n>z][z\<turnstile>n>y] = M[z\<turnstile>n>y][x\<turnstile>n>y]"
  using a
  apply(nominal_induct M avoiding: x y z rule: trm.strong_induct)
             apply(auto simp add: rename_fresh simp add: trm.inject alpha)
     apply(blast)
    apply(blast)
   apply(rotate_tac 12)
   apply(drule_tac x="x" in meta_spec)
   apply(rotate_tac 15)
   apply(drule_tac x="y" in meta_spec)
   apply(rotate_tac 15)
   apply(drule_tac x="z" in meta_spec)
   apply(blast)
  apply(rotate_tac 11)
  apply(drule_tac x="x" in meta_spec)
  apply(rotate_tac 14)
  apply(drule_tac x="y" in meta_spec)
  apply(rotate_tac 14)
  apply(drule_tac x="z" in meta_spec)
  apply(blast)
  done

lemma nrename_interesting2:
  assumes a: "x\<noteq>z" "x\<noteq>u" "x\<noteq>y" "z\<noteq>u" "y\<noteq>z"
  shows "M[x\<turnstile>n>y][z\<turnstile>n>u] = M[z\<turnstile>n>u][x\<turnstile>n>y]"
  using a
  apply(nominal_induct M avoiding: x y z u rule: trm.strong_induct)
             apply(auto simp add: rename_fresh simp add: trm.inject alpha)
  done

lemma not_fic_nrename_aux:
  assumes a: "fic M c" 
  shows "fic (M[x\<turnstile>n>y]) c" 
  using a
  apply(nominal_induct M avoiding: c x y rule: trm.strong_induct)
             apply(auto dest!: fic_elims intro!: fic.intros simp add: fresh_prod fresh_atm rename_fresh abs_fresh)
  done

lemma not_fic_nrename:
  assumes a: "\<not>(fic (M[x\<turnstile>n>y]) c)" 
  shows "\<not>(fic M c)" 
  using a
  apply(auto dest:  not_fic_nrename_aux)
  done

lemma fin_nrename:
  assumes a: "fin M z" "z\<sharp>(x,y)"
  shows "fin (M[x\<turnstile>n>y]) z" 
  using a
  apply(nominal_induct M avoiding: x y z rule: trm.strong_induct)
             apply(auto dest!: fin_elims intro!: fin.intros simp add: fresh_prod fresh_atm rename_fresh abs_fresh
      split: if_splits)
  done

lemma nrename_fresh_interesting1:
  fixes z::"name"
  assumes a: "z\<sharp>(M[x\<turnstile>n>y])" "z\<sharp>(x,y)"
  shows "z\<sharp>M"
  using a
  apply(nominal_induct M avoiding: x y z rule: trm.strong_induct)
             apply(auto split: if_splits simp add: abs_fresh abs_supp fin_supp)
  done

lemma nrename_fresh_interesting2:
  fixes c::"coname"
  assumes a: "c\<sharp>(M[x\<turnstile>n>y])" 
  shows "c\<sharp>M"
  using a
  apply(nominal_induct M avoiding: x y c rule: trm.strong_induct)
             apply(auto split: if_splits simp add: abs_fresh abs_supp fin_supp fresh_atm)
  done

lemma fin_nrename2:
  assumes a: "fin (M[x\<turnstile>n>y]) z" "z\<sharp>(x,y)"
  shows "fin M z" 
  using a
  apply(nominal_induct M avoiding: x y z rule: trm.strong_induct)
             apply(auto dest!: fin_elims intro!: fin.intros simp add: fresh_prod fresh_atm rename_fresh abs_fresh
      split: if_splits)
        apply(auto dest: nrename_fresh_interesting1 simp add: fresh_atm fresh_prod)
  done

lemma nrename_Cut:
  assumes a: "R[x\<turnstile>n>y] = Cut <c>.M (z).N" "c\<sharp>(N,R)" "z\<sharp>(x,y,M,R)"
  shows "\<exists>M' N'. R = Cut <c>.M' (z).N' \<and> M'[x\<turnstile>n>y] = M \<and> N'[x\<turnstile>n>y] = N \<and> c\<sharp>N' \<and> z\<sharp>M'"
  using a
  apply(nominal_induct R avoiding: c y x z M N rule: trm.strong_induct)
             apply(auto split: if_splits)
  apply(simp add: trm.inject)
  apply(auto simp add: alpha fresh_atm)
  apply(rule_tac x="[(coname,c)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule_tac x="[(name,z)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule conjI)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(auto simp add: fresh_atm)[1]
  apply(drule sym)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_NotR:
  assumes a: "R[x\<turnstile>n>y] = NotR (z).N c" "z\<sharp>(R,x,y)" 
  shows "\<exists>N'. (R = NotR (z).N' c) \<and> N'[x\<turnstile>n>y] = N" 
  using a
  apply(nominal_induct R avoiding: x y c z N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(name,z)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_NotL:
  assumes a: "R[x\<turnstile>n>y] = NotL <c>.N z" "c\<sharp>R" "z\<sharp>(x,y)"
  shows "\<exists>N'. (R = NotL <c>.N' z) \<and> N'[x\<turnstile>n>y] = N" 
  using a
  apply(nominal_induct R avoiding: x y c z N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(coname,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_NotL':
  assumes a: "R[x\<turnstile>n>y] = NotL <c>.N u" "c\<sharp>R" "x\<noteq>y" 
  shows "(\<exists>N'. (R = NotL <c>.N' u) \<and> N'[x\<turnstile>n>y] = N) \<or> (\<exists>N'. (R = NotL <c>.N' x) \<and> y=u \<and> N'[x\<turnstile>n>y] = N)"
  using a
  apply(nominal_induct R avoiding: y u c x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm abs_fresh alpha trm.inject)
   apply(rule_tac x="[(coname,c)]\<bullet>trm" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(coname,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_NotL_aux:
  assumes a: "R[x\<turnstile>n>y] = NotL <c>.N u" 
  shows "(x=u \<and> x=y) \<or> (x\<noteq>u)" 
  using a
  apply(nominal_induct R avoiding: y u c x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma nrename_AndL1:
  assumes a: "R[x\<turnstile>n>y] = AndL1 (z).N u" "z\<sharp>(R,x,y)" "u\<sharp>(x,y)"
  shows "\<exists>N'. (R = AndL1 (z).N' u) \<and> N'[x\<turnstile>n>y] = N" 
  using a
  apply(nominal_induct R avoiding: z u x y N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(name1,z)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_AndL1':
  assumes a: "R[x\<turnstile>n>y] = AndL1 (v).N u" "v\<sharp>(R,u,x,y)" "x\<noteq>y" 
  shows "(\<exists>N'. (R = AndL1 (v).N' u) \<and> N'[x\<turnstile>n>y] = N) \<or> (\<exists>N'. (R = AndL1 (v).N' x) \<and> y=u \<and> N'[x\<turnstile>n>y] = N)"
  using a
  apply(nominal_induct R avoiding: y u v x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm abs_fresh alpha trm.inject)
   apply(rule_tac x="[(name1,v)]\<bullet>trm" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(name1,v)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_AndL1_aux:
  assumes a: "R[x\<turnstile>n>y] = AndL1 (v).N u" 
  shows "(x=u \<and> x=y) \<or> (x\<noteq>u)" 
  using a
  apply(nominal_induct R avoiding: y u v x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma nrename_AndL2:
  assumes a: "R[x\<turnstile>n>y] = AndL2 (z).N u" "z\<sharp>(R,x,y)" "u\<sharp>(x,y)"
  shows "\<exists>N'. (R = AndL2 (z).N' u) \<and> N'[x\<turnstile>n>y] = N" 
  using a
  apply(nominal_induct R avoiding: z u x y N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(name1,z)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_AndL2':
  assumes a: "R[x\<turnstile>n>y] = AndL2 (v).N u" "v\<sharp>(R,u,x,y)" "x\<noteq>y" 
  shows "(\<exists>N'. (R = AndL2 (v).N' u) \<and> N'[x\<turnstile>n>y] = N) \<or> (\<exists>N'. (R = AndL2 (v).N' x) \<and> y=u \<and> N'[x\<turnstile>n>y] = N)"
  using a
  apply(nominal_induct R avoiding: y u v x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm abs_fresh alpha trm.inject)
   apply(rule_tac x="[(name1,v)]\<bullet>trm" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(name1,v)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_AndL2_aux:
  assumes a: "R[x\<turnstile>n>y] = AndL2 (v).N u" 
  shows "(x=u \<and> x=y) \<or> (x\<noteq>u)" 
  using a
  apply(nominal_induct R avoiding: y u v x N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma nrename_AndR:
  assumes a: "R[x\<turnstile>n>y] = AndR <c>.M <d>.N e" "c\<sharp>(d,e,N,R)" "d\<sharp>(c,e,M,R)" 
  shows "\<exists>M' N'. R = AndR <c>.M' <d>.N' e \<and> M'[x\<turnstile>n>y] = M \<and> N'[x\<turnstile>n>y] = N \<and> c\<sharp>N' \<and> d\<sharp>M'"
  using a
  apply(nominal_induct R avoiding: x y c d e M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: trm.inject alpha)
    apply(simp add: fresh_atm fresh_prod)
   apply(rule_tac x="[(coname1,c)]\<bullet>trm1" in exI)
   apply(perm_simp)
   apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(coname1,c)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(coname2,d)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule_tac s="trm2[x\<turnstile>n>y]" in  sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_OrR1:
  assumes a: "R[x\<turnstile>n>y] = OrR1 <c>.N d" "c\<sharp>(R,d)" 
  shows "\<exists>N'. (R = OrR1 <c>.N' d) \<and> N'[x\<turnstile>n>y] = N" 
  using a
  apply(nominal_induct R avoiding: x y c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(coname1,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_OrR2:
  assumes a: "R[x\<turnstile>n>y] = OrR2 <c>.N d" "c\<sharp>(R,d)" 
  shows "\<exists>N'. (R = OrR2 <c>.N' d) \<and> N'[x\<turnstile>n>y] = N" 
  using a
  apply(nominal_induct R avoiding: x y c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  apply(rule_tac x="[(coname1,c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_OrL:
  assumes a: "R[u\<turnstile>n>v] = OrL (x).M (y).N z" "x\<sharp>(y,z,u,v,N,R)" "y\<sharp>(x,z,u,v,M,R)" "z\<sharp>(u,v)"
  shows "\<exists>M' N'. R = OrL (x).M' (y).N' z \<and> M'[u\<turnstile>n>v] = M \<and> N'[u\<turnstile>n>v] = N \<and> x\<sharp>N' \<and> y\<sharp>M'"
  using a
  apply(nominal_induct R avoiding: u v x y z M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: trm.inject alpha fresh_prod fresh_atm)
  apply(rule_tac x="[(name1,x)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(name2,y)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(drule sym)
   apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule_tac s="trm2[u\<turnstile>n>v]" in  sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_OrL':
  assumes a: "R[x\<turnstile>n>y] = OrL (v).M (w).N u" "v\<sharp>(R,N,u,x,y)" "w\<sharp>(R,M,u,x,y)" "x\<noteq>y" 
  shows "(\<exists>M' N'. (R = OrL (v).M' (w).N' u) \<and> M'[x\<turnstile>n>y] = M \<and> N'[x\<turnstile>n>y] = N) \<or> 
         (\<exists>M' N'. (R = OrL (v).M' (w).N' x) \<and> y=u \<and> M'[x\<turnstile>n>y] = M \<and> N'[x\<turnstile>n>y] = N)"
  using a [[simproc del: defined_all]]
  apply(nominal_induct R avoiding: y x u v w M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm abs_fresh alpha trm.inject)
   apply(rule_tac x="[(name1,v)]\<bullet>trm1" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(rule_tac x="[(name2,w)]\<bullet>trm2" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(rule conjI)
    apply(drule sym)
    apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
    apply(simp add: eqvts calc_atm)
   apply(drule_tac s="trm2[x\<turnstile>n>u]" in sym)
   apply(drule_tac pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(name1,v)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule_tac x="[(name2,w)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule conjI)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule_tac s="trm2[x\<turnstile>n>y]" in sym)
  apply(drule_tac pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_OrL_aux:
  assumes a: "R[x\<turnstile>n>y] = OrL (v).M (w).N u" 
  shows "(x=u \<and> x=y) \<or> (x\<noteq>u)" 
  using a
  apply(nominal_induct R avoiding: y x w u v M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma nrename_ImpL:
  assumes a: "R[x\<turnstile>n>y] = ImpL <c>.M (u).N z" "c\<sharp>(N,R)" "u\<sharp>(y,x,z,M,R)" "z\<sharp>(x,y)"
  shows "\<exists>M' N'. R = ImpL <c>.M' (u).N' z \<and> M'[x\<turnstile>n>y] = M \<and> N'[x\<turnstile>n>y] = N \<and> c\<sharp>N' \<and> u\<sharp>M'"
  using a
  apply(nominal_induct R avoiding: u x c y z M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: trm.inject alpha fresh_prod fresh_atm)
  apply(rule_tac x="[(coname,c)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(rule_tac x="[(name1,u)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(auto simp add: abs_fresh fresh_left calc_atm fresh_prod fresh_atm)[1]
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule_tac s="trm2[x\<turnstile>n>y]" in  sym)
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm fresh_prod fresh_atm)
  done

lemma nrename_ImpL':
  assumes a: "R[x\<turnstile>n>y] = ImpL <c>.M (w).N u" "c\<sharp>(R,N)" "w\<sharp>(R,M,u,x,y)" "x\<noteq>y" 
  shows "(\<exists>M' N'. (R = ImpL <c>.M' (w).N' u) \<and> M'[x\<turnstile>n>y] = M \<and> N'[x\<turnstile>n>y] = N) \<or> 
         (\<exists>M' N'. (R = ImpL <c>.M' (w).N' x) \<and> y=u \<and> M'[x\<turnstile>n>y] = M \<and> N'[x\<turnstile>n>y] = N)"
  using a [[simproc del: defined_all]]
  apply(nominal_induct R avoiding: y x u c w M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm abs_fresh alpha trm.inject)
   apply(rule_tac x="[(coname,c)]\<bullet>trm1" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(rule_tac x="[(name1,w)]\<bullet>trm2" in exI)
   apply(perm_simp)
   apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
   apply(rule conjI)
    apply(drule sym)
    apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
    apply(simp add: eqvts calc_atm)
   apply(drule_tac s="trm2[x\<turnstile>n>u]" in sym)
   apply(drule_tac pt_bij1[OF pt_name_inst,OF at_name_inst])
   apply(simp add: eqvts calc_atm)
  apply(rule_tac x="[(coname,c)]\<bullet>trm1" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule_tac x="[(name1,w)]\<bullet>trm2" in exI)
  apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule conjI)
   apply(drule sym)
   apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
   apply(simp add: eqvts calc_atm)
  apply(drule_tac s="trm2[x\<turnstile>n>y]" in sym)
  apply(drule_tac pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_ImpL_aux:
  assumes a: "R[x\<turnstile>n>y] = ImpL <c>.M (w).N u" 
  shows "(x=u \<and> x=y) \<or> (x\<noteq>u)" 
  using a
  apply(nominal_induct R avoiding: y x w u c M N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm alpha abs_fresh trm.inject)
  done

lemma nrename_ImpR:
  assumes a: "R[u\<turnstile>n>v] = ImpR (x).<c>.N d" "c\<sharp>(R,d)" "x\<sharp>(R,u,v)" 
  shows "\<exists>N'. (R = ImpR (x).<c>.N' d) \<and> N'[u\<turnstile>n>v] = N" 
  using a
  apply(nominal_induct R avoiding: u v x c d N rule: trm.strong_induct)
             apply(auto split: if_splits simp add: fresh_prod fresh_atm abs_perm alpha abs_fresh trm.inject)
   apply(rule_tac x="[(name,x)]\<bullet>trm" in exI)
   apply(perm_simp)
  apply(simp add: abs_fresh fresh_left calc_atm fresh_prod)
  apply(rule_tac x="[(name,x)]\<bullet>[(coname1, c)]\<bullet>trm" in exI)
  apply(perm_simp)
  apply(simp add: abs_supp fin_supp abs_fresh fresh_left calc_atm fresh_prod)
  apply(drule sym)
  apply(drule pt_bij1[OF pt_coname_inst,OF at_coname_inst])
  apply(drule pt_bij1[OF pt_name_inst,OF at_name_inst])
  apply(simp add: eqvts calc_atm)
  done

lemma nrename_credu:
  assumes a: "(M[x\<turnstile>n>y]) \<longrightarrow>\<^sub>c M'"
  shows "\<exists>M0. M0[x\<turnstile>n>y]=M' \<and> M \<longrightarrow>\<^sub>c M0"
  using a
  apply(nominal_induct M\<equiv>"M[x\<turnstile>n>y]" M' avoiding: M x y rule: c_redu.strong_induct)
   apply(drule sym)
   apply(drule nrename_Cut)
     apply(simp)
    apply(simp)
   apply(auto)
   apply(rule_tac x="M'{a:=(x).N'}" in exI)
   apply(rule conjI)
    apply(simp add: fresh_atm abs_fresh subst_comm fresh_prod)
   apply(rule c_redu.intros)
     apply(auto dest: not_fic_nrename)[1]
    apply(simp add: abs_fresh)
   apply(simp add: abs_fresh)
  apply(drule sym)
  apply(drule nrename_Cut)
    apply(simp)
   apply(simp)
  apply(auto)
  apply(rule_tac x="N'{x:=<a>.M'}" in exI)
  apply(rule conjI)
   apply(simp add: fresh_atm abs_fresh subst_comm fresh_prod)
  apply(rule c_redu.intros)
    apply(auto)
  apply(drule_tac x="xa" and y="y" in fin_nrename)
   apply(auto simp add: fresh_prod abs_fresh)
  done

lemma nrename_ax2:
  assumes a: "N[x\<turnstile>n>y] = Ax z c"
  shows "\<exists>z. N = Ax z c"
  using a
  apply(nominal_induct N avoiding: x y rule: trm.strong_induct)
             apply(auto split: if_splits)
  apply(simp add: trm.inject)
  done

lemma fic_nrename:
  assumes a: "fic (M[x\<turnstile>n>y]) c" 
  shows "fic M c" 
  using a
  apply(nominal_induct M avoiding: c x y rule: trm.strong_induct)
             apply(auto dest!: fic_elims intro!: fic.intros simp add: fresh_prod fresh_atm rename_fresh abs_fresh
      split: if_splits)
       apply(auto dest: nrename_fresh_interesting2 simp add: fresh_prod fresh_atm)
  done

lemma nrename_lredu:
  assumes a: "(M[x\<turnstile>n>y]) \<longrightarrow>\<^sub>l M'"
  shows "\<exists>M0. M0[x\<turnstile>n>y]=M' \<and> M \<longrightarrow>\<^sub>l M0"
  using a
  apply(nominal_induct M\<equiv>"M[x\<turnstile>n>y]" M' avoiding: M x y rule: l_redu.strong_induct)
         apply(drule sym)
         apply(drule nrename_Cut)
           apply(simp add: fresh_prod fresh_atm)
          apply(simp)
         apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
         apply(case_tac "xa=y")
          apply(simp add: nrename_id)
          apply(rule l_redu.intros)
            apply(simp)
           apply(simp add: fresh_atm)
          apply(assumption)
         apply(frule nrename_ax2)
         apply(auto)[1]
         apply(case_tac "z=xa")
          apply(simp add: trm.inject)
         apply(simp)
         apply(rule_tac x="M'[a\<turnstile>c>b]" in exI)
         apply(rule conjI)
          apply(rule crename_interesting3)
         apply(rule l_redu.intros)
           apply(simp)
          apply(simp add: fresh_atm)
         apply(auto dest: fic_nrename simp add: fresh_prod fresh_atm)[1]
        apply(drule sym)
        apply(drule nrename_Cut)
          apply(simp add: fresh_prod fresh_atm)
         apply(simp add: fresh_prod fresh_atm)
        apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
        apply(case_tac "xa=ya")
         apply(simp add: nrename_id)
         apply(rule l_redu.intros)
           apply(simp)
          apply(simp add: fresh_atm)
         apply(assumption)
        apply(frule nrename_ax2)
        apply(auto)[1]
        apply(case_tac "z=xa")
         apply(simp add: trm.inject)
         apply(rule_tac x="N'[x\<turnstile>n>xa]" in exI)
         apply(rule conjI)
          apply(rule nrename_interesting1)
          apply(auto)[1]
         apply(rule l_redu.intros)
           apply(simp)
          apply(simp add: fresh_atm)
         apply(auto dest: fin_nrename2 simp add: fresh_prod fresh_atm)[1]
        apply(simp add: trm.inject)
        apply(rule_tac x="N'[x\<turnstile>n>y]" in exI)
        apply(rule conjI)
         apply(rule nrename_interesting2)
             apply(simp_all)
        apply(rule l_redu.intros)
          apply(simp)
         apply(simp add: fresh_atm)
        apply(auto dest: fin_nrename2 simp add: fresh_prod fresh_atm)[1]
    (* LNot *)
       apply(drule sym)
       apply(drule nrename_Cut)
         apply(simp add: fresh_prod abs_fresh fresh_atm)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
       apply(drule nrename_NotR)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
       apply(drule nrename_NotL)
         apply(simp add: fresh_prod abs_fresh fresh_atm)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
       apply(rule_tac x="Cut <b>.N'b (x).N'a" in exI)
       apply(simp add: fresh_atm)[1]
       apply(rule l_redu.intros)
            apply(auto simp add: fresh_prod fresh_atm intro: nrename_fresh_interesting1)[1]
           apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
          apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting2)[1]
         apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting2)[1]
        apply(simp add: fresh_atm)
       apply(simp add: fresh_atm)
    (* LAnd1 *)
      apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
      apply(drule sym)
      apply(drule nrename_Cut)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(auto)[1]
      apply(drule nrename_AndR)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
      apply(drule nrename_AndL1)
        apply(simp add: fresh_prod abs_fresh fresh_atm)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
      apply(rule_tac x="Cut <a1>.M'a (x).N'b" in exI)
      apply(simp add: fresh_atm)[1]
      apply(rule l_redu.intros)
           apply(auto simp add: fresh_atm abs_fresh fresh_prod intro: nrename_fresh_interesting2)[1]
          apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
         apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
        apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
       apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
      apply(simp add: fresh_atm)
    (* LAnd2 *)
     apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
     apply(drule sym)
     apply(drule nrename_Cut)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(auto)[1]
     apply(drule nrename_AndR)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
     apply(drule nrename_AndL2)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
     apply(rule_tac x="Cut <a2>.N'a (x).N'b" in exI)
     apply(simp add: fresh_atm)[1]
     apply(rule l_redu.intros)
          apply(auto simp add: fresh_atm abs_fresh fresh_prod intro: nrename_fresh_interesting2)[1]
         apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
        apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
       apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
      apply(auto simp add: fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
     apply(simp add: fresh_atm)
    (* LOr1 *)
    apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
    apply(drule sym)
    apply(drule nrename_Cut)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(auto)[1]
    apply(drule nrename_OrL)
       apply(simp add: fresh_prod abs_fresh fresh_atm)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(simp add: fresh_prod fresh_atm)
    apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
    apply(drule nrename_OrR1)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
    apply(rule_tac x="Cut <a>.N' (x1).M'a" in exI)
    apply(rule conjI)
     apply(simp add: abs_fresh fresh_atm)[1]
    apply(rule l_redu.intros)
         apply(auto simp add: fresh_atm abs_fresh fresh_prod intro: nrename_fresh_interesting2)[1]
        apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
       apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
      apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
     apply(simp add: fresh_atm)
    apply(simp add: fresh_atm)
    (* LOr2 *)
   apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
   apply(drule sym)
   apply(drule nrename_Cut)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(auto)[1]
   apply(drule nrename_OrL)
      apply(simp add: fresh_prod abs_fresh fresh_atm)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(simp add: fresh_prod fresh_atm)
   apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
   apply(drule nrename_OrR2)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
   apply(rule_tac x="Cut <a>.N' (x2).N'a" in exI)
   apply(rule conjI)
    apply(simp add: abs_fresh fresh_atm)[1]
   apply(rule l_redu.intros)
        apply(auto simp add: fresh_atm abs_fresh fresh_prod intro: nrename_fresh_interesting2)[1]
       apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
      apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
     apply(auto simp add: abs_fresh fresh_atm fresh_prod intro: nrename_fresh_interesting1)[1]
    apply(simp add: fresh_atm)
   apply(simp add: fresh_atm)
    (* ImpL *)
  apply(auto dest: fin_crename simp add: fresh_prod fresh_atm)[1]
  apply(drule sym) 
  apply(drule nrename_Cut)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(simp add: fresh_prod abs_fresh fresh_atm abs_supp fin_supp)
  apply(auto)[1]
  apply(drule nrename_ImpL)
     apply(simp add: fresh_prod abs_fresh fresh_atm)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(simp add: fresh_prod fresh_atm)
  apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
  apply(drule nrename_ImpR)
    apply(simp add: fresh_prod abs_fresh fresh_atm)
   apply(simp add: fresh_prod abs_fresh fresh_atm)
  apply(auto simp add: abs_fresh fresh_prod fresh_atm)[1]
  apply(rule_tac x="Cut <a>.(Cut <c>.M'a (x).N') (y).N'a" in exI)
  apply(rule conjI)
   apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
  apply(rule l_redu.intros)
       apply(auto simp add: fresh_atm abs_fresh abs_supp fin_supp fresh_prod intro: nrename_fresh_interesting1)[1]
      apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: nrename_fresh_interesting2)[1]
     apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: nrename_fresh_interesting1)[1]
    apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: nrename_fresh_interesting2)[1]
   apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: nrename_fresh_interesting2)[1]
  apply(auto simp add: abs_fresh fresh_atm abs_supp fin_supp fresh_prod intro: nrename_fresh_interesting2)[1]
  done

lemma nrename_aredu:
  assumes a: "(M[x\<turnstile>n>y]) \<longrightarrow>\<^sub>a M'" "x\<noteq>y"
  shows "\<exists>M0. M0[x\<turnstile>n>y]=M' \<and> M \<longrightarrow>\<^sub>a M0"
  using a
  apply(nominal_induct "M[x\<turnstile>n>y]" M' avoiding: M x y rule: a_redu.strong_induct)
                  apply(drule  nrename_lredu)
                  apply(blast)
                 apply(drule  nrename_credu)
                 apply(blast)
    (* Cut *)
                apply(drule sym)
                apply(drule nrename_Cut)
                  apply(simp)
                 apply(simp)
                apply(auto)[1]
                apply(drule_tac x="M'a" in meta_spec)
                apply(drule_tac x="xa" in meta_spec)
                apply(drule_tac x="y" in meta_spec)
                apply(auto)[1]
                apply(rule_tac x="Cut <a>.M0 (x).N'" in exI)
                apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
                apply(rule conjI)
                 apply(rule trans)
                  apply(rule nrename.simps)
                   apply(drule nrename_fresh_interesting2)
                   apply(simp add: fresh_a_redu)
                  apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
                  apply(drule nrename_fresh_interesting1)
                   apply(simp add: fresh_prod fresh_atm)
                  apply(simp add: fresh_a_redu)
                 apply(simp)
                apply(auto)[1]
               apply(drule sym)
               apply(drule nrename_Cut)
                 apply(simp)
                apply(simp)
               apply(auto)[1]
               apply(drule_tac x="N'a" in meta_spec)
               apply(drule_tac x="xa" in meta_spec)
               apply(drule_tac x="y" in meta_spec)
               apply(auto)[1]
               apply(rule_tac x="Cut <a>.M' (x).M0" in exI)
               apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
               apply(rule conjI)
                apply(rule trans)
                 apply(rule nrename.simps)
                  apply(simp add: fresh_a_redu)
                 apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
                apply(simp)
               apply(auto)[1]
    (* NotL *)
              apply(drule sym)
              apply(frule nrename_NotL_aux)
              apply(erule disjE)
               apply(auto)[1]
              apply(drule nrename_NotL')
                apply(simp)
               apply(simp add: fresh_atm)
              apply(erule disjE)
               apply(auto)[1]
               apply(drule_tac x="N'" in meta_spec)
               apply(drule_tac x="xa" in meta_spec)
               apply(drule_tac x="y" in meta_spec)
               apply(auto)[1]
               apply(rule_tac x="NotL <a>.M0 x" in exI)
               apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
               apply(auto)[1]
              apply(auto)[1]
              apply(drule_tac x="N'" in meta_spec)
              apply(drule_tac x="xa" in meta_spec)
              apply(drule_tac x="x" in meta_spec)
              apply(auto)[1]
              apply(rule_tac x="NotL <a>.M0 xa" in exI)
              apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
              apply(auto)[1]
    (* NotR *)
             apply(drule sym)
             apply(drule nrename_NotR)
              apply(simp)
             apply(auto)[1]
             apply(drule_tac x="N'" in meta_spec)
             apply(drule_tac x="xa" in meta_spec)
             apply(drule_tac x="y" in meta_spec)
             apply(auto)[1]
             apply(rule_tac x="NotR (x).M0 a" in exI)
             apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
             apply(auto)[1]
    (* AndR *)
            apply(drule sym)
            apply(drule nrename_AndR)
              apply(simp)
              apply(auto simp add: fresh_atm fresh_prod)[1]
             apply(auto simp add: fresh_atm fresh_prod)[1]
            apply(auto)[1]
            apply(drule_tac x="M'a" in meta_spec)
            apply(drule_tac x="x" in meta_spec)
            apply(drule_tac x="y" in meta_spec)
            apply(auto)[1]
            apply(rule_tac x="AndR <a>.M0 <b>.N' c" in exI)
            apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(auto)[1]
            apply(rule trans)
             apply(rule nrename.simps)
               apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
              apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
              apply(auto intro: fresh_a_redu)[1]
             apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(simp)
           apply(drule sym)
           apply(drule nrename_AndR)
             apply(simp)
             apply(auto simp add: fresh_atm fresh_prod)[1]
            apply(auto simp add: fresh_atm fresh_prod)[1]
           apply(auto)[1]
           apply(drule_tac x="N'a" in meta_spec)
           apply(drule_tac x="x" in meta_spec)
           apply(drule_tac x="y" in meta_spec)
           apply(auto)[1]
           apply(rule_tac x="AndR <a>.M' <b>.M0 c" in exI)
           apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
           apply(auto)[1]
           apply(rule trans)
            apply(rule nrename.simps)
              apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
              apply(auto intro: fresh_a_redu)[1]
             apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
            apply(simp)
           apply(simp)
    (* AndL1 *)
          apply(drule sym)
          apply(frule nrename_AndL1_aux)
          apply(erule disjE)
           apply(auto)[1]
          apply(drule nrename_AndL1')
            apply(simp)
           apply(simp add: fresh_atm)
          apply(erule disjE)
           apply(auto)[1]
           apply(drule_tac x="N'" in meta_spec)
           apply(drule_tac x="xa" in meta_spec)
           apply(drule_tac x="ya" in meta_spec)
           apply(auto)[1]
           apply(rule_tac x="AndL1 (x).M0 y" in exI)
           apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
           apply(auto)[1]
          apply(auto)[1]
          apply(drule_tac x="N'" in meta_spec)
          apply(drule_tac x="xa" in meta_spec)
          apply(drule_tac x="y" in meta_spec)
          apply(auto)[1]
          apply(rule_tac x="AndL1 (x).M0 xa" in exI)
          apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
          apply(auto)[1]
    (* AndL2 *)
         apply(drule sym)
         apply(frule nrename_AndL2_aux)
         apply(erule disjE)
          apply(auto)[1]
         apply(drule nrename_AndL2')
           apply(simp)
          apply(simp add: fresh_atm)
         apply(erule disjE)
          apply(auto)[1]
          apply(drule_tac x="N'" in meta_spec)
          apply(drule_tac x="xa" in meta_spec)
          apply(drule_tac x="ya" in meta_spec)
          apply(auto)[1]
          apply(rule_tac x="AndL2 (x).M0 y" in exI)
          apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
          apply(auto)[1]
         apply(auto)[1]
         apply(drule_tac x="N'" in meta_spec)
         apply(drule_tac x="xa" in meta_spec)
         apply(drule_tac x="y" in meta_spec)
         apply(auto)[1]
         apply(rule_tac x="AndL2 (x).M0 xa" in exI)
         apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
         apply(auto)[1]
    (* OrL *)
        apply(drule sym)
        apply(frule nrename_OrL_aux)
        apply(erule disjE)
         apply(auto)[1]
        apply(drule nrename_OrL')
           apply(simp add: fresh_prod fresh_atm)
          apply(simp add: fresh_atm)
         apply(simp add: fresh_atm)
        apply(erule disjE)
         apply(auto)[1]
         apply(drule_tac x="M'a" in meta_spec)
         apply(drule_tac x="xa" in meta_spec)
         apply(drule_tac x="ya" in meta_spec)
         apply(auto)[1]
         apply(rule_tac x="OrL (x).M0 (y).N' z" in exI)
         apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
         apply(auto)[1]
         apply(rule trans)
          apply(rule nrename.simps)
            apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
           apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
           apply(auto intro: fresh_a_redu)[1]
          apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
         apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(auto)[1]
        apply(drule_tac x="M'a" in meta_spec)
        apply(drule_tac x="xa" in meta_spec)
        apply(drule_tac x="z" in meta_spec)
        apply(auto)[1]
        apply(rule_tac x="OrL (x).M0 (y).N' xa" in exI)
        apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(auto)[1]
        apply(rule trans)
         apply(rule nrename.simps)
           apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
          apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
          apply(auto intro: fresh_a_redu)[1]
         apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
       apply(drule sym)
       apply(frule nrename_OrL_aux)
       apply(erule disjE)
        apply(auto)[1]
       apply(drule nrename_OrL')
          apply(simp add: fresh_prod fresh_atm)
         apply(simp add: fresh_atm)
        apply(simp add: fresh_atm)
       apply(erule disjE)
        apply(auto)[1]
        apply(drule_tac x="N'a" in meta_spec)
        apply(drule_tac x="xa" in meta_spec)
        apply(drule_tac x="ya" in meta_spec)
        apply(auto)[1]
        apply(rule_tac x="OrL (x).M' (y).M0 z" in exI)
        apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(auto)[1]
        apply(rule trans)
         apply(rule nrename.simps)
           apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
           apply(auto intro: fresh_a_redu)[1]
          apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
         apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
       apply(auto)[1]
       apply(drule_tac x="N'a" in meta_spec)
       apply(drule_tac x="xa" in meta_spec)
       apply(drule_tac x="z" in meta_spec)
       apply(auto)[1]
       apply(rule_tac x="OrL (x).M' (y).M0 xa" in exI)
       apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
       apply(auto)[1]
       apply(rule trans)
        apply(rule nrename.simps)
          apply(simp add: abs_fresh abs_supp fin_supp fresh_atm fresh_prod)[1]
          apply(auto intro: fresh_a_redu)[1]
         apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
        apply(simp)
       apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
    (* OrR1 *)
      apply(drule sym)
      apply(drule nrename_OrR1)
       apply(simp)
      apply(auto)[1]
      apply(drule_tac x="N'" in meta_spec)
      apply(drule_tac x="x" in meta_spec)
      apply(drule_tac x="y" in meta_spec)
      apply(auto)[1]
      apply(rule_tac x="OrR1 <a>.M0 b" in exI)
      apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
      apply(auto)[1]
    (* OrR2 *)
     apply(drule sym)
     apply(drule nrename_OrR2)
      apply(simp)
     apply(auto)[1]
     apply(drule_tac x="N'" in meta_spec)
     apply(drule_tac x="x" in meta_spec)
     apply(drule_tac x="y" in meta_spec)
     apply(auto)[1]
     apply(rule_tac x="OrR2 <a>.M0 b" in exI)
     apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
     apply(auto)[1]
    (* ImpL *)
    apply(drule sym)
    apply(frule nrename_ImpL_aux)
    apply(erule disjE)
     apply(auto)[1]
    apply(drule nrename_ImpL')
       apply(simp add: fresh_prod fresh_atm)
      apply(simp add: fresh_atm)
     apply(simp add: fresh_atm)
    apply(erule disjE)
     apply(auto)[1]
     apply(drule_tac x="M'a" in meta_spec)
     apply(drule_tac x="xa" in meta_spec)
     apply(drule_tac x="ya" in meta_spec)
     apply(auto)[1]
     apply(rule_tac x="ImpL <a>.M0 (x).N' y" in exI)
     apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
     apply(auto)[1]
     apply(rule trans)
      apply(rule nrename.simps)
       apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
      apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
      apply(auto intro: fresh_a_redu)[1]
     apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
    apply(auto)[1]
    apply(drule_tac x="M'a" in meta_spec)
    apply(drule_tac x="xa" in meta_spec)
    apply(drule_tac x="y" in meta_spec)
    apply(auto)[1]
    apply(rule_tac x="ImpL <a>.M0 (x).N' xa" in exI)
    apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
    apply(auto)[1]
    apply(rule trans)
     apply(rule nrename.simps)
      apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
     apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
     apply(auto intro: fresh_a_redu)[1]
    apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
   apply(drule sym)
   apply(frule nrename_ImpL_aux)
   apply(erule disjE)
    apply(auto)[1]
   apply(drule nrename_ImpL')
      apply(simp add: fresh_prod fresh_atm)
     apply(simp add: fresh_atm)
    apply(simp add: fresh_atm)
   apply(erule disjE)
    apply(auto)[1]
    apply(drule_tac x="N'a" in meta_spec)
    apply(drule_tac x="xa" in meta_spec)
    apply(drule_tac x="ya" in meta_spec)
    apply(auto)[1]
    apply(rule_tac x="ImpL <a>.M' (x).M0 y" in exI)
    apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
    apply(auto)[1]
    apply(rule trans)
     apply(rule nrename.simps)
      apply(auto intro: fresh_a_redu)[1]
     apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
    apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
   apply(auto)[1]
   apply(drule_tac x="N'a" in meta_spec)
   apply(drule_tac x="xa" in meta_spec)
   apply(drule_tac x="y" in meta_spec)
   apply(auto)[1]
   apply(rule_tac x="ImpL <a>.M' (x).M0 xa" in exI)
   apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
   apply(auto)[1]
   apply(rule trans)
    apply(rule nrename.simps)
     apply(auto intro: fresh_a_redu)[1]
    apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
   apply(simp add: fresh_prod abs_fresh abs_supp fin_supp fresh_atm)[1]
    (* ImpR *)
  apply(drule sym)
  apply(drule nrename_ImpR)
    apply(simp)
   apply(simp)
  apply(auto)[1]
  apply(drule_tac x="N'" in meta_spec)
  apply(drule_tac x="xa" in meta_spec)
  apply(drule_tac x="y" in meta_spec)
  apply(auto)[1]
  apply(rule_tac x="ImpR (x).<a>.M0 b" in exI)
  apply(simp add: abs_fresh abs_supp fin_supp fresh_atm)[1]
  apply(auto)[1]
  done

lemma SNa_preserved_renaming2:
  assumes a: "SNa N"
  shows "SNa (N[x\<turnstile>n>y])"
  using a
  apply(induct rule: SNa_induct)
  apply(case_tac "x=y")
   apply(simp add: nrename_id)
  apply(rule SNaI)
  apply(drule nrename_aredu)
   apply(blast)+
  done

text \<open>helper-stuff to set up the induction\<close>

abbreviation
  SNa_set :: "trm set"
  where
    "SNa_set \<equiv> {M. SNa M}"

abbreviation
  A_Redu_set :: "(trm\<times>trm) set"
  where
    "A_Redu_set \<equiv> {(N,M)| M N. M \<longrightarrow>\<^sub>a N}"

lemma SNa_elim:
  assumes a: "SNa M"
  shows "(\<forall>M. (\<forall>N. M \<longrightarrow>\<^sub>a N \<longrightarrow> P N)\<longrightarrow> P M) \<longrightarrow> P M"
  using a
  by (induct rule: SNa.induct) (blast)

lemma wf_SNa_restricted:
  shows "wf (A_Redu_set \<inter> (UNIV \<times> SNa_set))"
  apply(unfold wf_def)
  apply(intro strip)
  apply(case_tac "SNa x")
   apply(simp (no_asm_use))
   apply(drule_tac P="P" in SNa_elim)
   apply(erule mp)
   apply(blast)
    (* other case *)
  apply(drule_tac x="x" in spec)
  apply(erule mp)
  apply(fast)
  done

definition SNa_Redu :: "(trm \<times> trm) set" where
  "SNa_Redu \<equiv> A_Redu_set \<inter> (UNIV \<times> SNa_set)"

lemma wf_SNa_Redu:
  shows "wf SNa_Redu"
  apply(unfold SNa_Redu_def)
  apply(rule wf_SNa_restricted)
  done

lemma wf_measure_triple:
  shows "wf ((measure size) <*lex*> SNa_Redu <*lex*> SNa_Redu)"
  by (auto intro: wf_SNa_Redu)

lemma my_wf_induct_triple: 
  assumes a: " wf(r1 <*lex*> r2 <*lex*> r3)"           
    and     b: "\<And>x. \<lbrakk>\<And>y. ((fst y,fst (snd y),snd (snd y)),(fst x,fst (snd x), snd (snd x))) 
                                    \<in> (r1 <*lex*> r2 <*lex*> r3) \<longrightarrow> P y\<rbrakk> \<Longrightarrow> P x"  
  shows "P x"
  using a
  apply(induct x rule: wf_induct_rule)
  apply(rule b)
  apply(simp)
  done

lemma my_wf_induct_triple': 
  assumes a: " wf(r1 <*lex*> r2 <*lex*> r3)"           
    and    b: "\<And>x1 x2 x3. \<lbrakk>\<And>y1 y2 y3. ((y1,y2,y3),(x1,x2,x3)) \<in> (r1 <*lex*> r2 <*lex*> r3) \<longrightarrow> P (y1,y2,y3)\<rbrakk> 
             \<Longrightarrow> P (x1,x2,x3)"  
  shows "P (x1,x2,x3)"
  apply(rule_tac my_wf_induct_triple[OF a])
  apply(case_tac x rule: prod.exhaust)
  apply(simp)
  apply(rename_tac p a b)
  apply(case_tac b)
  apply(simp)
  apply(rule b)
  apply(blast)
  done

lemma my_wf_induct_triple'': 
  assumes a: " wf(r1 <*lex*> r2 <*lex*> r3)"           
    and     b: "\<And>x1 x2 x3. \<lbrakk>\<And>y1 y2 y3. ((y1,y2,y3),(x1,x2,x3)) \<in> (r1 <*lex*> r2 <*lex*> r3) \<longrightarrow> P y1 y2 y3\<rbrakk>
               \<Longrightarrow> P x1 x2 x3"  
  shows "P x1 x2 x3"
  apply(rule_tac my_wf_induct_triple'[where P="\<lambda>(x1,x2,x3). P x1 x2 x3", simplified])
   apply(rule a)
  apply(rule b)
  apply(auto)
  done

lemma excluded_m:
  assumes a: "<a>:M \<in> (\<parallel><B>\<parallel>)" "(x):N \<in> (\<parallel>(B)\<parallel>)"
  shows "(<a>:M \<in> BINDINGc B (\<parallel>(B)\<parallel>) \<or> (x):N \<in> BINDINGn B (\<parallel><B>\<parallel>))
      \<or>\<not>(<a>:M \<in> BINDINGc B (\<parallel>(B)\<parallel>) \<or> (x):N \<in> BINDINGn B (\<parallel><B>\<parallel>))"
  by (blast)

text \<open>The following two simplification rules are necessary because of the 
      new definition of lexicographic ordering\<close>
lemma ne_and_SNa_Redu[simp]: "M \<noteq> x \<and> (M,x) \<in> SNa_Redu \<longleftrightarrow> (M,x) \<in> SNa_Redu"
  using wf_SNa_Redu by auto

lemma ne_and_less_size [simp]: "A \<noteq> B \<and> size A < size B \<longleftrightarrow> size A < size B"
  by auto

lemma tricky_subst:
  assumes a1: "b\<sharp>(c,N)"
    and     a2: "z\<sharp>(x,P)"
    and     a3: "M\<noteq>Ax z b"
  shows "(Cut <c>.N (z).M){b:=(x).P} = Cut <c>.N (z).(M{b:=(x).P})"
  using a1 a2 a3
  apply -
  apply(generate_fresh "coname")
  apply(subgoal_tac "Cut <c>.N (z).M = Cut <ca>.([(ca,c)]\<bullet>N) (z).M")
   apply(simp)
   apply(rule trans)
    apply(rule better_Cut_substc)
     apply(simp)
    apply(simp add: abs_fresh)
   apply(simp)
   apply(subgoal_tac "b\<sharp>([(ca,c)]\<bullet>N)")
    apply(simp add: forget)
    apply(simp add: trm.inject)
   apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
  apply(simp add: trm.inject)
  apply(rule sym)
  apply(simp add: alpha fresh_prod fresh_atm)
  done

text \<open>3rd lemma\<close>

lemma CUT_SNa_aux:
  assumes a1: "<a>:M \<in> (\<parallel><B>\<parallel>)"
    and     a2: "SNa M"
    and     a3: "(x):N \<in> (\<parallel>(B)\<parallel>)"
    and     a4: "SNa N"
  shows   "SNa (Cut <a>.M (x).N)"
  using a1 a2 a3 a4 [[simproc del: defined_all]]
  apply(induct B M N arbitrary: a x rule: my_wf_induct_triple''[OF wf_measure_triple])
  apply(rule SNaI)
  apply(drule Cut_a_redu_elim)
  apply(erule disjE)
    (* left-inner reduction *)
   apply(erule exE)
   apply(erule conjE)+
   apply(simp)
   apply(drule_tac x="x1" in meta_spec)
   apply(drule_tac x="M'a" in meta_spec)
   apply(drule_tac x="x3" in meta_spec)
   apply(drule conjunct2)
   apply(drule mp)
    apply(rule conjI)
     apply(simp)
    apply(rule disjI1)
    apply(simp add: SNa_Redu_def)
   apply(drule_tac x="a" in spec)
   apply(drule mp)
    apply(simp add: CANDs_preserved_single)
   apply(drule mp)
    apply(simp add: a_preserves_SNa)
   apply(drule_tac x="x" in spec)
   apply(simp)
  apply(erule disjE)
    (* right-inner reduction *)
   apply(erule exE)
   apply(erule conjE)+
   apply(simp)
   apply(drule_tac x="x1" in meta_spec)
   apply(drule_tac x="x2" in meta_spec)
   apply(drule_tac x="N'" in meta_spec)
   apply(drule conjunct2)
   apply(drule mp)
    apply(rule conjI)
     apply(simp)
    apply(rule disjI2)
    apply(simp add: SNa_Redu_def)
   apply(drule_tac x="a" in spec)
   apply(drule mp)
    apply(simp add: CANDs_preserved_single)
   apply(drule mp)
    apply(assumption)
   apply(drule_tac x="x" in spec)
   apply(drule mp)
    apply(simp add: CANDs_preserved_single)
   apply(drule mp)
    apply(simp add: a_preserves_SNa)
   apply(assumption)
  apply(erule disjE)
    (******** c-reduction *********)
   apply(drule Cut_c_redu_elim)
    (* c-left reduction*)
   apply(erule disjE)
    apply(erule conjE)
    apply(frule_tac B="x1" in fic_CANDS)
     apply(simp)
    apply(erule disjE)
    (* in AXIOMSc *)
     apply(simp add: AXIOMSc_def)
     apply(erule exE)+
     apply(simp add: ctrm.inject)
     apply(simp add: alpha)
     apply(erule disjE)
      apply(simp)
      apply(rule impI)
      apply(simp)
      apply(subgoal_tac "fic (Ax y b) b")(*A*)
       apply(simp)
    (*A*)
      apply(auto)[1]
     apply(simp)
     apply(rule impI)
     apply(simp)
     apply(subgoal_tac "fic (Ax ([(a,aa)]\<bullet>y) a) a")(*B*)
      apply(simp)
    (*B*)
     apply(auto)[1]
    (* in BINDINGc *)
    apply(simp)
    apply(drule BINDINGc_elim)
    apply(simp)
    (* c-right reduction*)
   apply(erule conjE)
   apply(frule_tac B="x1" in fin_CANDS)
    apply(simp)
   apply(erule disjE)
    (* in AXIOMSc *)
    apply(simp add: AXIOMSn_def)
    apply(erule exE)+
    apply(simp add: ntrm.inject)
    apply(simp add: alpha)
    apply(erule disjE)
     apply(simp)
     apply(rule impI)
     apply(simp)
     apply(subgoal_tac "fin (Ax xa b) xa")(*A*)
      apply(simp)
    (*A*)
     apply(auto)[1]
    apply(simp)
    apply(rule impI)
    apply(simp)
    apply(subgoal_tac "fin (Ax x ([(x,xa)]\<bullet>b)) x")(*B*)
     apply(simp)
    (*B*)
    apply(auto)[1]
    (* in BINDINGc *)
   apply(simp)
   apply(drule BINDINGn_elim)
   apply(simp)
    (*********** l-reductions ************)
  apply(drule Cut_l_redu_elim)
  apply(erule disjE)
    (* ax1 *)
   apply(erule exE)
   apply(simp)
   apply(simp add: SNa_preserved_renaming1)
  apply(erule disjE)
    (* ax2 *)
   apply(erule exE)
   apply(simp add: SNa_preserved_renaming2)
  apply(erule disjE)
    (* LNot *)
   apply(erule exE)+
   apply(auto)[1]
   apply(frule_tac excluded_m)
    apply(assumption)
   apply(erule disjE)
    (* one of them in BINDING *)
    apply(erule disjE)
     apply(drule fin_elims)
     apply(drule fic_elims)
     apply(simp)
     apply(drule BINDINGc_elim)
     apply(drule_tac x="x" in spec)
     apply(drule_tac x="NotL <b>.N' x" in spec)
     apply(simp)
     apply(simp add: better_NotR_substc)
     apply(generate_fresh "coname")
     apply(subgoal_tac "fresh_fun (\<lambda>a'. Cut <a'>.NotR (y).M'a a' (x).NotL <b>.N' x) 
                   =  Cut <c>.NotR (y).M'a c (x).NotL <b>.N' x")
      apply(simp)
      apply(subgoal_tac "Cut <c>.NotR (y).M'a c (x).NotL <b>.N' x \<longrightarrow>\<^sub>a Cut <b>.N' (y).M'a")
       apply(simp only: a_preserves_SNa)
      apply(rule al_redu)
      apply(rule better_LNot_intro)
       apply(simp)
      apply(simp)
     apply(fresh_fun_simp (no_asm))
     apply(simp)
    (* other case of in BINDING *)
    apply(drule fin_elims)
    apply(drule fic_elims)
    apply(simp)
    apply(drule BINDINGn_elim)
    apply(drule_tac x="a" in spec)
    apply(drule_tac x="NotR (y).M'a a" in spec)
    apply(simp)
    apply(simp add: better_NotL_substn)
    apply(generate_fresh "name")
    apply(subgoal_tac "fresh_fun (\<lambda>x'. Cut <a>.NotR (y).M'a a (x').NotL <b>.N' x') 
                   = Cut <a>.NotR (y).M'a a (c).NotL <b>.N' c")
     apply(simp)
     apply(subgoal_tac "Cut <a>.NotR (y).M'a a (c).NotL <b>.N' c \<longrightarrow>\<^sub>a Cut <b>.N' (y).M'a")
      apply(simp only: a_preserves_SNa)
     apply(rule al_redu)
     apply(rule better_LNot_intro)
      apply(simp)
     apply(simp)
    apply(fresh_fun_simp (no_asm))
    apply(simp)
    (* none of them in BINDING *)
   apply(simp)
   apply(erule conjE)
   apply(frule CAND_NotR_elim)
    apply(assumption)
   apply(erule exE)
   apply(frule CAND_NotL_elim)
    apply(assumption)
   apply(erule exE)
   apply(simp only: ty.inject)
   apply(drule_tac x="B'" in meta_spec)
   apply(drule_tac x="N'" in meta_spec)
   apply(drule_tac x="M'a" in meta_spec)
   apply(erule conjE)+
   apply(drule mp)
    apply(simp)
   apply(drule_tac x="b" in spec)
   apply(rotate_tac 13)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 13)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(drule_tac x="y" in spec)
   apply(rotate_tac 13)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 13)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(assumption)
    (* LAnd1 case *)
  apply(erule disjE)
   apply(erule exE)+
   apply(auto)[1]
   apply(frule_tac excluded_m)
    apply(assumption)
   apply(erule disjE)
    (* one of them in BINDING *)
    apply(erule disjE)
     apply(drule fin_elims)
     apply(drule fic_elims)
     apply(simp)
     apply(drule BINDINGc_elim)
     apply(drule_tac x="x" in spec)
     apply(drule_tac x="AndL1 (y).N' x" in spec)
     apply(simp)
     apply(simp add: better_AndR_substc)
     apply(generate_fresh "coname")
     apply(subgoal_tac "fresh_fun (\<lambda>a'. Cut <a'>.AndR <b>.M1 <c>.M2 a' (x).AndL1 (y).N' x) 
                   = Cut <ca>.AndR <b>.M1 <c>.M2 ca (x).AndL1 (y).N' x")
      apply(simp)
      apply(subgoal_tac "Cut <ca>.AndR <b>.M1 <c>.M2 ca (x).AndL1 (y).N' x \<longrightarrow>\<^sub>a Cut <b>.M1 (y).N'")
       apply(auto intro: a_preserves_SNa)[1]
      apply(rule al_redu)
      apply(rule better_LAnd1_intro)
       apply(simp add: abs_fresh fresh_prod fresh_atm)
      apply(simp)
     apply(fresh_fun_simp (no_asm))
     apply(simp)
    (* other case of in BINDING *)
    apply(drule fin_elims)
    apply(drule fic_elims)
    apply(simp)
    apply(drule BINDINGn_elim)
    apply(drule_tac x="a" in spec)
    apply(drule_tac x="AndR <b>.M1 <c>.M2 a" in spec)
    apply(simp)
    apply(simp add: better_AndL1_substn)
    apply(generate_fresh "name")
    apply(subgoal_tac "fresh_fun (\<lambda>z'. Cut <a>.AndR <b>.M1 <c>.M2 a (z').AndL1 (y).N' z') 
                   = Cut <a>.AndR <b>.M1 <c>.M2 a (ca).AndL1 (y).N' ca")
     apply(simp)
     apply(subgoal_tac "Cut <a>.AndR <b>.M1 <c>.M2 a (ca).AndL1 (y).N' ca \<longrightarrow>\<^sub>a Cut <b>.M1 (y).N'")
      apply(auto intro: a_preserves_SNa)[1]
     apply(rule al_redu)
     apply(rule better_LAnd1_intro)
      apply(simp add: abs_fresh fresh_prod fresh_atm) 
     apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(fresh_fun_simp (no_asm))
    apply(simp)
    (* none of them in BINDING *)
   apply(simp)
   apply(erule conjE)
   apply(frule CAND_AndR_elim)
    apply(assumption)
   apply(erule exE)
   apply(frule CAND_AndL1_elim)
    apply(assumption)
   apply(erule exE)+
   apply(simp only: ty.inject)
   apply(drule_tac x="B1" in meta_spec)
   apply(drule_tac x="M1" in meta_spec)
   apply(drule_tac x="N'" in meta_spec)
   apply(erule conjE)+
   apply(drule mp)
    apply(simp)
   apply(drule_tac x="b" in spec)
   apply(rotate_tac 14)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 14)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(drule_tac x="y" in spec)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(assumption)
    (* LAnd2 case *)
  apply(erule disjE)
   apply(erule exE)+
   apply(auto)[1]
   apply(frule_tac excluded_m)
    apply(assumption)
   apply(erule disjE)
    (* one of them in BINDING *)
    apply(erule disjE)
     apply(drule fin_elims)
     apply(drule fic_elims)
     apply(simp)
     apply(drule BINDINGc_elim)
     apply(drule_tac x="x" in spec)
     apply(drule_tac x="AndL2 (y).N' x" in spec)
     apply(simp)
     apply(simp add: better_AndR_substc)
     apply(generate_fresh "coname")
     apply(subgoal_tac "fresh_fun (\<lambda>a'. Cut <a'>.AndR <b>.M1 <c>.M2 a' (x).AndL2 (y).N' x) 
                   = Cut <ca>.AndR <b>.M1 <c>.M2 ca (x).AndL2 (y).N' x")
      apply(simp)
      apply(subgoal_tac "Cut <ca>.AndR <b>.M1 <c>.M2 ca (x).AndL2 (y).N' x \<longrightarrow>\<^sub>a Cut <c>.M2 (y).N'")
       apply(auto intro: a_preserves_SNa)[1]
      apply(rule al_redu)
      apply(rule better_LAnd2_intro)
       apply(simp add: abs_fresh fresh_prod fresh_atm)
      apply(simp)
     apply(fresh_fun_simp (no_asm))
     apply(simp)
    (* other case of in BINDING *)
    apply(drule fin_elims)
    apply(drule fic_elims)
    apply(simp)
    apply(drule BINDINGn_elim)
    apply(drule_tac x="a" in spec)
    apply(drule_tac x="AndR <b>.M1 <c>.M2 a" in spec)
    apply(simp)
    apply(simp add: better_AndL2_substn)
    apply(generate_fresh "name")
    apply(subgoal_tac "fresh_fun (\<lambda>z'. Cut <a>.AndR <b>.M1 <c>.M2 a (z').AndL2 (y).N' z') 
                   = Cut <a>.AndR <b>.M1 <c>.M2 a (ca).AndL2 (y).N' ca")
     apply(simp)
     apply(subgoal_tac "Cut <a>.AndR <b>.M1 <c>.M2 a (ca).AndL2 (y).N' ca \<longrightarrow>\<^sub>a Cut <c>.M2 (y).N'")
      apply(auto intro: a_preserves_SNa)[1]
     apply(rule al_redu)
     apply(rule better_LAnd2_intro)
      apply(simp add: abs_fresh fresh_prod fresh_atm) 
     apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(fresh_fun_simp (no_asm))
    apply(simp)
    (* none of them in BINDING *)
   apply(simp)
   apply(erule conjE)
   apply(frule CAND_AndR_elim)
    apply(assumption)
   apply(erule exE)
   apply(frule CAND_AndL2_elim)
    apply(assumption)
   apply(erule exE)+
   apply(simp only: ty.inject)
   apply(drule_tac x="B2" in meta_spec)
   apply(drule_tac x="M2" in meta_spec)
   apply(drule_tac x="N'" in meta_spec)
   apply(erule conjE)+
   apply(drule mp)
    apply(simp)
   apply(drule_tac x="c" in spec)
   apply(rotate_tac 14)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 14)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(drule_tac x="y" in spec)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(assumption)
    (* LOr1 case *)
  apply(erule disjE)
   apply(erule exE)+
   apply(auto)[1]
   apply(frule_tac excluded_m)
    apply(assumption)
   apply(erule disjE)
    (* one of them in BINDING *)
    apply(erule disjE)
     apply(drule fin_elims)
     apply(drule fic_elims)
     apply(simp)
     apply(drule BINDINGc_elim)
     apply(drule_tac x="x" in spec)
     apply(drule_tac x="OrL (z).M1 (y).M2 x" in spec)
     apply(simp)
     apply(simp add: better_OrR1_substc)
     apply(generate_fresh "coname")
     apply(subgoal_tac "fresh_fun (\<lambda>a'. Cut <a'>.OrR1 <b>.N' a' (x).OrL (z).M1 (y).M2 x) 
                   = Cut <c>.OrR1 <b>.N' c (x).OrL (z).M1 (y).M2 x")
      apply(simp)
      apply(subgoal_tac "Cut <c>.OrR1 <b>.N' c (x).OrL (z).M1 (y).M2 x \<longrightarrow>\<^sub>a Cut <b>.N' (z).M1")
       apply(auto intro: a_preserves_SNa)[1]
      apply(rule al_redu)
      apply(rule better_LOr1_intro)
       apply(simp add: abs_fresh fresh_prod fresh_atm)
      apply(simp add: abs_fresh)
     apply(fresh_fun_simp (no_asm))
     apply(simp)
    (* other case of in BINDING *)
    apply(drule fin_elims)
    apply(drule fic_elims)
    apply(simp)
    apply(drule BINDINGn_elim)
    apply(drule_tac x="a" in spec)
    apply(drule_tac x="OrR1 <b>.N' a" in spec)
    apply(simp)
    apply(simp add: better_OrL_substn)
    apply(generate_fresh "name")
    apply(subgoal_tac "fresh_fun (\<lambda>z'. Cut <a>.OrR1 <b>.N' a (z').OrL (z).M1 (y).M2 z') 
                   = Cut <a>.OrR1 <b>.N' a (c).OrL (z).M1 (y).M2 c")
     apply(simp)
     apply(subgoal_tac "Cut <a>.OrR1 <b>.N' a (c).OrL (z).M1 (y).M2 c \<longrightarrow>\<^sub>a Cut <b>.N' (z).M1")
      apply(auto intro: a_preserves_SNa)[1]
     apply(rule al_redu)
     apply(rule better_LOr1_intro)
      apply(simp add: abs_fresh fresh_prod fresh_atm) 
     apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(fresh_fun_simp (no_asm))
    apply(simp)
    (* none of them in BINDING *)
   apply(simp)
   apply(erule conjE)
   apply(frule CAND_OrR1_elim)
    apply(assumption)
   apply(erule exE)+
   apply(frule CAND_OrL_elim)
    apply(assumption)
   apply(erule exE)+
   apply(simp only: ty.inject)
   apply(drule_tac x="B1" in meta_spec)
   apply(drule_tac x="N'" in meta_spec)
   apply(drule_tac x="M1" in meta_spec)
   apply(erule conjE)+
   apply(drule mp)
    apply(simp)
   apply(drule_tac x="b" in spec)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(drule_tac x="z" in spec)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(assumption)
    (* LOr2 case *)
  apply(erule disjE)
   apply(erule exE)+
   apply(auto)[1]
   apply(frule_tac excluded_m)
    apply(assumption)
   apply(erule disjE)
    (* one of them in BINDING *)
    apply(erule disjE)
     apply(drule fin_elims)
     apply(drule fic_elims)
     apply(simp)
     apply(drule BINDINGc_elim)
     apply(drule_tac x="x" in spec)
     apply(drule_tac x="OrL (z).M1 (y).M2 x" in spec)
     apply(simp)
     apply(simp add: better_OrR2_substc)
     apply(generate_fresh "coname")
     apply(subgoal_tac "fresh_fun (\<lambda>a'. Cut <a'>.OrR2 <b>.N' a' (x).OrL (z).M1 (y).M2 x) 
                   = Cut <c>.OrR2 <b>.N' c (x).OrL (z).M1 (y).M2 x")
      apply(simp)
      apply(subgoal_tac "Cut <c>.OrR2 <b>.N' c (x).OrL (z).M1 (y).M2 x \<longrightarrow>\<^sub>a Cut <b>.N' (y).M2")
       apply(auto intro: a_preserves_SNa)[1]
      apply(rule al_redu)
      apply(rule better_LOr2_intro)
       apply(simp add: abs_fresh fresh_prod fresh_atm)
      apply(simp add: abs_fresh)
     apply(fresh_fun_simp (no_asm))
     apply(simp)
    (* other case of in BINDING *)
    apply(drule fin_elims)
    apply(drule fic_elims)
    apply(simp)
    apply(drule BINDINGn_elim)
    apply(drule_tac x="a" in spec)
    apply(drule_tac x="OrR2 <b>.N' a" in spec)
    apply(simp)
    apply(simp add: better_OrL_substn)
    apply(generate_fresh "name")
    apply(subgoal_tac "fresh_fun (\<lambda>z'. Cut <a>.OrR2 <b>.N' a (z').OrL (z).M1 (y).M2 z') 
                   = Cut <a>.OrR2 <b>.N' a (c).OrL (z).M1 (y).M2 c")
     apply(simp)
     apply(subgoal_tac "Cut <a>.OrR2 <b>.N' a (c).OrL (z).M1 (y).M2 c \<longrightarrow>\<^sub>a Cut <b>.N' (y).M2")
      apply(auto intro: a_preserves_SNa)[1]
     apply(rule al_redu)
     apply(rule better_LOr2_intro)
      apply(simp add: abs_fresh fresh_prod fresh_atm) 
     apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(fresh_fun_simp (no_asm))
    apply(simp)
    (* none of them in BINDING *)
   apply(simp)
   apply(erule conjE)
   apply(frule CAND_OrR2_elim)
    apply(assumption)
   apply(erule exE)+
   apply(frule CAND_OrL_elim)
    apply(assumption)
   apply(erule exE)+
   apply(simp only: ty.inject)
   apply(drule_tac x="B2" in meta_spec)
   apply(drule_tac x="N'" in meta_spec)
   apply(drule_tac x="M2" in meta_spec)
   apply(erule conjE)+
   apply(drule mp)
    apply(simp)
   apply(drule_tac x="b" in spec)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(drule_tac x="y" in spec)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 15)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(assumption)
    (* LImp case *)
  apply(erule exE)+
  apply(auto)[1]
  apply(frule_tac excluded_m)
   apply(assumption)
  apply(erule disjE)
    (* one of them in BINDING *)
   apply(erule disjE)
    apply(drule fin_elims)
    apply(drule fic_elims)
    apply(simp)
    apply(drule BINDINGc_elim)
    apply(drule_tac x="x" in spec)
    apply(drule_tac x="ImpL <c>.N1 (y).N2 x" in spec)
    apply(simp)
    apply(simp add: better_ImpR_substc)
    apply(generate_fresh "coname")
    apply(subgoal_tac "fresh_fun (\<lambda>a'. Cut <a'>.ImpR (z).<b>.M'a a' (x).ImpL <c>.N1 (y).N2 x)
                   = Cut <ca>.ImpR (z).<b>.M'a ca (x).ImpL <c>.N1 (y).N2 x")
     apply(simp)
     apply(subgoal_tac "Cut <ca>.ImpR (z).<b>.M'a ca (x).ImpL <c>.N1 (y).N2 x \<longrightarrow>\<^sub>a 
                                                          Cut <b>.Cut <c>.N1 (z).M'a (y).N2")
      apply(auto intro: a_preserves_SNa)[1]
     apply(rule al_redu)
     apply(rule better_LImp_intro)
       apply(simp add: abs_fresh fresh_prod fresh_atm)
      apply(simp add: abs_fresh)
     apply(simp)
    apply(fresh_fun_simp (no_asm))
    apply(simp)
    (* other case of in BINDING *)
   apply(drule fin_elims)
   apply(drule fic_elims)
   apply(simp)
   apply(drule BINDINGn_elim)
   apply(drule_tac x="a" in spec)
   apply(drule_tac x="ImpR (z).<b>.M'a a" in spec)
   apply(simp)
   apply(simp add: better_ImpL_substn)
   apply(generate_fresh "name")
   apply(subgoal_tac "fresh_fun (\<lambda>z'. Cut <a>.ImpR (z).<b>.M'a a (z').ImpL <c>.N1 (y).N2 z')
                   = Cut <a>.ImpR (z).<b>.M'a a (ca).ImpL <c>.N1 (y).N2 ca")
    apply(simp)
    apply(subgoal_tac "Cut <a>.ImpR (z).<b>.M'a a (ca).ImpL <c>.N1 (y).N2 ca \<longrightarrow>\<^sub>a 
                                                          Cut <b>.Cut <c>.N1 (z).M'a (y).N2")
     apply(auto intro: a_preserves_SNa)[1]
    apply(rule al_redu)
    apply(rule better_LImp_intro)
      apply(simp add: abs_fresh fresh_prod fresh_atm) 
     apply(simp add: abs_fresh fresh_prod fresh_atm)
    apply(simp)
   apply(fresh_fun_simp (no_asm))
    apply(simp add: abs_fresh abs_supp fin_supp)
   apply(simp add: abs_fresh abs_supp fin_supp)
  apply(simp)
    (* none of them in BINDING *)
  apply(erule conjE)
  apply(frule CAND_ImpL_elim)
   apply(assumption)
  apply(erule exE)+
  apply(frule CAND_ImpR_elim) (* check here *)
   apply(assumption)
  apply(erule exE)+
  apply(erule conjE)+
  apply(simp only: ty.inject)
  apply(erule conjE)+
  apply(case_tac "M'a=Ax z b")
    (* case Ma = Ax z b *)
   apply(rule_tac t="Cut <b>.(Cut <c>.N1 (z).M'a) (y).N2" and s="Cut <b>.(M'a{z:=<c>.N1}) (y).N2" in subst)
    apply(simp)
   apply(drule_tac x="c" in spec)
   apply(drule_tac x="N1" in spec)
   apply(drule mp)
    apply(simp)
   apply(drule_tac x="B2" in meta_spec)
   apply(drule_tac x="M'a{z:=<c>.N1}" in meta_spec)
   apply(drule_tac x="N2" in meta_spec)
   apply(drule conjunct1)
   apply(drule mp)
    apply(simp)
   apply(rotate_tac 17)
   apply(drule_tac x="b" in spec)
   apply(drule mp)
    apply(assumption)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(rotate_tac 17)
   apply(drule_tac x="y" in spec)
   apply(drule mp)
    apply(assumption)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(assumption)
    (* case Ma \<noteq> Ax z b *)
  apply(subgoal_tac "<b>:Cut <c>.N1 (z).M'a \<in> \<parallel><B2>\<parallel>") (* lemma *)
   apply(frule_tac meta_spec)
   apply(drule_tac x="B2" in meta_spec)
   apply(drule_tac x="Cut <c>.N1 (z).M'a" in meta_spec)
   apply(drule_tac x="N2" in meta_spec)
   apply(erule conjE)+
   apply(drule mp)
    apply(simp)
   apply(rotate_tac 20)
   apply(drule_tac x="b" in spec)
   apply(rotate_tac 20)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 20)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(rotate_tac 20)
   apply(drule_tac x="y" in spec)
   apply(rotate_tac 20)
   apply(drule mp)
    apply(assumption)
   apply(rotate_tac 20)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(assumption)
    (* lemma *)
  apply(subgoal_tac "<b>:Cut <c>.N1 (z).M'a \<in> BINDINGc B2 (\<parallel>(B2)\<parallel>)") (* second lemma *)
   apply(simp add: BINDING_implies_CAND)
    (* second lemma *)
  apply(simp (no_asm) add: BINDINGc_def)
  apply(rule exI)+
  apply(rule conjI)
   apply(rule refl)
  apply(rule allI)+
  apply(rule impI)
  apply(generate_fresh "name")
  apply(rule_tac t="Cut <c>.N1 (z).M'a" and s="Cut <c>.N1 (ca).([(ca,z)]\<bullet>M'a)" in subst)
   apply(simp add: trm.inject alpha fresh_prod fresh_atm)
  apply(rule_tac t="(Cut <c>.N1 (ca).([(ca,z)]\<bullet>M'a)){b:=(xa).P}" 
      and s="Cut <c>.N1 (ca).(([(ca,z)]\<bullet>M'a){b:=(xa).P})" in subst)
   apply(rule sym)
   apply(rule tricky_subst)
     apply(simp)
    apply(simp)
   apply(clarify)
   apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
   apply(simp add: calc_atm)
  apply(drule_tac x="B1" in meta_spec)
  apply(drule_tac x="N1" in meta_spec)
  apply(drule_tac x="([(ca,z)]\<bullet>M'a){b:=(xa).P}" in meta_spec)
  apply(drule conjunct1)
  apply(drule mp)
   apply(simp)
  apply(rotate_tac 19)
  apply(drule_tac x="c" in spec)
  apply(drule mp)
   apply(assumption)
  apply(drule mp)
   apply(simp add: CANDs_imply_SNa)
  apply(rotate_tac 19)
  apply(drule_tac x="ca" in spec)
  apply(subgoal_tac "(ca):([(ca,z)]\<bullet>M'a){b:=(xa).P} \<in> \<parallel>(B1)\<parallel>")(*A*)
   apply(drule mp)
    apply(assumption)
   apply(drule mp)
    apply(simp add: CANDs_imply_SNa)
   apply(assumption)
    (*A*)
  apply(drule_tac x="[(ca,z)]\<bullet>xa" in spec)
  apply(drule_tac x="[(ca,z)]\<bullet>P" in spec)
  apply(rotate_tac 19)
  apply(simp add: fresh_prod fresh_left)
  apply(drule mp)
   apply(rule conjI)
    apply(auto simp add: calc_atm)[1]
   apply(rule conjI)
    apply(auto simp add: calc_atm)[1]
   apply(drule_tac pi="[(ca,z)]" and x="(xa):P" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
   apply(simp add: CAND_eqvt_name)
  apply(drule_tac pi="[(ca,z)]" and X="\<parallel>(B1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
  apply(simp add: CAND_eqvt_name csubst_eqvt)
  apply(perm_simp)
  done


(* parallel substitution *)


lemma CUT_SNa:
  assumes a1: "<a>:M \<in> (\<parallel><B>\<parallel>)"
    and     a2: "(x):N \<in> (\<parallel>(B)\<parallel>)"
  shows   "SNa (Cut <a>.M (x).N)"
  using a1 a2
  apply -
  apply(rule CUT_SNa_aux[OF a1])
    apply(simp_all add: CANDs_imply_SNa)
  done 


fun 
  findn :: "(name\<times>coname\<times>trm) list\<Rightarrow>name\<Rightarrow>(coname\<times>trm) option"
  where
    "findn [] x = None"
  | "findn ((y,c,P)#\<theta>_n) x = (if y=x then Some (c,P) else findn \<theta>_n x)"

lemma findn_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>findn \<theta>_n x) = findn (pi1\<bullet>\<theta>_n) (pi1\<bullet>x)" 
    and   "(pi2\<bullet>findn \<theta>_n x) = findn (pi2\<bullet>\<theta>_n) (pi2\<bullet>x)"
   apply(induct \<theta>_n)
     apply(auto simp add: perm_bij) 
  done

lemma findn_fresh:
  assumes a: "x\<sharp>\<theta>_n"
  shows "findn \<theta>_n x = None"
  using a
  apply(induct \<theta>_n)
   apply(auto simp add: fresh_list_cons fresh_atm fresh_prod)
  done

fun 
  findc :: "(coname\<times>name\<times>trm) list\<Rightarrow>coname\<Rightarrow>(name\<times>trm) option"
  where
    "findc [] x = None"
  | "findc ((c,y,P)#\<theta>_c) a = (if a=c then Some (y,P) else findc \<theta>_c a)"

lemma findc_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>findc \<theta>_c a) = findc (pi1\<bullet>\<theta>_c) (pi1\<bullet>a)" 
    and   "(pi2\<bullet>findc \<theta>_c a) = findc (pi2\<bullet>\<theta>_c) (pi2\<bullet>a)"
   apply(induct \<theta>_c)
     apply(auto simp add: perm_bij) 
  done

lemma findc_fresh:
  assumes a: "a\<sharp>\<theta>_c"
  shows "findc \<theta>_c a = None"
  using a
  apply(induct \<theta>_c)
   apply(auto simp add: fresh_list_cons fresh_atm fresh_prod)
  done

abbreviation 
  nmaps :: "(name\<times>coname\<times>trm) list \<Rightarrow> name \<Rightarrow> (coname\<times>trm) option \<Rightarrow> bool" ("_ nmaps _ to _" [55,55,55] 55) 
  where
    "\<theta>_n nmaps x to P \<equiv> (findn \<theta>_n x) = P"

abbreviation 
  cmaps :: "(coname\<times>name\<times>trm) list \<Rightarrow> coname \<Rightarrow> (name\<times>trm) option \<Rightarrow> bool" ("_ cmaps _ to _" [55,55,55] 55) 
  where
    "\<theta>_c cmaps a to P \<equiv> (findc \<theta>_c a) = P"

lemma nmaps_fresh:
  shows "\<theta>_n nmaps x to Some (c,P) \<Longrightarrow> a\<sharp>\<theta>_n \<Longrightarrow> a\<sharp>(c,P)"
  apply(induct \<theta>_n)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
   apply(case_tac "aa=x")
    apply(auto)
  apply(case_tac "aa=x")
   apply(auto)
  done

lemma cmaps_fresh:
  shows "\<theta>_c cmaps a to Some (y,P) \<Longrightarrow> x\<sharp>\<theta>_c \<Longrightarrow> x\<sharp>(y,P)"
  apply(induct \<theta>_c)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
   apply(case_tac "a=aa")
    apply(auto)
  apply(case_tac "a=aa")
   apply(auto)
  done

lemma nmaps_false:
  shows "\<theta>_n nmaps x to Some (c,P) \<Longrightarrow> x\<sharp>\<theta>_n \<Longrightarrow> False"
  apply(induct \<theta>_n)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
  done

lemma cmaps_false:
  shows "\<theta>_c cmaps c to Some (x,P) \<Longrightarrow> c\<sharp>\<theta>_c \<Longrightarrow> False"
  apply(induct \<theta>_c)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
  done

fun 
  lookupa :: "name\<Rightarrow>coname\<Rightarrow>(coname\<times>name\<times>trm) list\<Rightarrow>trm"
  where
    "lookupa x a [] = Ax x a"
  | "lookupa x a ((c,y,P)#\<theta>_c) = (if a=c then Cut <a>.Ax x a (y).P else lookupa x a \<theta>_c)"

lemma lookupa_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(lookupa x a \<theta>_c)) = lookupa (pi1\<bullet>x) (pi1\<bullet>a) (pi1\<bullet>\<theta>_c)"
    and   "(pi2\<bullet>(lookupa x a \<theta>_c)) = lookupa (pi2\<bullet>x) (pi2\<bullet>a) (pi2\<bullet>\<theta>_c)"
   apply -
   apply(induct \<theta>_c)
    apply(auto simp add: eqvts)
  apply(induct \<theta>_c)
   apply(auto simp add: eqvts)
  done

lemma lookupa_fire:
  assumes a: "\<theta>_c cmaps a to Some (y,P)"
  shows "(lookupa x a \<theta>_c) = Cut <a>.Ax x a (y).P"
  using a
  apply(induct \<theta>_c arbitrary: x a y P)
   apply(auto)
  done

fun 
  lookupb :: "name\<Rightarrow>coname\<Rightarrow>(coname\<times>name\<times>trm) list\<Rightarrow>coname\<Rightarrow>trm\<Rightarrow>trm"
  where
    "lookupb x a [] c P = Cut <c>.P (x).Ax x a"
  | "lookupb x a ((d,y,N)#\<theta>_c) c P = (if a=d then Cut <c>.P (y).N  else lookupb x a \<theta>_c c P)"

lemma lookupb_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(lookupb x a \<theta>_c c P)) = lookupb (pi1\<bullet>x) (pi1\<bullet>a) (pi1\<bullet>\<theta>_c) (pi1\<bullet>c) (pi1\<bullet>P)"
    and   "(pi2\<bullet>(lookupb x a \<theta>_c c P)) = lookupb (pi2\<bullet>x) (pi2\<bullet>a) (pi2\<bullet>\<theta>_c) (pi2\<bullet>c) (pi2\<bullet>P)"
   apply -
   apply(induct \<theta>_c)
    apply(auto simp add: eqvts)
  apply(induct \<theta>_c)
   apply(auto simp add: eqvts)
  done

fun 
  lookup :: "name\<Rightarrow>coname\<Rightarrow>(name\<times>coname\<times>trm) list\<Rightarrow>(coname\<times>name\<times>trm) list\<Rightarrow>trm"
  where
    "lookup x a [] \<theta>_c = lookupa x a \<theta>_c"
  | "lookup x a ((y,c,P)#\<theta>_n) \<theta>_c = (if x=y then (lookupb x a \<theta>_c c P) else lookup x a \<theta>_n \<theta>_c)"

lemma lookup_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(lookup x a \<theta>_n \<theta>_c)) = lookup (pi1\<bullet>x) (pi1\<bullet>a) (pi1\<bullet>\<theta>_n) (pi1\<bullet>\<theta>_c)"
    and   "(pi2\<bullet>(lookup x a \<theta>_n \<theta>_c)) = lookup (pi2\<bullet>x) (pi2\<bullet>a) (pi2\<bullet>\<theta>_n) (pi2\<bullet>\<theta>_c)"
   apply -
   apply(induct \<theta>_n)
    apply(auto simp add: eqvts)
  apply(induct \<theta>_n)
   apply(auto simp add: eqvts)
  done

fun 
  lookupc :: "name\<Rightarrow>coname\<Rightarrow>(name\<times>coname\<times>trm) list\<Rightarrow>trm"
  where
    "lookupc x a [] = Ax x a"
  | "lookupc x a ((y,c,P)#\<theta>_n) = (if x=y then P[c\<turnstile>c>a] else lookupc x a \<theta>_n)"

lemma lookupc_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(lookupc x a \<theta>_n)) = lookupc (pi1\<bullet>x) (pi1\<bullet>a) (pi1\<bullet>\<theta>_n)"
    and   "(pi2\<bullet>(lookupc x a \<theta>_n)) = lookupc (pi2\<bullet>x) (pi2\<bullet>a) (pi2\<bullet>\<theta>_n)"
   apply -
   apply(induct \<theta>_n)
    apply(auto simp add: eqvts)
  apply(induct \<theta>_n)
   apply(auto simp add: eqvts)
  done

fun 
  lookupd :: "name\<Rightarrow>coname\<Rightarrow>(coname\<times>name\<times>trm) list\<Rightarrow>trm"
  where
    "lookupd x a [] = Ax x a"
  | "lookupd x a ((c,y,P)#\<theta>_c) = (if a=c then P[y\<turnstile>n>x] else lookupd x a \<theta>_c)"

lemma lookupd_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(lookupd x a \<theta>_n)) = lookupd (pi1\<bullet>x) (pi1\<bullet>a) (pi1\<bullet>\<theta>_n)"
    and   "(pi2\<bullet>(lookupd x a \<theta>_n)) = lookupd (pi2\<bullet>x) (pi2\<bullet>a) (pi2\<bullet>\<theta>_n)"
   apply -
   apply(induct \<theta>_n)
    apply(auto simp add: eqvts)
  apply(induct \<theta>_n)
   apply(auto simp add: eqvts)
  done

lemma lookupa_fresh:
  assumes a: "a\<sharp>\<theta>_c"
  shows "lookupa y a \<theta>_c = Ax y a"
  using a
  apply(induct \<theta>_c)
   apply(auto simp add: fresh_prod fresh_list_cons fresh_atm)
  done

lemma lookupa_csubst:
  assumes a: "a\<sharp>\<theta>_c"
  shows "Cut <a>.Ax y a (x).P = (lookupa y a \<theta>_c){a:=(x).P}"
  using a by (simp add: lookupa_fresh)

lemma lookupa_freshness:
  fixes a::"coname"
    and   x::"name"
  shows "a\<sharp>(\<theta>_c,c) \<Longrightarrow> a\<sharp>lookupa y c \<theta>_c"
    and   "x\<sharp>(\<theta>_c,y) \<Longrightarrow> x\<sharp>lookupa y c \<theta>_c"
   apply(induct \<theta>_c)
     apply(auto simp add: fresh_prod fresh_list_cons abs_fresh fresh_atm)
  done

lemma lookupa_unicity:
  assumes a: "lookupa x a \<theta>_c= Ax y b" "b\<sharp>\<theta>_c" "y\<sharp>\<theta>_c"
  shows "x=y \<and> a=b"
  using a
  apply(induct \<theta>_c)
   apply(auto simp add: trm.inject fresh_list_cons fresh_prod fresh_atm)
   apply(case_tac "a=aa")
    apply(auto)
  apply(case_tac "a=aa")
   apply(auto)
  done

lemma lookupb_csubst:
  assumes a: "a\<sharp>(\<theta>_c,c,N)"
  shows "Cut <c>.N (x).P = (lookupb y a \<theta>_c c N){a:=(x).P}"
  using a
  apply(induct \<theta>_c)
   apply(auto simp add: fresh_list_cons fresh_atm fresh_prod)
  apply(rule sym)
  apply(generate_fresh "name")
  apply(generate_fresh "coname")
  apply(subgoal_tac "Cut <c>.N (y).Ax y a = Cut <caa>.([(caa,c)]\<bullet>N) (ca).Ax ca a")
   apply(simp)
   apply(rule trans)
    apply(rule better_Cut_substc)
     apply(simp)
    apply(simp add: abs_fresh)
   apply(simp)
   apply(subgoal_tac "a\<sharp>([(caa,c)]\<bullet>N)")
    apply(simp add: forget)
    apply(simp add: trm.inject)
   apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
  apply(simp add: trm.inject)
  apply(rule conjI)
   apply(rule sym)
   apply(simp add: alpha fresh_prod fresh_atm)
  apply(simp add: alpha calc_atm fresh_prod fresh_atm)
  done

lemma lookupb_freshness:
  fixes a::"coname"
    and   x::"name"
  shows "a\<sharp>(\<theta>_c,c,b,P) \<Longrightarrow> a\<sharp>lookupb y c \<theta>_c b P"
    and   "x\<sharp>(\<theta>_c,y,P) \<Longrightarrow> x\<sharp>lookupb y c \<theta>_c b P"
   apply(induct \<theta>_c)
     apply(auto simp add: fresh_prod fresh_list_cons abs_fresh fresh_atm)
  done

lemma lookupb_unicity:
  assumes a: "lookupb x a \<theta>_c c P = Ax y b" "b\<sharp>(\<theta>_c,c,P)" "y\<sharp>\<theta>_c"
  shows "x=y \<and> a=b"
  using a
  apply(induct \<theta>_c)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
   apply(case_tac "a=aa")
    apply(auto)
  apply(case_tac "a=aa")
   apply(auto)
  done

lemma lookupb_lookupa:
  assumes a: "x\<sharp>\<theta>_c"
  shows "lookupb x c \<theta>_c a P = (lookupa x c \<theta>_c){x:=<a>.P}"
  using a
  apply(induct \<theta>_c)
   apply(auto simp add: fresh_list_cons fresh_prod)
  apply(generate_fresh "coname")
  apply(generate_fresh "name")
  apply(subgoal_tac "Cut <c>.Ax x c (aa).b = Cut <ca>.Ax x ca (caa).([(caa,aa)]\<bullet>b)")
   apply(simp)
   apply(rule sym)
   apply(rule trans)
    apply(rule better_Cut_substn)
     apply(simp add: abs_fresh)
    apply(simp)
   apply(simp)
   apply(subgoal_tac "x\<sharp>([(caa,aa)]\<bullet>b)")
    apply(simp add: forget)
    apply(simp add: trm.inject)
   apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(simp add: trm.inject)
  apply(rule conjI)
   apply(simp add: alpha calc_atm fresh_atm fresh_prod)
  apply(rule sym)
  apply(simp add: alpha calc_atm fresh_atm fresh_prod)
  done

lemma lookup_csubst:
  assumes a: "a\<sharp>(\<theta>_n,\<theta>_c)"
  shows "lookup y c \<theta>_n ((a,x,P)#\<theta>_c) = (lookup y c \<theta>_n \<theta>_c){a:=(x).P}"
  using a
  apply(induct \<theta>_n)
   apply(auto simp add: fresh_prod fresh_list_cons)
     apply(simp add: lookupa_csubst)
    apply(simp add: lookupa_freshness forget fresh_atm fresh_prod)
   apply(rule lookupb_csubst)
   apply(simp)
  apply(auto simp add: lookupb_freshness forget fresh_atm fresh_prod)
  done

lemma lookup_fresh:
  assumes a: "x\<sharp>(\<theta>_n,\<theta>_c)"
  shows "lookup x c \<theta>_n \<theta>_c = lookupa x c \<theta>_c"
  using a
  apply(induct \<theta>_n)
   apply(auto simp add: fresh_prod fresh_list_cons fresh_atm)
  done

lemma lookup_unicity:
  assumes a: "lookup x a \<theta>_n \<theta>_c= Ax y b" "b\<sharp>(\<theta>_c,\<theta>_n)" "y\<sharp>(\<theta>_c,\<theta>_n)"
  shows "x=y \<and> a=b"
  using a
  apply(induct \<theta>_n)
   apply(auto simp add: trm.inject fresh_list_cons fresh_prod fresh_atm)
     apply(drule lookupa_unicity)
       apply(simp)+
    apply(drule lookupa_unicity)
      apply(simp)+
   apply(case_tac "x=aa")
    apply(auto)
   apply(drule lookupb_unicity)
     apply(simp add: fresh_atm)
    apply(simp)
   apply(simp)
  apply(case_tac "x=aa")
   apply(auto)
  apply(drule lookupb_unicity)
    apply(simp add: fresh_atm)
   apply(simp)
  apply(simp)
  done

lemma lookup_freshness:
  fixes a::"coname"
    and   x::"name"
  shows "a\<sharp>(c,\<theta>_c,\<theta>_n) \<Longrightarrow> a\<sharp>lookup y c \<theta>_n \<theta>_c"
    and   "x\<sharp>(y,\<theta>_c,\<theta>_n) \<Longrightarrow> x\<sharp>lookup y c \<theta>_n \<theta>_c"   
   apply(induct \<theta>_n)
     apply(auto simp add: fresh_prod fresh_list_cons abs_fresh fresh_atm)
     apply(simp add: fresh_atm fresh_prod lookupa_freshness)
    apply(simp add: fresh_atm fresh_prod lookupa_freshness)
   apply(simp add: fresh_atm fresh_prod lookupb_freshness)
  apply(simp add: fresh_atm fresh_prod lookupb_freshness)
  done

lemma lookupc_freshness:
  fixes a::"coname"
    and   x::"name"
  shows "a\<sharp>(\<theta>_c,c) \<Longrightarrow> a\<sharp>lookupc y c \<theta>_c"
    and   "x\<sharp>(\<theta>_c,y) \<Longrightarrow> x\<sharp>lookupc y c \<theta>_c"
   apply(induct \<theta>_c)
     apply(auto simp add: fresh_prod fresh_list_cons abs_fresh fresh_atm)
   apply(rule rename_fresh)
   apply(simp add: fresh_atm)
  apply(rule rename_fresh)
  apply(simp add: fresh_atm)
  done

lemma lookupc_fresh:
  assumes a: "y\<sharp>\<theta>_n"
  shows "lookupc y a \<theta>_n = Ax y a"
  using a
  apply(induct \<theta>_n)
   apply(auto simp add: fresh_prod fresh_list_cons fresh_atm)
  done

lemma lookupc_nmaps:
  assumes a: "\<theta>_n nmaps x to Some (c,P)"
  shows "lookupc x a \<theta>_n = P[c\<turnstile>c>a]"
  using a
  apply(induct \<theta>_n)
   apply(auto)
  done 

lemma lookupc_unicity:
  assumes a: "lookupc y a \<theta>_n = Ax x b" "x\<sharp>\<theta>_n"
  shows "y=x"
  using a
  apply(induct \<theta>_n)
   apply(auto simp add: trm.inject fresh_list_cons fresh_prod)
  apply(case_tac "y=aa")
   apply(auto)
  apply(subgoal_tac "x\<sharp>(ba[aa\<turnstile>c>a])")
   apply(simp add: fresh_atm)
  apply(rule rename_fresh)
  apply(simp)
  done

lemma lookupd_fresh:
  assumes a: "a\<sharp>\<theta>_c"
  shows "lookupd y a \<theta>_c = Ax y a"
  using a
  apply(induct \<theta>_c)
   apply(auto simp add: fresh_prod fresh_list_cons fresh_atm)
  done 

lemma lookupd_unicity:
  assumes a: "lookupd y a \<theta>_c = Ax y b" "b\<sharp>\<theta>_c"
  shows "a=b"
  using a
  apply(induct \<theta>_c)
   apply(auto simp add: trm.inject fresh_list_cons fresh_prod)
  apply(case_tac "a=aa")
   apply(auto)
  apply(subgoal_tac "b\<sharp>(ba[aa\<turnstile>n>y])")
   apply(simp add: fresh_atm)
  apply(rule rename_fresh)
  apply(simp)
  done

lemma lookupd_freshness:
  fixes a::"coname"
    and   x::"name"
  shows "a\<sharp>(\<theta>_c,c) \<Longrightarrow> a\<sharp>lookupd y c \<theta>_c"
    and   "x\<sharp>(\<theta>_c,y) \<Longrightarrow> x\<sharp>lookupd y c \<theta>_c"
   apply(induct \<theta>_c)
     apply(auto simp add: fresh_prod fresh_list_cons abs_fresh fresh_atm)
   apply(rule rename_fresh)
   apply(simp add: fresh_atm)
  apply(rule rename_fresh)
  apply(simp add: fresh_atm)
  done

lemma lookupd_cmaps:
  assumes a: "\<theta>_c cmaps a to Some (x,P)"
  shows "lookupd y a \<theta>_c = P[x\<turnstile>n>y]"
  using a
  apply(induct \<theta>_c)
   apply(auto)
  done 

nominal_primrec (freshness_context: "\<theta>_n::(name\<times>coname\<times>trm)")
  stn :: "trm\<Rightarrow>(name\<times>coname\<times>trm) list\<Rightarrow>trm" 
  where
    "stn (Ax x a) \<theta>_n = lookupc x a \<theta>_n"
  | "\<lbrakk>a\<sharp>(N,\<theta>_n);x\<sharp>(M,\<theta>_n)\<rbrakk> \<Longrightarrow> stn (Cut <a>.M (x).N) \<theta>_n = (Cut <a>.M (x).N)" 
  | "x\<sharp>\<theta>_n \<Longrightarrow> stn (NotR (x).M a) \<theta>_n = (NotR (x).M a)"
  | "a\<sharp>\<theta>_n \<Longrightarrow>stn (NotL <a>.M x) \<theta>_n = (NotL <a>.M x)"
  | "\<lbrakk>a\<sharp>(N,d,b,\<theta>_n);b\<sharp>(M,d,a,\<theta>_n)\<rbrakk> \<Longrightarrow> stn (AndR <a>.M <b>.N d) \<theta>_n = (AndR <a>.M <b>.N d)"
  | "x\<sharp>(z,\<theta>_n) \<Longrightarrow> stn (AndL1 (x).M z) \<theta>_n = (AndL1 (x).M z)"
  | "x\<sharp>(z,\<theta>_n) \<Longrightarrow> stn (AndL2 (x).M z) \<theta>_n = (AndL2 (x).M z)"
  | "a\<sharp>(b,\<theta>_n) \<Longrightarrow> stn (OrR1 <a>.M b) \<theta>_n = (OrR1 <a>.M b)"
  | "a\<sharp>(b,\<theta>_n) \<Longrightarrow> stn (OrR2 <a>.M b) \<theta>_n = (OrR2 <a>.M b)"
  | "\<lbrakk>x\<sharp>(N,z,u,\<theta>_n);u\<sharp>(M,z,x,\<theta>_n)\<rbrakk> \<Longrightarrow> stn (OrL (x).M (u).N z) \<theta>_n = (OrL (x).M (u).N z)"
  | "\<lbrakk>a\<sharp>(b,\<theta>_n);x\<sharp>\<theta>_n\<rbrakk> \<Longrightarrow> stn (ImpR (x).<a>.M b) \<theta>_n = (ImpR (x).<a>.M b)"
  | "\<lbrakk>a\<sharp>(N,\<theta>_n);x\<sharp>(M,z,\<theta>_n)\<rbrakk> \<Longrightarrow> stn (ImpL <a>.M (x).N z) \<theta>_n = (ImpL <a>.M (x).N z)"
                       apply(finite_guess)+
                       apply(rule TrueI)+
                       apply(simp add: abs_fresh abs_supp fin_supp)+
                       apply(fresh_guess)+
  done

nominal_primrec (freshness_context: "\<theta>_c::(coname\<times>name\<times>trm)")
  stc :: "trm\<Rightarrow>(coname\<times>name\<times>trm) list\<Rightarrow>trm" 
  where
    "stc (Ax x a) \<theta>_c = lookupd x a \<theta>_c"
  | "\<lbrakk>a\<sharp>(N,\<theta>_c);x\<sharp>(M,\<theta>_c)\<rbrakk> \<Longrightarrow> stc (Cut <a>.M (x).N) \<theta>_c = (Cut <a>.M (x).N)" 
  | "x\<sharp>\<theta>_c \<Longrightarrow> stc (NotR (x).M a) \<theta>_c = (NotR (x).M a)"
  | "a\<sharp>\<theta>_c \<Longrightarrow> stc (NotL <a>.M x) \<theta>_c = (NotL <a>.M x)"
  | "\<lbrakk>a\<sharp>(N,d,b,\<theta>_c);b\<sharp>(M,d,a,\<theta>_c)\<rbrakk> \<Longrightarrow> stc (AndR <a>.M <b>.N d) \<theta>_c = (AndR <a>.M <b>.N d)"
  | "x\<sharp>(z,\<theta>_c) \<Longrightarrow> stc (AndL1 (x).M z) \<theta>_c = (AndL1 (x).M z)"
  | "x\<sharp>(z,\<theta>_c) \<Longrightarrow> stc (AndL2 (x).M z) \<theta>_c = (AndL2 (x).M z)"
  | "a\<sharp>(b,\<theta>_c) \<Longrightarrow> stc (OrR1 <a>.M b) \<theta>_c = (OrR1 <a>.M b)"
  | "a\<sharp>(b,\<theta>_c) \<Longrightarrow> stc (OrR2 <a>.M b) \<theta>_c = (OrR2 <a>.M b)"
  | "\<lbrakk>x\<sharp>(N,z,u,\<theta>_c);u\<sharp>(M,z,x,\<theta>_c)\<rbrakk> \<Longrightarrow> stc (OrL (x).M (u).N z) \<theta>_c = (OrL (x).M (u).N z)"
  | "\<lbrakk>a\<sharp>(b,\<theta>_c);x\<sharp>\<theta>_c\<rbrakk> \<Longrightarrow> stc (ImpR (x).<a>.M b) \<theta>_c = (ImpR (x).<a>.M b)"
  | "\<lbrakk>a\<sharp>(N,\<theta>_c);x\<sharp>(M,z,\<theta>_c)\<rbrakk> \<Longrightarrow> stc (ImpL <a>.M (x).N z) \<theta>_c = (ImpL <a>.M (x).N z)"
                       apply(finite_guess)+
                       apply(rule TrueI)+
                       apply(simp add: abs_fresh abs_supp fin_supp)+
                       apply(fresh_guess)+
  done

lemma stn_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(stn M \<theta>_n)) = stn (pi1\<bullet>M) (pi1\<bullet>\<theta>_n)"
    and   "(pi2\<bullet>(stn M \<theta>_n)) = stn (pi2\<bullet>M) (pi2\<bullet>\<theta>_n)"
   apply -
   apply(nominal_induct M avoiding: \<theta>_n rule: trm.strong_induct)
              apply(auto simp add: eqvts fresh_bij fresh_prod eq_bij fresh_atm)
  apply(nominal_induct M avoiding: \<theta>_n rule: trm.strong_induct)
             apply(auto simp add: eqvts fresh_bij fresh_prod eq_bij fresh_atm)
  done

lemma stc_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(stc M \<theta>_c)) = stc (pi1\<bullet>M) (pi1\<bullet>\<theta>_c)"
    and   "(pi2\<bullet>(stc M \<theta>_c)) = stc (pi2\<bullet>M) (pi2\<bullet>\<theta>_c)"
   apply -
   apply(nominal_induct M avoiding: \<theta>_c rule: trm.strong_induct)
              apply(auto simp add: eqvts fresh_bij fresh_prod eq_bij fresh_atm)
  apply(nominal_induct M avoiding: \<theta>_c rule: trm.strong_induct)
             apply(auto simp add: eqvts fresh_bij fresh_prod eq_bij fresh_atm)
  done

lemma stn_fresh:
  fixes a::"coname"
    and   x::"name"
  shows "a\<sharp>(\<theta>_n,M) \<Longrightarrow> a\<sharp>stn M \<theta>_n"
    and   "x\<sharp>(\<theta>_n,M) \<Longrightarrow> x\<sharp>stn M \<theta>_n"
   apply(nominal_induct M avoiding: \<theta>_n a x rule: trm.strong_induct)
                       apply(auto simp add: abs_fresh fresh_prod fresh_atm)
   apply(rule lookupc_freshness)
   apply(simp add: fresh_atm)
  apply(rule lookupc_freshness)
  apply(simp add: fresh_atm)
  done

lemma stc_fresh:
  fixes a::"coname"
    and   x::"name"
  shows "a\<sharp>(\<theta>_c,M) \<Longrightarrow> a\<sharp>stc M \<theta>_c"
    and   "x\<sharp>(\<theta>_c,M) \<Longrightarrow> x\<sharp>stc M \<theta>_c"
   apply(nominal_induct M avoiding: \<theta>_c a x rule: trm.strong_induct)
                       apply(auto simp add: abs_fresh fresh_prod fresh_atm)
   apply(rule lookupd_freshness)
   apply(simp add: fresh_atm)
  apply(rule lookupd_freshness)
  apply(simp add: fresh_atm)
  done

lemma case_option_eqvt1[eqvt_force]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
    and   B::"(name\<times>trm) option"
    and   r::"trm"
  shows "(pi1\<bullet>(case B of Some (x,P) \<Rightarrow> s x P | None \<Rightarrow> r)) = 
              (case (pi1\<bullet>B) of Some (x,P) \<Rightarrow> (pi1\<bullet>s) x P | None \<Rightarrow> (pi1\<bullet>r))"
    and   "(pi2\<bullet>(case B of Some (x,P) \<Rightarrow> s x P| None \<Rightarrow> r)) = 
              (case (pi2\<bullet>B) of Some (x,P) \<Rightarrow> (pi2\<bullet>s) x P | None \<Rightarrow> (pi2\<bullet>r))"
   apply(cases "B")
    apply(auto)
   apply(perm_simp)
  apply(cases "B")
   apply(auto)
  apply(perm_simp)
  done

lemma case_option_eqvt2[eqvt_force]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
    and   B::"(coname\<times>trm) option"
    and   r::"trm"
  shows "(pi1\<bullet>(case B of Some (x,P) \<Rightarrow> s x P | None \<Rightarrow> r)) = 
              (case (pi1\<bullet>B) of Some (x,P) \<Rightarrow> (pi1\<bullet>s) x P | None \<Rightarrow> (pi1\<bullet>r))"
    and   "(pi2\<bullet>(case B of Some (x,P) \<Rightarrow> s x P| None \<Rightarrow> r)) = 
              (case (pi2\<bullet>B) of Some (x,P) \<Rightarrow> (pi2\<bullet>s) x P | None \<Rightarrow> (pi2\<bullet>r))"
   apply(cases "B")
    apply(auto)
   apply(perm_simp)
  apply(cases "B")
   apply(auto)
  apply(perm_simp)
  done

nominal_primrec (freshness_context: "(\<theta>_n::(name\<times>coname\<times>trm) list,\<theta>_c::(coname\<times>name\<times>trm) list)")
  psubst :: "(name\<times>coname\<times>trm) list\<Rightarrow>(coname\<times>name\<times>trm) list\<Rightarrow>trm\<Rightarrow>trm" ("_,_<_>" [100,100,100] 100) 
  where
    "\<theta>_n,\<theta>_c<Ax x a> = lookup x a \<theta>_n \<theta>_c" 
  | "\<lbrakk>a\<sharp>(N,\<theta>_n,\<theta>_c);x\<sharp>(M,\<theta>_n,\<theta>_c)\<rbrakk> \<Longrightarrow> \<theta>_n,\<theta>_c<Cut <a>.M (x).N> = 
   Cut <a>.(if \<exists>x. M=Ax x a then stn M \<theta>_n else \<theta>_n,\<theta>_c<M>) 
       (x).(if \<exists>a. N=Ax x a then stc N \<theta>_c else \<theta>_n,\<theta>_c<N>)" 
  | "x\<sharp>(\<theta>_n,\<theta>_c) \<Longrightarrow> \<theta>_n,\<theta>_c<NotR (x).M a> = 
  (case (findc \<theta>_c a) of 
       Some (u,P) \<Rightarrow> fresh_fun (\<lambda>a'. Cut <a'>.NotR (x).(\<theta>_n,\<theta>_c<M>) a' (u).P) 
     | None \<Rightarrow> NotR (x).(\<theta>_n,\<theta>_c<M>) a)"
  | "a\<sharp>(\<theta>_n,\<theta>_c) \<Longrightarrow> \<theta>_n,\<theta>_c<NotL <a>.M x> = 
  (case (findn \<theta>_n x) of 
       Some (c,P) \<Rightarrow> fresh_fun (\<lambda>x'. Cut <c>.P (x').(NotL <a>.(\<theta>_n,\<theta>_c<M>) x')) 
     | None \<Rightarrow> NotL <a>.(\<theta>_n,\<theta>_c<M>) x)"
  | "\<lbrakk>a\<sharp>(N,c,\<theta>_n,\<theta>_c);b\<sharp>(M,c,\<theta>_n,\<theta>_c);b\<noteq>a\<rbrakk> \<Longrightarrow> (\<theta>_n,\<theta>_c<AndR <a>.M <b>.N c>) = 
  (case (findc \<theta>_c c) of 
       Some (x,P) \<Rightarrow> fresh_fun (\<lambda>a'. Cut <a'>.(AndR <a>.(\<theta>_n,\<theta>_c<M>) <b>.(\<theta>_n,\<theta>_c<N>) a') (x).P)
     | None \<Rightarrow> AndR <a>.(\<theta>_n,\<theta>_c<M>) <b>.(\<theta>_n,\<theta>_c<N>) c)"
  | "x\<sharp>(z,\<theta>_n,\<theta>_c) \<Longrightarrow> (\<theta>_n,\<theta>_c<AndL1 (x).M z>) = 
  (case (findn \<theta>_n z) of 
       Some (c,P) \<Rightarrow> fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL1 (x).(\<theta>_n,\<theta>_c<M>) z') 
     | None \<Rightarrow> AndL1 (x).(\<theta>_n,\<theta>_c<M>) z)"
  | "x\<sharp>(z,\<theta>_n,\<theta>_c) \<Longrightarrow> (\<theta>_n,\<theta>_c<AndL2 (x).M z>) = 
  (case (findn \<theta>_n z) of 
       Some (c,P) \<Rightarrow> fresh_fun (\<lambda>z'. Cut <c>.P (z').AndL2 (x).(\<theta>_n,\<theta>_c<M>) z') 
     | None \<Rightarrow> AndL2 (x).(\<theta>_n,\<theta>_c<M>) z)"
  | "\<lbrakk>x\<sharp>(N,z,\<theta>_n,\<theta>_c);u\<sharp>(M,z,\<theta>_n,\<theta>_c);x\<noteq>u\<rbrakk> \<Longrightarrow> (\<theta>_n,\<theta>_c<OrL (x).M (u).N z>) =
  (case (findn \<theta>_n z) of  
       Some (c,P) \<Rightarrow> fresh_fun (\<lambda>z'. Cut <c>.P (z').OrL (x).(\<theta>_n,\<theta>_c<M>) (u).(\<theta>_n,\<theta>_c<N>) z') 
     | None \<Rightarrow> OrL (x).(\<theta>_n,\<theta>_c<M>) (u).(\<theta>_n,\<theta>_c<N>) z)"
  | "a\<sharp>(b,\<theta>_n,\<theta>_c) \<Longrightarrow> (\<theta>_n,\<theta>_c<OrR1 <a>.M b>) = 
  (case (findc \<theta>_c b) of
       Some (x,P) \<Rightarrow> fresh_fun (\<lambda>a'. Cut <a'>.OrR1 <a>.(\<theta>_n,\<theta>_c<M>) a' (x).P) 
     | None \<Rightarrow> OrR1 <a>.(\<theta>_n,\<theta>_c<M>) b)"
  | "a\<sharp>(b,\<theta>_n,\<theta>_c) \<Longrightarrow> (\<theta>_n,\<theta>_c<OrR2 <a>.M b>) = 
  (case (findc \<theta>_c b) of
       Some (x,P) \<Rightarrow> fresh_fun (\<lambda>a'. Cut <a'>.OrR2 <a>.(\<theta>_n,\<theta>_c<M>) a' (x).P) 
     | None \<Rightarrow> OrR2 <a>.(\<theta>_n,\<theta>_c<M>) b)"
  | "\<lbrakk>a\<sharp>(b,\<theta>_n,\<theta>_c); x\<sharp>(\<theta>_n,\<theta>_c)\<rbrakk> \<Longrightarrow> (\<theta>_n,\<theta>_c<ImpR (x).<a>.M b>) = 
  (case (findc \<theta>_c b) of
       Some (z,P) \<Rightarrow> fresh_fun (\<lambda>a'. Cut <a'>.ImpR (x).<a>.(\<theta>_n,\<theta>_c<M>) a' (z).P)
     | None \<Rightarrow> ImpR (x).<a>.(\<theta>_n,\<theta>_c<M>) b)"
  | "\<lbrakk>a\<sharp>(N,\<theta>_n,\<theta>_c); x\<sharp>(z,M,\<theta>_n,\<theta>_c)\<rbrakk> \<Longrightarrow> (\<theta>_n,\<theta>_c<ImpL <a>.M (x).N z>) = 
  (case (findn \<theta>_n z) of
       Some (c,P) \<Rightarrow> fresh_fun (\<lambda>z'. Cut <c>.P (z').ImpL <a>.(\<theta>_n,\<theta>_c<M>) (x).(\<theta>_n,\<theta>_c<N>) z') 
     | None \<Rightarrow> ImpL <a>.(\<theta>_n,\<theta>_c<M>) (x).(\<theta>_n,\<theta>_c<N>) z)"
                       apply(finite_guess)+
                       apply(rule TrueI)+
                       apply(simp add: abs_fresh stc_fresh)
                       apply(simp add: abs_fresh stn_fresh)
                       apply(case_tac "findc \<theta>_c x3")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "coname")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule cmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findn \<theta>_n x3")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "name")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule nmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findc \<theta>_c x5")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "coname")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule cmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findc \<theta>_c x5")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "coname")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule_tac x="x3" in cmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findn \<theta>_n x3")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "name")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule nmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findn \<theta>_n x3")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "name")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule nmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findc \<theta>_c x3")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "coname")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule cmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findc \<theta>_c x3")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "coname")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule cmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findn \<theta>_n x5")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "name")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule nmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findn \<theta>_n x5")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "name")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule_tac a="x3" in nmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findc \<theta>_c x4")
                       apply(simp add: abs_fresh abs_supp fin_supp)
                       apply(auto)[1]
                       apply(generate_fresh "coname")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule cmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm abs_supp fin_supp)
                       apply(case_tac "findc \<theta>_c x4")
                       apply(simp add: abs_fresh abs_supp fin_supp)
                       apply(auto)[1]
                       apply(generate_fresh "coname")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule_tac x="x2" in cmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm abs_supp fin_supp)
                       apply(case_tac "findn \<theta>_n x5")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "name")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule nmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(case_tac "findn \<theta>_n x5")
                       apply(simp add: abs_fresh)
                       apply(auto)[1]
                       apply(generate_fresh "name")
                       apply(fresh_fun_simp (no_asm))
                       apply(drule_tac a="x3" in nmaps_fresh)
                       apply(auto simp add: fresh_prod)[1]
                       apply(simp add: abs_fresh fresh_prod fresh_atm)
                       apply(fresh_guess)+
  done

lemma case_cong:
  assumes a: "B1=B2" "x1=x2" "y1=y2"
  shows "(case B1 of None \<Rightarrow> x1 | Some (x,P) \<Rightarrow> y1 x P) = (case B2 of None \<Rightarrow> x2 | Some (x,P) \<Rightarrow> y2 x P)"
  using a
  apply(auto)
  done

lemma find_maps:
  shows "\<theta>_c cmaps a to (findc \<theta>_c a)"
    and   "\<theta>_n nmaps x to (findn \<theta>_n x)"
   apply(auto)
  done

lemma psubst_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "pi1\<bullet>(\<theta>_n,\<theta>_c<M>) = (pi1\<bullet>\<theta>_n),(pi1\<bullet>\<theta>_c)<(pi1\<bullet>M)>"
    and   "pi2\<bullet>(\<theta>_n,\<theta>_c<M>) = (pi2\<bullet>\<theta>_n),(pi2\<bullet>\<theta>_c)<(pi2\<bullet>M)>"
   apply(nominal_induct M avoiding: \<theta>_n \<theta>_c rule: trm.strong_induct)
                       apply(auto simp add: eq_bij fresh_bij eqvts perm_pi_simp)
                     apply(rule case_cong)
                       apply(rule find_maps)
                      apply(simp)
                     apply(perm_simp add: eqvts)
                    apply(rule case_cong)
                      apply(rule find_maps)
                     apply(simp)
                    apply(perm_simp add: eqvts)
                   apply(rule case_cong)
                     apply(rule find_maps)
                    apply(simp)
                   apply(perm_simp add: eqvts)
                  apply(rule case_cong)
                    apply(rule find_maps)
                   apply(simp)
                  apply(perm_simp add: eqvts)
                 apply(rule case_cong)
                   apply(rule find_maps)
                  apply(simp)
                 apply(perm_simp add: eqvts)
                apply(rule case_cong)
                  apply(rule find_maps)
                 apply(simp)
                apply(perm_simp add: eqvts)
               apply(rule case_cong)
                 apply(rule find_maps)
                apply(simp)
               apply(perm_simp add: eqvts)
              apply(rule case_cong)
                apply(rule find_maps)
               apply(simp)
              apply(perm_simp add: eqvts)
             apply(rule case_cong)
               apply(rule find_maps)
              apply(simp)
             apply(perm_simp add: eqvts)
            apply(rule case_cong)
              apply(rule find_maps)
             apply(simp)
            apply(perm_simp add: eqvts)
           apply(rule case_cong)
             apply(rule find_maps)
            apply(simp)
           apply(perm_simp add: eqvts)
          apply(rule case_cong)
            apply(rule find_maps)
           apply(simp)
          apply(perm_simp add: eqvts)
         apply(rule case_cong)
           apply(rule find_maps)
          apply(simp)
         apply(perm_simp add: eqvts)
        apply(rule case_cong)
          apply(rule find_maps)
         apply(simp)
        apply(perm_simp add: eqvts)
       apply(rule case_cong)
         apply(rule find_maps)
        apply(simp)
       apply(perm_simp add: eqvts)
      apply(rule case_cong)
        apply(rule find_maps)
       apply(simp)
      apply(perm_simp add: eqvts)
     apply(rule case_cong)
       apply(rule find_maps)
      apply(simp)
     apply(perm_simp add: eqvts)
    apply(rule case_cong)
      apply(rule find_maps)
     apply(simp)
    apply(perm_simp add: eqvts)
   apply(rule case_cong)
     apply(rule find_maps)
    apply(simp)
   apply(perm_simp add: eqvts)
  apply(rule case_cong)
    apply(rule find_maps)
   apply(simp)
  apply(perm_simp add: eqvts)
  done

lemma ax_psubst:
  assumes a: "\<theta>_n,\<theta>_c<M> = Ax x a"
    and     b: "a\<sharp>(\<theta>_n,\<theta>_c)" "x\<sharp>(\<theta>_n,\<theta>_c)"
  shows "M = Ax x a"
  using a b
  apply(nominal_induct M avoiding: \<theta>_n \<theta>_c rule: trm.strong_induct)
             apply(auto)
            apply(drule lookup_unicity)
              apply(simp)+
           apply(case_tac "findc \<theta>_c coname")
            apply(simp)
           apply(auto)[1]
           apply(generate_fresh "coname")
           apply(fresh_fun_simp)
           apply(simp)
          apply(case_tac "findn \<theta>_n name")
           apply(simp)
          apply(auto)[1]
          apply(generate_fresh "name")
          apply(fresh_fun_simp)
          apply(simp)
         apply(case_tac "findc \<theta>_c coname3")
          apply(simp)
         apply(auto)[1]
         apply(generate_fresh "coname")
         apply(fresh_fun_simp)
         apply(simp)
        apply(case_tac "findn \<theta>_n name2")
         apply(simp)
        apply(auto)[1]
        apply(generate_fresh "name")
        apply(fresh_fun_simp)
        apply(simp)
       apply(case_tac "findn \<theta>_n name2")
        apply(simp)
       apply(auto)[1]
       apply(generate_fresh "name")
       apply(fresh_fun_simp)
       apply(simp)
      apply(case_tac "findc \<theta>_c coname2")
       apply(simp)
      apply(auto)[1]
      apply(generate_fresh "coname")
      apply(fresh_fun_simp)
      apply(simp)
     apply(case_tac "findc \<theta>_c coname2")
      apply(simp)
     apply(auto)[1]
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(simp)
    apply(case_tac "findn \<theta>_n name3")
     apply(simp)
    apply(auto)[1]
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(simp)
   apply(case_tac "findc \<theta>_c coname2")
    apply(simp)
   apply(auto)[1]
   apply(generate_fresh "coname")
   apply(fresh_fun_simp)
   apply(simp)
  apply(case_tac "findn \<theta>_n name2")
   apply(simp)
  apply(auto)[1]
  apply(generate_fresh "name")
  apply(fresh_fun_simp)
  apply(simp)
  done

lemma better_Cut_substc1:
  assumes a: "a\<sharp>(P,b)" "b\<sharp>N" 
  shows "(Cut <a>.M (x).N){b:=(y).P} = Cut <a>.(M{b:=(y).P}) (x).N"
  using a
  apply -
  apply(generate_fresh "coname")
  apply(generate_fresh "name")
  apply(subgoal_tac "Cut <a>.M (x).N = Cut <c>.([(c,a)]\<bullet>M) (ca).([(ca,x)]\<bullet>N)")
   apply(simp)
   apply(rule trans)
    apply(rule better_Cut_substc)
     apply(simp)
    apply(simp add: abs_fresh)
   apply(auto)[1]
    apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
    apply(simp add: calc_atm fresh_atm)
   apply(subgoal_tac"b\<sharp>([(ca,x)]\<bullet>N)")
    apply(simp add: forget)
    apply(simp add: trm.inject)
    apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
    apply(perm_simp)
   apply(simp add: fresh_left calc_atm)
  apply(simp add: trm.inject)
  apply(rule conjI)
   apply(rule sym)
   apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
  apply(rule sym)
  apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
  done

lemma better_Cut_substc2:
  assumes a: "x\<sharp>(y,P)" "b\<sharp>(a,M)" "N\<noteq>Ax x b"
  shows "(Cut <a>.M (x).N){b:=(y).P} = Cut <a>.M (x).(N{b:=(y).P})"
  using a
  apply -
  apply(generate_fresh "coname")
  apply(generate_fresh "name")
  apply(subgoal_tac "Cut <a>.M (x).N = Cut <c>.([(c,a)]\<bullet>M) (ca).([(ca,x)]\<bullet>N)")
   apply(simp)
   apply(rule trans)
    apply(rule better_Cut_substc)
     apply(simp)
    apply(simp add: abs_fresh)
   apply(auto)[1]
    apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
    apply(simp add: calc_atm fresh_atm fresh_prod)
   apply(subgoal_tac"b\<sharp>([(c,a)]\<bullet>M)")
    apply(simp add: forget)
    apply(simp add: trm.inject)
    apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
    apply(perm_simp)
   apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(simp add: trm.inject)
  apply(rule conjI)
   apply(rule sym)
   apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
  apply(rule sym)
  apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
  done

lemma better_Cut_substn1:
  assumes a: "y\<sharp>(x,N)" "a\<sharp>(b,P)" "M\<noteq>Ax y a"
  shows "(Cut <a>.M (x).N){y:=<b>.P} = Cut <a>.(M{y:=<b>.P}) (x).N"
  using a
  apply -
  apply(generate_fresh "coname")
  apply(generate_fresh "name")
  apply(subgoal_tac "Cut <a>.M (x).N = Cut <c>.([(c,a)]\<bullet>M) (ca).([(ca,x)]\<bullet>N)")
   apply(simp)
   apply(rule trans)
    apply(rule better_Cut_substn)
     apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
   apply(auto)[1]
    apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
    apply(simp add: calc_atm fresh_atm fresh_prod)
   apply(subgoal_tac"y\<sharp>([(ca,x)]\<bullet>N)")
    apply(simp add: forget)
    apply(simp add: trm.inject)
    apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
    apply(perm_simp)
   apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
  apply(simp add: trm.inject)
  apply(rule conjI)
   apply(rule sym)
   apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
  apply(rule sym)
  apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
  done

lemma better_Cut_substn2:
  assumes a: "x\<sharp>(P,y)" "y\<sharp>M" 
  shows "(Cut <a>.M (x).N){y:=<b>.P} = Cut <a>.M (x).(N{y:=<b>.P})"
  using a
  apply -
  apply(generate_fresh "coname")
  apply(generate_fresh "name")
  apply(subgoal_tac "Cut <a>.M (x).N = Cut <c>.([(c,a)]\<bullet>M) (ca).([(ca,x)]\<bullet>N)")
   apply(simp)
   apply(rule trans)
    apply(rule better_Cut_substn)
     apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
   apply(auto)[1]
    apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
    apply(simp add: calc_atm fresh_atm)
   apply(subgoal_tac"y\<sharp>([(c,a)]\<bullet>M)")
    apply(simp add: forget)
    apply(simp add: trm.inject)
    apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
    apply(perm_simp)
   apply(simp add: fresh_left calc_atm)
  apply(simp add: trm.inject)
  apply(rule conjI)
   apply(rule sym)
   apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
  apply(rule sym)
  apply(simp add: alpha eqvts calc_atm fresh_prod fresh_atm subst_fresh)[1]
  done

lemma psubst_fresh_name:
  fixes x::"name"
  assumes a: "x\<sharp>\<theta>_n" "x\<sharp>\<theta>_c" "x\<sharp>M"
  shows "x\<sharp>\<theta>_n,\<theta>_c<M>"
  using a
  apply(nominal_induct M avoiding: x \<theta>_n \<theta>_c rule: trm.strong_induct)
             apply(simp add: lookup_freshness)
            apply(auto simp add: abs_fresh)[1]
                 apply(simp add: lookupc_freshness)
                apply(simp add: lookupc_freshness)
               apply(simp add: lookupc_freshness)
              apply(simp add: lookupd_freshness)
             apply(simp add: lookupd_freshness)
            apply(simp add: lookupc_freshness)
           apply(simp)
           apply(case_tac "findc \<theta>_c coname")
            apply(auto simp add: abs_fresh)[1]
           apply(auto)[1]
           apply(generate_fresh "coname")
           apply(fresh_fun_simp)
           apply(simp add: abs_fresh fresh_prod fresh_atm cmaps_fresh)
          apply(simp)
          apply(case_tac "findn \<theta>_n name")
           apply(auto simp add: abs_fresh)[1]
          apply(auto)[1]
          apply(generate_fresh "name")
          apply(fresh_fun_simp)
          apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
         apply(simp)
         apply(case_tac "findc \<theta>_c coname3")
          apply(auto simp add: abs_fresh)[1]
         apply(auto)[1]
         apply(generate_fresh "coname")
         apply(fresh_fun_simp)
         apply(simp add: abs_fresh fresh_prod fresh_atm cmaps_fresh)
        apply(simp)
        apply(case_tac "findn \<theta>_n name2")
         apply(auto simp add: abs_fresh)[1]
        apply(auto)[1]
        apply(generate_fresh "name")
        apply(fresh_fun_simp)
        apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
       apply(simp)
       apply(case_tac "findn \<theta>_n name2")
        apply(auto simp add: abs_fresh)[1]
       apply(auto)[1]
       apply(generate_fresh "name")
       apply(fresh_fun_simp)
       apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
      apply(simp)
      apply(case_tac "findc \<theta>_c coname2")
       apply(auto simp add: abs_fresh)[1]
      apply(auto)[1]
      apply(generate_fresh "coname")
      apply(fresh_fun_simp)
      apply(simp add: abs_fresh fresh_prod fresh_atm cmaps_fresh)
     apply(simp)
     apply(case_tac "findc \<theta>_c coname2")
      apply(auto simp add: abs_fresh)[1]
     apply(auto)[1]
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(simp add: abs_fresh fresh_prod fresh_atm cmaps_fresh)
    apply(simp)
    apply(case_tac "findn \<theta>_n name3")
     apply(auto simp add: abs_fresh)[1]
    apply(auto)[1]
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
   apply(simp)
   apply(case_tac "findc \<theta>_c coname2")
    apply(auto simp add: abs_fresh abs_supp fin_supp)[1]
   apply(auto)[1]
   apply(generate_fresh "coname")
   apply(fresh_fun_simp)
   apply(simp add: abs_fresh abs_supp fin_supp fresh_prod fresh_atm cmaps_fresh)
  apply(simp)
  apply(case_tac "findn \<theta>_n name2")
   apply(auto simp add: abs_fresh)[1]
  apply(auto)[1]
  apply(generate_fresh "name")
  apply(fresh_fun_simp)
  apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
  done

lemma psubst_fresh_coname:
  fixes a::"coname"
  assumes a: "a\<sharp>\<theta>_n" "a\<sharp>\<theta>_c" "a\<sharp>M"
  shows "a\<sharp>\<theta>_n,\<theta>_c<M>"
  using a
  apply(nominal_induct M avoiding: a \<theta>_n \<theta>_c rule: trm.strong_induct)
             apply(simp add: lookup_freshness)
            apply(auto simp add: abs_fresh)[1]
                 apply(simp add: lookupd_freshness)
                apply(simp add: lookupd_freshness)
               apply(simp add: lookupc_freshness)
              apply(simp add: lookupd_freshness)
             apply(simp add: lookupc_freshness)
            apply(simp add: lookupd_freshness)
           apply(simp)
           apply(case_tac "findc \<theta>_c coname")
            apply(auto simp add: abs_fresh)[1]
           apply(auto)[1]
           apply(generate_fresh "coname")
           apply(fresh_fun_simp)
           apply(simp add: abs_fresh fresh_prod fresh_atm cmaps_fresh)
          apply(simp)
          apply(case_tac "findn \<theta>_n name")
           apply(auto simp add: abs_fresh)[1]
          apply(auto)[1]
          apply(generate_fresh "name")
          apply(fresh_fun_simp)
          apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
         apply(simp)
         apply(case_tac "findc \<theta>_c coname3")
          apply(auto simp add: abs_fresh)[1]
         apply(auto)[1]
         apply(generate_fresh "coname")
         apply(fresh_fun_simp)
         apply(simp add: abs_fresh fresh_prod fresh_atm cmaps_fresh)
        apply(simp)
        apply(case_tac "findn \<theta>_n name2")
         apply(auto simp add: abs_fresh)[1]
        apply(auto)[1]
        apply(generate_fresh "name")
        apply(fresh_fun_simp)
        apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
       apply(simp)
       apply(case_tac "findn \<theta>_n name2")
        apply(auto simp add: abs_fresh)[1]
       apply(auto)[1]
       apply(generate_fresh "name")
       apply(fresh_fun_simp)
       apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
      apply(simp)
      apply(case_tac "findc \<theta>_c coname2")
       apply(auto simp add: abs_fresh)[1]
      apply(auto)[1]
      apply(generate_fresh "coname")
      apply(fresh_fun_simp)
      apply(simp add: abs_fresh fresh_prod fresh_atm cmaps_fresh)
     apply(simp)
     apply(case_tac "findc \<theta>_c coname2")
      apply(auto simp add: abs_fresh)[1]
     apply(auto)[1]
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(simp add: abs_fresh fresh_prod fresh_atm cmaps_fresh)
    apply(simp)
    apply(case_tac "findn \<theta>_n name3")
     apply(auto simp add: abs_fresh)[1]
    apply(auto)[1]
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
   apply(simp)
   apply(case_tac "findc \<theta>_c coname2")
    apply(auto simp add: abs_fresh abs_supp fin_supp)[1]
   apply(auto)[1]
   apply(generate_fresh "coname")
   apply(fresh_fun_simp)
   apply(simp add: abs_fresh abs_supp fin_supp fresh_prod fresh_atm cmaps_fresh)
  apply(simp)
  apply(case_tac "findn \<theta>_n name2")
   apply(auto simp add: abs_fresh)[1]
  apply(auto)[1]
  apply(generate_fresh "name")
  apply(fresh_fun_simp)
  apply(simp add: abs_fresh fresh_prod fresh_atm nmaps_fresh)
  done

lemma psubst_csubst:
  assumes a: "a\<sharp>(\<theta>_n,\<theta>_c)"
  shows "\<theta>_n,((a,x,P)#\<theta>_c)<M> = ((\<theta>_n,\<theta>_c<M>){a:=(x).P})"
  using a
  apply(nominal_induct M avoiding: a x \<theta>_n \<theta>_c P rule: trm.strong_induct)
             apply(auto simp add: fresh_list_cons fresh_prod)[1]
             apply(simp add: lookup_csubst)
            apply(simp add: fresh_list_cons fresh_prod)
            apply(auto)[1]
                 apply(rule sym)
                 apply(rule trans)
                  apply(rule better_Cut_substc)
                   apply(simp)
                  apply(simp add: abs_fresh fresh_atm)
                 apply(simp add: lookupd_fresh)
                 apply(subgoal_tac "a\<sharp>lookupc xa coname \<theta>_n")
                  apply(simp add: forget)
                  apply(simp add: trm.inject)
                  apply(rule sym)
                  apply(simp add: alpha nrename_swap fresh_atm)
                 apply(rule lookupc_freshness)
                 apply(simp add: fresh_atm)
                apply(rule sym)
                apply(rule trans)
                 apply(rule better_Cut_substc)
                  apply(simp)
                 apply(simp add: abs_fresh fresh_atm)
                apply(simp)
                apply(rule conjI)
                 apply(rule impI)
                 apply(simp add: lookupd_unicity)
                apply(rule impI)
                apply(subgoal_tac "a\<sharp>lookupc xa coname \<theta>_n")
                 apply(subgoal_tac "a\<sharp>lookupd name aa \<theta>_c")
                  apply(simp add: forget)
                 apply(rule lookupd_freshness)
                 apply(simp add: fresh_atm)
                apply(rule lookupc_freshness)
                apply(simp add: fresh_atm)
               apply(rule sym)
               apply(rule trans)
                apply(rule better_Cut_substc)
                 apply(simp)
                apply(simp add: abs_fresh fresh_atm)
               apply(simp)
               apply(rule conjI)
                apply(rule impI)
                apply(drule ax_psubst)
                  apply(simp)
                 apply(simp)
                apply(blast)
               apply(rule impI)
               apply(subgoal_tac "a\<sharp>lookupc xa coname \<theta>_n")
                apply(simp add: forget)
               apply(rule lookupc_freshness)
               apply(simp add: fresh_atm)
              apply(rule sym)
              apply(rule trans)
               apply(rule better_Cut_substc)
                apply(simp)
               apply(simp add: abs_fresh fresh_atm)
              apply(simp)
              apply(rule conjI)
               apply(rule impI)
               apply(simp add: trm.inject)
               apply(rule sym)
               apply(simp add: alpha)
               apply(simp add: alpha nrename_swap fresh_atm)
              apply(simp add: lookupd_fresh)
             apply(rule sym)
             apply(rule trans)
              apply(rule better_Cut_substc)
               apply(simp)
              apply(simp add: abs_fresh fresh_atm)
             apply(simp)
             apply(rule conjI)
              apply(rule impI)
              apply(simp add: lookupd_unicity)
             apply(rule impI)
             apply(subgoal_tac "a\<sharp>lookupd name aa \<theta>_c")
              apply(simp add: forget)
             apply(rule lookupd_freshness)
             apply(simp add: fresh_atm)
            apply(rule sym)
            apply(rule trans)
             apply(rule better_Cut_substc)
              apply(simp)
             apply(simp add: abs_fresh fresh_atm)
            apply(simp)
            apply(rule impI)
            apply(drule ax_psubst)
              apply(simp)
             apply(simp)
            apply(blast)
    (* NotR *)
           apply(simp)
           apply(case_tac "findc \<theta>_c coname")
            apply(simp)
            apply(auto simp add: fresh_list_cons fresh_prod)[1]
           apply(simp)
           apply(auto simp add: fresh_list_cons fresh_prod)[1]
            apply(drule cmaps_false)
             apply(assumption)
            apply(simp)
           apply(generate_fresh "coname")
           apply(fresh_fun_simp)
           apply(fresh_fun_simp)
           apply(rule sym)
           apply(rule trans)
            apply(rule better_Cut_substc1)
             apply(simp)
            apply(simp add: cmaps_fresh)
           apply(auto simp add: fresh_prod fresh_atm)[1]
    (* NotL *)
          apply(simp)
          apply(case_tac "findn \<theta>_n name")
           apply(simp)
           apply(auto simp add: fresh_list_cons fresh_prod)[1]
          apply(simp)
          apply(auto simp add: fresh_list_cons fresh_prod)[1]
          apply(generate_fresh "name")
          apply(fresh_fun_simp)
          apply(fresh_fun_simp)
          apply(drule_tac a="a" in nmaps_fresh)
           apply(assumption)
          apply(rule sym)
          apply(rule trans)
           apply(rule better_Cut_substc2)
             apply(simp)
            apply(simp)
           apply(simp)
          apply(simp)
    (* AndR *)
         apply(simp)
         apply(case_tac "findc \<theta>_c coname3")
          apply(simp)
          apply(auto simp add: psubst_fresh_coname fresh_list_cons fresh_prod fresh_atm)[1]
         apply(simp)
         apply(auto simp add: fresh_list_cons fresh_prod)[1]
          apply(drule cmaps_false)
           apply(assumption)
          apply(simp)
         apply(generate_fresh "coname")
         apply(fresh_fun_simp)
         apply(fresh_fun_simp)
         apply(rule sym)
         apply(rule trans)
          apply(rule better_Cut_substc1)
           apply(simp)
          apply(simp add: cmaps_fresh)
         apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* AndL1 *)
        apply(simp)
        apply(case_tac "findn \<theta>_n name2")
         apply(simp)
         apply(auto simp add: fresh_list_cons fresh_prod)[1]
        apply(simp)
        apply(auto simp add: fresh_list_cons fresh_prod)[1]
        apply(generate_fresh "name")
        apply(fresh_fun_simp)
        apply(fresh_fun_simp)
        apply(drule_tac a="a" in nmaps_fresh)
         apply(assumption)
        apply(rule sym)
        apply(rule trans)
         apply(rule better_Cut_substc2)
           apply(simp)
          apply(simp)
         apply(simp)
        apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* AndL2 *)
       apply(simp)
       apply(case_tac "findn \<theta>_n name2")
        apply(simp)
        apply(auto simp add: fresh_list_cons fresh_prod)[1]
       apply(simp)
       apply(auto simp add: fresh_list_cons fresh_prod)[1]
       apply(generate_fresh "name")
       apply(fresh_fun_simp)
       apply(fresh_fun_simp)
       apply(drule_tac a="a" in nmaps_fresh)
        apply(assumption)
       apply(rule sym)
       apply(rule trans)
        apply(rule better_Cut_substc2)
          apply(simp)
         apply(simp)
        apply(simp)
       apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* OrR1 *)
      apply(simp)
      apply(case_tac "findc \<theta>_c coname2")
       apply(simp)
       apply(auto simp add: psubst_fresh_coname fresh_list_cons fresh_prod fresh_atm)[1]
      apply(simp)
      apply(auto simp add: fresh_list_cons fresh_prod)[1]
       apply(drule cmaps_false)
        apply(assumption)
       apply(simp)
      apply(generate_fresh "coname")
      apply(fresh_fun_simp)
      apply(fresh_fun_simp)
      apply(rule sym)
      apply(rule trans)
       apply(rule better_Cut_substc1)
        apply(simp)
       apply(simp add: cmaps_fresh)
      apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* OrR2 *)
     apply(simp)
     apply(case_tac "findc \<theta>_c coname2")
      apply(simp)
      apply(auto simp add: psubst_fresh_coname fresh_list_cons fresh_prod fresh_atm)[1]
     apply(simp)
     apply(auto simp add: fresh_list_cons fresh_prod)[1]
      apply(drule cmaps_false)
       apply(assumption)
      apply(simp)
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(fresh_fun_simp)
     apply(rule sym)
     apply(rule trans)
      apply(rule better_Cut_substc1)
       apply(simp)
      apply(simp add: cmaps_fresh)
     apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* OrL *)
    apply(simp)
    apply(case_tac "findn \<theta>_n name3")
     apply(simp)
     apply(auto simp add: fresh_list_cons psubst_fresh_name fresh_atm fresh_prod)[1]
    apply(simp)
    apply(auto simp add: fresh_list_cons fresh_prod)[1]
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(drule_tac a="a" in nmaps_fresh)
     apply(assumption)
    apply(rule sym)
    apply(rule trans)
     apply(rule better_Cut_substc2)
       apply(simp)
      apply(simp)
     apply(simp)
    apply(auto simp add:  psubst_fresh_name fresh_prod fresh_atm)[1]
    (* ImpR *)
   apply(simp)
   apply(case_tac "findc \<theta>_c coname2")
    apply(simp)
    apply(auto simp add: psubst_fresh_coname fresh_list_cons fresh_prod fresh_atm)[1]
   apply(simp)
   apply(auto simp add: fresh_list_cons fresh_prod)[1]
    apply(drule cmaps_false)
     apply(assumption)
    apply(simp)
   apply(generate_fresh "coname")
   apply(fresh_fun_simp)
   apply(fresh_fun_simp)
   apply(rule sym)
   apply(rule trans)
    apply(rule better_Cut_substc1)
     apply(simp)
    apply(simp add: cmaps_fresh)
   apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* ImpL *)
  apply(simp)
  apply(case_tac "findn \<theta>_n name2")
   apply(simp)
   apply(auto simp add: fresh_list_cons psubst_fresh_coname psubst_fresh_name fresh_atm fresh_prod)[1]
  apply(simp)
  apply(auto simp add: fresh_list_cons fresh_prod)[1]
  apply(generate_fresh "name")
  apply(fresh_fun_simp)
  apply(fresh_fun_simp)
  apply(simp add: abs_fresh subst_fresh)
  apply(drule_tac a="a" in nmaps_fresh)
   apply(assumption)
  apply(rule sym)
  apply(rule trans)
   apply(rule better_Cut_substc2)
     apply(simp)
    apply(simp)
   apply(simp)
  apply(auto simp add: psubst_fresh_coname psubst_fresh_name fresh_prod fresh_atm)[1]
  done

lemma psubst_nsubst:
  assumes a: "x\<sharp>(\<theta>_n,\<theta>_c)"
  shows "((x,a,P)#\<theta>_n),\<theta>_c<M> = ((\<theta>_n,\<theta>_c<M>){x:=<a>.P})"
  using a
  apply(nominal_induct M avoiding: a x \<theta>_n \<theta>_c P rule: trm.strong_induct)
             apply(auto simp add: fresh_list_cons fresh_prod)[1]
              apply(simp add: lookup_fresh)
              apply(rule lookupb_lookupa)
              apply(simp)
             apply(rule sym)
             apply(rule forget)
             apply(rule lookup_freshness)
             apply(simp add: fresh_atm)
            apply(auto simp add: lookupc_freshness fresh_list_cons fresh_prod)[1]
                 apply(simp add: lookupc_fresh)
                 apply(rule sym)
                 apply(rule trans)
                  apply(rule better_Cut_substn)
                   apply(simp add: abs_fresh)
                  apply(simp add: abs_fresh fresh_atm)
                 apply(simp add: lookupd_fresh)
                 apply(subgoal_tac "x\<sharp>lookupd name aa \<theta>_c")
                  apply(simp add: forget)
                  apply(simp add: trm.inject)
                  apply(rule sym)
                  apply(simp add: alpha crename_swap fresh_atm)
                 apply(rule lookupd_freshness)
                 apply(simp add: fresh_atm)
                apply(rule sym)
                apply(rule trans)
                 apply(rule better_Cut_substn)
                  apply(simp add: abs_fresh) 
                 apply(simp add: abs_fresh fresh_atm)
                apply(simp)
                apply(rule conjI)
                 apply(rule impI)
                 apply(simp add: lookupc_unicity)
                apply(rule impI)
                apply(subgoal_tac "x\<sharp>lookupc xa coname \<theta>_n")
                 apply(subgoal_tac "x\<sharp>lookupd name aa \<theta>_c")
                  apply(simp add: forget)
                 apply(rule lookupd_freshness)
                 apply(simp add: fresh_atm)
                apply(rule lookupc_freshness)
                apply(simp add: fresh_atm)
               apply(rule sym)
               apply(rule trans)
                apply(rule better_Cut_substn)
                 apply(simp add: abs_fresh)
                apply(simp add: abs_fresh fresh_atm)
               apply(simp)
               apply(rule conjI)
                apply(rule impI)
                apply(simp add: trm.inject)
                apply(rule sym)
                apply(simp add: alpha crename_swap fresh_atm)
               apply(rule impI)
               apply(simp add: lookupc_fresh)
              apply(rule sym)
              apply(rule trans)
               apply(rule better_Cut_substn)
                apply(simp add: abs_fresh)
               apply(simp add: abs_fresh fresh_atm)
              apply(simp)
              apply(rule conjI)
               apply(rule impI)
               apply(simp add: lookupc_unicity)
              apply(rule impI)
              apply(subgoal_tac "x\<sharp>lookupc xa coname \<theta>_n")
               apply(simp add: forget)
              apply(rule lookupc_freshness)
              apply(simp add: fresh_prod fresh_atm)
             apply(rule sym)
             apply(rule trans)
              apply(rule better_Cut_substn)
               apply(simp add: abs_fresh)
              apply(simp add: abs_fresh fresh_atm)
             apply(simp)
             apply(rule conjI)
              apply(rule impI)
              apply(drule ax_psubst)
                apply(simp)
               apply(simp)
              apply(simp)
              apply(blast)
             apply(rule impI)
             apply(subgoal_tac "x\<sharp>lookupd name aa \<theta>_c")
              apply(simp add: forget)
             apply(rule lookupd_freshness)
             apply(simp add: fresh_atm)
            apply(rule sym)
            apply(rule trans)
             apply(rule better_Cut_substn)
              apply(simp add: abs_fresh)
             apply(simp add: abs_fresh fresh_atm)
            apply(simp)
            apply(rule impI)
            apply(drule ax_psubst)
              apply(simp)
             apply(simp)
            apply(blast)
    (* NotR *)
           apply(simp)
           apply(case_tac "findc \<theta>_c coname")
            apply(simp)
            apply(auto simp add: fresh_list_cons fresh_prod)[1]
           apply(simp)
           apply(auto simp add: fresh_list_cons fresh_prod)[1]
           apply(generate_fresh "coname")
           apply(fresh_fun_simp)
           apply(fresh_fun_simp)
           apply(rule sym)
           apply(rule trans)
            apply(rule better_Cut_substn1)
              apply(simp add: cmaps_fresh)
             apply(simp)
            apply(simp)
           apply(simp)
    (* NotL *)
          apply(simp)
          apply(case_tac "findn \<theta>_n name")
           apply(simp)
           apply(auto simp add: fresh_list_cons fresh_prod)[1]
          apply(simp)
          apply(auto simp add: fresh_list_cons fresh_prod)[1]
           apply(drule nmaps_false)
            apply(simp)
           apply(simp)
          apply(generate_fresh "name")
          apply(fresh_fun_simp)
          apply(fresh_fun_simp)
          apply(rule sym)
          apply(rule trans)
           apply(rule better_Cut_substn2)
            apply(simp)
           apply(simp add: nmaps_fresh)
          apply(simp add: fresh_prod fresh_atm)
    (* AndR *)
         apply(simp)
         apply(case_tac "findc \<theta>_c coname3")
          apply(simp)
          apply(auto simp add: psubst_fresh_coname fresh_list_cons fresh_prod fresh_atm)[1]
         apply(simp)
         apply(auto simp add: fresh_list_cons fresh_prod)[1]
         apply(generate_fresh "coname")
         apply(fresh_fun_simp)
         apply(fresh_fun_simp)
         apply(rule sym)
         apply(rule trans)
          apply(rule better_Cut_substn1)
            apply(simp add: cmaps_fresh)
           apply(simp)
          apply(simp)
         apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* AndL1 *)
        apply(simp)
        apply(case_tac "findn \<theta>_n name2")
         apply(simp)
         apply(auto simp add: fresh_list_cons fresh_prod)[1]
        apply(simp)
        apply(auto simp add: fresh_list_cons fresh_prod)[1]
         apply(drule nmaps_false)
          apply(simp)
         apply(simp)
        apply(generate_fresh "name")
        apply(fresh_fun_simp)
        apply(fresh_fun_simp)
        apply(rule sym)
        apply(rule trans)
         apply(rule better_Cut_substn2)
          apply(simp)
         apply(simp add: nmaps_fresh)
        apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* AndL2 *)
       apply(simp)
       apply(case_tac "findn \<theta>_n name2")
        apply(simp)
        apply(auto simp add: fresh_list_cons fresh_prod)[1]
       apply(simp)
       apply(auto simp add: fresh_list_cons fresh_prod)[1]
        apply(drule nmaps_false)
         apply(simp)
        apply(simp)
       apply(generate_fresh "name")
       apply(fresh_fun_simp)
       apply(fresh_fun_simp)
       apply(rule sym)
       apply(rule trans)
        apply(rule better_Cut_substn2)
         apply(simp)
        apply(simp add: nmaps_fresh)
       apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* OrR1 *)
      apply(simp)
      apply(case_tac "findc \<theta>_c coname2")
       apply(simp)
       apply(auto simp add: psubst_fresh_coname fresh_list_cons fresh_prod fresh_atm)[1]
      apply(simp)
      apply(auto simp add: fresh_list_cons fresh_prod)[1]
      apply(generate_fresh "coname")
      apply(fresh_fun_simp)
      apply(fresh_fun_simp)
      apply(rule sym)
      apply(rule trans)
       apply(rule better_Cut_substn1)
         apply(simp add: cmaps_fresh)
        apply(simp)
       apply(simp)
      apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* OrR2 *)
     apply(simp)
     apply(case_tac "findc \<theta>_c coname2")
      apply(simp)
      apply(auto simp add: psubst_fresh_coname fresh_list_cons fresh_prod fresh_atm)[1]
     apply(simp)
     apply(auto simp add: fresh_list_cons fresh_prod)[1]
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(fresh_fun_simp)
     apply(rule sym)
     apply(rule trans)
      apply(rule better_Cut_substn1)
        apply(simp add: cmaps_fresh)
       apply(simp)
      apply(simp)
     apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* OrL *)
    apply(simp)
    apply(case_tac "findn \<theta>_n name3")
     apply(simp)
     apply(auto simp add: fresh_list_cons psubst_fresh_name fresh_atm fresh_prod)[1]
    apply(simp)
    apply(auto simp add: fresh_list_cons fresh_prod)[1]
     apply(drule nmaps_false)
      apply(simp)
     apply(simp)
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(rule sym)
    apply(rule trans)
     apply(rule better_Cut_substn2)
      apply(simp)
     apply(simp add: nmaps_fresh)
    apply(auto simp add:  psubst_fresh_name fresh_prod fresh_atm)[1]
    (* ImpR *)
   apply(simp)
   apply(case_tac "findc \<theta>_c coname2")
    apply(simp)
    apply(auto simp add: psubst_fresh_coname fresh_list_cons fresh_prod fresh_atm)[1]
   apply(simp)
   apply(auto simp add: fresh_list_cons fresh_prod)[1]
   apply(generate_fresh "coname")
   apply(fresh_fun_simp)
   apply(fresh_fun_simp)
   apply(rule sym)
   apply(rule trans)
    apply(rule better_Cut_substn1)
      apply(simp add: cmaps_fresh)
     apply(simp)
    apply(simp)
   apply(auto simp add:  psubst_fresh_coname fresh_prod fresh_atm)[1]
    (* ImpL *)
  apply(simp)
  apply(case_tac "findn \<theta>_n name2")
   apply(simp)
   apply(auto simp add: fresh_list_cons psubst_fresh_coname psubst_fresh_name fresh_atm fresh_prod)[1]
  apply(simp)
  apply(auto simp add: fresh_list_cons fresh_prod)[1]
   apply(drule nmaps_false)
    apply(simp)
   apply(simp)
  apply(generate_fresh "name")
  apply(fresh_fun_simp)
  apply(fresh_fun_simp)
  apply(rule sym)
  apply(rule trans)
   apply(rule better_Cut_substn2)
    apply(simp)
   apply(simp add: nmaps_fresh)
  apply(auto simp add: psubst_fresh_coname psubst_fresh_name fresh_prod fresh_atm)[1]
  done

definition 
  ncloses :: "(name\<times>coname\<times>trm) list\<Rightarrow>(name\<times>ty) list \<Rightarrow> bool" ("_ ncloses _" [55,55] 55) 
  where
    "\<theta>_n ncloses \<Gamma> \<equiv> \<forall>x B. ((x,B) \<in> set \<Gamma> \<longrightarrow> (\<exists>c P. \<theta>_n nmaps x to Some (c,P) \<and> <c>:P \<in> (\<parallel><B>\<parallel>)))"

definition 
  ccloses :: "(coname\<times>name\<times>trm) list\<Rightarrow>(coname\<times>ty) list \<Rightarrow> bool" ("_ ccloses _" [55,55] 55) 
  where
    "\<theta>_c ccloses \<Delta> \<equiv> \<forall>a B. ((a,B) \<in> set \<Delta> \<longrightarrow> (\<exists>x P. \<theta>_c cmaps a to Some (x,P) \<and> (x):P \<in> (\<parallel>(B)\<parallel>)))"

lemma ncloses_elim:
  assumes a: "(x,B) \<in> set \<Gamma>"
    and     b: "\<theta>_n ncloses \<Gamma>"
  shows "\<exists>c P. \<theta>_n nmaps x to Some (c,P) \<and> <c>:P \<in> (\<parallel><B>\<parallel>)"
  using a b by (auto simp add: ncloses_def)

lemma ccloses_elim:
  assumes a: "(a,B) \<in> set \<Delta>"
    and     b: "\<theta>_c ccloses \<Delta>"
  shows "\<exists>x P. \<theta>_c cmaps a to Some (x,P) \<and> (x):P \<in> (\<parallel>(B)\<parallel>)"
  using a b by (auto simp add: ccloses_def)

lemma ncloses_subset:
  assumes a: "\<theta>_n ncloses \<Gamma>"
    and     b: "set \<Gamma>' \<subseteq> set \<Gamma>"
  shows "\<theta>_n ncloses \<Gamma>'"
  using a b by (auto  simp add: ncloses_def)

lemma ccloses_subset:
  assumes a: "\<theta>_c ccloses \<Delta>"
    and     b: "set \<Delta>' \<subseteq> set \<Delta>"
  shows "\<theta>_c ccloses \<Delta>'"
  using a b by (auto  simp add: ccloses_def)

lemma validc_fresh:
  fixes a::"coname"
    and   \<Delta>::"(coname\<times>ty) list"
  assumes a: "a\<sharp>\<Delta>"
  shows "\<not>(\<exists>B. (a,B)\<in>set \<Delta>)"
  using a
  apply(induct \<Delta>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
  done

lemma validn_fresh:
  fixes x::"name"
    and   \<Gamma>::"(name\<times>ty) list"
  assumes a: "x\<sharp>\<Gamma>"
  shows "\<not>(\<exists>B. (x,B)\<in>set \<Gamma>)"
  using a
  apply(induct \<Gamma>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
  done

lemma ccloses_extend:
  assumes a: "\<theta>_c ccloses \<Delta>" "a\<sharp>\<Delta>" "a\<sharp>\<theta>_c" "(x):P\<in>\<parallel>(B)\<parallel>"
  shows "(a,x,P)#\<theta>_c ccloses (a,B)#\<Delta>"
  using a
  apply(simp add: ccloses_def)
  apply(drule validc_fresh)
  apply(auto)
  done

lemma ncloses_extend:
  assumes a: "\<theta>_n ncloses \<Gamma>" "x\<sharp>\<Gamma>" "x\<sharp>\<theta>_n" "<a>:P\<in>\<parallel><B>\<parallel>"
  shows "(x,a,P)#\<theta>_n ncloses (x,B)#\<Gamma>"
  using a
  apply(simp add: ncloses_def)
  apply(drule validn_fresh)
  apply(auto)
  done


text \<open>typing relation\<close>

inductive
  typing :: "ctxtn \<Rightarrow> trm \<Rightarrow> ctxtc \<Rightarrow> bool" ("_ \<turnstile> _ \<turnstile> _" [100,100,100] 100)
  where
    TAx:    "\<lbrakk>validn \<Gamma>;validc \<Delta>; (x,B)\<in>set \<Gamma>; (a,B)\<in>set \<Delta>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Ax x a \<turnstile> \<Delta>"
  | TNotR:  "\<lbrakk>x\<sharp>\<Gamma>; ((x,B)#\<Gamma>) \<turnstile> M \<turnstile> \<Delta>; set \<Delta>' = {(a,NOT B)}\<union>set \<Delta>; validc \<Delta>'\<rbrakk> 
           \<Longrightarrow> \<Gamma> \<turnstile> NotR (x).M a \<turnstile> \<Delta>'"
  | TNotL:  "\<lbrakk>a\<sharp>\<Delta>; \<Gamma> \<turnstile> M \<turnstile> ((a,B)#\<Delta>); set \<Gamma>' = {(x,NOT B)} \<union> set \<Gamma>; validn \<Gamma>'\<rbrakk>  
           \<Longrightarrow> \<Gamma>' \<turnstile> NotL <a>.M x \<turnstile> \<Delta>"
  | TAndL1: "\<lbrakk>x\<sharp>(\<Gamma>,y); ((x,B1)#\<Gamma>) \<turnstile> M \<turnstile> \<Delta>; set \<Gamma>' = {(y,B1 AND B2)} \<union> set \<Gamma>; validn \<Gamma>'\<rbrakk> 
           \<Longrightarrow> \<Gamma>' \<turnstile> AndL1 (x).M y \<turnstile> \<Delta>"
  | TAndL2: "\<lbrakk>x\<sharp>(\<Gamma>,y); ((x,B2)#\<Gamma>) \<turnstile> M \<turnstile> \<Delta>; set \<Gamma>' = {(y,B1 AND B2)} \<union> set \<Gamma>; validn \<Gamma>'\<rbrakk> 
           \<Longrightarrow> \<Gamma>' \<turnstile> AndL2 (x).M y \<turnstile> \<Delta>"
  | TAndR:  "\<lbrakk>a\<sharp>(\<Delta>,N,c); b\<sharp>(\<Delta>,M,c); a\<noteq>b; \<Gamma> \<turnstile> M \<turnstile> ((a,B)#\<Delta>); \<Gamma> \<turnstile> N \<turnstile> ((b,C)#\<Delta>); 
           set \<Delta>' = {(c,B AND C)}\<union>set \<Delta>; validc \<Delta>'\<rbrakk> 
           \<Longrightarrow> \<Gamma> \<turnstile> AndR <a>.M <b>.N c \<turnstile> \<Delta>'"
  | TOrL:   "\<lbrakk>x\<sharp>(\<Gamma>,N,z); y\<sharp>(\<Gamma>,M,z); x\<noteq>y; ((x,B)#\<Gamma>) \<turnstile> M \<turnstile> \<Delta>; ((y,C)#\<Gamma>) \<turnstile> N \<turnstile> \<Delta>;
           set \<Gamma>' = {(z,B OR C)} \<union> set \<Gamma>; validn \<Gamma>'\<rbrakk> 
           \<Longrightarrow> \<Gamma>' \<turnstile> OrL (x).M (y).N z \<turnstile> \<Delta>"
  | TOrR1:  "\<lbrakk>a\<sharp>(\<Delta>,b); \<Gamma> \<turnstile> M \<turnstile> ((a,B1)#\<Delta>); set \<Delta>' = {(b,B1 OR B2)}\<union>set \<Delta>; validc \<Delta>'\<rbrakk> 
           \<Longrightarrow> \<Gamma> \<turnstile> OrR1 <a>.M b \<turnstile> \<Delta>'"
  | TOrR2:  "\<lbrakk>a\<sharp>(\<Delta>,b); \<Gamma> \<turnstile> M \<turnstile> ((a,B2)#\<Delta>); set \<Delta>' = {(b,B1 OR B2)}\<union>set \<Delta>; validc \<Delta>'\<rbrakk> 
           \<Longrightarrow> \<Gamma> \<turnstile> OrR2 <a>.M b \<turnstile> \<Delta>'"
  | TImpL:  "\<lbrakk>a\<sharp>(\<Delta>,N); x\<sharp>(\<Gamma>,M,y); \<Gamma> \<turnstile> M \<turnstile> ((a,B)#\<Delta>); ((x,C)#\<Gamma>) \<turnstile> N \<turnstile> \<Delta>;
           set \<Gamma>' = {(y,B IMP C)} \<union> set \<Gamma>; validn \<Gamma>'\<rbrakk> 
           \<Longrightarrow> \<Gamma>' \<turnstile> ImpL <a>.M (x).N y \<turnstile> \<Delta>"
  | TImpR:  "\<lbrakk>a\<sharp>(\<Delta>,b); x\<sharp>\<Gamma>; ((x,B)#\<Gamma>) \<turnstile> M \<turnstile> ((a,C)#\<Delta>); set \<Delta>' = {(b,B IMP C)}\<union>set \<Delta>; validc \<Delta>'\<rbrakk> 
           \<Longrightarrow> \<Gamma> \<turnstile> ImpR (x).<a>.M b \<turnstile> \<Delta>'"
  | TCut:   "\<lbrakk>a\<sharp>(\<Delta>,N); x\<sharp>(\<Gamma>,M); \<Gamma> \<turnstile> M \<turnstile> ((a,B)#\<Delta>); ((x,B)#\<Gamma>) \<turnstile> N \<turnstile> \<Delta>\<rbrakk> 
           \<Longrightarrow> \<Gamma> \<turnstile> Cut <a>.M (x).N \<turnstile> \<Delta>"

equivariance typing

lemma fresh_set_member:
  fixes x::"name"
    and   a::"coname"
  shows "x\<sharp>L \<Longrightarrow> e\<in>set L \<Longrightarrow> x\<sharp>e"
    and   "a\<sharp>L \<Longrightarrow> e\<in>set L \<Longrightarrow> a\<sharp>e"   
  by (induct L) (auto simp add: fresh_list_cons) 

lemma fresh_subset:
  fixes x::"name"
    and   a::"coname"
  shows "x\<sharp>L \<Longrightarrow> set L' \<subseteq> set L \<Longrightarrow> x\<sharp>L'"
    and   "a\<sharp>L \<Longrightarrow> set L' \<subseteq> set L \<Longrightarrow> a\<sharp>L'"   
   apply(induct L' arbitrary: L) 
     apply(auto simp add: fresh_list_cons fresh_list_nil intro: fresh_set_member)
  done

lemma fresh_subset_ext:
  fixes x::"name"
    and   a::"coname"
  shows "x\<sharp>L \<Longrightarrow> x\<sharp>e \<Longrightarrow> set L' \<subseteq> set (e#L) \<Longrightarrow> x\<sharp>L'"
    and   "a\<sharp>L \<Longrightarrow> a\<sharp>e \<Longrightarrow> set L' \<subseteq> set (e#L) \<Longrightarrow> a\<sharp>L'"   
   apply(induct L' arbitrary: L) 
     apply(auto simp add: fresh_list_cons fresh_list_nil intro: fresh_set_member)
  done

lemma fresh_under_insert:
  fixes x::"name"
    and   a::"coname"
    and   \<Gamma>::"ctxtn"
    and   \<Delta>::"ctxtc"
  shows "x\<sharp>\<Gamma> \<Longrightarrow> x\<noteq>y \<Longrightarrow> set \<Gamma>' = insert (y,B) (set \<Gamma>) \<Longrightarrow> x\<sharp>\<Gamma>'"
    and   "a\<sharp>\<Delta> \<Longrightarrow> a\<noteq>c \<Longrightarrow> set \<Delta>' = insert (c,B) (set \<Delta>) \<Longrightarrow> a\<sharp>\<Delta>'"   
   apply(rule fresh_subset_ext(1))
     apply(auto simp add: fresh_prod fresh_atm fresh_ty)
  apply(rule fresh_subset_ext(2))
    apply(auto simp add: fresh_prod fresh_atm fresh_ty)
  done

nominal_inductive typing
                       apply (simp_all add: abs_fresh fresh_atm fresh_list_cons fresh_prod fresh_ty fresh_ctxt 
      fresh_list_append abs_supp fin_supp)
           apply(auto intro: fresh_under_insert)
  done

lemma validn_elim:
  assumes a: "validn ((x,B)#\<Gamma>)"
  shows "validn \<Gamma> \<and> x\<sharp>\<Gamma>"
  using a
  apply(erule_tac validn.cases)
   apply(auto)
  done

lemma validc_elim:
  assumes a: "validc ((a,B)#\<Delta>)"
  shows "validc \<Delta> \<and> a\<sharp>\<Delta>"
  using a
  apply(erule_tac validc.cases)
   apply(auto)
  done

lemma context_fresh:
  fixes x::"name"
    and   a::"coname"
  shows "x\<sharp>\<Gamma> \<Longrightarrow> \<not>(\<exists>B. (x,B)\<in>set \<Gamma>)"
    and   "a\<sharp>\<Delta> \<Longrightarrow> \<not>(\<exists>B. (a,B)\<in>set \<Delta>)"
   apply -
   apply(induct \<Gamma>)
    apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
  apply(induct \<Delta>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
  done

lemma typing_implies_valid:
  assumes a: "\<Gamma> \<turnstile> M \<turnstile> \<Delta>"
  shows "validn \<Gamma> \<and> validc \<Delta>"
  using a
  apply(nominal_induct rule: typing.strong_induct)
             apply(auto dest: validn_elim validc_elim)
  done

lemma ty_perm:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
    and   B::"ty"
  shows "pi1\<bullet>B=B" and "pi2\<bullet>B=B"
   apply(nominal_induct B rule: ty.strong_induct)
           apply(auto simp add: perm_string)
  done

lemma ctxt_perm:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
    and   \<Gamma>::"ctxtn"
    and   \<Delta>::"ctxtc"
  shows "pi2\<bullet>\<Gamma>=\<Gamma>" and "pi1\<bullet>\<Delta>=\<Delta>"
   apply -
   apply(induct \<Gamma>)
    apply(auto simp add: calc_atm ty_perm)
  apply(induct \<Delta>)
   apply(auto simp add: calc_atm ty_perm)
  done

lemma typing_Ax_elim1: 
  assumes a: "\<Gamma> \<turnstile> Ax x a \<turnstile> ((a,B)#\<Delta>)"
  shows "(x,B)\<in>set \<Gamma>"
  using a
  apply(erule_tac typing.cases)
             apply(simp_all add: trm.inject)
  apply(auto)
  apply(auto dest: validc_elim context_fresh)
  done

lemma typing_Ax_elim2: 
  assumes a: "((x,B)#\<Gamma>) \<turnstile> Ax x a \<turnstile> \<Delta>"
  shows "(a,B)\<in>set \<Delta>"
  using a
  apply(erule_tac typing.cases)
             apply(simp_all add: trm.inject)
  apply(auto  dest!: validn_elim context_fresh)
  done

lemma psubst_Ax_aux: 
  assumes a: "\<theta>_c cmaps a to Some (y,N)"
  shows "lookupb x a \<theta>_c c P = Cut <c>.P (y).N"
  using a
  apply(induct \<theta>_c)
   apply(auto)
  done

lemma psubst_Ax:
  assumes a: "\<theta>_n nmaps x to Some (c,P)"
    and     b: "\<theta>_c cmaps a to Some (y,N)"
  shows "\<theta>_n,\<theta>_c<Ax x a> = Cut <c>.P (y).N"
  using a b
  apply(induct \<theta>_n)
   apply(auto simp add: psubst_Ax_aux)
  done

lemma psubst_Cut:
  assumes a: "\<forall>x. M\<noteq>Ax x c"
    and     b: "\<forall>a. N\<noteq>Ax x a"
    and     c: "c\<sharp>(\<theta>_n,\<theta>_c,N)" "x\<sharp>(\<theta>_n,\<theta>_c,M)"
  shows "\<theta>_n,\<theta>_c<Cut <c>.M (x).N> = Cut <c>.(\<theta>_n,\<theta>_c<M>) (x).(\<theta>_n,\<theta>_c<N>)"
  using a b c
  apply(simp)
  done

lemma all_CAND: 
  assumes a: "\<Gamma> \<turnstile> M \<turnstile> \<Delta>"
    and     b: "\<theta>_n ncloses \<Gamma>"
    and     c: "\<theta>_c ccloses \<Delta>"
  shows "SNa (\<theta>_n,\<theta>_c<M>)"
  using a b c
proof(nominal_induct avoiding: \<theta>_n \<theta>_c rule: typing.strong_induct)
  case (TAx \<Gamma> \<Delta> x B a \<theta>_n \<theta>_c)
  then show ?case
    apply -
    apply(drule ncloses_elim)
     apply(assumption)
    apply(drule ccloses_elim)
     apply(assumption)
    apply(erule exE)+
    apply(erule conjE)+
    apply(rule_tac s="Cut <c>.P (xa).Pa" and t="\<theta>_n,\<theta>_c<Ax x a>" in subst)
     apply(rule sym)
     apply(simp only: psubst_Ax)
    apply(simp add: CUT_SNa)
    done
next
  case (TNotR x \<Gamma> B M \<Delta> \<Delta>' a \<theta>_n \<theta>_c) 
  then show ?case 
    apply(simp)
    apply(subgoal_tac "(a,NOT B) \<in> set \<Delta>'")
     apply(drule ccloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(simp)
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(rule_tac B="NOT B" in CUT_SNa)
      apply(simp)
      apply(rule disjI2)
      apply(rule disjI2)
      apply(rule_tac x="c" in exI)
      apply(rule_tac x="x" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp)
      apply(rule conjI)
       apply(rule fic.intros)
       apply(rule psubst_fresh_coname)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGn_def)
      apply(simp)
      apply(rule_tac x="x" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp)
      apply(rule allI)+
      apply(rule impI)
      apply(simp add: psubst_nsubst[symmetric])
      apply(drule_tac x="(x,aa,Pa)#\<theta>_n" in meta_spec)
      apply(drule_tac x="\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(rule ncloses_extend)
          apply(assumption)
         apply(assumption)
        apply(assumption)
       apply(assumption)
      apply(drule meta_mp)
       apply(rule ccloses_subset)
        apply(assumption)
       apply(blast)
      apply(assumption)
     apply(simp)
    apply(blast)
    done
next
  case (TNotL a \<Delta> \<Gamma> M B \<Gamma>' x \<theta>_n \<theta>_c)
  then show ?case
    apply(simp)
    apply(subgoal_tac "(x,NOT B) \<in> set \<Gamma>'")
     apply(drule ncloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(simp del: NEGc.simps)
     apply(generate_fresh "name")
     apply(fresh_fun_simp)
     apply(rule_tac B="NOT B" in CUT_SNa)
      apply(simp)
     apply(rule NEG_intro)
     apply(simp (no_asm))
     apply(rule disjI2)
     apply(rule disjI2)
     apply(rule_tac x="a" in exI)
     apply(rule_tac x="ca" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
     apply(simp del: NEGc.simps)
     apply(rule conjI)
      apply(rule fin.intros)
      apply(rule psubst_fresh_name)
        apply(simp)
       apply(simp)
      apply(simp)
     apply(rule BINDING_implies_CAND)
     apply(unfold BINDINGc_def)
     apply(simp (no_asm))
     apply(rule_tac x="a" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
     apply(simp (no_asm))
     apply(rule allI)+
     apply(rule impI)
     apply(simp del: NEGc.simps add: psubst_csubst[symmetric])
     apply(drule_tac x="\<theta>_n" in meta_spec)
     apply(drule_tac x="(a,xa,Pa)#\<theta>_c" in meta_spec)
     apply(drule meta_mp)
      apply(rule ncloses_subset)
       apply(assumption)
      apply(blast)
     apply(drule meta_mp)
      apply(rule ccloses_extend)
         apply(assumption)
        apply(assumption)
       apply(assumption)
      apply(assumption)
     apply(assumption)
    apply(blast)
    done
next
  case (TAndL1 x \<Gamma> y B1 M \<Delta> \<Gamma>' B2 \<theta>_n \<theta>_c)
  then show ?case     
    apply(simp)
    apply(subgoal_tac "(y,B1 AND B2) \<in> set \<Gamma>'")
     apply(drule ncloses_elim)
      apply(assumption)
     apply(erule exE)+ 
     apply(simp del: NEGc.simps)
     apply(generate_fresh "name")
     apply(fresh_fun_simp)
     apply(rule_tac B="B1 AND B2" in CUT_SNa)
      apply(simp)
     apply(rule NEG_intro)
     apply(simp (no_asm))
     apply(rule disjI2)
     apply(rule disjI2)
     apply(rule disjI1)
     apply(rule_tac x="x" in exI)
     apply(rule_tac x="ca" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
     apply(simp del: NEGc.simps)
     apply(rule conjI)
      apply(rule fin.intros)
      apply(simp del: NEGc.simps add: abs_fresh fresh_prod fresh_atm)
      apply(rule psubst_fresh_name)
        apply(simp)
       apply(simp)
      apply(simp)
     apply(rule BINDING_implies_CAND)
     apply(unfold BINDINGn_def)
     apply(simp (no_asm))
     apply(rule_tac x="x" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
     apply(simp (no_asm))
     apply(rule allI)+
     apply(rule impI)
     apply(simp del: NEGc.simps add: psubst_nsubst[symmetric])
     apply(drule_tac x="(x,a,Pa)#\<theta>_n" in meta_spec)
     apply(drule_tac x="\<theta>_c" in meta_spec)
     apply(drule meta_mp)
      apply(rule ncloses_extend)
         apply(rule ncloses_subset)
          apply(assumption)
         apply(blast)
        apply(simp)
       apply(simp)
      apply(simp)
     apply(drule meta_mp)
      apply(assumption)
     apply(assumption)
    apply(blast)
    done
next
  case (TAndL2 x \<Gamma> y B2 M \<Delta> \<Gamma>' B1 \<theta>_n \<theta>_c)
  then show ?case 
    apply(simp)
    apply(subgoal_tac "(y,B1 AND B2) \<in> set \<Gamma>'")
     apply(drule ncloses_elim)
      apply(assumption)
     apply(erule exE)+ 
     apply(simp del: NEGc.simps)
     apply(generate_fresh "name")
     apply(fresh_fun_simp)
     apply(rule_tac B="B1 AND B2" in CUT_SNa)
      apply(simp)
     apply(rule NEG_intro)
     apply(simp (no_asm))
     apply(rule disjI2)
     apply(rule disjI2)
     apply(rule disjI2)
     apply(rule_tac x="x" in exI)
     apply(rule_tac x="ca" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
     apply(simp del: NEGc.simps)
     apply(rule conjI)
      apply(rule fin.intros)
      apply(simp del: NEGc.simps add: abs_fresh fresh_prod fresh_atm)
      apply(rule psubst_fresh_name)
        apply(simp)
       apply(simp)
      apply(simp)
     apply(rule BINDING_implies_CAND)
     apply(unfold BINDINGn_def)
     apply(simp (no_asm))
     apply(rule_tac x="x" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
     apply(simp (no_asm))
     apply(rule allI)+
     apply(rule impI)
     apply(simp del: NEGc.simps add: psubst_nsubst[symmetric])
     apply(drule_tac x="(x,a,Pa)#\<theta>_n" in meta_spec)
     apply(drule_tac x="\<theta>_c" in meta_spec)
     apply(drule meta_mp)
      apply(rule ncloses_extend)
         apply(rule ncloses_subset)
          apply(assumption)
         apply(blast)
        apply(simp)
       apply(simp)
      apply(simp)
     apply(drule meta_mp)
      apply(assumption)
     apply(assumption)
    apply(blast)
    done
next
  case (TAndR a \<Delta> N c b M \<Gamma> B C \<Delta>' \<theta>_n \<theta>_c)
  then show ?case 
    apply(simp)
    apply(subgoal_tac "(c,B AND C) \<in> set \<Delta>'")
     apply(drule ccloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(simp)
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(rule_tac B="B AND C" in CUT_SNa)
      apply(simp)
      apply(rule disjI2)
      apply(rule disjI2)
      apply(rule_tac x="ca" in exI)
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="b" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<N>" in exI)
      apply(simp)
      apply(rule conjI)
       apply(rule fic.intros)
        apply(simp add: abs_fresh fresh_prod fresh_atm)
        apply(rule psubst_fresh_coname)
          apply(simp)
         apply(simp)
        apply(simp)
       apply(simp add: abs_fresh fresh_prod fresh_atm)
       apply(rule psubst_fresh_coname)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(rule conjI)
       apply(rule BINDING_implies_CAND)
       apply(unfold BINDINGc_def)
       apply(simp)
       apply(rule_tac x="a" in exI)
       apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
       apply(simp)
       apply(rule allI)+
       apply(rule impI)
       apply(simp add: psubst_csubst[symmetric])
       apply(drule_tac x="\<theta>_n" in meta_spec)
       apply(drule_tac x="(a,xa,Pa)#\<theta>_c" in meta_spec)
       apply(drule meta_mp)
        apply(assumption)
       apply(drule meta_mp)
        apply(rule ccloses_extend)
           apply(rule ccloses_subset)
            apply(assumption)
           apply(blast)
          apply(simp)
         apply(simp)
        apply(assumption)
       apply(assumption)
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGc_def)
      apply(simp)
      apply(rule_tac x="b" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<N>" in exI)
      apply(simp)
      apply(rule allI)+
      apply(rule impI)
      apply(simp add: psubst_csubst[symmetric])
      apply(rotate_tac 14)
      apply(drule_tac x="\<theta>_n" in meta_spec)
      apply(drule_tac x="(b,xa,Pa)#\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(assumption)
      apply(drule meta_mp)
       apply(rule ccloses_extend)
          apply(rule ccloses_subset)
           apply(assumption)
          apply(blast)
         apply(simp)
        apply(simp)
       apply(assumption)
      apply(assumption)
     apply(simp)
    apply(blast)
    done
next
  case (TOrL x \<Gamma> N z y M B \<Delta> C \<Gamma>' \<theta>_n \<theta>_c)
  then show ?case 
    apply(simp)
    apply(subgoal_tac "(z,B OR C) \<in> set \<Gamma>'")
     apply(drule ncloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(simp del: NEGc.simps)
     apply(generate_fresh "name")
     apply(fresh_fun_simp)
     apply(rule_tac B="B OR C" in CUT_SNa)
      apply(simp)
     apply(rule NEG_intro)
     apply(simp (no_asm))
     apply(rule disjI2)
     apply(rule disjI2)
     apply(rule_tac x="x" in exI)
     apply(rule_tac x="y" in exI)
     apply(rule_tac x="ca" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<N>" in exI)
     apply(simp del: NEGc.simps)
     apply(rule conjI)
      apply(rule fin.intros)
       apply(simp del: NEGc.simps add: abs_fresh fresh_prod fresh_atm)
       apply(rule psubst_fresh_name)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(simp del: NEGc.simps add: abs_fresh fresh_prod fresh_atm)
      apply(rule psubst_fresh_name)
        apply(simp)
       apply(simp)
      apply(simp)
     apply(rule conjI)
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGn_def)
      apply(simp del: NEGc.simps)
      apply(rule_tac x="x" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp del: NEGc.simps)
      apply(rule allI)+
      apply(rule impI)
      apply(simp del: NEGc.simps add: psubst_nsubst[symmetric])
      apply(drule_tac x="(x,a,Pa)#\<theta>_n" in meta_spec)
      apply(drule_tac x="\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(rule ncloses_extend)
          apply(rule ncloses_subset)
           apply(assumption)
          apply(blast)
         apply(simp)
        apply(simp)
       apply(assumption)
      apply(drule meta_mp)
       apply(assumption)
      apply(assumption)
     apply(rule BINDING_implies_CAND)
     apply(unfold BINDINGn_def)
     apply(simp del: NEGc.simps)
     apply(rule_tac x="y" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<N>" in exI)
     apply(simp del: NEGc.simps)
     apply(rule allI)+
     apply(rule impI)
     apply(simp del: NEGc.simps add: psubst_nsubst[symmetric])
     apply(rotate_tac 14)
     apply(drule_tac x="(y,a,Pa)#\<theta>_n" in meta_spec)
     apply(drule_tac x="\<theta>_c" in meta_spec)
     apply(drule meta_mp)
      apply(rule ncloses_extend)
         apply(rule ncloses_subset)
          apply(assumption)
         apply(blast)
        apply(simp)
       apply(simp)
      apply(assumption)
     apply(drule meta_mp)
      apply(assumption)
     apply(assumption)
    apply(blast)
    done
next
  case (TOrR1 a \<Delta> b \<Gamma> M B1 \<Delta>' B2 \<theta>_n \<theta>_c)
  then show ?case
    apply(simp)
    apply(subgoal_tac "(b,B1 OR B2) \<in> set \<Delta>'")
     apply(drule ccloses_elim)
      apply(assumption)
     apply(erule exE)+ 
     apply(simp del: NEGc.simps)
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(rule_tac B="B1 OR B2" in CUT_SNa)
      apply(simp)
      apply(rule disjI2)
      apply(rule disjI2)
      apply(rule disjI1)
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="c" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp)
      apply(rule conjI)
       apply(rule fic.intros)
       apply(simp del: NEGc.simps add: abs_fresh fresh_prod fresh_atm)
       apply(rule psubst_fresh_coname)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGc_def)
      apply(simp (no_asm))
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp (no_asm))
      apply(rule allI)+
      apply(rule impI)    
      apply(simp del: NEGc.simps add: psubst_csubst[symmetric])
      apply(drule_tac x="\<theta>_n" in meta_spec)
      apply(drule_tac x="(a,xa,Pa)#\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(assumption)
      apply(drule meta_mp)
       apply(rule ccloses_extend)
          apply(rule ccloses_subset)
           apply(assumption)
          apply(blast)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(assumption)
     apply(simp)
    apply(blast)
    done
next
  case (TOrR2 a \<Delta> b \<Gamma> M B2 \<Delta>' B1 \<theta>_n \<theta>_c)
  then show ?case 
    apply(simp)
    apply(subgoal_tac "(b,B1 OR B2) \<in> set \<Delta>'")
     apply(drule ccloses_elim)
      apply(assumption)
     apply(erule exE)+ 
     apply(simp del: NEGc.simps)
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(rule_tac B="B1 OR B2" in CUT_SNa)
      apply(simp)
      apply(rule disjI2)
      apply(rule disjI2)
      apply(rule disjI2)
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="c" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp)
      apply(rule conjI)
       apply(rule fic.intros)
       apply(simp del: NEGc.simps add: abs_fresh fresh_prod fresh_atm)
       apply(rule psubst_fresh_coname)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGc_def)
      apply(simp (no_asm))
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp (no_asm))
      apply(rule allI)+
      apply(rule impI)    
      apply(simp del: NEGc.simps add: psubst_csubst[symmetric])
      apply(drule_tac x="\<theta>_n" in meta_spec)
      apply(drule_tac x="(a,xa,Pa)#\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(assumption)
      apply(drule meta_mp)
       apply(rule ccloses_extend)
          apply(rule ccloses_subset)
           apply(assumption)
          apply(blast)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(assumption)
     apply(simp)
    apply(blast)
    done
next
  case (TImpL a \<Delta> N x \<Gamma> M y B C \<Gamma>' \<theta>_n \<theta>_c)
  then show ?case
    apply(simp)
    apply(subgoal_tac "(y,B IMP C) \<in> set \<Gamma>'")
     apply(drule ncloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(simp del: NEGc.simps)
     apply(generate_fresh "name")
     apply(fresh_fun_simp)
     apply(rule_tac B="B IMP C" in CUT_SNa)
      apply(simp)
     apply(rule NEG_intro)
     apply(simp (no_asm))
     apply(rule disjI2)
     apply(rule disjI2)
     apply(rule_tac x="x" in exI)
     apply(rule_tac x="a" in exI)
     apply(rule_tac x="ca" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<N>" in exI)
     apply(simp del: NEGc.simps)
     apply(rule conjI)
      apply(rule fin.intros)
       apply(rule psubst_fresh_name)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(simp del: NEGc.simps add: abs_fresh fresh_prod fresh_atm)
      apply(rule psubst_fresh_name)
        apply(simp)
       apply(simp)
      apply(simp)
     apply(rule conjI)
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGc_def)
      apply(simp del: NEGc.simps)
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp del: NEGc.simps)
      apply(rule allI)+
      apply(rule impI)
      apply(simp del: NEGc.simps add: psubst_csubst[symmetric])
      apply(drule_tac x="\<theta>_n" in meta_spec)
      apply(drule_tac x="(a,xa,Pa)#\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(rule ncloses_subset)
        apply(assumption)
       apply(blast)
      apply(drule meta_mp)
       apply(rule ccloses_extend)
          apply(assumption)
         apply(simp)
        apply(simp)
       apply(assumption)
      apply(assumption)
     apply(rule BINDING_implies_CAND)
     apply(unfold BINDINGn_def)
     apply(simp del: NEGc.simps)
     apply(rule_tac x="x" in exI)
     apply(rule_tac x="\<theta>_n,\<theta>_c<N>" in exI)
     apply(simp del: NEGc.simps)
     apply(rule allI)+
     apply(rule impI)
     apply(simp del: NEGc.simps add: psubst_nsubst[symmetric])
     apply(rotate_tac 12)
     apply(drule_tac x="(x,aa,Pa)#\<theta>_n" in meta_spec)
     apply(drule_tac x="\<theta>_c" in meta_spec)
     apply(drule meta_mp)
      apply(rule ncloses_extend)
         apply(rule ncloses_subset)
          apply(assumption)
         apply(blast)
        apply(simp)
       apply(simp)
      apply(assumption)
     apply(drule meta_mp)
      apply(assumption)
     apply(assumption)
    apply(blast)
    done
next
  case (TImpR a \<Delta> b x \<Gamma> B M C \<Delta>' \<theta>_n \<theta>_c)
  then show ?case
    apply(simp)
    apply(subgoal_tac "(b,B IMP C) \<in> set \<Delta>'")
     apply(drule ccloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(simp)
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(rule_tac B="B IMP C" in CUT_SNa)
      apply(simp)
      apply(rule disjI2)
      apply(rule disjI2)
      apply(rule_tac x="x" in exI)
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="c" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp)
      apply(rule conjI)
       apply(rule fic.intros)
       apply(simp add: abs_fresh fresh_prod fresh_atm)
       apply(rule psubst_fresh_coname)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(rule conjI)
       apply(rule allI)+
       apply(rule impI)
       apply(simp add: psubst_csubst[symmetric])
       apply(rule BINDING_implies_CAND)
       apply(unfold BINDINGn_def)
       apply(simp)
       apply(rule_tac x="x" in exI)
       apply(rule_tac x="\<theta>_n,((a,z,Pa)#\<theta>_c)<M>" in exI)
       apply(simp)
       apply(rule allI)+
       apply(rule impI)
       apply(rule_tac t="\<theta>_n,((a,z,Pa)#\<theta>_c)<M>{x:=<aa>.Pb}" and 
        s="((x,aa,Pb)#\<theta>_n),((a,z,Pa)#\<theta>_c)<M>" in subst)
        apply(rule psubst_nsubst)
        apply(simp add: fresh_prod fresh_atm fresh_list_cons)
       apply(drule_tac x="(x,aa,Pb)#\<theta>_n" in meta_spec)
       apply(drule_tac x="(a,z,Pa)#\<theta>_c" in meta_spec)
       apply(drule meta_mp)
        apply(rule ncloses_extend)
           apply(assumption)
          apply(simp)
         apply(simp)
        apply(simp)
       apply(drule meta_mp)
        apply(rule ccloses_extend)
           apply(rule ccloses_subset)
            apply(assumption)
           apply(blast)
          apply(auto intro: fresh_subset simp del: NEGc.simps)[1]
         apply(simp)
        apply(simp)
       apply(assumption)
      apply(rule allI)+
      apply(rule impI)
      apply(simp add: psubst_nsubst[symmetric])
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGc_def)
      apply(simp)
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="((x,ca,Q)#\<theta>_n),\<theta>_c<M>" in exI)
      apply(simp)
      apply(rule allI)+
      apply(rule impI)
      apply(rule_tac t="((x,ca,Q)#\<theta>_n),\<theta>_c<M>{a:=(xaa).Pa}" and 
        s="((x,ca,Q)#\<theta>_n),((a,xaa,Pa)#\<theta>_c)<M>" in subst)
       apply(rule psubst_csubst)
       apply(simp add: fresh_prod fresh_atm fresh_list_cons)
      apply(drule_tac x="(x,ca,Q)#\<theta>_n" in meta_spec)
      apply(drule_tac x="(a,xaa,Pa)#\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(rule ncloses_extend)
          apply(assumption)
         apply(simp)
        apply(simp)
       apply(simp)
      apply(drule meta_mp)
       apply(rule ccloses_extend)
          apply(rule ccloses_subset)
           apply(assumption)
          apply(blast)
         apply(auto intro: fresh_subset simp del: NEGc.simps)[1]
        apply(simp)
       apply(simp)
      apply(assumption)
     apply(simp)
    apply(blast)
    done
next
  case (TCut a \<Delta> N x \<Gamma> M B \<theta>_n \<theta>_c)
  then show ?case 
    apply -
    apply(case_tac "\<forall>y. M\<noteq>Ax y a")
     apply(case_tac "\<forall>c. N\<noteq>Ax x c")
      apply(simp)
      apply(rule_tac B="B" in CUT_SNa)
       apply(rule BINDING_implies_CAND)
       apply(unfold BINDINGc_def)
       apply(simp)
       apply(rule_tac x="a" in exI)
       apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
       apply(simp)
       apply(rule allI)
       apply(rule allI)
       apply(rule impI)
       apply(simp add: psubst_csubst[symmetric]) (*?*)
       apply(drule_tac x="\<theta>_n" in meta_spec)
       apply(drule_tac x="(a,xa,P)#\<theta>_c" in meta_spec)
       apply(drule meta_mp)
        apply(assumption)
       apply(drule meta_mp)
        apply(rule ccloses_extend) 
           apply(assumption)
          apply(assumption)
         apply(assumption)
        apply(assumption)
       apply(assumption)
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGn_def)
      apply(simp)
      apply(rule_tac x="x" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<N>" in exI)
      apply(simp)
      apply(rule allI)
      apply(rule allI)
      apply(rule impI)
      apply(simp add: psubst_nsubst[symmetric]) (*?*)
      apply(rotate_tac 11)
      apply(drule_tac x="(x,aa,P)#\<theta>_n" in meta_spec)
      apply(drule_tac x="\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(rule ncloses_extend)
          apply(assumption)
         apply(assumption)
        apply(assumption)
       apply(assumption)
      apply(drule_tac meta_mp)
       apply(assumption)
      apply(assumption)
      (* cases at least one axiom *)
     apply(simp (no_asm_use))
     apply(erule exE)
     apply(simp del: psubst.simps)
     apply(drule typing_Ax_elim2)
     apply(auto simp add: trm.inject)[1]
     apply(rule_tac B="B" in CUT_SNa)
      (* left term *)
      apply(rule BINDING_implies_CAND)
      apply(unfold BINDINGc_def)
      apply(simp)
      apply(rule_tac x="a" in exI)
      apply(rule_tac x="\<theta>_n,\<theta>_c<M>" in exI)
      apply(simp)
      apply(rule allI)+
      apply(rule impI)
      apply(drule_tac x="\<theta>_n" in meta_spec)
      apply(drule_tac x="(a,xa,P)#\<theta>_c" in meta_spec)
      apply(drule meta_mp)
       apply(assumption)
      apply(drule meta_mp)
       apply(rule ccloses_extend) 
          apply(assumption)
         apply(assumption)
        apply(assumption)
       apply(assumption)
      apply(simp add: psubst_csubst[symmetric]) (*?*)
      (* right term -axiom *)
     apply(drule ccloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(erule conjE)
     apply(frule_tac y="x" in lookupd_cmaps)
     apply(drule cmaps_fresh)
      apply(assumption)
     apply(simp)
     apply(subgoal_tac "(x):P[xa\<turnstile>n>x] = (xa):P")
      apply(simp)
     apply(simp add: ntrm.inject)
     apply(simp add: alpha fresh_prod fresh_atm)
     apply(rule sym)
     apply(rule nrename_swap)
     apply(simp)
      (* M is axiom *)
    apply(simp)
    apply(auto)[1]
      (* both are axioms *)
     apply(rule_tac B="B" in CUT_SNa)
      apply(drule typing_Ax_elim1)
      apply(drule ncloses_elim)
       apply(assumption)
      apply(erule exE)+
      apply(erule conjE)
      apply(frule_tac a="a" in lookupc_nmaps)
      apply(drule_tac a="a" in nmaps_fresh)
       apply(assumption)
      apply(simp)
      apply(subgoal_tac "<a>:P[c\<turnstile>c>a] = <c>:P")
       apply(simp)
      apply(simp add: ctrm.inject)
      apply(simp add: alpha fresh_prod fresh_atm)
      apply(rule sym)
      apply(rule crename_swap)
      apply(simp)
     apply(drule typing_Ax_elim2)
     apply(drule ccloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(erule conjE)
     apply(frule_tac y="x" in lookupd_cmaps)
     apply(drule cmaps_fresh)
      apply(assumption)
     apply(simp)
     apply(subgoal_tac "(x):P[xa\<turnstile>n>x] = (xa):P")
      apply(simp)
     apply(simp add: ntrm.inject)
     apply(simp add: alpha fresh_prod fresh_atm)
     apply(rule sym)
     apply(rule nrename_swap)
     apply(simp)
      (* N is not axioms *)
    apply(rule_tac B="B" in CUT_SNa)
      (* left term *)
     apply(drule typing_Ax_elim1)
     apply(drule ncloses_elim)
      apply(assumption)
     apply(erule exE)+
     apply(erule conjE)
     apply(frule_tac a="a" in lookupc_nmaps)
     apply(drule_tac a="a" in nmaps_fresh)
      apply(assumption)
     apply(simp)
     apply(subgoal_tac "<a>:P[c\<turnstile>c>a] = <c>:P")
      apply(simp)
     apply(simp add: ctrm.inject)
     apply(simp add: alpha fresh_prod fresh_atm)
     apply(rule sym)
     apply(rule crename_swap)
     apply(simp)
    apply(rule BINDING_implies_CAND)
    apply(unfold BINDINGn_def)
    apply(simp)
    apply(rule_tac x="x" in exI)
    apply(rule_tac x="\<theta>_n,\<theta>_c<N>" in exI)
    apply(simp)
    apply(rule allI)
    apply(rule allI)
    apply(rule impI)
    apply(simp add: psubst_nsubst[symmetric]) (*?*)
    apply(rotate_tac 10)
    apply(drule_tac x="(x,aa,P)#\<theta>_n" in meta_spec)
    apply(drule_tac x="\<theta>_c" in meta_spec)
    apply(drule meta_mp)
     apply(rule ncloses_extend)
        apply(assumption)
       apply(assumption)
      apply(assumption)
     apply(assumption)
    apply(drule_tac meta_mp)
     apply(assumption)
    apply(assumption)
    done
qed

primrec "idn" :: "(name\<times>ty) list\<Rightarrow>coname\<Rightarrow>(name\<times>coname\<times>trm) list" where
  "idn [] a   = []"
| "idn (p#\<Gamma>) a = ((fst p),a,Ax (fst p) a)#(idn \<Gamma> a)"

primrec "idc" :: "(coname\<times>ty) list\<Rightarrow>name\<Rightarrow>(coname\<times>name\<times>trm) list" where
  "idc [] x    = []"
| "idc (p#\<Delta>) x = ((fst p),x,Ax x (fst p))#(idc \<Delta> x)"

lemma idn_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(idn \<Gamma> a)) = idn (pi1\<bullet>\<Gamma>) (pi1\<bullet>a)"
    and   "(pi2\<bullet>(idn \<Gamma> a)) = idn (pi2\<bullet>\<Gamma>) (pi2\<bullet>a)"
   apply(induct \<Gamma>)
     apply(auto)
  done

lemma idc_eqvt[eqvt]:
  fixes pi1::"name prm"
    and   pi2::"coname prm"
  shows "(pi1\<bullet>(idc \<Delta> x)) = idc (pi1\<bullet>\<Delta>) (pi1\<bullet>x)"
    and   "(pi2\<bullet>(idc \<Delta> x)) = idc (pi2\<bullet>\<Delta>) (pi2\<bullet>x)"
   apply(induct \<Delta>)
     apply(auto)
  done

lemma ccloses_id:
  shows "(idc \<Delta> x) ccloses \<Delta>"
  apply(induct \<Delta>)
   apply(auto simp add: ccloses_def)
   apply(rule Ax_in_CANDs)
  apply(rule Ax_in_CANDs)
  done

lemma ncloses_id:
  shows "(idn \<Gamma> a) ncloses \<Gamma>"
  apply(induct \<Gamma>)
   apply(auto simp add: ncloses_def)
   apply(rule Ax_in_CANDs)
  apply(rule Ax_in_CANDs)
  done

lemma fresh_idn:
  fixes x::"name"
    and   a::"coname"
  shows "x\<sharp>\<Gamma> \<Longrightarrow> x\<sharp>idn \<Gamma> a"
    and   "a\<sharp>(\<Gamma>,b) \<Longrightarrow> a\<sharp>idn \<Gamma> b"
   apply(induct \<Gamma>)
     apply(auto simp add: fresh_list_cons fresh_list_nil fresh_atm fresh_prod)
  done

lemma fresh_idc:
  fixes x::"name"
    and   a::"coname"
  shows "x\<sharp>(\<Delta>,y) \<Longrightarrow> x\<sharp>idc \<Delta> y"
    and   "a\<sharp>\<Delta>  \<Longrightarrow> a\<sharp>idc \<Delta> y"
   apply(induct \<Delta>)
     apply(auto simp add: fresh_list_cons fresh_list_nil fresh_atm fresh_prod)
  done

lemma idc_cmaps:
  assumes a: "idc \<Delta> y cmaps b to Some (x,M)"
  shows "M=Ax x b"
  using a
  apply(induct \<Delta>)
   apply(auto)
  apply(case_tac "b=a")
   apply(auto)
  done

lemma idn_nmaps:
  assumes a: "idn \<Gamma> a nmaps x to Some (b,M)"
  shows "M=Ax x b"
  using a
  apply(induct \<Gamma>)
   apply(auto)
  apply(case_tac "aa=x")
   apply(auto)
  done

lemma lookup1:
  assumes a: "x\<sharp>(idn \<Gamma> b)"
  shows "lookup x a (idn \<Gamma> b) \<theta>_c = lookupa x a \<theta>_c"
  using a
  apply(induct \<Gamma>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
  done

lemma lookup2:
  assumes a: "\<not>(x\<sharp>(idn \<Gamma> b))"
  shows "lookup x a (idn \<Gamma> b) \<theta>_c = lookupb x a \<theta>_c b (Ax x b)"
  using a
  apply(induct \<Gamma>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm fresh_list_nil)
  done

lemma lookup3:
  assumes a: "a\<sharp>(idc \<Delta> y)"
  shows "lookupa x a (idc \<Delta> y) = Ax x a"
  using a
  apply(induct \<Delta>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm)
  done

lemma lookup4:
  assumes a: "\<not>(a\<sharp>(idc \<Delta> y))"
  shows "lookupa x a (idc \<Delta> y) = Cut <a>.(Ax x a) (y).Ax y a"
  using a
  apply(induct \<Delta>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm fresh_list_nil)
  done

lemma lookup5:
  assumes a: "a\<sharp>(idc \<Delta> y)"
  shows "lookupb x a (idc \<Delta> y) c P = Cut <c>.P (x).Ax x a"
  using a
  apply(induct \<Delta>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm fresh_list_nil)
  done

lemma lookup6:
  assumes a: "\<not>(a\<sharp>(idc \<Delta> y))"
  shows "lookupb x a (idc \<Delta> y) c P = Cut <c>.P (y).Ax y a"
  using a
  apply(induct \<Delta>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm fresh_list_nil)
  done

lemma lookup7:
  shows "lookupc x a (idn \<Gamma> b) = Ax x a"
  apply(induct \<Gamma>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm fresh_list_nil)
  done

lemma lookup8:
  shows "lookupd x a (idc \<Delta> y) = Ax x a"
  apply(induct \<Delta>)
   apply(auto simp add: fresh_list_cons fresh_prod fresh_atm fresh_list_nil)
  done

lemma id_redu:
  shows "(idn \<Gamma> x),(idc \<Delta> a)<M> \<longrightarrow>\<^sub>a* M"
  apply(nominal_induct M avoiding: \<Gamma> \<Delta> x a rule: trm.strong_induct)
             apply(auto)
    (* Ax *)
             apply(case_tac "name\<sharp>(idn \<Gamma> x)")
              apply(simp add: lookup1)
              apply(case_tac "coname\<sharp>(idc \<Delta> a)")
               apply(simp add: lookup3)
              apply(simp add: lookup4)
              apply(rule rtranclp_trans)
               apply(rule a_starI)
               apply(rule al_redu)
               apply(rule better_LAxR_intro)
               apply(rule fic.intros)
              apply(simp)
             apply(simp add: lookup2)
             apply(case_tac "coname\<sharp>(idc \<Delta> a)")
              apply(simp add: lookup5)
              apply(rule rtranclp_trans)
               apply(rule a_starI)
               apply(rule al_redu)
               apply(rule better_LAxR_intro)
               apply(rule fic.intros)
              apply(simp)
             apply(simp add: lookup6)
             apply(rule rtranclp_trans)
              apply(rule a_starI)
              apply(rule al_redu)
              apply(rule better_LAxR_intro)
              apply(rule fic.intros)
             apply(simp)
    (* Cut *)
            apply(auto simp add: fresh_idn fresh_idc psubst_fresh_name psubst_fresh_coname fresh_atm fresh_prod )[1]
               apply(simp add: lookup7 lookup8)
              apply(simp add: lookup7 lookup8)
              apply(simp add: a_star_Cut)
             apply(simp add: lookup7 lookup8)
             apply(simp add: a_star_Cut)
            apply(simp add: a_star_Cut)
    (* NotR *)
           apply(simp add: fresh_idn fresh_idc)
           apply(case_tac "findc (idc \<Delta> a) coname")
            apply(simp)
            apply(simp add: a_star_NotR)
           apply(auto)[1]
           apply(generate_fresh "coname")
           apply(fresh_fun_simp)
           apply(drule idc_cmaps)
           apply(simp)
           apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm>")
            apply(rule rtranclp_trans)
             apply(rule a_starI)
             apply(rule al_redu)
             apply(rule better_LAxR_intro)
             apply(rule fic.intros)
             apply(assumption)
            apply(simp add: crename_fresh)
            apply(simp add: a_star_NotR)
           apply(rule psubst_fresh_coname)
             apply(rule fresh_idn)
             apply(simp)
            apply(rule fresh_idc)
            apply(simp)
           apply(simp)
    (* NotL *)
          apply(simp add: fresh_idn fresh_idc)
          apply(case_tac "findn (idn \<Gamma> x) name")
           apply(simp)
           apply(simp add: a_star_NotL)
          apply(auto)[1]
          apply(generate_fresh "name")
          apply(fresh_fun_simp)
          apply(drule idn_nmaps)
          apply(simp)
          apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm>")
           apply(rule rtranclp_trans)
            apply(rule a_starI)
            apply(rule al_redu)
            apply(rule better_LAxL_intro)
            apply(rule fin.intros)
            apply(assumption)
           apply(simp add: nrename_fresh)
           apply(simp add: a_star_NotL)
          apply(rule psubst_fresh_name)
            apply(rule fresh_idn)
            apply(simp)
           apply(rule fresh_idc)
           apply(simp)
          apply(simp)
    (* AndR *)
         apply(simp add: fresh_idn fresh_idc)
         apply(case_tac "findc (idc \<Delta> a) coname3")
          apply(simp)
          apply(simp add: a_star_AndR)
         apply(auto)[1]
         apply(generate_fresh "coname")
         apply(fresh_fun_simp)
         apply(drule idc_cmaps)
         apply(simp)
         apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm1>")
          apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm2>")
           apply(rule rtranclp_trans)
            apply(rule a_starI)
            apply(rule al_redu)
            apply(rule better_LAxR_intro)
            apply(rule fic.intros)
             apply(simp add: abs_fresh)
            apply(simp add: abs_fresh)
           apply(auto simp add: fresh_idn fresh_idc psubst_fresh_name crename_fresh fresh_atm fresh_prod )[1]
           apply(rule aux3)
            apply(rule crename.simps)
              apply(auto simp add: fresh_prod fresh_atm)[1]
              apply(rule psubst_fresh_coname)
                apply(rule fresh_idn)
                apply(simp add: fresh_prod fresh_atm)
               apply(rule fresh_idc)
               apply(simp)
              apply(simp)
             apply(auto simp add: fresh_prod fresh_atm)[1]
             apply(rule psubst_fresh_coname)
               apply(rule fresh_idn)
               apply(simp add: fresh_prod fresh_atm)
              apply(rule fresh_idc)
              apply(simp)
             apply(simp)
            apply(simp)
           apply(simp)
           apply(simp add: crename_fresh)
           apply(simp add: a_star_AndR)
          apply(rule psubst_fresh_coname)
            apply(rule fresh_idn)
            apply(simp)
           apply(rule fresh_idc)
           apply(simp)
          apply(simp)
         apply(rule psubst_fresh_coname)
           apply(rule fresh_idn)
           apply(simp)
          apply(rule fresh_idc)
          apply(simp)
         apply(simp)
    (* AndL1 *)
        apply(simp add: fresh_idn fresh_idc)
        apply(case_tac "findn (idn \<Gamma> x) name2")
         apply(simp)
         apply(simp add: a_star_AndL1)
        apply(auto)[1]
        apply(generate_fresh "name")
        apply(fresh_fun_simp)
        apply(drule idn_nmaps)
        apply(simp)
        apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm>")
         apply(rule rtranclp_trans)
          apply(rule a_starI)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(rule fin.intros)
          apply(simp add: abs_fresh)
         apply(rule aux3)
          apply(rule nrename.simps)
          apply(auto simp add: fresh_prod fresh_atm)[1]
         apply(simp)
         apply(simp add: nrename_fresh)
         apply(simp add: a_star_AndL1)
        apply(rule psubst_fresh_name)
          apply(rule fresh_idn)
          apply(simp)
         apply(rule fresh_idc)
         apply(simp)
        apply(simp)
    (* AndL2 *)
       apply(simp add: fresh_idn fresh_idc)
       apply(case_tac "findn (idn \<Gamma> x) name2")
        apply(simp)
        apply(simp add: a_star_AndL2)
       apply(auto)[1]
       apply(generate_fresh "name")
       apply(fresh_fun_simp)
       apply(drule idn_nmaps)
       apply(simp)
       apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm>")
        apply(rule rtranclp_trans)
         apply(rule a_starI)
         apply(rule al_redu)
         apply(rule better_LAxL_intro)
         apply(rule fin.intros)
         apply(simp add: abs_fresh)
        apply(rule aux3)
         apply(rule nrename.simps)
         apply(auto simp add: fresh_prod fresh_atm)[1]
        apply(simp)
        apply(simp add: nrename_fresh)
        apply(simp add: a_star_AndL2)
       apply(rule psubst_fresh_name)
         apply(rule fresh_idn)
         apply(simp)
        apply(rule fresh_idc)
        apply(simp)
       apply(simp)
    (* OrR1 *)
      apply(simp add: fresh_idn fresh_idc)
      apply(case_tac "findc (idc \<Delta> a) coname2")
       apply(simp)
       apply(simp add: a_star_OrR1)
      apply(auto)[1]
      apply(generate_fresh "coname")
      apply(fresh_fun_simp)
      apply(drule idc_cmaps)
      apply(simp)
      apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm>")
       apply(rule rtranclp_trans)
        apply(rule a_starI)
        apply(rule al_redu)
        apply(rule better_LAxR_intro)
        apply(rule fic.intros)
        apply(simp add: abs_fresh)
       apply(rule aux3)
        apply(rule crename.simps)
        apply(auto simp add: fresh_prod fresh_atm)[1]
       apply(simp)
       apply(simp add: crename_fresh)
       apply(simp add: a_star_OrR1)
      apply(rule psubst_fresh_coname)
        apply(rule fresh_idn)
        apply(simp)
       apply(rule fresh_idc)
       apply(simp)
      apply(simp)
    (* OrR2 *)
     apply(simp add: fresh_idn fresh_idc)
     apply(case_tac "findc (idc \<Delta> a) coname2")
      apply(simp)
      apply(simp add: a_star_OrR2)
     apply(auto)[1]
     apply(generate_fresh "coname")
     apply(fresh_fun_simp)
     apply(drule idc_cmaps)
     apply(simp)
     apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm>")
      apply(rule rtranclp_trans)
       apply(rule a_starI)
       apply(rule al_redu)
       apply(rule better_LAxR_intro)
       apply(rule fic.intros)
       apply(simp add: abs_fresh)
      apply(rule aux3)
       apply(rule crename.simps)
       apply(auto simp add: fresh_prod fresh_atm)[1]
      apply(simp)
      apply(simp add: crename_fresh)
      apply(simp add: a_star_OrR2)
     apply(rule psubst_fresh_coname)
       apply(rule fresh_idn)
       apply(simp)
      apply(rule fresh_idc)
      apply(simp)
     apply(simp)
    (* OrL *)
    apply(simp add: fresh_idn fresh_idc)
    apply(case_tac "findn (idn \<Gamma> x) name3")
     apply(simp)
     apply(simp add: a_star_OrL)
    apply(auto)[1]
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(drule idn_nmaps)
    apply(simp)
    apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm1>")
     apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm2>")
      apply(rule rtranclp_trans)
       apply(rule a_starI)
       apply(rule al_redu)
       apply(rule better_LAxL_intro)
       apply(rule fin.intros)
        apply(simp add: abs_fresh)
       apply(simp add: abs_fresh)
      apply(rule aux3)
       apply(rule nrename.simps)
         apply(auto simp add: fresh_prod fresh_atm)[1]
         apply(rule psubst_fresh_name)
           apply(rule fresh_idn)
           apply(simp)
          apply(rule fresh_idc)
          apply(simp add: fresh_prod fresh_atm)
         apply(simp)
        apply(auto simp add: fresh_prod fresh_atm)[1]
        apply(rule psubst_fresh_name)
          apply(rule fresh_idn)
          apply(simp)
         apply(rule fresh_idc)
         apply(simp add: fresh_prod fresh_atm)
        apply(simp)
       apply(simp)
      apply(simp)
      apply(simp add: nrename_fresh)
      apply(simp add: a_star_OrL)
     apply(rule psubst_fresh_name)
       apply(rule fresh_idn)
       apply(simp)
      apply(rule fresh_idc)
      apply(simp)
     apply(simp)
    apply(rule psubst_fresh_name)
      apply(rule fresh_idn)
      apply(simp)
     apply(rule fresh_idc)
     apply(simp)
    apply(simp)
    (* ImpR *)
   apply(simp add: fresh_idn fresh_idc)
   apply(case_tac "findc (idc \<Delta> a) coname2")
    apply(simp)
    apply(simp add: a_star_ImpR)
   apply(auto)[1]
   apply(generate_fresh "coname")
   apply(fresh_fun_simp)
   apply(drule idc_cmaps)
   apply(simp)
   apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm>")
    apply(rule rtranclp_trans)
     apply(rule a_starI)
     apply(rule al_redu)
     apply(rule better_LAxR_intro)
     apply(rule fic.intros)
     apply(simp add: abs_fresh)
    apply(rule aux3)
     apply(rule crename.simps)
     apply(auto simp add: fresh_prod fresh_atm)[1]
    apply(simp)
    apply(simp add: crename_fresh)
    apply(simp add: a_star_ImpR)
   apply(rule psubst_fresh_coname)
     apply(rule fresh_idn)
     apply(simp)
    apply(rule fresh_idc)
    apply(simp)
   apply(simp)
    (* ImpL *)
  apply(simp add: fresh_idn fresh_idc)
  apply(case_tac "findn (idn \<Gamma> x) name2")
   apply(simp)
   apply(simp add: a_star_ImpL)
  apply(auto)[1]
  apply(generate_fresh "name")
  apply(fresh_fun_simp)
  apply(drule idn_nmaps)
  apply(simp)
  apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm1>")
   apply(subgoal_tac "c\<sharp>idn \<Gamma> x,idc \<Delta> a<trm2>")
    apply(rule rtranclp_trans)
     apply(rule a_starI)
     apply(rule al_redu)
     apply(rule better_LAxL_intro)
     apply(rule fin.intros)
      apply(simp add: abs_fresh)
     apply(simp add: abs_fresh)
    apply(rule aux3)
     apply(rule nrename.simps)
      apply(auto simp add: fresh_prod fresh_atm)[1]
      apply(rule psubst_fresh_coname)
        apply(rule fresh_idn)
        apply(simp add: fresh_atm)
       apply(rule fresh_idc)
       apply(simp add: fresh_prod fresh_atm)
      apply(simp)
     apply(auto simp add: fresh_prod fresh_atm)[1]
     apply(rule psubst_fresh_name)
       apply(rule fresh_idn)
       apply(simp)
      apply(rule fresh_idc)
      apply(simp add: fresh_prod fresh_atm)
     apply(simp)
    apply(simp)
    apply(simp add: nrename_fresh)
    apply(simp add: a_star_ImpL)
   apply(rule psubst_fresh_name)
     apply(rule fresh_idn)
     apply(simp)
    apply(rule fresh_idc)
    apply(simp)
   apply(simp)
  apply(rule psubst_fresh_name)
    apply(rule fresh_idn)
    apply(simp)
   apply(rule fresh_idc)
   apply(simp)
  apply(simp)
  done

theorem ALL_SNa:
  assumes a: "\<Gamma> \<turnstile> M \<turnstile> \<Delta>"
  shows "SNa M"
proof -
  fix x have "(idc \<Delta> x) ccloses \<Delta>" by (simp add: ccloses_id)
  moreover
  fix a have "(idn \<Gamma> a) ncloses \<Gamma>" by (simp add: ncloses_id)
  ultimately have "SNa ((idn \<Gamma> a),(idc \<Delta> x)<M>)" using a by (simp add: all_CAND)
  moreover
  have "((idn \<Gamma> a),(idc \<Delta> x)<M>) \<longrightarrow>\<^sub>a* M" by (simp add: id_redu)
  ultimately show "SNa M" by (simp add: a_star_preserves_SNa)
qed

end
