theory Class2
imports Class1
begin

text {* Reduction *}

lemma fin_not_Cut:
  assumes a: "fin M x"
  shows "\<not>(\<exists>a M' x N'. M = Cut <a>.M' (x).N')"
using a
by (induct) (auto)

lemma fresh_not_fin:
  assumes a: "x\<sharp>M"
  shows "\<not>fin M x"
proof -
  have "fin M x \<Longrightarrow> x\<sharp>M \<Longrightarrow> False" by (induct rule: fin.induct) (auto simp add: abs_fresh fresh_atm)
  with a show "\<not>fin M x" by blast
qed

lemma fresh_not_fic:
  assumes a: "a\<sharp>M"
  shows "\<not>fic M a"
proof -
  have "fic M a \<Longrightarrow> a\<sharp>M \<Longrightarrow> False" by (induct rule: fic.induct) (auto simp add: abs_fresh fresh_atm)
  with a show "\<not>fic M a" by blast
qed

lemma c_redu_subst1:
  assumes a: "M \<longrightarrow>\<^isub>c M'" "c\<sharp>M" "y\<sharp>P"
  shows "M{y:=<c>.P} \<longrightarrow>\<^isub>c M'{y:=<c>.P}"
using a
proof(nominal_induct avoiding: y c P rule: c_redu.strong_induct)
  case (left M a N x)
  then show ?case
    apply -
    apply(simp)
    apply(rule conjI)
    apply(force)
    apply(auto)
    apply(subgoal_tac "M{a:=(x).N}{y:=<c>.P} = M{y:=<c>.P}{a:=(x).(N{y:=<c>.P})}")(*A*)
    apply(simp)
    apply(rule c_redu.intros)
    apply(rule not_fic_subst1)
    apply(simp)
    apply(simp add: subst_fresh)
    apply(simp add: subst_fresh)
    apply(simp add: abs_fresh fresh_atm)
    apply(rule subst_subst2)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp)
    done
next
  case (right N x a M)
  then show ?case
    apply -
    apply(simp)
    apply(rule conjI)
    (* case M = Ax y a *)
    apply(rule impI)
    apply(subgoal_tac "N{x:=<a>.Ax y a}{y:=<c>.P} = N{y:=<c>.P}{x:=<c>.P}")
    apply(simp)
    apply(rule c_redu.right)
    apply(rule not_fin_subst2)
    apply(simp)
    apply(rule subst_fresh)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(rule sym)
    apply(rule interesting_subst1')
    apply(simp add: fresh_atm)
    apply(simp)
    apply(simp)
    (* case M \<noteq> Ax y a*)
    apply(rule impI)
    apply(subgoal_tac "N{x:=<a>.M}{y:=<c>.P} = N{y:=<c>.P}{x:=<a>.(M{y:=<c>.P})}")
    apply(simp)
    apply(rule c_redu.right)
    apply(rule not_fin_subst2)
    apply(simp)
    apply(simp add: subst_fresh)
    apply(simp add: subst_fresh)
    apply(simp add: abs_fresh fresh_atm)
    apply(rule subst_subst3)
    apply(simp_all add: fresh_atm fresh_prod)
    done
qed

lemma c_redu_subst2:
  assumes a: "M \<longrightarrow>\<^isub>c M'" "c\<sharp>P" "y\<sharp>M"
  shows "M{c:=(y).P} \<longrightarrow>\<^isub>c M'{c:=(y).P}"
using a
proof(nominal_induct avoiding: y c P rule: c_redu.strong_induct)
  case (right N x a M)
  then show ?case
    apply -
    apply(simp)
    apply(rule conjI)
    apply(force)
    apply(auto)
    apply(subgoal_tac "N{x:=<a>.M}{c:=(y).P} = N{c:=(y).P}{x:=<a>.(M{c:=(y).P})}")(*A*)
    apply(simp)
    apply(rule c_redu.intros)
    apply(rule not_fin_subst1)
    apply(simp)
    apply(simp add: subst_fresh)
    apply(simp add: subst_fresh)
    apply(simp add: abs_fresh fresh_atm)
    apply(rule subst_subst1)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp)
    done
next
  case (left M a N x)
  then show ?case
    apply -
    apply(simp)
    apply(rule conjI)
    (* case N = Ax x c *)
    apply(rule impI)
    apply(subgoal_tac "M{a:=(x).Ax x c}{c:=(y).P} = M{c:=(y).P}{a:=(y).P}")
    apply(simp)
    apply(rule c_redu.left)
    apply(rule not_fic_subst2)
    apply(simp)
    apply(simp)
    apply(rule subst_fresh)
    apply(simp add: abs_fresh)
    apply(rule sym)
    apply(rule interesting_subst2')
    apply(simp add: fresh_atm)
    apply(simp)
    apply(simp)
    (* case M \<noteq> Ax y a*)
    apply(rule impI)
    apply(subgoal_tac "M{a:=(x).N}{c:=(y).P} = M{c:=(y).P}{a:=(x).(N{c:=(y).P})}")
    apply(simp)
    apply(rule c_redu.left)
    apply(rule not_fic_subst2)
    apply(simp)
    apply(simp add: subst_fresh)
    apply(simp add: subst_fresh)
    apply(simp add: abs_fresh fresh_atm)
    apply(rule subst_subst4)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp add: fresh_prod fresh_atm)
    apply(simp)
    done
qed

lemma c_redu_subst1':
  assumes a: "M \<longrightarrow>\<^isub>c M'" 
  shows "M{y:=<c>.P} \<longrightarrow>\<^isub>c M'{y:=<c>.P}"
using a
proof -
  obtain y'::"name"   where fs1: "y'\<sharp>(M,M',P,P,y)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain c'::"coname" where fs2: "c'\<sharp>(M,M',P,P,c)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "M{y:=<c>.P} = ([(y',y)]\<bullet>M){y':=<c'>.([(c',c)]\<bullet>P)}" using fs1 fs2
    apply -
    apply(rule trans)
    apply(rule_tac y="y'" in subst_rename(3))
    apply(simp)
    apply(rule subst_rename(4))
    apply(simp)
    done
  also have "\<dots> \<longrightarrow>\<^isub>c ([(y',y)]\<bullet>M'){y':=<c'>.([(c',c)]\<bullet>P)}" using fs1 fs2
    apply -
    apply(rule c_redu_subst1)
    apply(simp add: c_redu.eqvt a)
    apply(simp_all add: fresh_left calc_atm fresh_prod)
    done
  also have "\<dots> = M'{y:=<c>.P}" using fs1 fs2
    apply -
    apply(rule sym)
    apply(rule trans)
    apply(rule_tac y="y'" in subst_rename(3))
    apply(simp)
    apply(rule subst_rename(4))
    apply(simp)
    done
  finally show ?thesis by simp
qed

lemma c_redu_subst2':
  assumes a: "M \<longrightarrow>\<^isub>c M'" 
  shows "M{c:=(y).P} \<longrightarrow>\<^isub>c M'{c:=(y).P}"
using a
proof -
  obtain y'::"name"   where fs1: "y'\<sharp>(M,M',P,P,y)" by (rule exists_fresh(1), rule fin_supp, blast)
  obtain c'::"coname" where fs2: "c'\<sharp>(M,M',P,P,c)" by (rule exists_fresh(2), rule fin_supp, blast)
  have "M{c:=(y).P} = ([(c',c)]\<bullet>M){c':=(y').([(y',y)]\<bullet>P)}" using fs1 fs2
    apply -
    apply(rule trans)
    apply(rule_tac c="c'" in subst_rename(1))
    apply(simp)
    apply(rule subst_rename(2))
    apply(simp)
    done
  also have "\<dots> \<longrightarrow>\<^isub>c ([(c',c)]\<bullet>M'){c':=(y').([(y',y)]\<bullet>P)}" using fs1 fs2
    apply -
    apply(rule c_redu_subst2)
    apply(simp add: c_redu.eqvt a)
    apply(simp_all add: fresh_left calc_atm fresh_prod)
    done
  also have "\<dots> = M'{c:=(y).P}" using fs1 fs2
    apply -
    apply(rule sym)
    apply(rule trans)
    apply(rule_tac c="c'" in subst_rename(1))
    apply(simp)
    apply(rule subst_rename(2))
    apply(simp)
    done

  finally show ?thesis by simp
qed

lemma aux1:
  assumes a: "M = M'" "M' \<longrightarrow>\<^isub>l M''"
  shows "M \<longrightarrow>\<^isub>l M''"
using a by simp
  
lemma aux2:
  assumes a: "M \<longrightarrow>\<^isub>l M'" "M' = M''"
  shows "M \<longrightarrow>\<^isub>l M''"
using a by simp

lemma aux3:
  assumes a: "M = M'" "M' \<longrightarrow>\<^isub>a* M''"
  shows "M \<longrightarrow>\<^isub>a* M''"
using a by simp

lemma aux4:
  assumes a: "M = M'"
  shows "M \<longrightarrow>\<^isub>a* M'"
using a by blast

lemma l_redu_subst1:
  assumes a: "M \<longrightarrow>\<^isub>l M'" 
  shows "M{y:=<c>.P} \<longrightarrow>\<^isub>a* M'{y:=<c>.P}"
using a
proof(nominal_induct M M' avoiding: y c P rule: l_redu.strong_induct)
  case LAxR
  then show ?case
    apply -
    apply(rule aux3)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp add: fresh_atm)
    apply(auto)
    apply(rule aux4)
    apply(simp add: trm.inject alpha calc_atm fresh_atm)
    apply(rule a_star_trans)
    apply(rule a_starI)
    apply(rule al_redu)
    apply(rule l_redu.intros)
    apply(simp add: subst_fresh)
    apply(simp add: fresh_atm)
    apply(rule fic_subst2)
    apply(simp_all)
    apply(rule aux4)
    apply(rule subst_comm')
    apply(simp_all)
    done
next
  case LAxL
  then show ?case
    apply -
    apply(rule aux3)
    apply(rule better_Cut_substn)
    apply(simp add: abs_fresh)
    apply(simp)
    apply(simp add: trm.inject fresh_atm)
    apply(auto)
    apply(rule aux4)
    apply(rule sym)
    apply(rule fin_substn_nrename)
    apply(simp_all)
    apply(rule a_starI)
    apply(rule al_redu)
    apply(rule aux2)
    apply(rule l_redu.intros)
    apply(simp add: subst_fresh)
    apply(simp add: fresh_atm)
    apply(rule fin_subst1)
    apply(simp_all)
    apply(rule subst_comm')
    apply(simp_all)
    done
next
  case (LNot v M N u a b)
  then show ?case
  proof -
    { assume asm: "N\<noteq>Ax y b"
      have "(Cut <a>.NotR (u).M a (v).NotL <b>.N v){y:=<c>.P} = 
        (Cut <a>.NotR (u).(M{y:=<c>.P}) a (v).NotL <b>.(N{y:=<c>.P}) v)" using LNot
        by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>l (Cut <b>.(N{y:=<c>.P}) (u).(M{y:=<c>.P}))" using LNot
        by (auto intro: l_redu.intros simp add: subst_fresh)
      also have "\<dots> = (Cut <b>.N (u).M){y:=<c>.P}" using LNot asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally have ?thesis by auto
    }
    moreover
    { assume asm: "N=Ax y b"
      have "(Cut <a>.NotR (u).M a (v).NotL <b>.N v){y:=<c>.P} = 
        (Cut <a>.NotR (u).(M{y:=<c>.P}) a (v).NotL <b>.(N{y:=<c>.P}) v)" using LNot
        by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* (Cut <b>.(N{y:=<c>.P}) (u).(M{y:=<c>.P}))" using LNot
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <b>.(Cut <c>.P (y).Ax y b) (u).(M{y:=<c>.P}))" using LNot asm
        by simp
      also have "\<dots> \<longrightarrow>\<^isub>a* (Cut <b>.(P[c\<turnstile>c>b]) (u).(M{y:=<c>.P}))" 
      proof (cases "fic P c")
        case True 
        assume "fic P c"
        then show ?thesis using LNot
          apply -
          apply(rule a_starI)
          apply(rule better_CutL_intro)
          apply(rule al_redu)
          apply(rule better_LAxR_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fic P c" 
        then show ?thesis
          apply -
          apply(rule a_star_CutL)
          apply(rule a_star_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_left)
          apply(simp)
          apply(simp add: subst_with_ax2)
          done
      qed
      also have "\<dots> = (Cut <b>.N (u).M){y:=<c>.P}" using LNot asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule crename_swap)
        apply(simp)
        done
      finally have "(Cut <a>.NotR (u).M a (v).NotL <b>.N v){y:=<c>.P} \<longrightarrow>\<^isub>a* (Cut <b>.N (u).M){y:=<c>.P}" 
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LAnd1 b a1 M1 a2 M2 N z u)
  then show ?case
  proof -
    { assume asm: "M1\<noteq>Ax y a1"
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL1 (u).N z){y:=<c>.P} = 
        Cut <b>.AndR <a1>.(M1{y:=<c>.P}) <a2>.(M2{y:=<c>.P}) b (z).AndL1 (u).(N{y:=<c>.P}) z" 
        using LAnd1 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a1>.(M1{y:=<c>.P}) (u).(N{y:=<c>.P})"
        using LAnd1
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a1>.M1 (u).N){y:=<c>.P}" using LAnd1 asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL1 (u).N z){y:=<c>.P} \<longrightarrow>\<^isub>a* (Cut <a1>.M1 (u).N){y:=<c>.P}"
        by simp
    } 
    moreover
    { assume asm: "M1=Ax y a1"
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL1 (u).N z){y:=<c>.P} = 
        Cut <b>.AndR <a1>.(M1{y:=<c>.P}) <a2>.(M2{y:=<c>.P}) b (z).AndL1 (u).(N{y:=<c>.P}) z" 
        using LAnd1 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a1>.(M1{y:=<c>.P}) (u).(N{y:=<c>.P})"
        using LAnd1
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a1>.(Cut <c>.P (y). Ax y a1) (u).(N{y:=<c>.P})" 
        using LAnd1 asm by simp
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a1>.P[c\<turnstile>c>a1] (u).(N{y:=<c>.P})"
      proof (cases "fic P c")
        case True 
        assume "fic P c"
        then show ?thesis using LAnd1
          apply -
          apply(rule a_starI)
          apply(rule better_CutL_intro)
          apply(rule al_redu)
          apply(rule better_LAxR_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fic P c" 
        then show ?thesis
          apply -
          apply(rule a_star_CutL)
          apply(rule a_star_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_left)
          apply(simp)
          apply(simp add: subst_with_ax2)
          done
      qed
      also have "\<dots> = (Cut <a1>.M1 (u).N){y:=<c>.P}" using LAnd1 asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule crename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL1 (u).N z){y:=<c>.P} \<longrightarrow>\<^isub>a* (Cut <a1>.M1 (u).N){y:=<c>.P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LAnd2 b a1 M1 a2 M2 N z u)
  then show ?case
  proof -
    { assume asm: "M2\<noteq>Ax y a2"
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL2 (u).N z){y:=<c>.P} = 
        Cut <b>.AndR <a1>.(M1{y:=<c>.P}) <a2>.(M2{y:=<c>.P}) b (z).AndL2 (u).(N{y:=<c>.P}) z" 
        using LAnd2 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a2>.(M2{y:=<c>.P}) (u).(N{y:=<c>.P})"
        using LAnd2
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a2>.M2 (u).N){y:=<c>.P}" using LAnd2 asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL2 (u).N z){y:=<c>.P} \<longrightarrow>\<^isub>a* (Cut <a2>.M2 (u).N){y:=<c>.P}"
        by simp
    } 
    moreover
    { assume asm: "M2=Ax y a2"
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL2 (u).N z){y:=<c>.P} = 
        Cut <b>.AndR <a1>.(M1{y:=<c>.P}) <a2>.(M2{y:=<c>.P}) b (z).AndL2 (u).(N{y:=<c>.P}) z" 
        using LAnd2 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a2>.(M2{y:=<c>.P}) (u).(N{y:=<c>.P})"
        using LAnd2
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a2>.(Cut <c>.P (y). Ax y a2) (u).(N{y:=<c>.P})" 
        using LAnd2 asm by simp
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a2>.P[c\<turnstile>c>a2] (u).(N{y:=<c>.P})"
      proof (cases "fic P c")
        case True 
        assume "fic P c"
        then show ?thesis using LAnd2 asm
          apply -
          apply(rule a_starI)
          apply(rule better_CutL_intro)
          apply(rule al_redu)
          apply(rule better_LAxR_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fic P c" 
        then show ?thesis
          apply -
          apply(rule a_star_CutL)
          apply(rule a_star_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_left)
          apply(simp)
          apply(simp add: subst_with_ax2)
          done
      qed
      also have "\<dots> = (Cut <a2>.M2 (u).N){y:=<c>.P}" using LAnd2 asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule crename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL2 (u).N z){y:=<c>.P} \<longrightarrow>\<^isub>a* (Cut <a2>.M2 (u).N){y:=<c>.P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LOr1 b a M N1 N2 z x1 x2 y c P)
  then show ?case
  proof -
    { assume asm: "M\<noteq>Ax y a"
      have "(Cut <b>.OrR1 <a>.M b (z).OrL (x1).N1 (x2).N2 z){y:=<c>.P} = 
        Cut <b>.OrR1 <a>.(M{y:=<c>.P}) b (z).OrL (x1).(N1{y:=<c>.P}) (x2).(N2{y:=<c>.P}) z" 
        using LOr1 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(M{y:=<c>.P}) (x1).(N1{y:=<c>.P})"
        using LOr1
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a>.M (x1).N1){y:=<c>.P}" using LOr1 asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.OrR1 <a>.M b (z).OrL (x1).N1 (x2).N2 z){y:=<c>.P} \<longrightarrow>\<^isub>a* (Cut <a>.M (x1).N1){y:=<c>.P}"
        by simp
    } 
    moreover
    { assume asm: "M=Ax y a"
      have "(Cut <b>.OrR1 <a>.M b (z).OrL (x1).N1 (x2).N2 z){y:=<c>.P} = 
        Cut <b>.OrR1 <a>.(M{y:=<c>.P}) b (z).OrL (x1).(N1{y:=<c>.P}) (x2).(N2{y:=<c>.P}) z" 
        using LOr1 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(M{y:=<c>.P}) (x1).(N1{y:=<c>.P})"
        using LOr1
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a>.(Cut <c>.P (y). Ax y a) (x1).(N1{y:=<c>.P})" 
        using LOr1 asm by simp
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.P[c\<turnstile>c>a] (x1).(N1{y:=<c>.P})"
      proof (cases "fic P c")
        case True 
        assume "fic P c"
        then show ?thesis using LOr1
          apply -
          apply(rule a_starI)
          apply(rule better_CutL_intro)
          apply(rule al_redu)
          apply(rule better_LAxR_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fic P c" 
        then show ?thesis
          apply -
          apply(rule a_star_CutL)
          apply(rule a_star_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_left)
          apply(simp)
          apply(simp add: subst_with_ax2)
          done
      qed
      also have "\<dots> = (Cut <a>.M (x1).N1){y:=<c>.P}" using LOr1 asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule crename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.OrR1 <a>.M b (z).OrL (x1).N1 (x2).N2 z){y:=<c>.P} \<longrightarrow>\<^isub>a* (Cut <a>.M (x1).N1){y:=<c>.P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LOr2 b a M N1 N2 z x1 x2 y c P)
  then show ?case
  proof -
    { assume asm: "M\<noteq>Ax y a"
      have "(Cut <b>.OrR2 <a>.M b (z).OrL (x1).N1 (x2).N2 z){y:=<c>.P} = 
        Cut <b>.OrR2 <a>.(M{y:=<c>.P}) b (z).OrL (x1).(N1{y:=<c>.P}) (x2).(N2{y:=<c>.P}) z" 
        using LOr2 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(M{y:=<c>.P}) (x2).(N2{y:=<c>.P})"
        using LOr2
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a>.M (x2).N2){y:=<c>.P}" using LOr2 asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.OrR2 <a>.M b (z).OrL (x1).N1 (x2).N2 z){y:=<c>.P} \<longrightarrow>\<^isub>a* (Cut <a>.M (x2).N2){y:=<c>.P}"
        by simp
    } 
    moreover
    { assume asm: "M=Ax y a"
      have "(Cut <b>.OrR2 <a>.M b (z).OrL (x1).N1 (x2).N2 z){y:=<c>.P} = 
        Cut <b>.OrR2 <a>.(M{y:=<c>.P}) b (z).OrL (x1).(N1{y:=<c>.P}) (x2).(N2{y:=<c>.P}) z" 
        using LOr2 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(M{y:=<c>.P}) (x2).(N2{y:=<c>.P})"
        using LOr2
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a>.(Cut <c>.P (y). Ax y a) (x2).(N2{y:=<c>.P})" 
        using LOr2 asm by simp
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.P[c\<turnstile>c>a] (x2).(N2{y:=<c>.P})"
      proof (cases "fic P c")
        case True 
        assume "fic P c"
        then show ?thesis using LOr2
          apply -
          apply(rule a_starI)
          apply(rule better_CutL_intro)
          apply(rule al_redu)
          apply(rule better_LAxR_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fic P c" 
        then show ?thesis
          apply -
          apply(rule a_star_CutL)
          apply(rule a_star_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_left)
          apply(simp)
          apply(simp add: subst_with_ax2)
          done
      qed
      also have "\<dots> = (Cut <a>.M (x2).N2){y:=<c>.P}" using LOr2 asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule crename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.OrR2 <a>.M b (z).OrL (x1).N1 (x2).N2 z){y:=<c>.P} \<longrightarrow>\<^isub>a* (Cut <a>.M (x2).N2){y:=<c>.P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LImp z N u Q x M b a d y c P)
  then show ?case
  proof -
    { assume asm: "N\<noteq>Ax y d"
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){y:=<c>.P} = 
        Cut <b>.ImpR (x).<a>.(M{y:=<c>.P}) b (z).ImpL <d>.(N{y:=<c>.P}) (u).(Q{y:=<c>.P}) z" 
        using LImp by (simp add: fresh_prod abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(Cut <d>.(N{y:=<c>.P})  (x).(M{y:=<c>.P})) (u).(Q{y:=<c>.P})"
        using LImp
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a>.(Cut <d>.N  (x).M) (u).Q){y:=<c>.P}" using LImp asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){y:=<c>.P} \<longrightarrow>\<^isub>a* 
                     (Cut <a>.(Cut <d>.N  (x).M) (u).Q){y:=<c>.P}"
        by simp
    } 
    moreover
    { assume asm: "N=Ax y d"
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){y:=<c>.P} = 
        Cut <b>.ImpR (x).<a>.(M{y:=<c>.P}) b (z).ImpL <d>.(N{y:=<c>.P}) (u).(Q{y:=<c>.P}) z" 
        using LImp by (simp add: subst_fresh abs_fresh fresh_atm fresh_prod)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(Cut <d>.(N{y:=<c>.P})  (x).(M{y:=<c>.P})) (u).(Q{y:=<c>.P})"
        using LImp
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a>.(Cut <d>.(Cut <c>.P (y).Ax y d)  (x).(M{y:=<c>.P})) (u).(Q{y:=<c>.P})"
        using LImp asm by simp
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(Cut <d>.(P[c\<turnstile>c>d]) (x).(M{y:=<c>.P})) (u).(Q{y:=<c>.P})"
      proof (cases "fic P c")
        case True 
        assume "fic P c"
        then show ?thesis using LImp
          apply -
          apply(rule a_starI)
          apply(rule better_CutL_intro)
          apply(rule a_Cut_l)
          apply(simp add: subst_fresh abs_fresh)
          apply(simp add: abs_fresh fresh_atm)
          apply(rule al_redu)
          apply(rule better_LAxR_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fic P c" 
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutL)
          apply(rule a_star_CutL)
          apply(rule a_star_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_left)
          apply(simp)
          apply(simp add: subst_with_ax2)
          done
      qed
      also have "\<dots> = (Cut <a>.(Cut <d>.N (x).M) (u).Q){y:=<c>.P}" using LImp asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(simp add: trm.inject)
        apply(simp add: alpha)
        apply(rule sym)
        apply(rule crename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){y:=<c>.P} \<longrightarrow>\<^isub>a* 
               (Cut <a>.(Cut <d>.N (x).M) (u).Q){y:=<c>.P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
qed

lemma l_redu_subst2:
  assumes a: "M \<longrightarrow>\<^isub>l M'" 
  shows "M{c:=(y).P} \<longrightarrow>\<^isub>a* M'{c:=(y).P}"
using a
proof(nominal_induct M M' avoiding: y c P rule: l_redu.strong_induct)
  case LAxR
  then show ?case
    apply -
    apply(rule aux3)
    apply(rule better_Cut_substc)
    apply(simp add: abs_fresh)
    apply(simp add: abs_fresh)
    apply(simp add: trm.inject fresh_atm)
    apply(auto)
    apply(rule aux4)
    apply(rule sym)
    apply(rule fic_substc_crename)
    apply(simp_all)
    apply(rule a_starI)
    apply(rule al_redu)
    apply(rule aux2)
    apply(rule l_redu.intros)
    apply(simp add: subst_fresh)
    apply(simp add: fresh_atm)
    apply(rule fic_subst1)
    apply(simp_all)
    apply(rule subst_comm')
    apply(simp_all)
    done
next
  case LAxL
  then show ?case
    apply -
    apply(rule aux3)
    apply(rule better_Cut_substc)
    apply(simp)
    apply(simp add: abs_fresh)
    apply(simp add: fresh_atm)
    apply(auto)
    apply(rule aux4)
    apply(simp add: trm.inject alpha calc_atm fresh_atm)
    apply(rule a_star_trans)
    apply(rule a_starI)
    apply(rule al_redu)
    apply(rule l_redu.intros)
    apply(simp add: subst_fresh)
    apply(simp add: fresh_atm)
    apply(rule fin_subst2)
    apply(simp_all)
    apply(rule aux4)
    apply(rule subst_comm')
    apply(simp_all)
    done
next
  case (LNot v M N u a b)
  then show ?case
  proof -
    { assume asm: "M\<noteq>Ax u c"
      have "(Cut <a>.NotR (u).M a (v).NotL <b>.N v){c:=(y).P} = 
        (Cut <a>.NotR (u).(M{c:=(y).P}) a (v).NotL <b>.(N{c:=(y).P}) v)" using LNot
        by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>l (Cut <b>.(N{c:=(y).P}) (u).(M{c:=(y).P}))" using LNot
        by (auto intro: l_redu.intros simp add: subst_fresh)
      also have "\<dots> = (Cut <b>.N (u).M){c:=(y).P}" using LNot asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally have ?thesis by auto
    }
    moreover
    { assume asm: "M=Ax u c"
      have "(Cut <a>.NotR (u).M a (v).NotL <b>.N v){c:=(y).P} = 
        (Cut <a>.NotR (u).(M{c:=(y).P}) a (v).NotL <b>.(N{c:=(y).P}) v)" using LNot
        by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* (Cut <b>.(N{c:=(y).P}) (u).(M{c:=(y).P}))" using LNot
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <b>.(N{c:=(y).P}) (u).(Cut <c>.(Ax u c) (y).P))" using LNot asm
        by simp
      also have "\<dots> \<longrightarrow>\<^isub>a* (Cut <b>.(N{c:=(y).P})  (u).(P[y\<turnstile>n>u]))" 
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LNot
          apply -
          apply(rule a_starI)
          apply(rule better_CutR_intro)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis
          apply -
          apply(rule a_star_CutR)
          apply(rule a_star_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> = (Cut <b>.N (u).M){c:=(y).P}" using LNot asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule nrename_swap)
        apply(simp)
        done
      finally have "(Cut <a>.NotR (u).M a (v).NotL <b>.N v){c:=(y).P} \<longrightarrow>\<^isub>a* (Cut <b>.N (u).M){c:=(y).P}" 
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LAnd1 b a1 M1 a2 M2 N z u)
  then show ?case
  proof -
    { assume asm: "N\<noteq>Ax u c"
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL1 (u).N z){c:=(y).P} = 
        Cut <b>.AndR <a1>.(M1{c:=(y).P}) <a2>.(M2{c:=(y).P}) b (z).AndL1 (u).(N{c:=(y).P}) z" 
        using LAnd1 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a1>.(M1{c:=(y).P}) (u).(N{c:=(y).P})"
        using LAnd1
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a1>.M1 (u).N){c:=(y).P}" using LAnd1 asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL1 (u).N z){c:=(y).P} \<longrightarrow>\<^isub>a* (Cut <a1>.M1 (u).N){c:=(y).P}"
        by simp
    } 
    moreover
    { assume asm: "N=Ax u c"
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL1 (u).N z){c:=(y).P} = 
        Cut <b>.AndR <a1>.(M1{c:=(y).P}) <a2>.(M2{c:=(y).P}) b (z).AndL1 (u).(N{c:=(y).P}) z" 
        using LAnd1 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a1>.(M1{c:=(y).P}) (u).(N{c:=(y).P})"
        using LAnd1
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a1>.(M1{c:=(y).P}) (u).(Cut <c>.(Ax u c) (y).P)" 
        using LAnd1 asm by simp
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a1>.(M1{c:=(y).P}) (u).(P[y\<turnstile>n>u])"
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LAnd1
          apply -
          apply(rule a_starI)
          apply(rule better_CutR_intro)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis
          apply -
          apply(rule a_star_CutR)
          apply(rule a_star_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> = (Cut <a1>.M1 (u).N){c:=(y).P}" using LAnd1 asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule nrename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL1 (u).N z){c:=(y).P} \<longrightarrow>\<^isub>a* (Cut <a1>.M1 (u).N){c:=(y).P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LAnd2 b a1 M1 a2 M2 N z u)
  then show ?case
  proof -
    { assume asm: "N\<noteq>Ax u c"
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL2 (u).N z){c:=(y).P} = 
        Cut <b>.AndR <a1>.(M1{c:=(y).P}) <a2>.(M2{c:=(y).P}) b (z).AndL2 (u).(N{c:=(y).P}) z" 
        using LAnd2 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a2>.(M2{c:=(y).P}) (u).(N{c:=(y).P})"
        using LAnd2
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a2>.M2 (u).N){c:=(y).P}" using LAnd2 asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL2 (u).N z){c:=(y).P} \<longrightarrow>\<^isub>a* (Cut <a2>.M2 (u).N){c:=(y).P}"
        by simp
    } 
    moreover
    { assume asm: "N=Ax u c"
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL2 (u).N z){c:=(y).P} = 
        Cut <b>.AndR <a1>.(M1{c:=(y).P}) <a2>.(M2{c:=(y).P}) b (z).AndL2 (u).(N{c:=(y).P}) z" 
        using LAnd2 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a2>.(M2{c:=(y).P}) (u).(N{c:=(y).P})"
        using LAnd2
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a2>.(M2{c:=(y).P}) (u).(Cut <c>.(Ax u c) (y).P)" 
        using LAnd2 asm by simp
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a2>.(M2{c:=(y).P}) (u).(P[y\<turnstile>n>u])"
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LAnd2
          apply -
          apply(rule a_starI)
          apply(rule better_CutR_intro)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis
          apply -
          apply(rule a_star_CutR)
          apply(rule a_star_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> = (Cut <a2>.M2 (u).N){c:=(y).P}" using LAnd2 asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule nrename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.AndR <a1>.M1 <a2>.M2 b (z).AndL2 (u).N z){c:=(y).P} \<longrightarrow>\<^isub>a* (Cut <a2>.M2 (u).N){c:=(y).P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LOr1 b a M N1 N2 z x1 x2 y c P)
  then show ?case
  proof -
    { assume asm: "N1\<noteq>Ax x1 c"
      have "(Cut <b>.OrR1 <a>.M b (z).OrL (x1).N1 (x2).N2 z){c:=(y).P} = 
        Cut <b>.OrR1 <a>.(M{c:=(y).P}) b (z).OrL (x1).(N1{c:=(y).P}) (x2).(N2{c:=(y).P}) z" 
        using LOr1 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(M{c:=(y).P}) (x1).(N1{c:=(y).P})"
        using LOr1
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a>.M (x1).N1){c:=(y).P}" using LOr1 asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.OrR1 <a>.M b (z).OrL (x1).N1 (x2).N2 z){c:=(y).P} \<longrightarrow>\<^isub>a* (Cut <a>.M (x1).N1){c:=(y).P}"
        by simp
    } 
    moreover
    { assume asm: "N1=Ax x1 c"
      have "(Cut <b>.OrR1 <a>.M b (z).OrL (x1).N1 (x2).N2 z){c:=(y).P} = 
        Cut <b>.OrR1 <a>.(M{c:=(y).P}) b (z).OrL (x1).(N1{c:=(y).P}) (x2).(N2{c:=(y).P}) z" 
        using LOr1 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(M{c:=(y).P}) (x1).(N1{c:=(y).P})"
        using LOr1
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a>.(M{c:=(y).P}) (x1).(Cut <c>.(Ax x1 c) (y).P)" 
        using LOr1 asm by simp
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(M{c:=(y).P})   (x1).(P[y\<turnstile>n>x1])"
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LOr1
          apply -
          apply(rule a_starI)
          apply(rule better_CutR_intro)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis
          apply -
          apply(rule a_star_CutR)
          apply(rule a_star_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> = (Cut <a>.M (x1).N1){c:=(y).P}" using LOr1 asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule nrename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.OrR1 <a>.M b (z).OrL (x1).N1 (x2).N2 z){c:=(y).P} \<longrightarrow>\<^isub>a* (Cut <a>.M (x1).N1){c:=(y).P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LOr2 b a M N1 N2 z x1 x2 y c P)
  then show ?case
  proof -
    { assume asm: "N2\<noteq>Ax x2 c"
      have "(Cut <b>.OrR2 <a>.M b (z).OrL (x1).N1 (x2).N2 z){c:=(y).P} = 
        Cut <b>.OrR2 <a>.(M{c:=(y).P}) b (z).OrL (x1).(N1{c:=(y).P}) (x2).(N2{c:=(y).P}) z" 
        using LOr2 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(M{c:=(y).P}) (x2).(N2{c:=(y).P})"
        using LOr2
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a>.M (x2).N2){c:=(y).P}" using LOr2 asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.OrR2 <a>.M b (z).OrL (x1).N1 (x2).N2 z){c:=(y).P} \<longrightarrow>\<^isub>a* (Cut <a>.M (x2).N2){c:=(y).P}"
        by simp
    } 
    moreover
    { assume asm: "N2=Ax x2 c"
      have "(Cut <b>.OrR2 <a>.M b (z).OrL (x1).N1 (x2).N2 z){c:=(y).P} = 
        Cut <b>.OrR2 <a>.(M{c:=(y).P}) b (z).OrL (x1).(N1{c:=(y).P}) (x2).(N2{c:=(y).P}) z" 
        using LOr2 by (simp add: subst_fresh abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(M{c:=(y).P}) (x2).(N2{c:=(y).P})"
        using LOr2
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a>.(M{c:=(y).P}) (x2).(Cut <c>.(Ax x2 c) (y).P)" 
        using LOr2 asm by simp
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(M{c:=(y).P}) (x2).(P[y\<turnstile>n>x2])"
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LOr2
          apply -
          apply(rule a_starI)
          apply(rule better_CutR_intro)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis
          apply -
          apply(rule a_star_CutR)
          apply(rule a_star_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> = (Cut <a>.M (x2).N2){c:=(y).P}" using LOr2 asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(rule sym)
        apply(rule nrename_swap)
        apply(simp)
        done
      finally 
      have "(Cut <b>.OrR2 <a>.M b (z).OrL (x1).N1 (x2).N2 z){c:=(y).P} \<longrightarrow>\<^isub>a* (Cut <a>.M (x2).N2){c:=(y).P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
next
  case (LImp z N u Q x M b a d y c P)
  then show ?case
  proof -
    { assume asm: "M\<noteq>Ax x c \<and> Q\<noteq>Ax u c"
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){c:=(y).P} = 
        Cut <b>.ImpR (x).<a>.(M{c:=(y).P}) b (z).ImpL <d>.(N{c:=(y).P}) (u).(Q{c:=(y).P}) z" 
        using LImp by (simp add: fresh_prod abs_fresh fresh_atm)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(M{c:=(y).P})) (u).(Q{c:=(y).P})"
        using LImp
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = (Cut <a>.(Cut <d>.N  (x).M) (u).Q){c:=(y).P}" using LImp asm
        by (simp add: subst_fresh abs_fresh fresh_atm)
      finally 
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){c:=(y).P} \<longrightarrow>\<^isub>a* 
                     (Cut <a>.(Cut <d>.N  (x).M) (u).Q){c:=(y).P}"
        by simp
    } 
    moreover
    { assume asm: "M=Ax x c \<and> Q\<noteq>Ax u c"
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){c:=(y).P} = 
        Cut <b>.ImpR (x).<a>.(M{c:=(y).P}) b (z).ImpL <d>.(N{c:=(y).P}) (u).(Q{c:=(y).P}) z" 
        using LImp by (simp add: subst_fresh abs_fresh fresh_atm fresh_prod)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(M{c:=(y).P})) (u).(Q{c:=(y).P})"
        using LImp
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(Cut <c>.Ax x c (y).P)) (u).(Q{c:=(y).P})"
        using LImp asm by simp
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(P[y\<turnstile>n>x])) (u).(Q{c:=(y).P})"
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutL)
          apply(rule a_star_CutR)
          apply(rule a_star_trans)
          apply(rule a_starI)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutL)
          apply(rule a_star_CutR)
          apply(rule a_star_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> = (Cut <a>.(Cut <d>.N (x).M) (u).Q){c:=(y).P}" using LImp asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(simp add: trm.inject)
        apply(simp add: alpha)
        apply(simp add: nrename_swap)
        done
      finally 
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){c:=(y).P} \<longrightarrow>\<^isub>a* 
               (Cut <a>.(Cut <d>.N (x).M) (u).Q){c:=(y).P}"
        by simp
    }
     moreover
    { assume asm: "M\<noteq>Ax x c \<and> Q=Ax u c"
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){c:=(y).P} = 
        Cut <b>.ImpR (x).<a>.(M{c:=(y).P}) b (z).ImpL <d>.(N{c:=(y).P}) (u).(Q{c:=(y).P}) z" 
        using LImp by (simp add: subst_fresh abs_fresh fresh_atm fresh_prod)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(M{c:=(y).P})) (u).(Q{c:=(y).P})"
        using LImp
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(M{c:=(y).P})) (u).(Cut <c>.Ax u c (y).P)"
        using LImp asm by simp
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(M{c:=(y).P})) (u).(P[y\<turnstile>n>u])"
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutR)
          apply(rule a_starI)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutR)
          apply(rule a_star_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> = (Cut <a>.(Cut <d>.N (x).M) (u).Q){c:=(y).P}" using LImp asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(simp add: alpha fresh_atm)
        apply(simp add: nrename_swap)
        done
      finally 
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){c:=(y).P} \<longrightarrow>\<^isub>a* 
               (Cut <a>.(Cut <d>.N (x).M) (u).Q){c:=(y).P}"
        by simp
    }
     moreover
    { assume asm: "M=Ax x c \<and> Q=Ax u c"
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){c:=(y).P} = 
        Cut <b>.ImpR (x).<a>.(M{c:=(y).P}) b (z).ImpL <d>.(N{c:=(y).P}) (u).(Q{c:=(y).P}) z" 
        using LImp by (simp add: subst_fresh abs_fresh fresh_atm fresh_prod)
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(M{c:=(y).P})) (u).(Q{c:=(y).P})"
        using LImp
        apply -
        apply(rule a_starI)
        apply(rule al_redu)
        apply(auto intro: l_redu.intros simp add: subst_fresh abs_fresh)
        done
      also have "\<dots> = Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(Cut <c>.Ax x c (y).P)) (u).(Cut <c>.Ax u c (y).P)"
        using LImp asm by simp
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(Cut <c>.Ax x c (y).P)) (u).(P[y\<turnstile>n>u])"
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutR)
          apply(rule a_starI)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutR)
          apply(rule a_star_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> \<longrightarrow>\<^isub>a* Cut <a>.(Cut <d>.(N{c:=(y).P})  (x).(P[y\<turnstile>n>x])) (u).(P[y\<turnstile>n>u])"
      proof (cases "fin P y")
        case True 
        assume "fin P y"
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutL)
          apply(rule a_star_CutR)
          apply(rule a_starI)
          apply(rule al_redu)
          apply(rule better_LAxL_intro)
          apply(simp)
          done
      next
        case False 
        assume "\<not>fin P y" 
        then show ?thesis using LImp
          apply -
          apply(rule a_star_CutL)
          apply(rule a_star_CutR)
          apply(rule a_star_trans)
          apply(rule a_starI)
          apply(rule ac_redu)
          apply(rule better_right)
          apply(simp)
          apply(simp add: subst_with_ax1)
          done
      qed
      also have "\<dots> = (Cut <a>.(Cut <d>.N (x).M) (u).Q){c:=(y).P}" using LImp asm
        apply -
        apply(auto simp add: subst_fresh abs_fresh)
        apply(simp add: trm.inject)
        apply(rule conjI)
        apply(simp add: alpha fresh_atm trm.inject)
        apply(simp add: nrename_swap)
        apply(simp add: alpha fresh_atm trm.inject)
        apply(simp add: nrename_swap)
        done
      finally 
      have "(Cut <b>.ImpR (x).<a>.M b (z).ImpL <d>.N (u).Q z){c:=(y).P} \<longrightarrow>\<^isub>a* 
               (Cut <a>.(Cut <d>.N (x).M) (u).Q){c:=(y).P}"
        by simp
    }
    ultimately show ?thesis by blast
  qed
qed

lemma a_redu_subst1:
  assumes a: "M \<longrightarrow>\<^isub>a M'"
  shows "M{y:=<c>.P} \<longrightarrow>\<^isub>a* M'{y:=<c>.P}"
using a
proof(nominal_induct avoiding: y c P rule: a_redu.strong_induct)
  case al_redu
  then show ?case by (simp only: l_redu_subst1)
next
  case ac_redu
  then show ?case
    apply -
    apply(rule a_starI)
    apply(rule a_redu.ac_redu)
    apply(simp only: c_redu_subst1')
    done
next
  case (a_Cut_l a N x M M' y c P)
  then show ?case
    apply(simp add: subst_fresh fresh_a_redu)
    apply(rule conjI)
    apply(rule impI)+
    apply(simp)
    apply(drule ax_do_not_a_reduce)
    apply(simp)
    apply(rule impI)
    apply(rule conjI)
    apply(rule impI)
    apply(simp)
    apply(drule_tac x="y" in meta_spec)
    apply(drule_tac x="c" in meta_spec)
    apply(drule_tac x="P" in meta_spec)
    apply(simp)
    apply(rule a_star_trans)
    apply(rule a_star_CutL)
    apply(assumption)
    apply(rule a_star_trans)
    apply(rule_tac M'="P[c\<turnstile>c>a]" in a_star_CutL)
    apply(case_tac "fic P c")
    apply(rule a_starI)
    apply(rule al_redu)
    apply(rule better_LAxR_intro)
    apply(simp)
    apply(rule a_star_trans)
    apply(rule a_starI)
    apply(rule ac_redu)
    apply(rule better_left)
    apply(simp)
    apply(rule subst_with_ax2)
    apply(rule aux4)
    apply(simp add: trm.inject)
    apply(simp add: alpha fresh_atm)
    apply(simp add: crename_swap)
    apply(rule impI)
    apply(rule a_star_CutL)
    apply(auto)
    done
next
  case (a_Cut_r a N x M M' y c P)
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_CutR)
    apply(auto)[1]
    apply(rule a_star_CutR)
    apply(auto)[1]
    done
next
  case a_NotL
  then show ?case 
    apply(auto)
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutR)
    apply(rule a_star_NotL)
    apply(auto)[1]
    apply(rule a_star_NotL)
    apply(auto)[1]
    done
next
  case a_NotR
  then show ?case 
    apply(auto)
    apply(rule a_star_NotR)
    apply(auto)[1]
    done
next
  case a_AndR_l
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_AndR)
    apply(auto)
    done
next
  case a_AndR_r
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_AndR)
    apply(auto)
    done
next
  case a_AndL1
  then show ?case 
    apply(auto)
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutR)
    apply(rule a_star_AndL1)
    apply(auto)[1]
    apply(rule a_star_AndL1)
    apply(auto)[1]
    done
next
  case a_AndL2
  then show ?case 
    apply(auto)
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutR)
    apply(rule a_star_AndL2)
    apply(auto)[1]
    apply(rule a_star_AndL2)
    apply(auto)[1]
    done
next
  case a_OrR1
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_OrR1)
    apply(auto)
    done
next
  case a_OrR2
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_OrR2)
    apply(auto)
    done
next
  case a_OrL_l
  then show ?case 
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutR)
    apply(rule a_star_OrL)
    apply(auto)
    apply(rule a_star_OrL)
    apply(auto)
    done
next
  case a_OrL_r
  then show ?case 
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutR)
    apply(rule a_star_OrL)
    apply(auto)
    apply(rule a_star_OrL)
    apply(auto)
    done
next
  case a_ImpR
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_ImpR)
    apply(auto)
    done
next
  case a_ImpL_r
  then show ?case 
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutR)
    apply(rule a_star_ImpL)
    apply(auto)
    apply(rule a_star_ImpL)
    apply(auto)
    done
next
  case a_ImpL_l
  then show ?case 
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(generate_fresh "name")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutR)
    apply(rule a_star_ImpL)
    apply(auto)
    apply(rule a_star_ImpL)
    apply(auto)
    done
qed

lemma a_redu_subst2:
  assumes a: "M \<longrightarrow>\<^isub>a M'"
  shows "M{c:=(y).P} \<longrightarrow>\<^isub>a* M'{c:=(y).P}"
using a
proof(nominal_induct avoiding: y c P rule: a_redu.strong_induct)
  case al_redu
  then show ?case by (simp only: l_redu_subst2)
next
  case ac_redu
  then show ?case
    apply -
    apply(rule a_starI)
    apply(rule a_redu.ac_redu)
    apply(simp only: c_redu_subst2')
    done
next
  case (a_Cut_r a N x M M' y c P)
  then show ?case
    apply(simp add: subst_fresh fresh_a_redu)
    apply(rule conjI)
    apply(rule impI)+
    apply(simp)
    apply(drule ax_do_not_a_reduce)
    apply(simp)
    apply(rule impI)
    apply(rule conjI)
    apply(rule impI)
    apply(simp)
    apply(drule_tac x="c" in meta_spec)
    apply(drule_tac x="y" in meta_spec)
    apply(drule_tac x="P" in meta_spec)
    apply(simp)
    apply(rule a_star_trans)
    apply(rule a_star_CutR)
    apply(assumption)
    apply(rule a_star_trans)
    apply(rule_tac N'="P[y\<turnstile>n>x]" in a_star_CutR)
    apply(case_tac "fin P y")
    apply(rule a_starI)
    apply(rule al_redu)
    apply(rule better_LAxL_intro)
    apply(simp)
    apply(rule a_star_trans)
    apply(rule a_starI)
    apply(rule ac_redu)
    apply(rule better_right)
    apply(simp)
    apply(rule subst_with_ax1)
    apply(rule aux4)
    apply(simp add: trm.inject)
    apply(simp add: alpha fresh_atm)
    apply(simp add: nrename_swap)
    apply(rule impI)
    apply(rule a_star_CutR)
    apply(auto)
    done
next
  case (a_Cut_l a N x M M' y c P)
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_CutL)
    apply(auto)[1]
    apply(rule a_star_CutL)
    apply(auto)[1]
    done
next
  case a_NotR
  then show ?case 
    apply(auto)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutL)
    apply(rule a_star_NotR)
    apply(auto)[1]
    apply(rule a_star_NotR)
    apply(auto)[1]
    done
next
  case a_NotL
  then show ?case 
    apply(auto)
    apply(rule a_star_NotL)
    apply(auto)[1]
    done
next
  case a_AndR_l
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutL)
    apply(rule a_star_AndR)
    apply(auto)
    apply(rule a_star_AndR)
    apply(auto)
    done
next
  case a_AndR_r
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutL)
    apply(rule a_star_AndR)
    apply(auto)
    apply(rule a_star_AndR)
    apply(auto)
    done
next
  case a_AndL1
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_AndL1)
    apply(auto)
    done
next
  case a_AndL2
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_AndL2)
    apply(auto)
    done
next
  case a_OrR1
  then show ?case 
    apply(auto)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutL)
    apply(rule a_star_OrR1)
    apply(auto)[1]
    apply(rule a_star_OrR1)
    apply(auto)[1]
    done
next
  case a_OrR2
  then show ?case 
    apply(auto)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutL)
    apply(rule a_star_OrR2)
    apply(auto)[1]
    apply(rule a_star_OrR2)
    apply(auto)[1]
    done
next
  case a_OrL_l
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_OrL)
    apply(auto)
    done
next
  case a_OrL_r
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_OrL)
    apply(auto)
    done
next
  case a_ImpR
  then show ?case 
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(generate_fresh "coname")
    apply(fresh_fun_simp)
    apply(fresh_fun_simp)
    apply(simp add: subst_fresh)
    apply(rule a_star_CutL)
    apply(rule a_star_ImpR)
    apply(auto)
    apply(rule a_star_ImpR)
    apply(auto)
    done
next
  case a_ImpL_l
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_ImpL)
    apply(auto)
    done
next
  case a_ImpL_r
  then show ?case
    apply(auto simp add: subst_fresh fresh_a_redu)
    apply(rule a_star_ImpL)
    apply(auto)
    done
qed

lemma a_star_subst1:
  assumes a: "M \<longrightarrow>\<^isub>a* M'"
  shows "M{y:=<c>.P} \<longrightarrow>\<^isub>a* M'{y:=<c>.P}"
using a
apply(induct)
apply(blast)
apply(drule_tac y="y" and c="c" and P="P" in a_redu_subst1)
apply(auto)
done

lemma a_star_subst2:
  assumes a: "M \<longrightarrow>\<^isub>a* M'"
  shows "M{c:=(y).P} \<longrightarrow>\<^isub>a* M'{c:=(y).P}"
using a
apply(induct)
apply(blast)
apply(drule_tac y="y" and c="c" and P="P" in a_redu_subst2)
apply(auto)
done

text {* Candidates and SN *}

text {* SNa *}

inductive 
  SNa :: "trm \<Rightarrow> bool"
where
  SNaI: "(\<And>M'. M \<longrightarrow>\<^isub>a M' \<Longrightarrow> SNa M') \<Longrightarrow> SNa M"

lemma SNa_induct[consumes 1]:
  assumes major: "SNa M"
  assumes hyp: "\<And>M'. SNa M' \<Longrightarrow> (\<forall>M''. M'\<longrightarrow>\<^isub>a M'' \<longrightarrow> P M'' \<Longrightarrow> P M')"
  shows "P M"
  apply (rule major[THEN SNa.induct])
  apply (rule hyp)
  apply (rule SNaI)
  apply (blast)+
  done


lemma double_SNa_aux:
  assumes a_SNa: "SNa a"
  and b_SNa: "SNa b"
  and hyp: "\<And>x z.
    (\<And>y. x\<longrightarrow>\<^isub>a y \<Longrightarrow> SNa y) \<Longrightarrow>
    (\<And>y. x\<longrightarrow>\<^isub>a y \<Longrightarrow> P y z) \<Longrightarrow>
    (\<And>u. z\<longrightarrow>\<^isub>a u \<Longrightarrow> SNa u) \<Longrightarrow>
    (\<And>u. z\<longrightarrow>\<^isub>a u \<Longrightarrow> P x u) \<Longrightarrow> P x z"
  shows "P a b"
proof -
  from a_SNa
  have r: "\<And>b. SNa b \<Longrightarrow> P a b"
  proof (induct a rule: SNa.induct)
    case (SNaI x)
    note SNa' = this
    have "SNa b" by fact
    thus ?case
    proof (induct b rule: SNa.induct)
      case (SNaI y)
      show ?case
        apply (rule hyp)
        apply (erule SNa')
        apply (erule SNa')
        apply (rule SNa.SNaI)
        apply (erule SNaI)+
        done
    qed
  qed
  from b_SNa show ?thesis by (rule r)
qed

lemma double_SNa:
  "\<lbrakk>SNa a; SNa b; \<forall>x z. ((\<forall>y. x\<longrightarrow>\<^isub>ay \<longrightarrow> P y z) \<and> (\<forall>u. z\<longrightarrow>\<^isub>a u \<longrightarrow> P x u)) \<longrightarrow> P x z\<rbrakk> \<Longrightarrow> P a b"
apply(rule_tac double_SNa_aux)
apply(assumption)+
apply(blast)
done

lemma a_preserves_SNa:
  assumes a: "SNa M" "M\<longrightarrow>\<^isub>a M'"
  shows "SNa M'"
using a 
by (erule_tac SNa.cases) (simp)

lemma a_star_preserves_SNa:
  assumes a: "SNa M" and b: "M\<longrightarrow>\<^isub>a* M'"
  shows "SNa M'"
using b a
by (induct) (auto simp add: a_preserves_SNa)

lemma Ax_in_SNa:
  shows "SNa (Ax x a)"
apply(rule SNaI)
apply(erule a_redu.cases, auto)
apply(erule l_redu.cases, auto)
apply(erule c_redu.cases, auto)
done

lemma NotL_in_SNa:
  assumes a: "SNa M"
  shows "SNa (NotL <a>.M x)"
using a
apply(induct)
apply(rule SNaI)
apply(erule a_redu.cases, auto)
apply(erule l_redu.cases, auto)
apply(erule c_redu.cases, auto)
apply(auto simp add: trm.inject alpha)
apply(rotate_tac 1)
apply(drule_tac x="[(a,aa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(subgoal_tac "NotL <a>.([(a,aa)]\<bullet>M'a) x = NotL <aa>.M'a x")
apply(simp)
apply(simp add: trm.inject alpha fresh_a_redu)
done

lemma NotR_in_SNa:
  assumes a: "SNa M"
  shows "SNa (NotR (x).M a)"
using a
apply(induct)
apply(rule SNaI)
apply(erule a_redu.cases, auto)
apply(erule l_redu.cases, auto)
apply(erule c_redu.cases, auto)
apply(auto simp add: trm.inject alpha)
apply(rotate_tac 1)
apply(drule_tac x="[(x,xa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(rule_tac s="NotR (x).([(x,xa)]\<bullet>M'a) a" in subst)
apply(simp add: trm.inject alpha fresh_a_redu)
apply(simp)
done

lemma AndL1_in_SNa:
  assumes a: "SNa M"
  shows "SNa (AndL1 (x).M y)"
using a
apply(induct)
apply(rule SNaI)
apply(erule a_redu.cases, auto)
apply(erule l_redu.cases, auto)
apply(erule c_redu.cases, auto)
apply(auto simp add: trm.inject alpha)
apply(rotate_tac 1)
apply(drule_tac x="[(x,xa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(rule_tac s="AndL1 x.([(x,xa)]\<bullet>M'a) y" in subst)
apply(simp add: trm.inject alpha fresh_a_redu)
apply(simp)
done

lemma AndL2_in_SNa:
  assumes a: "SNa M"
  shows "SNa (AndL2 (x).M y)"
using a
apply(induct)
apply(rule SNaI)
apply(erule a_redu.cases, auto)
apply(erule l_redu.cases, auto)
apply(erule c_redu.cases, auto)
apply(auto simp add: trm.inject alpha)
apply(rotate_tac 1)
apply(drule_tac x="[(x,xa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(rule_tac s="AndL2 x.([(x,xa)]\<bullet>M'a) y" in subst)
apply(simp add: trm.inject alpha fresh_a_redu)
apply(simp)
done

lemma OrR1_in_SNa:
  assumes a: "SNa M"
  shows "SNa (OrR1 <a>.M b)"
using a
apply(induct)
apply(rule SNaI)
apply(erule a_redu.cases, auto)
apply(erule l_redu.cases, auto)
apply(erule c_redu.cases, auto)
apply(auto simp add: trm.inject alpha)
apply(rotate_tac 1)
apply(drule_tac x="[(a,aa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(rule_tac s="OrR1 <a>.([(a,aa)]\<bullet>M'a) b" in subst)
apply(simp add: trm.inject alpha fresh_a_redu)
apply(simp)
done

lemma OrR2_in_SNa:
  assumes a: "SNa M"
  shows "SNa (OrR2 <a>.M b)"
using a
apply(induct)
apply(rule SNaI)
apply(erule a_redu.cases, auto)
apply(erule l_redu.cases, auto)
apply(erule c_redu.cases, auto)
apply(auto simp add: trm.inject alpha)
apply(rotate_tac 1)
apply(drule_tac x="[(a,aa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(rule_tac s="OrR2 <a>.([(a,aa)]\<bullet>M'a) b" in subst)
apply(simp add: trm.inject alpha fresh_a_redu)
apply(simp)
done

lemma ImpR_in_SNa:
  assumes a: "SNa M"
  shows "SNa (ImpR (x).<a>.M b)"
using a
apply(induct)
apply(rule SNaI)
apply(erule a_redu.cases, auto)
apply(erule l_redu.cases, auto)
apply(erule c_redu.cases, auto)
apply(auto simp add: trm.inject alpha abs_fresh abs_perm calc_atm)
apply(rotate_tac 1)
apply(drule_tac x="[(a,aa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(rule_tac s="ImpR (x).<a>.([(a,aa)]\<bullet>M'a) b" in subst)
apply(simp add: trm.inject alpha fresh_a_redu)
apply(simp)
apply(rotate_tac 1)
apply(drule_tac x="[(x,xa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(rule_tac s="ImpR (x).<a>.([(x,xa)]\<bullet>M'a) b" in subst)
apply(simp add: trm.inject alpha fresh_a_redu abs_fresh abs_perm calc_atm)
apply(simp)
apply(rotate_tac 1)
apply(drule_tac x="[(a,aa)]\<bullet>[(x,xa)]\<bullet>M'a" in meta_spec)
apply(simp add: a_redu.eqvt)
apply(rule_tac s="ImpR (x).<a>.([(a,aa)]\<bullet>[(x,xa)]\<bullet>M'a) b" in subst)
apply(simp add: trm.inject alpha fresh_a_redu abs_fresh abs_perm calc_atm)
apply(simp add: fresh_left calc_atm fresh_a_redu)
apply(simp)
done

lemma AndR_in_SNa:
  assumes a: "SNa M" "SNa N"
  shows "SNa (AndR <a>.M <b>.N c)"
apply(rule_tac a="M" and b="N" in double_SNa)
apply(rule a)+
apply(auto)
apply(rule SNaI)
apply(drule a_redu_AndR_elim)
apply(auto)
done

lemma OrL_in_SNa:
  assumes a: "SNa M" "SNa N"
  shows "SNa (OrL (x).M (y).N z)"
apply(rule_tac a="M" and b="N" in double_SNa)
apply(rule a)+
apply(auto)
apply(rule SNaI)
apply(drule a_redu_OrL_elim)
apply(auto)
done

lemma ImpL_in_SNa:
  assumes a: "SNa M" "SNa N"
  shows "SNa (ImpL <a>.M (y).N z)"
apply(rule_tac a="M" and b="N" in double_SNa)
apply(rule a)+
apply(auto)
apply(rule SNaI)
apply(drule a_redu_ImpL_elim)
apply(auto)
done

lemma SNa_eqvt:
  fixes pi1::"name prm"
  and   pi2::"coname prm"
  shows "SNa M \<Longrightarrow> SNa (pi1\<bullet>M)"
  and   "SNa M \<Longrightarrow> SNa (pi2\<bullet>M)"
apply -
apply(induct rule: SNa.induct)
apply(rule SNaI)
apply(drule_tac pi="(rev pi1)" in a_redu.eqvt(1))
apply(rotate_tac 1)
apply(drule_tac x="(rev pi1)\<bullet>M'" in meta_spec)
apply(perm_simp)
apply(induct rule: SNa.induct)
apply(rule SNaI)
apply(drule_tac pi="(rev pi2)" in a_redu.eqvt(2))
apply(rotate_tac 1)
apply(drule_tac x="(rev pi2)\<bullet>M'" in meta_spec)
apply(perm_simp)
done

text {* set operators *}

definition AXIOMSn :: "ty \<Rightarrow> ntrm set" where
  "AXIOMSn B \<equiv> { (x):(Ax y b) | x y b. True }"

definition AXIOMSc::"ty \<Rightarrow> ctrm set" where
  "AXIOMSc B \<equiv> { <a>:(Ax y b) | a y b. True }"

definition BINDINGn::"ty \<Rightarrow> ctrm set \<Rightarrow> ntrm set" where
  "BINDINGn B X \<equiv> { (x):M | x M. \<forall>a P. <a>:P\<in>X \<longrightarrow> SNa (M{x:=<a>.P})}"

definition BINDINGc::"ty \<Rightarrow> ntrm set \<Rightarrow> ctrm set" where
  "BINDINGc B X \<equiv> { <a>:M | a M. \<forall>x P. (x):P\<in>X \<longrightarrow> SNa (M{a:=(x).P})}"

lemma BINDINGn_decreasing:
  shows "X\<subseteq>Y \<Longrightarrow> BINDINGn B Y \<subseteq> BINDINGn B X"
by (simp add: BINDINGn_def) (blast) 

lemma BINDINGc_decreasing:
  shows "X\<subseteq>Y \<Longrightarrow> BINDINGc B Y \<subseteq> BINDINGc B X"
by (simp add: BINDINGc_def) (blast) 
  
nominal_primrec
  NOTRIGHT :: "ty \<Rightarrow> ntrm set \<Rightarrow> ctrm set"
where
 "NOTRIGHT (NOT B) X = { <a>:NotR (x).M a | a x M. fic (NotR (x).M a) a \<and> (x):M \<in> X }"
apply(rule TrueI)+
done

lemma NOTRIGHT_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(NOTRIGHT (NOT B) X)) = NOTRIGHT (NOT B) (pi\<bullet>X)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>a" in exI) 
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(1))
apply(simp)
apply(rule_tac x="(xb):M" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>(<a>:NotR (xa).M a)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fic.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: swap_simps)
done

lemma NOTRIGHT_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(NOTRIGHT (NOT B) X)) = NOTRIGHT (NOT B) (pi\<bullet>X)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>a" in exI) 
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(2))
apply(simp)
apply(rule_tac x="(xb):M" in exI)
apply(simp)
apply(rule_tac x="<((rev pi)\<bullet>a)>:NotR ((rev pi)\<bullet>xa).((rev pi)\<bullet>M) ((rev pi)\<bullet>a)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fic.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: swap_simps)
done
  
nominal_primrec
  NOTLEFT :: "ty \<Rightarrow> ctrm set \<Rightarrow> ntrm set"
where
 "NOTLEFT (NOT B) X = { (x):NotL <a>.M x | a x M. fin (NotL <a>.M x) x \<and> <a>:M \<in> X }"
apply(rule TrueI)+
done

lemma NOTLEFT_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(NOTLEFT (NOT B) X)) = NOTLEFT (NOT B) (pi\<bullet>X)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>a" in exI) 
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(1))
apply(simp)
apply(rule_tac x="<a>:M" in exI)
apply(simp)
apply(rule_tac x="(((rev pi)\<bullet>xa)):NotL <((rev pi)\<bullet>a)>.((rev pi)\<bullet>M) ((rev pi)\<bullet>xa)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fin.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: swap_simps)
done

lemma NOTLEFT_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(NOTLEFT (NOT B) X)) = NOTLEFT (NOT B) (pi\<bullet>X)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>a" in exI) 
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(2))
apply(simp)
apply(rule_tac x="<a>:M" in exI)
apply(simp)
apply(rule_tac x="(((rev pi)\<bullet>xa)):NotL <((rev pi)\<bullet>a)>.((rev pi)\<bullet>M) ((rev pi)\<bullet>xa)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fin.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: swap_simps)
done
  
nominal_primrec
  ANDRIGHT :: "ty \<Rightarrow> ctrm set \<Rightarrow> ctrm set \<Rightarrow> ctrm set"
where
 "ANDRIGHT (B AND C) X Y = 
            { <c>:AndR <a>.M <b>.N c | c a b M N. fic (AndR <a>.M <b>.N c) c \<and> <a>:M \<in> X \<and> <b>:N \<in> Y }"
apply(rule TrueI)+
done

lemma ANDRIGHT_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(ANDRIGHT (A AND B) X Y)) = ANDRIGHT (A AND B) (pi\<bullet>X) (pi\<bullet>Y)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>c" in exI)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>b" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(rule_tac x="pi\<bullet>N" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(1))
apply(simp)
apply(rule conjI)
apply(rule_tac x="<a>:M" in exI)
apply(simp)
apply(rule_tac x="<b>:N" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>(<c>:AndR <a>.M <b>.N c)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>c" in exI)
apply(rule_tac x="(rev pi)\<bullet>a" in exI)
apply(rule_tac x="(rev pi)\<bullet>b" in exI)
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(rule_tac x="(rev pi)\<bullet>N" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fic.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: swap_simps)
done

lemma ANDRIGHT_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(ANDRIGHT (A AND B) X Y)) = ANDRIGHT (A AND B) (pi\<bullet>X) (pi\<bullet>Y)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>c" in exI)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>b" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(rule_tac x="pi\<bullet>N" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(2))
apply(simp)
apply(rule conjI)
apply(rule_tac x="<a>:M" in exI)
apply(simp)
apply(rule_tac x="<b>:N" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>(<c>:AndR <a>.M <b>.N c)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>c" in exI)
apply(rule_tac x="(rev pi)\<bullet>a" in exI)
apply(rule_tac x="(rev pi)\<bullet>b" in exI)
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(rule_tac x="(rev pi)\<bullet>N" in exI)
apply(simp)
apply(drule_tac pi="rev pi" in fic.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp)
done

nominal_primrec
  ANDLEFT1 :: "ty \<Rightarrow> ntrm set \<Rightarrow> ntrm set"
where
 "ANDLEFT1 (B AND C) X = { (y):AndL1 (x).M y | x y M. fin (AndL1 (x).M y) y \<and> (x):M \<in> X }"
apply(rule TrueI)+
done

lemma ANDLEFT1_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(ANDLEFT1 (A AND B) X)) = ANDLEFT1 (A AND B) (pi\<bullet>X)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>y" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(1))
apply(simp)
apply(rule_tac x="(xb):M" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>((y):AndL1 (xa).M y)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>y" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp)
apply(drule_tac pi="rev pi" in fin.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp)
done

lemma ANDLEFT1_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(ANDLEFT1 (A AND B) X)) = ANDLEFT1 (A AND B) (pi\<bullet>X)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>y" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(2))
apply(simp)
apply(rule_tac x="(xb):M" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>((y):AndL1 (xa).M y)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>y" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fin.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: swap_simps)
done

nominal_primrec
  ANDLEFT2 :: "ty \<Rightarrow> ntrm set \<Rightarrow> ntrm set"
where
 "ANDLEFT2 (B AND C) X = { (y):AndL2 (x).M y | x y M. fin (AndL2 (x).M y) y \<and> (x):M \<in> X }"
apply(rule TrueI)+
done

lemma ANDLEFT2_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(ANDLEFT2 (A AND B) X)) = ANDLEFT2 (A AND B) (pi\<bullet>X)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>y" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(1))
apply(simp)
apply(rule_tac x="(xb):M" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>((y):AndL2 (xa).M y)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>y" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp)
apply(drule_tac pi="rev pi" in fin.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp)
done

lemma ANDLEFT2_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(ANDLEFT2 (A AND B) X)) = ANDLEFT2 (A AND B) (pi\<bullet>X)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>y" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(2))
apply(simp)
apply(rule_tac x="(xb):M" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>((y):AndL2 (xa).M y)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>y" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fin.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: swap_simps)
done

nominal_primrec
  ORLEFT :: "ty \<Rightarrow> ntrm set \<Rightarrow> ntrm set \<Rightarrow> ntrm set"
where
 "ORLEFT (B OR C) X Y = 
            { (z):OrL (x).M (y).N z | x y z M N. fin (OrL (x).M (y).N z) z \<and> (x):M \<in> X \<and> (y):N \<in> Y }"
apply(rule TrueI)+
done

lemma ORLEFT_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(ORLEFT (A OR B) X Y)) = ORLEFT (A OR B) (pi\<bullet>X) (pi\<bullet>Y)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>xb" in exI)
apply(rule_tac x="pi\<bullet>y" in exI)
apply(rule_tac x="pi\<bullet>z" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(rule_tac x="pi\<bullet>N" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(1))
apply(simp)
apply(rule conjI)
apply(rule_tac x="(xb):M" in exI)
apply(simp)
apply(rule_tac x="(y):N" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>((z):OrL (xa).M (y).N z)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI)
apply(rule_tac x="(rev pi)\<bullet>y" in exI)
apply(rule_tac x="(rev pi)\<bullet>z" in exI)
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(rule_tac x="(rev pi)\<bullet>N" in exI)
apply(simp)
apply(drule_tac pi="rev pi" in fin.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp)
done

lemma ORLEFT_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(ORLEFT (A OR B) X Y)) = ORLEFT (A OR B) (pi\<bullet>X) (pi\<bullet>Y)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>xb" in exI)
apply(rule_tac x="pi\<bullet>y" in exI)
apply(rule_tac x="pi\<bullet>z" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(rule_tac x="pi\<bullet>N" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(2))
apply(simp)
apply(rule conjI)
apply(rule_tac x="(xb):M" in exI)
apply(simp)
apply(rule_tac x="(y):N" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>((z):OrL (xa).M (y).N z)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI)
apply(rule_tac x="(rev pi)\<bullet>y" in exI)
apply(rule_tac x="(rev pi)\<bullet>z" in exI)
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(rule_tac x="(rev pi)\<bullet>N" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fin.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: swap_simps)
done

nominal_primrec
  ORRIGHT1 :: "ty \<Rightarrow> ctrm set \<Rightarrow> ctrm set"
where
 "ORRIGHT1 (B OR C) X = { <b>:OrR1 <a>.M b | a b M. fic (OrR1 <a>.M b) b \<and> <a>:M \<in> X }"
apply(rule TrueI)+
done

lemma ORRIGHT1_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(ORRIGHT1 (A OR B) X)) = ORRIGHT1 (A OR B) (pi\<bullet>X)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>a" in exI) 
apply(rule_tac x="pi\<bullet>b" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(1))
apply(simp)
apply(rule_tac x="<a>:M" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>(<b>:OrR1 <a>.M b)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>b" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fic.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: swap_simps)
done

lemma ORRIGHT1_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(ORRIGHT1 (A OR B) X)) = ORRIGHT1 (A OR B) (pi\<bullet>X)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>a" in exI) 
apply(rule_tac x="pi\<bullet>b" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(2))
apply(simp)
apply(rule_tac x="<a>:M" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>(<b>:OrR1 <a>.M b)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>b" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp)
apply(drule_tac pi="rev pi" in fic.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp)
done

nominal_primrec
  ORRIGHT2 :: "ty \<Rightarrow> ctrm set \<Rightarrow> ctrm set"
where
 "ORRIGHT2 (B OR C) X = { <b>:OrR2 <a>.M b | a b M. fic (OrR2 <a>.M b) b \<and> <a>:M \<in> X }"
apply(rule TrueI)+
done

lemma ORRIGHT2_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(ORRIGHT2 (A OR B) X)) = ORRIGHT2 (A OR B) (pi\<bullet>X)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>a" in exI) 
apply(rule_tac x="pi\<bullet>b" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(1))
apply(simp)
apply(rule_tac x="<a>:M" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>(<b>:OrR2 <a>.M b)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>b" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fic.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: swap_simps)
done

lemma ORRIGHT2_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(ORRIGHT2 (A OR B) X)) = ORRIGHT2 (A OR B) (pi\<bullet>X)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>a" in exI) 
apply(rule_tac x="pi\<bullet>b" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(2))
apply(simp)
apply(rule_tac x="<a>:M" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>(<b>:OrR2 <a>.M b)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>b" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp)
apply(drule_tac pi="rev pi" in fic.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp)
done

nominal_primrec
  IMPRIGHT :: "ty \<Rightarrow> ntrm set \<Rightarrow> ctrm set \<Rightarrow> ntrm set \<Rightarrow> ctrm set \<Rightarrow> ctrm set"
where
 "IMPRIGHT (B IMP C) X Y Z U= 
        { <b>:ImpR (x).<a>.M b | x a b M. fic (ImpR (x).<a>.M b) b 
                                        \<and> (\<forall>z P. x\<sharp>(z,P) \<and> (z):P \<in> Z \<longrightarrow> (x):(M{a:=(z).P}) \<in> X)
                                        \<and> (\<forall>c Q. a\<sharp>(c,Q) \<and> <c>:Q \<in> U \<longrightarrow> <a>:(M{x:=<c>.Q}) \<in> Y)}"
apply(rule TrueI)+
done

lemma IMPRIGHT_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(IMPRIGHT (A IMP B) X Y Z U)) = IMPRIGHT (A IMP B) (pi\<bullet>X) (pi\<bullet>Y) (pi\<bullet>Z) (pi\<bullet>U)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>xb" in exI)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>b" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(1))
apply(simp)
apply(rule conjI)
apply(auto)[1]
apply(rule_tac x="(xb):(M{a:=((rev pi)\<bullet>z).((rev pi)\<bullet>P)})" in exI)
apply(perm_simp add: csubst_eqvt)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp)
apply(simp add: fresh_right)
apply(auto)[1]
apply(rule_tac x="<a>:(M{xb:=<((rev pi)\<bullet>c)>.((rev pi)\<bullet>Q)})" in exI)
apply(perm_simp add: nsubst_eqvt)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: swap_simps fresh_left)
apply(rule_tac x="(rev pi)\<bullet>(<b>:ImpR xa.<a>.M b)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI)
apply(rule_tac x="(rev pi)\<bullet>a" in exI)
apply(rule_tac x="(rev pi)\<bullet>b" in exI)
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fic.eqvt(1))
apply(simp add: swap_simps)
apply(rule conjI)
apply(auto)[1]
apply(drule_tac x="pi\<bullet>z" in spec)
apply(drule_tac x="pi\<bullet>P" in spec)
apply(drule mp)
apply(simp add: fresh_right)
apply(rule_tac x="(z):P" in exI)
apply(simp)
apply(auto)[1]
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: csubst_eqvt fresh_right)
apply(auto)[1]
apply(drule_tac x="pi\<bullet>c" in spec)
apply(drule_tac x="pi\<bullet>Q" in spec)
apply(drule mp)
apply(simp add: swap_simps fresh_left)
apply(rule_tac x="<c>:Q" in exI)
apply(simp add: swap_simps)
apply(auto)[1]
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: nsubst_eqvt)
done

lemma IMPRIGHT_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(IMPRIGHT (A IMP B) X Y Z U)) = IMPRIGHT (A IMP B) (pi\<bullet>X) (pi\<bullet>Y) (pi\<bullet>Z) (pi\<bullet>U)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>xb" in exI)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>b" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fic.eqvt(2))
apply(simp)
apply(rule conjI)
apply(auto)[1]
apply(rule_tac x="(xb):(M{a:=((rev pi)\<bullet>z).((rev pi)\<bullet>P)})" in exI)
apply(perm_simp add: csubst_eqvt)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: swap_simps fresh_left)
apply(auto)[1]
apply(rule_tac x="<a>:(M{xb:=<((rev pi)\<bullet>c)>.((rev pi)\<bullet>Q)})" in exI)
apply(perm_simp add: nsubst_eqvt)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: fresh_right)
apply(rule_tac x="(rev pi)\<bullet>(<b>:ImpR xa.<a>.M b)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI)
apply(rule_tac x="(rev pi)\<bullet>a" in exI)
apply(rule_tac x="(rev pi)\<bullet>b" in exI)
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fic.eqvt(2))
apply(simp add: swap_simps)
apply(rule conjI)
apply(auto)[1]
apply(drule_tac x="pi\<bullet>z" in spec)
apply(drule_tac x="pi\<bullet>P" in spec)
apply(simp add: swap_simps fresh_left)
apply(drule mp)
apply(rule_tac x="(z):P" in exI)
apply(simp add: swap_simps)
apply(auto)[1]
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: csubst_eqvt fresh_right)
apply(auto)[1]
apply(drule_tac x="pi\<bullet>c" in spec)
apply(drule_tac x="pi\<bullet>Q" in spec)
apply(simp add: fresh_right)
apply(drule mp)
apply(rule_tac x="<c>:Q" in exI)
apply(simp)
apply(auto)[1]
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: nsubst_eqvt fresh_right)
done

nominal_primrec
  IMPLEFT :: "ty \<Rightarrow> ctrm set \<Rightarrow> ntrm set \<Rightarrow> ntrm set"
where
 "IMPLEFT (B IMP C) X Y = 
        { (y):ImpL <a>.M (x).N y | x a y M N. fin (ImpL <a>.M (x).N y) y \<and> <a>:M \<in> X \<and> (x):N \<in> Y }"
apply(rule TrueI)+
done

lemma IMPLEFT_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(IMPLEFT (A IMP B) X Y)) = IMPLEFT (A IMP B) (pi\<bullet>X) (pi\<bullet>Y)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>y" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI) 
apply(rule_tac x="pi\<bullet>N" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(1))
apply(simp)
apply(rule conjI)
apply(rule_tac x="<a>:M" in exI)
apply(simp)
apply(rule_tac x="(xb):N" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>((y):ImpL <a>.M (xa).N y)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>y" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(rule_tac x="(rev pi)\<bullet>N" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fin.eqvt(1))
apply(simp)
apply(drule sym)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: swap_simps)
done

lemma IMPLEFT_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(IMPLEFT (A IMP B) X Y)) = IMPLEFT (A IMP B) (pi\<bullet>X) (pi\<bullet>Y)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="pi\<bullet>xb" in exI) 
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>y" in exI) 
apply(rule_tac x="pi\<bullet>M" in exI) 
apply(rule_tac x="pi\<bullet>N" in exI)
apply(simp)
apply(rule conjI)
apply(drule_tac pi="pi" in fin.eqvt(2))
apply(simp)
apply(rule conjI)
apply(rule_tac x="<a>:M" in exI)
apply(simp)
apply(rule_tac x="(xb):N" in exI)
apply(simp)
apply(rule_tac x="(rev pi)\<bullet>((y):ImpL <a>.M (xa).N y)" in exI)
apply(perm_simp)
apply(rule_tac x="(rev pi)\<bullet>xa" in exI) 
apply(rule_tac x="(rev pi)\<bullet>a" in exI) 
apply(rule_tac x="(rev pi)\<bullet>y" in exI) 
apply(rule_tac x="(rev pi)\<bullet>M" in exI)
apply(rule_tac x="(rev pi)\<bullet>N" in exI)
apply(simp add: swap_simps)
apply(drule_tac pi="rev pi" in fin.eqvt(2))
apply(simp)
apply(drule sym)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: swap_simps)
done

lemma sum_cases:
 shows "(\<exists>y. x=Inl y) \<or> (\<exists>y. x=Inr y)"
apply(rule_tac s="x" in sumE)
apply(auto)
done

function
  NEGc::"ty \<Rightarrow> ntrm set \<Rightarrow> ctrm set"
and
  NEGn::"ty \<Rightarrow> ctrm set \<Rightarrow> ntrm set"
where
  "NEGc (PR A)    X = AXIOMSc (PR A) \<union> BINDINGc (PR A) X"  
| "NEGc (NOT C)   X = AXIOMSc (NOT C) \<union> BINDINGc (NOT C) X 
                         \<union> NOTRIGHT (NOT C) (lfp (NEGn C \<circ> NEGc C))"  
| "NEGc (C AND D) X = AXIOMSc (C AND D) \<union> BINDINGc (C AND D) X 
                     \<union> ANDRIGHT (C AND D) (NEGc C (lfp (NEGn C \<circ> NEGc C))) (NEGc D (lfp (NEGn D \<circ> NEGc D)))"
| "NEGc (C OR D)  X = AXIOMSc (C OR D) \<union> BINDINGc (C OR D) X  
                         \<union> ORRIGHT1 (C OR D) (NEGc C (lfp (NEGn C \<circ> NEGc C))) 
                         \<union> ORRIGHT2 (C OR D) (NEGc D (lfp (NEGn D \<circ> NEGc D)))"
| "NEGc (C IMP D) X = AXIOMSc (C IMP D) \<union> BINDINGc (C IMP D) X 
    \<union> IMPRIGHT (C IMP D) (lfp (NEGn C \<circ> NEGc C)) (NEGc D (lfp (NEGn D \<circ> NEGc D))) 
                          (lfp (NEGn D \<circ> NEGc D)) (NEGc C (lfp (NEGn C \<circ> NEGc C)))"
| "NEGn (PR A)    X = AXIOMSn (PR A) \<union> BINDINGn (PR A) X"   
| "NEGn (NOT C)   X = AXIOMSn (NOT C) \<union> BINDINGn (NOT C) X 
                         \<union> NOTLEFT (NOT C) (NEGc C (lfp (NEGn C \<circ> NEGc C)))"  
| "NEGn (C AND D) X = AXIOMSn (C AND D) \<union> BINDINGn (C AND D) X 
                         \<union> ANDLEFT1 (C AND D) (lfp (NEGn C \<circ> NEGc C)) 
                         \<union> ANDLEFT2 (C AND D) (lfp (NEGn D \<circ> NEGc D))"
| "NEGn (C OR D)  X = AXIOMSn (C OR D) \<union> BINDINGn (C OR D) X 
                         \<union> ORLEFT (C OR D) (lfp (NEGn C \<circ> NEGc C)) (lfp (NEGn D \<circ> NEGc D))"
| "NEGn (C IMP D) X = AXIOMSn (C IMP D) \<union> BINDINGn (C IMP D) X 
                         \<union> IMPLEFT (C IMP D) (NEGc C (lfp (NEGn C \<circ> NEGc C))) (lfp (NEGn D \<circ> NEGc D))"
using ty_cases sum_cases 
apply(auto simp add: ty.inject)
apply(drule_tac x="x" in meta_spec)
apply(auto simp add: ty.inject)
apply(rotate_tac 10)
apply(drule_tac x="a" in meta_spec)
apply(auto simp add: ty.inject)
apply(blast)
apply(blast)
apply(blast)
apply(rotate_tac 10)
apply(drule_tac x="a" in meta_spec)
apply(auto simp add: ty.inject)
apply(blast)
apply(blast)
apply(blast)
done

termination
apply(relation "measure (sum_case (size\<circ>fst) (size\<circ>fst))")
apply(simp_all)
done

text {* Candidates *}

lemma test1:
  shows "x\<in>(X\<union>Y) = (x\<in>X \<or> x\<in>Y)"
by blast

lemma test2:
  shows "x\<in>(X\<inter>Y) = (x\<in>X \<and> x\<in>Y)"
by blast

lemma big_inter_eqvt:
  fixes pi1::"name prm"
  and   X::"('a::pt_name) set set"
  and   pi2::"coname prm"
  and   Y::"('b::pt_coname) set set"
  shows "(pi1\<bullet>(\<Inter> X)) = \<Inter> (pi1\<bullet>X)"
  and   "(pi2\<bullet>(\<Inter> Y)) = \<Inter> (pi2\<bullet>Y)"
apply(auto simp add: perm_set_eq)
apply(rule_tac x="(rev pi1)\<bullet>x" in exI)
apply(perm_simp)
apply(rule ballI)
apply(drule_tac x="pi1\<bullet>xa" in spec)
apply(auto)
apply(drule_tac x="xa" in spec)
apply(auto)[1]
apply(rule_tac x="(rev pi1)\<bullet>xb" in exI)
apply(perm_simp)
apply(simp add: pt_set_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: pt_set_bij[OF pt_name_inst, OF at_name_inst])
apply(simp add: pt_set_bij1[OF pt_name_inst, OF at_name_inst])
apply(rule_tac x="(rev pi2)\<bullet>x" in exI)
apply(perm_simp)
apply(rule ballI)
apply(drule_tac x="pi2\<bullet>xa" in spec)
apply(auto)
apply(drule_tac x="xa" in spec)
apply(auto)[1]
apply(rule_tac x="(rev pi2)\<bullet>xb" in exI)
apply(perm_simp)
apply(simp add: pt_set_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: pt_set_bij[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: pt_set_bij1[OF pt_coname_inst, OF at_coname_inst])
done

lemma lfp_eqvt:
  fixes pi1::"name prm"
  and   f::"'a set \<Rightarrow> ('a::pt_name) set"
  and   pi2::"coname prm"
  and   g::"'b set \<Rightarrow> ('b::pt_coname) set"
  shows "pi1\<bullet>(lfp f) = lfp (pi1\<bullet>f)"
  and   "pi2\<bullet>(lfp g) = lfp (pi2\<bullet>g)"
apply(simp add: lfp_def)
apply(simp add: big_inter_eqvt)
apply(simp add: pt_Collect_eqvt[OF pt_name_inst, OF at_name_inst])
apply(subgoal_tac "{u. (pi1\<bullet>f) u \<subseteq> u} = {u. ((rev pi1)\<bullet>((pi1\<bullet>f) u)) \<subseteq> ((rev pi1)\<bullet>u)}")
apply(perm_simp)
apply(rule Collect_cong)
apply(rule iffI)
apply(rule subseteq_eqvt(1)[THEN iffD1])
apply(simp add: perm_bool)
apply(drule subseteq_eqvt(1)[THEN iffD2])
apply(simp add: perm_bool)
apply(simp add: lfp_def)
apply(simp add: big_inter_eqvt)
apply(simp add: pt_Collect_eqvt[OF pt_coname_inst, OF at_coname_inst])
apply(subgoal_tac "{u. (pi2\<bullet>g) u \<subseteq> u} = {u. ((rev pi2)\<bullet>((pi2\<bullet>g) u)) \<subseteq> ((rev pi2)\<bullet>u)}")
apply(perm_simp)
apply(rule Collect_cong)
apply(rule iffI)
apply(rule subseteq_eqvt(2)[THEN iffD1])
apply(simp add: perm_bool)
apply(drule subseteq_eqvt(2)[THEN iffD2])
apply(simp add: perm_bool)
done

abbreviation
  CANDn::"ty \<Rightarrow> ntrm set"  ("\<parallel>'(_')\<parallel>" [60] 60) 
where
  "\<parallel>(B)\<parallel> \<equiv> lfp (NEGn B \<circ> NEGc B)" 

abbreviation
  CANDc::"ty \<Rightarrow> ctrm set"  ("\<parallel><_>\<parallel>" [60] 60)
where
  "\<parallel><B>\<parallel> \<equiv> NEGc B (\<parallel>(B)\<parallel>)"

lemma NEGn_decreasing:
  shows "X\<subseteq>Y \<Longrightarrow> NEGn B Y \<subseteq> NEGn B X"
by (nominal_induct B rule: ty.strong_induct)
   (auto dest: BINDINGn_decreasing)

lemma NEGc_decreasing:
  shows "X\<subseteq>Y \<Longrightarrow> NEGc B Y \<subseteq> NEGc B X"
by (nominal_induct B rule: ty.strong_induct)
   (auto dest: BINDINGc_decreasing)

lemma mono_NEGn_NEGc:
  shows "mono (NEGn B \<circ> NEGc B)"
  and   "mono (NEGc B \<circ> NEGn B)"
proof -
  have "\<forall>X Y. X\<subseteq>Y \<longrightarrow> NEGn B (NEGc B X) \<subseteq> NEGn B (NEGc B Y)"
  proof (intro strip)
    fix X::"ntrm set" and Y::"ntrm set"
    assume "X\<subseteq>Y"
    then have "NEGc B Y \<subseteq> NEGc B X" by (simp add: NEGc_decreasing)
    then show "NEGn B (NEGc B X) \<subseteq> NEGn B (NEGc B Y)" by (simp add: NEGn_decreasing)
  qed
  then show "mono (NEGn B \<circ> NEGc B)" by (simp add: mono_def)
next
  have "\<forall>X Y. X\<subseteq>Y \<longrightarrow> NEGc B (NEGn B X) \<subseteq> NEGc B (NEGn B Y)"
  proof (intro strip)
    fix X::"ctrm set" and Y::"ctrm set"
    assume "X\<subseteq>Y"
    then have "NEGn B Y \<subseteq> NEGn B X" by (simp add: NEGn_decreasing)
    then show "NEGc B (NEGn B X) \<subseteq> NEGc B (NEGn B Y)" by (simp add: NEGc_decreasing)
  qed
  then show "mono (NEGc B \<circ> NEGn B)" by (simp add: mono_def)
qed

lemma NEG_simp:
  shows "\<parallel><B>\<parallel> = NEGc B (\<parallel>(B)\<parallel>)"
  and   "\<parallel>(B)\<parallel> = NEGn B (\<parallel><B>\<parallel>)"
proof -
  show "\<parallel><B>\<parallel> = NEGc B (\<parallel>(B)\<parallel>)" by simp
next
  have "\<parallel>(B)\<parallel> \<equiv> lfp (NEGn B \<circ> NEGc B)" by simp
  then have "\<parallel>(B)\<parallel> = (NEGn B \<circ> NEGc B) (\<parallel>(B)\<parallel>)" using mono_NEGn_NEGc def_lfp_unfold by blast
  then show "\<parallel>(B)\<parallel> = NEGn B (\<parallel><B>\<parallel>)" by simp
qed

lemma NEG_elim:
  shows "M \<in> \<parallel><B>\<parallel> \<Longrightarrow> M \<in> NEGc B (\<parallel>(B)\<parallel>)"
  and   "N \<in> \<parallel>(B)\<parallel> \<Longrightarrow> N \<in> NEGn B (\<parallel><B>\<parallel>)"
using NEG_simp by (blast)+

lemma NEG_intro:
  shows "M \<in> NEGc B (\<parallel>(B)\<parallel>) \<Longrightarrow> M \<in> \<parallel><B>\<parallel>"
  and   "N \<in> NEGn B (\<parallel><B>\<parallel>) \<Longrightarrow> N \<in> \<parallel>(B)\<parallel>"
using NEG_simp by (blast)+

lemma NEGc_simps:
  shows "NEGc (PR A) (\<parallel>(PR A)\<parallel>) = AXIOMSc (PR A) \<union> BINDINGc (PR A) (\<parallel>(PR A)\<parallel>)"  
  and   "NEGc (NOT C) (\<parallel>(NOT C)\<parallel>) = AXIOMSc (NOT C) \<union> BINDINGc (NOT C) (\<parallel>(NOT C)\<parallel>) 
                                        \<union> (NOTRIGHT (NOT C) (\<parallel>(C)\<parallel>))"  
  and   "NEGc (C AND D) (\<parallel>(C AND D)\<parallel>) = AXIOMSc (C AND D) \<union> BINDINGc (C AND D) (\<parallel>(C AND D)\<parallel>) 
                                        \<union> (ANDRIGHT (C AND D) (\<parallel><C>\<parallel>) (\<parallel><D>\<parallel>))"
  and   "NEGc (C OR D) (\<parallel>(C OR D)\<parallel>) = AXIOMSc (C OR D) \<union> BINDINGc (C OR D)  (\<parallel>(C OR D)\<parallel>)
                                        \<union> (ORRIGHT1 (C OR D) (\<parallel><C>\<parallel>)) \<union> (ORRIGHT2 (C OR D) (\<parallel><D>\<parallel>))"
  and   "NEGc (C IMP D) (\<parallel>(C IMP D)\<parallel>) = AXIOMSc (C IMP D) \<union> BINDINGc (C IMP D) (\<parallel>(C IMP D)\<parallel>) 
          \<union> (IMPRIGHT (C IMP D) (\<parallel>(C)\<parallel>) (\<parallel><D>\<parallel>) (\<parallel>(D)\<parallel>) (\<parallel><C>\<parallel>))"
by (simp_all only: NEGc.simps)

lemma AXIOMS_in_CANDs:
  shows "AXIOMSn B \<subseteq> (\<parallel>(B)\<parallel>)"
  and   "AXIOMSc B \<subseteq> (\<parallel><B>\<parallel>)"
proof -
  have "AXIOMSn B \<subseteq> NEGn B (\<parallel><B>\<parallel>)"
    by (nominal_induct B rule: ty.strong_induct) (auto)
  then show "AXIOMSn B \<subseteq> \<parallel>(B)\<parallel>" using NEG_simp by blast
next
  have "AXIOMSc B \<subseteq> NEGc B (\<parallel>(B)\<parallel>)"
    by (nominal_induct B rule: ty.strong_induct) (auto)
  then show "AXIOMSc B \<subseteq> \<parallel><B>\<parallel>" using NEG_simp by blast
qed

lemma Ax_in_CANDs:
  shows "(y):Ax x a \<in> \<parallel>(B)\<parallel>"
  and   "<b>:Ax x a \<in> \<parallel><B>\<parallel>"
proof -
  have "(y):Ax x a \<in> AXIOMSn B" by (auto simp add: AXIOMSn_def)
  also have "AXIOMSn B \<subseteq> \<parallel>(B)\<parallel>" by (rule AXIOMS_in_CANDs)
  finally show "(y):Ax x a \<in> \<parallel>(B)\<parallel>" by simp
next
  have "<b>:Ax x a \<in> AXIOMSc B" by (auto simp add: AXIOMSc_def)
  also have "AXIOMSc B \<subseteq> \<parallel><B>\<parallel>" by (rule AXIOMS_in_CANDs)
  finally show "<b>:Ax x a \<in> \<parallel><B>\<parallel>" by simp
qed

lemma AXIOMS_eqvt_aux_name:
  fixes pi::"name prm"
  shows "M \<in> AXIOMSn B \<Longrightarrow> (pi\<bullet>M) \<in> AXIOMSn B" 
  and   "N \<in> AXIOMSc B \<Longrightarrow> (pi\<bullet>N) \<in> AXIOMSc B"
apply(auto simp add: AXIOMSn_def AXIOMSc_def)
apply(rule_tac x="pi\<bullet>x" in exI)
apply(rule_tac x="pi\<bullet>y" in exI)
apply(rule_tac x="pi\<bullet>b" in exI)
apply(simp)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>y" in exI)
apply(rule_tac x="pi\<bullet>b" in exI)
apply(simp)
done

lemma AXIOMS_eqvt_aux_coname:
  fixes pi::"coname prm"
  shows "M \<in> AXIOMSn B \<Longrightarrow> (pi\<bullet>M) \<in> AXIOMSn B" 
  and   "N \<in> AXIOMSc B \<Longrightarrow> (pi\<bullet>N) \<in> AXIOMSc B"
apply(auto simp add: AXIOMSn_def AXIOMSc_def)
apply(rule_tac x="pi\<bullet>x" in exI)
apply(rule_tac x="pi\<bullet>y" in exI)
apply(rule_tac x="pi\<bullet>b" in exI)
apply(simp)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>y" in exI)
apply(rule_tac x="pi\<bullet>b" in exI)
apply(simp)
done

lemma AXIOMS_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>AXIOMSn B) = AXIOMSn B" 
  and   "(pi\<bullet>AXIOMSc B) = AXIOMSc B"
apply(auto)
apply(simp add: pt_set_bij1a[OF pt_name_inst, OF at_name_inst])
apply(drule_tac pi="pi" in AXIOMS_eqvt_aux_name(1))
apply(perm_simp)
apply(drule_tac pi="rev pi" in AXIOMS_eqvt_aux_name(1))
apply(simp add: pt_set_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp add: pt_set_bij1a[OF pt_name_inst, OF at_name_inst])
apply(drule_tac pi="pi" in AXIOMS_eqvt_aux_name(2))
apply(perm_simp)
apply(drule_tac pi="rev pi" in AXIOMS_eqvt_aux_name(2))
apply(simp add: pt_set_bij1[OF pt_name_inst, OF at_name_inst])
done

lemma AXIOMS_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>AXIOMSn B) = AXIOMSn B" 
  and   "(pi\<bullet>AXIOMSc B) = AXIOMSc B"
apply(auto)
apply(simp add: pt_set_bij1a[OF pt_coname_inst, OF at_coname_inst])
apply(drule_tac pi="pi" in AXIOMS_eqvt_aux_coname(1))
apply(perm_simp)
apply(drule_tac pi="rev pi" in AXIOMS_eqvt_aux_coname(1))
apply(simp add: pt_set_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: pt_set_bij1a[OF pt_coname_inst, OF at_coname_inst])
apply(drule_tac pi="pi" in AXIOMS_eqvt_aux_coname(2))
apply(perm_simp)
apply(drule_tac pi="rev pi" in AXIOMS_eqvt_aux_coname(2))
apply(simp add: pt_set_bij1[OF pt_coname_inst, OF at_coname_inst])
done

lemma BINDING_eqvt_name:
  fixes pi::"name prm"
  shows "(pi\<bullet>(BINDINGn B X)) = BINDINGn B (pi\<bullet>X)" 
  and   "(pi\<bullet>(BINDINGc B Y)) = BINDINGc B (pi\<bullet>Y)" 
apply(auto simp add: BINDINGn_def BINDINGc_def perm_set_eq)
apply(rule_tac x="pi\<bullet>xb" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(auto)[1]
apply(drule_tac x="(rev pi)\<bullet>a" in spec)
apply(drule_tac x="(rev pi)\<bullet>P" in spec)
apply(drule mp)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp)
apply(drule_tac ?pi1.0="pi" in SNa_eqvt(1))
apply(perm_simp add: nsubst_eqvt)
apply(rule_tac x="(rev pi\<bullet>xa):(rev pi\<bullet>M)" in exI)
apply(perm_simp)
apply(rule_tac x="rev pi\<bullet>xa" in exI)
apply(rule_tac x="rev pi\<bullet>M" in exI)
apply(simp)
apply(auto)[1]
apply(drule_tac x="pi\<bullet>a" in spec)
apply(drule_tac x="pi\<bullet>P" in spec)
apply(drule mp)
apply(force)
apply(drule_tac ?pi1.0="rev pi" in SNa_eqvt(1))
apply(perm_simp add: nsubst_eqvt)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(auto)[1]
apply(drule_tac x="(rev pi)\<bullet>x" in spec)
apply(drule_tac x="(rev pi)\<bullet>P" in spec)
apply(drule mp)
apply(drule sym)
apply(drule pt_bij1[OF pt_name_inst, OF at_name_inst])
apply(simp)
apply(drule_tac ?pi1.0="pi" in SNa_eqvt(1))
apply(perm_simp add: csubst_eqvt)
apply(rule_tac x="<(rev pi\<bullet>a)>:(rev pi\<bullet>M)" in exI)
apply(perm_simp)
apply(rule_tac x="rev pi\<bullet>a" in exI)
apply(rule_tac x="rev pi\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(auto)[1]
apply(drule_tac x="pi\<bullet>x" in spec)
apply(drule_tac x="pi\<bullet>P" in spec)
apply(drule mp)
apply(force)
apply(drule_tac ?pi1.0="rev pi" in SNa_eqvt(1))
apply(perm_simp add: csubst_eqvt)
done

lemma BINDING_eqvt_coname:
  fixes pi::"coname prm"
  shows "(pi\<bullet>(BINDINGn B X)) = BINDINGn B (pi\<bullet>X)" 
  and   "(pi\<bullet>(BINDINGc B Y)) = BINDINGc B (pi\<bullet>Y)" 
apply(auto simp add: BINDINGn_def BINDINGc_def perm_set_eq)
apply(rule_tac x="pi\<bullet>xb" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(auto)[1]
apply(drule_tac x="(rev pi)\<bullet>a" in spec)
apply(drule_tac x="(rev pi)\<bullet>P" in spec)
apply(drule mp)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp)
apply(drule_tac ?pi2.0="pi" in SNa_eqvt(2))
apply(perm_simp add: nsubst_eqvt)
apply(rule_tac x="(rev pi\<bullet>xa):(rev pi\<bullet>M)" in exI)
apply(perm_simp)
apply(rule_tac x="rev pi\<bullet>xa" in exI)
apply(rule_tac x="rev pi\<bullet>M" in exI)
apply(simp add: swap_simps)
apply(auto)[1]
apply(drule_tac x="pi\<bullet>a" in spec)
apply(drule_tac x="pi\<bullet>P" in spec)
apply(drule mp)
apply(force)
apply(drule_tac ?pi2.0="rev pi" in SNa_eqvt(2))
apply(perm_simp add: nsubst_eqvt)
apply(rule_tac x="pi\<bullet>a" in exI)
apply(rule_tac x="pi\<bullet>M" in exI)
apply(simp)
apply(auto)[1]
apply(drule_tac x="(rev pi)\<bullet>x" in spec)
apply(drule_tac x="(rev pi)\<bullet>P" in spec)
apply(drule mp)
apply(drule sym)
apply(drule pt_bij1[OF pt_coname_inst, OF at_coname_inst])
apply(simp)
apply(drule_tac ?pi2.0="pi" in SNa_eqvt(2))
apply(perm_simp add: csubst_eqvt)
apply(rule_tac x="<(rev pi\<bullet>a)>:(rev pi\<bullet>M)" in exI)
apply(perm_simp)
apply(rule_tac x="rev pi\<bullet>a" in exI)
apply(rule_tac x="rev pi\<bullet>M" in exI)
apply(simp)
apply(auto)[1]
apply(drule_tac x="pi\<bullet>x" in spec)
apply(drule_tac x="pi\<bullet>P" in spec)
apply(drule mp)
apply(force)
apply(drule_tac ?pi2.0="rev pi" in SNa_eqvt(2))
apply(perm_simp add: csubst_eqvt)
done

lemma CAND_eqvt_name:
  fixes pi::"name prm"
  shows   "(pi\<bullet>(\<parallel>(B)\<parallel>)) = (\<parallel>(B)\<parallel>)"
  and     "(pi\<bullet>(\<parallel><B>\<parallel>)) = (\<parallel><B>\<parallel>)"
proof (nominal_induct B rule: ty.strong_induct)
  case (PR X)
  { case 1 show ?case 
      apply -
      apply(simp add: lfp_eqvt)
      apply(simp add: perm_fun_def)
      apply(simp add: union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name)
      apply(perm_simp)
    done
  next
    case 2 show ?case
      apply -
      apply(simp only: NEGc_simps)
      apply(simp add: union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name)
      apply(simp add: lfp_eqvt)
      apply(simp add: comp_def)
      apply(simp add: perm_fun_def)
      apply(simp add: union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name)
      apply(perm_simp)
      done
  }
next
  case (NOT B)
  have ih1: "pi\<bullet>(\<parallel>(B)\<parallel>) = (\<parallel>(B)\<parallel>)" by fact
  have ih2: "pi\<bullet>(\<parallel><B>\<parallel>) = (\<parallel><B>\<parallel>)" by fact
  have g: "pi\<bullet>(\<parallel>(NOT B)\<parallel>) = (\<parallel>(NOT B)\<parallel>)"
    apply -
    apply(simp only: lfp_eqvt)
    apply(simp only: comp_def)
    apply(simp only: perm_fun_def)
    apply(simp only: NEGc.simps NEGn.simps)
    apply(simp only: union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name NOTRIGHT_eqvt_name NOTLEFT_eqvt_name)
    apply(perm_simp add: ih1 ih2)
    done
  { case 1 show ?case by (rule g)
  next 
    case 2 show ?case
      by (simp only: NEGc_simps union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name NOTRIGHT_eqvt_name ih1 ih2 g)
  }
next
  case (AND A B)
  have ih1: "pi\<bullet>(\<parallel>(A)\<parallel>) = (\<parallel>(A)\<parallel>)" by fact
  have ih2: "pi\<bullet>(\<parallel><A>\<parallel>) = (\<parallel><A>\<parallel>)" by fact
  have ih3: "pi\<bullet>(\<parallel>(B)\<parallel>) = (\<parallel>(B)\<parallel>)" by fact
  have ih4: "pi\<bullet>(\<parallel><B>\<parallel>) = (\<parallel><B>\<parallel>)" by fact
  have g: "pi\<bullet>(\<parallel>(A AND B)\<parallel>) = (\<parallel>(A AND B)\<parallel>)"
    apply -
    apply(simp only: lfp_eqvt)
    apply(simp only: comp_def)
    apply(simp only: perm_fun_def)
    apply(simp only: NEGc.simps NEGn.simps)
    apply(simp only: union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name ANDRIGHT_eqvt_name 
                     ANDLEFT2_eqvt_name ANDLEFT1_eqvt_name)
    apply(perm_simp add: ih1 ih2 ih3 ih4)
    done
  { case 1 show ?case by (rule g)
  next 
    case 2 show ?case
      by (simp only: NEGc_simps union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name 
                     ANDRIGHT_eqvt_name ANDLEFT1_eqvt_name ANDLEFT2_eqvt_name ih1 ih2 ih3 ih4 g)
  }
next
  case (OR A B)
  have ih1: "pi\<bullet>(\<parallel>(A)\<parallel>) = (\<parallel>(A)\<parallel>)" by fact
  have ih2: "pi\<bullet>(\<parallel><A>\<parallel>) = (\<parallel><A>\<parallel>)" by fact
  have ih3: "pi\<bullet>(\<parallel>(B)\<parallel>) = (\<parallel>(B)\<parallel>)" by fact
  have ih4: "pi\<bullet>(\<parallel><B>\<parallel>) = (\<parallel><B>\<parallel>)" by fact
  have g: "pi\<bullet>(\<parallel>(A OR B)\<parallel>) = (\<parallel>(A OR B)\<parallel>)"
    apply -
    apply(simp only: lfp_eqvt)
    apply(simp only: comp_def)
    apply(simp only: perm_fun_def)
    apply(simp only: NEGc.simps NEGn.simps)
    apply(simp only: union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name ORRIGHT1_eqvt_name 
                     ORRIGHT2_eqvt_name ORLEFT_eqvt_name)
    apply(perm_simp add: ih1 ih2 ih3 ih4)
    done
  { case 1 show ?case by (rule g)
  next 
    case 2 show ?case
      by (simp only: NEGc_simps union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name 
                     ORRIGHT1_eqvt_name ORRIGHT2_eqvt_name ORLEFT_eqvt_name ih1 ih2 ih3 ih4 g)
  }
next
  case (IMP A B)
  have ih1: "pi\<bullet>(\<parallel>(A)\<parallel>) = (\<parallel>(A)\<parallel>)" by fact
  have ih2: "pi\<bullet>(\<parallel><A>\<parallel>) = (\<parallel><A>\<parallel>)" by fact
  have ih3: "pi\<bullet>(\<parallel>(B)\<parallel>) = (\<parallel>(B)\<parallel>)" by fact
  have ih4: "pi\<bullet>(\<parallel><B>\<parallel>) = (\<parallel><B>\<parallel>)" by fact
  have g: "pi\<bullet>(\<parallel>(A IMP B)\<parallel>) = (\<parallel>(A IMP B)\<parallel>)"
    apply -
    apply(simp only: lfp_eqvt)
    apply(simp only: comp_def)
    apply(simp only: perm_fun_def)
    apply(simp only: NEGc.simps NEGn.simps)
    apply(simp only: union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name IMPRIGHT_eqvt_name IMPLEFT_eqvt_name)
    apply(perm_simp add: ih1 ih2 ih3 ih4)
    done
  { case 1 show ?case by (rule g)
  next 
    case 2 show ?case
      by (simp only: NEGc_simps union_eqvt AXIOMS_eqvt_name BINDING_eqvt_name 
                     IMPRIGHT_eqvt_name IMPLEFT_eqvt_name ih1 ih2 ih3 ih4 g)
  }
qed

lemma CAND_eqvt_coname:
  fixes pi::"coname prm"
  shows   "(pi\<bullet>(\<parallel>(B)\<parallel>)) = (\<parallel>(B)\<parallel>)"
  and     "(pi\<bullet>(\<parallel><B>\<parallel>)) = (\<parallel><B>\<parallel>)"
proof (nominal_induct B rule: ty.strong_induct)
  case (PR X)
  { case 1 show ?case 
      apply -
      apply(simp add: lfp_eqvt)
      apply(simp add: perm_fun_def)
      apply(simp add: union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname)
      apply(perm_simp)
    done
  next
    case 2 show ?case
      apply -
      apply(simp only: NEGc_simps)
      apply(simp add: union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname)
      apply(simp add: lfp_eqvt)
      apply(simp add: comp_def)
      apply(simp add: perm_fun_def)
      apply(simp add: union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname)
      apply(perm_simp)
      done
  }
next
  case (NOT B)
  have ih1: "pi\<bullet>(\<parallel>(B)\<parallel>) = (\<parallel>(B)\<parallel>)" by fact
  have ih2: "pi\<bullet>(\<parallel><B>\<parallel>) = (\<parallel><B>\<parallel>)" by fact
  have g: "pi\<bullet>(\<parallel>(NOT B)\<parallel>) = (\<parallel>(NOT B)\<parallel>)"
    apply -
    apply(simp only: lfp_eqvt)
    apply(simp only: comp_def)
    apply(simp only: perm_fun_def)
    apply(simp only: NEGc.simps NEGn.simps)
    apply(simp only: union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname 
            NOTRIGHT_eqvt_coname NOTLEFT_eqvt_coname)
    apply(perm_simp add: ih1 ih2)
    done
  { case 1 show ?case by (rule g)
  next 
    case 2 show ?case
      by (simp only: NEGc_simps union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname 
              NOTRIGHT_eqvt_coname ih1 ih2 g)
  }
next
  case (AND A B)
  have ih1: "pi\<bullet>(\<parallel>(A)\<parallel>) = (\<parallel>(A)\<parallel>)" by fact
  have ih2: "pi\<bullet>(\<parallel><A>\<parallel>) = (\<parallel><A>\<parallel>)" by fact
  have ih3: "pi\<bullet>(\<parallel>(B)\<parallel>) = (\<parallel>(B)\<parallel>)" by fact
  have ih4: "pi\<bullet>(\<parallel><B>\<parallel>) = (\<parallel><B>\<parallel>)" by fact
  have g: "pi\<bullet>(\<parallel>(A AND B)\<parallel>) = (\<parallel>(A AND B)\<parallel>)"
    apply -
    apply(simp only: lfp_eqvt)
    apply(simp only: comp_def)
    apply(simp only: perm_fun_def)
    apply(simp only: NEGc.simps NEGn.simps)
    apply(simp only: union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname ANDRIGHT_eqvt_coname 
                     ANDLEFT2_eqvt_coname ANDLEFT1_eqvt_coname)
    apply(perm_simp add: ih1 ih2 ih3 ih4)
    done
  { case 1 show ?case by (rule g)
  next 
    case 2 show ?case
      by (simp only: NEGc_simps union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname 
                     ANDRIGHT_eqvt_coname ANDLEFT1_eqvt_coname ANDLEFT2_eqvt_coname ih1 ih2 ih3 ih4 g)
  }
next
  case (OR A B)
  have ih1: "pi\<bullet>(\<parallel>(A)\<parallel>) = (\<parallel>(A)\<parallel>)" by fact
  have ih2: "pi\<bullet>(\<parallel><A>\<parallel>) = (\<parallel><A>\<parallel>)" by fact
  have ih3: "pi\<bullet>(\<parallel>(B)\<parallel>) = (\<parallel>(B)\<parallel>)" by fact
  have ih4: "pi\<bullet>(\<parallel><B>\<parallel>) = (\<parallel><B>\<parallel>)" by fact
  have g: "pi\<bullet>(\<parallel>(A OR B)\<parallel>) = (\<parallel>(A OR B)\<parallel>)"
    apply -
    apply(simp only: lfp_eqvt)
    apply(simp only: comp_def)
    apply(simp only: perm_fun_def)
    apply(simp only: NEGc.simps NEGn.simps)
    apply(simp only: union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname ORRIGHT1_eqvt_coname 
                     ORRIGHT2_eqvt_coname ORLEFT_eqvt_coname)
    apply(perm_simp add: ih1 ih2 ih3 ih4)
    done
  { case 1 show ?case by (rule g)
  next 
    case 2 show ?case
      by (simp only: NEGc_simps union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname 
                     ORRIGHT1_eqvt_coname ORRIGHT2_eqvt_coname ORLEFT_eqvt_coname ih1 ih2 ih3 ih4 g)
  }
next
  case (IMP A B)
  have ih1: "pi\<bullet>(\<parallel>(A)\<parallel>) = (\<parallel>(A)\<parallel>)" by fact
  have ih2: "pi\<bullet>(\<parallel><A>\<parallel>) = (\<parallel><A>\<parallel>)" by fact
  have ih3: "pi\<bullet>(\<parallel>(B)\<parallel>) = (\<parallel>(B)\<parallel>)" by fact
  have ih4: "pi\<bullet>(\<parallel><B>\<parallel>) = (\<parallel><B>\<parallel>)" by fact
  have g: "pi\<bullet>(\<parallel>(A IMP B)\<parallel>) = (\<parallel>(A IMP B)\<parallel>)"
    apply -
    apply(simp only: lfp_eqvt)
    apply(simp only: comp_def)
    apply(simp only: perm_fun_def)
    apply(simp only: NEGc.simps NEGn.simps)
    apply(simp only: union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname IMPRIGHT_eqvt_coname 
         IMPLEFT_eqvt_coname)
    apply(perm_simp add: ih1 ih2 ih3 ih4)
    done
  { case 1 show ?case by (rule g)
  next 
    case 2 show ?case
      by (simp only: NEGc_simps union_eqvt AXIOMS_eqvt_coname BINDING_eqvt_coname 
                     IMPRIGHT_eqvt_coname IMPLEFT_eqvt_coname ih1 ih2 ih3 ih4 g)
  }
qed

text {* Elimination rules for the set-operators *}

lemma BINDINGc_elim:
  assumes a: "<a>:M \<in> BINDINGc B (\<parallel>(B)\<parallel>)"
  shows "\<forall>x P. ((x):P)\<in>(\<parallel>(B)\<parallel>) \<longrightarrow> SNa (M{a:=(x).P})"
using a
apply(auto simp add: BINDINGc_def)
apply(auto simp add: ctrm.inject alpha)
apply(drule_tac x="[(a,aa)]\<bullet>x" in spec)
apply(drule_tac x="[(a,aa)]\<bullet>P" in spec)
apply(drule mp)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname)
apply(drule_tac ?pi2.0="[(a,aa)]" in SNa_eqvt(2))
apply(perm_simp add: csubst_eqvt)
done

lemma BINDINGn_elim:
  assumes a: "(x):M \<in> BINDINGn B (\<parallel><B>\<parallel>)"
  shows "\<forall>c P. (<c>:P)\<in>(\<parallel><B>\<parallel>) \<longrightarrow> SNa (M{x:=<c>.P})"
using a
apply(auto simp add: BINDINGn_def)
apply(auto simp add: ntrm.inject alpha)
apply(drule_tac x="[(x,xa)]\<bullet>c" in spec)
apply(drule_tac x="[(x,xa)]\<bullet>P" in spec)
apply(drule mp)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name)
apply(drule_tac ?pi1.0="[(x,xa)]" in SNa_eqvt(1))
apply(perm_simp add: nsubst_eqvt)
done

lemma NOTRIGHT_elim:
  assumes a: "<a>:M \<in> NOTRIGHT (NOT B) (\<parallel>(B)\<parallel>)"
  obtains x' M' where "M = NotR (x').M' a" and "fic (NotR (x').M' a) a" and "(x'):M' \<in> (\<parallel>(B)\<parallel>)"
using a
apply(auto simp add: ctrm.inject alpha abs_fresh calc_atm)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(a,aa)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
done

lemma NOTLEFT_elim:
  assumes a: "(x):M \<in> NOTLEFT (NOT B) (\<parallel><B>\<parallel>)"
  obtains a' M' where "M = NotL <a'>.M' x" and "fin (NotL <a'>.M' x) x" and "<a'>:M' \<in> (\<parallel><B>\<parallel>)"
using a
apply(auto simp add: ntrm.inject alpha abs_fresh calc_atm)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
done

lemma ANDRIGHT_elim:
  assumes a: "<a>:M \<in> ANDRIGHT (B AND C) (\<parallel><B>\<parallel>) (\<parallel><C>\<parallel>)"
  obtains d' M' e' N' where "M = AndR <d'>.M' <e'>.N' a" and "fic (AndR <d'>.M' <e'>.N' a) a" 
                      and "<d'>:M' \<in> (\<parallel><B>\<parallel>)" and "<e'>:N' \<in> (\<parallel><C>\<parallel>)"
using a
apply(auto simp add: ctrm.inject alpha abs_fresh calc_atm fresh_atm)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(a,c)]\<bullet>M" in meta_spec)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(a,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" and x="<a>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(case_tac "a=b")
apply(simp)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(b,c)]\<bullet>M" in meta_spec)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(b,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "c=b")
apply(simp)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>M" in meta_spec)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(a,c)]\<bullet>M" in meta_spec)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(a,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(case_tac "a=aa")
apply(simp)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(aa,c)]\<bullet>M" in meta_spec)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(aa,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,c)]" and x="<aa>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "c=aa")
apply(simp)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,aa)]\<bullet>M" in meta_spec)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(a,aa)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" and x="<a>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(a,c)]\<bullet>M" in meta_spec)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(a,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" and x="<a>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(case_tac "a=aa")
apply(simp)
apply(case_tac "aa=b")
apply(simp)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(b,c)]\<bullet>M" in meta_spec)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(b,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "c=b")
apply(simp)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(aa,b)]\<bullet>M" in meta_spec)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(aa,b)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,b)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(aa,c)]\<bullet>M" in meta_spec)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(aa,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,c)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "c=aa")
apply(simp)
apply(case_tac "a=b")
apply(simp)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(b,aa)]\<bullet>M" in meta_spec)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(b,aa)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(b,aa)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(b,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(b,aa)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "aa=b")
apply(simp)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>M" in meta_spec)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,aa)]\<bullet>M" in meta_spec)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(a,aa)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "a=b")
apply(simp)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(b,c)]\<bullet>M" in meta_spec)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="[(b,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(b,c)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "c=b")
apply(simp)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>M" in meta_spec)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(a,c)]\<bullet>M" in meta_spec)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(a,c)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule meta_mp)
apply(drule_tac pi="[(a,c)]" and x="<b>:N" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
done 

lemma ANDLEFT1_elim:
  assumes a: "(x):M \<in> ANDLEFT1 (B AND C) (\<parallel>(B)\<parallel>)"
  obtains x' M' where "M = AndL1 (x').M' x" and "fin (AndL1 (x').M' x) x" and "(x'):M' \<in> (\<parallel>(B)\<parallel>)"
using a
apply(auto simp add: ntrm.inject alpha abs_fresh calc_atm)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(xa,y)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "y=xa")
apply(simp)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
done

lemma ANDLEFT2_elim:
  assumes a: "(x):M \<in> ANDLEFT2 (B AND C) (\<parallel>(C)\<parallel>)"
  obtains x' M' where "M = AndL2 (x').M' x" and "fin (AndL2 (x').M' x) x" and "(x'):M' \<in> (\<parallel>(C)\<parallel>)"
using a
apply(auto simp add: ntrm.inject alpha abs_fresh calc_atm)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(xa,y)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "y=xa")
apply(simp)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
done

lemma ORRIGHT1_elim:
  assumes a: "<a>:M \<in> ORRIGHT1 (B OR C) (\<parallel><B>\<parallel>)"
  obtains a' M' where "M = OrR1 <a'>.M' a" and "fic (OrR1 <a'>.M' a) a" and "<a'>:M' \<in> (\<parallel><B>\<parallel>)"
using a
apply(auto simp add: ctrm.inject alpha abs_fresh calc_atm)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(case_tac "a=aa")
apply(simp)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(aa,b)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "b=aa")
apply(simp)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,aa)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
done

lemma ORRIGHT2_elim:
  assumes a: "<a>:M \<in> ORRIGHT2 (B OR C) (\<parallel><C>\<parallel>)"
  obtains a' M' where "M = OrR2 <a'>.M' a" and "fic (OrR2 <a'>.M' a) a" and "<a'>:M' \<in> (\<parallel><C>\<parallel>)"
using a
apply(auto simp add: ctrm.inject alpha abs_fresh calc_atm)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(case_tac "a=aa")
apply(simp)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(aa,b)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(case_tac "b=aa")
apply(simp)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,aa)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
apply(simp)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(simp)
done

lemma ORLEFT_elim:
  assumes a: "(x):M \<in> ORLEFT (B OR C) (\<parallel>(B)\<parallel>) (\<parallel>(C)\<parallel>)"
  obtains y' M' z' N' where "M = OrL (y').M' (z').N' x" and "fin (OrL (y').M' (z').N' x) x" 
                      and "(y'):M' \<in> (\<parallel>(B)\<parallel>)" and "(z'):N' \<in> (\<parallel>(C)\<parallel>)"
using a
apply(auto simp add: ntrm.inject alpha abs_fresh calc_atm fresh_atm)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(x,z)]\<bullet>M" in meta_spec)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(x,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" and x="(x):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(case_tac "x=y")
apply(simp)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(y,z)]\<bullet>M" in meta_spec)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(y,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "z=y")
apply(simp)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>M" in meta_spec)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(x,z)]\<bullet>M" in meta_spec)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(x,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(xa,z)]\<bullet>M" in meta_spec)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(xa,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,z)]" and x="(xa):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "z=xa")
apply(simp)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>M" in meta_spec)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" and x="(x):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(x,z)]\<bullet>M" in meta_spec)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(x,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" and x="(x):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(case_tac "x=xa")
apply(simp)
apply(case_tac "xa=y")
apply(simp)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(y,z)]\<bullet>M" in meta_spec)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(y,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "z=y")
apply(simp)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(xa,y)]\<bullet>M" in meta_spec)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(xa,y)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(xa,z)]\<bullet>M" in meta_spec)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(xa,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,z)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "z=xa")
apply(simp)
apply(case_tac "x=y")
apply(simp)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(y,xa)]\<bullet>M" in meta_spec)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(y,xa)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(y,xa)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(y,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(y,xa)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "xa=y")
apply(simp)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>M" in meta_spec)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>M" in meta_spec)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "x=y")
apply(simp)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(y,z)]\<bullet>M" in meta_spec)
apply(drule_tac x="z" in meta_spec)
apply(drule_tac x="[(y,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(y,z)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "z=y")
apply(simp)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>M" in meta_spec)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(x,z)]\<bullet>M" in meta_spec)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(x,z)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,z)]" and x="(y):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
done

lemma IMPRIGHT_elim:
  assumes a: "<a>:M \<in> IMPRIGHT (B IMP C) (\<parallel>(B)\<parallel>) (\<parallel><C>\<parallel>) (\<parallel>(C)\<parallel>) (\<parallel><B>\<parallel>)"
  obtains x' a' M' where "M = ImpR (x').<a'>.M' a" and "fic (ImpR (x').<a'>.M' a) a" 
                   and "\<forall>z P. x'\<sharp>(z,P) \<and> (z):P \<in> \<parallel>(C)\<parallel> \<longrightarrow> (x'):(M'{a':=(z).P}) \<in> \<parallel>(B)\<parallel>" 
                   and "\<forall>c Q. a'\<sharp>(c,Q) \<and> <c>:Q \<in> \<parallel><B>\<parallel> \<longrightarrow> <a'>:(M'{x':=<c>.Q}) \<in> \<parallel><C>\<parallel>"
using a
apply(auto simp add: ctrm.inject alpha abs_fresh calc_atm)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(auto)[1]
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule_tac x="z" in spec)
apply(drule_tac x="[(a,b)]\<bullet>P" in spec)
apply(simp add: fresh_prod fresh_left calc_atm)
apply(drule_tac pi="[(a,b)]" and x="(x):M{a:=(z).([(a,b)]\<bullet>P)}" 
                                     in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: calc_atm csubst_eqvt CAND_eqvt_coname)
apply(drule meta_mp)
apply(auto)[1]
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add:  CAND_eqvt_coname)
apply(rotate_tac 2)
apply(drule_tac x="[(a,b)]\<bullet>c" in spec)
apply(drule_tac x="[(a,b)]\<bullet>Q" in spec)
apply(simp add: fresh_prod fresh_left)
apply(drule mp)
apply(simp add: calc_atm)
apply(drule_tac pi="[(a,b)]" and x="<a>:M{x:=<([(a,b)]\<bullet>c)>.([(a,b)]\<bullet>Q)}" 
                                        in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: nsubst_eqvt CAND_eqvt_coname)
apply(simp add: calc_atm)
apply(case_tac "a=aa")
apply(simp)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="b" in meta_spec)
apply(drule_tac x="[(aa,b)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(aa,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(auto)[1]
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule_tac x="z" in spec)
apply(drule_tac x="[(a,b)]\<bullet>P" in spec)
apply(simp add: fresh_prod fresh_left calc_atm)
apply(drule_tac pi="[(a,b)]" and x="(x):M{a:=(z).([(a,b)]\<bullet>P)}" 
                                     in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: calc_atm csubst_eqvt  CAND_eqvt_coname)
apply(drule meta_mp)
apply(auto)[1]
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname)
apply(drule_tac x="[(a,b)]\<bullet>c" in spec)
apply(drule_tac x="[(a,b)]\<bullet>Q" in spec)
apply(simp)
apply(simp add: fresh_prod fresh_left)
apply(drule mp)
apply(simp add: calc_atm)
apply(drule_tac pi="[(a,b)]" and x="<a>:M{x:=<([(a,b)]\<bullet>c)>.([(a,b)]\<bullet>Q)}" 
                                      in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: nsubst_eqvt CAND_eqvt_coname)
apply(simp add: calc_atm)
apply(simp)
apply(case_tac "b=aa")
apply(simp)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(a,aa)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(auto)[1]
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm CAND_eqvt_coname)
apply(drule_tac x="z" in spec)
apply(drule_tac x="[(a,aa)]\<bullet>P" in spec)
apply(simp add: fresh_prod fresh_left calc_atm)
apply(drule_tac pi="[(a,aa)]" and x="(x):M{aa:=(z).([(a,aa)]\<bullet>P)}" 
                                    in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: calc_atm csubst_eqvt  CAND_eqvt_coname)
apply(drule meta_mp)
apply(auto)[1]
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add:  CAND_eqvt_coname)
apply(drule_tac x="[(a,aa)]\<bullet>c" in spec)
apply(drule_tac x="[(a,aa)]\<bullet>Q" in spec)
apply(simp)
apply(simp add: fresh_prod fresh_left)
apply(drule mp)
apply(simp add: calc_atm)
apply(drule_tac pi="[(a,aa)]" and x="<aa>:M{x:=<([(a,aa)]\<bullet>c)>.([(a,aa)]\<bullet>Q)}" 
                                    in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: nsubst_eqvt  CAND_eqvt_coname)
apply(simp add: calc_atm)
apply(simp)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="aa" in meta_spec)
apply(drule_tac x="[(a,b)]\<bullet>M" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(auto)[1]
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: calc_atm  CAND_eqvt_coname)
apply(drule_tac x="z" in spec)
apply(drule_tac x="[(a,b)]\<bullet>P" in spec)
apply(simp add: fresh_prod fresh_left calc_atm)
apply(drule_tac pi="[(a,b)]" and x="(x):M{aa:=(z).([(a,b)]\<bullet>P)}" 
                                          in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: calc_atm csubst_eqvt  CAND_eqvt_coname)
apply(drule meta_mp)
apply(auto)[1]
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add:  CAND_eqvt_coname)
apply(drule_tac x="[(a,b)]\<bullet>c" in spec)
apply(drule_tac x="[(a,b)]\<bullet>Q" in spec)
apply(simp add: fresh_prod fresh_left)
apply(drule mp)
apply(simp add: calc_atm)
apply(drule_tac pi="[(a,b)]" and x="<aa>:M{x:=<([(a,b)]\<bullet>c)>.([(a,b)]\<bullet>Q)}" 
                                        in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: nsubst_eqvt  CAND_eqvt_coname)
apply(simp add: calc_atm)
done

lemma IMPLEFT_elim:
  assumes a: "(x):M \<in> IMPLEFT (B IMP C) (\<parallel><B>\<parallel>) (\<parallel>(C)\<parallel>)"
  obtains x' a' M' N' where "M = ImpL <a'>.M' (x').N' x" and "fin (ImpL <a'>.M' (x').N' x) x" 
                   and "<a'>:M' \<in> \<parallel><B>\<parallel>" and "(x'):N' \<in> \<parallel>(C)\<parallel>"
using a
apply(auto simp add: ntrm.inject alpha abs_fresh calc_atm)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>M" in meta_spec)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" and x="(x):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: calc_atm  CAND_eqvt_name)
apply(simp)
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(xa,y)]\<bullet>M" in meta_spec)
apply(drule_tac x="y" in meta_spec)
apply(drule_tac x="[(xa,y)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(xa,y)]" and x="(xa):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(case_tac "y=xa")
apply(simp)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>M" in meta_spec)
apply(drule_tac x="x" in meta_spec)
apply(drule_tac x="[(x,xa)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" and x="<a>:M" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm  CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,xa)]" and x="(xa):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
apply(simp)
apply(drule_tac x="a" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>M" in meta_spec)
apply(drule_tac x="xa" in meta_spec)
apply(drule_tac x="[(x,y)]\<bullet>N" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(drule meta_mp)
apply(drule_tac pi="[(x,y)]" and x="(xa):N" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: calc_atm CAND_eqvt_name)
apply(simp)
done

lemma CANDs_alpha:
  shows "<a>:M \<in> (\<parallel><B>\<parallel>) \<Longrightarrow> [a].M = [b].N \<Longrightarrow> <b>:N \<in> (\<parallel><B>\<parallel>)"
  and   "(x):M \<in> (\<parallel>(B)\<parallel>) \<Longrightarrow> [x].M = [y].N \<Longrightarrow> (y):N \<in> (\<parallel>(B)\<parallel>)"
apply(auto simp add: alpha)
apply(drule_tac pi="[(a,b)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(perm_simp add: CAND_eqvt_coname calc_atm)
apply(drule_tac pi="[(x,y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name calc_atm)
done

lemma CAND_NotR_elim:
  assumes a: "<a>:NotR (x).M a \<in> (\<parallel><B>\<parallel>)" "<a>:NotR (x).M a \<notin> BINDINGc B (\<parallel>(B)\<parallel>)"
  shows "\<exists>B'. B = NOT B' \<and> (x):M \<in> (\<parallel>(B')\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSc_def ctrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
done

lemma CAND_NotL_elim_aux:
  assumes a: "(x):NotL <a>.M x \<in> NEGn B (\<parallel><B>\<parallel>)" "(x):NotL <a>.M x \<notin> BINDINGn B (\<parallel><B>\<parallel>)"
  shows "\<exists>B'. B = NOT B' \<and> <a>:M \<in> (\<parallel><B'>\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSn_def ntrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
done

lemmas CAND_NotL_elim = CAND_NotL_elim_aux[OF NEG_elim(2)]

lemma CAND_AndR_elim:
  assumes a: "<a>:AndR <b>.M <c>.N a \<in> (\<parallel><B>\<parallel>)" "<a>:AndR <b>.M <c>.N a \<notin> BINDINGc B (\<parallel>(B)\<parallel>)"
  shows "\<exists>B1 B2. B = B1 AND B2 \<and> <b>:M \<in> (\<parallel><B1>\<parallel>) \<and> <c>:N \<in> (\<parallel><B2>\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSc_def ctrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(a,ca)]" and x="<a>:Ma" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(drule_tac pi="[(a,ca)]" and x="<a>:Na" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(drule_tac pi="[(a,ca)]" and x="<a>:Ma" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "a=ba")
apply(simp)
apply(drule_tac pi="[(ba,ca)]" and x="<ba>:Na" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "ca=ba")
apply(simp)
apply(drule_tac pi="[(a,ba)]" and x="<ba>:Na" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(a,ca)]" and x="<ba>:Na" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "a=aa")
apply(simp)
apply(drule_tac pi="[(aa,ca)]" and x="<aa>:Ma" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "ca=aa")
apply(simp)
apply(drule_tac pi="[(a,aa)]" and x="<aa>:Ma" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(a,ca)]" and x="<aa>:Ma" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(drule_tac pi="[(a,ca)]" and x="<a>:Na" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "a=aa")
apply(simp)
apply(drule_tac pi="[(aa,ca)]" and x="<aa>:Ma" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "ca=aa")
apply(simp)
apply(drule_tac pi="[(a,aa)]" and x="<aa>:Ma" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(a,ca)]" and x="<aa>:Ma" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "a=ba")
apply(simp)
apply(drule_tac pi="[(ba,ca)]" and x="<ba>:Na" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "ca=ba")
apply(simp)
apply(drule_tac pi="[(a,ba)]" and x="<ba>:Na" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(a,ca)]" and x="<ba>:Na" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_coname calc_atm)
apply(auto intro: CANDs_alpha)[1]
done

lemma CAND_OrR1_elim:
  assumes a: "<a>:OrR1 <b>.M a \<in> (\<parallel><B>\<parallel>)" "<a>:OrR1 <b>.M a \<notin> BINDINGc B (\<parallel>(B)\<parallel>)"
  shows "\<exists>B1 B2. B = B1 OR B2 \<and> <b>:M \<in> (\<parallel><B1>\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSc_def ctrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(a,ba)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
apply(case_tac "a=aa")
apply(simp)
apply(drule_tac pi="[(aa,ba)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
apply(case_tac "ba=aa")
apply(simp)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
apply(drule_tac pi="[(a,ba)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
done

lemma CAND_OrR2_elim:
  assumes a: "<a>:OrR2 <b>.M a \<in> (\<parallel><B>\<parallel>)" "<a>:OrR2 <b>.M a \<notin> BINDINGc B (\<parallel>(B)\<parallel>)"
  shows "\<exists>B1 B2. B = B1 OR B2 \<and> <b>:M \<in> (\<parallel><B2>\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSc_def ctrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(a,ba)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
apply(case_tac "a=aa")
apply(simp)
apply(drule_tac pi="[(aa,ba)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
apply(case_tac "ba=aa")
apply(simp)
apply(drule_tac pi="[(a,aa)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
apply(drule_tac pi="[(a,ba)]" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(auto simp add: CAND_eqvt_coname calc_atm intro: CANDs_alpha)
done

lemma CAND_OrL_elim_aux:
  assumes a: "(x):(OrL (y).M (z).N x) \<in> NEGn B (\<parallel><B>\<parallel>)" "(x):(OrL (y).M (z).N x) \<notin> BINDINGn B (\<parallel><B>\<parallel>)"
  shows "\<exists>B1 B2. B = B1 OR B2 \<and> (y):M \<in> (\<parallel>(B1)\<parallel>) \<and> (z):N \<in> (\<parallel>(B2)\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSn_def ntrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(x,za)]" and x="(x):Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(drule_tac pi="[(x,za)]" and x="(x):Nb" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(drule_tac pi="[(x,za)]" and x="(x):Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "x=ya")
apply(simp)
apply(drule_tac pi="[(ya,za)]" and x="(ya):Nb" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "za=ya")
apply(simp)
apply(drule_tac pi="[(x,ya)]" and x="(ya):Nb" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(x,za)]" and x="(ya):Nb" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac pi="[(xa,za)]" and x="(xa):Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "za=xa")
apply(simp)
apply(drule_tac pi="[(x,xa)]" and x="(xa):Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(x,za)]" and x="(xa):Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(drule_tac pi="[(x,za)]" and x="(x):Nb" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac pi="[(xa,za)]" and x="(xa):Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "za=xa")
apply(simp)
apply(drule_tac pi="[(x,xa)]" and x="(xa):Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(x,za)]" and x="(xa):Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "x=ya")
apply(simp)
apply(drule_tac pi="[(ya,za)]" and x="(ya):Nb" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "za=ya")
apply(simp)
apply(drule_tac pi="[(x,ya)]" and x="(ya):Nb" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(x,za)]" and x="(ya):Nb" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
done

lemmas CAND_OrL_elim = CAND_OrL_elim_aux[OF NEG_elim(2)]

lemma CAND_AndL1_elim_aux:
  assumes a: "(x):(AndL1 (y).M x) \<in> NEGn B (\<parallel><B>\<parallel>)" "(x):(AndL1 (y).M x) \<notin> BINDINGn B (\<parallel><B>\<parallel>)"
  shows "\<exists>B1 B2. B = B1 AND B2 \<and> (y):M \<in> (\<parallel>(B1)\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSn_def ntrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(x,ya)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac pi="[(xa,ya)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
apply(case_tac "ya=xa")
apply(simp)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
apply(drule_tac pi="[(x,ya)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
done

lemmas CAND_AndL1_elim = CAND_AndL1_elim_aux[OF NEG_elim(2)]

lemma CAND_AndL2_elim_aux:
  assumes a: "(x):(AndL2 (y).M x) \<in> NEGn B (\<parallel><B>\<parallel>)" "(x):(AndL2 (y).M x) \<notin> BINDINGn B (\<parallel><B>\<parallel>)"
  shows "\<exists>B1 B2. B = B1 AND B2 \<and> (y):M \<in> (\<parallel>(B2)\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSn_def ntrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(x,ya)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac pi="[(xa,ya)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
apply(case_tac "ya=xa")
apply(simp)
apply(drule_tac pi="[(x,xa)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
apply(drule_tac pi="[(x,ya)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(auto simp add: CAND_eqvt_name calc_atm intro: CANDs_alpha)
done

lemmas CAND_AndL2_elim = CAND_AndL2_elim_aux[OF NEG_elim(2)]

lemma CAND_ImpL_elim_aux:
  assumes a: "(x):(ImpL <a>.M (z).N x) \<in> NEGn B (\<parallel><B>\<parallel>)" "(x):(ImpL <a>.M (z).N x) \<notin> BINDINGn B (\<parallel><B>\<parallel>)"
  shows "\<exists>B1 B2. B = B1 IMP B2 \<and> <a>:M \<in> (\<parallel><B1>\<parallel>) \<and> (z):N \<in> (\<parallel>(B2)\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSn_def ntrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm)
apply(drule_tac pi="[(x,y)]" and x="<aa>:Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(drule_tac pi="[(x,y)]" and x="(x):Nb" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(drule_tac pi="[(x,y)]" and x="<aa>:Ma" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(case_tac "x=xa")
apply(simp)
apply(drule_tac pi="[(xa,y)]" and x="(xa):Nb" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(case_tac "y=xa")
apply(simp)
apply(drule_tac pi="[(x,xa)]" and x="(xa):Nb" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
apply(simp)
apply(drule_tac pi="[(x,y)]" and x="(xa):Nb" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name calc_atm)
apply(auto intro: CANDs_alpha)[1]
done

lemmas CAND_ImpL_elim = CAND_ImpL_elim_aux[OF NEG_elim(2)]

lemma CAND_ImpR_elim:
  assumes a: "<a>:ImpR (x).<b>.M a \<in> (\<parallel><B>\<parallel>)" "<a>:ImpR (x).<b>.M a \<notin> BINDINGc B (\<parallel>(B)\<parallel>)"
  shows "\<exists>B1 B2. B = B1 IMP B2 \<and> 
                 (\<forall>z P. x\<sharp>(z,P) \<and> (z):P \<in> \<parallel>(B2)\<parallel> \<longrightarrow> (x):(M{b:=(z).P}) \<in> \<parallel>(B1)\<parallel>) \<and>
                 (\<forall>c Q. b\<sharp>(c,Q) \<and> <c>:Q \<in> \<parallel><B1>\<parallel> \<longrightarrow> <b>:(M{x:=<c>.Q}) \<in> \<parallel><B2>\<parallel>)" 
using a
apply(nominal_induct B rule: ty.strong_induct)
apply(simp_all add: ty.inject AXIOMSc_def ctrm.inject alpha)
apply(auto intro: CANDs_alpha simp add: trm.inject calc_atm abs_fresh fresh_atm fresh_prod fresh_bij)
apply(generate_fresh "name") 
apply(generate_fresh "coname")
apply(drule_tac a="ca" and z="c" in alpha_name_coname)
apply(simp) 
apply(simp) 
apply(simp) 
apply(drule_tac x="[(xa,c)]\<bullet>[(aa,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>z" in spec)
apply(drule_tac x="[(xa,c)]\<bullet>[(aa,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>P" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(aa,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(aa,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="cb" and z="ca" in alpha_name_coname)
apply(simp)
apply(simp)
apply(simp)
apply(drule_tac x="[(xa,ca)]\<bullet>[(aa,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>c" in spec)
apply(drule_tac x="[(xa,ca)]\<bullet>[(aa,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>Q" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(aa,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(aa,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="ca" and z="c" in alpha_name_coname)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)[1]
apply(simp)
apply(drule_tac x="[(a,ba)]\<bullet>[(xa,c)]\<bullet>[(ba,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>z" in spec)
apply(drule_tac x="[(a,ba)]\<bullet>[(xa,c)]\<bullet>[(ba,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>P" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(ba,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ba)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ba)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(ba,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="cb" and z="ca" in alpha_name_coname)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)[1]
apply(simp)
apply(drule_tac x="[(a,ba)]\<bullet>[(xa,ca)]\<bullet>[(ba,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>c" in spec)
apply(drule_tac x="[(a,ba)]\<bullet>[(xa,ca)]\<bullet>[(ba,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>Q" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(ba,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ba)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ba)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(ba,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(case_tac "a=aa")
apply(simp)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="ca" and z="c" in alpha_name_coname)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)[1]
apply(simp)
apply(drule_tac x="[(aa,ba)]\<bullet>[(xa,c)]\<bullet>[(ba,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>z" in spec)
apply(drule_tac x="[(aa,ba)]\<bullet>[(xa,c)]\<bullet>[(ba,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>P" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(ba,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(aa,ba)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(aa,ba)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(ba,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(simp)
apply(case_tac "ba=aa")
apply(simp)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="ca" and z="c" in alpha_name_coname)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)[1]
apply(simp)
apply(drule_tac x="[(a,aa)]\<bullet>[(xa,c)]\<bullet>[(a,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>z" in spec)
apply(drule_tac x="[(a,aa)]\<bullet>[(xa,c)]\<bullet>[(a,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>P" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,aa)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,aa)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(a,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(simp)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="ca" and z="c" in alpha_name_coname)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)[1]
apply(simp)
apply(drule_tac x="[(a,ba)]\<bullet>[(xa,c)]\<bullet>[(aa,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>z" in spec)
apply(drule_tac x="[(a,ba)]\<bullet>[(xa,c)]\<bullet>[(aa,ca)]\<bullet>[(b,ca)]\<bullet>[(x,c)]\<bullet>P" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(aa,ca)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ba)]" and X="\<parallel>(ty2)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ba)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(xa,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(aa,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,ca)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,c)]" and X="\<parallel>(ty1)\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(case_tac "a=aa")
apply(simp)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="cb" and z="ca" in alpha_name_coname)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)[1]
apply(simp)
apply(drule_tac x="[(aa,ba)]\<bullet>[(xa,ca)]\<bullet>[(ba,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>c" in spec)
apply(drule_tac x="[(aa,ba)]\<bullet>[(xa,ca)]\<bullet>[(ba,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>Q" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(ba,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(aa,ba)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(aa,ba)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(ba,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(simp)
apply(case_tac "ba=aa")
apply(simp)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="cb" and z="ca" in alpha_name_coname)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)[1]
apply(simp)
apply(drule_tac x="[(a,aa)]\<bullet>[(xa,ca)]\<bullet>[(a,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>c" in spec)
apply(drule_tac x="[(a,aa)]\<bullet>[(xa,ca)]\<bullet>[(a,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>Q" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,aa)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,aa)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(a,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(simp)
apply(generate_fresh "name")
apply(generate_fresh "coname")
apply(drule_tac a="cb" and z="ca" in alpha_name_coname)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(simp add: fresh_left calc_atm fresh_prod fresh_atm)
apply(auto)[1]
apply(simp)
apply(drule_tac x="[(a,ba)]\<bullet>[(xa,ca)]\<bullet>[(aa,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>c" in spec)
apply(drule_tac x="[(a,ba)]\<bullet>[(xa,ca)]\<bullet>[(aa,cb)]\<bullet>[(b,cb)]\<bullet>[(x,ca)]\<bullet>Q" in spec)
apply(drule mp)
apply(rule conjI)
apply(auto simp add: calc_atm fresh_prod fresh_atm)[1]
apply(rule conjI)
apply(auto simp add: fresh_left calc_atm fresh_prod fresh_atm)[1]
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(aa,cb)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ba)]" and X="\<parallel><ty1>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(a,ba)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(xa,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(aa,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
apply(drule_tac pi="[(b,cb)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_coname_inst, OF at_coname_inst])
apply(simp add: CAND_eqvt_name CAND_eqvt_coname)
apply(drule_tac pi="[(x,ca)]" and X="\<parallel><ty2>\<parallel>" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
apply(perm_simp add: CAND_eqvt_name CAND_eqvt_coname csubst_eqvt nsubst_eqvt)
done

text {* Main lemma 1 *}

lemma AXIOMS_imply_SNa:
  shows "<a>:M \<in> AXIOMSc B \<Longrightarrow> SNa M"
  and   "(x):M \<in> AXIOMSn B \<Longrightarrow> SNa M"
apply -
apply(auto simp add: AXIOMSn_def AXIOMSc_def ntrm.inject ctrm.inject alpha)
apply(rule Ax_in_SNa)+
done

lemma BINDING_imply_SNa:
  shows "<a>:M \<in> BINDINGc B (\<parallel>(B)\<parallel>) \<Longrightarrow> SNa M"
  and   "(x):M \<in> BINDINGn B (\<parallel><B>\<parallel>) \<Longrightarrow> SNa M"
apply -
apply(auto simp add: BINDINGn_def BINDINGc_def ntrm.inject ctrm.inject alpha)
apply(drule_tac x="x" in spec)
apply(drule_tac x="Ax x a" in spec)
apply(drule mp)
apply(rule Ax_in_CANDs)
apply(drule a_star_preserves_SNa)
apply(rule subst_with_ax2)
apply(simp add: crename_id)
apply(drule_tac x="x" in spec)
apply(drule_tac x="Ax x aa" in spec)
apply(drule mp)
apply(rule Ax_in_CANDs)
apply(drule a_star_preserves_SNa)
apply(rule subst_with_ax2)
apply(simp add: crename_id SNa_eqvt)
apply(drule_tac x="a" in spec)
apply(drule_tac x="Ax x a" in spec)
apply(drule mp)
apply(rule Ax_in_CANDs)
apply(drule a_star_preserves_SNa)
apply(rule subst_with_ax1)
apply(simp add: nrename_id)
apply(drule_tac x="a" in spec)
apply(drule_tac x="Ax xa a" in spec)
apply(drule mp)
apply(rule Ax_in_CANDs)
apply(drule a_star_preserves_SNa)
apply(rule subst_with_ax1)
apply(simp add: nrename_id SNa_eqvt)
done

lemma CANDs_imply_SNa:
  shows "<a>:M \<in> \<parallel><B>\<parallel> \<Longrightarrow> SNa M"
  and   "(x):M \<in> \<parallel>(B)\<parallel> \<Longrightarrow> SNa M"
proof(induct B arbitrary: a x M rule: ty.induct)
  case (PR X)
  { case 1 
    have "<a>:M \<in> \<parallel><PR X>\<parallel>" by fact
    then have "<a>:M \<in> NEGc (PR X) (\<parallel>(PR X)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (PR X) \<union> BINDINGc (PR X) (\<parallel>(PR X)\<parallel>)" by simp
    moreover
    { assume "<a>:M \<in> AXIOMSc (PR X)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (PR X) (\<parallel>(PR X)\<parallel>)"
      then have "SNa M" by (simp add: BINDING_imply_SNa)
    }
    ultimately show "SNa M" by blast 
  next
    case 2
    have "(x):M \<in> (\<parallel>(PR X)\<parallel>)" by fact
    then have "(x):M \<in> NEGn (PR X) (\<parallel><PR X>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (PR X) \<union> BINDINGn (PR X) (\<parallel><PR X>\<parallel>)" by simp
    moreover
    { assume "(x):M \<in> AXIOMSn (PR X)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (PR X) (\<parallel><PR X>\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
    ultimately show "SNa M" by blast
  }
next
  case (NOT B)
  have ih1: "\<And>a M. <a>:M \<in> \<parallel><B>\<parallel> \<Longrightarrow> SNa M" by fact
  have ih2: "\<And>x M. (x):M \<in> \<parallel>(B)\<parallel> \<Longrightarrow> SNa M" by fact
  { case 1
    have "<a>:M \<in> (\<parallel><NOT B>\<parallel>)" by fact
    then have "<a>:M \<in> NEGc (NOT B) (\<parallel>(NOT B)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (NOT B) \<union> BINDINGc (NOT B) (\<parallel>(NOT B)\<parallel>) \<union> NOTRIGHT (NOT B) (\<parallel>(B)\<parallel>)" by simp
     moreover
    { assume "<a>:M \<in> AXIOMSc (NOT B)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (NOT B) (\<parallel>(NOT B)\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
     moreover
    { assume "<a>:M \<in> NOTRIGHT (NOT B) (\<parallel>(B)\<parallel>)"
      then obtain x' M' where eq: "M = NotR (x').M' a" and "(x'):M' \<in> (\<parallel>(B)\<parallel>)"
        using NOTRIGHT_elim by blast
      then have "SNa M'" using ih2 by blast
      then have "SNa M" using eq by (simp add: NotR_in_SNa)
    }
    ultimately show "SNa M" by blast
  next
    case 2
    have "(x):M \<in> (\<parallel>(NOT B)\<parallel>)" by fact
    then have "(x):M \<in> NEGn (NOT B) (\<parallel><NOT B>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (NOT B) \<union> BINDINGn (NOT B) (\<parallel><NOT B>\<parallel>) \<union> NOTLEFT (NOT B) (\<parallel><B>\<parallel>)" 
      by (simp only: NEGn.simps)
     moreover
    { assume "(x):M \<in> AXIOMSn (NOT B)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (NOT B) (\<parallel><NOT B>\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
     moreover
    { assume "(x):M \<in> NOTLEFT (NOT B) (\<parallel><B>\<parallel>)"
      then obtain a' M' where eq: "M = NotL <a'>.M' x" and "<a'>:M' \<in> (\<parallel><B>\<parallel>)"
        using NOTLEFT_elim by blast
      then have "SNa M'" using ih1 by blast
      then have "SNa M" using eq by (simp add: NotL_in_SNa)
    }
    ultimately show "SNa M" by blast
  }
next
  case (AND A B)
  have ih1: "\<And>a M. <a>:M \<in> \<parallel><A>\<parallel> \<Longrightarrow> SNa M" by fact
  have ih2: "\<And>x M. (x):M \<in> \<parallel>(A)\<parallel> \<Longrightarrow> SNa M" by fact
  have ih3: "\<And>a M. <a>:M \<in> \<parallel><B>\<parallel> \<Longrightarrow> SNa M" by fact
  have ih4: "\<And>x M. (x):M \<in> \<parallel>(B)\<parallel> \<Longrightarrow> SNa M" by fact
  { case 1
    have "<a>:M \<in> (\<parallel><A AND B>\<parallel>)" by fact
    then have "<a>:M \<in> NEGc (A AND B) (\<parallel>(A AND B)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (A AND B) \<union> BINDINGc (A AND B) (\<parallel>(A AND B)\<parallel>) 
                                  \<union> ANDRIGHT (A AND B) (\<parallel><A>\<parallel>) (\<parallel><B>\<parallel>)" by simp
     moreover
    { assume "<a>:M \<in> AXIOMSc (A AND B)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (A AND B) (\<parallel>(A AND B)\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
     moreover
    { assume "<a>:M \<in> ANDRIGHT (A AND B) (\<parallel><A>\<parallel>) (\<parallel><B>\<parallel>)"
      then obtain a' M' b' N' where eq: "M = AndR <a'>.M' <b'>.N' a" 
                                and "<a'>:M' \<in> (\<parallel><A>\<parallel>)" and "<b'>:N' \<in> (\<parallel><B>\<parallel>)"
        by (erule_tac ANDRIGHT_elim, blast)
      then have "SNa M'" and "SNa N'" using ih1 ih3 by blast+
      then have "SNa M" using eq by (simp add: AndR_in_SNa)
    }
    ultimately show "SNa M" by blast
  next
    case 2
    have "(x):M \<in> (\<parallel>(A AND B)\<parallel>)" by fact
    then have "(x):M \<in> NEGn (A AND B) (\<parallel><A AND B>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (A AND B) \<union> BINDINGn (A AND B) (\<parallel><A AND B>\<parallel>) 
                       \<union> ANDLEFT1 (A AND B) (\<parallel>(A)\<parallel>) \<union> ANDLEFT2 (A AND B) (\<parallel>(B)\<parallel>)" 
      by (simp only: NEGn.simps)
     moreover
    { assume "(x):M \<in> AXIOMSn (A AND B)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (A AND B) (\<parallel><A AND B>\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
     moreover
    { assume "(x):M \<in> ANDLEFT1 (A AND B) (\<parallel>(A)\<parallel>)"
      then obtain x' M' where eq: "M = AndL1 (x').M' x" and "(x'):M' \<in> (\<parallel>(A)\<parallel>)"
        using ANDLEFT1_elim by blast
      then have "SNa M'" using ih2 by blast
      then have "SNa M" using eq by (simp add: AndL1_in_SNa)
    }
    moreover
    { assume "(x):M \<in> ANDLEFT2 (A AND B) (\<parallel>(B)\<parallel>)"
      then obtain x' M' where eq: "M = AndL2 (x').M' x" and "(x'):M' \<in> (\<parallel>(B)\<parallel>)"
        using ANDLEFT2_elim by blast
      then have "SNa M'" using ih4 by blast
      then have "SNa M" using eq by (simp add: AndL2_in_SNa)
    }
    ultimately show "SNa M" by blast
  }
next
  case (OR A B)
  have ih1: "\<And>a M. <a>:M \<in> \<parallel><A>\<parallel> \<Longrightarrow> SNa M" by fact
  have ih2: "\<And>x M. (x):M \<in> \<parallel>(A)\<parallel> \<Longrightarrow> SNa M" by fact
  have ih3: "\<And>a M. <a>:M \<in> \<parallel><B>\<parallel> \<Longrightarrow> SNa M" by fact
  have ih4: "\<And>x M. (x):M \<in> \<parallel>(B)\<parallel> \<Longrightarrow> SNa M" by fact
  { case 1
    have "<a>:M \<in> (\<parallel><A OR B>\<parallel>)" by fact
    then have "<a>:M \<in> NEGc (A OR B) (\<parallel>(A OR B)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (A OR B) \<union> BINDINGc (A OR B) (\<parallel>(A OR B)\<parallel>) 
                                  \<union> ORRIGHT1 (A OR B) (\<parallel><A>\<parallel>) \<union> ORRIGHT2 (A OR B) (\<parallel><B>\<parallel>)" by simp
     moreover
    { assume "<a>:M \<in> AXIOMSc (A OR B)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (A OR B) (\<parallel>(A OR B)\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
     moreover
    { assume "<a>:M \<in> ORRIGHT1 (A OR B) (\<parallel><A>\<parallel>)"
      then obtain a' M' where eq: "M = OrR1 <a'>.M' a" 
                                and "<a'>:M' \<in> (\<parallel><A>\<parallel>)" 
        by (erule_tac ORRIGHT1_elim, blast)
      then have "SNa M'" using ih1 by blast
      then have "SNa M" using eq by (simp add: OrR1_in_SNa)
    }
     moreover
    { assume "<a>:M \<in> ORRIGHT2 (A OR B) (\<parallel><B>\<parallel>)"
      then obtain a' M' where eq: "M = OrR2 <a'>.M' a" and "<a'>:M' \<in> (\<parallel><B>\<parallel>)" 
        using ORRIGHT2_elim by blast
      then have "SNa M'" using ih3 by blast
      then have "SNa M" using eq by (simp add: OrR2_in_SNa)
    }
    ultimately show "SNa M" by blast
  next
    case 2
    have "(x):M \<in> (\<parallel>(A OR B)\<parallel>)" by fact
    then have "(x):M \<in> NEGn (A OR B) (\<parallel><A OR B>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (A OR B) \<union> BINDINGn (A OR B) (\<parallel><A OR B>\<parallel>) 
                       \<union> ORLEFT (A OR B) (\<parallel>(A)\<parallel>) (\<parallel>(B)\<parallel>)" 
      by (simp only: NEGn.simps)
     moreover
    { assume "(x):M \<in> AXIOMSn (A OR B)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (A OR B) (\<parallel><A OR B>\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
     moreover
    { assume "(x):M \<in> ORLEFT (A OR B) (\<parallel>(A)\<parallel>) (\<parallel>(B)\<parallel>)"
      then obtain x' M' y' N' where eq: "M = OrL (x').M' (y').N' x" 
                                and "(x'):M' \<in> (\<parallel>(A)\<parallel>)" and  "(y'):N' \<in> (\<parallel>(B)\<parallel>)"
        by (erule_tac ORLEFT_elim, blast)
      then have "SNa M'" and "SNa N'" using ih2 ih4 by blast+
      then have "SNa M" using eq by (simp add: OrL_in_SNa)
    }
    ultimately show "SNa M" by blast
  }
next 
  case (IMP A B)
  have ih1: "\<And>a M. <a>:M \<in> \<parallel><A>\<parallel> \<Longrightarrow> SNa M" by fact
  have ih2: "\<And>x M. (x):M \<in> \<parallel>(A)\<parallel> \<Longrightarrow> SNa M" by fact
  have ih3: "\<And>a M. <a>:M \<in> \<parallel><B>\<parallel> \<Longrightarrow> SNa M" by fact
  have ih4: "\<And>x M. (x):M \<in> \<parallel>(B)\<parallel> \<Longrightarrow> SNa M" by fact
  { case 1
    have "<a>:M \<in> (\<parallel><A IMP B>\<parallel>)" by fact
    then have "<a>:M \<in> NEGc (A IMP B) (\<parallel>(A IMP B)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (A IMP B) \<union> BINDINGc (A IMP B) (\<parallel>(A IMP B)\<parallel>) 
                                  \<union> IMPRIGHT (A IMP B) (\<parallel>(A)\<parallel>) (\<parallel><B>\<parallel>) (\<parallel>(B)\<parallel>) (\<parallel><A>\<parallel>)" by simp
     moreover
    { assume "<a>:M \<in> AXIOMSc (A IMP B)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (A IMP B) (\<parallel>(A IMP B)\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
     moreover
    { assume "<a>:M \<in> IMPRIGHT (A IMP B) (\<parallel>(A)\<parallel>) (\<parallel><B>\<parallel>) (\<parallel>(B)\<parallel>) (\<parallel><A>\<parallel>)"
      then obtain x' a' M' where eq: "M = ImpR (x').<a'>.M' a" 
                           and imp: "\<forall>z P. x'\<sharp>(z,P) \<and> (z):P \<in> \<parallel>(B)\<parallel> \<longrightarrow> (x'):(M'{a':=(z).P}) \<in> \<parallel>(A)\<parallel>"    
        by (erule_tac IMPRIGHT_elim, blast)
      obtain z::"name" where fs: "z\<sharp>x'" by (rule_tac exists_fresh, rule fin_supp, blast)
      have "(z):Ax z a'\<in> \<parallel>(B)\<parallel>" by (simp add: Ax_in_CANDs)
      with imp fs have "(x'):(M'{a':=(z).Ax z a'}) \<in> \<parallel>(A)\<parallel>" by (simp add: fresh_prod fresh_atm)
      then have "SNa (M'{a':=(z).Ax z a'})" using ih2 by blast
      moreover 
      have "M'{a':=(z).Ax z a'} \<longrightarrow>\<^isub>a* M'[a'\<turnstile>c>a']" by (simp add: subst_with_ax2)
      ultimately have "SNa (M'[a'\<turnstile>c>a'])" by (simp add: a_star_preserves_SNa)
      then have "SNa M'" by (simp add: crename_id)
      then have "SNa M" using eq by (simp add: ImpR_in_SNa)
    }
    ultimately show "SNa M" by blast
  next
    case 2
    have "(x):M \<in> (\<parallel>(A IMP B)\<parallel>)" by fact
    then have "(x):M \<in> NEGn (A IMP B) (\<parallel><A IMP B>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (A IMP B) \<union> BINDINGn (A IMP B) (\<parallel><A IMP B>\<parallel>) 
                       \<union> IMPLEFT (A IMP B) (\<parallel><A>\<parallel>) (\<parallel>(B)\<parallel>)" 
      by (simp only: NEGn.simps)
     moreover
    { assume "(x):M \<in> AXIOMSn (A IMP B)"
      then have "SNa M" by (simp add: AXIOMS_imply_SNa)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (A IMP B) (\<parallel><A IMP B>\<parallel>)"
      then have "SNa M" by (simp only: BINDING_imply_SNa)
    }
     moreover
    { assume "(x):M \<in> IMPLEFT (A IMP B) (\<parallel><A>\<parallel>) (\<parallel>(B)\<parallel>)"
      then obtain a' M' y' N' where eq: "M = ImpL <a'>.M' (y').N' x" 
                                and "<a'>:M' \<in> (\<parallel><A>\<parallel>)" and  "(y'):N' \<in> (\<parallel>(B)\<parallel>)"
        by (erule_tac IMPLEFT_elim, blast)
      then have "SNa M'" and "SNa N'" using ih1 ih4 by blast+
      then have "SNa M" using eq by (simp add: ImpL_in_SNa)
    }
    ultimately show "SNa M" by blast
  }
qed 

text {* Main lemma 2 *}

lemma AXIOMS_preserved:
  shows "<a>:M \<in> AXIOMSc B \<Longrightarrow> M \<longrightarrow>\<^isub>a* M' \<Longrightarrow> <a>:M' \<in> AXIOMSc B"
  and   "(x):M \<in> AXIOMSn B \<Longrightarrow> M \<longrightarrow>\<^isub>a* M' \<Longrightarrow> (x):M' \<in> AXIOMSn B"
  apply(simp_all add: AXIOMSc_def AXIOMSn_def)
  apply(auto simp add: ntrm.inject ctrm.inject alpha)
  apply(drule ax_do_not_a_star_reduce)
  apply(auto)
  apply(drule ax_do_not_a_star_reduce)
  apply(auto)
  apply(drule ax_do_not_a_star_reduce)
  apply(auto)
  apply(drule ax_do_not_a_star_reduce)
  apply(auto)
  done  

lemma BINDING_preserved:
  shows "<a>:M \<in> BINDINGc B (\<parallel>(B)\<parallel>) \<Longrightarrow> M \<longrightarrow>\<^isub>a* M' \<Longrightarrow> <a>:M' \<in> BINDINGc B (\<parallel>(B)\<parallel>)"
  and   "(x):M \<in> BINDINGn B (\<parallel><B>\<parallel>) \<Longrightarrow> M \<longrightarrow>\<^isub>a* M' \<Longrightarrow> (x):M' \<in> BINDINGn B (\<parallel><B>\<parallel>)"
proof -
  assume red: "M \<longrightarrow>\<^isub>a* M'"
  assume asm: "<a>:M \<in> BINDINGc B (\<parallel>(B)\<parallel>)"
  {
    fix x::"name" and  P::"trm"
    from asm have "((x):P) \<in> (\<parallel>(B)\<parallel>) \<Longrightarrow> SNa (M{a:=(x).P})" by (simp add: BINDINGc_elim)
    moreover
    have "M{a:=(x).P} \<longrightarrow>\<^isub>a* M'{a:=(x).P}" using red by (simp add: a_star_subst2)
    ultimately 
    have "((x):P) \<in> (\<parallel>(B)\<parallel>) \<Longrightarrow> SNa (M'{a:=(x).P})" by (simp add: a_star_preserves_SNa)
  }
  then show "<a>:M' \<in> BINDINGc B (\<parallel>(B)\<parallel>)" by (auto simp add: BINDINGc_def)
next
  assume red: "M \<longrightarrow>\<^isub>a* M'"
  assume asm: "(x):M \<in> BINDINGn B (\<parallel><B>\<parallel>)"
  {
    fix c::"coname" and  P::"trm"
    from asm have "(<c>:P) \<in> (\<parallel><B>\<parallel>) \<Longrightarrow> SNa (M{x:=<c>.P})" by (simp add: BINDINGn_elim)
    moreover
    have "M{x:=<c>.P} \<longrightarrow>\<^isub>a* M'{x:=<c>.P}" using red by (simp add: a_star_subst1)
    ultimately 
    have "(<c>:P) \<in> (\<parallel><B>\<parallel>) \<Longrightarrow> SNa (M'{x:=<c>.P})" by (simp add: a_star_preserves_SNa)
  }
  then show "(x):M' \<in> BINDINGn B (\<parallel><B>\<parallel>)" by (auto simp add: BINDINGn_def)
qed
    
lemma CANDs_preserved:
  shows "<a>:M \<in> \<parallel><B>\<parallel> \<Longrightarrow> M \<longrightarrow>\<^isub>a* M' \<Longrightarrow> <a>:M' \<in> \<parallel><B>\<parallel>"
  and   "(x):M \<in> \<parallel>(B)\<parallel> \<Longrightarrow> M \<longrightarrow>\<^isub>a* M' \<Longrightarrow> (x):M' \<in> \<parallel>(B)\<parallel>" 
proof(nominal_induct B arbitrary: a x M M' rule: ty.strong_induct) 
  case (PR X)
  { case 1 
    have asm: "M \<longrightarrow>\<^isub>a* M'" by fact
    have "<a>:M \<in> \<parallel><PR X>\<parallel>" by fact
    then have "<a>:M \<in> NEGc (PR X) (\<parallel>(PR X)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (PR X) \<union> BINDINGc (PR X) (\<parallel>(PR X)\<parallel>)" by simp
    moreover
    { assume "<a>:M \<in> AXIOMSc (PR X)"
      then have "<a>:M' \<in> AXIOMSc (PR X)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (PR X) (\<parallel>(PR X)\<parallel>)"
      then have "<a>:M' \<in> BINDINGc (PR X) (\<parallel>(PR X)\<parallel>)" using asm by (simp add: BINDING_preserved)
    }
    ultimately have "<a>:M' \<in> AXIOMSc (PR X) \<union> BINDINGc (PR X) (\<parallel>(PR X)\<parallel>)" by blast
    then have "<a>:M' \<in> NEGc (PR X) (\<parallel>(PR X)\<parallel>)" by simp
    then show "<a>:M' \<in> (\<parallel><PR X>\<parallel>)" using NEG_simp by blast
  next
    case 2
    have asm: "M \<longrightarrow>\<^isub>a* M'" by fact
    have "(x):M \<in> \<parallel>(PR X)\<parallel>" by fact
    then have "(x):M \<in> NEGn (PR X) (\<parallel><PR X>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (PR X) \<union> BINDINGn (PR X) (\<parallel><PR X>\<parallel>)" by simp
    moreover
    { assume "(x):M \<in> AXIOMSn (PR X)"
      then have "(x):M' \<in> AXIOMSn (PR X)" using asm by (simp only: AXIOMS_preserved) 
    }
    moreover
    { assume "(x):M \<in> BINDINGn (PR X) (\<parallel><PR X>\<parallel>)"
      then have "(x):M' \<in> BINDINGn (PR X) (\<parallel><PR X>\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    ultimately have "(x):M' \<in> AXIOMSn (PR X) \<union> BINDINGn (PR X) (\<parallel><PR X>\<parallel>)" by blast
    then have "(x):M' \<in> NEGn (PR X) (\<parallel><PR X>\<parallel>)" by simp
    then show "(x):M' \<in> (\<parallel>(PR X)\<parallel>)" using NEG_simp by blast
  }
next
  case (IMP A B)
  have ih1: "\<And>a M M'. \<lbrakk><a>:M \<in> \<parallel><A>\<parallel>; M \<longrightarrow>\<^isub>a* M'\<rbrakk> \<Longrightarrow> <a>:M' \<in> \<parallel><A>\<parallel>" by fact
  have ih2: "\<And>x M M'. \<lbrakk>(x):M \<in> \<parallel>(A)\<parallel>; M \<longrightarrow>\<^isub>a* M'\<rbrakk> \<Longrightarrow> (x):M' \<in> \<parallel>(A)\<parallel>" by fact
  have ih3: "\<And>a M M'. \<lbrakk><a>:M \<in> \<parallel><B>\<parallel>; M \<longrightarrow>\<^isub>a* M'\<rbrakk> \<Longrightarrow> <a>:M' \<in> \<parallel><B>\<parallel>" by fact
  have ih4: "\<And>x M M'. \<lbrakk>(x):M \<in> \<parallel>(B)\<parallel>; M \<longrightarrow>\<^isub>a* M'\<rbrakk> \<Longrightarrow> (x):M' \<in> \<parallel>(B)\<parallel>" by fact
  { case 1 
    have asm: "M \<longrightarrow>\<^isub>a* M'" by fact
    have "<a>:M \<in> \<parallel><A IMP B>\<parallel>" by fact
    then have "<a>:M \<in> NEGc (A IMP B) (\<parallel>(A IMP B)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (A IMP B) \<union> BINDINGc (A IMP B) (\<parallel>(A IMP B)\<parallel>) 
                            \<union> IMPRIGHT (A IMP B) (\<parallel>(A)\<parallel>) (\<parallel><B>\<parallel>) (\<parallel>(B)\<parallel>) (\<parallel><A>\<parallel>)" by simp
    moreover
    { assume "<a>:M \<in> AXIOMSc (A IMP B)"
      then have "<a>:M' \<in> AXIOMSc (A IMP B)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (A IMP B) (\<parallel>(A IMP B)\<parallel>)"
      then have "<a>:M' \<in> BINDINGc (A IMP B) (\<parallel>(A IMP B)\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    moreover
    { assume "<a>:M \<in> IMPRIGHT (A IMP B) (\<parallel>(A)\<parallel>) (\<parallel><B>\<parallel>) (\<parallel>(B)\<parallel>) (\<parallel><A>\<parallel>)"
      then obtain x' a' N' where eq: "M = ImpR (x').<a'>.N' a" and fic: "fic (ImpR (x').<a'>.N' a) a"
                           and imp1: "\<forall>z P. x'\<sharp>(z,P) \<and> (z):P \<in> \<parallel>(B)\<parallel> \<longrightarrow> (x'):(N'{a':=(z).P}) \<in> \<parallel>(A)\<parallel>" 
                           and imp2: "\<forall>c Q. a'\<sharp>(c,Q) \<and> <c>:Q \<in> \<parallel><A>\<parallel> \<longrightarrow> <a'>:(N'{x':=<c>.Q}) \<in> \<parallel><B>\<parallel>"
        using IMPRIGHT_elim by blast
      from eq asm obtain N'' where eq': "M' = ImpR (x').<a'>.N'' a" and red: "N' \<longrightarrow>\<^isub>a* N''" 
        using a_star_redu_ImpR_elim by (blast)
      from imp1 have "\<forall>z P. x'\<sharp>(z,P) \<and> (z):P \<in> \<parallel>(B)\<parallel> \<longrightarrow> (x'):(N''{a':=(z).P}) \<in> \<parallel>(A)\<parallel>" using red ih2
        apply(auto)
        apply(drule_tac x="z" in spec)
        apply(drule_tac x="P" in spec)
        apply(simp)
        apply(drule_tac a_star_subst2)
        apply(blast)
        done
      moreover
      from imp2 have "\<forall>c Q. a'\<sharp>(c,Q) \<and> <c>:Q \<in> \<parallel><A>\<parallel> \<longrightarrow> <a'>:(N''{x':=<c>.Q}) \<in> \<parallel><B>\<parallel>" using red ih3
        apply(auto)
        apply(drule_tac x="c" in spec)
        apply(drule_tac x="Q" in spec)
        apply(simp)
        apply(drule_tac a_star_subst1)
        apply(blast)
        done
      moreover
      from fic have "fic M' a" using eq asm by (simp add: fic_a_star_reduce)
      ultimately have "<a>:M' \<in> IMPRIGHT (A IMP B) (\<parallel>(A)\<parallel>) (\<parallel><B>\<parallel>) (\<parallel>(B)\<parallel>) (\<parallel><A>\<parallel>)" using eq' by auto
    }
    ultimately have "<a>:M' \<in> AXIOMSc (A IMP B) \<union> BINDINGc (A IMP B) (\<parallel>(A IMP B)\<parallel>)
                                            \<union> IMPRIGHT (A IMP B) (\<parallel>(A)\<parallel>) (\<parallel><B>\<parallel>) (\<parallel>(B)\<parallel>) (\<parallel><A>\<parallel>)" by blast
    then have "<a>:M' \<in> NEGc (A IMP B) (\<parallel>(A IMP B)\<parallel>)" by simp
    then show "<a>:M' \<in> (\<parallel><A IMP B>\<parallel>)" using NEG_simp by blast
  next
    case 2
    have asm: "M \<longrightarrow>\<^isub>a* M'" by fact
    have "(x):M \<in> \<parallel>(A IMP B)\<parallel>" by fact
    then have "(x):M \<in> NEGn (A IMP B) (\<parallel><A IMP B>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (A IMP B) \<union> BINDINGn (A IMP B) (\<parallel><A IMP B>\<parallel>) 
                                              \<union> IMPLEFT (A IMP B) (\<parallel><A>\<parallel>) (\<parallel>(B)\<parallel>)" by simp
    moreover
    { assume "(x):M \<in> AXIOMSn (A IMP B)"
      then have "(x):M' \<in> AXIOMSn (A IMP B)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (A IMP B) (\<parallel><A IMP B>\<parallel>)"
      then have "(x):M' \<in> BINDINGn (A IMP B) (\<parallel><A IMP B>\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    moreover
    { assume "(x):M \<in> IMPLEFT (A IMP B) (\<parallel><A>\<parallel>) (\<parallel>(B)\<parallel>)"
      then obtain a' T' y' N' where eq: "M = ImpL <a'>.T' (y').N' x" 
                             and fin: "fin (ImpL <a'>.T' (y').N' x) x"
                             and imp1: "<a'>:T' \<in> \<parallel><A>\<parallel>" and imp2: "(y'):N' \<in> \<parallel>(B)\<parallel>"
        by (erule_tac IMPLEFT_elim, blast)
      from eq asm obtain T'' N'' where eq': "M' = ImpL <a'>.T'' (y').N'' x" 
                                 and red1: "T' \<longrightarrow>\<^isub>a* T''"  and red2: "N' \<longrightarrow>\<^isub>a* N''"
        using a_star_redu_ImpL_elim by blast
      from fin have "fin M' x" using eq asm by (simp add: fin_a_star_reduce)
      moreover
      from imp1 red1 have "<a'>:T'' \<in> \<parallel><A>\<parallel>" using ih1 by simp
      moreover
      from imp2 red2 have "(y'):N'' \<in> \<parallel>(B)\<parallel>" using ih4 by simp
      ultimately have "(x):M' \<in> IMPLEFT (A IMP B) (\<parallel><A>\<parallel>) (\<parallel>(B)\<parallel>)" using eq' by (simp, blast) 
    }
    ultimately have "(x):M' \<in> AXIOMSn (A IMP B) \<union> BINDINGn (A IMP B) (\<parallel><A IMP B>\<parallel>)
                                              \<union> IMPLEFT (A IMP B) (\<parallel><A>\<parallel>) (\<parallel>(B)\<parallel>)" by blast
    then have "(x):M' \<in> NEGn (A IMP B) (\<parallel><A IMP B>\<parallel>)" by simp
    then show "(x):M' \<in> (\<parallel>(A IMP B)\<parallel>)" using NEG_simp by blast
  }
next
  case (AND A B)
  have ih1: "\<And>a M M'. \<lbrakk><a>:M \<in> \<parallel><A>\<parallel>; M \<longrightarrow>\<^isub>a* M'\<rbrakk> \<Longrightarrow> <a>:M' \<in> \<parallel><A>\<parallel>" by fact
  have ih2: "\<And>x M M'. \<lbrakk>(x):M \<in> \<parallel>(A)\<parallel>; M \<longrightarrow>\<^isub>a* M'\<rbrakk> \<Longrightarrow> (x):M' \<in> \<parallel>(A)\<parallel>" by fact
  have ih3: "\<And>a M M'. \<lbrakk><a>:M \<in> \<parallel><B>\<parallel>; M \<longrightarrow>\<^isub>a* M'\<rbrakk> \<Longrightarrow> <a>:M' \<in> \<parallel><B>\<parallel>" by fact
  have ih4: "\<And>x M M'. \<lbrakk>(x):M \<in> \<parallel>(B)\<parallel>; M \<longrightarrow>\<^isub>a* M'\<rbrakk> \<Longrightarrow> (x):M' \<in> \<parallel>(B)\<parallel>" by fact
  { case 1 
    have asm: "M \<longrightarrow>\<^isub>a* M'" by fact
    have "<a>:M \<in> \<parallel><A AND B>\<parallel>" by fact
    then have "<a>:M \<in> NEGc (A AND B) (\<parallel>(A AND B)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (A AND B) \<union> BINDINGc (A AND B) (\<parallel>(A AND B)\<parallel>) 
                                              \<union> ANDRIGHT (A AND B) (\<parallel><A>\<parallel>) (\<parallel><B>\<parallel>)" by simp
    moreover
    { assume "<a>:M \<in> AXIOMSc (A AND B)"
      then have "<a>:M' \<in> AXIOMSc (A AND B)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (A AND B) (\<parallel>(A AND B)\<parallel>)"
      then have "<a>:M' \<in> BINDINGc (A AND B) (\<parallel>(A AND B)\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    moreover
    { assume "<a>:M \<in> ANDRIGHT (A AND B) (\<parallel><A>\<parallel>) (\<parallel><B>\<parallel>)"
      then obtain a' T' b' N' where eq: "M = AndR <a'>.T' <b'>.N' a" 
                              and fic: "fic (AndR <a'>.T' <b'>.N' a) a"
                           and imp1: "<a'>:T' \<in> \<parallel><A>\<parallel>" and imp2: "<b'>:N' \<in> \<parallel><B>\<parallel>"
        using ANDRIGHT_elim by blast
      from eq asm obtain T'' N'' where eq': "M' = AndR <a'>.T'' <b'>.N'' a" 
                          and red1: "T' \<longrightarrow>\<^isub>a* T''" and red2: "N' \<longrightarrow>\<^isub>a* N''" 
        using a_star_redu_AndR_elim by blast
      from fic have "fic M' a" using eq asm by (simp add: fic_a_star_reduce)
      moreover
      from imp1 red1 have "<a'>:T'' \<in> \<parallel><A>\<parallel>" using ih1 by simp
      moreover
      from imp2 red2 have "<b'>:N'' \<in> \<parallel><B>\<parallel>" using ih3 by simp
      ultimately have "<a>:M' \<in> ANDRIGHT (A AND B) (\<parallel><A>\<parallel>) (\<parallel><B>\<parallel>)" using eq' by (simp, blast) 
    }
    ultimately have "<a>:M' \<in> AXIOMSc (A AND B) \<union> BINDINGc (A AND B) (\<parallel>(A AND B)\<parallel>)
                                              \<union> ANDRIGHT (A AND B) (\<parallel><A>\<parallel>) (\<parallel><B>\<parallel>)" by blast
    then have "<a>:M' \<in> NEGc (A AND B) (\<parallel>(A AND B)\<parallel>)" by simp
    then show "<a>:M' \<in> (\<parallel><A AND B>\<parallel>)" using NEG_simp by blast
  next
    case 2
    have asm: "M \<longrightarrow>\<^isub>a* M'" by fact
    have "(x):M \<in> \<parallel>(A AND B)\<parallel>" by fact
    then have "(x):M \<in> NEGn (A AND B) (\<parallel><A AND B>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (A AND B) \<union> BINDINGn (A AND B) (\<parallel><A AND B>\<parallel>) 
                                     \<union> ANDLEFT1 (A AND B) (\<parallel>(A)\<parallel>) \<union> ANDLEFT2 (A AND B) (\<parallel>(B)\<parallel>)" by simp
    moreover
    { assume "(x):M \<in> AXIOMSn (A AND B)"
      then have "(x):M' \<in> AXIOMSn (A AND B)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (A AND B) (\<parallel><A AND B>\<parallel>)"
      then have "(x):M' \<in> BINDINGn (A AND B) (\<parallel><A AND B>\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    moreover
    { assume "(x):M \<in> ANDLEFT1 (A AND B) (\<parallel>(A)\<parallel>)"
      then obtain y' N' where eq: "M = AndL1 (y').N' x" 
                             and fin: "fin (AndL1 (y').N' x) x" and imp: "(y'):N' \<in> \<parallel>(A)\<parallel>"
        by (erule_tac ANDLEFT1_elim, blast)
      from eq asm obtain N'' where eq': "M' = AndL1 (y').N'' x" and red1: "N' \<longrightarrow>\<^isub>a* N''"
        using a_star_redu_AndL1_elim by blast
      from fin have "fin M' x" using eq asm by (simp add: fin_a_star_reduce)
      moreover
      from imp red1 have "(y'):N'' \<in> \<parallel>(A)\<parallel>" using ih2 by simp
      ultimately have "(x):M' \<in> ANDLEFT1 (A AND B) (\<parallel>(A)\<parallel>)" using eq' by (simp, blast) 
    }
     moreover
    { assume "(x):M \<in> ANDLEFT2 (A AND B) (\<parallel>(B)\<parallel>)"
      then obtain y' N' where eq: "M = AndL2 (y').N' x" 
                             and fin: "fin (AndL2 (y').N' x) x" and imp: "(y'):N' \<in> \<parallel>(B)\<parallel>"
        by (erule_tac ANDLEFT2_elim, blast)
      from eq asm obtain N'' where eq': "M' = AndL2 (y').N'' x" and red1: "N' \<longrightarrow>\<^isub>a* N''"
        using a_star_redu_AndL2_elim by blast
      from fin have "fin M' x" using eq asm by (simp add: fin_a_star_reduce)
      moreover
      from imp red1 have "(y'):N'' \<in> \<parallel>(B)\<parallel>" using ih4 by simp
      ultimately have "(x):M' \<in> ANDLEFT2 (A AND B) (\<parallel>(B)\<parallel>)" using eq' by (simp, blast) 
    }
    ultimately have "(x):M' \<in> AXIOMSn (A AND B) \<union> BINDINGn (A AND B) (\<parallel><A AND B>\<parallel>)
                               \<union> ANDLEFT1 (A AND B) (\<parallel>(A)\<parallel>) \<union> ANDLEFT2 (A AND B) (\<parallel>(B)\<parallel>)" by blast
    then have "(x):M' \<in> NEGn (A AND B) (\<parallel><A AND B>\<parallel>)" by simp
    then show "(x):M' \<in> (\<parallel>(A AND B)\<parallel>)" using NEG_simp by blast
  }
next    
 case (OR A B)
  have ih1: "\<And>a M M'. \<lbrakk><a>:M \<in> \<parallel><A>\<parallel>; M \<longrightarrow>\<^isub>a* M'\<rbrakk> \<Longrightarrow> <a>:M' \<in> \<parallel><A>\<parallel>" by fact
  have ih2: "\<And>x M M'. \<lbrakk>(x):M \<in> \<parallel>(A)\<parallel>; M \<longrightarrow>\<^isub>a* M'\<rbrakk> \<Longrightarrow> (x):M' \<in> \<parallel>(A)\<parallel>" by fact
  have ih3: "\<And>a M M'. \<lbrakk><a>:M \<in> \<parallel><B>\<parallel>; M \<longrightarrow>\<^isub>a* M'\<rbrakk> \<Longrightarrow> <a>:M' \<in> \<parallel><B>\<parallel>" by fact
  have ih4: "\<And>x M M'. \<lbrakk>(x):M \<in> \<parallel>(B)\<parallel>; M \<longrightarrow>\<^isub>a* M'\<rbrakk> \<Longrightarrow> (x):M' \<in> \<parallel>(B)\<parallel>" by fact
  { case 1 
    have asm: "M \<longrightarrow>\<^isub>a* M'" by fact
    have "<a>:M \<in> \<parallel><A OR B>\<parallel>" by fact
    then have "<a>:M \<in> NEGc (A OR B) (\<parallel>(A OR B)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (A OR B) \<union> BINDINGc (A OR B) (\<parallel>(A OR B)\<parallel>) 
                          \<union> ORRIGHT1 (A OR B) (\<parallel><A>\<parallel>) \<union> ORRIGHT2 (A OR B) (\<parallel><B>\<parallel>)" by simp
    moreover
    { assume "<a>:M \<in> AXIOMSc (A OR B)"
      then have "<a>:M' \<in> AXIOMSc (A OR B)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (A OR B) (\<parallel>(A OR B)\<parallel>)"
      then have "<a>:M' \<in> BINDINGc (A OR B) (\<parallel>(A OR B)\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    moreover
    { assume "<a>:M \<in> ORRIGHT1 (A OR B) (\<parallel><A>\<parallel>)"
      then obtain a' N' where eq: "M = OrR1 <a'>.N' a" 
                              and fic: "fic (OrR1 <a'>.N' a) a" and imp1: "<a'>:N' \<in> \<parallel><A>\<parallel>"
        using ORRIGHT1_elim by blast
      from eq asm obtain N'' where eq': "M' = OrR1 <a'>.N'' a" and red1: "N' \<longrightarrow>\<^isub>a* N''" 
        using a_star_redu_OrR1_elim by blast
      from fic have "fic M' a" using eq asm by (simp add: fic_a_star_reduce)
      moreover
      from imp1 red1 have "<a'>:N'' \<in> \<parallel><A>\<parallel>" using ih1 by simp
      ultimately have "<a>:M' \<in> ORRIGHT1 (A OR B) (\<parallel><A>\<parallel>)" using eq' by (simp, blast) 
    }
    moreover
    { assume "<a>:M \<in> ORRIGHT2 (A OR B) (\<parallel><B>\<parallel>)"
      then obtain a' N' where eq: "M = OrR2 <a'>.N' a" 
                              and fic: "fic (OrR2 <a'>.N' a) a" and imp1: "<a'>:N' \<in> \<parallel><B>\<parallel>"
        using ORRIGHT2_elim by blast
      from eq asm obtain N'' where eq': "M' = OrR2 <a'>.N'' a" and red1: "N' \<longrightarrow>\<^isub>a* N''" 
        using a_star_redu_OrR2_elim by blast
      from fic have "fic M' a" using eq asm by (simp add: fic_a_star_reduce)
      moreover
      from imp1 red1 have "<a'>:N'' \<in> \<parallel><B>\<parallel>" using ih3 by simp
      ultimately have "<a>:M' \<in> ORRIGHT2 (A OR B) (\<parallel><B>\<parallel>)" using eq' by (simp, blast) 
    }
    ultimately have "<a>:M' \<in> AXIOMSc (A OR B) \<union> BINDINGc (A OR B) (\<parallel>(A OR B)\<parallel>)
                                \<union> ORRIGHT1 (A OR B) (\<parallel><A>\<parallel>) \<union> ORRIGHT2 (A OR B) (\<parallel><B>\<parallel>)" by blast
    then have "<a>:M' \<in> NEGc (A OR B) (\<parallel>(A OR B)\<parallel>)" by simp
    then show "<a>:M' \<in> (\<parallel><A OR B>\<parallel>)" using NEG_simp by blast
  next
    case 2
    have asm: "M \<longrightarrow>\<^isub>a* M'" by fact
    have "(x):M \<in> \<parallel>(A OR B)\<parallel>" by fact
    then have "(x):M \<in> NEGn (A OR B) (\<parallel><A OR B>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (A OR B) \<union> BINDINGn (A OR B) (\<parallel><A OR B>\<parallel>) 
                                     \<union> ORLEFT (A OR B) (\<parallel>(A)\<parallel>) (\<parallel>(B)\<parallel>)" by simp
    moreover
    { assume "(x):M \<in> AXIOMSn (A OR B)"
      then have "(x):M' \<in> AXIOMSn (A OR B)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (A OR B) (\<parallel><A OR B>\<parallel>)"
      then have "(x):M' \<in> BINDINGn (A OR B) (\<parallel><A OR B>\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    moreover
    { assume "(x):M \<in> ORLEFT (A OR B) (\<parallel>(A)\<parallel>) (\<parallel>(B)\<parallel>)"
      then obtain y' T' z' N' where eq: "M = OrL (y').T' (z').N' x" 
                             and fin: "fin (OrL (y').T' (z').N' x) x" 
                             and imp1: "(y'):T' \<in> \<parallel>(A)\<parallel>" and imp2: "(z'):N' \<in> \<parallel>(B)\<parallel>"
        by (erule_tac ORLEFT_elim, blast)
      from eq asm obtain T'' N'' where eq': "M' = OrL (y').T'' (z').N'' x" 
                and red1: "T' \<longrightarrow>\<^isub>a* T''" and red2: "N' \<longrightarrow>\<^isub>a* N''"
        using a_star_redu_OrL_elim by blast
      from fin have "fin M' x" using eq asm by (simp add: fin_a_star_reduce)
      moreover
      from imp1 red1 have "(y'):T'' \<in> \<parallel>(A)\<parallel>" using ih2 by simp
      moreover
      from imp2 red2 have "(z'):N'' \<in> \<parallel>(B)\<parallel>" using ih4 by simp
      ultimately have "(x):M' \<in> ORLEFT (A OR B) (\<parallel>(A)\<parallel>) (\<parallel>(B)\<parallel>)" using eq' by (simp, blast) 
    }
    ultimately have "(x):M' \<in> AXIOMSn (A OR B) \<union> BINDINGn (A OR B) (\<parallel><A OR B>\<parallel>)
                               \<union> ORLEFT (A OR B) (\<parallel>(A)\<parallel>) (\<parallel>(B)\<parallel>)" by blast
    then have "(x):M' \<in> NEGn (A OR B) (\<parallel><A OR B>\<parallel>)" by simp
    then show "(x):M' \<in> (\<parallel>(A OR B)\<parallel>)" using NEG_simp by blast
  }
next
  case (NOT A)
  have ih1: "\<And>a M M'. \<lbrakk><a>:M \<in> \<parallel><A>\<parallel>; M \<longrightarrow>\<^isub>a* M'\<rbrakk> \<Longrightarrow> <a>:M' \<in> \<parallel><A>\<parallel>" by fact
  have ih2: "\<And>x M M'. \<lbrakk>(x):M \<in> \<parallel>(A)\<parallel>; M \<longrightarrow>\<^isub>a* M'\<rbrakk> \<Longrightarrow> (x):M' \<in> \<parallel>(A)\<parallel>" by fact
  { case 1 
    have asm: "M \<longrightarrow>\<^isub>a* M'" by fact
    have "<a>:M \<in> \<parallel><NOT A>\<parallel>" by fact
    then have "<a>:M \<in> NEGc (NOT A) (\<parallel>(NOT A)\<parallel>)" by simp
    then have "<a>:M \<in> AXIOMSc (NOT A) \<union> BINDINGc (NOT A) (\<parallel>(NOT A)\<parallel>) 
                                              \<union> NOTRIGHT (NOT A) (\<parallel>(A)\<parallel>)" by simp
    moreover
    { assume "<a>:M \<in> AXIOMSc (NOT A)"
      then have "<a>:M' \<in> AXIOMSc (NOT A)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "<a>:M \<in> BINDINGc (NOT A) (\<parallel>(NOT A)\<parallel>)"
      then have "<a>:M' \<in> BINDINGc (NOT A) (\<parallel>(NOT A)\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    moreover
    { assume "<a>:M \<in> NOTRIGHT (NOT A) (\<parallel>(A)\<parallel>)"
      then obtain y' N' where eq: "M = NotR (y').N' a" 
                              and fic: "fic (NotR (y').N' a) a" and imp: "(y'):N' \<in> \<parallel>(A)\<parallel>"
        using NOTRIGHT_elim by blast
      from eq asm obtain N'' where eq': "M' = NotR (y').N'' a" and red: "N' \<longrightarrow>\<^isub>a* N''" 
        using a_star_redu_NotR_elim by blast
      from fic have "fic M' a" using eq asm by (simp add: fic_a_star_reduce)
      moreover
      from imp red have "(y'):N'' \<in> \<parallel>(A)\<parallel>" using ih2 by simp
      ultimately have "<a>:M' \<in> NOTRIGHT (NOT A) (\<parallel>(A)\<parallel>)" using eq' by (simp, blast) 
    }
    ultimately have "<a>:M' \<in> AXIOMSc (NOT A) \<union> BINDINGc (NOT A) (\<parallel>(NOT A)\<parallel>)
                                              \<union> NOTRIGHT (NOT A) (\<parallel>(A)\<parallel>)" by blast
    then have "<a>:M' \<in> NEGc (NOT A) (\<parallel>(NOT A)\<parallel>)" by simp
    then show "<a>:M' \<in> (\<parallel><NOT A>\<parallel>)" using NEG_simp by blast
  next
    case 2
    have asm: "M \<longrightarrow>\<^isub>a* M'" by fact
    have "(x):M \<in> \<parallel>(NOT A)\<parallel>" by fact
    then have "(x):M \<in> NEGn (NOT A) (\<parallel><NOT A>\<parallel>)" using NEG_simp by blast
    then have "(x):M \<in> AXIOMSn (NOT A) \<union> BINDINGn (NOT A) (\<parallel><NOT A>\<parallel>) 
                                     \<union> NOTLEFT (NOT A) (\<parallel><A>\<parallel>)" by simp
    moreover
    { assume "(x):M \<in> AXIOMSn (NOT A)"
      then have "(x):M' \<in> AXIOMSn (NOT A)" using asm by (simp only: AXIOMS_preserved)
    }
    moreover
    { assume "(x):M \<in> BINDINGn (NOT A) (\<parallel><NOT A>\<parallel>)"
      then have "(x):M' \<in> BINDINGn (NOT A) (\<parallel><NOT A>\<parallel>)" using asm by (simp only: BINDING_preserved)
    }
    moreover
    { assume "(x):M \<in> NOTLEFT (NOT A) (\<parallel><A>\<parallel>)"
      then obtain a' N' where eq: "M = NotL <a'>.N' x" 
                             and fin: "fin (NotL <a'>.N' x) x" and imp: "<a'>:N' \<in> \<parallel><A>\<parallel>"
        by (erule_tac NOTLEFT_elim, blast)
      from eq asm obtain N'' where eq': "M' = NotL <a'>.N'' x" and red1: "N' \<longrightarrow>\<^isub>a* N''"
        using a_star_redu_NotL_elim by blast
      from fin have "fin M' x" using eq asm by (simp add: fin_a_star_reduce)
      moreover
      from imp red1 have "<a'>:N'' \<in> \<parallel><A>\<parallel>" using ih1 by simp
      ultimately have "(x):M' \<in> NOTLEFT (NOT A) (\<parallel><A>\<parallel>)" using eq' by (simp, blast) 
    }
    ultimately have "(x):M' \<in> AXIOMSn (NOT A) \<union> BINDINGn (NOT A) (\<parallel><NOT A>\<parallel>)
                               \<union> NOTLEFT (NOT A) (\<parallel><A>\<parallel>)" by blast
    then have "(x):M' \<in> NEGn (NOT A) (\<parallel><NOT A>\<parallel>)" by simp
    then show "(x):M' \<in> (\<parallel>(NOT A)\<parallel>)" using NEG_simp by blast
  }
qed

lemma CANDs_preserved_single:
  shows "<a>:M \<in> \<parallel><B>\<parallel> \<Longrightarrow> M \<longrightarrow>\<^isub>a M' \<Longrightarrow> <a>:M' \<in> \<parallel><B>\<parallel>"
  and   "(x):M \<in> \<parallel>(B)\<parallel> \<Longrightarrow> M \<longrightarrow>\<^isub>a M' \<Longrightarrow> (x):M' \<in> \<parallel>(B)\<parallel>"
by (auto simp add: a_starI CANDs_preserved)

lemma fic_CANDS:
  assumes a: "\<not>fic M a"
  and     b: "<a>:M \<in> \<parallel><B>\<parallel>"
  shows "<a>:M \<in> AXIOMSc B \<or> <a>:M \<in> BINDINGc B (\<parallel>(B)\<parallel>)"
using a b
apply(nominal_induct B rule: ty.strong_induct)
apply(simp)
apply(simp)
apply(erule disjE)
apply(simp)
apply(erule disjE)
apply(simp)
apply(auto simp add: ctrm.inject)[1]
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(auto simp add: calc_atm)[1]
apply(drule_tac pi="[(a,aa)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(simp)
apply(erule disjE)
apply(simp)
apply(erule disjE)
apply(simp)
apply(auto simp add: ctrm.inject)[1]
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(erule conjE)+
apply(simp)
apply(drule_tac pi="[(a,c)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(simp)
apply(erule disjE)
apply(simp)
apply(erule disjE)
apply(simp)
apply(auto simp add: ctrm.inject)[1]
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(erule conjE)+
apply(simp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(erule conjE)+
apply(simp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
apply(simp)
apply(erule disjE)
apply(simp)
apply(erule disjE)
apply(simp)
apply(auto simp add: ctrm.inject)[1]
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(erule conjE)+
apply(simp)
apply(drule_tac pi="[(a,b)]" in fic.eqvt(2))
apply(simp add: calc_atm)
done

lemma fin_CANDS_aux:
  assumes a: "\<not>fin M x"
  and     b: "(x):M \<in> (NEGn B (\<parallel><B>\<parallel>))"
  shows "(x):M \<in> AXIOMSn B \<or> (x):M \<in> BINDINGn B (\<parallel><B>\<parallel>)"
using a b
apply(nominal_induct B rule: ty.strong_induct)
apply(simp)
apply(simp)
apply(erule disjE)
apply(simp)
apply(erule disjE)
apply(simp)
apply(auto simp add: ntrm.inject)[1]
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(auto simp add: calc_atm)[1]
apply(drule_tac pi="[(x,xa)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(simp)
apply(erule disjE)
apply(simp)
apply(erule disjE)
apply(simp)
apply(auto simp add: ntrm.inject)[1]
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(erule conjE)+
apply(simp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(erule conjE)+
apply(simp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(simp)
apply(erule disjE)
apply(simp)
apply(erule disjE)
apply(simp)
apply(auto simp add: ntrm.inject)[1]
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(erule conjE)+
apply(simp)
apply(drule_tac pi="[(x,z)]" in fin.eqvt(1))
apply(simp add: calc_atm)
apply(simp)
apply(erule disjE)
apply(simp)
apply(erule disjE)
apply(simp)
apply(auto simp add: ntrm.inject)[1]
apply(simp add: alpha)
apply(erule disjE)
apply(simp)
apply(erule conjE)+
apply(simp)
apply(drule_tac pi="[(x,y)]" in fin.eqvt(1))
apply(simp add: calc_atm)
done

lemma fin_CANDS:
  assumes a: "\<not>fin M x"
  and     b: "(x):M \<in> (\<parallel>(B)\<parallel>)"
  shows "(x):M \<in> AXIOMSn B \<or> (x):M \<in> BINDINGn B (\<parallel><B>\<parallel>)"
apply(rule fin_CANDS_aux)
apply(rule a)
apply(rule NEG_elim)
apply(rule b)
done

lemma BINDING_implies_CAND:
  shows "<c>:M \<in> BINDINGc B (\<parallel>(B)\<parallel>) \<Longrightarrow> <c>:M \<in> (\<parallel><B>\<parallel>)"
  and   "(x):N \<in> BINDINGn B (\<parallel><B>\<parallel>) \<Longrightarrow> (x):N \<in> (\<parallel>(B)\<parallel>)"
apply -
apply(nominal_induct B rule: ty.strong_induct)
apply(auto)
apply(rule NEG_intro)
apply(nominal_induct B rule: ty.strong_induct)
apply(auto)
done

end
