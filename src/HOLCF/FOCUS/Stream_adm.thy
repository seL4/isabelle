(*  Title:      HOLCF/ex/Stream_adm.thy
    ID:         $Id$
    Author:     David von Oheimb, TU Muenchen
*)

header {* Admissibility for streams *}

theory Stream_adm
imports Stream Continuity
begin

definition

  stream_monoP  :: "(('a stream) set \<Rightarrow> ('a stream) set) \<Rightarrow> bool"
  "stream_monoP F = (\<exists>Q i. \<forall>P s. Fin i \<le> #s \<longrightarrow>
                    (s \<in> F P) = (stream_take i\<cdot>s \<in> Q \<and> iterate i\<cdot>rt\<cdot>s \<in> P))"

  stream_antiP  :: "(('a stream) set \<Rightarrow> ('a stream) set) \<Rightarrow> bool"
  "stream_antiP F = (\<forall>P x. \<exists>Q i.
                (#x  < Fin i \<longrightarrow> (\<forall>y. x \<sqsubseteq> y \<longrightarrow> y \<in> F P \<longrightarrow> x \<in> F P)) \<and>
                (Fin i <= #x \<longrightarrow> (\<forall>y. x \<sqsubseteq> y \<longrightarrow>
                (y \<in> F P) = (stream_take i\<cdot>y \<in> Q \<and> iterate i\<cdot>rt\<cdot>y \<in> P))))"

  antitonP :: "'a set => bool"
  "antitonP P = (\<forall>x y. x \<sqsubseteq> y \<longrightarrow> y\<in>P \<longrightarrow> x\<in>P)"


(* ----------------------------------------------------------------------- *)

section "admissibility"

lemma flatstream_adm_lemma:
  assumes 1: "chain Y"
  assumes 2: "!i. P (Y i)"
  assumes 3: "(!!Y. [| chain Y; !i. P (Y i); !k. ? j. Fin k < #((Y j)::'a::flat stream)|]
  ==> P(lub (range Y)))"
  shows "P(lub (range Y))"
apply (rule increasing_chain_adm_lemma [OF 1 2])
apply (erule 3, assumption)
apply (erule thin_rl)
apply (rule allI)
apply (case_tac "!j. stream_finite (Y j)")
apply ( rule chain_incr)
apply ( rule allI)
apply ( drule spec)
apply ( safe)
apply ( rule exI)
apply ( rule slen_strict_mono)
apply (   erule spec)
apply (  assumption)
apply ( assumption)
apply (drule not_ex [THEN iffD1])
apply (subst slen_infinite)
apply (erule thin_rl)
apply (drule spec)
apply (fold ile_def)
apply (erule ile_iless_trans [THEN Infty_eq [THEN iffD1]])
apply (simp)
done


(* should be without reference to stream length? *)
lemma flatstream_admI: "[|(!!Y. [| chain Y; !i. P (Y i); 
 !k. ? j. Fin k < #((Y j)::'a::flat stream)|] ==> P(lub (range Y)))|]==> adm P"
apply (unfold adm_def)
apply (intro strip)
apply (erule (1) flatstream_adm_lemma)
apply (fast)
done


(* context (theory "Nat_InFinity");*)
lemma ile_lemma: "Fin (i + j) <= x ==> Fin i <= x"
apply (rule ile_trans)
prefer 2
apply  (assumption)
apply (simp)
done

lemma stream_monoP2I:
"!!X. stream_monoP F ==> !i. ? l. !x y. 
  Fin l <= #x --> (x::'a::flat stream) << y --> x:down_iterate F i --> y:down_iterate F i"
apply (unfold stream_monoP_def)
apply (safe)
apply (rule_tac x="i*ia" in exI)
apply (induct_tac "ia")
apply ( simp)
apply (simp)
apply (intro strip)
apply (erule allE, erule all_dupE, drule mp, erule ile_lemma)
apply (drule_tac P="%x. x" in subst, assumption)
apply (erule allE, drule mp, rule ile_lemma) back
apply ( erule ile_trans)
apply ( erule slen_mono)
apply (erule ssubst)
apply (safe)
apply ( erule (2) ile_lemma [THEN slen_take_lemma3, THEN subst])
apply (erule allE)
apply (drule mp)
apply ( erule slen_rt_mult)
apply (erule allE)
apply (drule mp)
apply (erule monofun_rt_mult)
apply (drule (1) mp)
apply (assumption)
done

lemma stream_monoP2_gfp_admI: "[| !i. ? l. !x y. 
 Fin l <= #x --> (x::'a::flat stream) << y --> x:down_iterate F i --> y:down_iterate F i;
    down_cont F |] ==> adm (%x. x:gfp F)"
apply (erule INTER_down_iterate_is_gfp [THEN ssubst]) (* cont *)
apply (simp (no_asm))
apply (rule adm_lemmas)
apply (rule flatstream_admI)
apply (erule allE)
apply (erule exE)
apply (erule allE, erule exE)
apply (erule allE, erule allE, drule mp) (* stream_monoP *)
apply ( drule ileI1)
apply ( drule ile_trans)
apply (  rule ile_iSuc)
apply ( drule iSuc_ile_mono [THEN iffD1])
apply ( assumption)
apply (drule mp)
apply ( erule is_ub_thelub)
apply (fast)
done

lemmas fstream_gfp_admI = stream_monoP2I [THEN stream_monoP2_gfp_admI]

lemma stream_antiP2I:
"!!X. [|stream_antiP (F::(('a::flat stream)set => ('a stream set)))|]
  ==> !i x y. x << y --> y:down_iterate F i --> x:down_iterate F i"
apply (unfold stream_antiP_def)
apply (rule allI)
apply (induct_tac "i")
apply ( simp)
apply (simp)
apply (intro strip)
apply (erule allE, erule all_dupE, erule exE, erule exE)
apply (erule conjE)
apply (case_tac "#x < Fin i")
apply ( fast)
apply (fold ile_def)
apply (drule (1) mp)
apply (erule all_dupE, drule mp, rule refl_less)
apply (erule ssubst)
apply (erule allE, drule (1) mp)
apply (drule_tac P="%x. x" in subst, assumption)
apply (erule conjE, rule conjI)
apply ( erule slen_take_lemma3 [THEN ssubst], assumption)
apply ( assumption)
apply (erule allE, erule allE, drule mp, erule monofun_rt_mult)
apply (drule (1) mp)
apply (assumption)
done

lemma stream_antiP2_non_gfp_admI:
"!!X. [|!i x y. x << y --> y:down_iterate F i --> x:down_iterate F i; down_cont F |] 
  ==> adm (%u. ~ u:gfp F)"
apply (unfold adm_def)
apply (simp add: INTER_down_iterate_is_gfp)
apply (fast dest!: is_ub_thelub)
done

lemmas fstream_non_gfp_admI = stream_antiP2I [THEN stream_antiP2_non_gfp_admI]



(**new approach for adm********************************************************)

section "antitonP"

lemma antitonPD: "[| antitonP P; y:P; x<<y |] ==> x:P"
apply (unfold antitonP_def)
apply auto
done

lemma antitonPI: "!x y. y:P --> x<<y --> x:P ==> antitonP P"
apply (unfold antitonP_def)
apply (fast)
done

lemma antitonP_adm_non_P: "antitonP P ==> adm (%u. u~:P)"
apply (unfold adm_def)
apply (auto dest: antitonPD elim: is_ub_thelub)
done

lemma def_gfp_adm_nonP: "P \<equiv> gfp F \<Longrightarrow> {y. \<exists>x::'a::pcpo. y \<sqsubseteq> x \<and> x \<in> P} \<subseteq> F {y. \<exists>x. y \<sqsubseteq> x \<and> x \<in> P} \<Longrightarrow> 
  adm (\<lambda>u. u\<notin>P)"
apply (simp)
apply (rule antitonP_adm_non_P)
apply (rule antitonPI)
apply (drule gfp_upperbound)
apply (fast)
done

lemma adm_set:
"{lub (range Y) |Y. chain Y & (\<forall>i. Y i \<in> P)} \<subseteq> P \<Longrightarrow> adm (\<lambda>x. x\<in>P)"
apply (unfold adm_def)
apply (fast)
done

lemma def_gfp_admI: "P \<equiv> gfp F \<Longrightarrow> {lub (range Y) |Y. chain Y \<and> (\<forall>i. Y i \<in> P)} \<subseteq> 
  F {lub (range Y) |Y. chain Y \<and> (\<forall>i. Y i \<in> P)} \<Longrightarrow> adm (\<lambda>x. x\<in>P)"
apply (simp)
apply (rule adm_set)
apply (erule gfp_upperbound)
done

end
