(*  Title: 	HOLCF/FOCUS/Fstreams.thy
    ID:         $Id$
    Author: 	Borislav Gajanovic

FOCUS flat streams (with lifted elements)
###TODO: integrate this with Fstream.*
*)

theory Fstreams = Stream:

defaultsort type

types 'a fstream = "('a lift) stream"

consts

  fsingleton    :: "'a => 'a fstream"  ("<_>" [1000] 999)
  fsfilter      :: "'a set \<Rightarrow> 'a fstream \<rightarrow> 'a fstream"
  fsmap		:: "('a => 'b) => 'a fstream -> 'b fstream"

  jth           :: "nat => 'a fstream => 'a"

  first         :: "'a fstream => 'a"
  last          :: "'a fstream => 'a"


syntax

  "@emptystream":: "'a fstream" 			("<>")
  "@fsfilter"	:: "'a set \<Rightarrow> 'a fstream \<Rightarrow> 'a fstream"	("(_'(C')_)" [64,63] 63)

syntax (xsymbols)

  "@fsfilter"	:: "'a set \<Rightarrow> 'a fstream \<Rightarrow> 'a fstream" ("(_\<copyright>_)"
								     [64,63] 63)
translations

  "<>"    => "\<bottom>"
  "A(C)s" == "fsfilter A\<cdot>s"

defs

  fsingleton_def2:    "fsingleton  == %a. Def a && UU"

  jth_def:            "jth == %n s. if Fin n < #s then THE a. i_th n s = Def a else arbitrary" 

  first_def:          "first == %s. jth 0 s"
  last_def:           "last == %s. case #s of Fin n => (if n~=0 then jth (THE k. Suc k = n) s else arbitrary)
                              | Infty => arbitrary"

  fsfilter_def:       "fsfilter A \<equiv> sfilter\<cdot>(flift2 (\<lambda>x. x\<in>A))"
  fsmap_def:   	      "fsmap f  == smap$(flift2 f)"


lemma ft_fsingleton[simp]: "ft$(<a>) = Def a"
by (simp add: fsingleton_def2)

lemma slen_fsingleton[simp]: "#(<a>) = Fin 1"
by (simp add: fsingleton_def2 inat_defs)

lemma slen_fstreams[simp]: "#(<a> ooo s) = iSuc (#s)"
by (simp add: fsingleton_def2)

lemma slen_fstreams2[simp]: "#(s ooo <a>) = iSuc (#s)"
apply (case_tac "#s", auto)
apply (insert slen_sconc [of _ s "Suc 0" "<a>"], auto)
by (simp add: sconc_def)

lemma j_th_0_fsingleton[simp]:"jth 0 (<a>) = a"
apply (simp add: fsingleton_def2 jth_def)
by (simp add: i_th_def Fin_0)

lemma jth_0[simp]: "jth 0 (<a> ooo s) = a"  
apply (simp add: fsingleton_def2 jth_def)
by (simp add: i_th_def Fin_0)

lemma first_sconc[simp]: "first (<a> ooo s) = a"
by (simp add: first_def)

lemma first_fsingleton[simp]: "first (<a>) = a"
by (simp add: first_def)

lemma jth_n[simp]: "Fin n = #s ==> jth n (s ooo <a>) = a"
apply (simp add: jth_def, auto)
apply (simp add: i_th_def rt_sconc1)
by (simp add: inat_defs split: inat_splits)

lemma last_sconc[simp]: "Fin n = #s ==> last (s ooo <a>) = a"
apply (simp add: last_def)
apply (simp add: inat_defs split:inat_splits)
by (drule sym, auto)

lemma last_fsingleton[simp]: "last (<a>) = a"
by (simp add: last_def)

lemma first_UU[simp]: "first UU = arbitrary"
by (simp add: first_def jth_def)

lemma last_UU[simp]:"last UU = arbitrary"
by (simp add: last_def jth_def inat_defs)

lemma last_infinite[simp]:"#s = Infty ==> last s = arbitrary"
by (simp add: last_def)

lemma jth_slen_lemma1:"n <= k & Fin n = #s ==> jth k s = arbitrary"
by (simp add: jth_def inat_defs split:inat_splits, auto)

lemma jth_UU[simp]:"jth n UU = arbitrary" 
by (simp add: jth_def)

lemma ext_last:"[|s ~= UU; Fin (Suc n) = #s|] ==> (stream_take n$s) ooo <(last s)> = s" 
apply (simp add: last_def)
apply (case_tac "#s", auto)
apply (simp add: fsingleton_def2)
apply (subgoal_tac "Def (jth n s) = i_th n s")
apply (auto simp add: i_th_last)
apply (drule slen_take_lemma1, auto)
apply (simp add: jth_def)
apply (case_tac "i_th n s = UU")
apply auto
apply (simp add: i_th_def)
apply (case_tac "i_rt n s = UU", auto)
apply (drule i_rt_slen [THEN iffD1])
apply (drule slen_take_eq_rev [rule_format, THEN iffD2],auto)
by (drule not_Undef_is_Def [THEN iffD1], auto)


lemma fsingleton_lemma1[simp]: "(<a> = <b>) = (a=b)"
by (simp add: fsingleton_def2)

lemma fsingleton_lemma2[simp]: "<a> ~= <>"
by (simp add: fsingleton_def2)

lemma fsingleton_sconc:"<a> ooo s = Def a && s"
by (simp add: fsingleton_def2)

lemma fstreams_ind: 
  "[| adm P; P <>; !!a s. P s ==> P (<a> ooo s) |] ==> P x"
apply (simp add: fsingleton_def2)
apply (rule stream.ind, auto)
by (drule not_Undef_is_Def [THEN iffD1], auto)

lemma fstreams_ind2:
  "[| adm P; P <>; !!a. P (<a>); !!a b s. P s ==> P (<a> ooo <b> ooo s) |] ==> P x"
apply (simp add: fsingleton_def2)
apply (rule stream_ind2, auto)
by (drule not_Undef_is_Def [THEN iffD1], auto)+

lemma fstreams_take_Suc[simp]: "stream_take (Suc n)$(<a> ooo s) = <a> ooo stream_take n$s"
by (simp add: fsingleton_def2)

lemma fstreams_not_empty[simp]: "<a> ooo s ~= <>"
by (simp add: fsingleton_def2)

lemma fstreams_not_empty2[simp]: "s ooo <a> ~= <>"
by (case_tac "s=UU", auto)

lemma fstreams_exhaust: "x = UU | (EX a s. x = <a> ooo s)"
apply (simp add: fsingleton_def2, auto)
apply (erule contrapos_pp, auto)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
by (drule not_Undef_is_Def [THEN iffD1], auto)

lemma fstreams_cases: "[| x = UU ==> P; !!a y. x = <a> ooo y ==> P |] ==> P"
by (insert fstreams_exhaust [of x], auto)

lemma fstreams_exhaust_eq: "(x ~= UU) = (? a y. x = <a> ooo y)"
apply (simp add: fsingleton_def2, auto)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
by (drule not_Undef_is_Def [THEN iffD1], auto)

lemma fstreams_inject: "(<a> ooo s = <b> ooo t) = (a=b & s=t)"
by (simp add: fsingleton_def2)

lemma fstreams_prefix: "<a> ooo s << t ==> EX tt. t = <a> ooo tt &  s << tt"
apply (simp add: fsingleton_def2)
apply (insert stream_prefix [of "Def a" s t], auto)
by (drule stream.inverts, auto)

lemma fstreams_prefix': "x << <a> ooo z = (x = <> |  (EX y. x = <a> ooo y &  y << z))"
apply (auto, case_tac "x=UU", auto)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
apply (simp add: fsingleton_def2, auto)
apply (drule stream.inverts, auto)
apply (drule ax_flat [rule_format], simp)
apply (drule stream.inverts, auto)
by (erule sconc_mono)

lemma ft_fstreams[simp]: "ft$(<a> ooo s) = Def a"
by (simp add: fsingleton_def2)

lemma rt_fstreams[simp]: "rt$(<a> ooo s) = s"
by (simp add: fsingleton_def2)

lemma ft_eq[simp]: "(ft$s = Def a) = (EX t. s = <a> ooo t)"
apply (rule stream.casedist [of s],auto)
by (drule sym, auto simp add: fsingleton_def2)

lemma surjective_fstreams: "(<d> ooo y = x) = (ft$x = Def d & rt$x = y)"
by auto

lemma fstreams_mono: "<a> ooo b << <a> ooo c ==> b << c"
apply (simp add: fsingleton_def2)
by (drule stream.inverts, auto)

lemma fsmap_UU[simp]: "fsmap f$UU = UU"
by (simp add: fsmap_def)

lemma fsmap_fsingleton_sconc: "fsmap f$(<x> ooo xs) = <(f x)> ooo (fsmap f$xs)"
by (simp add: fsmap_def fsingleton_def2 flift2_def)

lemma fsmap_fsingleton[simp]: "fsmap f$(<x>) = <(f x)>"
by (simp add: fsmap_def fsingleton_def2 flift2_def)


declare range_composition[simp del]


lemma fstreams_chain_lemma[rule_format]:
  "ALL s x y. stream_take n$(s::'a fstream) << x & x << y & y << s & x ~= y --> stream_take (Suc n)$s << y"
apply (induct_tac n, auto)
apply (case_tac "s=UU", auto)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
apply (case_tac "y=UU", auto)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
apply (drule stream.inverts, auto)
apply (simp add: less_lift_def, auto)
apply (rule monofun_cfun, auto)
apply (case_tac "s=UU", auto)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
apply (erule_tac x="ya" in allE)
apply (drule stream_prefix, auto)
apply (case_tac "y=UU",auto)
apply (drule stream_exhaust_eq [THEN iffD1], clarsimp)
apply (drule stream.inverts, auto)
apply (simp add: less_lift_def)
apply (drule stream.inverts, auto)+
apply (erule_tac x="tt" in allE)
apply (erule_tac x="yb" in allE, auto)
apply (simp add: less_lift_def)
by (rule monofun_cfun, auto)

lemma fstreams_lub_lemma1: "[| chain Y; lub (range Y) = <a> ooo s |] ==> EX j t. Y j = <a> ooo t"
apply (subgoal_tac "lub(range Y) ~= UU")
apply (drule chain_UU_I_inverse2, auto)
apply (drule_tac x="i" in is_ub_thelub, auto)
by (drule fstreams_prefix' [THEN iffD1], auto)

lemma fstreams_lub1: 
 "[| chain Y; lub (range Y) = <a> ooo s |]
     ==> (EX j t. Y j = <a> ooo t) & (EX X. chain X & (ALL i. EX j. <a> ooo X i << Y j) & lub (range X) = s)"
apply (auto simp add: fstreams_lub_lemma1)
apply (rule_tac x="%n. stream_take n$s" in exI, auto)
apply (simp add: chain_stream_take)
apply (induct_tac i, auto)
apply (drule fstreams_lub_lemma1, auto)
apply (rule_tac x="j" in exI, auto)
apply (case_tac "max_in_chain j Y")
apply (frule lub_finch1 [THEN thelubI], auto)
apply (rule_tac x="j" in exI)
apply (erule subst) back back
apply (simp add: less_cprod_def sconc_mono)
apply (simp add: max_in_chain_def, auto)
apply (rule_tac x="ja" in exI)
apply (subgoal_tac "Y j << Y ja")
apply (drule fstreams_prefix, auto)+
apply (rule sconc_mono)
apply (rule fstreams_chain_lemma, auto)
apply (subgoal_tac "Y ja << (LUB i. (Y i))", clarsimp)
apply (drule fstreams_mono, simp)
apply (rule is_ub_thelub, simp)
apply (blast intro: chain_mono3)
by (rule stream_reach2)


lemma lub_Pair_not_UU_lemma: 
  "[| chain Y; lub (range Y) = ((a::'a::flat), b); a ~= UU; b ~= UU |] 
      ==> EX j c d. Y j = (c, d) & c ~= UU & d ~= UU"
apply (frule thelub_cprod, clarsimp)
apply (drule chain_UU_I_inverse2, clarsimp)
apply (case_tac "Y i", clarsimp)
apply (case_tac "max_in_chain i Y")
apply (drule maxinch_is_thelub, auto)
apply (rule_tac x="i" in exI, auto)
apply (simp add: max_in_chain_def, auto)
apply (subgoal_tac "Y i << Y j",auto)
apply (simp add: less_cprod_def, clarsimp)
apply (drule ax_flat [rule_format], auto)
apply (case_tac "snd (Y j) = UU",auto)
apply (case_tac "Y j", auto)
apply (rule_tac x="j" in exI)
apply (case_tac "Y j",auto)
by (drule chain_mono3, auto)

lemma fstreams_lub_lemma2: 
  "[| chain Y; lub (range Y) = (a, <m> ooo ms); (a::'a::flat) ~= UU |] ==> EX j t. Y j = (a, <m> ooo t)"
apply (frule lub_Pair_not_UU_lemma, auto)
apply (drule_tac x="j" in is_ub_thelub, auto)
apply (simp add: less_cprod_def, clarsimp)
apply (drule ax_flat [rule_format], clarsimp)
by (drule fstreams_prefix' [THEN iffD1], auto)

lemma fstreams_lub2:
  "[| chain Y; lub (range Y) = (a, <m> ooo ms); (a::'a::flat) ~= UU |] 
      ==> (EX j t. Y j = (a, <m> ooo t)) & (EX X. chain X & (ALL i. EX j. (a, <m> ooo X i) << Y j) & lub (range X) = ms)"
apply (auto simp add: fstreams_lub_lemma2)
apply (rule_tac x="%n. stream_take n$ms" in exI, auto)
apply (simp add: chain_stream_take)
apply (induct_tac i, auto)
apply (drule fstreams_lub_lemma2, auto)
apply (rule_tac x="j" in exI, auto)
apply (simp add: less_cprod_def)
apply (case_tac "max_in_chain j Y")
apply (frule lub_finch1 [THEN thelubI], auto)
apply (rule_tac x="j" in exI)
apply (erule subst) back back
apply (simp add: less_cprod_def sconc_mono)
apply (simp add: max_in_chain_def, auto)
apply (rule_tac x="ja" in exI)
apply (subgoal_tac "Y j << Y ja")
apply (simp add: less_cprod_def, auto)
apply (drule trans_less)
apply (simp add: ax_flat, auto)
apply (drule fstreams_prefix, auto)+
apply (rule sconc_mono)
apply (subgoal_tac "tt ~= tta" "tta << ms")
apply (blast intro: fstreams_chain_lemma)
apply (frule lub_cprod [THEN thelubI], auto)
apply (subgoal_tac "snd (Y ja) << (LUB i. snd (Y i))", clarsimp)
apply (drule fstreams_mono, simp)
apply (rule is_ub_thelub chainI)
apply (simp add: chain_def less_cprod_def)
apply (subgoal_tac "fst (Y j) ~= fst (Y ja) | snd (Y j) ~= snd (Y ja)", simp)
apply (drule ax_flat[rule_format], simp)+
apply (drule prod_eqI, auto)
apply (simp add: chain_mono3)
by (rule stream_reach2)


lemma cpo_cont_lemma:
  "[| monofun (f::'a::cpo => 'b::cpo); (!Y. chain Y --> f (lub(range Y)) << (LUB i. f (Y i))) |] ==> cont f"
apply (rule monocontlub2cont, auto)
apply (simp add: contlub_def, auto)
apply (erule_tac x="Y" in allE, auto)
apply (simp add: po_eq_conv)
apply (frule cpo,auto)
apply (frule is_lubD1)
apply (frule ub2ub_monofun, auto)
apply (drule thelubI, auto)
apply (rule is_lub_thelub, auto)
by (erule ch2ch_monofun, simp)

end




