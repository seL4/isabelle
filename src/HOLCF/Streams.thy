(*  Title: 	HOLCF/Streams.thy
    ID:         $Id$
    Author: 	Borislav Gajanovic and David von Oheimb

Stream domains with concatenation.
TODO: HOLCF/ex/Stream.* should be integrated into this file.
*)

theory Streams = Stream :

(* ----------------------------------------------------------------------- *)

lemma stream_neq_UU: "x~=UU ==> EX a as. x=a&&as & a~=UU"
by (simp add: stream_exhaust_eq,auto)

lemma stream_prefix1: "[| x<<y; xs<<ys |] ==> x&&xs << y&&ys"
by (insert stream_prefix' [of y "x&&xs" ys],force)

lemma stream_take_le_mono : "k<=n ==> stream_take k$s1 << stream_take n$s1"
apply (insert chain_stream_take [of s1])
by (drule chain_mono3,auto)

lemma mono_stream_take: "s1 << s2 ==> stream_take n$s1 << stream_take n$s2"
by (simp add: monofun_cfun_arg)

lemma stream_take_prefix [simp]: "stream_take n$s << s"
apply (subgoal_tac "s=(LUB n. stream_take n$s)")
 apply (erule ssubst, rule is_ub_thelub)
 apply (simp only: chain_stream_take)
by (simp only: stream_reach2)

lemma stream_take_take_less:"stream_take k$(stream_take n$s) << stream_take k$s"
by (rule monofun_cfun_arg,auto)

(* ----------------------------------------------------------------------- *)

lemma slen_rt_mono: "#s2 <= #s1 ==> #(rt$s2) <= #(rt$s1)"
apply (rule stream.casedist [of s1])
 apply (rule stream.casedist [of s2],simp+)
by (rule stream.casedist [of s2],auto)

lemma slen_take_lemma4 [rule_format]: 
  "!s. stream_take n$s ~= s --> #(stream_take n$s) = Fin n"
apply (induct_tac n,auto simp add: Fin_0)
apply (case_tac "s=UU",simp)
by (drule stream_neq_UU,auto)

lemma slen_take_lemma5: "#(stream_take n$s) <= Fin n"; 
apply (case_tac "stream_take n$s = s")
 apply (simp add: slen_take_eq_rev)
by (simp add: slen_take_lemma4)

lemma stream_take_idempotent [simp]: 
 "stream_take n$(stream_take n$s) = stream_take n$s"
apply (case_tac "stream_take n$s = s")
apply (auto,insert slen_take_lemma4 [of n s]);
by (auto,insert slen_take_lemma1 [of "stream_take n$s" n],simp)

lemma stream_take_take_Suc [simp]: "stream_take n$(stream_take (Suc n)$s) = 
                                    stream_take n$s"
apply (simp add: po_eq_conv,auto)
 apply (simp add: stream_take_take_less)
apply (subgoal_tac "stream_take n$s = stream_take n$(stream_take n$s)")
 apply (erule ssubst)
 apply (rule_tac monofun_cfun_arg)
 apply (insert chain_stream_take [of s])
by (simp add: chain_def,simp)

lemma mono_stream_take_pred: 
  "stream_take (Suc n)$s1 << stream_take (Suc n)$s2 ==>
                       stream_take n$s1 << stream_take n$s2"
by (drule mono_stream_take [of _ _ n],simp)

lemma stream_take_lemma10 [rule_format]:
  "ALL k<=n. stream_take n$s1 << stream_take n$s2 
                             --> stream_take k$s1 << stream_take k$s2"
apply (induct_tac n,simp,clarsimp)
apply (case_tac "k=Suc n",blast)
apply (erule_tac x="k" in allE)
by (drule mono_stream_take_pred,simp)

lemma stream_take_finite [simp]: "stream_finite (stream_take n$s)"
apply (simp add: stream.finite_def)
by (rule_tac x="n" in exI,simp)

lemma slen_stream_take_finite [simp]: "#(stream_take n$s) ~= \<infinity>"
by (simp add: slen_def)

lemma stream_take_Suc_neq: "stream_take (Suc n)$s ~=s ==> 
                     stream_take n$s ~= stream_take (Suc n)$s"
apply auto
apply (subgoal_tac "stream_take n$s ~=s")
 apply (insert slen_take_lemma4 [of n s],auto)
apply (rule stream.casedist [of s],simp)
apply (simp add: inat_defs split:inat_splits)
by (simp add: slen_take_lemma4)


(* ----------------------------------------------------------------------- *)

consts
 
  i_rt :: "nat => 'a stream => 'a stream" (* chops the first i elements *)
  i_th :: "nat => 'a stream => 'a"        (* the i-th element *)

  sconc         :: "'a stream => 'a stream => 'a stream" (infixr "ooo" 65) 
  constr_sconc  :: "'a stream => 'a stream => 'a stream" (* constructive *)
  constr_sconc' :: "nat => 'a stream => 'a stream => 'a stream" 

defs
  i_rt_def: "i_rt == %i s. iterate i rt s"  
  i_th_def: "i_th == %i s. ft$(i_rt i s)" 

  sconc_def: "s1 ooo s2 == case #s1 of 
                       Fin n => (SOME s. (stream_take n$s=s1) & (i_rt n s = s2))
                     | \<infinity>     => s1" 

  constr_sconc_def: "constr_sconc s1 s2 == case #s1 of 
                                             Fin n => constr_sconc' n s1 s2 
                                           | \<infinity>    => s1"
primrec 
  constr_sconc'_0:   "constr_sconc' 0 s1 s2 = s2"
  constr_sconc'_Suc: "constr_sconc' (Suc n) s1 s2 = ft$s1 && 
                                                    constr_sconc' n (rt$s1) s2"


(* ----------------------------------------------------------------------- *)
   section "i_rt"
(* ----------------------------------------------------------------------- *)

lemma i_rt_UU [simp]: "i_rt n UU = UU"
apply (simp add: i_rt_def)
by (rule iterate.induct,auto)

lemma i_rt_0 [simp]: "i_rt 0 s = s"
by (simp add: i_rt_def)

lemma i_rt_Suc [simp]: "a ~= UU ==> i_rt (Suc n) (a&&s) = i_rt n s"
by (simp add: i_rt_def iterate_Suc2 del: iterate_Suc)

lemma i_rt_Suc_forw: "i_rt (Suc n) s = i_rt n (rt$s)"
by (simp only: i_rt_def iterate_Suc2)

lemma i_rt_Suc_back:"i_rt (Suc n) s = rt$(i_rt n s)"
by (simp only: i_rt_def,auto)

lemma i_rt_mono: "x << s ==> i_rt n x  << i_rt n s"
by (simp add: i_rt_def monofun_rt_mult)

lemma i_rt_ij_lemma: "Fin (i + j) <= #x ==> Fin j <= #(i_rt i x)"
by (simp add: i_rt_def slen_rt_mult)

lemma slen_i_rt_mono: "#s2 <= #s1 ==> #(i_rt n s2) <= #(i_rt n s1)"
apply (induct_tac n,auto)
apply (simp add: i_rt_Suc_back)
by (drule slen_rt_mono,simp)

lemma i_rt_take_lemma1 [rule_format]: "ALL s. i_rt n (stream_take n$s) = UU"
apply (induct_tac n); 
 apply (simp add: i_rt_Suc_back,auto)
apply (case_tac "s=UU",auto)
by (drule stream_neq_UU,simp add: i_rt_Suc_forw,auto)

lemma i_rt_slen: "(i_rt n s = UU) = (stream_take n$s = s)"
apply auto
 apply (insert i_rt_ij_lemma [of n "Suc 0" s]);
 apply (subgoal_tac "#(i_rt n s)=0")
  apply (case_tac "stream_take n$s = s",simp+)
  apply (insert slen_take_eq [of n s],simp)
  apply (simp add: inat_defs split:inat_splits)
 apply (simp add: slen_take_eq )
by (simp, insert i_rt_take_lemma1 [of n s],simp)

lemma i_rt_lemma_slen: "#s=Fin n ==> i_rt n s = UU"
by (simp add: i_rt_slen slen_take_lemma1)

lemma stream_finite_i_rt [simp]: "stream_finite (i_rt n s) = stream_finite s"
apply (induct_tac n, auto)
 apply (rule stream.casedist [of "s"], auto simp del: i_rt_Suc)
by (simp add: i_rt_Suc_back stream_finite_rt_eq)+

lemma take_i_rt_len_lemma: "ALL sl x j t. Fin sl = #x & n <= sl &
                            #(stream_take n$x) = Fin t & #(i_rt n x)= Fin j 
                                              --> Fin (j + t) = #x"
apply (induct_tac n,auto)
 apply (simp add: inat_defs)
apply (case_tac "x=UU",auto)
 apply (simp add: inat_defs)
apply (drule stream_neq_UU,auto)
apply (subgoal_tac "EX k. Fin k = #as",clarify)
 apply (erule_tac x="k" in allE)
 apply (erule_tac x="as" in allE,auto)
 apply (erule_tac x="THE p. Suc p = t" in allE,auto)
   apply (simp add: inat_defs split:inat_splits)
  apply (simp add: inat_defs split:inat_splits)
  apply (simp only: the_equality)
 apply (simp add: inat_defs split:inat_splits)
 apply force
by (simp add: inat_defs split:inat_splits)

lemma take_i_rt_len: 
"[| Fin sl = #x; n <= sl; #(stream_take n$x) = Fin t; #(i_rt n x) = Fin j |] ==>
    Fin (j + t) = #x"
by (blast intro: take_i_rt_len_lemma [rule_format])


(* ----------------------------------------------------------------------- *)
   section "i_th"
(* ----------------------------------------------------------------------- *)

lemma i_th_i_rt_step:
"[| i_th n s1 << i_th n s2; i_rt (Suc n) s1 << i_rt (Suc n) s2 |] ==> 
   i_rt n s1 << i_rt n s2"
apply (simp add: i_th_def i_rt_Suc_back)
apply (rule stream.casedist [of "i_rt n s1"],simp)
apply (rule stream.casedist [of "i_rt n s2"],auto)
by (drule stream_prefix1,auto)

lemma i_th_stream_take_Suc [rule_format]: 
 "ALL s. i_th n (stream_take (Suc n)$s) = i_th n s"
apply (induct_tac n,auto)
 apply (simp add: i_th_def)
 apply (case_tac "s=UU",auto)
 apply (drule stream_neq_UU,auto)
apply (case_tac "s=UU",simp add: i_th_def)
apply (drule stream_neq_UU,auto)
by (simp add: i_th_def i_rt_Suc_forw)

lemma last_lemma10: "stream_take (Suc n)$s1 << stream_take (Suc n)$s2 ==> 
                     i_th n s1 << i_th n s2"
apply (rule i_th_stream_take_Suc [THEN subst])
apply (rule i_th_stream_take_Suc [THEN subst]) back
apply (simp add: i_th_def)
apply (rule monofun_cfun_arg)
by (erule i_rt_mono)

lemma i_th_last: "i_th n s && UU = i_rt n (stream_take (Suc n)$s)"
apply (insert surjectiv_scons [of "i_rt n (stream_take (Suc n)$s)"])
apply (rule i_th_stream_take_Suc [THEN subst])
apply (simp add: i_th_def  i_rt_Suc_back [symmetric])
by (simp add: i_rt_take_lemma1)

lemma i_th_last_eq: 
"i_th n s1 = i_th n s2 ==> i_rt n (stream_take (Suc n)$s1) = i_rt n (stream_take (Suc n)$s2)"
apply (insert i_th_last [of n s1])
apply (insert i_th_last [of n s2])
by auto

lemma i_th_prefix_lemma:
"[| k <= n; stream_take (Suc n)$s1 << stream_take (Suc n)$s2 |] ==> 
    i_th k s1 << i_th k s2"
apply (subgoal_tac "stream_take (Suc k)$s1 << stream_take (Suc k)$s2")
 apply (simp add: last_lemma10)
by (blast intro: stream_take_lemma10)

lemma take_i_rt_prefix_lemma1: 
  "stream_take (Suc n)$s1 << stream_take (Suc n)$s2 ==>
   i_rt (Suc n) s1 << i_rt (Suc n) s2 ==> 
   i_rt n s1 << i_rt n s2 & stream_take n$s1 << stream_take n$s2"
apply auto
 apply (insert i_th_prefix_lemma [of n n s1 s2])
 apply (rule i_th_i_rt_step,auto)
by (drule mono_stream_take_pred,simp)

lemma take_i_rt_prefix_lemma: 
"[| stream_take n$s1 << stream_take n$s2; i_rt n s1 << i_rt n s2 |] ==> s1 << s2"
apply (case_tac "n=0",simp)
apply (insert neq0_conv [of n])
apply (insert not0_implies_Suc [of n],auto)
apply (subgoal_tac "stream_take 0$s1 << stream_take 0$s2 & 
                    i_rt 0 s1 << i_rt 0 s2")
 defer 1
 apply (rule zero_induct,blast)
 apply (blast dest: take_i_rt_prefix_lemma1)
by simp

lemma streams_prefix_lemma: "(s1 << s2) = 
  (stream_take n$s1 << stream_take n$s2 & i_rt n s1 << i_rt n s2)"; 
apply auto
  apply (simp add: monofun_cfun_arg)
 apply (simp add: i_rt_mono)
by (erule take_i_rt_prefix_lemma,simp)

lemma streams_prefix_lemma1:
 "[| stream_take n$s1 = stream_take n$s2; i_rt n s1 = i_rt n s2 |] ==> s1 = s2"
apply (simp add: po_eq_conv,auto)
 apply (insert streams_prefix_lemma)
 by blast+


(* ----------------------------------------------------------------------- *)
   section "sconc"
(* ----------------------------------------------------------------------- *)

lemma UU_sconc [simp]: " UU ooo s = s "
by (simp add: sconc_def inat_defs)

lemma scons_neq_UU: "a~=UU ==> a && s ~=UU"
by auto

lemma singleton_sconc [rule_format, simp]: "x~=UU --> (x && UU) ooo y = x && y"
apply (simp add: sconc_def inat_defs split:inat_splits,auto)
apply (rule someI2_ex,auto)
 apply (rule_tac x="x && y" in exI,auto)
apply (simp add: i_rt_Suc_forw)
apply (case_tac "xa=UU",simp)
by (drule stream_neq_UU,auto)

lemma ex_sconc [rule_format]: 
  "ALL k y. #x = Fin k --> (EX w. stream_take k$w = x & i_rt k w = y)"
apply (case_tac "#x")
 apply (rule stream_finite_ind [of x],auto)
  apply (simp add: stream.finite_def)
  apply (drule slen_take_lemma1,blast)
 apply (simp add: inat_defs split:inat_splits)+
apply (erule_tac x="y" in allE,auto)
by (rule_tac x="a && w" in exI,auto)

lemma rt_sconc1: "Fin n = #x ==> i_rt n (x ooo y) = y"; 
apply (simp add: sconc_def inat_defs split:inat_splits , arith?,auto)
apply (rule someI2_ex,auto)
by (drule ex_sconc,simp)

lemma sconc_inj2: "\<lbrakk>Fin n = #x; x ooo y = x ooo z\<rbrakk> \<Longrightarrow> y = z"
apply (frule_tac y=y in rt_sconc1)
by (auto elim: rt_sconc1)

lemma sconc_UU [simp]:"s ooo UU = s"
apply (case_tac "#s")
 apply (simp add: sconc_def inat_defs)
 apply (rule someI2_ex)
  apply (rule_tac x="s" in exI)
  apply auto
   apply (drule slen_take_lemma1,auto)
  apply (simp add: i_rt_lemma_slen)
 apply (drule slen_take_lemma1,auto)
 apply (simp add: i_rt_slen)
by (simp add: sconc_def inat_defs)

lemma stream_take_sconc [simp]: "Fin n = #x ==> stream_take n$(x ooo y) = x"
apply (simp add: sconc_def)
apply (simp add: inat_defs split:inat_splits,auto)
apply (rule someI2_ex,auto)
by (drule ex_sconc,simp)

lemma scons_sconc [rule_format,simp]: "a~=UU --> (a && x) ooo y = a && x ooo y"
apply (case_tac "#x",auto)
 apply (simp add: sconc_def) 
 apply (rule someI2_ex)
  apply (drule ex_sconc,simp)
 apply (rule someI2_ex,auto)
  apply (simp add: i_rt_Suc_forw)
  apply (rule_tac x="a && x" in exI,auto)
 apply (case_tac "xa=UU",auto)
  apply (drule_tac s="stream_take nat$x" in scons_neq_UU)
  apply (simp add: i_rt_Suc_forw)
 apply (drule stream_neq_UU,clarsimp)
 apply (drule streams_prefix_lemma1,simp+)
by (simp add: sconc_def)

lemma ft_sconc: "x ~= UU ==> ft$(x ooo y) = ft$x"
by (rule stream.casedist [of x],auto)

lemma sconc_assoc: "(x ooo y) ooo z = x ooo y ooo z"
apply (case_tac "#x")
 apply (rule stream_finite_ind [of x],auto simp del: scons_sconc)
  apply (simp add: stream.finite_def del: scons_sconc)
  apply (drule slen_take_lemma1,auto simp del: scons_sconc)
 apply (case_tac "a = UU", auto)
by (simp add: sconc_def)


(* ----------------------------------------------------------------------- *)

lemma sconc_mono: "y << y' ==> x ooo y << x ooo y'"
apply (case_tac "#x")
 apply (rule stream_finite_ind [of "x"])
   apply (auto simp add: stream.finite_def)
  apply (drule slen_take_lemma1,blast)
 by (simp add: stream_prefix',auto simp add: sconc_def)

lemma sconc_mono1 [simp]: "x << x ooo y"
by (rule sconc_mono [of UU, simplified])

(* ----------------------------------------------------------------------- *)

lemma empty_sconc [simp]: "(x ooo y = UU) = (x = UU & y = UU)"
apply (case_tac "#x",auto)
   by (insert sconc_mono1 [of x y],auto);

(* ----------------------------------------------------------------------- *)

lemma rt_sconc [rule_format, simp]: "s~=UU --> rt$(s ooo x) = rt$s ooo x"
by (rule stream.casedist,auto)

(* ----------------------------------------------------------------------- *)

lemma sconc_lemma [rule_format, simp]: "ALL s. stream_take n$s ooo i_rt n s = s"
apply (induct_tac n,auto)
apply (case_tac "s=UU",auto)
by (drule stream_neq_UU,auto)

(* ----------------------------------------------------------------------- *)
   subsection "pointwise equality"
(* ----------------------------------------------------------------------- *)

lemma ex_last_stream_take_scons: "stream_take (Suc n)$s = 
                     stream_take n$s ooo i_rt n (stream_take (Suc n)$s)"
by (insert sconc_lemma [of n "stream_take (Suc n)$s"],simp)

lemma i_th_stream_take_eq: 
"!!n. ALL n. i_th n s1 = i_th n s2 ==> stream_take n$s1 = stream_take n$s2"
apply (induct_tac n,auto)
apply (subgoal_tac "stream_take (Suc na)$s1 =
                    stream_take na$s1 ooo i_rt na (stream_take (Suc na)$s1)")
 apply (subgoal_tac "i_rt na (stream_take (Suc na)$s1) = 
                    i_rt na (stream_take (Suc na)$s2)")
  apply (subgoal_tac "stream_take (Suc na)$s2 = 
                    stream_take na$s2 ooo i_rt na (stream_take (Suc na)$s2)")
   apply (insert ex_last_stream_take_scons,simp)
  apply blast
 apply (erule_tac x="na" in allE)
 apply (insert i_th_last_eq [of _ s1 s2])
by blast+

lemma pointwise_eq_lemma[rule_format]: "ALL n. i_th n s1 = i_th n s2 ==> s1 = s2"
by (insert i_th_stream_take_eq [THEN stream.take_lemmas],blast)

(* ----------------------------------------------------------------------- *)
   subsection "finiteness"
(* ----------------------------------------------------------------------- *)

lemma slen_sconc_finite1:
  "[| #(x ooo y) = Infty; Fin n = #x |] ==> #y = Infty"
apply (case_tac "#y ~= Infty",auto)
apply (simp only: slen_infinite [symmetric])
apply (drule_tac y=y in rt_sconc1)
apply (insert stream_finite_i_rt [of n "x ooo y"])
by (simp add: slen_infinite)

lemma slen_sconc_infinite1: "#x=Infty ==> #(x ooo y) = Infty"
by (simp add: sconc_def)

lemma slen_sconc_infinite2: "#y=Infty ==> #(x ooo y) = Infty"
apply (case_tac "#x")
 apply (simp add: sconc_def)
 apply (rule someI2_ex)
  apply (drule ex_sconc,auto)
 apply (erule contrapos_pp)
 apply (insert stream_finite_i_rt)
 apply (simp add: slen_infinite ,auto)
by (simp add: sconc_def)

lemma sconc_finite: "(#x~=Infty & #y~=Infty) = (#(x ooo y)~=Infty)"
apply auto
  apply (case_tac "#x",auto)
  apply (erule contrapos_pp,simp)
  apply (erule slen_sconc_finite1,simp)
 apply (drule slen_sconc_infinite1 [of _ y],simp)
by (drule slen_sconc_infinite2 [of _ x],simp)

(* ----------------------------------------------------------------------- *)

lemma slen_sconc_mono3: "[| Fin n = #x; Fin k = #(x ooo y) |] ==> n <= k"
apply (insert slen_mono [of "x" "x ooo y"])
by (simp add: inat_defs split: inat_splits)

(* ----------------------------------------------------------------------- *)
   subsection "finite slen"
(* ----------------------------------------------------------------------- *)

lemma slen_sconc: "[| Fin n = #x; Fin m = #y |] ==> #(x ooo y) = Fin (n + m)"
apply (case_tac "#(x ooo y)")
 apply (frule_tac y=y in rt_sconc1)
 apply (insert take_i_rt_len [of "THE j. Fin j = #(x ooo y)" "x ooo y" n n m],simp)
 apply (insert slen_sconc_mono3 [of n x _ y],simp)
by (insert sconc_finite [of x y],auto)

(* ----------------------------------------------------------------------- *)
   subsection "flat prefix"
(* ----------------------------------------------------------------------- *)

lemma sconc_prefix: "(s1::'a::flat stream) << s2 ==> EX t. s1 ooo t = s2"
apply (case_tac "#s1")
 apply (subgoal_tac "stream_take nat$s1 = stream_take nat$s2");
  apply (rule_tac x="i_rt nat s2" in exI)
  apply (simp add: sconc_def)
  apply (rule someI2_ex)
   apply (drule ex_sconc)
   apply (simp,clarsimp,drule streams_prefix_lemma1)
   apply (simp+,rule slen_take_lemma3 [rule_format, of _ s1 s2]);
  apply (simp+,rule_tac x="UU" in exI)
apply (insert slen_take_lemma3 [rule_format, of _ s1 s2]);
by (rule stream.take_lemmas,simp)

(* ----------------------------------------------------------------------- *)
   subsection "continuity"
(* ----------------------------------------------------------------------- *)

lemma chain_sconc: "chain S ==> chain (%i. (x ooo S i))"
by (simp add: chain_def,auto simp add: sconc_mono)

lemma chain_scons: "chain S ==> chain (%i. a && S i)"
apply (simp add: chain_def,auto)
by (rule monofun_cfun_arg,simp)

lemma contlub_scons: "contlub (%x. a && x)"
by (simp add: contlub_Rep_CFun2)

lemma contlub_scons_lemma: "chain S ==> (LUB i. a && S i) = a && (LUB i. S i)"
apply (insert contlub_scons [of a])
by (simp only: contlub)

lemma finite_lub_sconc: "chain Y ==> (stream_finite x) ==> 
                        (LUB i. x ooo Y i) = (x ooo (LUB i. Y i))"
apply (rule stream_finite_ind [of x])
 apply (auto)
apply (subgoal_tac "(LUB i. a && (s ooo Y i)) = a && (LUB i. s ooo Y i)")
 by (force,blast dest: contlub_scons_lemma chain_sconc)

lemma contlub_sconc_lemma: 
  "chain Y ==> (LUB i. x ooo Y i) = (x ooo (LUB i. Y i))"
apply (case_tac "#x=Infty")
 apply (simp add: sconc_def)
 prefer 2
 apply (drule finite_lub_sconc,auto simp add: slen_infinite)
apply (simp add: slen_def)
apply (insert lub_const [of x] unique_lub [of _ x _])
by (auto simp add: lub)

lemma contlub_sconc: "contlub (%y. x ooo y)"; 
by (rule contlubI, insert contlub_sconc_lemma [of _ x], simp);

lemma monofun_sconc: "monofun (%y. x ooo y)"
by (simp add: monofun sconc_mono)

lemma cont_sconc: "cont (%y. x ooo y)"
apply (rule  monocontlub2cont)
 apply (rule monofunI, simp add: sconc_mono)
by (rule contlub_sconc);


(* ----------------------------------------------------------------------- *)
   section "constr_sconc"
(* ----------------------------------------------------------------------- *)

lemma constr_sconc_UUs [simp]: "constr_sconc UU s = s"
by (simp add: constr_sconc_def inat_defs)

lemma "x ooo y = constr_sconc x y"
apply (case_tac "#x")
 apply (rule stream_finite_ind [of x],auto simp del: scons_sconc)
  defer 1
  apply (simp add: constr_sconc_def del: scons_sconc)
  apply (case_tac "#s")
   apply (simp add: inat_defs)
   apply (case_tac "a=UU",auto simp del: scons_sconc)
   apply (simp)
  apply (simp add: sconc_def)
 apply (simp add: constr_sconc_def)
apply (simp add: stream.finite_def)
by (drule slen_take_lemma1,auto)

end
