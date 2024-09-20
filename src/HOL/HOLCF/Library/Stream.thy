(*  Title:      HOL/HOLCF/Library/Stream.thy
    Author:     Franz Regensburger, David von Oheimb, Borislav Gajanovic
*)

section \<open>General Stream domain\<close>

theory Stream
imports HOLCF "HOL-Library.Extended_Nat"
begin

default_sort pcpo

domain (unsafe) 'a stream = scons (ft::'a) (lazy rt::"'a stream") (infixr \<open>&&\<close> 65)

definition
  smap :: "('a \<rightarrow> 'b) \<rightarrow> 'a stream \<rightarrow> 'b stream" where
  "smap = fix\<cdot>(\<Lambda> h f s. case s of x && xs \<Rightarrow> f\<cdot>x && h\<cdot>f\<cdot>xs)"

definition
  sfilter :: "('a \<rightarrow> tr) \<rightarrow> 'a stream \<rightarrow> 'a stream" where
  "sfilter = fix\<cdot>(\<Lambda> h p s. case s of x && xs \<Rightarrow>
                                     If p\<cdot>x then x && h\<cdot>p\<cdot>xs else h\<cdot>p\<cdot>xs)"

definition
  slen :: "'a stream \<Rightarrow> enat"  (\<open>#_\<close> [1000] 1000) where
  "#s = (if stream_finite s then enat (LEAST n. stream_take n\<cdot>s = s) else \<infinity>)"


(* concatenation *)

definition
  i_rt :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where (* chops the first i elements *)
  "i_rt = (\<lambda>i s. iterate i\<cdot>rt\<cdot>s)"

definition
  i_th :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a" where (* the i-th element *)
  "i_th = (\<lambda>i s. ft\<cdot>(i_rt i s))"

definition
  sconc :: "'a stream \<Rightarrow> 'a stream \<Rightarrow> 'a stream"  (infixr \<open>ooo\<close> 65) where
  "s1 ooo s2 = (case #s1 of
                  enat n \<Rightarrow> (SOME s. (stream_take n\<cdot>s = s1) \<and> (i_rt n s = s2))
               | \<infinity>     \<Rightarrow> s1)"

primrec constr_sconc' :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a stream \<Rightarrow> 'a stream"
where
  constr_sconc'_0:   "constr_sconc' 0 s1 s2 = s2"
| constr_sconc'_Suc: "constr_sconc' (Suc n) s1 s2 = ft\<cdot>s1 && constr_sconc' n (rt\<cdot>s1) s2"

definition
  constr_sconc  :: "'a stream \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where (* constructive *)
  "constr_sconc s1 s2 = (case #s1 of
                          enat n \<Rightarrow> constr_sconc' n s1 s2
                        | \<infinity>    \<Rightarrow> s1)"


(* ----------------------------------------------------------------------- *)
(* theorems about scons                                                    *)
(* ----------------------------------------------------------------------- *)


section "scons"

lemma scons_eq_UU: "(a && s = UU) = (a = UU)"
by simp

lemma scons_not_empty: "\<lbrakk>a && x = UU; a \<noteq> UU\<rbrakk> \<Longrightarrow> R"
by simp

lemma stream_exhaust_eq: "x \<noteq> UU \<longleftrightarrow> (\<exists>a y. a \<noteq> UU \<and> x = a && y)"
by (cases x, auto)

lemma stream_neq_UU: "x \<noteq> UU \<Longrightarrow> \<exists>a a_s. x = a && a_s \<and> a \<noteq> UU"
by (simp add: stream_exhaust_eq,auto)

lemma stream_prefix:
  "\<lbrakk>a && s \<sqsubseteq> t; a \<noteq> UU\<rbrakk> \<Longrightarrow> \<exists>b tt. t = b && tt \<and> b \<noteq> UU \<and> s \<sqsubseteq> tt"
by (cases t, auto)

lemma stream_prefix':
  "b \<noteq> UU \<Longrightarrow> x \<sqsubseteq> b && z =
   (x = UU \<or> (\<exists>a y. x = a && y \<and> a \<noteq> UU \<and> a \<sqsubseteq> b \<and> y \<sqsubseteq> z))"
by (cases x, auto)


(*
lemma stream_prefix1: "\<lbrakk>x \<sqsubseteq> y; xs \<sqsubseteq> ys\<rbrakk> \<Longrightarrow> x && xs \<sqsubseteq> y && ys"
by (insert stream_prefix' [of y "x && xs" ys],force)
*)

lemma stream_flat_prefix:
  "\<lbrakk>x && xs \<sqsubseteq> y && ys; (x::'a::flat) \<noteq> UU\<rbrakk> \<Longrightarrow> x = y \<and> xs \<sqsubseteq> ys"
apply (case_tac "y = UU",auto)
apply (drule ax_flat,simp)
done




(* ----------------------------------------------------------------------- *)
(* theorems about stream_case                                              *)
(* ----------------------------------------------------------------------- *)

section "stream_case"


lemma stream_case_strictf: "stream_case\<cdot>UU\<cdot>s = UU"
by (cases s, auto)



(* ----------------------------------------------------------------------- *)
(* theorems about ft and rt                                                *)
(* ----------------------------------------------------------------------- *)


section "ft and rt"


lemma ft_defin: "s \<noteq> UU \<Longrightarrow> ft\<cdot>s \<noteq> UU"
by simp

lemma rt_strict_rev: "rt\<cdot>s \<noteq> UU \<Longrightarrow> s \<noteq> UU"
by auto

lemma surjectiv_scons: "(ft\<cdot>s) && (rt\<cdot>s) = s"
by (cases s, auto)

lemma monofun_rt_mult: "x \<sqsubseteq> s \<Longrightarrow> iterate i\<cdot>rt\<cdot>x \<sqsubseteq> iterate i\<cdot>rt\<cdot>s"
by (rule monofun_cfun_arg)



(* ----------------------------------------------------------------------- *)
(* theorems about stream_take                                              *)
(* ----------------------------------------------------------------------- *)


section "stream_take"


lemma stream_reach2: "(LUB i. stream_take i\<cdot>s) = s"
by (rule stream.reach)

lemma chain_stream_take: "chain (\<lambda>i. stream_take i\<cdot>s)"
by simp

lemma stream_take_prefix [simp]: "stream_take n\<cdot>s \<sqsubseteq> s"
apply (insert stream_reach2 [of s])
apply (erule subst) back
apply (rule is_ub_thelub)
apply (simp only: chain_stream_take)
done

lemma stream_take_more [rule_format]:
  "\<forall>x. stream_take n\<cdot>x = x \<longrightarrow> stream_take (Suc n)\<cdot>x = x"
apply (induct_tac n,auto)
apply (case_tac "x=UU",auto)
apply (drule stream_exhaust_eq [THEN iffD1],auto)
done

lemma stream_take_lemma3 [rule_format]:
  "\<forall>x xs. x \<noteq> UU \<longrightarrow> stream_take n\<cdot>(x && xs) = x && xs \<longrightarrow> stream_take n\<cdot>xs = xs"
apply (induct_tac n,clarsimp)
(*apply (drule sym, erule scons_not_empty, simp)*)
apply (clarify, rule stream_take_more)
apply (erule_tac x="x" in allE)
apply (erule_tac x="xs" in allE,simp)
done

lemma stream_take_lemma4:
  "\<forall>x xs. stream_take n\<cdot>xs = xs \<longrightarrow> stream_take (Suc n)\<cdot>(x && xs) = x && xs"
by auto

lemma stream_take_idempotent [rule_format, simp]:
  "\<forall>s. stream_take n\<cdot>(stream_take n\<cdot>s) = stream_take n\<cdot>s"
apply (induct_tac n, auto)
apply (case_tac "s=UU", auto)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
done

lemma stream_take_take_Suc [rule_format, simp]:
  "\<forall>s. stream_take n\<cdot>(stream_take (Suc n)\<cdot>s) = stream_take n\<cdot>s"
apply (induct_tac n, auto)
apply (case_tac "s=UU", auto)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
done

lemma mono_stream_take_pred:
  "stream_take (Suc n)\<cdot>s1 \<sqsubseteq> stream_take (Suc n)\<cdot>s2 \<Longrightarrow>
                       stream_take n\<cdot>s1 \<sqsubseteq> stream_take n\<cdot>s2"
by (insert monofun_cfun_arg [of "stream_take (Suc n)\<cdot>s1"
  "stream_take (Suc n)\<cdot>s2" "stream_take n"], auto)
(*
lemma mono_stream_take_pred:
  "stream_take (Suc n)\<cdot>s1 \<sqsubseteq> stream_take (Suc n)\<cdot>s2 \<Longrightarrow>
                       stream_take n\<cdot>s1 \<sqsubseteq> stream_take n\<cdot>s2"
by (drule mono_stream_take [of _ _ n],simp)
*)

lemma stream_take_lemma10 [rule_format]:
  "\<forall>k\<le>n. stream_take n\<cdot>s1 \<sqsubseteq> stream_take n\<cdot>s2 \<longrightarrow> stream_take k\<cdot>s1 \<sqsubseteq> stream_take k\<cdot>s2"
apply (induct_tac n,simp,clarsimp)
apply (case_tac "k=Suc n",blast)
apply (erule_tac x="k" in allE)
apply (drule mono_stream_take_pred,simp)
done

lemma stream_take_le_mono : "k \<le> n \<Longrightarrow> stream_take k\<cdot>s1 \<sqsubseteq> stream_take n\<cdot>s1"
apply (insert chain_stream_take [of s1])
apply (drule chain_mono,auto)
done

lemma mono_stream_take: "s1 \<sqsubseteq> s2 \<Longrightarrow> stream_take n\<cdot>s1 \<sqsubseteq> stream_take n\<cdot>s2"
by (simp add: monofun_cfun_arg)

(*
lemma stream_take_prefix [simp]: "stream_take n\<cdot>s \<sqsubseteq> s"
apply (subgoal_tac "s=(LUB n. stream_take n\<cdot>s)")
 apply (erule ssubst, rule is_ub_thelub)
 apply (simp only: chain_stream_take)
by (simp only: stream_reach2)
*)

lemma stream_take_take_less:"stream_take k\<cdot>(stream_take n\<cdot>s) \<sqsubseteq> stream_take k\<cdot>s"
by (rule monofun_cfun_arg,auto)


(* ------------------------------------------------------------------------- *)
(* special induction rules                                                   *)
(* ------------------------------------------------------------------------- *)


section "induction"

lemma stream_finite_ind:
  "\<lbrakk>stream_finite x; P UU; \<And>a s. \<lbrakk>a \<noteq> UU; P s\<rbrakk> \<Longrightarrow> P (a && s)\<rbrakk> \<Longrightarrow> P x"
apply (simp add: stream.finite_def,auto)
apply (erule subst)
apply (drule stream.finite_induct [of P _ x], auto)
done

lemma stream_finite_ind2:
  "\<lbrakk>P UU; \<And>x. x \<noteq> UU \<Longrightarrow> P (x && UU); \<And>y z s. \<lbrakk>y \<noteq> UU; z \<noteq> UU; P s\<rbrakk> \<Longrightarrow> P (y && z && s)\<rbrakk> \<Longrightarrow>
                                 \<forall>s. P (stream_take n\<cdot>s)"
apply (rule nat_less_induct [of _ n],auto)
apply (case_tac n, auto) 
apply (case_tac nat, auto) 
apply (case_tac "s=UU",clarsimp)
apply (drule stream_exhaust_eq [THEN iffD1],clarsimp)
apply (case_tac "s=UU",clarsimp)
apply (drule stream_exhaust_eq [THEN iffD1],clarsimp)
apply (case_tac "y=UU",clarsimp)
apply (drule stream_exhaust_eq [THEN iffD1],clarsimp)
done

lemma stream_ind2:
"\<lbrakk> adm P; P UU; \<And>a. a \<noteq> UU \<Longrightarrow> P (a && UU); \<And>a b s. \<lbrakk>a \<noteq> UU; b \<noteq> UU; P s\<rbrakk> \<Longrightarrow> P (a && b && s)\<rbrakk> \<Longrightarrow> P x"
apply (insert stream.reach [of x],erule subst)
apply (erule admD, rule chain_stream_take)
apply (insert stream_finite_ind2 [of P])
by simp



(* ----------------------------------------------------------------------- *)
(* simplify use of coinduction                                             *)
(* ----------------------------------------------------------------------- *)


section "coinduction"

lemma stream_coind_lemma2: "\<forall>s1 s2. R s1 s2 \<longrightarrow> ft\<cdot>s1 = ft\<cdot>s2 \<and> R (rt\<cdot>s1) (rt\<cdot>s2) \<Longrightarrow> stream_bisim R"
 apply (simp add: stream.bisim_def,clarsimp)
 apply (drule spec, drule spec, drule (1) mp)
 apply (case_tac "x", simp)
 apply (case_tac "y", simp)
 apply auto
 done



(* ----------------------------------------------------------------------- *)
(* theorems about stream_finite                                            *)
(* ----------------------------------------------------------------------- *)


section "stream_finite"

lemma stream_finite_UU [simp]: "stream_finite UU"
by (simp add: stream.finite_def)

lemma stream_finite_UU_rev: "\<not> stream_finite s \<Longrightarrow> s \<noteq> UU"
by (auto simp add: stream.finite_def)

lemma stream_finite_lemma1: "stream_finite xs \<Longrightarrow> stream_finite (x && xs)"
apply (simp add: stream.finite_def,auto)
apply (rule_tac x="Suc n" in exI)
apply (simp add: stream_take_lemma4)
done

lemma stream_finite_lemma2: "\<lbrakk>x \<noteq> UU; stream_finite (x && xs)\<rbrakk> \<Longrightarrow> stream_finite xs"
apply (simp add: stream.finite_def, auto)
apply (rule_tac x="n" in exI)
apply (erule stream_take_lemma3,simp)
done

lemma stream_finite_rt_eq: "stream_finite (rt\<cdot>s) = stream_finite s"
apply (cases s, auto)
apply (rule stream_finite_lemma1, simp)
apply (rule stream_finite_lemma2,simp)
apply assumption
done

lemma stream_finite_less: "stream_finite s \<Longrightarrow> \<forall>t. t \<sqsubseteq> s \<longrightarrow> stream_finite t"
apply (erule stream_finite_ind [of s], auto)
apply (case_tac "t=UU", auto)
apply (drule stream_exhaust_eq [THEN iffD1],auto)
apply (erule_tac x="y" in allE, simp)
apply (rule stream_finite_lemma1, simp)
done

lemma stream_take_finite [simp]: "stream_finite (stream_take n\<cdot>s)"
apply (simp add: stream.finite_def)
apply (rule_tac x="n" in exI,simp)
done

lemma adm_not_stream_finite: "adm (\<lambda>x. \<not> stream_finite x)"
apply (rule adm_upward)
apply (erule contrapos_nn)
apply (erule (1) stream_finite_less [rule_format])
done



(* ----------------------------------------------------------------------- *)
(* theorems about stream length                                            *)
(* ----------------------------------------------------------------------- *)


section "slen"

lemma slen_empty [simp]: "#\<bottom> = 0"
by (simp add: slen_def stream.finite_def zero_enat_def Least_equality)

lemma slen_scons [simp]: "x \<noteq> \<bottom> \<Longrightarrow> #(x && xs) = eSuc (#xs)"
apply (case_tac "stream_finite (x && xs)")
apply (simp add: slen_def, auto)
apply (simp add: stream.finite_def, auto simp add: eSuc_enat)
apply (rule Least_Suc2, auto)
(*apply (drule sym)*)
(*apply (drule sym scons_eq_UU [THEN iffD1],simp)*)
apply (erule stream_finite_lemma2, simp)
apply (simp add: slen_def, auto)
apply (drule stream_finite_lemma1,auto)
done

lemma slen_less_1_eq: "(#x < enat (Suc 0)) = (x = \<bottom>)"
by (cases x) (auto simp add: enat_0 eSuc_enat[THEN sym])

lemma slen_empty_eq: "(#x = 0) = (x = \<bottom>)"
by (cases x) auto

lemma slen_scons_eq: "(enat (Suc n) < #x) = (\<exists>a y. x = a && y \<and> a \<noteq> \<bottom> \<and> enat n < #y)"
apply (auto, case_tac "x=UU",auto)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
apply (case_tac "#y") apply simp_all
apply (case_tac "#y") apply simp_all
done

lemma slen_eSuc: "#x = eSuc n \<longrightarrow> (\<exists>a y. x = a && y \<and> a \<noteq> \<bottom> \<and> #y = n)"
by (cases x) auto

lemma slen_stream_take_finite [simp]: "#(stream_take n\<cdot>s) \<noteq> \<infinity>"
by (simp add: slen_def)

lemma slen_scons_eq_rev: "#x < enat (Suc (Suc n)) \<longleftrightarrow> (\<forall>a y. x \<noteq> a && y \<or> a = \<bottom> \<or> #y < enat (Suc n))"
 apply (cases x, auto)
   apply (simp add: zero_enat_def)
  apply (case_tac "#stream") apply (simp_all add: eSuc_enat)
 apply (case_tac "#stream") apply (simp_all add: eSuc_enat)
done

lemma slen_take_lemma4 [rule_format]:
  "\<forall>s. stream_take n\<cdot>s \<noteq> s \<longrightarrow> #(stream_take n\<cdot>s) = enat n"
apply (induct n, auto simp add: enat_0)
apply (case_tac "s=UU", simp)
apply (drule stream_exhaust_eq [THEN iffD1], auto simp add: eSuc_enat)
done

(*
lemma stream_take_idempotent [simp]:
 "stream_take n\<cdot>(stream_take n\<cdot>s) = stream_take n\<cdot>s"
apply (case_tac "stream_take n\<cdot>s = s")
apply (auto,insert slen_take_lemma4 [of n s]);
by (auto,insert slen_take_lemma1 [of "stream_take n\<cdot>s" n],simp)

lemma stream_take_take_Suc [simp]: "stream_take n\<cdot>(stream_take (Suc n)\<cdot>s) =
                                    stream_take n\<cdot>s"
apply (simp add: po_eq_conv,auto)
 apply (simp add: stream_take_take_less)
apply (subgoal_tac "stream_take n\<cdot>s = stream_take n\<cdot>(stream_take n\<cdot>s)")
 apply (erule ssubst)
 apply (rule_tac monofun_cfun_arg)
 apply (insert chain_stream_take [of s])
by (simp add: chain_def,simp)
*)

lemma slen_take_eq: "\<forall>x. enat n < #x \<longleftrightarrow> stream_take n\<cdot>x \<noteq> x"
apply (induct_tac n, auto)
apply (simp add: enat_0, clarsimp)
apply (drule not_sym)
apply (drule slen_empty_eq [THEN iffD1], simp)
apply (case_tac "x=UU", simp)
apply (drule stream_exhaust_eq [THEN iffD1], clarsimp)
apply (erule_tac x="y" in allE, auto)
apply (simp_all add: not_less eSuc_enat)
apply (case_tac "#y") apply simp_all
apply (case_tac "x=UU", simp)
apply (drule stream_exhaust_eq [THEN iffD1], clarsimp)
apply (erule_tac x="y" in allE, simp)
apply (case_tac "#y")
apply simp_all
done

lemma slen_take_eq_rev: "#x \<le> enat n \<longleftrightarrow> stream_take n\<cdot>x = x"
by (simp add: linorder_not_less [symmetric] slen_take_eq)

lemma slen_take_lemma1: "#x = enat n \<Longrightarrow> stream_take n\<cdot>x = x"
by (rule slen_take_eq_rev [THEN iffD1], auto)

lemma slen_rt_mono: "#s2 \<le> #s1 \<Longrightarrow> #(rt\<cdot>s2) \<le> #(rt\<cdot>s1)"
apply (cases s1)
 apply (cases s2, simp+)+
done

lemma slen_take_lemma5: "#(stream_take n\<cdot>s) \<le> enat n"
apply (case_tac "stream_take n\<cdot>s = s")
 apply (simp add: slen_take_eq_rev)
apply (simp add: slen_take_lemma4)
done

lemma slen_take_lemma2: "\<forall>x. \<not> stream_finite x \<longrightarrow> #(stream_take i\<cdot>x) = enat i"
apply (simp add: stream.finite_def, auto)
apply (simp add: slen_take_lemma4)
done

lemma slen_infinite: "stream_finite x \<longleftrightarrow> #x \<noteq> \<infinity>"
by (simp add: slen_def)

lemma slen_mono_lemma: "stream_finite s \<Longrightarrow> \<forall>t. s \<sqsubseteq> t \<longrightarrow> #s \<le> #t"
apply (erule stream_finite_ind [of s], auto)
apply (case_tac "t = UU", auto)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
done

lemma slen_mono: "s \<sqsubseteq> t \<Longrightarrow> #s \<le> #t"
apply (case_tac "stream_finite t")
apply (frule stream_finite_less)
apply (erule_tac x="s" in allE, simp)
apply (drule slen_mono_lemma, auto)
apply (simp add: slen_def)
done

lemma iterate_lemma: "F\<cdot>(iterate n\<cdot>F\<cdot>x) = iterate n\<cdot>F\<cdot>(F\<cdot>x)"
by (insert iterate_Suc2 [of n F x], auto)

lemma slen_rt_mult [rule_format]: "\<forall>x. enat (i + j) \<le> #x \<longrightarrow> enat j \<le> #(iterate i\<cdot>rt\<cdot>x)"
apply (induct i, auto)
apply (case_tac "x = UU", auto simp add: zero_enat_def)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
apply (erule_tac x = "y" in allE, auto)
apply (simp add: not_le) apply (case_tac "#y") apply (simp_all add: eSuc_enat)
apply (simp add: iterate_lemma)
done

lemma slen_take_lemma3 [rule_format]:
  "\<forall>(x::'a::flat stream) y. enat n \<le> #x \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> stream_take n\<cdot>x = stream_take n\<cdot>y"
apply (induct_tac n, auto)
apply (case_tac "x=UU", auto)
apply (simp add: zero_enat_def)
apply (simp add: Suc_ile_eq)
apply (case_tac "y=UU", clarsimp)
apply (drule stream_exhaust_eq [THEN iffD1], clarsimp)+
apply (erule_tac x="ya" in allE, simp)
by (drule ax_flat, simp)

lemma slen_strict_mono_lemma:
  "stream_finite t \<Longrightarrow> \<forall>s. #(s::'a::flat stream) = #t \<and> s \<sqsubseteq> t \<longrightarrow> s = t"
apply (erule stream_finite_ind, auto)
apply (case_tac "sa = UU", auto)
apply (drule stream_exhaust_eq [THEN iffD1], clarsimp)
apply (drule ax_flat, simp)
done

lemma slen_strict_mono: "\<lbrakk>stream_finite t; s \<noteq> t; s \<sqsubseteq> (t::'a::flat stream)\<rbrakk> \<Longrightarrow> #s < #t"
by (auto simp add: slen_mono less_le dest: slen_strict_mono_lemma)

lemma stream_take_Suc_neq: "stream_take (Suc n)\<cdot>s \<noteq> s \<Longrightarrow>
                     stream_take n\<cdot>s \<noteq> stream_take (Suc n)\<cdot>s"
apply auto
apply (subgoal_tac "stream_take n\<cdot>s \<noteq> s")
 apply (insert slen_take_lemma4 [of n s],auto)
apply (cases s, simp)
apply (simp add: slen_take_lemma4 eSuc_enat)
done

(* ----------------------------------------------------------------------- *)
(* theorems about smap                                                     *)
(* ----------------------------------------------------------------------- *)


section "smap"

lemma smap_unfold: "smap = (\<Lambda> f t. case t of x && xs \<Rightarrow> f\<cdot>x && smap\<cdot>f\<cdot>xs)"
by (insert smap_def [where 'a='a and 'b='b, THEN eq_reflection, THEN fix_eq2], auto)

lemma smap_empty [simp]: "smap\<cdot>f\<cdot>\<bottom> = \<bottom>"
by (subst smap_unfold, simp)

lemma smap_scons [simp]: "x \<noteq> \<bottom> \<Longrightarrow> smap\<cdot>f\<cdot>(x && xs) = (f\<cdot>x) && (smap\<cdot>f\<cdot>xs)"
by (subst smap_unfold, force)



(* ----------------------------------------------------------------------- *)
(* theorems about sfilter                                                  *)
(* ----------------------------------------------------------------------- *)

section "sfilter"

lemma sfilter_unfold:
 "sfilter = (\<Lambda> p s. case s of x && xs \<Rightarrow>
  If p\<cdot>x then x && sfilter\<cdot>p\<cdot>xs else sfilter\<cdot>p\<cdot>xs)"
by (insert sfilter_def [where 'a='a, THEN eq_reflection, THEN fix_eq2], auto)

lemma strict_sfilter: "sfilter\<cdot>\<bottom> = \<bottom>"
apply (rule cfun_eqI)
apply (subst sfilter_unfold, auto)
apply (case_tac "x=UU", auto)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
done

lemma sfilter_empty [simp]: "sfilter\<cdot>f\<cdot>\<bottom> = \<bottom>"
by (subst sfilter_unfold, force)

lemma sfilter_scons [simp]:
  "x \<noteq> \<bottom> \<Longrightarrow> sfilter\<cdot>f\<cdot>(x && xs) =
                           If f\<cdot>x then x && sfilter\<cdot>f\<cdot>xs else sfilter\<cdot>f\<cdot>xs"
by (subst sfilter_unfold, force)


(* ----------------------------------------------------------------------- *)
   section "i_rt"
(* ----------------------------------------------------------------------- *)

lemma i_rt_UU [simp]: "i_rt n UU = UU"
  by (induct n) (simp_all add: i_rt_def)

lemma i_rt_0 [simp]: "i_rt 0 s = s"
by (simp add: i_rt_def)

lemma i_rt_Suc [simp]: "a \<noteq> UU \<Longrightarrow> i_rt (Suc n) (a&&s) = i_rt n s"
by (simp add: i_rt_def iterate_Suc2 del: iterate_Suc)

lemma i_rt_Suc_forw: "i_rt (Suc n) s = i_rt n (rt\<cdot>s)"
by (simp only: i_rt_def iterate_Suc2)

lemma i_rt_Suc_back: "i_rt (Suc n) s = rt\<cdot>(i_rt n s)"
by (simp only: i_rt_def,auto)

lemma i_rt_mono: "x << s \<Longrightarrow> i_rt n x  << i_rt n s"
by (simp add: i_rt_def monofun_rt_mult)

lemma i_rt_ij_lemma: "enat (i + j) \<le> #x \<Longrightarrow> enat j \<le> #(i_rt i x)"
by (simp add: i_rt_def slen_rt_mult)

lemma slen_i_rt_mono: "#s2 \<le> #s1 \<Longrightarrow> #(i_rt n s2) \<le> #(i_rt n s1)"
apply (induct_tac n,auto)
apply (simp add: i_rt_Suc_back)
apply (drule slen_rt_mono,simp)
done

lemma i_rt_take_lemma1 [rule_format]: "\<forall>s. i_rt n (stream_take n\<cdot>s) = UU"
apply (induct_tac n)
 apply (simp add: i_rt_Suc_back,auto)
apply (case_tac "s=UU",auto)
apply (drule stream_exhaust_eq [THEN iffD1],auto)
done

lemma i_rt_slen: "i_rt n s = UU \<longleftrightarrow> stream_take n\<cdot>s = s"
apply auto
 apply (insert i_rt_ij_lemma [of n "Suc 0" s])
 apply (subgoal_tac "#(i_rt n s)=0")
  apply (case_tac "stream_take n\<cdot>s = s",simp+)
  apply (insert slen_take_eq [rule_format,of n s],simp)
  apply (cases "#s") apply (simp_all add: zero_enat_def)
  apply (simp add: slen_take_eq)
  apply (cases "#s")
  using i_rt_take_lemma1 [of n s]
  apply (simp_all add: zero_enat_def)
  done

lemma i_rt_lemma_slen: "#s=enat n \<Longrightarrow> i_rt n s = UU"
by (simp add: i_rt_slen slen_take_lemma1)

lemma stream_finite_i_rt [simp]: "stream_finite (i_rt n s) = stream_finite s"
apply (induct_tac n, auto)
 apply (cases s, auto simp del: i_rt_Suc)
apply (simp add: i_rt_Suc_back stream_finite_rt_eq)+
done

lemma take_i_rt_len_lemma: "\<forall>sl x j t. enat sl = #x \<and> n \<le> sl \<and>
                            #(stream_take n\<cdot>x) = enat t \<and> #(i_rt n x) = enat j
                                              \<longrightarrow> enat (j + t) = #x"
apply (induct n, auto)
 apply (simp add: zero_enat_def)
apply (case_tac "x=UU",auto)
 apply (simp add: zero_enat_def)
apply (drule stream_exhaust_eq [THEN iffD1],clarsimp)
apply (subgoal_tac "\<exists>k. enat k = #y",clarify)
 apply (erule_tac x="k" in allE)
 apply (erule_tac x="y" in allE,auto)
 apply (erule_tac x="THE p. Suc p = t" in allE,auto)
   apply (simp add: eSuc_def split: enat.splits)
  apply (simp add: eSuc_def split: enat.splits)
  apply (simp only: the_equality)
 apply (simp add: eSuc_def split: enat.splits)
 apply force
apply (simp add: eSuc_def split: enat.splits)
done

lemma take_i_rt_len:
"\<lbrakk>enat sl = #x; n \<le> sl; #(stream_take n\<cdot>x) = enat t; #(i_rt n x) = enat j\<rbrakk> \<Longrightarrow>
    enat (j + t) = #x"
by (blast intro: take_i_rt_len_lemma [rule_format])


(* ----------------------------------------------------------------------- *)
   section "i_th"
(* ----------------------------------------------------------------------- *)

lemma i_th_i_rt_step:
"[| i_th n s1 << i_th n s2; i_rt (Suc n) s1 << i_rt (Suc n) s2 |] ==>
   i_rt n s1 << i_rt n s2"
apply (simp add: i_th_def i_rt_Suc_back)
apply (cases "i_rt n s1", simp)
apply (cases "i_rt n s2", auto)
done

lemma i_th_stream_take_Suc [rule_format]:
 "\<forall>s. i_th n (stream_take (Suc n)\<cdot>s) = i_th n s"
apply (induct_tac n,auto)
 apply (simp add: i_th_def)
 apply (case_tac "s=UU",auto)
 apply (drule stream_exhaust_eq [THEN iffD1],auto)
apply (case_tac "s=UU",simp add: i_th_def)
apply (drule stream_exhaust_eq [THEN iffD1],auto)
apply (simp add: i_th_def i_rt_Suc_forw)
done

lemma i_th_last: "i_th n s && UU = i_rt n (stream_take (Suc n)\<cdot>s)"
apply (insert surjectiv_scons [of "i_rt n (stream_take (Suc n)\<cdot>s)"])
apply (rule i_th_stream_take_Suc [THEN subst])
apply (simp add: i_th_def  i_rt_Suc_back [symmetric])
by (simp add: i_rt_take_lemma1)

lemma i_th_last_eq:
"i_th n s1 = i_th n s2 \<Longrightarrow> i_rt n (stream_take (Suc n)\<cdot>s1) = i_rt n (stream_take (Suc n)\<cdot>s2)"
apply (insert i_th_last [of n s1])
apply (insert i_th_last [of n s2])
apply auto
done

lemma i_th_prefix_lemma:
"\<lbrakk>k \<le> n; stream_take (Suc n)\<cdot>s1 << stream_take (Suc n)\<cdot>s2\<rbrakk> \<Longrightarrow>
    i_th k s1 << i_th k s2"
apply (insert i_th_stream_take_Suc [of k s1, THEN sym])
apply (insert i_th_stream_take_Suc [of k s2, THEN sym],auto)
apply (simp add: i_th_def)
apply (rule monofun_cfun, auto)
apply (rule i_rt_mono)
apply (blast intro: stream_take_lemma10)
done

lemma take_i_rt_prefix_lemma1:
  "stream_take (Suc n)\<cdot>s1 << stream_take (Suc n)\<cdot>s2 \<Longrightarrow>
   i_rt (Suc n) s1 << i_rt (Suc n) s2 \<Longrightarrow>
   i_rt n s1 << i_rt n s2 \<and> stream_take n\<cdot>s1 << stream_take n\<cdot>s2"
apply auto
 apply (insert i_th_prefix_lemma [of n n s1 s2])
 apply (rule i_th_i_rt_step,auto)
apply (drule mono_stream_take_pred,simp)
done

lemma take_i_rt_prefix_lemma:
"\<lbrakk>stream_take n\<cdot>s1 << stream_take n\<cdot>s2; i_rt n s1 << i_rt n s2\<rbrakk> \<Longrightarrow> s1 << s2"
apply (case_tac "n=0",simp)
apply (auto)
apply (subgoal_tac "stream_take 0\<cdot>s1 << stream_take 0\<cdot>s2 \<and> i_rt 0 s1 << i_rt 0 s2")
 defer 1
 apply (rule zero_induct,blast)
 apply (blast dest: take_i_rt_prefix_lemma1)
apply simp
done

lemma streams_prefix_lemma: "s1 << s2 \<longleftrightarrow>
  (stream_take n\<cdot>s1 << stream_take n\<cdot>s2 \<and> i_rt n s1 << i_rt n s2)"
apply auto
  apply (simp add: monofun_cfun_arg)
 apply (simp add: i_rt_mono)
apply (erule take_i_rt_prefix_lemma,simp)
done

lemma streams_prefix_lemma1:
  "\<lbrakk>stream_take n\<cdot>s1 = stream_take n\<cdot>s2; i_rt n s1 = i_rt n s2\<rbrakk> \<Longrightarrow> s1 = s2"
apply (simp add: po_eq_conv,auto)
 apply (insert streams_prefix_lemma)
 apply blast+
done


(* ----------------------------------------------------------------------- *)
   section "sconc"
(* ----------------------------------------------------------------------- *)

lemma UU_sconc [simp]: " UU ooo s = s "
by (simp add: sconc_def zero_enat_def)

lemma scons_neq_UU: "a \<noteq> UU \<Longrightarrow> a && s \<noteq> UU"
by auto

lemma singleton_sconc [rule_format, simp]: "x \<noteq> UU \<longrightarrow> (x && UU) ooo y = x && y"
apply (simp add: sconc_def zero_enat_def eSuc_def split: enat.splits, auto)
apply (rule someI2_ex,auto)
 apply (rule_tac x="x && y" in exI,auto)
apply (simp add: i_rt_Suc_forw)
apply (case_tac "xa=UU",simp)
by (drule stream_exhaust_eq [THEN iffD1],auto)

lemma ex_sconc [rule_format]:
  "\<forall>k y. #x = enat k \<longrightarrow> (\<exists>w. stream_take k\<cdot>w = x \<and> i_rt k w = y)"
apply (case_tac "#x")
 apply (rule stream_finite_ind [of x],auto)
  apply (simp add: stream.finite_def)
  apply (drule slen_take_lemma1,blast)
 apply (simp_all add: zero_enat_def eSuc_def split: enat.splits)
apply (erule_tac x="y" in allE,auto)
apply (rule_tac x="a && w" in exI,auto)
done

lemma rt_sconc1: "enat n = #x \<Longrightarrow> i_rt n (x ooo y) = y"
apply (simp add: sconc_def split: enat.splits, arith?,auto)
apply (rule someI2_ex,auto)
apply (drule ex_sconc,simp)
done

lemma sconc_inj2: "\<lbrakk>enat n = #x; x ooo y = x ooo z\<rbrakk> \<Longrightarrow> y = z"
apply (frule_tac y=y in rt_sconc1)
apply (auto elim: rt_sconc1)
done

lemma sconc_UU [simp]:"s ooo UU = s"
apply (case_tac "#s")
 apply (simp add: sconc_def)
 apply (rule someI2_ex)
  apply (rule_tac x="s" in exI)
  apply auto
   apply (drule slen_take_lemma1,auto)
  apply (simp add: i_rt_lemma_slen)
 apply (drule slen_take_lemma1,auto)
 apply (simp add: i_rt_slen)
apply (simp add: sconc_def)
done

lemma stream_take_sconc [simp]: "enat n = #x \<Longrightarrow> stream_take n\<cdot>(x ooo y) = x"
apply (simp add: sconc_def)
apply (cases "#x")
apply auto
apply (rule someI2_ex, auto)
apply (drule ex_sconc,simp)
done

lemma scons_sconc [rule_format,simp]: "a \<noteq> UU \<longrightarrow> (a && x) ooo y = a && x ooo y"
apply (cases "#x",auto)
 apply (simp add: sconc_def eSuc_enat)
 apply (rule someI2_ex)
  apply (drule ex_sconc, simp)
 apply (rule someI2_ex, auto)
  apply (simp add: i_rt_Suc_forw)
  apply (rule_tac x="a && xa" in exI, auto)
 apply (case_tac "xaa=UU",auto)
 apply (drule stream_exhaust_eq [THEN iffD1],auto)
 apply (drule streams_prefix_lemma1,simp+)
apply (simp add: sconc_def)
done

lemma ft_sconc: "x \<noteq> UU \<Longrightarrow> ft\<cdot>(x ooo y) = ft\<cdot>x"
by (cases x) auto

lemma sconc_assoc: "(x ooo y) ooo z = x ooo y ooo z"
apply (case_tac "#x")
 apply (rule stream_finite_ind [of x],auto simp del: scons_sconc)
  apply (simp add: stream.finite_def del: scons_sconc)
  apply (drule slen_take_lemma1,auto simp del: scons_sconc)
 apply (case_tac "a = UU", auto)
by (simp add: sconc_def)


(* ----------------------------------------------------------------------- *)

lemma cont_sconc_lemma1: "stream_finite x \<Longrightarrow> cont (\<lambda>y. x ooo y)"
by (erule stream_finite_ind, simp_all)

lemma cont_sconc_lemma2: "\<not> stream_finite x \<Longrightarrow> cont (\<lambda>y. x ooo y)"
by (simp add: sconc_def slen_def)

lemma cont_sconc: "cont (\<lambda>y. x ooo y)"
apply (cases "stream_finite x")
apply (erule cont_sconc_lemma1)
apply (erule cont_sconc_lemma2)
done

lemma sconc_mono: "y << y' \<Longrightarrow> x ooo y << x ooo y'"
by (rule cont_sconc [THEN cont2mono, THEN monofunE])

lemma sconc_mono1 [simp]: "x << x ooo y"
by (rule sconc_mono [of UU, simplified])

(* ----------------------------------------------------------------------- *)

lemma empty_sconc [simp]: "x ooo y = UU \<longleftrightarrow> x = UU \<and> y = UU"
apply (case_tac "#x",auto)
   apply (insert sconc_mono1 [of x y])
   apply auto
done

(* ----------------------------------------------------------------------- *)

lemma rt_sconc [rule_format, simp]: "s \<noteq> UU \<longrightarrow> rt\<cdot>(s ooo x) = rt\<cdot>s ooo x"
by (cases s, auto)

lemma i_th_sconc_lemma [rule_format]:
  "\<forall>x y. enat n < #x \<longrightarrow> i_th n (x ooo y) = i_th n x"
apply (induct_tac n, auto)
apply (simp add: enat_0 i_th_def)
apply (simp add: slen_empty_eq ft_sconc)
apply (simp add: i_th_def)
apply (case_tac "x=UU",auto)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
apply (erule_tac x="ya" in allE)
apply (case_tac "#ya")
apply simp_all
done



(* ----------------------------------------------------------------------- *)

lemma sconc_lemma [rule_format, simp]: "\<forall>s. stream_take n\<cdot>s ooo i_rt n s = s"
apply (induct_tac n,auto)
apply (case_tac "s=UU",auto)
apply (drule stream_exhaust_eq [THEN iffD1],auto)
done

(* ----------------------------------------------------------------------- *)
   subsection "pointwise equality"
(* ----------------------------------------------------------------------- *)

lemma ex_last_stream_take_scons: "stream_take (Suc n)\<cdot>s =
                     stream_take n\<cdot>s ooo i_rt n (stream_take (Suc n)\<cdot>s)"
by (insert sconc_lemma [of n "stream_take (Suc n)\<cdot>s"],simp)

lemma i_th_stream_take_eq:
  "\<And>n. \<forall>n. i_th n s1 = i_th n s2 \<Longrightarrow> stream_take n\<cdot>s1 = stream_take n\<cdot>s2"
apply (induct_tac n,auto)
apply (subgoal_tac "stream_take (Suc na)\<cdot>s1 =
                    stream_take na\<cdot>s1 ooo i_rt na (stream_take (Suc na)\<cdot>s1)")
 apply (subgoal_tac "i_rt na (stream_take (Suc na)\<cdot>s1) =
                    i_rt na (stream_take (Suc na)\<cdot>s2)")
  apply (subgoal_tac "stream_take (Suc na)\<cdot>s2 =
                    stream_take na\<cdot>s2 ooo i_rt na (stream_take (Suc na)\<cdot>s2)")
   apply (insert ex_last_stream_take_scons,simp)
  apply blast
 apply (erule_tac x="na" in allE)
 apply (insert i_th_last_eq [of _ s1 s2])
by blast+

lemma pointwise_eq_lemma[rule_format]: "\<forall>n. i_th n s1 = i_th n s2 \<Longrightarrow> s1 = s2"
by (insert i_th_stream_take_eq [THEN stream.take_lemma],blast)

(* ----------------------------------------------------------------------- *)
   subsection "finiteness"
(* ----------------------------------------------------------------------- *)

lemma slen_sconc_finite1:
  "\<lbrakk>#(x ooo y) = \<infinity>; enat n = #x\<rbrakk> \<Longrightarrow> #y = \<infinity>"
apply (case_tac "#y \<noteq> \<infinity>",auto)
apply (drule_tac y=y in rt_sconc1)
apply (insert stream_finite_i_rt [of n "x ooo y"])
apply (simp add: slen_infinite)
done

lemma slen_sconc_infinite1: "#x=\<infinity> \<Longrightarrow> #(x ooo y) = \<infinity>"
by (simp add: sconc_def)

lemma slen_sconc_infinite2: "#y=\<infinity> \<Longrightarrow> #(x ooo y) = \<infinity>"
apply (case_tac "#x")
 apply (simp add: sconc_def)
 apply (rule someI2_ex)
  apply (drule ex_sconc,auto)
 apply (erule contrapos_pp)
 apply (insert stream_finite_i_rt)
 apply (fastforce simp add: slen_infinite,auto)
by (simp add: sconc_def)

lemma sconc_finite: "#x \<noteq> \<infinity> \<and> #y \<noteq> \<infinity> \<longleftrightarrow> #(x ooo y) \<noteq> \<infinity>"
apply auto
  apply (metis not_infinity_eq slen_sconc_finite1)
 apply (metis not_infinity_eq slen_sconc_infinite1)
apply (metis not_infinity_eq slen_sconc_infinite2)
done

(* ----------------------------------------------------------------------- *)

lemma slen_sconc_mono3: "\<lbrakk>enat n = #x; enat k = #(x ooo y)\<rbrakk> \<Longrightarrow> n \<le> k"
apply (insert slen_mono [of "x" "x ooo y"])
apply (cases "#x") apply simp_all
apply (cases "#(x ooo y)") apply simp_all
done

(* ----------------------------------------------------------------------- *)
   subsection "finite slen"
(* ----------------------------------------------------------------------- *)

lemma slen_sconc: "\<lbrakk>enat n = #x; enat m = #y\<rbrakk> \<Longrightarrow> #(x ooo y) = enat (n + m)"
apply (case_tac "#(x ooo y)")
 apply (frule_tac y=y in rt_sconc1)
 apply (insert take_i_rt_len [of "THE j. enat j = #(x ooo y)" "x ooo y" n n m],simp)
 apply (insert slen_sconc_mono3 [of n x _ y],simp)
apply (insert sconc_finite [of x y],auto)
done

(* ----------------------------------------------------------------------- *)
   subsection "flat prefix"
(* ----------------------------------------------------------------------- *)

lemma sconc_prefix: "(s1::'a::flat stream) << s2 \<Longrightarrow> \<exists>t. s1 ooo t = s2"
apply (case_tac "#s1")
 apply (subgoal_tac "stream_take nat\<cdot>s1 = stream_take nat\<cdot>s2")
  apply (rule_tac x="i_rt nat s2" in exI)
  apply (simp add: sconc_def)
  apply (rule someI2_ex)
   apply (drule ex_sconc)
   apply (simp,clarsimp,drule streams_prefix_lemma1)
   apply (simp+,rule slen_take_lemma3 [of _ s1 s2])
  apply (simp+,rule_tac x="UU" in exI)
apply (insert slen_take_lemma3 [of _ s1 s2])
apply (rule stream.take_lemma,simp)
done

(* ----------------------------------------------------------------------- *)
   subsection "continuity"
(* ----------------------------------------------------------------------- *)

lemma chain_sconc: "chain S \<Longrightarrow> chain (\<lambda>i. (x ooo S i))"
by (simp add: chain_def,auto simp add: sconc_mono)

lemma chain_scons: "chain S \<Longrightarrow> chain (\<lambda>i. a && S i)"
apply (simp add: chain_def,auto)
apply (rule monofun_cfun_arg,simp)
done

lemma contlub_scons_lemma: "chain S \<Longrightarrow> (LUB i. a && S i) = a && (LUB i. S i)"
by (rule cont2contlubE [OF cont_Rep_cfun2, symmetric])

lemma finite_lub_sconc: "chain Y \<Longrightarrow> stream_finite x \<Longrightarrow>
                        (LUB i. x ooo Y i) = (x ooo (LUB i. Y i))"
apply (rule stream_finite_ind [of x])
 apply (auto)
apply (subgoal_tac "(LUB i. a && (s ooo Y i)) = a && (LUB i. s ooo Y i)")
 apply (force,blast dest: contlub_scons_lemma chain_sconc)
done

lemma contlub_sconc_lemma:
  "chain Y \<Longrightarrow> (LUB i. x ooo Y i) = (x ooo (LUB i. Y i))"
apply (case_tac "#x=\<infinity>")
 apply (simp add: sconc_def)
apply (drule finite_lub_sconc,auto simp add: slen_infinite)
done

lemma monofun_sconc: "monofun (\<lambda>y. x ooo y)"
by (simp add: monofun_def sconc_mono)


(* ----------------------------------------------------------------------- *)
   section "constr_sconc"
(* ----------------------------------------------------------------------- *)

lemma constr_sconc_UUs [simp]: "constr_sconc UU s = s"
by (simp add: constr_sconc_def zero_enat_def)

lemma "x ooo y = constr_sconc x y"
apply (case_tac "#x")
 apply (rule stream_finite_ind [of x],auto simp del: scons_sconc)
  defer 1
  apply (simp add: constr_sconc_def del: scons_sconc)
  apply (case_tac "#s")
   apply (simp add: eSuc_enat)
   apply (case_tac "a=UU",auto simp del: scons_sconc)
   apply (simp)
  apply (simp add: sconc_def)
 apply (simp add: constr_sconc_def)
apply (simp add: stream.finite_def)
apply (drule slen_take_lemma1,auto)
done

end
