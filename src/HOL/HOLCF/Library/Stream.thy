(*  Title:      HOL/HOLCF/Library/Stream.thy
    Author:     Franz Regensburger, David von Oheimb, Borislav Gajanovic
*)

header {* General Stream domain *}

theory Stream
imports HOLCF "~~/src/HOL/Library/Extended_Nat"
begin

default_sort pcpo

domain (unsafe) 'a stream = scons (ft::'a) (lazy rt::"'a stream") (infixr "&&" 65)

definition
  smap :: "('a \<rightarrow> 'b) \<rightarrow> 'a stream \<rightarrow> 'b stream" where
  "smap = fix\<cdot>(\<Lambda> h f s. case s of x && xs \<Rightarrow> f\<cdot>x && h\<cdot>f\<cdot>xs)"

definition
  sfilter :: "('a \<rightarrow> tr) \<rightarrow> 'a stream \<rightarrow> 'a stream" where
  "sfilter = fix\<cdot>(\<Lambda> h p s. case s of x && xs \<Rightarrow>
                                     If p\<cdot>x then x && h\<cdot>p\<cdot>xs else h\<cdot>p\<cdot>xs)"

definition
  slen :: "'a stream \<Rightarrow> enat"  ("#_" [1000] 1000) where
  "#s = (if stream_finite s then enat (LEAST n. stream_take n\<cdot>s = s) else \<infinity>)"


(* concatenation *)

definition
  i_rt :: "nat => 'a stream => 'a stream" where (* chops the first i elements *)
  "i_rt = (%i s. iterate i$rt$s)"

definition
  i_th :: "nat => 'a stream => 'a" where (* the i-th element *)
  "i_th = (%i s. ft$(i_rt i s))"

definition
  sconc :: "'a stream => 'a stream => 'a stream"  (infixr "ooo" 65) where
  "s1 ooo s2 = (case #s1 of
                  enat n \<Rightarrow> (SOME s. (stream_take n$s=s1) & (i_rt n s = s2))
               | \<infinity>     \<Rightarrow> s1)"

primrec constr_sconc' :: "nat => 'a stream => 'a stream => 'a stream"
where
  constr_sconc'_0:   "constr_sconc' 0 s1 s2 = s2"
| constr_sconc'_Suc: "constr_sconc' (Suc n) s1 s2 = ft$s1 &&
                                                    constr_sconc' n (rt$s1) s2"

definition
  constr_sconc  :: "'a stream => 'a stream => 'a stream" where (* constructive *)
  "constr_sconc s1 s2 = (case #s1 of
                          enat n \<Rightarrow> constr_sconc' n s1 s2
                        | \<infinity>    \<Rightarrow> s1)"


(* ----------------------------------------------------------------------- *)
(* theorems about scons                                                    *)
(* ----------------------------------------------------------------------- *)


section "scons"

lemma scons_eq_UU: "(a && s = UU) = (a = UU)"
by simp

lemma scons_not_empty: "[| a && x = UU; a ~= UU |] ==> R"
by simp

lemma stream_exhaust_eq: "(x ~= UU) = (EX a y. a ~= UU &  x = a && y)"
by (cases x, auto)

lemma stream_neq_UU: "x~=UU ==> EX a a_s. x=a&&a_s & a~=UU"
by (simp add: stream_exhaust_eq,auto)

lemma stream_prefix:
  "[| a && s << t; a ~= UU  |] ==> EX b tt. t = b && tt &  b ~= UU &  s << tt"
by (cases t, auto)

lemma stream_prefix':
  "b ~= UU ==> x << b && z =
   (x = UU |  (EX a y. x = a && y &  a ~= UU &  a << b &  y << z))"
by (cases x, auto)


(*
lemma stream_prefix1: "[| x<<y; xs<<ys |] ==> x&&xs << y&&ys"
by (insert stream_prefix' [of y "x&&xs" ys],force)
*)

lemma stream_flat_prefix:
  "[| x && xs << y && ys; (x::'a::flat) ~= UU|] ==> x = y & xs << ys"
apply (case_tac "y=UU",auto)
apply (drule ax_flat,simp)
done




(* ----------------------------------------------------------------------- *)
(* theorems about stream_case                                              *)
(* ----------------------------------------------------------------------- *)

section "stream_case"


lemma stream_case_strictf: "stream_case$UU$s=UU"
by (cases s, auto)



(* ----------------------------------------------------------------------- *)
(* theorems about ft and rt                                                *)
(* ----------------------------------------------------------------------- *)


section "ft & rt"


lemma ft_defin: "s~=UU ==> ft$s~=UU"
by simp

lemma rt_strict_rev: "rt$s~=UU ==> s~=UU"
by auto

lemma surjectiv_scons: "(ft$s)&&(rt$s)=s"
by (cases s, auto)

lemma monofun_rt_mult: "x << s ==> iterate i$rt$x << iterate i$rt$s"
by (rule monofun_cfun_arg)



(* ----------------------------------------------------------------------- *)
(* theorems about stream_take                                              *)
(* ----------------------------------------------------------------------- *)


section "stream_take"


lemma stream_reach2: "(LUB i. stream_take i$s) = s"
by (rule stream.reach)

lemma chain_stream_take: "chain (%i. stream_take i$s)"
by simp

lemma stream_take_prefix [simp]: "stream_take n$s << s"
apply (insert stream_reach2 [of s])
apply (erule subst) back
apply (rule is_ub_thelub)
apply (simp only: chain_stream_take)
done

lemma stream_take_more [rule_format]:
  "ALL x. stream_take n$x = x --> stream_take (Suc n)$x = x"
apply (induct_tac n,auto)
apply (case_tac "x=UU",auto)
apply (drule stream_exhaust_eq [THEN iffD1],auto)
done

lemma stream_take_lemma3 [rule_format]:
  "ALL x xs. x~=UU --> stream_take n$(x && xs) = x && xs --> stream_take n$xs=xs"
apply (induct_tac n,clarsimp)
(*apply (drule sym, erule scons_not_empty, simp)*)
apply (clarify, rule stream_take_more)
apply (erule_tac x="x" in allE)
apply (erule_tac x="xs" in allE,simp)
done

lemma stream_take_lemma4:
  "ALL x xs. stream_take n$xs=xs --> stream_take (Suc n)$(x && xs) = x && xs"
by auto

lemma stream_take_idempotent [rule_format, simp]:
 "ALL s. stream_take n$(stream_take n$s) = stream_take n$s"
apply (induct_tac n, auto)
apply (case_tac "s=UU", auto)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
done

lemma stream_take_take_Suc [rule_format, simp]:
  "ALL s. stream_take n$(stream_take (Suc n)$s) =
                                    stream_take n$s"
apply (induct_tac n, auto)
apply (case_tac "s=UU", auto)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
done

lemma mono_stream_take_pred:
  "stream_take (Suc n)$s1 << stream_take (Suc n)$s2 ==>
                       stream_take n$s1 << stream_take n$s2"
by (insert monofun_cfun_arg [of "stream_take (Suc n)$s1"
  "stream_take (Suc n)$s2" "stream_take n"], auto)
(*
lemma mono_stream_take_pred:
  "stream_take (Suc n)$s1 << stream_take (Suc n)$s2 ==>
                       stream_take n$s1 << stream_take n$s2"
by (drule mono_stream_take [of _ _ n],simp)
*)

lemma stream_take_lemma10 [rule_format]:
  "ALL k<=n. stream_take n$s1 << stream_take n$s2
                             --> stream_take k$s1 << stream_take k$s2"
apply (induct_tac n,simp,clarsimp)
apply (case_tac "k=Suc n",blast)
apply (erule_tac x="k" in allE)
apply (drule mono_stream_take_pred,simp)
done

lemma stream_take_le_mono : "k<=n ==> stream_take k$s1 << stream_take n$s1"
apply (insert chain_stream_take [of s1])
apply (drule chain_mono,auto)
done

lemma mono_stream_take: "s1 << s2 ==> stream_take n$s1 << stream_take n$s2"
by (simp add: monofun_cfun_arg)

(*
lemma stream_take_prefix [simp]: "stream_take n$s << s"
apply (subgoal_tac "s=(LUB n. stream_take n$s)")
 apply (erule ssubst, rule is_ub_thelub)
 apply (simp only: chain_stream_take)
by (simp only: stream_reach2)
*)

lemma stream_take_take_less:"stream_take k$(stream_take n$s) << stream_take k$s"
by (rule monofun_cfun_arg,auto)


(* ------------------------------------------------------------------------- *)
(* special induction rules                                                   *)
(* ------------------------------------------------------------------------- *)


section "induction"

lemma stream_finite_ind:
 "[| stream_finite x; P UU; !!a s. [| a ~= UU; P s |] ==> P (a && s) |] ==> P x"
apply (simp add: stream.finite_def,auto)
apply (erule subst)
apply (drule stream.finite_induct [of P _ x], auto)
done

lemma stream_finite_ind2:
"[| P UU; !! x. x ~= UU ==> P (x && UU); !! y z s. [| y ~= UU; z ~= UU; P s |] ==> P (y && z && s )|] ==>
                                 !s. P (stream_take n$s)"
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
"[| adm P; P UU; !!a. a ~= UU ==> P (a && UU); !!a b s. [| a ~= UU; b ~= UU; P s |] ==> P (a && b && s) |] ==> P x"
apply (insert stream.reach [of x],erule subst)
apply (erule admD, rule chain_stream_take)
apply (insert stream_finite_ind2 [of P])
by simp



(* ----------------------------------------------------------------------- *)
(* simplify use of coinduction                                             *)
(* ----------------------------------------------------------------------- *)


section "coinduction"

lemma stream_coind_lemma2: "!s1 s2. R s1 s2 --> ft$s1 = ft$s2 &  R (rt$s1) (rt$s2) ==> stream_bisim R"
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

lemma stream_finite_UU_rev: "~  stream_finite s ==> s ~= UU"
by (auto simp add: stream.finite_def)

lemma stream_finite_lemma1: "stream_finite xs ==> stream_finite (x && xs)"
apply (simp add: stream.finite_def,auto)
apply (rule_tac x="Suc n" in exI)
apply (simp add: stream_take_lemma4)
done

lemma stream_finite_lemma2: "[| x ~= UU; stream_finite (x && xs) |] ==> stream_finite xs"
apply (simp add: stream.finite_def, auto)
apply (rule_tac x="n" in exI)
apply (erule stream_take_lemma3,simp)
done

lemma stream_finite_rt_eq: "stream_finite (rt$s) = stream_finite s"
apply (cases s, auto)
apply (rule stream_finite_lemma1, simp)
apply (rule stream_finite_lemma2,simp)
apply assumption
done

lemma stream_finite_less: "stream_finite s ==> !t. t<<s --> stream_finite t"
apply (erule stream_finite_ind [of s], auto)
apply (case_tac "t=UU", auto)
apply (drule stream_exhaust_eq [THEN iffD1],auto)
apply (erule_tac x="y" in allE, simp)
apply (rule stream_finite_lemma1, simp)
done

lemma stream_take_finite [simp]: "stream_finite (stream_take n$s)"
apply (simp add: stream.finite_def)
apply (rule_tac x="n" in exI,simp)
done

lemma adm_not_stream_finite: "adm (%x. ~ stream_finite x)"
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

lemma slen_scons [simp]: "x ~= \<bottom> ==> #(x&&xs) = eSuc (#xs)"
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

lemma slen_scons_eq: "(enat (Suc n) < #x) = (? a y. x = a && y &  a ~= \<bottom> &  enat n < #y)"
apply (auto, case_tac "x=UU",auto)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
apply (case_tac "#y") apply simp_all
apply (case_tac "#y") apply simp_all
done

lemma slen_eSuc: "#x = eSuc n --> (? a y. x = a&&y &  a ~= \<bottom> &  #y = n)"
by (cases x) auto

lemma slen_stream_take_finite [simp]: "#(stream_take n$s) ~= \<infinity>"
by (simp add: slen_def)

lemma slen_scons_eq_rev: "(#x < enat (Suc (Suc n))) = (!a y. x ~= a && y |  a = \<bottom> |  #y < enat (Suc n))"
 apply (cases x, auto)
   apply (simp add: zero_enat_def)
  apply (case_tac "#stream") apply (simp_all add: eSuc_enat)
 apply (case_tac "#stream") apply (simp_all add: eSuc_enat)
done

lemma slen_take_lemma4 [rule_format]:
  "!s. stream_take n$s ~= s --> #(stream_take n$s) = enat n"
apply (induct n, auto simp add: enat_0)
apply (case_tac "s=UU", simp)
apply (drule stream_exhaust_eq [THEN iffD1], auto simp add: eSuc_enat)
done

(*
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
*)

lemma slen_take_eq: "ALL x. (enat n < #x) = (stream_take n\<cdot>x ~= x)"
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

lemma slen_take_eq_rev: "(#x <= enat n) = (stream_take n\<cdot>x = x)"
by (simp add: linorder_not_less [symmetric] slen_take_eq)

lemma slen_take_lemma1: "#x = enat n ==> stream_take n\<cdot>x = x"
by (rule slen_take_eq_rev [THEN iffD1], auto)

lemma slen_rt_mono: "#s2 <= #s1 ==> #(rt$s2) <= #(rt$s1)"
apply (cases s1)
 apply (cases s2, simp+)+
done

lemma slen_take_lemma5: "#(stream_take n$s) <= enat n"
apply (case_tac "stream_take n$s = s")
 apply (simp add: slen_take_eq_rev)
apply (simp add: slen_take_lemma4)
done

lemma slen_take_lemma2: "!x. ~stream_finite x --> #(stream_take i\<cdot>x) = enat i"
apply (simp add: stream.finite_def, auto)
apply (simp add: slen_take_lemma4)
done

lemma slen_infinite: "stream_finite x = (#x ~= \<infinity>)"
by (simp add: slen_def)

lemma slen_mono_lemma: "stream_finite s ==> ALL t. s << t --> #s <= #t"
apply (erule stream_finite_ind [of s], auto)
apply (case_tac "t=UU", auto)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
done

lemma slen_mono: "s << t ==> #s <= #t"
apply (case_tac "stream_finite t")
apply (frule stream_finite_less)
apply (erule_tac x="s" in allE, simp)
apply (drule slen_mono_lemma, auto)
apply (simp add: slen_def)
done

lemma iterate_lemma: "F$(iterate n$F$x) = iterate n$F$(F$x)"
by (insert iterate_Suc2 [of n F x], auto)

lemma slen_rt_mult [rule_format]: "!x. enat (i + j) <= #x --> enat j <= #(iterate i$rt$x)"
apply (induct i, auto)
apply (case_tac "x=UU", auto simp add: zero_enat_def)
apply (drule stream_exhaust_eq [THEN iffD1], auto)
apply (erule_tac x="y" in allE, auto)
apply (simp add: not_le) apply (case_tac "#y") apply (simp_all add: eSuc_enat)
apply (simp add: iterate_lemma)
done

lemma slen_take_lemma3 [rule_format]:
  "!(x::'a::flat stream) y. enat n <= #x --> x << y --> stream_take n\<cdot>x = stream_take n\<cdot>y"
apply (induct_tac n, auto)
apply (case_tac "x=UU", auto)
apply (simp add: zero_enat_def)
apply (simp add: Suc_ile_eq)
apply (case_tac "y=UU", clarsimp)
apply (drule stream_exhaust_eq [THEN iffD1], clarsimp)+
apply (erule_tac x="ya" in allE, simp)
by (drule ax_flat, simp)

lemma slen_strict_mono_lemma:
  "stream_finite t ==> !s. #(s::'a::flat stream) = #t &  s << t --> s = t"
apply (erule stream_finite_ind, auto)
apply (case_tac "sa=UU", auto)
apply (drule stream_exhaust_eq [THEN iffD1], clarsimp)
apply (drule ax_flat, simp)
done

lemma slen_strict_mono: "[|stream_finite t; s ~= t; s << (t::'a::flat stream) |] ==> #s < #t"
by (auto simp add: slen_mono less_le dest: slen_strict_mono_lemma)

lemma stream_take_Suc_neq: "stream_take (Suc n)$s ~=s ==>
                     stream_take n$s ~= stream_take (Suc n)$s"
apply auto
apply (subgoal_tac "stream_take n$s ~=s")
 apply (insert slen_take_lemma4 [of n s],auto)
apply (cases s, simp)
apply (simp add: slen_take_lemma4 eSuc_enat)
done

(* ----------------------------------------------------------------------- *)
(* theorems about smap                                                     *)
(* ----------------------------------------------------------------------- *)


section "smap"

lemma smap_unfold: "smap = (\<Lambda> f t. case t of x&&xs \<Rightarrow> f$x && smap$f$xs)"
by (insert smap_def [where 'a='a and 'b='b, THEN eq_reflection, THEN fix_eq2], auto)

lemma smap_empty [simp]: "smap\<cdot>f\<cdot>\<bottom> = \<bottom>"
by (subst smap_unfold, simp)

lemma smap_scons [simp]: "x~=\<bottom> ==> smap\<cdot>f\<cdot>(x&&xs) = (f\<cdot>x)&&(smap\<cdot>f\<cdot>xs)"
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
  "x ~= \<bottom> ==> sfilter\<cdot>f\<cdot>(x && xs) =
                           If f\<cdot>x then x && sfilter\<cdot>f\<cdot>xs else sfilter\<cdot>f\<cdot>xs"
by (subst sfilter_unfold, force)


(* ----------------------------------------------------------------------- *)
   section "i_rt"
(* ----------------------------------------------------------------------- *)

lemma i_rt_UU [simp]: "i_rt n UU = UU"
  by (induct n) (simp_all add: i_rt_def)

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

lemma i_rt_ij_lemma: "enat (i + j) <= #x ==> enat j <= #(i_rt i x)"
by (simp add: i_rt_def slen_rt_mult)

lemma slen_i_rt_mono: "#s2 <= #s1 ==> #(i_rt n s2) <= #(i_rt n s1)"
apply (induct_tac n,auto)
apply (simp add: i_rt_Suc_back)
apply (drule slen_rt_mono,simp)
done

lemma i_rt_take_lemma1 [rule_format]: "ALL s. i_rt n (stream_take n$s) = UU"
apply (induct_tac n)
 apply (simp add: i_rt_Suc_back,auto)
apply (case_tac "s=UU",auto)
apply (drule stream_exhaust_eq [THEN iffD1],auto)
done

lemma i_rt_slen: "(i_rt n s = UU) = (stream_take n$s = s)"
apply auto
 apply (insert i_rt_ij_lemma [of n "Suc 0" s])
 apply (subgoal_tac "#(i_rt n s)=0")
  apply (case_tac "stream_take n$s = s",simp+)
  apply (insert slen_take_eq [rule_format,of n s],simp)
  apply (cases "#s") apply (simp_all add: zero_enat_def)
  apply (simp add: slen_take_eq)
  apply (cases "#s")
  using i_rt_take_lemma1 [of n s]
  apply (simp_all add: zero_enat_def)
  done

lemma i_rt_lemma_slen: "#s=enat n ==> i_rt n s = UU"
by (simp add: i_rt_slen slen_take_lemma1)

lemma stream_finite_i_rt [simp]: "stream_finite (i_rt n s) = stream_finite s"
apply (induct_tac n, auto)
 apply (cases s, auto simp del: i_rt_Suc)
apply (simp add: i_rt_Suc_back stream_finite_rt_eq)+
done

lemma take_i_rt_len_lemma: "ALL sl x j t. enat sl = #x & n <= sl &
                            #(stream_take n$x) = enat t & #(i_rt n x)= enat j
                                              --> enat (j + t) = #x"
apply (induct n, auto)
 apply (simp add: zero_enat_def)
apply (case_tac "x=UU",auto)
 apply (simp add: zero_enat_def)
apply (drule stream_exhaust_eq [THEN iffD1],clarsimp)
apply (subgoal_tac "EX k. enat k = #y",clarify)
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
"[| enat sl = #x; n <= sl; #(stream_take n$x) = enat t; #(i_rt n x) = enat j |] ==>
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
 "ALL s. i_th n (stream_take (Suc n)$s) = i_th n s"
apply (induct_tac n,auto)
 apply (simp add: i_th_def)
 apply (case_tac "s=UU",auto)
 apply (drule stream_exhaust_eq [THEN iffD1],auto)
apply (case_tac "s=UU",simp add: i_th_def)
apply (drule stream_exhaust_eq [THEN iffD1],auto)
apply (simp add: i_th_def i_rt_Suc_forw)
done

lemma i_th_last: "i_th n s && UU = i_rt n (stream_take (Suc n)$s)"
apply (insert surjectiv_scons [of "i_rt n (stream_take (Suc n)$s)"])
apply (rule i_th_stream_take_Suc [THEN subst])
apply (simp add: i_th_def  i_rt_Suc_back [symmetric])
by (simp add: i_rt_take_lemma1)

lemma i_th_last_eq:
"i_th n s1 = i_th n s2 ==> i_rt n (stream_take (Suc n)$s1) = i_rt n (stream_take (Suc n)$s2)"
apply (insert i_th_last [of n s1])
apply (insert i_th_last [of n s2])
apply auto
done

lemma i_th_prefix_lemma:
"[| k <= n; stream_take (Suc n)$s1 << stream_take (Suc n)$s2 |] ==>
    i_th k s1 << i_th k s2"
apply (insert i_th_stream_take_Suc [of k s1, THEN sym])
apply (insert i_th_stream_take_Suc [of k s2, THEN sym],auto)
apply (simp add: i_th_def)
apply (rule monofun_cfun, auto)
apply (rule i_rt_mono)
apply (blast intro: stream_take_lemma10)
done

lemma take_i_rt_prefix_lemma1:
  "stream_take (Suc n)$s1 << stream_take (Suc n)$s2 ==>
   i_rt (Suc n) s1 << i_rt (Suc n) s2 ==>
   i_rt n s1 << i_rt n s2 & stream_take n$s1 << stream_take n$s2"
apply auto
 apply (insert i_th_prefix_lemma [of n n s1 s2])
 apply (rule i_th_i_rt_step,auto)
apply (drule mono_stream_take_pred,simp)
done

lemma take_i_rt_prefix_lemma:
"[| stream_take n$s1 << stream_take n$s2; i_rt n s1 << i_rt n s2 |] ==> s1 << s2"
apply (case_tac "n=0",simp)
apply (auto)
apply (subgoal_tac "stream_take 0$s1 << stream_take 0$s2 &
                    i_rt 0 s1 << i_rt 0 s2")
 defer 1
 apply (rule zero_induct,blast)
 apply (blast dest: take_i_rt_prefix_lemma1)
apply simp
done

lemma streams_prefix_lemma: "(s1 << s2) =
  (stream_take n$s1 << stream_take n$s2 & i_rt n s1 << i_rt n s2)"
apply auto
  apply (simp add: monofun_cfun_arg)
 apply (simp add: i_rt_mono)
apply (erule take_i_rt_prefix_lemma,simp)
done

lemma streams_prefix_lemma1:
 "[| stream_take n$s1 = stream_take n$s2; i_rt n s1 = i_rt n s2 |] ==> s1 = s2"
apply (simp add: po_eq_conv,auto)
 apply (insert streams_prefix_lemma)
 apply blast+
done


(* ----------------------------------------------------------------------- *)
   section "sconc"
(* ----------------------------------------------------------------------- *)

lemma UU_sconc [simp]: " UU ooo s = s "
by (simp add: sconc_def zero_enat_def)

lemma scons_neq_UU: "a~=UU ==> a && s ~=UU"
by auto

lemma singleton_sconc [rule_format, simp]: "x~=UU --> (x && UU) ooo y = x && y"
apply (simp add: sconc_def zero_enat_def eSuc_def split: enat.splits, auto)
apply (rule someI2_ex,auto)
 apply (rule_tac x="x && y" in exI,auto)
apply (simp add: i_rt_Suc_forw)
apply (case_tac "xa=UU",simp)
by (drule stream_exhaust_eq [THEN iffD1],auto)

lemma ex_sconc [rule_format]:
  "ALL k y. #x = enat k --> (EX w. stream_take k$w = x & i_rt k w = y)"
apply (case_tac "#x")
 apply (rule stream_finite_ind [of x],auto)
  apply (simp add: stream.finite_def)
  apply (drule slen_take_lemma1,blast)
 apply (simp_all add: zero_enat_def eSuc_def split: enat.splits)
apply (erule_tac x="y" in allE,auto)
apply (rule_tac x="a && w" in exI,auto)
done

lemma rt_sconc1: "enat n = #x ==> i_rt n (x ooo y) = y"
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

lemma stream_take_sconc [simp]: "enat n = #x ==> stream_take n$(x ooo y) = x"
apply (simp add: sconc_def)
apply (cases "#x")
apply auto
apply (rule someI2_ex, auto)
apply (drule ex_sconc,simp)
done

lemma scons_sconc [rule_format,simp]: "a~=UU --> (a && x) ooo y = a && x ooo y"
apply (cases "#x",auto)
 apply (simp add: sconc_def eSuc_enat)
 apply (rule someI2_ex)
  apply (drule ex_sconc, simp)
 apply (rule someI2_ex, auto)
  apply (simp add: i_rt_Suc_forw)
  apply (rule_tac x="a && x" in exI, auto)
 apply (case_tac "xa=UU",auto)
 apply (drule stream_exhaust_eq [THEN iffD1],auto)
 apply (drule streams_prefix_lemma1,simp+)
apply (simp add: sconc_def)
done

lemma ft_sconc: "x ~= UU ==> ft$(x ooo y) = ft$x"
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

lemma sconc_mono: "y << y' ==> x ooo y << x ooo y'"
by (rule cont_sconc [THEN cont2mono, THEN monofunE])

lemma sconc_mono1 [simp]: "x << x ooo y"
by (rule sconc_mono [of UU, simplified])

(* ----------------------------------------------------------------------- *)

lemma empty_sconc [simp]: "(x ooo y = UU) = (x = UU & y = UU)"
apply (case_tac "#x",auto)
   apply (insert sconc_mono1 [of x y])
   apply auto
done

(* ----------------------------------------------------------------------- *)

lemma rt_sconc [rule_format, simp]: "s~=UU --> rt$(s ooo x) = rt$s ooo x"
by (cases s, auto)

lemma i_th_sconc_lemma [rule_format]:
  "ALL x y. enat n < #x --> i_th n (x ooo y) = i_th n x"
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

lemma sconc_lemma [rule_format, simp]: "ALL s. stream_take n$s ooo i_rt n s = s"
apply (induct_tac n,auto)
apply (case_tac "s=UU",auto)
apply (drule stream_exhaust_eq [THEN iffD1],auto)
done

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
by (insert i_th_stream_take_eq [THEN stream.take_lemma],blast)

(* ----------------------------------------------------------------------- *)
   subsection "finiteness"
(* ----------------------------------------------------------------------- *)

lemma slen_sconc_finite1:
  "[| #(x ooo y) = \<infinity>; enat n = #x |] ==> #y = \<infinity>"
apply (case_tac "#y ~= \<infinity>",auto)
apply (drule_tac y=y in rt_sconc1)
apply (insert stream_finite_i_rt [of n "x ooo y"])
apply (simp add: slen_infinite)
done

lemma slen_sconc_infinite1: "#x=\<infinity> ==> #(x ooo y) = \<infinity>"
by (simp add: sconc_def)

lemma slen_sconc_infinite2: "#y=\<infinity> ==> #(x ooo y) = \<infinity>"
apply (case_tac "#x")
 apply (simp add: sconc_def)
 apply (rule someI2_ex)
  apply (drule ex_sconc,auto)
 apply (erule contrapos_pp)
 apply (insert stream_finite_i_rt)
 apply (fastforce simp add: slen_infinite,auto)
by (simp add: sconc_def)

lemma sconc_finite: "(#x~=\<infinity> & #y~=\<infinity>) = (#(x ooo y)~=\<infinity>)"
apply auto
  apply (metis not_infinity_eq slen_sconc_finite1)
 apply (metis not_infinity_eq slen_sconc_infinite1)
apply (metis not_infinity_eq slen_sconc_infinite2)
done

(* ----------------------------------------------------------------------- *)

lemma slen_sconc_mono3: "[| enat n = #x; enat k = #(x ooo y) |] ==> n <= k"
apply (insert slen_mono [of "x" "x ooo y"])
apply (cases "#x") apply simp_all
apply (cases "#(x ooo y)") apply simp_all
done

(* ----------------------------------------------------------------------- *)
   subsection "finite slen"
(* ----------------------------------------------------------------------- *)

lemma slen_sconc: "[| enat n = #x; enat m = #y |] ==> #(x ooo y) = enat (n + m)"
apply (case_tac "#(x ooo y)")
 apply (frule_tac y=y in rt_sconc1)
 apply (insert take_i_rt_len [of "THE j. enat j = #(x ooo y)" "x ooo y" n n m],simp)
 apply (insert slen_sconc_mono3 [of n x _ y],simp)
apply (insert sconc_finite [of x y],auto)
done

(* ----------------------------------------------------------------------- *)
   subsection "flat prefix"
(* ----------------------------------------------------------------------- *)

lemma sconc_prefix: "(s1::'a::flat stream) << s2 ==> EX t. s1 ooo t = s2"
apply (case_tac "#s1")
 apply (subgoal_tac "stream_take nat$s1 = stream_take nat$s2")
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

lemma chain_sconc: "chain S ==> chain (%i. (x ooo S i))"
by (simp add: chain_def,auto simp add: sconc_mono)

lemma chain_scons: "chain S ==> chain (%i. a && S i)"
apply (simp add: chain_def,auto)
apply (rule monofun_cfun_arg,simp)
done

lemma contlub_scons_lemma: "chain S ==> (LUB i. a && S i) = a && (LUB i. S i)"
by (rule cont2contlubE [OF cont_Rep_cfun2, symmetric])

lemma finite_lub_sconc: "chain Y ==> (stream_finite x) ==>
                        (LUB i. x ooo Y i) = (x ooo (LUB i. Y i))"
apply (rule stream_finite_ind [of x])
 apply (auto)
apply (subgoal_tac "(LUB i. a && (s ooo Y i)) = a && (LUB i. s ooo Y i)")
 apply (force,blast dest: contlub_scons_lemma chain_sconc)
done

lemma contlub_sconc_lemma:
  "chain Y ==> (LUB i. x ooo Y i) = (x ooo (LUB i. Y i))"
apply (case_tac "#x=\<infinity>")
 apply (simp add: sconc_def)
apply (drule finite_lub_sconc,auto simp add: slen_infinite)
done

lemma monofun_sconc: "monofun (%y. x ooo y)"
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
