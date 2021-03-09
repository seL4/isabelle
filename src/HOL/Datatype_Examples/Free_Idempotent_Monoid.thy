theory Free_Idempotent_Monoid imports
  "HOL-Library.Confluent_Quotient"
begin

inductive cancel1 :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where cancel1: "xs \<noteq> [] \<Longrightarrow> cancel1 (gs @ xs @ xs @ gs') (gs @ xs @ gs')"

abbreviation cancel where "cancel \<equiv> cancel1\<^sup>*\<^sup>*"

lemma cancel1_append_same1:
  assumes "cancel1 xs ys"
  shows "cancel1 (zs @ xs) (zs @ ys)"
using assms
proof cases
  case (cancel1 ys gs gs')
  from \<open>ys \<noteq> []\<close> have "cancel1 ((zs @ gs) @ ys @ ys @ gs') ((zs @ gs) @ ys @ gs')" ..
  with cancel1 show ?thesis by simp
qed

lemma cancel_append_same1: "cancel (zs @ xs) (zs @ ys)" if "cancel xs ys"
  using that by induction(blast intro: rtranclp.rtrancl_into_rtrancl cancel1_append_same1)+

lemma cancel1_append_same2: "cancel1 xs ys \<Longrightarrow> cancel1 (xs @ zs) (ys @ zs)"
by(cases rule: cancel1.cases)(auto intro: cancel1.intros)

lemma cancel_append_same2: "cancel (xs @ zs) (ys @ zs)" if "cancel xs ys"
  using that by induction(blast intro: rtranclp.rtrancl_into_rtrancl cancel1_append_same2)+

lemma cancel1_same:
  assumes "xs \<noteq> []"
  shows "cancel1 (xs @ xs) xs"
proof -
  have "cancel1 ([] @ xs @ xs @ []) ([] @ xs @ [])" using assms ..
  thus ?thesis by simp
qed

lemma cancel_same: "cancel (xs @ xs) xs"
  by(cases "xs = []")(auto intro: cancel1_same)

abbreviation (input) eq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where "eq \<equiv> equivclp cancel1"

lemma eq_sym: "eq x y \<Longrightarrow> eq y x"
  by(rule equivclp_sym)

lemma equivp_eq: "equivp eq" by simp

lemma eq_append_same1: "eq xs' ys' \<Longrightarrow> eq (xs @ xs') (xs @ ys')"
  by(induction rule: equivclp_induct)(auto intro: cancel1_append_same1 equivclp_into_equivclp)

lemma append_eq_cong: "\<lbrakk>eq xs ys; eq xs' ys'\<rbrakk> \<Longrightarrow> eq (xs @ xs') (ys @ ys')"
  by(induction rule: equivclp_induct)(auto intro: eq_append_same1 equivclp_into_equivclp cancel1_append_same2)


quotient_type 'a fim = "'a list" / eq by simp

instantiation fim :: (type) monoid_add begin
lift_definition zero_fim :: "'a fim" is "[]" .
lift_definition plus_fim :: "'a fim \<Rightarrow> 'a fim \<Rightarrow> 'a fim" is "(@)" by(rule append_eq_cong)
instance by(intro_classes; transfer; simp)
end

lemma plus_idem_fim [simp]: fixes x :: "'a fim" shows "x + x = x"
proof transfer
  fix xs :: "'a list"
  show "eq (xs @ xs) xs"
  proof(cases "xs = []")
    case False thus ?thesis using cancel1_same[of xs] by(auto)
  qed simp
qed


inductive pcancel1 :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  pcancel1: "pcancel1 (concat xss) (concat yss)" if "list_all2 (\<lambda>xs ys. xs = ys \<or> xs = ys @ ys) xss yss"

lemma cancel1_into_pcancel1: "pcancel1 xs ys" if "cancel1 xs ys"
  using that
proof cases
  case (cancel1 xs gs gs')
  let ?xss = "[gs, xs @ xs, gs']" and ?yss = "[gs, xs, gs']"
  have "pcancel1 (concat ?xss) (concat ?yss)" by(rule pcancel1.intros) simp
  then show ?thesis using cancel1 by simp
qed

lemma pcancel_into_cancel: "cancel1\<^sup>*\<^sup>* xs ys" if "pcancel1 xs ys"
  using that
proof cases
  case (pcancel1 xss yss)
  from pcancel1(3) show ?thesis unfolding pcancel1(1-2)
    apply induction
     apply simp
    apply(auto intro: cancel_append_same1)
    apply(rule rtranclp_trans)
    apply(subst append_assoc[symmetric])
     apply(rule cancel_append_same2)
     apply(rule cancel_same)
    apply(auto intro: cancel_append_same1)
    done
qed

lemma pcancel1_cancel1_confluent:
  assumes "pcancel1 xs ys"
    and "cancel1 zs ys"
  shows "\<exists>us. cancel us xs \<and> pcancel1 us zs"
proof -
  let ?P = "\<lambda>xs ys. xs = ys \<or> xs = ys @ ys"
  consider ass as2 bs1 bss bs2 cs1 css ass' as2bs1 bss' bs2cs1 css'
    where "ys = concat ass @ as2 @ bs1 @ concat bss @ bs2 @ cs1 @ concat css"
     and "xs = concat ass' @ as2bs1 @ concat bss' @ bs2cs1 @ concat css'"
     and "zs = concat ass @ as2 @ bs1 @ concat bss @ bs2 @ bs1 @ concat bss @ bs2 @ cs1 @ concat css"
     and "list_all2 ?P ass' ass"
     and "list_all2 ?P bss' bss"
     and "list_all2 ?P css' css"
     and "?P as2bs1 (as2 @ bs1)"
     and "?P bs2cs1 (bs2 @ cs1)"
   | ass as2 bs cs1 css ass' css'
   where "ys = concat ass @ as2 @ bs @ cs1 @ concat css"
     and "xs = concat ass' @ as2 @ bs @ cs1 @ as2 @ bs @ cs1 @ concat css'"
     and "zs = concat ass @ as2 @ bs @ bs @ cs1 @ concat css"
     and "list_all2 ?P ass' ass"
     and "list_all2 ?P css' css"
  proof -
    from assms obtain xss bs as cs yss
      where xs: "xs = concat xss" and zs: "zs = as @ bs @ bs @ cs"
      and xss: "list_all2 (\<lambda>xs ys. xs = ys \<or> xs = ys @ ys) xss yss"
      and ys: "ys = as @ bs @ cs"
      and yss: "concat yss = as @ bs @ cs"
      and bs: "bs \<noteq> []"
      by(clarsimp simp add: pcancel1.simps cancel1.simps)
    from yss bs obtain ass as2 BS bcss
      where yss: "yss = ass @ (as2 @ BS) # bcss"
       and as: "as = concat ass @ as2"
       and eq: "bs @ cs = BS @ concat bcss"
      by(auto simp add: concat_eq_append_conv split: if_split_asm)
    define bcss' where "bcss' = (if bcss = [] then [[]] else bcss)"
    have bcss': "bcss' \<noteq> []" by(simp add: bcss'_def)
    from eq consider us where "bs = BS @ us" "concat bcss = us @ cs" "bcss \<noteq> []" |
      "BS = bs @ cs" "bcss = []" |
      us where "BS = bs @ us" "cs = us @ concat bcss"
      by(cases "bcss = []")(auto simp add: append_eq_append_conv2)
    then show thesis
    proof cases
      case 1
      from 1(2,3) obtain bss bs2 cs1 css
        where "bcss = bss @ (bs2 @ cs1) # css"
          and us: "us = concat bss @ bs2"
          and cs: "cs = cs1 @ concat css" by(auto simp add: concat_eq_append_conv)
      with 1 xs xss ys yss zs as that(1)[of ass as2 BS bss bs2 cs1 css] show ?thesis
        by(clarsimp simp add: list_all2_append2 list_all2_Cons2)
    next
      case 2
      with xs xss ys yss zs as show ?thesis
        using that(1)[of ass as2 bs "[]" "[]" "[]" "[cs]" _ "as2 @ bs" "[]" "[]" "[cs]"]
        using that(2)[of ass as2 bs cs "[]"]
        by(auto simp add: list_all2_append2 list_all2_Cons2)
    next
      case 3
      with xs xss ys yss zs as show ?thesis
        using that(1)[of ass as2 "[]" "[bs]" "[]" "us" "bcss" _ "as2" "[bs]"] that(2)[of ass as2 bs us bcss]
        by(auto simp add: list_all2_append2 list_all2_Cons2)
    qed
  qed
  then show ?thesis
  proof cases
    case 1
    let ?us = "concat ass' @ as2bs1 @ concat bss' @ bs2 @ bs1 @ concat bss' @ bs2cs1 @ concat css'"
    have "?us = concat (ass' @ [as2bs1] @ bss' @ [bs2 @ bs1] @ bss' @ [bs2cs1] @ css')" by simp
    also have "pcancel1 \<dots> (concat (ass @ [as2 @ bs1] @ bss @ [bs2 @ bs1] @ bss @ [bs2 @ cs1] @ css))"
      by(rule pcancel1.intros)(use 1 in \<open>simp add: list_all2_appendI\<close>)
    also have "\<dots> = zs" using 1 by simp
    also have "cancel ?us xs"
    proof -
      define as2b where "as2b = (if as2bs1 = as2 @ bs1 then as2 else as2 @ bs1 @ as2)"
      have as2bs1: "as2bs1 = as2b @ bs1" using 1 by(auto simp add: as2b_def)
      define b2cs where "b2cs = (if bs2cs1 = bs2 @ cs1 then cs1 else cs1 @ bs2 @ cs1)"
      have bs2cs1: "bs2cs1 = bs2 @ b2cs" using 1 by(auto simp add: b2cs_def)
      have "?us = (concat ass' @ as2b) @ ((bs1 @ concat bss' @ bs2) @ (bs1 @ concat bss' @ bs2)) @ b2cs @ concat css'"
        by(simp add: as2bs1 bs2cs1)
      also have "cancel \<dots> ((concat ass' @ as2b) @ (bs1 @ concat bss' @ bs2) @ b2cs @ concat css')"
        by(rule cancel_append_same1 cancel_append_same2 cancel_same)+
      also have "\<dots> = xs" using 1 bs2cs1 as2bs1 by simp
      finally show ?thesis .
    qed
    ultimately show ?thesis by blast
  next
    case 2
    let ?us = "concat ass' @ as2 @ bs @ bs @ cs1 @ as2 @ bs @ bs @ cs1 @ concat css'"
    have "?us = concat (ass' @ [as2 @ bs @ bs @ cs1 @ as2 @ bs @ bs @ cs1] @ css')" by simp
    also have "pcancel1 \<dots> (concat (ass @ [as2 @ bs @ bs @ cs1] @ css))"
      by(intro pcancel1.intros list_all2_appendI)(simp_all add: 2)
    also have "\<dots> = zs" using 2 by simp
    also have "cancel ?us xs"
    proof -
      have "?us = (concat ass' @ as2) @ (bs @ bs) @ cs1 @ as2 @ bs @ bs @ cs1 @ concat css'" by simp
      also have "cancel \<dots> ((concat ass' @ as2) @ bs @ cs1 @ as2 @ bs @ bs @ cs1 @ concat css')"
        by(rule cancel_append_same1 cancel_append_same2 cancel_same)+
      also have "\<dots> = (concat ass' @ as2 @ bs @ cs1 @ as2) @ (bs @ bs) @ cs1 @ concat css'" by simp
      also have "cancel \<dots> ((concat ass' @ as2 @ bs @ cs1 @ as2) @ bs @ cs1 @ concat css')"
        by(rule cancel_append_same1 cancel_append_same2 cancel_same)+
      also have "\<dots> = xs" using 2 by simp
      finally show ?thesis .
    qed
    ultimately show ?thesis by blast
  qed
qed

lemma pcancel1_cancel_confluent:
  assumes "pcancel1 xs ys"
    and "cancel zs ys"
  shows "\<exists>us. cancel us xs \<and> pcancel1 us zs"
  using assms(2,1)
  by(induction arbitrary: xs)(fastforce elim!: rtranclp_trans dest: pcancel1_cancel1_confluent)+

lemma cancel1_semiconfluent:
  assumes "cancel1 xs ys"
    and "cancel zs ys"
  shows "\<exists>us. cancel us xs \<and> cancel us zs"
  using pcancel1_cancel_confluent[OF cancel1_into_pcancel1, OF assms]
  by(blast intro: pcancel_into_cancel)

lemma semiconfluentp_cancel1: "semiconfluentp cancel1\<inverse>\<inverse>"
  by(auto simp add: semiconfluentp_def rtranclp_conversep dest: cancel1_semiconfluent)

lemma retract_cancel1_aux:
  assumes "cancel1 ys (map f xs)"
  shows "\<exists>zs. cancel1 zs xs \<and> ys = map f zs \<and> set zs \<subseteq> set xs"
  using assms
  by cases(fastforce simp add: map_eq_append_conv append_eq_map_conv intro: cancel1.intros)

lemma retract_cancel1:
  assumes "cancel1 ys (map f xs)"
  shows "\<exists>zs. eq xs zs \<and> ys = map f zs \<and> set zs \<subseteq> set xs"
  using retract_cancel1_aux[OF assms] by(blast intro: symclpI)

lemma cancel1_set_eq:
  assumes "cancel1 ys xs"
  shows "set ys = set xs"
  using assms by cases auto

lemma eq_set_eq: "set xs = set ys" if "eq xs ys"
  using that by(induction)(auto dest!: cancel1_set_eq elim!: symclpE)

context includes lifting_syntax begin
lemma map_respect_cancel1: "((=) ===> cancel1 ===> eq) map map"
  by(auto 4 4 simp add: rel_fun_def cancel1.simps intro: symclpI cancel1.intros)

lemma map_respect_eq: "((=) ===> eq ===> eq) map map"
  apply(intro rel_funI; hypsubst)
  subgoal for _ f x y
    by(induction rule: equivclp_induct)
      (auto dest: map_respect_cancel1[THEN rel_funD, THEN rel_funD, OF refl] intro: eq_sym equivclp_trans)
  done
end

lemma confluent_quotient_fim:
  "confluent_quotient cancel1\<inverse>\<inverse> eq eq eq eq eq (map fst) (map snd) (map fst) (map snd) list_all2 list_all2 list_all2 set set"
  by(unfold_locales)(auto dest: retract_cancel1 eq_set_eq simp add: list.in_rel list.rel_compp map_respect_eq[THEN rel_funD, OF refl] semiconfluentp_imp_confluentp semiconfluentp_cancel1)+

lift_bnf 'a fim
  subgoal for A B by(rule confluent_quotient.subdistributivity[OF confluent_quotient_fim])
  subgoal by(force dest: eq_set_eq)
  done

end
