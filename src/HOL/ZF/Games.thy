(*  Title:      HOL/ZF/Games.thy
    Author:     Steven Obua

An application of HOLZF: Partizan Games.  See "Partizan Games in
Isabelle/HOLZF", available from http://www4.in.tum.de/~obua/partizan
*)

theory Games 
imports MainZF
begin

definition fixgames :: "ZF set \<Rightarrow> ZF set" where
  "fixgames A \<equiv> { Opair l r | l r. explode l \<subseteq> A & explode r \<subseteq> A}"

definition games_lfp :: "ZF set" where
  "games_lfp \<equiv> lfp fixgames"

definition games_gfp :: "ZF set" where
  "games_gfp \<equiv> gfp fixgames"

lemma mono_fixgames: "mono (fixgames)"
  apply (auto simp add: mono_def fixgames_def)
  apply (rule_tac x=l in exI)
  apply (rule_tac x=r in exI)
  apply auto
  done

lemma games_lfp_unfold: "games_lfp = fixgames games_lfp"
  by (auto simp add: def_lfp_unfold games_lfp_def mono_fixgames)

lemma games_gfp_unfold: "games_gfp = fixgames games_gfp"
  by (auto simp add: def_gfp_unfold games_gfp_def mono_fixgames)

lemma games_lfp_nonempty: "Opair Empty Empty \<in> games_lfp"
proof -
  have "fixgames {} \<subseteq> games_lfp" 
    apply (subst games_lfp_unfold)
    apply (simp add: mono_fixgames[simplified mono_def, rule_format])
    done
  moreover have "fixgames {} = {Opair Empty Empty}"
    by (simp add: fixgames_def explode_Empty)
  finally show ?thesis
    by auto
qed

definition left_option :: "ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "left_option g opt \<equiv> (Elem opt (Fst g))"

definition right_option :: "ZF \<Rightarrow> ZF \<Rightarrow> bool" where
  "right_option g opt \<equiv> (Elem opt (Snd g))"

definition is_option_of :: "(ZF * ZF) set" where
  "is_option_of \<equiv> { (opt, g) | opt g. g \<in> games_gfp \<and> (left_option g opt \<or> right_option g opt) }"

lemma games_lfp_subset_gfp: "games_lfp \<subseteq> games_gfp"
proof -
  have "games_lfp \<subseteq> fixgames games_lfp" 
    by (simp add: games_lfp_unfold[symmetric])
  then show ?thesis
    by (simp add: games_gfp_def gfp_upperbound)
qed

lemma games_option_stable: 
  assumes fixgames: "games = fixgames games"
  and g: "g \<in> games"
  and opt: "left_option g opt \<or> right_option g opt"
  shows "opt \<in> games"
proof -
  from g fixgames have "g \<in> fixgames games" by auto
  then have "\<exists> l r. g = Opair l r \<and> explode l \<subseteq> games \<and> explode r \<subseteq> games"
    by (simp add: fixgames_def)
  then obtain l where "\<exists> r. g = Opair l r \<and> explode l \<subseteq> games \<and> explode r \<subseteq> games" ..
  then obtain r where lr: "g = Opair l r \<and> explode l \<subseteq> games \<and> explode r \<subseteq> games" ..
  with opt show ?thesis
    by (auto intro: Elem_explode_in simp add: left_option_def right_option_def Fst Snd)
qed
    
lemma option2elem: "(opt,g) \<in> is_option_of  \<Longrightarrow> \<exists> u v. Elem opt u \<and> Elem u v \<and> Elem v g"
  apply (simp add: is_option_of_def)
  apply (subgoal_tac "(g \<in> games_gfp) = (g \<in> (fixgames games_gfp))")
  prefer 2
  apply (simp add: games_gfp_unfold[symmetric])
  apply (auto simp add: fixgames_def left_option_def right_option_def Fst Snd)
  apply (rule_tac x=l in exI, insert Elem_Opair_exists, blast)
  apply (rule_tac x=r in exI, insert Elem_Opair_exists, blast) 
  done

lemma is_option_of_subset_is_Elem_of: "is_option_of \<subseteq> (is_Elem_of^+)"
proof -
  {
    fix opt
    fix g
    assume "(opt, g) \<in> is_option_of"
    then have "\<exists> u v. (opt, u) \<in> (is_Elem_of^+) \<and> (u,v) \<in> (is_Elem_of^+) \<and> (v,g) \<in> (is_Elem_of^+)" 
      apply -
      apply (drule option2elem)
      apply (auto simp add: r_into_trancl' is_Elem_of_def)
      done
    then have "(opt, g) \<in> (is_Elem_of^+)"
      by (blast intro: trancl_into_rtrancl trancl_rtrancl_trancl)
  } 
  then show ?thesis by auto
qed

lemma wfzf_is_option_of: "wfzf is_option_of"
proof - 
  have "wfzf (is_Elem_of^+)" by (simp add: wfzf_trancl wfzf_is_Elem_of)
  then show ?thesis 
    apply (rule wfzf_subset)
    apply (rule is_option_of_subset_is_Elem_of)
    done
  qed
  
lemma games_gfp_imp_lfp: "g \<in> games_gfp \<longrightarrow> g \<in> games_lfp"
proof -
  have unfold_gfp: "\<And> x. x \<in> games_gfp \<Longrightarrow> x \<in> (fixgames games_gfp)" 
    by (simp add: games_gfp_unfold[symmetric])
  have unfold_lfp: "\<And> x. (x \<in> games_lfp) = (x \<in> (fixgames games_lfp))"
    by (simp add: games_lfp_unfold[symmetric])
  show ?thesis
    apply (rule wf_induct[OF wfzf_implies_wf[OF wfzf_is_option_of]])
    apply (auto simp add: is_option_of_def)
    apply (drule_tac unfold_gfp)
    apply (simp add: fixgames_def)
    apply (auto simp add: left_option_def Fst right_option_def Snd)
    apply (subgoal_tac "explode l \<subseteq> games_lfp")
    apply (subgoal_tac "explode r \<subseteq> games_lfp")
    apply (subst unfold_lfp)
    apply (auto simp add: fixgames_def)
    apply (simp_all add: explode_Elem Elem_explode_in)
    done
qed

theorem games_lfp_eq_gfp: "games_lfp = games_gfp"
  apply (auto simp add: games_gfp_imp_lfp)
  apply (insert games_lfp_subset_gfp)
  apply auto
  done

theorem unique_games: "(g = fixgames g) = (g = games_lfp)"
proof -
  {
    fix g 
    assume g: "g = fixgames g"
    from g have "fixgames g \<subseteq> g" by auto
    then have l:"games_lfp \<subseteq> g" 
      by (simp add: games_lfp_def lfp_lowerbound)
    from g have "g \<subseteq> fixgames g" by auto
    then have u:"g \<subseteq> games_gfp" 
      by (simp add: games_gfp_def gfp_upperbound)
    from l u games_lfp_eq_gfp[symmetric] have "g = games_lfp"
      by auto
  }
  note games = this
  show ?thesis
    apply (rule iff[rule_format])
    apply (erule games)
    apply (simp add: games_lfp_unfold[symmetric])
    done
qed

lemma games_lfp_option_stable: 
  assumes g: "g \<in> games_lfp"
  and opt: "left_option g opt \<or> right_option g opt"
  shows "opt \<in> games_lfp"
  apply (rule games_option_stable[where g=g])
  apply (simp add: games_lfp_unfold[symmetric])
  apply (simp_all add: assms)
  done

lemma is_option_of_imp_games:
  assumes hyp: "(opt, g) \<in> is_option_of"
  shows "opt \<in> games_lfp \<and> g \<in> games_lfp"
proof -
  from hyp have g_game: "g \<in> games_lfp" 
    by (simp add: is_option_of_def games_lfp_eq_gfp)
  from hyp have "left_option g opt \<or> right_option g opt"
    by (auto simp add: is_option_of_def)
  with g_game games_lfp_option_stable[OF g_game, OF this] show ?thesis
    by auto
qed
 
lemma games_lfp_represent: "x \<in> games_lfp \<Longrightarrow> \<exists> l r. x = Opair l r"
  apply (rule exI[where x="Fst x"])
  apply (rule exI[where x="Snd x"])
  apply (subgoal_tac "x \<in> (fixgames games_lfp)")
  apply (simp add: fixgames_def)
  apply (auto simp add: Fst Snd)
  apply (simp add: games_lfp_unfold[symmetric])
  done

definition "game = games_lfp"

typedef game = game
  unfolding game_def by (blast intro: games_lfp_nonempty)

definition left_options :: "game \<Rightarrow> game zet" where
  "left_options g \<equiv> zimage Abs_game (zexplode (Fst (Rep_game g)))"

definition right_options :: "game \<Rightarrow> game zet" where
  "right_options g \<equiv> zimage Abs_game (zexplode (Snd (Rep_game g)))"

definition options :: "game \<Rightarrow> game zet" where
  "options g \<equiv> zunion (left_options g) (right_options g)"

definition Game :: "game zet \<Rightarrow> game zet \<Rightarrow> game" where
  "Game L R \<equiv> Abs_game (Opair (zimplode (zimage Rep_game L)) (zimplode (zimage Rep_game R)))"
  
lemma Repl_Rep_game_Abs_game: "\<forall> e. Elem e z \<longrightarrow> e \<in> games_lfp \<Longrightarrow> Repl z (Rep_game o Abs_game) = z"
  apply (subst Ext)
  apply (simp add: Repl)
  apply auto
  apply (subst Abs_game_inverse, simp_all add: game_def)
  apply (rule_tac x=za in exI)
  apply (subst Abs_game_inverse, simp_all add: game_def)
  done

lemma game_split: "g = Game (left_options g) (right_options g)"
proof -
  have "\<exists> l r. Rep_game g = Opair l r"
    apply (insert Rep_game[of g])
    apply (simp add: game_def games_lfp_represent)
    done
  then obtain l r where lr: "Rep_game g = Opair l r" by auto
  have partizan_g: "Rep_game g \<in> games_lfp" 
    apply (insert Rep_game[of g])
    apply (simp add: game_def)
    done
  have "\<forall> e. Elem e l \<longrightarrow> left_option (Rep_game g) e"
    by (simp add: lr left_option_def Fst)
  then have partizan_l: "\<forall> e. Elem e l \<longrightarrow> e \<in> games_lfp"
    apply auto
    apply (rule games_lfp_option_stable[where g="Rep_game g", OF partizan_g])
    apply auto
    done
  have "\<forall> e. Elem e r \<longrightarrow> right_option (Rep_game g) e"
    by (simp add: lr right_option_def Snd)
  then have partizan_r: "\<forall> e. Elem e r \<longrightarrow> e \<in> games_lfp"
    apply auto
    apply (rule games_lfp_option_stable[where g="Rep_game g", OF partizan_g])
    apply auto
    done   
  let ?L = "zimage (Abs_game) (zexplode l)"
  let ?R = "zimage (Abs_game) (zexplode r)"
  have L:"?L = left_options g"
    by (simp add: left_options_def lr Fst)
  have R:"?R = right_options g"
    by (simp add: right_options_def lr Snd)
  have "g = Game ?L ?R"
    apply (simp add: Game_def Rep_game_inject[symmetric] comp_zimage_eq zimage_zexplode_eq zimplode_zexplode)
    apply (simp add: Repl_Rep_game_Abs_game partizan_l partizan_r)
    apply (subst Abs_game_inverse)
    apply (simp_all add: lr[symmetric] Rep_game) 
    done
  then show ?thesis
    by (simp add: L R)
qed

lemma Opair_in_games_lfp: 
  assumes l: "explode l \<subseteq> games_lfp"
  and r: "explode r \<subseteq> games_lfp"
  shows "Opair l r \<in> games_lfp"
proof -
  note f = unique_games[of games_lfp, simplified]
  show ?thesis
    apply (subst f)
    apply (simp add: fixgames_def)
    apply (rule exI[where x=l])
    apply (rule exI[where x=r])
    apply (auto simp add: l r)
    done
qed

lemma left_options[simp]: "left_options (Game l r) = l"
  apply (simp add: left_options_def Game_def)
  apply (subst Abs_game_inverse)
  apply (simp add: game_def)
  apply (rule Opair_in_games_lfp)
  apply (auto simp add: explode_Elem Elem_zimplode zimage_iff Rep_game[simplified game_def])
  apply (simp add: Fst zexplode_zimplode comp_zimage_eq)
  apply (simp add: zet_ext_eq zimage_iff Rep_game_inverse)
  done

lemma right_options[simp]: "right_options (Game l r) = r"
  apply (simp add: right_options_def Game_def)
  apply (subst Abs_game_inverse)
  apply (simp add: game_def)
  apply (rule Opair_in_games_lfp)
  apply (auto simp add: explode_Elem Elem_zimplode zimage_iff Rep_game[simplified game_def])
  apply (simp add: Snd zexplode_zimplode comp_zimage_eq)
  apply (simp add: zet_ext_eq zimage_iff Rep_game_inverse)
  done  

lemma Game_ext: "(Game l1 r1 = Game l2 r2) = ((l1 = l2) \<and> (r1 = r2))"
  apply auto
  apply (subst left_options[where l=l1 and r=r1,symmetric])
  apply (subst left_options[where l=l2 and r=r2,symmetric])
  apply simp
  apply (subst right_options[where l=l1 and r=r1,symmetric])
  apply (subst right_options[where l=l2 and r=r2,symmetric])
  apply simp
  done

definition option_of :: "(game * game) set" where
  "option_of \<equiv> image (\<lambda> (option, g). (Abs_game option, Abs_game g)) is_option_of"

lemma option_to_is_option_of: "((option, g) \<in> option_of) = ((Rep_game option, Rep_game g) \<in> is_option_of)"
  apply (auto simp add: option_of_def)
  apply (subst Abs_game_inverse)
  apply (simp add: is_option_of_imp_games game_def)
  apply (subst Abs_game_inverse)
  apply (simp add: is_option_of_imp_games game_def)
  apply simp
  apply (auto simp add: Bex_def image_def)  
  apply (rule exI[where x="Rep_game option"])
  apply (rule exI[where x="Rep_game g"])
  apply (simp add: Rep_game_inverse)
  done
  
lemma wf_is_option_of: "wf is_option_of"
  apply (rule wfzf_implies_wf)
  apply (simp add: wfzf_is_option_of)
  done

lemma wf_option_of[simp, intro]: "wf option_of"
proof -
  have option_of: "option_of = inv_image is_option_of Rep_game"
    apply (rule set_eqI)
    apply (case_tac "x")
    by (simp add: option_to_is_option_of) 
  show ?thesis
    apply (simp add: option_of)
    apply (auto intro: wf_is_option_of)
    done
qed
  
lemma right_option_is_option[simp, intro]: "zin x (right_options g) \<Longrightarrow> zin x (options g)"
  by (simp add: options_def zunion)

lemma left_option_is_option[simp, intro]: "zin x (left_options g) \<Longrightarrow> zin x (options g)"
  by (simp add: options_def zunion)

lemma zin_options[simp, intro]: "zin x (options g) \<Longrightarrow> (x, g) \<in> option_of"
  apply (simp add: options_def zunion left_options_def right_options_def option_of_def 
    image_def is_option_of_def zimage_iff zin_zexplode_eq) 
  apply (cases g)
  apply (cases x)
  apply (auto simp add: Abs_game_inverse games_lfp_eq_gfp[symmetric] game_def 
    right_option_def[symmetric] left_option_def[symmetric])
  done

function
  neg_game :: "game \<Rightarrow> game"
where
  [simp del]: "neg_game g = Game (zimage neg_game (right_options g)) (zimage neg_game (left_options g))"
by auto
termination by (relation "option_of") auto

lemma "neg_game (neg_game g) = g"
  apply (induct g rule: neg_game.induct)
  apply (subst neg_game.simps)+
  apply (simp add: comp_zimage_eq)
  apply (subgoal_tac "zimage (neg_game o neg_game) (left_options g) = left_options g")
  apply (subgoal_tac "zimage (neg_game o neg_game) (right_options g) = right_options g")
  apply (auto simp add: game_split[symmetric])
  apply (auto simp add: zet_ext_eq zimage_iff)
  done

function
  ge_game :: "(game * game) \<Rightarrow> bool" 
where
  [simp del]: "ge_game (G, H) = (\<forall> x. if zin x (right_options G) then (
                          if zin x (left_options H) then \<not> (ge_game (H, x) \<or> (ge_game (x, G))) 
                                                    else \<not> (ge_game (H, x)))
                          else (if zin x (left_options H) then \<not> (ge_game (x, G)) else True))"
by auto
termination by (relation "(gprod_2_1 option_of)") 
 (simp, auto simp: gprod_2_1_def)

lemma ge_game_eq: "ge_game (G, H) = (\<forall> x. (zin x (right_options G) \<longrightarrow> \<not> ge_game (H, x)) \<and> (zin x (left_options H) \<longrightarrow> \<not> ge_game (x, G)))"
  apply (subst ge_game.simps[where G=G and H=H])
  apply (auto)
  done

lemma ge_game_leftright_refl[rule_format]: 
  "\<forall> y. (zin y (right_options x) \<longrightarrow> \<not> ge_game (x, y)) \<and> (zin y (left_options x) \<longrightarrow> \<not> (ge_game (y, x))) \<and> ge_game (x, x)"
proof (induct x rule: wf_induct[OF wf_option_of]) 
  case (1 "g")
  { 
    fix y
    assume y: "zin y (right_options g)"
    have "\<not> ge_game (g, y)"
    proof -
      have "(y, g) \<in> option_of" by (auto intro: y)
      with 1 have "ge_game (y, y)" by auto
      with y show ?thesis by (subst ge_game_eq, auto)
    qed
  }
  note right = this
  { 
    fix y
    assume y: "zin y (left_options g)"
    have "\<not> ge_game (y, g)"
    proof -
      have "(y, g) \<in> option_of" by (auto intro: y)
      with 1 have "ge_game (y, y)" by auto
      with y show ?thesis by (subst ge_game_eq, auto)
    qed
  } 
  note left = this
  from left right show ?case
    by (auto, subst ge_game_eq, auto)
qed

lemma ge_game_refl: "ge_game (x,x)" by (simp add: ge_game_leftright_refl)

lemma "\<forall> y. (zin y (right_options x) \<longrightarrow> \<not> ge_game (x, y)) \<and> (zin y (left_options x) \<longrightarrow> \<not> (ge_game (y, x))) \<and> ge_game (x, x)"
proof (induct x rule: wf_induct[OF wf_option_of]) 
  case (1 "g")  
  show ?case
  proof (auto)
    {case (goal1 y) 
      from goal1 have "(y, g) \<in> option_of" by (auto)
      with 1 have "ge_game (y, y)" by auto
      with goal1 have "\<not> ge_game (g, y)" 
        by (subst ge_game_eq, auto)
      with goal1 show ?case by auto}
    note right = this
    {case (goal2 y)
      from goal2 have "(y, g) \<in> option_of" by (auto)
      with 1 have "ge_game (y, y)" by auto
      with goal2 have "\<not> ge_game (y, g)" 
        by (subst ge_game_eq, auto)
      with goal2 show ?case by auto}
    note left = this
    {case goal3
      from left right show ?case
        by (subst ge_game_eq, auto)
    }
  qed
qed
        
definition eq_game :: "game \<Rightarrow> game \<Rightarrow> bool" where
  "eq_game G H \<equiv> ge_game (G, H) \<and> ge_game (H, G)" 

lemma eq_game_sym: "(eq_game G H) = (eq_game H G)"
  by (auto simp add: eq_game_def)

lemma eq_game_refl: "eq_game G G"
  by (simp add: ge_game_refl eq_game_def)

lemma induct_game: "(\<And>x. \<forall>y. (y, x) \<in> lprod option_of \<longrightarrow> P y \<Longrightarrow> P x) \<Longrightarrow> P a"
  by (erule wf_induct[OF wf_lprod[OF wf_option_of]])

lemma ge_game_trans:
  assumes "ge_game (x, y)" "ge_game (y, z)" 
  shows "ge_game (x, z)"
proof -  
  { 
    fix a
    have "\<forall> x y z. a = [x,y,z] \<longrightarrow> ge_game (x,y) \<longrightarrow> ge_game (y,z) \<longrightarrow> ge_game (x, z)"
    proof (induct a rule: induct_game)
      case (1 a)
      show ?case
      proof (rule allI | rule impI)+
        case (goal1 x y z)
        show ?case
        proof -
          { fix xr
            assume xr:"zin xr (right_options x)"
            assume a: "ge_game (z, xr)"
            have "ge_game (y, xr)"
              apply (rule 1[rule_format, where y="[y,z,xr]"])
              apply (auto intro: xr lprod_3_1 simp add: goal1 a)
              done
            moreover from xr have "\<not> ge_game (y, xr)"
              by (simp add: goal1(2)[simplified ge_game_eq[of x y], rule_format, of xr, simplified xr])
            ultimately have "False" by auto      
          }
          note xr = this
          { fix zl
            assume zl:"zin zl (left_options z)"
            assume a: "ge_game (zl, x)"
            have "ge_game (zl, y)"
              apply (rule 1[rule_format, where y="[zl,x,y]"])
              apply (auto intro: zl lprod_3_2 simp add: goal1 a)
              done
            moreover from zl have "\<not> ge_game (zl, y)"
              by (simp add: goal1(3)[simplified ge_game_eq[of y z], rule_format, of zl, simplified zl])
            ultimately have "False" by auto
          }
          note zl = this
          show ?thesis
            by (auto simp add: ge_game_eq[of x z] intro: xr zl)
        qed
      qed
    qed
  } 
  note trans = this[of "[x, y, z]", simplified, rule_format]    
  with assms show ?thesis by blast
qed

lemma eq_game_trans: "eq_game a b \<Longrightarrow> eq_game b c \<Longrightarrow> eq_game a c"
  by (auto simp add: eq_game_def intro: ge_game_trans)

definition zero_game :: game
 where  "zero_game \<equiv> Game zempty zempty"

function 
  plus_game :: "game \<Rightarrow> game \<Rightarrow> game"
where
  [simp del]: "plus_game G H = Game (zunion (zimage (\<lambda> g. plus_game g H) (left_options G))
                                   (zimage (\<lambda> h. plus_game G h) (left_options H)))
                           (zunion (zimage (\<lambda> g. plus_game g H) (right_options G))
                                   (zimage (\<lambda> h. plus_game G h) (right_options H)))"
by auto
termination by (relation "gprod_2_2 option_of")
  (simp, auto simp: gprod_2_2_def)

lemma plus_game_comm: "plus_game G H = plus_game H G"
proof (induct G H rule: plus_game.induct)
  case (1 G H)
  show ?case
    by (auto simp add: 
      plus_game.simps[where G=G and H=H] 
      plus_game.simps[where G=H and H=G]
      Game_ext zet_ext_eq zunion zimage_iff 1)
qed

lemma game_ext_eq: "(G = H) = (left_options G = left_options H \<and> right_options G = right_options H)"
proof -
  have "(G = H) = (Game (left_options G) (right_options G) = Game (left_options H) (right_options H))"
    by (simp add: game_split[symmetric])
  then show ?thesis by auto
qed

lemma left_zero_game[simp]: "left_options (zero_game) = zempty"
  by (simp add: zero_game_def)

lemma right_zero_game[simp]: "right_options (zero_game) = zempty"
  by (simp add: zero_game_def)

lemma plus_game_zero_right[simp]: "plus_game G zero_game = G"
proof -
  { 
    fix G H
    have "H = zero_game \<longrightarrow> plus_game G H = G "
    proof (induct G H rule: plus_game.induct, rule impI)
      case (goal1 G H)
      note induct_hyp = this[simplified goal1, simplified] and this
      show ?case
        apply (simp only: plus_game.simps[where G=G and H=H])
        apply (simp add: game_ext_eq goal1)
        apply (auto simp add: 
          zimage_cong [where f = "\<lambda> g. plus_game g zero_game" and g = "id"] 
          induct_hyp)
        done
    qed
  }
  then show ?thesis by auto
qed

lemma plus_game_zero_left: "plus_game zero_game G = G"
  by (simp add: plus_game_comm)

lemma left_imp_options[simp]: "zin opt (left_options g) \<Longrightarrow> zin opt (options g)"
  by (simp add: options_def zunion)

lemma right_imp_options[simp]: "zin opt (right_options g) \<Longrightarrow> zin opt (options g)"
  by (simp add: options_def zunion)

lemma left_options_plus: 
  "left_options (plus_game u v) =  zunion (zimage (\<lambda>g. plus_game g v) (left_options u)) (zimage (\<lambda>h. plus_game u h) (left_options v))" 
  by (subst plus_game.simps, simp)

lemma right_options_plus:
  "right_options (plus_game u v) =  zunion (zimage (\<lambda>g. plus_game g v) (right_options u)) (zimage (\<lambda>h. plus_game u h) (right_options v))"
  by (subst plus_game.simps, simp)

lemma left_options_neg: "left_options (neg_game u) = zimage neg_game (right_options u)"  
  by (subst neg_game.simps, simp)

lemma right_options_neg: "right_options (neg_game u) = zimage neg_game (left_options u)"
  by (subst neg_game.simps, simp)
  
lemma plus_game_assoc: "plus_game (plus_game F G) H = plus_game F (plus_game G H)"
proof -
  { 
    fix a
    have "\<forall> F G H. a = [F, G, H] \<longrightarrow> plus_game (plus_game F G) H = plus_game F (plus_game G H)"
    proof (induct a rule: induct_game, (rule impI | rule allI)+)
      case (goal1 x F G H)
      let ?L = "plus_game (plus_game F G) H"
      let ?R = "plus_game F (plus_game G H)"
      note options_plus = left_options_plus right_options_plus
      {
        fix opt
        note hyp = goal1(1)[simplified goal1(2), rule_format] 
        have F: "zin opt (options F)  \<Longrightarrow> plus_game (plus_game opt G) H = plus_game opt (plus_game G H)"
          by (blast intro: hyp lprod_3_3)
        have G: "zin opt (options G) \<Longrightarrow> plus_game (plus_game F opt) H = plus_game F (plus_game opt H)"
          by (blast intro: hyp lprod_3_4)
        have H: "zin opt (options H) \<Longrightarrow> plus_game (plus_game F G) opt = plus_game F (plus_game G opt)" 
          by (blast intro: hyp lprod_3_5)
        note F and G and H
      }
      note induct_hyp = this
      have "left_options ?L = left_options ?R \<and> right_options ?L = right_options ?R"
        by (auto simp add: 
          plus_game.simps[where G="plus_game F G" and H=H]
          plus_game.simps[where G="F" and H="plus_game G H"] 
          zet_ext_eq zunion zimage_iff options_plus
          induct_hyp left_imp_options right_imp_options)
      then show ?case
        by (simp add: game_ext_eq)
    qed
  }
  then show ?thesis by auto
qed

lemma neg_plus_game: "neg_game (plus_game G H) = plus_game (neg_game G) (neg_game H)"
proof (induct G H rule: plus_game.induct)
  case (1 G H)
  note opt_ops = 
    left_options_plus right_options_plus 
    left_options_neg right_options_neg  
  show ?case
    by (auto simp add: opt_ops
      neg_game.simps[of "plus_game G H"]
      plus_game.simps[of "neg_game G" "neg_game H"]
      Game_ext zet_ext_eq zunion zimage_iff 1)
qed

lemma eq_game_plus_inverse: "eq_game (plus_game x (neg_game x)) zero_game"
proof (induct x rule: wf_induct[OF wf_option_of])
  case (goal1 x)
  { fix y
    assume "zin y (options x)"
    then have "eq_game (plus_game y (neg_game y)) zero_game"
      by (auto simp add: goal1)
  }
  note ihyp = this
  {
    fix y
    assume y: "zin y (right_options x)"
    have "\<not> (ge_game (zero_game, plus_game y (neg_game x)))"
      apply (subst ge_game.simps, simp)
      apply (rule exI[where x="plus_game y (neg_game y)"])
      apply (auto simp add: ihyp[of y, simplified y right_imp_options eq_game_def])
      apply (auto simp add: left_options_plus left_options_neg zunion zimage_iff intro: y)
      done
  }
  note case1 = this
  {
    fix y
    assume y: "zin y (left_options x)"
    have "\<not> (ge_game (zero_game, plus_game x (neg_game y)))"
      apply (subst ge_game.simps, simp)
      apply (rule exI[where x="plus_game y (neg_game y)"])
      apply (auto simp add: ihyp[of y, simplified y left_imp_options eq_game_def])
      apply (auto simp add: left_options_plus zunion zimage_iff intro: y)
      done
  }
  note case2 = this
  {
    fix y
    assume y: "zin y (left_options x)"
    have "\<not> (ge_game (plus_game y (neg_game x), zero_game))"
      apply (subst ge_game.simps, simp)
      apply (rule exI[where x="plus_game y (neg_game y)"])
      apply (auto simp add: ihyp[of y, simplified y left_imp_options eq_game_def])
      apply (auto simp add: right_options_plus right_options_neg zunion zimage_iff intro: y)
      done
  }
  note case3 = this
  {
    fix y
    assume y: "zin y (right_options x)"
    have "\<not> (ge_game (plus_game x (neg_game y), zero_game))"
      apply (subst ge_game.simps, simp)
      apply (rule exI[where x="plus_game y (neg_game y)"])
      apply (auto simp add: ihyp[of y, simplified y right_imp_options eq_game_def])
      apply (auto simp add: right_options_plus zunion zimage_iff intro: y)
      done
  }
  note case4 = this
  show ?case
    apply (simp add: eq_game_def)
    apply (simp add: ge_game.simps[of "plus_game x (neg_game x)" "zero_game"])
    apply (simp add: ge_game.simps[of "zero_game" "plus_game x (neg_game x)"])
    apply (simp add: right_options_plus left_options_plus right_options_neg left_options_neg zunion zimage_iff)
    apply (auto simp add: case1 case2 case3 case4)
    done
qed

lemma ge_plus_game_left: "ge_game (y,z) = ge_game (plus_game x y, plus_game x z)"
proof -
  { fix a
    have "\<forall> x y z. a = [x,y,z] \<longrightarrow> ge_game (y,z) = ge_game (plus_game x y, plus_game x z)"
    proof (induct a rule: induct_game, (rule impI | rule allI)+)
      case (goal1 a x y z)
      note induct_hyp = goal1(1)[rule_format, simplified goal1(2)]
      { 
        assume hyp: "ge_game(plus_game x y, plus_game x z)"
        have "ge_game (y, z)"
        proof -
          { fix yr
            assume yr: "zin yr (right_options y)"
            from hyp have "\<not> (ge_game (plus_game x z, plus_game x yr))"
              by (auto simp add: ge_game_eq[of "plus_game x y" "plus_game x z"]
                right_options_plus zunion zimage_iff intro: yr)
            then have "\<not> (ge_game (z, yr))"
              apply (subst induct_hyp[where y="[x, z, yr]", of "x" "z" "yr"])
              apply (simp_all add: yr lprod_3_6)
              done
          }
          note yr = this
          { fix zl
            assume zl: "zin zl (left_options z)"
            from hyp have "\<not> (ge_game (plus_game x zl, plus_game x y))"
              by (auto simp add: ge_game_eq[of "plus_game x y" "plus_game x z"]
                left_options_plus zunion zimage_iff intro: zl)
            then have "\<not> (ge_game (zl, y))"
              apply (subst goal1(1)[rule_format, where y="[x, zl, y]", of "x" "zl" "y"])
              apply (simp_all add: goal1(2) zl lprod_3_7)
              done
          }     
          note zl = this
          show "ge_game (y, z)"
            apply (subst ge_game_eq)
            apply (auto simp add: yr zl)
            done
        qed      
      }
      note right_imp_left = this
      {
        assume yz: "ge_game (y, z)"
        {
          fix x'
          assume x': "zin x' (right_options x)"
          assume hyp: "ge_game (plus_game x z, plus_game x' y)"
          then have n: "\<not> (ge_game (plus_game x' y, plus_game x' z))"
            by (auto simp add: ge_game_eq[of "plus_game x z" "plus_game x' y"] 
              right_options_plus zunion zimage_iff intro: x')
          have t: "ge_game (plus_game x' y, plus_game x' z)"
            apply (subst induct_hyp[symmetric])
            apply (auto intro: lprod_3_3 x' yz)
            done
          from n t have "False" by blast
        }    
        note case1 = this
        {
          fix x'
          assume x': "zin x' (left_options x)"
          assume hyp: "ge_game (plus_game x' z, plus_game x y)"
          then have n: "\<not> (ge_game (plus_game x' y, plus_game x' z))"
            by (auto simp add: ge_game_eq[of "plus_game x' z" "plus_game x y"] 
              left_options_plus zunion zimage_iff intro: x')
          have t: "ge_game (plus_game x' y, plus_game x' z)"
            apply (subst induct_hyp[symmetric])
            apply (auto intro: lprod_3_3 x' yz)
            done
          from n t have "False" by blast
        }
        note case3 = this
        {
          fix y'
          assume y': "zin y' (right_options y)"
          assume hyp: "ge_game (plus_game x z, plus_game x y')"
          then have "ge_game(z, y')"
            apply (subst induct_hyp[of "[x, z, y']" "x" "z" "y'"])
            apply (auto simp add: hyp lprod_3_6 y')
            done
          with yz have "ge_game (y, y')"
            by (blast intro: ge_game_trans)      
          with y' have "False" by (auto simp add: ge_game_leftright_refl)
        }
        note case2 = this
        {
          fix z'
          assume z': "zin z' (left_options z)"
          assume hyp: "ge_game (plus_game x z', plus_game x y)"
          then have "ge_game(z', y)"
            apply (subst induct_hyp[of "[x, z', y]" "x" "z'" "y"])
            apply (auto simp add: hyp lprod_3_7 z')
            done    
          with yz have "ge_game (z', z)"
            by (blast intro: ge_game_trans)      
          with z' have "False" by (auto simp add: ge_game_leftright_refl)
        }
        note case4 = this   
        have "ge_game(plus_game x y, plus_game x z)"
          apply (subst ge_game_eq)
          apply (auto simp add: right_options_plus left_options_plus zunion zimage_iff)
          apply (auto intro: case1 case2 case3 case4)
          done
      }
      note left_imp_right = this
      show ?case by (auto intro: right_imp_left left_imp_right)
    qed
  }
  note a = this[of "[x, y, z]"]
  then show ?thesis by blast
qed

lemma ge_plus_game_right: "ge_game (y,z) = ge_game(plus_game y x, plus_game z x)"
  by (simp add: ge_plus_game_left plus_game_comm)

lemma ge_neg_game: "ge_game (neg_game x, neg_game y) = ge_game (y, x)"
proof -
  { fix a
    have "\<forall> x y. a = [x, y] \<longrightarrow> ge_game (neg_game x, neg_game y) = ge_game (y, x)"
    proof (induct a rule: induct_game, (rule impI | rule allI)+)
      case (goal1 a x y)
      note ihyp = goal1(1)[rule_format, simplified goal1(2)]
      { fix xl
        assume xl: "zin xl (left_options x)"
        have "ge_game (neg_game y, neg_game xl) = ge_game (xl, y)"
          apply (subst ihyp)
          apply (auto simp add: lprod_2_1 xl)
          done
      }
      note xl = this
      { fix yr
        assume yr: "zin yr (right_options y)"
        have "ge_game (neg_game yr, neg_game x) = ge_game (x, yr)"
          apply (subst ihyp)
          apply (auto simp add: lprod_2_2 yr)
          done
      }
      note yr = this
      show ?case
        by (auto simp add: ge_game_eq[of "neg_game x" "neg_game y"] ge_game_eq[of "y" "x"]
          right_options_neg left_options_neg zimage_iff  xl yr)
    qed
  }
  note a = this[of "[x,y]"]
  then show ?thesis by blast
qed

definition eq_game_rel :: "(game * game) set" where
  "eq_game_rel \<equiv> { (p, q) . eq_game p q }"

definition "Pg = UNIV//eq_game_rel"

typedef Pg = Pg
  unfolding Pg_def by (auto simp add: quotient_def)

lemma equiv_eq_game[simp]: "equiv UNIV eq_game_rel"
  by (auto simp add: equiv_def refl_on_def sym_def trans_def eq_game_rel_def
    eq_game_sym intro: eq_game_refl eq_game_trans)

instantiation Pg :: "{ord, zero, plus, minus, uminus}"
begin

definition
  Pg_zero_def: "0 = Abs_Pg (eq_game_rel `` {zero_game})"

definition
  Pg_le_def: "G \<le> H \<longleftrightarrow> (\<exists> g h. g \<in> Rep_Pg G \<and> h \<in> Rep_Pg H \<and> ge_game (h, g))"

definition
  Pg_less_def: "G < H \<longleftrightarrow> G \<le> H \<and> G \<noteq> (H::Pg)"

definition
  Pg_minus_def: "- G = the_elem (\<Union> g \<in> Rep_Pg G. {Abs_Pg (eq_game_rel `` {neg_game g})})"

definition
  Pg_plus_def: "G + H = the_elem (\<Union> g \<in> Rep_Pg G. \<Union> h \<in> Rep_Pg H. {Abs_Pg (eq_game_rel `` {plus_game g h})})"

definition
  Pg_diff_def: "G - H = G + (- (H::Pg))"

instance ..

end

lemma Rep_Abs_eq_Pg[simp]: "Rep_Pg (Abs_Pg (eq_game_rel `` {g})) = eq_game_rel `` {g}"
  apply (subst Abs_Pg_inverse)
  apply (auto simp add: Pg_def quotient_def)
  done

lemma char_Pg_le[simp]: "(Abs_Pg (eq_game_rel `` {g}) \<le> Abs_Pg (eq_game_rel `` {h})) = (ge_game (h, g))"
  apply (simp add: Pg_le_def)
  apply (auto simp add: eq_game_rel_def eq_game_def intro: ge_game_trans ge_game_refl)
  done

lemma char_Pg_eq[simp]: "(Abs_Pg (eq_game_rel `` {g}) = Abs_Pg (eq_game_rel `` {h})) = (eq_game g h)"
  apply (simp add: Rep_Pg_inject [symmetric])
  apply (subst eq_equiv_class_iff[of UNIV])
  apply (simp_all)
  apply (simp add: eq_game_rel_def)
  done

lemma char_Pg_plus[simp]: "Abs_Pg (eq_game_rel `` {g}) + Abs_Pg (eq_game_rel `` {h}) = Abs_Pg (eq_game_rel `` {plus_game g h})"
proof -
  have "(\<lambda> g h. {Abs_Pg (eq_game_rel `` {plus_game g h})}) respects2 eq_game_rel" 
    apply (simp add: congruent2_def)
    apply (auto simp add: eq_game_rel_def eq_game_def)
    apply (rule_tac y="plus_game a ba" in ge_game_trans)
    apply (simp add: ge_plus_game_left[symmetric] ge_plus_game_right[symmetric])+
    apply (rule_tac y="plus_game b aa" in ge_game_trans)
    apply (simp add: ge_plus_game_left[symmetric] ge_plus_game_right[symmetric])+
    done
  then show ?thesis
    by (simp add: Pg_plus_def UN_equiv_class2[OF equiv_eq_game equiv_eq_game]) 
qed
    
lemma char_Pg_minus[simp]: "- Abs_Pg (eq_game_rel `` {g}) = Abs_Pg (eq_game_rel `` {neg_game g})"
proof -
  have "(\<lambda> g. {Abs_Pg (eq_game_rel `` {neg_game g})}) respects eq_game_rel"
    apply (simp add: congruent_def)
    apply (auto simp add: eq_game_rel_def eq_game_def ge_neg_game)
    done    
  then show ?thesis
    by (simp add: Pg_minus_def UN_equiv_class[OF equiv_eq_game])
qed

lemma eq_Abs_Pg[rule_format, cases type: Pg]: "(\<forall> g. z = Abs_Pg (eq_game_rel `` {g}) \<longrightarrow> P) \<longrightarrow> P"
  apply (cases z, simp)
  apply (simp add: Rep_Pg_inject[symmetric])
  apply (subst Abs_Pg_inverse, simp)
  apply (auto simp add: Pg_def quotient_def)
  done

instance Pg :: ordered_ab_group_add 
proof
  fix a b c :: Pg
  show "a - b = a + (- b)" by (simp add: Pg_diff_def)
  {
    assume ab: "a \<le> b"
    assume ba: "b \<le> a"
    from ab ba show "a = b"
      apply (cases a, cases b)
      apply (simp add: eq_game_def)
      done
  }
  then show "(a < b) = (a \<le> b \<and> \<not> b \<le> a)" by (auto simp add: Pg_less_def)
  show "a + b = b + a"
    apply (cases a, cases b)
    apply (simp add: eq_game_def plus_game_comm)
    done
  show "a + b + c = a + (b + c)"
    apply (cases a, cases b, cases c)
    apply (simp add: eq_game_def plus_game_assoc)
    done
  show "0 + a = a"
    apply (cases a)
    apply (simp add: Pg_zero_def plus_game_zero_left)
    done
  show "- a + a = 0"
    apply (cases a)
    apply (simp add: Pg_zero_def eq_game_plus_inverse plus_game_comm)
    done
  show "a \<le> a"
    apply (cases a)
    apply (simp add: ge_game_refl)
    done
  {
    assume ab: "a \<le> b"
    assume bc: "b \<le> c"
    from ab bc show "a \<le> c"
      apply (cases a, cases b, cases c)
      apply (auto intro: ge_game_trans)
      done
  }
  {
    assume ab: "a \<le> b"
    from ab show "c + a \<le> c + b"
      apply (cases a, cases b, cases c)
      apply (simp add: ge_plus_game_left[symmetric])
      done
  }
qed

end

