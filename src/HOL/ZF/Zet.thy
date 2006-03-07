(*  Title:      HOL/ZF/Zet.thy
    ID:         $Id$
    Author:     Steven Obua

    Introduces a type 'a zet of ZF representable sets.
    See "Partizan Games in Isabelle/HOLZF", available from http://www4.in.tum.de/~obua/partizan
*)

theory Zet 
imports HOLZF
begin

typedef 'a zet = "{A :: 'a set | A f z. inj_on f A \<and> f ` A \<subseteq> explode z}"
  by blast

constdefs
  zin :: "'a \<Rightarrow> 'a zet \<Rightarrow> bool"
  "zin x A == x \<in> (Rep_zet A)"

lemma zet_ext_eq: "(A = B) = (! x. zin x A = zin x B)"
  by (auto simp add: Rep_zet_inject[symmetric] zin_def)

constdefs
  zimage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a zet \<Rightarrow> 'b zet"
  "zimage f A == Abs_zet (image f (Rep_zet A))"

lemma zet_def': "zet = {A :: 'a set | A f z. inj_on f A \<and> f ` A = explode z}"
  apply (rule set_ext)
  apply (auto simp add: zet_def)
  apply (rule_tac x=f in exI)
  apply auto
  apply (rule_tac x="Sep z (\<lambda> y. y \<in> (f ` x))" in exI)
  apply (auto simp add: explode_def Sep)
  done

lemma image_Inv_f_f: "inj_on f B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (Inv B f) ` f ` A = A"
  apply (rule set_ext)
  apply (auto simp add: Inv_f_f image_def)
  apply (rule_tac x="f x" in exI)
  apply (auto simp add: Inv_f_f)
  done
  
lemma image_zet_rep: "A \<in> zet \<Longrightarrow> ? z . g ` A = explode z"
  apply (auto simp add: zet_def')
  apply (rule_tac x="Repl z (g o (Inv A f))" in exI)
  apply (simp add: explode_Repl_eq)
  apply (subgoal_tac "explode z = f ` A")
  apply (simp_all add: comp_image_eq image_Inv_f_f)  
  done

lemma Inv_f_f_mem:       
  assumes "x \<in> A"
  shows "Inv A g (g x) \<in> A"
  apply (simp add: Inv_def)
  apply (rule someI2)
  apply (auto!)
  done

lemma zet_image_mem:
  assumes Azet: "A \<in> zet"
  shows "g ` A \<in> zet"
proof -
  from Azet have "? (f :: _ \<Rightarrow> ZF). inj_on f A" 
    by (auto simp add: zet_def')
  then obtain f where injf: "inj_on (f :: _ \<Rightarrow> ZF) A"  
    by auto
  let ?w = "f o (Inv A g)"
  have subset: "(Inv A g) ` (g ` A) \<subseteq> A"
    by (auto simp add: Inv_f_f_mem)
  have "inj_on (Inv A g) (g ` A)" by (simp add: inj_on_Inv)
  then have injw: "inj_on ?w (g ` A)"
    apply (rule comp_inj_on)
    apply (rule subset_inj_on[where B=A])
    apply (auto simp add: subset injf)
    done
  show ?thesis
    apply (simp add: zet_def' comp_image_eq[symmetric])
    apply (rule exI[where x="?w"])
    apply (simp add: injw image_zet_rep Azet)
    done
qed

lemma Rep_zimage_eq: "Rep_zet (zimage f A) = image f (Rep_zet A)"
  apply (simp add: zimage_def)
  apply (subst Abs_zet_inverse)
  apply (simp_all add: Rep_zet zet_image_mem)
  done

lemma zimage_iff: "zin y (zimage f A) = (? x. zin x A & y = f x)"
  by (auto simp add: zin_def Rep_zimage_eq)

constdefs
  zimplode :: "ZF zet \<Rightarrow> ZF"
  "zimplode A == implode (Rep_zet A)"
  zexplode :: "ZF \<Rightarrow> ZF zet"
  "zexplode z == Abs_zet (explode z)"

lemma Rep_zet_eq_explode: "? z. Rep_zet A = explode z"
  by (rule image_zet_rep[where g="\<lambda> x. x",OF Rep_zet, simplified])

lemma zexplode_zimplode: "zexplode (zimplode A) = A"
  apply (simp add: zimplode_def zexplode_def)
  apply (simp add: implode_def)
  apply (subst f_inv_f[where y="Rep_zet A"])
  apply (auto simp add: Rep_zet_inverse Rep_zet_eq_explode image_def)
  done

lemma explode_mem_zet: "explode z \<in> zet"
  apply (simp add: zet_def')
  apply (rule_tac x="% x. x" in exI)
  apply (auto simp add: inj_on_def)
  done

lemma zimplode_zexplode: "zimplode (zexplode z) = z"
  apply (simp add: zimplode_def zexplode_def)
  apply (subst Abs_zet_inverse)
  apply (auto simp add: explode_mem_zet implode_explode)
  done  

lemma zin_zexplode_eq: "zin x (zexplode A) = Elem x A"
  apply (simp add: zin_def zexplode_def)
  apply (subst Abs_zet_inverse)
  apply (simp_all add: explode_Elem explode_mem_zet) 
  done

lemma comp_zimage_eq: "zimage g (zimage f A) = zimage (g o f) A"
  apply (simp add: zimage_def)
  apply (subst Abs_zet_inverse)
  apply (simp_all add: comp_image_eq zet_image_mem Rep_zet)
  done
    
constdefs
  zunion :: "'a zet \<Rightarrow> 'a zet \<Rightarrow> 'a zet"
  "zunion a b \<equiv> Abs_zet ((Rep_zet a) \<union> (Rep_zet b))"
  zsubset :: "'a zet \<Rightarrow> 'a zet \<Rightarrow> bool"
  "zsubset a b \<equiv> ! x. zin x a \<longrightarrow> zin x b"

lemma explode_union: "explode (union a b) = (explode a) \<union> (explode b)"
  apply (rule set_ext)
  apply (simp add: explode_def union)
  done

lemma Rep_zet_zunion: "Rep_zet (zunion a b) = (Rep_zet a) \<union> (Rep_zet b)"
proof -
  from Rep_zet[of a] have "? f z. inj_on f (Rep_zet a) \<and> f ` (Rep_zet a) = explode z"
    by (auto simp add: zet_def')
  then obtain fa za where a:"inj_on fa (Rep_zet a) \<and> fa ` (Rep_zet a) = explode za"
    by blast
  from a have fa: "inj_on fa (Rep_zet a)" by blast
  from a have za: "fa ` (Rep_zet a) = explode za" by blast
  from Rep_zet[of b] have "? f z. inj_on f (Rep_zet b) \<and> f ` (Rep_zet b) = explode z"
    by (auto simp add: zet_def')
  then obtain fb zb where b:"inj_on fb (Rep_zet b) \<and> fb ` (Rep_zet b) = explode zb"
    by blast
  from b have fb: "inj_on fb (Rep_zet b)" by blast
  from b have zb: "fb ` (Rep_zet b) = explode zb" by blast 
  let ?f = "(\<lambda> x. if x \<in> (Rep_zet a) then Opair (fa x) (Empty) else Opair (fb x) (Singleton Empty))" 
  let ?z = "CartProd (union za zb) (Upair Empty (Singleton Empty))"
  have se: "Singleton Empty \<noteq> Empty"
    apply (auto simp add: Ext Singleton)
    apply (rule exI[where x=Empty])
    apply (simp add: Empty)
    done
  show ?thesis
    apply (simp add: zunion_def)
    apply (subst Abs_zet_inverse)
    apply (auto simp add: zet_def)
    apply (rule exI[where x = ?f])
    apply (rule conjI)
    apply (auto simp add: inj_on_def Opair inj_onD[OF fa] inj_onD[OF fb] se se[symmetric])
    apply (rule exI[where x = ?z])
    apply (insert za zb)
    apply (auto simp add: explode_def CartProd union Upair Opair)
    done
qed

lemma zunion: "zin x (zunion a b) = ((zin x a) \<or> (zin x b))"
  by (auto simp add: zin_def Rep_zet_zunion)

lemma zimage_zexplode_eq: "zimage f (zexplode z) = zexplode (Repl z f)"
  by (simp add: zet_ext_eq zin_zexplode_eq Repl zimage_iff)

lemma range_explode_eq_zet: "range explode = zet"
  apply (rule set_ext)
  apply (auto simp add: explode_mem_zet)
  apply (drule image_zet_rep)
  apply (simp add: image_def)
  apply auto
  apply (rule_tac x=z in exI)
  apply auto
  done

lemma Elem_zimplode: "(Elem x (zimplode z)) = (zin x z)"
  apply (simp add: zimplode_def)
  apply (subst Elem_implode)
  apply (simp_all add: zin_def Rep_zet range_explode_eq_zet)
  done

constdefs
  zempty :: "'a zet"
  "zempty \<equiv> Abs_zet {}"

lemma zempty[simp]: "\<not> (zin x zempty)"
  by (auto simp add: zin_def zempty_def Abs_zet_inverse zet_def)

lemma zimage_zempty[simp]: "zimage f zempty = zempty"
  by (auto simp add: zet_ext_eq zimage_iff)

lemma zunion_zempty_left[simp]: "zunion zempty a = a"
  by (simp add: zet_ext_eq zunion)

lemma zunion_zempty_right[simp]: "zunion a zempty = a"
  by (simp add: zet_ext_eq zunion)

lemma zimage_id[simp]: "zimage id A = A"
  by (simp add: zet_ext_eq zimage_iff)

lemma zimage_cong[recdef_cong]: "\<lbrakk> M = N; !! x. zin x N \<Longrightarrow> f x = g x \<rbrakk> \<Longrightarrow> zimage f M = zimage g N"
  by (auto simp add: zet_ext_eq zimage_iff)

end
