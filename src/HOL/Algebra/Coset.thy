(*  Title:      HOL/Algebra/Coset.thy
    Author:     Florian Kammueller
    Author:     L C Paulson
    Author:     Stephan Hohe
*)

theory Coset
imports Group
begin

section {*Cosets and Quotient Groups*}

definition
  r_coset    :: "[_, 'a set, 'a] \<Rightarrow> 'a set"    (infixl "#>\<index>" 60)
  where "H #>\<^bsub>G\<^esub> a = (\<Union>h\<in>H. {h \<otimes>\<^bsub>G\<^esub> a})"

definition
  l_coset    :: "[_, 'a, 'a set] \<Rightarrow> 'a set"    (infixl "<#\<index>" 60)
  where "a <#\<^bsub>G\<^esub> H = (\<Union>h\<in>H. {a \<otimes>\<^bsub>G\<^esub> h})"

definition
  RCOSETS  :: "[_, 'a set] \<Rightarrow> ('a set)set"   ("rcosets\<index> _" [81] 80)
  where "rcosets\<^bsub>G\<^esub> H = (\<Union>a\<in>carrier G. {H #>\<^bsub>G\<^esub> a})"

definition
  set_mult  :: "[_, 'a set ,'a set] \<Rightarrow> 'a set" (infixl "<#>\<index>" 60)
  where "H <#>\<^bsub>G\<^esub> K = (\<Union>h\<in>H. \<Union>k\<in>K. {h \<otimes>\<^bsub>G\<^esub> k})"

definition
  SET_INV :: "[_,'a set] \<Rightarrow> 'a set"  ("set'_inv\<index> _" [81] 80)
  where "set_inv\<^bsub>G\<^esub> H = (\<Union>h\<in>H. {inv\<^bsub>G\<^esub> h})"


locale normal = subgroup + group +
  assumes coset_eq: "(\<forall>x \<in> carrier G. H #> x = x <# H)"

abbreviation
  normal_rel :: "['a set, ('a, 'b) monoid_scheme] \<Rightarrow> bool"  (infixl "\<lhd>" 60) where
  "H \<lhd> G \<equiv> normal H G"


subsection {*Basic Properties of Cosets*}

lemma (in group) coset_mult_assoc:
     "[| M \<subseteq> carrier G; g \<in> carrier G; h \<in> carrier G |]
      ==> (M #> g) #> h = M #> (g \<otimes> h)"
by (force simp add: r_coset_def m_assoc)

lemma (in group) coset_mult_one [simp]: "M \<subseteq> carrier G ==> M #> \<one> = M"
by (force simp add: r_coset_def)

lemma (in group) coset_mult_inv1:
     "[| M #> (x \<otimes> (inv y)) = M;  x \<in> carrier G ; y \<in> carrier G;
         M \<subseteq> carrier G |] ==> M #> x = M #> y"
apply (erule subst [of concl: "%z. M #> x = z #> y"])
apply (simp add: coset_mult_assoc m_assoc)
done

lemma (in group) coset_mult_inv2:
     "[| M #> x = M #> y;  x \<in> carrier G;  y \<in> carrier G;  M \<subseteq> carrier G |]
      ==> M #> (x \<otimes> (inv y)) = M "
apply (simp add: coset_mult_assoc [symmetric])
apply (simp add: coset_mult_assoc)
done

lemma (in group) coset_join1:
     "[| H #> x = H;  x \<in> carrier G;  subgroup H G |] ==> x \<in> H"
apply (erule subst)
apply (simp add: r_coset_def)
apply (blast intro: l_one subgroup.one_closed sym)
done

lemma (in group) solve_equation:
    "\<lbrakk>subgroup H G; x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> \<exists>h\<in>H. y = h \<otimes> x"
apply (rule bexI [of _ "y \<otimes> (inv x)"])
apply (auto simp add: subgroup.m_closed subgroup.m_inv_closed m_assoc
                      subgroup.subset [THEN subsetD])
done

lemma (in group) repr_independence:
     "\<lbrakk>y \<in> H #> x;  x \<in> carrier G; subgroup H G\<rbrakk> \<Longrightarrow> H #> x = H #> y"
by (auto simp add: r_coset_def m_assoc [symmetric]
                   subgroup.subset [THEN subsetD]
                   subgroup.m_closed solve_equation)

lemma (in group) coset_join2:
     "\<lbrakk>x \<in> carrier G;  subgroup H G;  x\<in>H\<rbrakk> \<Longrightarrow> H #> x = H"
  --{*Alternative proof is to put @{term "x=\<one>"} in @{text repr_independence}.*}
by (force simp add: subgroup.m_closed r_coset_def solve_equation)

lemma (in monoid) r_coset_subset_G:
     "[| H \<subseteq> carrier G; x \<in> carrier G |] ==> H #> x \<subseteq> carrier G"
by (auto simp add: r_coset_def)

lemma (in group) rcosI:
     "[| h \<in> H; H \<subseteq> carrier G; x \<in> carrier G|] ==> h \<otimes> x \<in> H #> x"
by (auto simp add: r_coset_def)

lemma (in group) rcosetsI:
     "\<lbrakk>H \<subseteq> carrier G; x \<in> carrier G\<rbrakk> \<Longrightarrow> H #> x \<in> rcosets H"
by (auto simp add: RCOSETS_def)

text{*Really needed?*}
lemma (in group) transpose_inv:
     "[| x \<otimes> y = z;  x \<in> carrier G;  y \<in> carrier G;  z \<in> carrier G |]
      ==> (inv x) \<otimes> z = y"
by (force simp add: m_assoc [symmetric])

lemma (in group) rcos_self: "[| x \<in> carrier G; subgroup H G |] ==> x \<in> H #> x"
apply (simp add: r_coset_def)
apply (blast intro: sym l_one subgroup.subset [THEN subsetD]
                    subgroup.one_closed)
done

text (in group) {* Opposite of @{thm [source] "repr_independence"} *}
lemma (in group) repr_independenceD:
  assumes "subgroup H G"
  assumes ycarr: "y \<in> carrier G"
      and repr:  "H #> x = H #> y"
  shows "y \<in> H #> x"
proof -
  interpret subgroup H G by fact
  show ?thesis  apply (subst repr)
  apply (intro rcos_self)
   apply (rule ycarr)
   apply (rule is_subgroup)
  done
qed

text {* Elements of a right coset are in the carrier *}
lemma (in subgroup) elemrcos_carrier:
  assumes "group G"
  assumes acarr: "a \<in> carrier G"
    and a': "a' \<in> H #> a"
  shows "a' \<in> carrier G"
proof -
  interpret group G by fact
  from subset and acarr
  have "H #> a \<subseteq> carrier G" by (rule r_coset_subset_G)
  from this and a'
  show "a' \<in> carrier G"
    by fast
qed

lemma (in subgroup) rcos_const:
  assumes "group G"
  assumes hH: "h \<in> H"
  shows "H #> h = H"
proof -
  interpret group G by fact
  show ?thesis apply (unfold r_coset_def)
    apply rule
    apply rule
    apply clarsimp
    apply (intro subgroup.m_closed)
    apply (rule is_subgroup)
    apply assumption
    apply (rule hH)
    apply rule
    apply simp
  proof -
    fix h'
    assume h'H: "h' \<in> H"
    note carr = hH[THEN mem_carrier] h'H[THEN mem_carrier]
    from carr
    have a: "h' = (h' \<otimes> inv h) \<otimes> h" by (simp add: m_assoc)
    from h'H hH
    have "h' \<otimes> inv h \<in> H" by simp
    from this and a
    show "\<exists>x\<in>H. h' = x \<otimes> h" by fast
  qed
qed

text {* Step one for lemma @{text "rcos_module"} *}
lemma (in subgroup) rcos_module_imp:
  assumes "group G"
  assumes xcarr: "x \<in> carrier G"
      and x'cos: "x' \<in> H #> x"
  shows "(x' \<otimes> inv x) \<in> H"
proof -
  interpret group G by fact
  from xcarr x'cos
      have x'carr: "x' \<in> carrier G"
      by (rule elemrcos_carrier[OF is_group])
  from xcarr
      have ixcarr: "inv x \<in> carrier G"
      by simp
  from x'cos
      have "\<exists>h\<in>H. x' = h \<otimes> x"
      unfolding r_coset_def
      by fast
  from this
      obtain h
        where hH: "h \<in> H"
        and x': "x' = h \<otimes> x"
      by auto
  from hH and subset
      have hcarr: "h \<in> carrier G" by fast
  note carr = xcarr x'carr hcarr
  from x' and carr
      have "x' \<otimes> (inv x) = (h \<otimes> x) \<otimes> (inv x)" by fast
  also from carr
      have "\<dots> = h \<otimes> (x \<otimes> inv x)" by (simp add: m_assoc)
  also from carr
      have "\<dots> = h \<otimes> \<one>" by simp
  also from carr
      have "\<dots> = h" by simp
  finally
      have "x' \<otimes> (inv x) = h" by simp
  from hH this
      show "x' \<otimes> (inv x) \<in> H" by simp
qed

text {* Step two for lemma @{text "rcos_module"} *}
lemma (in subgroup) rcos_module_rev:
  assumes "group G"
  assumes carr: "x \<in> carrier G" "x' \<in> carrier G"
      and xixH: "(x' \<otimes> inv x) \<in> H"
  shows "x' \<in> H #> x"
proof -
  interpret group G by fact
  from xixH
      have "\<exists>h\<in>H. x' \<otimes> (inv x) = h" by fast
  from this
      obtain h
        where hH: "h \<in> H"
        and hsym: "x' \<otimes> (inv x) = h"
      by fast
  from hH subset have hcarr: "h \<in> carrier G" by simp
  note carr = carr hcarr
  from hsym[symmetric] have "h \<otimes> x = x' \<otimes> (inv x) \<otimes> x" by fast
  also from carr
      have "\<dots> = x' \<otimes> ((inv x) \<otimes> x)" by (simp add: m_assoc)
  also from carr
      have "\<dots> = x' \<otimes> \<one>" by simp
  also from carr
      have "\<dots> = x'" by simp
  finally
      have "h \<otimes> x = x'" by simp
  from this[symmetric] and hH
      show "x' \<in> H #> x"
      unfolding r_coset_def
      by fast
qed

text {* Module property of right cosets *}
lemma (in subgroup) rcos_module:
  assumes "group G"
  assumes carr: "x \<in> carrier G" "x' \<in> carrier G"
  shows "(x' \<in> H #> x) = (x' \<otimes> inv x \<in> H)"
proof -
  interpret group G by fact
  show ?thesis proof  assume "x' \<in> H #> x"
    from this and carr
    show "x' \<otimes> inv x \<in> H"
      by (intro rcos_module_imp[OF is_group])
  next
    assume "x' \<otimes> inv x \<in> H"
    from this and carr
    show "x' \<in> H #> x"
      by (intro rcos_module_rev[OF is_group])
  qed
qed

text {* Right cosets are subsets of the carrier. *} 
lemma (in subgroup) rcosets_carrier:
  assumes "group G"
  assumes XH: "X \<in> rcosets H"
  shows "X \<subseteq> carrier G"
proof -
  interpret group G by fact
  from XH have "\<exists>x\<in> carrier G. X = H #> x"
      unfolding RCOSETS_def
      by fast
  from this
      obtain x
        where xcarr: "x\<in> carrier G"
        and X: "X = H #> x"
      by fast
  from subset and xcarr
      show "X \<subseteq> carrier G"
      unfolding X
      by (rule r_coset_subset_G)
qed

text {* Multiplication of general subsets *}
lemma (in monoid) set_mult_closed:
  assumes Acarr: "A \<subseteq> carrier G"
      and Bcarr: "B \<subseteq> carrier G"
  shows "A <#> B \<subseteq> carrier G"
apply rule apply (simp add: set_mult_def, clarsimp)
proof -
  fix a b
  assume "a \<in> A"
  from this and Acarr
      have acarr: "a \<in> carrier G" by fast

  assume "b \<in> B"
  from this and Bcarr
      have bcarr: "b \<in> carrier G" by fast

  from acarr bcarr
      show "a \<otimes> b \<in> carrier G" by (rule m_closed)
qed

lemma (in comm_group) mult_subgroups:
  assumes subH: "subgroup H G"
      and subK: "subgroup K G"
  shows "subgroup (H <#> K) G"
apply (rule subgroup.intro)
   apply (intro set_mult_closed subgroup.subset[OF subH] subgroup.subset[OF subK])
  apply (simp add: set_mult_def) apply clarsimp defer 1
  apply (simp add: set_mult_def) defer 1
  apply (simp add: set_mult_def, clarsimp) defer 1
proof -
  fix ha hb ka kb
  assume haH: "ha \<in> H" and hbH: "hb \<in> H" and kaK: "ka \<in> K" and kbK: "kb \<in> K"
  note carr = haH[THEN subgroup.mem_carrier[OF subH]] hbH[THEN subgroup.mem_carrier[OF subH]]
              kaK[THEN subgroup.mem_carrier[OF subK]] kbK[THEN subgroup.mem_carrier[OF subK]]
  from carr
      have "(ha \<otimes> ka) \<otimes> (hb \<otimes> kb) = ha \<otimes> (ka \<otimes> hb) \<otimes> kb" by (simp add: m_assoc)
  also from carr
      have "\<dots> = ha \<otimes> (hb \<otimes> ka) \<otimes> kb" by (simp add: m_comm)
  also from carr
      have "\<dots> = (ha \<otimes> hb) \<otimes> (ka \<otimes> kb)" by (simp add: m_assoc)
  finally
      have eq: "(ha \<otimes> ka) \<otimes> (hb \<otimes> kb) = (ha \<otimes> hb) \<otimes> (ka \<otimes> kb)" .

  from haH hbH have hH: "ha \<otimes> hb \<in> H" by (simp add: subgroup.m_closed[OF subH])
  from kaK kbK have kK: "ka \<otimes> kb \<in> K" by (simp add: subgroup.m_closed[OF subK])
  
  from hH and kK and eq
      show "\<exists>h'\<in>H. \<exists>k'\<in>K. (ha \<otimes> ka) \<otimes> (hb \<otimes> kb) = h' \<otimes> k'" by fast
next
  have "\<one> = \<one> \<otimes> \<one>" by simp
  from subgroup.one_closed[OF subH] subgroup.one_closed[OF subK] this
      show "\<exists>h\<in>H. \<exists>k\<in>K. \<one> = h \<otimes> k" by fast
next
  fix h k
  assume hH: "h \<in> H"
     and kK: "k \<in> K"

  from hH[THEN subgroup.mem_carrier[OF subH]] kK[THEN subgroup.mem_carrier[OF subK]]
      have "inv (h \<otimes> k) = inv h \<otimes> inv k" by (simp add: inv_mult_group m_comm)

  from subgroup.m_inv_closed[OF subH hH] and subgroup.m_inv_closed[OF subK kK] and this
      show "\<exists>ha\<in>H. \<exists>ka\<in>K. inv (h \<otimes> k) = ha \<otimes> ka" by fast
qed

lemma (in subgroup) lcos_module_rev:
  assumes "group G"
  assumes carr: "x \<in> carrier G" "x' \<in> carrier G"
      and xixH: "(inv x \<otimes> x') \<in> H"
  shows "x' \<in> x <# H"
proof -
  interpret group G by fact
  from xixH
      have "\<exists>h\<in>H. (inv x) \<otimes> x' = h" by fast
  from this
      obtain h
        where hH: "h \<in> H"
        and hsym: "(inv x) \<otimes> x' = h"
      by fast

  from hH subset have hcarr: "h \<in> carrier G" by simp
  note carr = carr hcarr
  from hsym[symmetric] have "x \<otimes> h = x \<otimes> ((inv x) \<otimes> x')" by fast
  also from carr
      have "\<dots> = (x \<otimes> (inv x)) \<otimes> x'" by (simp add: m_assoc[symmetric])
  also from carr
      have "\<dots> = \<one> \<otimes> x'" by simp
  also from carr
      have "\<dots> = x'" by simp
  finally
      have "x \<otimes> h = x'" by simp

  from this[symmetric] and hH
      show "x' \<in> x <# H"
      unfolding l_coset_def
      by fast
qed


subsection {* Normal subgroups *}

lemma normal_imp_subgroup: "H \<lhd> G \<Longrightarrow> subgroup H G"
  by (simp add: normal_def subgroup_def)

lemma (in group) normalI: 
  "subgroup H G \<Longrightarrow> (\<forall>x \<in> carrier G. H #> x = x <# H) \<Longrightarrow> H \<lhd> G"
  by (simp add: normal_def normal_axioms_def is_group)

lemma (in normal) inv_op_closed1:
     "\<lbrakk>x \<in> carrier G; h \<in> H\<rbrakk> \<Longrightarrow> (inv x) \<otimes> h \<otimes> x \<in> H"
apply (insert coset_eq) 
apply (auto simp add: l_coset_def r_coset_def)
apply (drule bspec, assumption)
apply (drule equalityD1 [THEN subsetD], blast, clarify)
apply (simp add: m_assoc)
apply (simp add: m_assoc [symmetric])
done

lemma (in normal) inv_op_closed2:
     "\<lbrakk>x \<in> carrier G; h \<in> H\<rbrakk> \<Longrightarrow> x \<otimes> h \<otimes> (inv x) \<in> H"
apply (subgoal_tac "inv (inv x) \<otimes> h \<otimes> (inv x) \<in> H") 
apply (simp add: ) 
apply (blast intro: inv_op_closed1) 
done

text{*Alternative characterization of normal subgroups*}
lemma (in group) normal_inv_iff:
     "(N \<lhd> G) = 
      (subgroup N G & (\<forall>x \<in> carrier G. \<forall>h \<in> N. x \<otimes> h \<otimes> (inv x) \<in> N))"
      (is "_ = ?rhs")
proof
  assume N: "N \<lhd> G"
  show ?rhs
    by (blast intro: N normal.inv_op_closed2 normal_imp_subgroup) 
next
  assume ?rhs
  hence sg: "subgroup N G" 
    and closed: "\<And>x. x\<in>carrier G \<Longrightarrow> \<forall>h\<in>N. x \<otimes> h \<otimes> inv x \<in> N" by auto
  hence sb: "N \<subseteq> carrier G" by (simp add: subgroup.subset) 
  show "N \<lhd> G"
  proof (intro normalI [OF sg], simp add: l_coset_def r_coset_def, clarify)
    fix x
    assume x: "x \<in> carrier G"
    show "(\<Union>h\<in>N. {h \<otimes> x}) = (\<Union>h\<in>N. {x \<otimes> h})"
    proof
      show "(\<Union>h\<in>N. {h \<otimes> x}) \<subseteq> (\<Union>h\<in>N. {x \<otimes> h})"
      proof clarify
        fix n
        assume n: "n \<in> N" 
        show "n \<otimes> x \<in> (\<Union>h\<in>N. {x \<otimes> h})"
        proof 
          from closed [of "inv x"]
          show "inv x \<otimes> n \<otimes> x \<in> N" by (simp add: x n)
          show "n \<otimes> x \<in> {x \<otimes> (inv x \<otimes> n \<otimes> x)}"
            by (simp add: x n m_assoc [symmetric] sb [THEN subsetD])
        qed
      qed
    next
      show "(\<Union>h\<in>N. {x \<otimes> h}) \<subseteq> (\<Union>h\<in>N. {h \<otimes> x})"
      proof clarify
        fix n
        assume n: "n \<in> N" 
        show "x \<otimes> n \<in> (\<Union>h\<in>N. {h \<otimes> x})"
        proof 
          show "x \<otimes> n \<otimes> inv x \<in> N" by (simp add: x n closed)
          show "x \<otimes> n \<in> {x \<otimes> n \<otimes> inv x \<otimes> x}"
            by (simp add: x n m_assoc sb [THEN subsetD])
        qed
      qed
    qed
  qed
qed


subsection{*More Properties of Cosets*}

lemma (in group) lcos_m_assoc:
     "[| M \<subseteq> carrier G; g \<in> carrier G; h \<in> carrier G |]
      ==> g <# (h <# M) = (g \<otimes> h) <# M"
by (force simp add: l_coset_def m_assoc)

lemma (in group) lcos_mult_one: "M \<subseteq> carrier G ==> \<one> <# M = M"
by (force simp add: l_coset_def)

lemma (in group) l_coset_subset_G:
     "[| H \<subseteq> carrier G; x \<in> carrier G |] ==> x <# H \<subseteq> carrier G"
by (auto simp add: l_coset_def subsetD)

lemma (in group) l_coset_swap:
     "\<lbrakk>y \<in> x <# H;  x \<in> carrier G;  subgroup H G\<rbrakk> \<Longrightarrow> x \<in> y <# H"
proof (simp add: l_coset_def)
  assume "\<exists>h\<in>H. y = x \<otimes> h"
    and x: "x \<in> carrier G"
    and sb: "subgroup H G"
  then obtain h' where h': "h' \<in> H & x \<otimes> h' = y" by blast
  show "\<exists>h\<in>H. x = y \<otimes> h"
  proof
    show "x = y \<otimes> inv h'" using h' x sb
      by (auto simp add: m_assoc subgroup.subset [THEN subsetD])
    show "inv h' \<in> H" using h' sb
      by (auto simp add: subgroup.subset [THEN subsetD] subgroup.m_inv_closed)
  qed
qed

lemma (in group) l_coset_carrier:
     "[| y \<in> x <# H;  x \<in> carrier G;  subgroup H G |] ==> y \<in> carrier G"
by (auto simp add: l_coset_def m_assoc
                   subgroup.subset [THEN subsetD] subgroup.m_closed)

lemma (in group) l_repr_imp_subset:
  assumes y: "y \<in> x <# H" and x: "x \<in> carrier G" and sb: "subgroup H G"
  shows "y <# H \<subseteq> x <# H"
proof -
  from y
  obtain h' where "h' \<in> H" "x \<otimes> h' = y" by (auto simp add: l_coset_def)
  thus ?thesis using x sb
    by (auto simp add: l_coset_def m_assoc
                       subgroup.subset [THEN subsetD] subgroup.m_closed)
qed

lemma (in group) l_repr_independence:
  assumes y: "y \<in> x <# H" and x: "x \<in> carrier G" and sb: "subgroup H G"
  shows "x <# H = y <# H"
proof
  show "x <# H \<subseteq> y <# H"
    by (rule l_repr_imp_subset,
        (blast intro: l_coset_swap l_coset_carrier y x sb)+)
  show "y <# H \<subseteq> x <# H" by (rule l_repr_imp_subset [OF y x sb])
qed

lemma (in group) setmult_subset_G:
     "\<lbrakk>H \<subseteq> carrier G; K \<subseteq> carrier G\<rbrakk> \<Longrightarrow> H <#> K \<subseteq> carrier G"
by (auto simp add: set_mult_def subsetD)

lemma (in group) subgroup_mult_id: "subgroup H G \<Longrightarrow> H <#> H = H"
apply (auto simp add: subgroup.m_closed set_mult_def Sigma_def image_def)
apply (rule_tac x = x in bexI)
apply (rule bexI [of _ "\<one>"])
apply (auto simp add: subgroup.one_closed subgroup.subset [THEN subsetD])
done


subsubsection {* Set of Inverses of an @{text r_coset}. *}

lemma (in normal) rcos_inv:
  assumes x:     "x \<in> carrier G"
  shows "set_inv (H #> x) = H #> (inv x)" 
proof (simp add: r_coset_def SET_INV_def x inv_mult_group, safe)
  fix h
  assume h: "h \<in> H"
  show "inv x \<otimes> inv h \<in> (\<Union>j\<in>H. {j \<otimes> inv x})"
  proof
    show "inv x \<otimes> inv h \<otimes> x \<in> H"
      by (simp add: inv_op_closed1 h x)
    show "inv x \<otimes> inv h \<in> {inv x \<otimes> inv h \<otimes> x \<otimes> inv x}"
      by (simp add: h x m_assoc)
  qed
  show "h \<otimes> inv x \<in> (\<Union>j\<in>H. {inv x \<otimes> inv j})"
  proof
    show "x \<otimes> inv h \<otimes> inv x \<in> H"
      by (simp add: inv_op_closed2 h x)
    show "h \<otimes> inv x \<in> {inv x \<otimes> inv (x \<otimes> inv h \<otimes> inv x)}"
      by (simp add: h x m_assoc [symmetric] inv_mult_group)
  qed
qed


subsubsection {*Theorems for @{text "<#>"} with @{text "#>"} or @{text "<#"}.*}

lemma (in group) setmult_rcos_assoc:
     "\<lbrakk>H \<subseteq> carrier G; K \<subseteq> carrier G; x \<in> carrier G\<rbrakk>
      \<Longrightarrow> H <#> (K #> x) = (H <#> K) #> x"
by (force simp add: r_coset_def set_mult_def m_assoc)

lemma (in group) rcos_assoc_lcos:
     "\<lbrakk>H \<subseteq> carrier G; K \<subseteq> carrier G; x \<in> carrier G\<rbrakk>
      \<Longrightarrow> (H #> x) <#> K = H <#> (x <# K)"
by (force simp add: r_coset_def l_coset_def set_mult_def m_assoc)

lemma (in normal) rcos_mult_step1:
     "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk>
      \<Longrightarrow> (H #> x) <#> (H #> y) = (H <#> (x <# H)) #> y"
by (simp add: setmult_rcos_assoc subset
              r_coset_subset_G l_coset_subset_G rcos_assoc_lcos)

lemma (in normal) rcos_mult_step2:
     "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk>
      \<Longrightarrow> (H <#> (x <# H)) #> y = (H <#> (H #> x)) #> y"
by (insert coset_eq, simp add: normal_def)

lemma (in normal) rcos_mult_step3:
     "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk>
      \<Longrightarrow> (H <#> (H #> x)) #> y = H #> (x \<otimes> y)"
by (simp add: setmult_rcos_assoc coset_mult_assoc
              subgroup_mult_id normal.axioms subset normal_axioms)

lemma (in normal) rcos_sum:
     "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk>
      \<Longrightarrow> (H #> x) <#> (H #> y) = H #> (x \<otimes> y)"
by (simp add: rcos_mult_step1 rcos_mult_step2 rcos_mult_step3)

lemma (in normal) rcosets_mult_eq: "M \<in> rcosets H \<Longrightarrow> H <#> M = M"
  -- {* generalizes @{text subgroup_mult_id} *}
  by (auto simp add: RCOSETS_def subset
        setmult_rcos_assoc subgroup_mult_id normal.axioms normal_axioms)


subsubsection{*An Equivalence Relation*}

definition
  r_congruent :: "[('a,'b)monoid_scheme, 'a set] \<Rightarrow> ('a*'a)set"  ("rcong\<index> _")
  where "rcong\<^bsub>G\<^esub> H = {(x,y). x \<in> carrier G & y \<in> carrier G & inv\<^bsub>G\<^esub> x \<otimes>\<^bsub>G\<^esub> y \<in> H}"


lemma (in subgroup) equiv_rcong:
   assumes "group G"
   shows "equiv (carrier G) (rcong H)"
proof -
  interpret group G by fact
  show ?thesis
  proof (intro equivI)
    show "refl_on (carrier G) (rcong H)"
      by (auto simp add: r_congruent_def refl_on_def) 
  next
    show "sym (rcong H)"
    proof (simp add: r_congruent_def sym_def, clarify)
      fix x y
      assume [simp]: "x \<in> carrier G" "y \<in> carrier G" 
         and "inv x \<otimes> y \<in> H"
      hence "inv (inv x \<otimes> y) \<in> H" by simp
      thus "inv y \<otimes> x \<in> H" by (simp add: inv_mult_group)
    qed
  next
    show "trans (rcong H)"
    proof (simp add: r_congruent_def trans_def, clarify)
      fix x y z
      assume [simp]: "x \<in> carrier G" "y \<in> carrier G" "z \<in> carrier G"
         and "inv x \<otimes> y \<in> H" and "inv y \<otimes> z \<in> H"
      hence "(inv x \<otimes> y) \<otimes> (inv y \<otimes> z) \<in> H" by simp
      hence "inv x \<otimes> (y \<otimes> inv y) \<otimes> z \<in> H"
        by (simp add: m_assoc del: r_inv Units_r_inv) 
      thus "inv x \<otimes> z \<in> H" by simp
    qed
  qed
qed

text{*Equivalence classes of @{text rcong} correspond to left cosets.
  Was there a mistake in the definitions? I'd have expected them to
  correspond to right cosets.*}

(* CB: This is correct, but subtle.
   We call H #> a the right coset of a relative to H.  According to
   Jacobson, this is what the majority of group theory literature does.
   He then defines the notion of congruence relation ~ over monoids as
   equivalence relation with a ~ a' & b ~ b' \<Longrightarrow> a*b ~ a'*b'.
   Our notion of right congruence induced by K: rcong K appears only in
   the context where K is a normal subgroup.  Jacobson doesn't name it.
   But in this context left and right cosets are identical.
*)

lemma (in subgroup) l_coset_eq_rcong:
  assumes "group G"
  assumes a: "a \<in> carrier G"
  shows "a <# H = rcong H `` {a}"
proof -
  interpret group G by fact
  show ?thesis by (force simp add: r_congruent_def l_coset_def m_assoc [symmetric] a ) 
qed


subsubsection{*Two Distinct Right Cosets are Disjoint*}

lemma (in group) rcos_equation:
  assumes "subgroup H G"
  assumes p: "ha \<otimes> a = h \<otimes> b" "a \<in> carrier G" "b \<in> carrier G" "h \<in> H" "ha \<in> H" "hb \<in> H"
  shows "hb \<otimes> a \<in> (\<Union>h\<in>H. {h \<otimes> b})"
proof -
  interpret subgroup H G by fact
  from p show ?thesis apply (rule_tac UN_I [of "hb \<otimes> ((inv ha) \<otimes> h)"])
    apply (simp add: )
    apply (simp add: m_assoc transpose_inv)
    done
qed

lemma (in group) rcos_disjoint:
  assumes "subgroup H G"
  assumes p: "a \<in> rcosets H" "b \<in> rcosets H" "a\<noteq>b"
  shows "a \<inter> b = {}"
proof -
  interpret subgroup H G by fact
  from p show ?thesis
    apply (simp add: RCOSETS_def r_coset_def)
    apply (blast intro: rcos_equation assms sym)
    done
qed


subsection {* Further lemmas for @{text "r_congruent"} *}

text {* The relation is a congruence *}

lemma (in normal) congruent_rcong:
  shows "congruent2 (rcong H) (rcong H) (\<lambda>a b. a \<otimes> b <# H)"
proof (intro congruent2I[of "carrier G" _ "carrier G" _] equiv_rcong is_group)
  fix a b c
  assume abrcong: "(a, b) \<in> rcong H"
    and ccarr: "c \<in> carrier G"

  from abrcong
      have acarr: "a \<in> carrier G"
        and bcarr: "b \<in> carrier G"
        and abH: "inv a \<otimes> b \<in> H"
      unfolding r_congruent_def
      by fast+

  note carr = acarr bcarr ccarr

  from ccarr and abH
      have "inv c \<otimes> (inv a \<otimes> b) \<otimes> c \<in> H" by (rule inv_op_closed1)
  moreover
      from carr and inv_closed
      have "inv c \<otimes> (inv a \<otimes> b) \<otimes> c = (inv c \<otimes> inv a) \<otimes> (b \<otimes> c)" 
      by (force cong: m_assoc)
  moreover 
      from carr and inv_closed
      have "\<dots> = (inv (a \<otimes> c)) \<otimes> (b \<otimes> c)"
      by (simp add: inv_mult_group)
  ultimately
      have "(inv (a \<otimes> c)) \<otimes> (b \<otimes> c) \<in> H" by simp
  from carr and this
     have "(b \<otimes> c) \<in> (a \<otimes> c) <# H"
     by (simp add: lcos_module_rev[OF is_group])
  from carr and this and is_subgroup
     show "(a \<otimes> c) <# H = (b \<otimes> c) <# H" by (intro l_repr_independence, simp+)
next
  fix a b c
  assume abrcong: "(a, b) \<in> rcong H"
    and ccarr: "c \<in> carrier G"

  from ccarr have "c \<in> Units G" by simp
  hence cinvc_one: "inv c \<otimes> c = \<one>" by (rule Units_l_inv)

  from abrcong
      have acarr: "a \<in> carrier G"
       and bcarr: "b \<in> carrier G"
       and abH: "inv a \<otimes> b \<in> H"
      by (unfold r_congruent_def, fast+)

  note carr = acarr bcarr ccarr

  from carr and inv_closed
     have "inv a \<otimes> b = inv a \<otimes> (\<one> \<otimes> b)" by simp
  also from carr and inv_closed
      have "\<dots> = inv a \<otimes> (inv c \<otimes> c) \<otimes> b" by simp
  also from carr and inv_closed
      have "\<dots> = (inv a \<otimes> inv c) \<otimes> (c \<otimes> b)" by (force cong: m_assoc)
  also from carr and inv_closed
      have "\<dots> = inv (c \<otimes> a) \<otimes> (c \<otimes> b)" by (simp add: inv_mult_group)
  finally
      have "inv a \<otimes> b = inv (c \<otimes> a) \<otimes> (c \<otimes> b)" .
  from abH and this
      have "inv (c \<otimes> a) \<otimes> (c \<otimes> b) \<in> H" by simp

  from carr and this
     have "(c \<otimes> b) \<in> (c \<otimes> a) <# H"
     by (simp add: lcos_module_rev[OF is_group])
  from carr and this and is_subgroup
     show "(c \<otimes> a) <# H = (c \<otimes> b) <# H" by (intro l_repr_independence, simp+)
qed


subsection {*Order of a Group and Lagrange's Theorem*}

definition
  order :: "('a, 'b) monoid_scheme \<Rightarrow> nat"
  where "order S = card (carrier S)"

lemma (in group) rcosets_part_G:
  assumes "subgroup H G"
  shows "\<Union>(rcosets H) = carrier G"
proof -
  interpret subgroup H G by fact
  show ?thesis
    apply (rule equalityI)
    apply (force simp add: RCOSETS_def r_coset_def)
    apply (auto simp add: RCOSETS_def intro: rcos_self assms)
    done
qed

lemma (in group) cosets_finite:
     "\<lbrakk>c \<in> rcosets H;  H \<subseteq> carrier G;  finite (carrier G)\<rbrakk> \<Longrightarrow> finite c"
apply (auto simp add: RCOSETS_def)
apply (simp add: r_coset_subset_G [THEN finite_subset])
done

text{*The next two lemmas support the proof of @{text card_cosets_equal}.*}
lemma (in group) inj_on_f:
    "\<lbrakk>H \<subseteq> carrier G;  a \<in> carrier G\<rbrakk> \<Longrightarrow> inj_on (\<lambda>y. y \<otimes> inv a) (H #> a)"
apply (rule inj_onI)
apply (subgoal_tac "x \<in> carrier G & y \<in> carrier G")
 prefer 2 apply (blast intro: r_coset_subset_G [THEN subsetD])
apply (simp add: subsetD)
done

lemma (in group) inj_on_g:
    "\<lbrakk>H \<subseteq> carrier G;  a \<in> carrier G\<rbrakk> \<Longrightarrow> inj_on (\<lambda>y. y \<otimes> a) H"
by (force simp add: inj_on_def subsetD)

lemma (in group) card_cosets_equal:
     "\<lbrakk>c \<in> rcosets H;  H \<subseteq> carrier G; finite(carrier G)\<rbrakk>
      \<Longrightarrow> card c = card H"
apply (auto simp add: RCOSETS_def)
apply (rule card_bij_eq)
     apply (rule inj_on_f, assumption+)
    apply (force simp add: m_assoc subsetD r_coset_def)
   apply (rule inj_on_g, assumption+)
  apply (force simp add: m_assoc subsetD r_coset_def)
 txt{*The sets @{term "H #> a"} and @{term "H"} are finite.*}
 apply (simp add: r_coset_subset_G [THEN finite_subset])
apply (blast intro: finite_subset)
done

lemma (in group) rcosets_subset_PowG:
     "subgroup H G  \<Longrightarrow> rcosets H \<subseteq> Pow(carrier G)"
apply (simp add: RCOSETS_def)
apply (blast dest: r_coset_subset_G subgroup.subset)
done


theorem (in group) lagrange:
     "\<lbrakk>finite(carrier G); subgroup H G\<rbrakk>
      \<Longrightarrow> card(rcosets H) * card(H) = order(G)"
apply (simp (no_asm_simp) add: order_def rcosets_part_G [symmetric])
apply (subst mult_commute)
apply (rule card_partition)
   apply (simp add: rcosets_subset_PowG [THEN finite_subset])
  apply (simp add: rcosets_part_G)
 apply (simp add: card_cosets_equal subgroup.subset)
apply (simp add: rcos_disjoint)
done


subsection {*Quotient Groups: Factorization of a Group*}

definition
  FactGroup :: "[('a,'b) monoid_scheme, 'a set] \<Rightarrow> ('a set) monoid" (infixl "Mod" 65)
    --{*Actually defined for groups rather than monoids*}
   where "FactGroup G H = \<lparr>carrier = rcosets\<^bsub>G\<^esub> H, mult = set_mult G, one = H\<rparr>"

lemma (in normal) setmult_closed:
     "\<lbrakk>K1 \<in> rcosets H; K2 \<in> rcosets H\<rbrakk> \<Longrightarrow> K1 <#> K2 \<in> rcosets H"
by (auto simp add: rcos_sum RCOSETS_def)

lemma (in normal) setinv_closed:
     "K \<in> rcosets H \<Longrightarrow> set_inv K \<in> rcosets H"
by (auto simp add: rcos_inv RCOSETS_def)

lemma (in normal) rcosets_assoc:
     "\<lbrakk>M1 \<in> rcosets H; M2 \<in> rcosets H; M3 \<in> rcosets H\<rbrakk>
      \<Longrightarrow> M1 <#> M2 <#> M3 = M1 <#> (M2 <#> M3)"
by (auto simp add: RCOSETS_def rcos_sum m_assoc)

lemma (in subgroup) subgroup_in_rcosets:
  assumes "group G"
  shows "H \<in> rcosets H"
proof -
  interpret group G by fact
  from _ subgroup_axioms have "H #> \<one> = H"
    by (rule coset_join2) auto
  then show ?thesis
    by (auto simp add: RCOSETS_def)
qed

lemma (in normal) rcosets_inv_mult_group_eq:
     "M \<in> rcosets H \<Longrightarrow> set_inv M <#> M = H"
by (auto simp add: RCOSETS_def rcos_inv rcos_sum subgroup.subset normal.axioms normal_axioms)

theorem (in normal) factorgroup_is_group:
  "group (G Mod H)"
apply (simp add: FactGroup_def)
apply (rule groupI)
    apply (simp add: setmult_closed)
   apply (simp add: normal_imp_subgroup subgroup_in_rcosets [OF is_group])
  apply (simp add: restrictI setmult_closed rcosets_assoc)
 apply (simp add: normal_imp_subgroup
                  subgroup_in_rcosets rcosets_mult_eq)
apply (auto dest: rcosets_inv_mult_group_eq simp add: setinv_closed)
done

lemma mult_FactGroup [simp]: "X \<otimes>\<^bsub>(G Mod H)\<^esub> X' = X <#>\<^bsub>G\<^esub> X'"
  by (simp add: FactGroup_def) 

lemma (in normal) inv_FactGroup:
     "X \<in> carrier (G Mod H) \<Longrightarrow> inv\<^bsub>G Mod H\<^esub> X = set_inv X"
apply (rule group.inv_equality [OF factorgroup_is_group]) 
apply (simp_all add: FactGroup_def setinv_closed rcosets_inv_mult_group_eq)
done

text{*The coset map is a homomorphism from @{term G} to the quotient group
  @{term "G Mod H"}*}
lemma (in normal) r_coset_hom_Mod:
  "(\<lambda>a. H #> a) \<in> hom G (G Mod H)"
  by (auto simp add: FactGroup_def RCOSETS_def Pi_def hom_def rcos_sum)

 
subsection{*The First Isomorphism Theorem*}

text{*The quotient by the kernel of a homomorphism is isomorphic to the 
  range of that homomorphism.*}

definition
  kernel :: "('a, 'm) monoid_scheme \<Rightarrow> ('b, 'n) monoid_scheme \<Rightarrow>  ('a \<Rightarrow> 'b) \<Rightarrow> 'a set"
    --{*the kernel of a homomorphism*}
  where "kernel G H h = {x. x \<in> carrier G & h x = \<one>\<^bsub>H\<^esub>}"

lemma (in group_hom) subgroup_kernel: "subgroup (kernel G H h) G"
apply (rule subgroup.intro) 
apply (auto simp add: kernel_def group.intro is_group) 
done

text{*The kernel of a homomorphism is a normal subgroup*}
lemma (in group_hom) normal_kernel: "(kernel G H h) \<lhd> G"
apply (simp add: G.normal_inv_iff subgroup_kernel)
apply (simp add: kernel_def)
done

lemma (in group_hom) FactGroup_nonempty:
  assumes X: "X \<in> carrier (G Mod kernel G H h)"
  shows "X \<noteq> {}"
proof -
  from X
  obtain g where "g \<in> carrier G" 
             and "X = kernel G H h #> g"
    by (auto simp add: FactGroup_def RCOSETS_def)
  thus ?thesis 
   by (auto simp add: kernel_def r_coset_def image_def intro: hom_one)
qed


lemma (in group_hom) FactGroup_the_elem_mem:
  assumes X: "X \<in> carrier (G Mod (kernel G H h))"
  shows "the_elem (h`X) \<in> carrier H"
proof -
  from X
  obtain g where g: "g \<in> carrier G" 
             and "X = kernel G H h #> g"
    by (auto simp add: FactGroup_def RCOSETS_def)
  hence "h ` X = {h g}" by (auto simp add: kernel_def r_coset_def image_def g)
  thus ?thesis by (auto simp add: g)
qed

lemma (in group_hom) FactGroup_hom:
     "(\<lambda>X. the_elem (h`X)) \<in> hom (G Mod (kernel G H h)) H"
apply (simp add: hom_def FactGroup_the_elem_mem normal.factorgroup_is_group [OF normal_kernel] group.axioms monoid.m_closed)
proof (intro ballI)
  fix X and X'
  assume X:  "X  \<in> carrier (G Mod kernel G H h)"
     and X': "X' \<in> carrier (G Mod kernel G H h)"
  then
  obtain g and g'
           where "g \<in> carrier G" and "g' \<in> carrier G" 
             and "X = kernel G H h #> g" and "X' = kernel G H h #> g'"
    by (auto simp add: FactGroup_def RCOSETS_def)
  hence all: "\<forall>x\<in>X. h x = h g" "\<forall>x\<in>X'. h x = h g'" 
    and Xsub: "X \<subseteq> carrier G" and X'sub: "X' \<subseteq> carrier G"
    by (force simp add: kernel_def r_coset_def image_def)+
  hence "h ` (X <#> X') = {h g \<otimes>\<^bsub>H\<^esub> h g'}" using X X'
    by (auto dest!: FactGroup_nonempty
             simp add: set_mult_def image_eq_UN 
                       subsetD [OF Xsub] subsetD [OF X'sub]) 
  thus "the_elem (h ` (X <#> X')) = the_elem (h ` X) \<otimes>\<^bsub>H\<^esub> the_elem (h ` X')"
    by (simp add: all image_eq_UN FactGroup_nonempty X X')
qed


text{*Lemma for the following injectivity result*}
lemma (in group_hom) FactGroup_subset:
     "\<lbrakk>g \<in> carrier G; g' \<in> carrier G; h g = h g'\<rbrakk>
      \<Longrightarrow>  kernel G H h #> g \<subseteq> kernel G H h #> g'"
apply (clarsimp simp add: kernel_def r_coset_def image_def)
apply (rename_tac y)  
apply (rule_tac x="y \<otimes> g \<otimes> inv g'" in exI) 
apply (simp add: G.m_assoc) 
done

lemma (in group_hom) FactGroup_inj_on:
     "inj_on (\<lambda>X. the_elem (h ` X)) (carrier (G Mod kernel G H h))"
proof (simp add: inj_on_def, clarify) 
  fix X and X'
  assume X:  "X  \<in> carrier (G Mod kernel G H h)"
     and X': "X' \<in> carrier (G Mod kernel G H h)"
  then
  obtain g and g'
           where gX: "g \<in> carrier G"  "g' \<in> carrier G" 
              "X = kernel G H h #> g" "X' = kernel G H h #> g'"
    by (auto simp add: FactGroup_def RCOSETS_def)
  hence all: "\<forall>x\<in>X. h x = h g" "\<forall>x\<in>X'. h x = h g'" 
    by (force simp add: kernel_def r_coset_def image_def)+
  assume "the_elem (h ` X) = the_elem (h ` X')"
  hence h: "h g = h g'"
    by (simp add: image_eq_UN all FactGroup_nonempty X X') 
  show "X=X'" by (rule equalityI) (simp_all add: FactGroup_subset h gX) 
qed

text{*If the homomorphism @{term h} is onto @{term H}, then so is the
homomorphism from the quotient group*}
lemma (in group_hom) FactGroup_onto:
  assumes h: "h ` carrier G = carrier H"
  shows "(\<lambda>X. the_elem (h ` X)) ` carrier (G Mod kernel G H h) = carrier H"
proof
  show "(\<lambda>X. the_elem (h ` X)) ` carrier (G Mod kernel G H h) \<subseteq> carrier H"
    by (auto simp add: FactGroup_the_elem_mem)
  show "carrier H \<subseteq> (\<lambda>X. the_elem (h ` X)) ` carrier (G Mod kernel G H h)"
  proof
    fix y
    assume y: "y \<in> carrier H"
    with h obtain g where g: "g \<in> carrier G" "h g = y"
      by (blast elim: equalityE) 
    hence "(\<Union>x\<in>kernel G H h #> g. {h x}) = {y}" 
      by (auto simp add: y kernel_def r_coset_def) 
    with g show "y \<in> (\<lambda>X. the_elem (h ` X)) ` carrier (G Mod kernel G H h)" 
      by (auto intro!: bexI simp add: FactGroup_def RCOSETS_def image_eq_UN)
  qed
qed


text{*If @{term h} is a homomorphism from @{term G} onto @{term H}, then the
 quotient group @{term "G Mod (kernel G H h)"} is isomorphic to @{term H}.*}
theorem (in group_hom) FactGroup_iso:
  "h ` carrier G = carrier H
   \<Longrightarrow> (\<lambda>X. the_elem (h`X)) \<in> (G Mod (kernel G H h)) \<cong> H"
by (simp add: iso_def FactGroup_hom FactGroup_inj_on bij_betw_def 
              FactGroup_onto) 


end
