(* Title:  ZF/ex/Group.thy
  Id:     $Id$

*)

header {* Groups *}

theory Group = Main:

text{*Based on work by Clemens Ballarin, Florian Kammueller, L C Paulson and
Markus Wenzel.*}


subsection {* Monoids *}

(*First, we must simulate a record declaration:
record monoid = 
  carrier :: i
  mult :: "[i,i] => i" (infixl "\<cdot>\<index>" 70)
  one :: i ("\<one>\<index>")
*)

constdefs
  carrier :: "i => i"
   "carrier(M) == fst(M)"

  mmult :: "[i, i, i] => i" (infixl "\<cdot>\<index>" 70)
   "mmult(M,x,y) == fst(snd(M)) ` <x,y>"

  one :: "i => i" ("\<one>\<index>")
   "one(M) == fst(snd(snd(M)))"

  update_carrier :: "[i,i] => i"
   "update_carrier(M,A) == <A,snd(M)>"

constdefs (structure G)
  m_inv :: "i => i => i" ("inv\<index> _" [81] 80)
  "inv x == (THE y. y \<in> carrier(G) & y \<cdot> x = \<one> & x \<cdot> y = \<one>)"

locale monoid = struct G +
  assumes m_closed [intro, simp]:
         "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> carrier(G)"
      and m_assoc:
         "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G); z \<in> carrier(G)\<rbrakk> 
          \<Longrightarrow> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
      and one_closed [intro, simp]: "\<one> \<in> carrier(G)"
      and l_one [simp]: "x \<in> carrier(G) \<Longrightarrow> \<one> \<cdot> x = x"
      and r_one [simp]: "x \<in> carrier(G) \<Longrightarrow> x \<cdot> \<one> = x"

text{*Simulating the record*}
lemma carrier_eq [simp]: "carrier(<A,Z>) = A"
  by (simp add: carrier_def)

lemma mult_eq [simp]: "mmult(<A,M,Z>, x, y) = M ` <x,y>"
  by (simp add: mmult_def)

lemma one_eq [simp]: "one(<A,M,I,Z>) = I"
  by (simp add: one_def)

lemma update_carrier_eq [simp]: "update_carrier(<A,Z>,B) = <B,Z>"
  by (simp add: update_carrier_def)

lemma carrier_update_carrier [simp]: "carrier(update_carrier(M,B)) = B"
by (simp add: update_carrier_def) 

lemma mult_update_carrier [simp]: "mmult(update_carrier(M,B),x,y) = mmult(M,x,y)"
by (simp add: update_carrier_def mmult_def) 

lemma one_update_carrier [simp]: "one(update_carrier(M,B)) = one(M)"
by (simp add: update_carrier_def one_def) 


lemma (in monoid) inv_unique:
  assumes eq: "y \<cdot> x = \<one>"  "x \<cdot> y' = \<one>"
    and G: "x \<in> carrier(G)"  "y \<in> carrier(G)"  "y' \<in> carrier(G)"
  shows "y = y'"
proof -
  from G eq have "y = y \<cdot> (x \<cdot> y')" by simp
  also from G have "... = (y \<cdot> x) \<cdot> y'" by (simp add: m_assoc)
  also from G eq have "... = y'" by simp
  finally show ?thesis .
qed

text {*
  A group is a monoid all of whose elements are invertible.
*}

locale group = monoid +
  assumes inv_ex:
     "\<And>x. x \<in> carrier(G) \<Longrightarrow> \<exists>y \<in> carrier(G). y \<cdot> x = \<one> & x \<cdot> y = \<one>"

lemma (in group) is_group [simp]: "group(G)"
  by (rule group.intro [OF prems]) 

theorem groupI:
  includes struct G
  assumes m_closed [simp]:
      "\<And>x y. \<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> carrier(G)"
    and one_closed [simp]: "\<one> \<in> carrier(G)"
    and m_assoc:
      "\<And>x y z. \<lbrakk>x \<in> carrier(G); y \<in> carrier(G); z \<in> carrier(G)\<rbrakk> \<Longrightarrow>
      (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
    and l_one [simp]: "\<And>x. x \<in> carrier(G) \<Longrightarrow> \<one> \<cdot> x = x"
    and l_inv_ex: "\<And>x. x \<in> carrier(G) \<Longrightarrow> \<exists>y \<in> carrier(G). y \<cdot> x = \<one>"
  shows "group(G)"
proof -
  have l_cancel [simp]:
    "\<And>x y z. \<lbrakk>x \<in> carrier(G); y \<in> carrier(G); z \<in> carrier(G)\<rbrakk> \<Longrightarrow>
    (x \<cdot> y = x \<cdot> z) <-> (y = z)"
  proof
    fix x y z
    assume G: "x \<in> carrier(G)"  "y \<in> carrier(G)"  "z \<in> carrier(G)"
    { 
      assume eq: "x \<cdot> y = x \<cdot> z"
      with G l_inv_ex obtain x_inv where xG: "x_inv \<in> carrier(G)"
	and l_inv: "x_inv \<cdot> x = \<one>" by fast
      from G eq xG have "(x_inv \<cdot> x) \<cdot> y = (x_inv \<cdot> x) \<cdot> z"
	by (simp add: m_assoc)
      with G show "y = z" by (simp add: l_inv)
    next
      assume eq: "y = z"
      with G show "x \<cdot> y = x \<cdot> z" by simp
    }
  qed
  have r_one:
    "\<And>x. x \<in> carrier(G) \<Longrightarrow> x \<cdot> \<one> = x"
  proof -
    fix x
    assume x: "x \<in> carrier(G)"
    with l_inv_ex obtain x_inv where xG: "x_inv \<in> carrier(G)"
      and l_inv: "x_inv \<cdot> x = \<one>" by fast
    from x xG have "x_inv \<cdot> (x \<cdot> \<one>) = x_inv \<cdot> x"
      by (simp add: m_assoc [symmetric] l_inv)
    with x xG show "x \<cdot> \<one> = x" by simp
  qed
  have inv_ex:
    "!!x. x \<in> carrier(G) ==> \<exists>y \<in> carrier(G). y \<cdot> x = \<one> & x \<cdot> y = \<one>"
  proof -
    fix x
    assume x: "x \<in> carrier(G)"
    with l_inv_ex obtain y where y: "y \<in> carrier(G)"
      and l_inv: "y \<cdot> x = \<one>" by fast
    from x y have "y \<cdot> (x \<cdot> y) = y \<cdot> \<one>"
      by (simp add: m_assoc [symmetric] l_inv r_one)
    with x y have r_inv: "x \<cdot> y = \<one>"
      by simp
    from x y show "\<exists>y \<in> carrier(G). y \<cdot> x = \<one> & x \<cdot> y = \<one>"
      by (fast intro: l_inv r_inv)
  qed
  show ?thesis
    by (blast intro: group.intro monoid.intro group_axioms.intro 
                     prems r_one inv_ex)
qed

lemma (in group) inv [simp]:
  "x \<in> carrier(G) \<Longrightarrow> inv x \<in> carrier(G) & inv x \<cdot> x = \<one> & x \<cdot> inv x = \<one>"
  apply (frule inv_ex) 
  apply (unfold Bex_def m_inv_def)
  apply (erule exE) 
  apply (rule theI)
  apply (rule ex1I, assumption)
   apply (blast intro: inv_unique)
  done

lemma (in group) inv_closed [intro!]:
  "x \<in> carrier(G) \<Longrightarrow> inv x \<in> carrier(G)"
  by simp

lemma (in group) l_inv:
  "x \<in> carrier(G) \<Longrightarrow> inv x \<cdot> x = \<one>"
  by simp

lemma (in group) r_inv:
  "x \<in> carrier(G) \<Longrightarrow> x \<cdot> inv x = \<one>"
  by simp


subsection {* Cancellation Laws and Basic Properties *}

lemma (in group) l_cancel [simp]:
  assumes [simp]: "x \<in> carrier(G)" "y \<in> carrier(G)" "z \<in> carrier(G)"
  shows "(x \<cdot> y = x \<cdot> z) <-> (y = z)"
proof
  assume eq: "x \<cdot> y = x \<cdot> z"
  hence  "(inv x \<cdot> x) \<cdot> y = (inv x \<cdot> x) \<cdot> z"
    by (simp only: m_assoc inv_closed prems)
  thus "y = z" by simp
next
  assume eq: "y = z"
  then show "x \<cdot> y = x \<cdot> z" by simp
qed

lemma (in group) r_cancel [simp]:
  assumes [simp]: "x \<in> carrier(G)" "y \<in> carrier(G)" "z \<in> carrier(G)"
  shows "(y \<cdot> x = z \<cdot> x) <-> (y = z)"
proof
  assume eq: "y \<cdot> x = z \<cdot> x"
  then have "y \<cdot> (x \<cdot> inv x) = z \<cdot> (x \<cdot> inv x)"
    by (simp only: m_assoc [symmetric] inv_closed prems)
  thus "y = z" by simp
next
  assume eq: "y = z"
  thus  "y \<cdot> x = z \<cdot> x" by simp
qed

lemma (in group) inv_comm:
  assumes inv: "x \<cdot> y = \<one>"
      and G: "x \<in> carrier(G)"  "y \<in> carrier(G)"
  shows "y \<cdot> x = \<one>"
proof -
  from G have "x \<cdot> y \<cdot> x = x \<cdot> \<one>" by (auto simp add: inv)
  with G show ?thesis by (simp del: r_one add: m_assoc)
qed

lemma (in group) inv_equality:
     "\<lbrakk>y \<cdot> x = \<one>; x \<in> carrier(G); y \<in> carrier(G)\<rbrakk> \<Longrightarrow> inv x = y"
apply (simp add: m_inv_def)
apply (rule the_equality)
 apply (simp add: inv_comm [of y x])
apply (rule r_cancel [THEN iffD1], auto)
done

lemma (in group) inv_one [simp]:
  "inv \<one> = \<one>"
  by (auto intro: inv_equality) 

lemma (in group) inv_inv [simp]: "x \<in> carrier(G) \<Longrightarrow> inv (inv x) = x"
  by (auto intro: inv_equality) 

text{*This proof is by cancellation*}
lemma (in group) inv_mult_group:
  "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk> \<Longrightarrow> inv (x \<cdot> y) = inv y \<cdot> inv x"
proof -
  assume G: "x \<in> carrier(G)"  "y \<in> carrier(G)"
  then have "inv (x \<cdot> y) \<cdot> (x \<cdot> y) = (inv y \<cdot> inv x) \<cdot> (x \<cdot> y)"
    by (simp add: m_assoc l_inv) (simp add: m_assoc [symmetric] l_inv)
  with G show ?thesis by (simp_all del: inv add: inv_closed)
qed


subsection {* Substructures *}

locale subgroup = var H + struct G + 
  assumes subset: "H \<subseteq> carrier(G)"
    and m_closed [intro, simp]: "\<lbrakk>x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> H"
    and  one_closed [simp]: "\<one> \<in> H"
    and m_inv_closed [intro,simp]: "x \<in> H \<Longrightarrow> inv x \<in> H"


lemma (in subgroup) mem_carrier [simp]:
  "x \<in> H \<Longrightarrow> x \<in> carrier(G)"
  using subset by blast


lemma subgroup_imp_subset:
  "subgroup(H,G) \<Longrightarrow> H \<subseteq> carrier(G)"
  by (rule subgroup.subset)

lemma (in subgroup) group_axiomsI [intro]:
  includes group G
  shows "group_axioms (update_carrier(G,H))"
by (force intro: group_axioms.intro l_inv r_inv) 

lemma (in subgroup) is_group [intro]:
  includes group G
  shows "group (update_carrier(G,H))"
  by (rule groupI) (auto intro: m_assoc l_inv mem_carrier)

text {*
  Since @{term H} is nonempty, it contains some element @{term x}.  Since
  it is closed under inverse, it contains @{text "inv x"}.  Since
  it is closed under product, it contains @{text "x \<cdot> inv x = \<one>"}.
*}

text {*
  Since @{term H} is nonempty, it contains some element @{term x}.  Since
  it is closed under inverse, it contains @{text "inv x"}.  Since
  it is closed under product, it contains @{text "x \<cdot> inv x = \<one>"}.
*}

lemma (in group) one_in_subset:
  "\<lbrakk>H \<subseteq> carrier(G); H \<noteq> 0; \<forall>a \<in> H. inv a \<in> H; \<forall>a\<in>H. \<forall>b\<in>H. a \<cdot> b \<in> H\<rbrakk>
   \<Longrightarrow> \<one> \<in> H"
by (force simp add: l_inv)

text {* A characterization of subgroups: closed, non-empty subset. *}

declare monoid.one_closed [simp] group.inv_closed [simp]
  monoid.l_one [simp] monoid.r_one [simp] group.inv_inv [simp]

lemma subgroup_nonempty:
  "~ subgroup(0,G)"
  by (blast dest: subgroup.one_closed)


subsection {* Direct Products *}

constdefs
  DirProdGroup :: "[i,i] => i"  (infixr "\<Otimes>" 80)
  "G \<Otimes> H == <carrier(G) \<times> carrier(H),
              (\<lambda><<g,h>, <g', h'>>
                   \<in> (carrier(G) \<times> carrier(H)) \<times> (carrier(G) \<times> carrier(H)).
                <g \<cdot>\<^bsub>G\<^esub> g', h \<cdot>\<^bsub>H\<^esub> h'>),
              <\<one>\<^bsub>G\<^esub>, \<one>\<^bsub>H\<^esub>>, 0>"

lemma DirProdGroup_group:
  includes group G + group H
  shows "group (G \<Otimes> H)"
by (force intro!: groupI G.m_assoc H.m_assoc G.l_inv H.l_inv
          simp add: DirProdGroup_def)

lemma carrier_DirProdGroup [simp]:
     "carrier (G \<Otimes> H) = carrier(G) \<times> carrier(H)"
  by (simp add: DirProdGroup_def)

lemma one_DirProdGroup [simp]:
     "\<one>\<^bsub>G \<Otimes> H\<^esub> = <\<one>\<^bsub>G\<^esub>, \<one>\<^bsub>H\<^esub>>"
  by (simp add: DirProdGroup_def)

lemma mult_DirProdGroup [simp]:
     "[|g \<in> carrier(G); h \<in> carrier(H); g' \<in> carrier(G); h' \<in> carrier(H)|]
      ==> <g, h> \<cdot>\<^bsub>G \<Otimes> H\<^esub> <g', h'> = <g \<cdot>\<^bsub>G\<^esub> g', h \<cdot>\<^bsub>H\<^esub> h'>"
by (simp add: DirProdGroup_def)

lemma inv_DirProdGroup [simp]:
  includes group G + group H
  assumes g: "g \<in> carrier(G)"
      and h: "h \<in> carrier(H)"
  shows "inv \<^bsub>G \<Otimes> H\<^esub> <g, h> = <inv\<^bsub>G\<^esub> g, inv\<^bsub>H\<^esub> h>"
  apply (rule group.inv_equality [OF DirProdGroup_group])
  apply (simp_all add: prems group_def group.l_inv)
  done

subsection {* Isomorphisms *}

constdefs
  hom :: "[i,i] => i"
  "hom(G,H) ==
    {h \<in> carrier(G) -> carrier(H).
      (\<forall>x \<in> carrier(G). \<forall>y \<in> carrier(G). h ` (x \<cdot>\<^bsub>G\<^esub> y) = (h ` x) \<cdot>\<^bsub>H\<^esub> (h ` y))}"

lemma hom_mult:
  "\<lbrakk>h \<in> hom(G,H); x \<in> carrier(G); y \<in> carrier(G)\<rbrakk>
   \<Longrightarrow> h ` (x \<cdot>\<^bsub>G\<^esub> y) = h ` x \<cdot>\<^bsub>H\<^esub> h ` y"
  by (simp add: hom_def)

lemma hom_closed:
  "\<lbrakk>h \<in> hom(G,H); x \<in> carrier(G)\<rbrakk> \<Longrightarrow> h ` x \<in> carrier(H)"
  by (auto simp add: hom_def)

lemma (in group) hom_compose:
     "\<lbrakk>h \<in> hom(G,H); i \<in> hom(H,I)\<rbrakk> \<Longrightarrow> i O h \<in> hom(G,I)"
by (force simp add: hom_def comp_fun) 

lemma hom_is_fun:
  "h \<in> hom(G,H) \<Longrightarrow> h \<in> carrier(G) -> carrier(H)"
  by (simp add: hom_def)


subsection {* Isomorphisms *}

constdefs
  iso :: "[i,i] => i"  (infixr "\<cong>" 60)
  "G \<cong> H == hom(G,H) \<inter> bij(carrier(G), carrier(H))"

lemma (in group) iso_refl: "id(carrier(G)) \<in> G \<cong> G"
by (simp add: iso_def hom_def id_type id_bij) 


lemma (in group) iso_sym:
     "h \<in> G \<cong> H \<Longrightarrow> converse(h) \<in> H \<cong> G"
apply (simp add: iso_def bij_converse_bij, clarify) 
apply (subgoal_tac "converse(h) \<in> carrier(H) \<rightarrow> carrier(G)") 
 prefer 2 apply (simp add: bij_converse_bij bij_is_fun) 
apply (auto intro: left_inverse_eq [of _ "carrier(G)" "carrier(H)"] 
            simp add: hom_def bij_is_inj right_inverse_bij); 
done

lemma (in group) iso_trans: 
     "\<lbrakk>h \<in> G \<cong> H; i \<in> H \<cong> I\<rbrakk> \<Longrightarrow> i O h \<in> G \<cong> I"
by (auto simp add: iso_def hom_compose comp_bij)

lemma DirProdGroup_commute_iso:
  includes group G + group H
  shows "(\<lambda><x,y> \<in> carrier(G \<Otimes> H). <y,x>) \<in> (G \<Otimes> H) \<cong> (H \<Otimes> G)"
by (auto simp add: iso_def hom_def inj_def surj_def bij_def) 

lemma DirProdGroup_assoc_iso:
  includes group G + group H + group I
  shows "(\<lambda><<x,y>,z> \<in> carrier((G \<Otimes> H) \<Otimes> I). <x,<y,z>>)
          \<in> ((G \<Otimes> H) \<Otimes> I) \<cong> (G \<Otimes> (H \<Otimes> I))"
by (auto intro: lam_type simp add: iso_def hom_def inj_def surj_def bij_def) 

text{*Basis for homomorphism proofs: we assume two groups @{term G} and
  @term{H}, with a homomorphism @{term h} between them*}
locale group_hom = group G + group H + var h +
  assumes homh: "h \<in> hom(G,H)"
  notes hom_mult [simp] = hom_mult [OF homh]
    and hom_closed [simp] = hom_closed [OF homh]
    and hom_is_fun [simp] = hom_is_fun [OF homh]

lemma (in group_hom) one_closed [simp]:
  "h ` \<one> \<in> carrier(H)"
  by simp

lemma (in group_hom) hom_one [simp]:
  "h ` \<one> = \<one>\<^bsub>H\<^esub>"
proof -
  have "h ` \<one> \<cdot>\<^bsub>H\<^esub> \<one>\<^bsub>H\<^esub> = (h ` \<one>) \<cdot>\<^bsub>H\<^esub> (h ` \<one>)"
    by (simp add: hom_mult [symmetric] del: hom_mult)
  then show ?thesis by (simp del: r_one)
qed

lemma (in group_hom) inv_closed [simp]:
  "x \<in> carrier(G) \<Longrightarrow> h ` (inv x) \<in> carrier(H)"
  by simp

lemma (in group_hom) hom_inv [simp]:
  "x \<in> carrier(G) \<Longrightarrow> h ` (inv x) = inv\<^bsub>H\<^esub> (h ` x)"
proof -
  assume x: "x \<in> carrier(G)"
  then have "h ` x \<cdot>\<^bsub>H\<^esub> h ` (inv x) = \<one>\<^bsub>H\<^esub>"
    by (simp add: hom_mult [symmetric] G.r_inv del: hom_mult)
  also from x have "... = h ` x \<cdot>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub> (h ` x)"
    by (simp add: hom_mult [symmetric] H.r_inv del: hom_mult)
  finally have "h ` x \<cdot>\<^bsub>H\<^esub> h ` (inv x) = h ` x \<cdot>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub> (h ` x)" .
  with x show ?thesis by (simp del: inv add: is_group)
qed

subsection {* Commutative Structures *}

text {*
  Naming convention: multiplicative structures that are commutative
  are called \emph{commutative}, additive structures are called
  \emph{Abelian}.
*}

subsection {* Definition *}

locale comm_monoid = monoid +
  assumes m_comm: "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk> \<Longrightarrow> x \<cdot> y = y \<cdot> x"

lemma (in comm_monoid) m_lcomm:
  "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G); z \<in> carrier(G)\<rbrakk> \<Longrightarrow>
   x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
proof -
  assume xyz: "x \<in> carrier(G)"  "y \<in> carrier(G)"  "z \<in> carrier(G)"
  from xyz have "x \<cdot> (y \<cdot> z) = (x \<cdot> y) \<cdot> z" by (simp add: m_assoc)
  also from xyz have "... = (y \<cdot> x) \<cdot> z" by (simp add: m_comm)
  also from xyz have "... = y \<cdot> (x \<cdot> z)" by (simp add: m_assoc)
  finally show ?thesis .
qed

lemmas (in comm_monoid) m_ac = m_assoc m_comm m_lcomm

locale comm_group = comm_monoid + group

lemma (in comm_group) inv_mult:
  "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk> \<Longrightarrow> inv (x \<cdot> y) = inv x \<cdot> inv y"
  by (simp add: m_ac inv_mult_group)


lemma (in group) subgroup_self: "subgroup (carrier(G),G)"
by (simp add: subgroup_def prems) 

lemma (in group) subgroup_imp_group:
  "subgroup(H,G) \<Longrightarrow> group (update_carrier(G,H))"
by (simp add: subgroup.is_group)

lemma (in group) subgroupI:
  assumes subset: "H \<subseteq> carrier(G)" and non_empty: "H \<noteq> 0"
    and inv: "!!a. a \<in> H ==> inv a \<in> H"
    and mult: "!!a b. [|a \<in> H; b \<in> H|] ==> a \<cdot> b \<in> H"
  shows "subgroup(H,G)"
proof (simp add: subgroup_def prems)
  show "\<one> \<in> H" by (rule one_in_subset) (auto simp only: prems)
qed


subsection {* Bijections of a Set, Permutation Groups, Automorphism Groups *}

constdefs
  BijGroup :: "i=>i"
  "BijGroup(S) ==
    <bij(S,S),
     \<lambda><g,f> \<in> bij(S,S) \<times> bij(S,S). g O f,
     id(S), 0>"


subsection {*Bijections Form a Group *}

theorem group_BijGroup: "group(BijGroup(S))"
apply (simp add: BijGroup_def)
apply (rule groupI) 
    apply (simp_all add: id_bij comp_bij comp_assoc) 
 apply (simp add: id_bij bij_is_fun left_comp_id [of _ S S] fun_is_rel)
apply (blast intro: left_comp_inverse bij_is_inj bij_converse_bij)
done


subsection{*Automorphisms Form a Group*}

lemma Bij_Inv_mem: "\<lbrakk>f \<in> bij(S,S);  x \<in> S\<rbrakk> \<Longrightarrow> converse(f) ` x \<in> S" 
by (blast intro: apply_funtype bij_is_fun bij_converse_bij)

lemma inv_BijGroup: "f \<in> bij(S,S) \<Longrightarrow> m_inv (BijGroup(S), f) = converse(f)"
apply (rule group.inv_equality)
apply (rule group_BijGroup)
apply (simp_all add: BijGroup_def bij_converse_bij 
          left_comp_inverse [OF bij_is_inj]) 
done

lemma iso_is_bij: "h \<in> G \<cong> H ==> h \<in> bij(carrier(G), carrier(H))"
by (simp add: iso_def)


constdefs
  auto :: "i=>i"
  "auto(G) == iso(G,G)"

  AutoGroup :: "i=>i"
  "AutoGroup(G) == update_carrier(BijGroup(carrier(G)), auto(G))"


lemma (in group) id_in_auto: "id(carrier(G)) \<in> auto(G)"
  by (simp add: iso_refl auto_def)

lemma (in group) subgroup_auto:
      "subgroup (auto(G)) (BijGroup (carrier(G)))"
proof (rule subgroup.intro)
  show "auto(G) \<subseteq> carrier (BijGroup (carrier(G)))"
    by (auto simp add: auto_def BijGroup_def iso_def)
next
  fix x y
  assume "x \<in> auto(G)" "y \<in> auto(G)" 
  thus "x \<cdot>\<^bsub>BijGroup (carrier(G))\<^esub> y \<in> auto(G)"
    by (auto simp add: BijGroup_def auto_def iso_def bij_is_fun 
                       group.hom_compose comp_bij)
next
  show "\<one>\<^bsub>BijGroup (carrier(G))\<^esub> \<in> auto(G)" by (simp add:  BijGroup_def id_in_auto)
next
  fix x 
  assume "x \<in> auto(G)" 
  thus "inv\<^bsub>BijGroup (carrier(G))\<^esub> x \<in> auto(G)"
    by (simp add: auto_def inv_BijGroup iso_is_bij iso_sym) 
qed

theorem (in group) AutoGroup: "group (AutoGroup(G))"
by (simp add: AutoGroup_def subgroup.is_group subgroup_auto group_BijGroup)



subsection{*Cosets and Quotient Groups*}

constdefs (structure G)
  r_coset  :: "[i,i,i] => i"    (infixl "#>\<index>" 60)
   "H #> a == \<Union>h\<in>H. {h \<cdot> a}"

  l_coset  :: "[i,i,i] => i"    (infixl "<#\<index>" 60)
   "a <# H == \<Union>h\<in>H. {a \<cdot> h}"

  RCOSETS  :: "[i,i] => i"          ("rcosets\<index> _" [81] 80)
   "rcosets H == \<Union>a\<in>carrier(G). {H #> a}"

  set_mult :: "[i,i,i] => i"    (infixl "<#>\<index>" 60)
   "H <#> K == \<Union>h\<in>H. \<Union>k\<in>K. {h \<cdot> k}"

  SET_INV  :: "[i,i] => i"  ("set'_inv\<index> _" [81] 80)
   "set_inv H == \<Union>h\<in>H. {inv h}"


locale normal = subgroup + group +
  assumes coset_eq: "(\<forall>x \<in> carrier(G). H #> x = x <# H)"


syntax
  "@normal" :: "[i,i] => i"  (infixl "\<lhd>" 60)

translations
  "H \<lhd> G" == "normal(H,G)"


subsection {*Basic Properties of Cosets*}

lemma (in group) coset_mult_assoc:
     "\<lbrakk>M \<subseteq> carrier(G); g \<in> carrier(G); h \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> (M #> g) #> h = M #> (g \<cdot> h)"
by (force simp add: r_coset_def m_assoc)

lemma (in group) coset_mult_one [simp]: "M \<subseteq> carrier(G) \<Longrightarrow> M #> \<one> = M"
by (force simp add: r_coset_def)

lemma (in group) solve_equation:
    "\<lbrakk>subgroup(H,G); x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> \<exists>h\<in>H. y = h \<cdot> x"
apply (rule bexI [of _ "y \<cdot> (inv x)"])
apply (auto simp add: subgroup.m_closed subgroup.m_inv_closed m_assoc
                      subgroup.subset [THEN subsetD])
done

lemma (in group) repr_independence:
     "\<lbrakk>y \<in> H #> x;  x \<in> carrier(G); subgroup(H,G)\<rbrakk> \<Longrightarrow> H #> x = H #> y"
by (auto simp add: r_coset_def m_assoc [symmetric]
                   subgroup.subset [THEN subsetD]
                   subgroup.m_closed solve_equation)

lemma (in group) coset_join2:
     "\<lbrakk>x \<in> carrier(G);  subgroup(H,G);  x\<in>H\<rbrakk> \<Longrightarrow> H #> x = H"
  --{*Alternative proof is to put @{term "x=\<one>"} in @{text repr_independence}.*}
by (force simp add: subgroup.m_closed r_coset_def solve_equation)

lemma (in group) r_coset_subset_G:
     "\<lbrakk>H \<subseteq> carrier(G); x \<in> carrier(G)\<rbrakk> \<Longrightarrow> H #> x \<subseteq> carrier(G)"
by (auto simp add: r_coset_def)

lemma (in group) rcosI:
     "\<lbrakk>h \<in> H; H \<subseteq> carrier(G); x \<in> carrier(G)\<rbrakk> \<Longrightarrow> h \<cdot> x \<in> H #> x"
by (auto simp add: r_coset_def)

lemma (in group) rcosetsI:
     "\<lbrakk>H \<subseteq> carrier(G); x \<in> carrier(G)\<rbrakk> \<Longrightarrow> H #> x \<in> rcosets H"
by (auto simp add: RCOSETS_def)


text{*Really needed?*}
lemma (in group) transpose_inv:
     "\<lbrakk>x \<cdot> y = z;  x \<in> carrier(G);  y \<in> carrier(G);  z \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> (inv x) \<cdot> z = y"
by (force simp add: m_assoc [symmetric])



subsection {* Normal subgroups *}

lemma normal_imp_subgroup: "H \<lhd> G ==> subgroup(H,G)"
  by (simp add: normal_def subgroup_def)

lemma (in group) normalI: 
  "subgroup(H,G) \<Longrightarrow> (\<forall>x \<in> carrier(G). H #> x = x <# H) \<Longrightarrow> H \<lhd> G";
apply (simp add: normal_def normal_axioms_def, auto) 
  by (blast intro: prems)

lemma (in normal) inv_op_closed1:
     "\<lbrakk>x \<in> carrier(G); h \<in> H\<rbrakk> \<Longrightarrow> (inv x) \<cdot> h \<cdot> x \<in> H"
apply (insert coset_eq) 
apply (auto simp add: l_coset_def r_coset_def)
apply (drule bspec, assumption)
apply (drule equalityD1 [THEN subsetD], blast, clarify)
apply (simp add: m_assoc)
apply (simp add: m_assoc [symmetric])
done

lemma (in normal) inv_op_closed2:
     "\<lbrakk>x \<in> carrier(G); h \<in> H\<rbrakk> \<Longrightarrow> x \<cdot> h \<cdot> (inv x) \<in> H"
apply (subgoal_tac "inv (inv x) \<cdot> h \<cdot> (inv x) \<in> H") 
apply simp 
apply (blast intro: inv_op_closed1) 
done

text{*Alternative characterization of normal subgroups*}
lemma (in group) normal_inv_iff:
     "(N \<lhd> G) <->
      (subgroup(N,G) & (\<forall>x \<in> carrier(G). \<forall>h \<in> N. x \<cdot> h \<cdot> (inv x) \<in> N))"
      (is "_ <-> ?rhs")
proof
  assume N: "N \<lhd> G"
  show ?rhs
    by (blast intro: N normal.inv_op_closed2 normal_imp_subgroup) 
next
  assume ?rhs
  hence sg: "subgroup(N,G)" 
    and closed: "\<And>x. x\<in>carrier(G) \<Longrightarrow> \<forall>h\<in>N. x \<cdot> h \<cdot> inv x \<in> N" by auto
  hence sb: "N \<subseteq> carrier(G)" by (simp add: subgroup.subset) 
  show "N \<lhd> G"
  proof (intro normalI [OF sg], simp add: l_coset_def r_coset_def, clarify)
    fix x
    assume x: "x \<in> carrier(G)"
    show "(\<Union>h\<in>N. {h \<cdot> x}) = (\<Union>h\<in>N. {x \<cdot> h})"
    proof
      show "(\<Union>h\<in>N. {h \<cdot> x}) \<subseteq> (\<Union>h\<in>N. {x \<cdot> h})"
      proof clarify
        fix n
        assume n: "n \<in> N" 
        show "n \<cdot> x \<in> (\<Union>h\<in>N. {x \<cdot> h})"
        proof (rule UN_I) 
          from closed [of "inv x"]
          show "inv x \<cdot> n \<cdot> x \<in> N" by (simp add: x n)
          show "n \<cdot> x \<in> {x \<cdot> (inv x \<cdot> n \<cdot> x)}"
            by (simp add: x n m_assoc [symmetric] sb [THEN subsetD])
        qed
      qed
    next
      show "(\<Union>h\<in>N. {x \<cdot> h}) \<subseteq> (\<Union>h\<in>N. {h \<cdot> x})"
      proof clarify
        fix n
        assume n: "n \<in> N" 
        show "x \<cdot> n \<in> (\<Union>h\<in>N. {h \<cdot> x})"
        proof (rule UN_I) 
          show "x \<cdot> n \<cdot> inv x \<in> N" by (simp add: x n closed)
          show "x \<cdot> n \<in> {x \<cdot> n \<cdot> inv x \<cdot> x}"
            by (simp add: x n m_assoc sb [THEN subsetD])
        qed
      qed
    qed
  qed
qed


subsection{*More Properties of Cosets*}

lemma (in group) l_coset_subset_G:
     "\<lbrakk>H \<subseteq> carrier(G); x \<in> carrier(G)\<rbrakk> \<Longrightarrow> x <# H \<subseteq> carrier(G)"
by (auto simp add: l_coset_def subsetD)

lemma (in group) l_coset_swap:
     "\<lbrakk>y \<in> x <# H;  x \<in> carrier(G);  subgroup(H,G)\<rbrakk> \<Longrightarrow> x \<in> y <# H"
proof (simp add: l_coset_def)
  assume "\<exists>h\<in>H. y = x \<cdot> h"
    and x: "x \<in> carrier(G)"
    and sb: "subgroup(H,G)"
  then obtain h' where h': "h' \<in> H & x \<cdot> h' = y" by blast
  show "\<exists>h\<in>H. x = y \<cdot> h"
  proof
    show "x = y \<cdot> inv h'" using h' x sb
      by (auto simp add: m_assoc subgroup.subset [THEN subsetD])
    show "inv h' \<in> H" using h' sb
      by (auto simp add: subgroup.subset [THEN subsetD] subgroup.m_inv_closed)
  qed
qed

lemma (in group) l_coset_carrier:
     "\<lbrakk>y \<in> x <# H;  x \<in> carrier(G);  subgroup(H,G)\<rbrakk> \<Longrightarrow> y \<in> carrier(G)"
by (auto simp add: l_coset_def m_assoc
                   subgroup.subset [THEN subsetD] subgroup.m_closed)

lemma (in group) l_repr_imp_subset:
  assumes y: "y \<in> x <# H" and x: "x \<in> carrier(G)" and sb: "subgroup(H,G)"
  shows "y <# H \<subseteq> x <# H"
proof -
  from y
  obtain h' where "h' \<in> H" "x \<cdot> h' = y" by (auto simp add: l_coset_def)
  thus ?thesis using x sb
    by (auto simp add: l_coset_def m_assoc
                       subgroup.subset [THEN subsetD] subgroup.m_closed)
qed

lemma (in group) l_repr_independence:
  assumes y: "y \<in> x <# H" and x: "x \<in> carrier(G)" and sb: "subgroup(H,G)"
  shows "x <# H = y <# H"
proof
  show "x <# H \<subseteq> y <# H"
    by (rule l_repr_imp_subset,
        (blast intro: l_coset_swap l_coset_carrier y x sb)+)
  show "y <# H \<subseteq> x <# H" by (rule l_repr_imp_subset [OF y x sb])
qed

lemma (in group) setmult_subset_G:
     "\<lbrakk>H \<subseteq> carrier(G); K \<subseteq> carrier(G)\<rbrakk> \<Longrightarrow> H <#> K \<subseteq> carrier(G)"
by (auto simp add: set_mult_def subsetD)

lemma (in group) subgroup_mult_id: "subgroup(H,G) \<Longrightarrow> H <#> H = H"
apply (rule equalityI) 
apply (auto simp add: subgroup.m_closed set_mult_def Sigma_def image_def)
apply (rule_tac x = x in bexI)
apply (rule bexI [of _ "\<one>"])
apply (auto simp add: subgroup.m_closed subgroup.one_closed
                      r_one subgroup.subset [THEN subsetD])
done


subsubsection {* Set of inverses of an @{text r_coset}. *}

lemma (in normal) rcos_inv:
  assumes x:     "x \<in> carrier(G)"
  shows "set_inv (H #> x) = H #> (inv x)" 
proof (simp add: r_coset_def SET_INV_def x inv_mult_group, safe intro!: equalityI)
  fix h
  assume "h \<in> H"
  show "inv x \<cdot> inv h \<in> (\<Union>j\<in>H. {j \<cdot> inv x})"
  proof (rule UN_I)
    show "inv x \<cdot> inv h \<cdot> x \<in> H"
      by (simp add: inv_op_closed1 prems)
    show "inv x \<cdot> inv h \<in> {inv x \<cdot> inv h \<cdot> x \<cdot> inv x}"
      by (simp add: prems m_assoc)
  qed
next
  fix h
  assume "h \<in> H"
  show "h \<cdot> inv x \<in> (\<Union>j\<in>H. {inv x \<cdot> inv j})"
  proof (rule UN_I)
    show "x \<cdot> inv h \<cdot> inv x \<in> H"
      by (simp add: inv_op_closed2 prems)
    show "h \<cdot> inv x \<in> {inv x \<cdot> inv (x \<cdot> inv h \<cdot> inv x)}"
      by (simp add: prems m_assoc [symmetric] inv_mult_group)
  qed
qed



subsubsection {*Theorems for @{text "<#>"} with @{text "#>"} or @{text "<#"}.*}

lemma (in group) setmult_rcos_assoc:
     "\<lbrakk>H \<subseteq> carrier(G); K \<subseteq> carrier(G); x \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> H <#> (K #> x) = (H <#> K) #> x"
by (force simp add: r_coset_def set_mult_def m_assoc)

lemma (in group) rcos_assoc_lcos:
     "\<lbrakk>H \<subseteq> carrier(G); K \<subseteq> carrier(G); x \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> (H #> x) <#> K = H <#> (x <# K)"
by (force simp add: r_coset_def l_coset_def set_mult_def m_assoc)

lemma (in normal) rcos_mult_step1:
     "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> (H #> x) <#> (H #> y) = (H <#> (x <# H)) #> y"
by (simp add: setmult_rcos_assoc subset
              r_coset_subset_G l_coset_subset_G rcos_assoc_lcos)

lemma (in normal) rcos_mult_step2:
     "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> (H <#> (x <# H)) #> y = (H <#> (H #> x)) #> y"
by (insert coset_eq, simp add: normal_def)

lemma (in normal) rcos_mult_step3:
     "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> (H <#> (H #> x)) #> y = H #> (x \<cdot> y)"
by (simp add: setmult_rcos_assoc coset_mult_assoc
              subgroup_mult_id subset prems)

lemma (in normal) rcos_sum:
     "\<lbrakk>x \<in> carrier(G); y \<in> carrier(G)\<rbrakk>
      \<Longrightarrow> (H #> x) <#> (H #> y) = H #> (x \<cdot> y)"
by (simp add: rcos_mult_step1 rcos_mult_step2 rcos_mult_step3)

lemma (in normal) rcosets_mult_eq: "M \<in> rcosets H \<Longrightarrow> H <#> M = M"
  -- {* generalizes @{text subgroup_mult_id} *}
  by (auto simp add: RCOSETS_def subset
        setmult_rcos_assoc subgroup_mult_id prems)


subsubsection{*Two distinct right cosets are disjoint*}

constdefs (structure G)
  r_congruent :: "[i,i] => i" ("rcong\<index> _" [60] 60)
   "rcong H == {<x,y> \<in> carrier(G) * carrier(G). inv x \<cdot> y \<in> H}"


lemma (in subgroup) equiv_rcong:
   includes group G
   shows "equiv (carrier(G), rcong H)"
proof (simp add: equiv_def, intro conjI)
  show "rcong H \<subseteq> carrier(G) \<times> carrier(G)"
    by (auto simp add: r_congruent_def) 
next
  show "refl (carrier(G), rcong H)"
    by (auto simp add: r_congruent_def refl_def) 
next
  show "sym (rcong H)"
  proof (simp add: r_congruent_def sym_def, clarify)
    fix x y
    assume [simp]: "x \<in> carrier(G)" "y \<in> carrier(G)" 
       and "inv x \<cdot> y \<in> H"
    hence "inv (inv x \<cdot> y) \<in> H" by (simp add: m_inv_closed) 
    thus "inv y \<cdot> x \<in> H" by (simp add: inv_mult_group)
  qed
next
  show "trans (rcong H)"
  proof (simp add: r_congruent_def trans_def, clarify)
    fix x y z
    assume [simp]: "x \<in> carrier(G)" "y \<in> carrier(G)" "z \<in> carrier(G)"
       and "inv x \<cdot> y \<in> H" and "inv y \<cdot> z \<in> H"
    hence "(inv x \<cdot> y) \<cdot> (inv y \<cdot> z) \<in> H" by simp
    hence "inv x \<cdot> (y \<cdot> inv y) \<cdot> z \<in> H" by (simp add: m_assoc del: inv) 
    thus "inv x \<cdot> z \<in> H" by simp
  qed
qed

text{*Equivalence classes of @{text rcong} correspond to left cosets.
  Was there a mistake in the definitions? I'd have expected them to
  correspond to right cosets.*}
lemma (in subgroup) l_coset_eq_rcong:
  includes group G
  assumes a: "a \<in> carrier(G)"
  shows "a <# H = (rcong H) `` {a}" 
by (force simp add: r_congruent_def l_coset_def m_assoc [symmetric] a
                Collect_image_eq) 


lemma (in group) rcos_equation:
  includes subgroup H G
  shows
     "\<lbrakk>ha \<cdot> a = h \<cdot> b; a \<in> carrier(G);  b \<in> carrier(G);  
        h \<in> H;  ha \<in> H;  hb \<in> H\<rbrakk>
      \<Longrightarrow> hb \<cdot> a \<in> (\<Union>h\<in>H. {h \<cdot> b})"
apply (rule UN_I [of "hb \<cdot> ((inv ha) \<cdot> h)"], simp)
apply (simp add: m_assoc transpose_inv)
done


lemma (in group) rcos_disjoint:
  includes subgroup H G
  shows "\<lbrakk>a \<in> rcosets H; b \<in> rcosets H; a\<noteq>b\<rbrakk> \<Longrightarrow> a \<inter> b = 0"
apply (simp add: RCOSETS_def r_coset_def)
apply (blast intro: rcos_equation prems sym)
done


subsection {*Order of a Group and Lagrange's Theorem*}

constdefs
  order :: "i => i"
  "order(S) == |carrier(S)|"

lemma (in group) rcos_self:
  includes subgroup
  shows "x \<in> carrier(G) \<Longrightarrow> x \<in> H #> x"
apply (simp add: r_coset_def)
apply (rule_tac x="\<one>" in bexI, auto) 
done

lemma (in group) rcosets_part_G:
  includes subgroup
  shows "\<Union>(rcosets H) = carrier(G)"
apply (rule equalityI)
 apply (force simp add: RCOSETS_def r_coset_def)
apply (auto simp add: RCOSETS_def intro: rcos_self prems)
done

lemma (in group) cosets_finite:
     "\<lbrakk>c \<in> rcosets H;  H \<subseteq> carrier(G);  Finite (carrier(G))\<rbrakk> \<Longrightarrow> Finite(c)"
apply (auto simp add: RCOSETS_def)
apply (simp add: r_coset_subset_G [THEN subset_Finite])
done

text{*More general than the HOL version, which also requires @{term G} to
      be finite.*}
lemma (in group) card_cosets_equal:
  assumes H:   "H \<subseteq> carrier(G)"
  shows "c \<in> rcosets H \<Longrightarrow> |c| = |H|"
proof (simp add: RCOSETS_def, clarify)
  fix a
  assume a: "a \<in> carrier(G)"
  show "|H #> a| = |H|"
  proof (rule eqpollI [THEN cardinal_cong])
    show "H #> a \<lesssim> H"
    proof (simp add: lepoll_def, intro exI) 
      show "(\<lambda>y \<in> H#>a. y \<cdot> inv a) \<in> inj(H #> a, H)"
        by (auto intro: lam_type 
                 simp add: inj_def r_coset_def m_assoc subsetD [OF H] a)
    qed
    show "H \<lesssim> H #> a"
    proof (simp add: lepoll_def, intro exI) 
      show "(\<lambda>y\<in> H. y \<cdot> a) \<in> inj(H, H #> a)"
        by (auto intro: lam_type 
                 simp add: inj_def r_coset_def  subsetD [OF H] a)
    qed
  qed
qed


lemma (in group) rcosets_subset_PowG:
     "subgroup(H,G) \<Longrightarrow> rcosets H \<subseteq> Pow(carrier(G))"
apply (simp add: RCOSETS_def)
apply (blast dest: r_coset_subset_G subgroup.subset)
done

theorem (in group) lagrange:
     "\<lbrakk>Finite(carrier(G)); subgroup(H,G)\<rbrakk>
      \<Longrightarrow> |rcosets H| #* |H| = order(G)"
apply (simp (no_asm_simp) add: order_def rcosets_part_G [symmetric])
apply (subst mult_commute)
apply (rule card_partition)
   apply (simp add: rcosets_subset_PowG [THEN subset_Finite])
  apply (simp add: rcosets_part_G)
 apply (simp add: card_cosets_equal [OF subgroup.subset])
apply (simp add: rcos_disjoint)
done


subsection {*Quotient Groups: Factorization of a Group*}

constdefs (structure G)
  FactGroup :: "[i,i] => i" (infixl "Mod" 65)
    --{*Actually defined for groups rather than monoids*}
  "G Mod H == 
     <rcosets\<^bsub>G\<^esub> H, \<lambda><K1,K2> \<in> (rcosets\<^bsub>G\<^esub> H) \<times> (rcosets\<^bsub>G\<^esub> H). K1 <#> K2, H, 0>"

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
  includes group G
  shows "H \<in> rcosets H"
proof -
  have "H #> \<one> = H"
    by (rule coset_join2, auto)
  then show ?thesis
    by (auto simp add: RCOSETS_def intro: sym)
qed

lemma (in normal) rcosets_inv_mult_group_eq:
     "M \<in> rcosets H \<Longrightarrow> set_inv M <#> M = H"
by (auto simp add: RCOSETS_def rcos_inv rcos_sum subgroup.subset prems)

theorem (in normal) factorgroup_is_group:
  "group (G Mod H)"
apply (simp add: FactGroup_def)
apply (rule groupI)
    apply (simp add: setmult_closed)
   apply (simp add: normal_imp_subgroup subgroup_in_rcosets)
  apply (simp add: setmult_closed rcosets_assoc)
 apply (simp add: normal_imp_subgroup
                  subgroup_in_rcosets rcosets_mult_eq)
apply (auto dest: rcosets_inv_mult_group_eq simp add: setinv_closed)
done

lemma (in normal) inv_FactGroup:
     "X \<in> carrier (G Mod H) \<Longrightarrow> inv\<^bsub>G Mod H\<^esub> X = set_inv X"
apply (rule group.inv_equality [OF factorgroup_is_group]) 
apply (simp_all add: FactGroup_def setinv_closed rcosets_inv_mult_group_eq)
done

text{*The coset map is a homomorphism from @{term G} to the quotient group
  @{term "G Mod H"}*}
lemma (in normal) r_coset_hom_Mod:
  "(\<lambda>a \<in> carrier(G). H #> a) \<in> hom(G, G Mod H)"
by (auto simp add: FactGroup_def RCOSETS_def hom_def rcos_sum intro: lam_type) 


subsection{*The First Isomorphism Theorem*}

text{*The quotient by the kernel of a homomorphism is isomorphic to the 
  range of that homomorphism.*}

constdefs
  kernel :: "[i,i,i] => i" 
    --{*the kernel of a homomorphism*}
  "kernel(G,H,h) == {x \<in> carrier(G). h ` x = \<one>\<^bsub>H\<^esub>}";

lemma (in group_hom) subgroup_kernel: "subgroup (kernel(G,H,h), G)"
apply (rule subgroup.intro) 
apply (auto simp add: kernel_def group.intro prems) 
done

text{*The kernel of a homomorphism is a normal subgroup*}
lemma (in group_hom) normal_kernel: "(kernel(G,H,h)) \<lhd> G"
apply (simp add: group.normal_inv_iff subgroup_kernel group.intro prems)
apply (simp add: kernel_def)  
done

lemma (in group_hom) FactGroup_nonempty:
  assumes X: "X \<in> carrier (G Mod kernel(G,H,h))"
  shows "X \<noteq> 0"
proof -
  from X
  obtain g where "g \<in> carrier(G)" 
             and "X = kernel(G,H,h) #> g"
    by (auto simp add: FactGroup_def RCOSETS_def)
  thus ?thesis 
   by (auto simp add: kernel_def r_coset_def image_def intro: hom_one)
qed


lemma (in group_hom) FactGroup_contents_mem:
  assumes X: "X \<in> carrier (G Mod (kernel(G,H,h)))"
  shows "contents (h``X) \<in> carrier(H)"
proof -
  from X
  obtain g where g: "g \<in> carrier(G)" 
             and "X = kernel(G,H,h) #> g"
    by (auto simp add: FactGroup_def RCOSETS_def)
  hence "h `` X = {h ` g}"
    by (auto simp add: kernel_def r_coset_def image_UN 
                       image_eq_UN [OF hom_is_fun] g)
  thus ?thesis by (auto simp add: g)
qed

lemma mult_FactGroup:
     "[|X \<in> carrier(G Mod H); X' \<in> carrier(G Mod H)|] 
      ==> X \<cdot>\<^bsub>(G Mod H)\<^esub> X' = X <#>\<^bsub>G\<^esub> X'"
by (simp add: FactGroup_def) 

lemma (in normal) FactGroup_m_closed:
     "[|X \<in> carrier(G Mod H); X' \<in> carrier(G Mod H)|] 
      ==> X <#>\<^bsub>G\<^esub> X' \<in> carrier(G Mod H)"
by (simp add: FactGroup_def setmult_closed) 

lemma (in group_hom) FactGroup_hom:
     "(\<lambda>X \<in> carrier(G Mod (kernel(G,H,h))). contents (h``X))
      \<in> hom (G Mod (kernel(G,H,h)), H)" 
proof (simp add: hom_def FactGroup_contents_mem lam_type mult_FactGroup normal.FactGroup_m_closed [OF normal_kernel], intro ballI)  
  fix X and X'
  assume X:  "X  \<in> carrier (G Mod kernel(G,H,h))"
     and X': "X' \<in> carrier (G Mod kernel(G,H,h))"
  then
  obtain g and g'
           where "g \<in> carrier(G)" and "g' \<in> carrier(G)" 
             and "X = kernel(G,H,h) #> g" and "X' = kernel(G,H,h) #> g'"
    by (auto simp add: FactGroup_def RCOSETS_def)
  hence all: "\<forall>x\<in>X. h ` x = h ` g" "\<forall>x\<in>X'. h ` x = h ` g'" 
    and Xsub: "X \<subseteq> carrier(G)" and X'sub: "X' \<subseteq> carrier(G)"
    by (force simp add: kernel_def r_coset_def image_def)+
  hence "h `` (X <#> X') = {h ` g \<cdot>\<^bsub>H\<^esub> h ` g'}" using X X'
    by (auto dest!: FactGroup_nonempty
             simp add: set_mult_def image_eq_UN [OF hom_is_fun] image_UN
                       subsetD [OF Xsub] subsetD [OF X'sub]) 
  thus "contents (h `` (X <#> X')) = contents (h `` X) \<cdot>\<^bsub>H\<^esub> contents (h `` X')"
    by (simp add: all image_eq_UN [OF hom_is_fun] FactGroup_nonempty 
                  X X' Xsub X'sub)
qed


text{*Lemma for the following injectivity result*}
lemma (in group_hom) FactGroup_subset:
     "\<lbrakk>g \<in> carrier(G); g' \<in> carrier(G); h ` g = h ` g'\<rbrakk>
      \<Longrightarrow>  kernel(G,H,h) #> g \<subseteq> kernel(G,H,h) #> g'"
apply (clarsimp simp add: kernel_def r_coset_def image_def)
apply (rename_tac y)  
apply (rule_tac x="y \<cdot> g \<cdot> inv g'" in bexI) 
apply (simp_all add: G.m_assoc) 
done

lemma (in group_hom) FactGroup_inj:
     "(\<lambda>X\<in>carrier (G Mod kernel(G,H,h)). contents (h `` X))
      \<in> inj(carrier (G Mod kernel(G,H,h)), carrier(H))"
proof (simp add: inj_def FactGroup_contents_mem lam_type, clarify) 
  fix X and X'
  assume X:  "X  \<in> carrier (G Mod kernel(G,H,h))"
     and X': "X' \<in> carrier (G Mod kernel(G,H,h))"
  then
  obtain g and g'
           where gX: "g \<in> carrier(G)"  "g' \<in> carrier(G)" 
              "X = kernel(G,H,h) #> g" "X' = kernel(G,H,h) #> g'"
    by (auto simp add: FactGroup_def RCOSETS_def)
  hence all: "\<forall>x\<in>X. h ` x = h ` g" "\<forall>x\<in>X'. h ` x = h ` g'"
    and Xsub: "X \<subseteq> carrier(G)" and X'sub: "X' \<subseteq> carrier(G)"
    by (force simp add: kernel_def r_coset_def image_def)+
  assume "contents (h `` X) = contents (h `` X')"
  hence h: "h ` g = h ` g'"
    by (simp add: all image_eq_UN [OF hom_is_fun] FactGroup_nonempty 
                  X X' Xsub X'sub)
  show "X=X'" by (rule equalityI) (simp_all add: FactGroup_subset h gX) 
qed


lemma (in group_hom) kernel_rcoset_subset:
  assumes g: "g \<in> carrier(G)"
  shows "kernel(G,H,h) #> g \<subseteq> carrier (G)"
    by (auto simp add: g kernel_def r_coset_def) 



text{*If the homomorphism @{term h} is onto @{term H}, then so is the
homomorphism from the quotient group*}
lemma (in group_hom) FactGroup_surj:
  assumes h: "h \<in> surj(carrier(G), carrier(H))"
  shows "(\<lambda>X\<in>carrier (G Mod kernel(G,H,h)). contents (h `` X))
         \<in> surj(carrier (G Mod kernel(G,H,h)), carrier(H))"
proof (simp add: surj_def FactGroup_contents_mem lam_type, clarify)
  fix y
  assume y: "y \<in> carrier(H)"
  with h obtain g where g: "g \<in> carrier(G)" "h ` g = y"
    by (auto simp add: surj_def) 
  hence "(\<Union>x\<in>kernel(G,H,h) #> g. {h ` x}) = {y}" 
    by (auto simp add: y kernel_def r_coset_def) 
  with g show "\<exists>x\<in>carrier(G Mod kernel(G, H, h)). contents(h `` x) = y"
        --{*The witness is @{term "kernel(G,H,h) #> g"}*}
    by (force simp add: FactGroup_def RCOSETS_def 
           image_eq_UN [OF hom_is_fun] kernel_rcoset_subset)
qed


text{*If @{term h} is a homomorphism from @{term G} onto @{term H}, then the
 quotient group @{term "G Mod (kernel(G,H,h))"} is isomorphic to @{term H}.*}
theorem (in group_hom) FactGroup_iso:
  "h \<in> surj(carrier(G), carrier(H))
   \<Longrightarrow> (\<lambda>X\<in>carrier (G Mod kernel(G,H,h)). contents (h``X)) \<in> (G Mod (kernel(G,H,h))) \<cong> H"
by (simp add: iso_def FactGroup_hom FactGroup_inj bij_def FactGroup_surj)
 
end
