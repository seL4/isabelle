(*  Title:      HOL/Finite_Set.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Lawrence C Paulson and Markus Wenzel
                Additions by Jeremy Avigad in Feb 2004
*)

header {* Finite sets *}

theory Finite_Set
imports Power Inductive Lattice_Locales
begin

subsection {* Definition and basic properties *}

consts Finites :: "'a set set"
syntax
  finite :: "'a set => bool"
translations
  "finite A" == "A : Finites"

inductive Finites
  intros
    emptyI [simp, intro!]: "{} : Finites"
    insertI [simp, intro!]: "A : Finites ==> insert a A : Finites"

axclass finite \<subseteq> type
  finite: "finite UNIV"

lemma ex_new_if_finite: -- "does not depend on def of finite at all"
  assumes "\<not> finite (UNIV :: 'a set)" and "finite A"
  shows "\<exists>a::'a. a \<notin> A"
proof -
  from prems have "A \<noteq> UNIV" by blast
  thus ?thesis by blast
qed

lemma finite_induct [case_names empty insert, induct set: Finites]:
  "finite F ==>
    P {} ==> (!!x F. finite F ==> x \<notin> F ==> P F ==> P (insert x F)) ==> P F"
  -- {* Discharging @{text "x \<notin> F"} entails extra work. *}
proof -
  assume "P {}" and
    insert: "!!x F. finite F ==> x \<notin> F ==> P F ==> P (insert x F)"
  assume "finite F"
  thus "P F"
  proof induct
    show "P {}" .
    fix x F assume F: "finite F" and P: "P F"
    show "P (insert x F)"
    proof cases
      assume "x \<in> F"
      hence "insert x F = F" by (rule insert_absorb)
      with P show ?thesis by (simp only:)
    next
      assume "x \<notin> F"
      from F this P show ?thesis by (rule insert)
    qed
  qed
qed

lemma finite_ne_induct[case_names singleton insert, consumes 2]:
assumes fin: "finite F" shows "F \<noteq> {} \<Longrightarrow>
 \<lbrakk> \<And>x. P{x};
   \<And>x F. \<lbrakk> finite F; F \<noteq> {}; x \<notin> F; P F \<rbrakk> \<Longrightarrow> P (insert x F) \<rbrakk>
 \<Longrightarrow> P F"
using fin
proof induct
  case empty thus ?case by simp
next
  case (insert x F)
  show ?case
  proof cases
    assume "F = {}" thus ?thesis using insert(4) by simp
  next
    assume "F \<noteq> {}" thus ?thesis using insert by blast
  qed
qed

lemma finite_subset_induct [consumes 2, case_names empty insert]:
  "finite F ==> F \<subseteq> A ==>
    P {} ==> (!!a F. finite F ==> a \<in> A ==> a \<notin> F ==> P F ==> P (insert a F)) ==>
    P F"
proof -
  assume "P {}" and insert:
    "!!a F. finite F ==> a \<in> A ==> a \<notin> F ==> P F ==> P (insert a F)"
  assume "finite F"
  thus "F \<subseteq> A ==> P F"
  proof induct
    show "P {}" .
    fix x F assume "finite F" and "x \<notin> F"
      and P: "F \<subseteq> A ==> P F" and i: "insert x F \<subseteq> A"
    show "P (insert x F)"
    proof (rule insert)
      from i show "x \<in> A" by blast
      from i have "F \<subseteq> A" by blast
      with P show "P F" .
    qed
  qed
qed

text{* Finite sets are the images of initial segments of natural numbers: *}

lemma finite_imp_nat_seg_image_inj_on:
  assumes fin: "finite A" 
  shows "\<exists> (n::nat) f. A = f ` {i. i<n} & inj_on f {i. i<n}"
using fin
proof induct
  case empty
  show ?case  
  proof show "\<exists>f. {} = f ` {i::nat. i < 0} & inj_on f {i. i<0}" by simp 
  qed
next
  case (insert a A)
  have notinA: "a \<notin> A" .
  from insert.hyps obtain n f
    where "A = f ` {i::nat. i < n}" "inj_on f {i. i < n}" by blast
  hence "insert a A = f(n:=a) ` {i. i < Suc n}"
        "inj_on (f(n:=a)) {i. i < Suc n}" using notinA
    by (auto simp add: image_def Ball_def inj_on_def less_Suc_eq)
  thus ?case by blast
qed

lemma nat_seg_image_imp_finite:
  "!!f A. A = f ` {i::nat. i<n} \<Longrightarrow> finite A"
proof (induct n)
  case 0 thus ?case by simp
next
  case (Suc n)
  let ?B = "f ` {i. i < n}"
  have finB: "finite ?B" by(rule Suc.hyps[OF refl])
  show ?case
  proof cases
    assume "\<exists>k<n. f n = f k"
    hence "A = ?B" using Suc.prems by(auto simp:less_Suc_eq)
    thus ?thesis using finB by simp
  next
    assume "\<not>(\<exists> k<n. f n = f k)"
    hence "A = insert (f n) ?B" using Suc.prems by(auto simp:less_Suc_eq)
    thus ?thesis using finB by simp
  qed
qed

lemma finite_conv_nat_seg_image:
  "finite A = (\<exists> (n::nat) f. A = f ` {i::nat. i<n})"
by(blast intro: nat_seg_image_imp_finite dest: finite_imp_nat_seg_image_inj_on)

subsubsection{* Finiteness and set theoretic constructions *}

lemma finite_UnI: "finite F ==> finite G ==> finite (F Un G)"
  -- {* The union of two finite sets is finite. *}
  by (induct set: Finites) simp_all

lemma finite_subset: "A \<subseteq> B ==> finite B ==> finite A"
  -- {* Every subset of a finite set is finite. *}
proof -
  assume "finite B"
  thus "!!A. A \<subseteq> B ==> finite A"
  proof induct
    case empty
    thus ?case by simp
  next
    case (insert x F A)
    have A: "A \<subseteq> insert x F" and r: "A - {x} \<subseteq> F ==> finite (A - {x})" .
    show "finite A"
    proof cases
      assume x: "x \<in> A"
      with A have "A - {x} \<subseteq> F" by (simp add: subset_insert_iff)
      with r have "finite (A - {x})" .
      hence "finite (insert x (A - {x}))" ..
      also have "insert x (A - {x}) = A" by (rule insert_Diff)
      finally show ?thesis .
    next
      show "A \<subseteq> F ==> ?thesis" .
      assume "x \<notin> A"
      with A show "A \<subseteq> F" by (simp add: subset_insert_iff)
    qed
  qed
qed

lemma finite_Un [iff]: "finite (F Un G) = (finite F & finite G)"
  by (blast intro: finite_subset [of _ "X Un Y", standard] finite_UnI)

lemma finite_Int [simp, intro]: "finite F | finite G ==> finite (F Int G)"
  -- {* The converse obviously fails. *}
  by (blast intro: finite_subset)

lemma finite_insert [simp]: "finite (insert a A) = finite A"
  apply (subst insert_is_Un)
  apply (simp only: finite_Un, blast)
  done

lemma finite_Union[simp, intro]:
 "\<lbrakk> finite A; !!M. M \<in> A \<Longrightarrow> finite M \<rbrakk> \<Longrightarrow> finite(\<Union>A)"
by (induct rule:finite_induct) simp_all

lemma finite_empty_induct:
  "finite A ==>
  P A ==> (!!a A. finite A ==> a:A ==> P A ==> P (A - {a})) ==> P {}"
proof -
  assume "finite A"
    and "P A" and "!!a A. finite A ==> a:A ==> P A ==> P (A - {a})"
  have "P (A - A)"
  proof -
    fix c b :: "'a set"
    presume c: "finite c" and b: "finite b"
      and P1: "P b" and P2: "!!x y. finite y ==> x \<in> y ==> P y ==> P (y - {x})"
    from c show "c \<subseteq> b ==> P (b - c)"
    proof induct
      case empty
      from P1 show ?case by simp
    next
      case (insert x F)
      have "P (b - F - {x})"
      proof (rule P2)
        from _ b show "finite (b - F)" by (rule finite_subset) blast
        from insert show "x \<in> b - F" by simp
        from insert show "P (b - F)" by simp
      qed
      also have "b - F - {x} = b - insert x F" by (rule Diff_insert [symmetric])
      finally show ?case .
    qed
  next
    show "A \<subseteq> A" ..
  qed
  thus "P {}" by simp
qed

lemma finite_Diff [simp]: "finite B ==> finite (B - Ba)"
  by (rule Diff_subset [THEN finite_subset])

lemma finite_Diff_insert [iff]: "finite (A - insert a B) = finite (A - B)"
  apply (subst Diff_insert)
  apply (case_tac "a : A - B")
   apply (rule finite_insert [symmetric, THEN trans])
   apply (subst insert_Diff, simp_all)
  done


text {* Image and Inverse Image over Finite Sets *}

lemma finite_imageI[simp]: "finite F ==> finite (h ` F)"
  -- {* The image of a finite set is finite. *}
  by (induct set: Finites) simp_all

lemma finite_surj: "finite A ==> B <= f ` A ==> finite B"
  apply (frule finite_imageI)
  apply (erule finite_subset, assumption)
  done

lemma finite_range_imageI:
    "finite (range g) ==> finite (range (%x. f (g x)))"
  apply (drule finite_imageI, simp)
  done

lemma finite_imageD: "finite (f`A) ==> inj_on f A ==> finite A"
proof -
  have aux: "!!A. finite (A - {}) = finite A" by simp
  fix B :: "'a set"
  assume "finite B"
  thus "!!A. f`A = B ==> inj_on f A ==> finite A"
    apply induct
     apply simp
    apply (subgoal_tac "EX y:A. f y = x & F = f ` (A - {y})")
     apply clarify
     apply (simp (no_asm_use) add: inj_on_def)
     apply (blast dest!: aux [THEN iffD1], atomize)
    apply (erule_tac V = "ALL A. ?PP (A)" in thin_rl)
    apply (frule subsetD [OF equalityD2 insertI1], clarify)
    apply (rule_tac x = xa in bexI)
     apply (simp_all add: inj_on_image_set_diff)
    done
qed (rule refl)


lemma inj_vimage_singleton: "inj f ==> f-`{a} \<subseteq> {THE x. f x = a}"
  -- {* The inverse image of a singleton under an injective function
         is included in a singleton. *}
  apply (auto simp add: inj_on_def)
  apply (blast intro: the_equality [symmetric])
  done

lemma finite_vimageI: "[|finite F; inj h|] ==> finite (h -` F)"
  -- {* The inverse image of a finite set under an injective function
         is finite. *}
  apply (induct set: Finites, simp_all)
  apply (subst vimage_insert)
  apply (simp add: finite_Un finite_subset [OF inj_vimage_singleton])
  done


text {* The finite UNION of finite sets *}

lemma finite_UN_I: "finite A ==> (!!a. a:A ==> finite (B a)) ==> finite (UN a:A. B a)"
  by (induct set: Finites) simp_all

text {*
  Strengthen RHS to
  @{prop "((ALL x:A. finite (B x)) & finite {x. x:A & B x \<noteq> {}})"}?

  We'd need to prove
  @{prop "finite C ==> ALL A B. (UNION A B) <= C --> finite {x. x:A & B x \<noteq> {}}"}
  by induction. *}

lemma finite_UN [simp]: "finite A ==> finite (UNION A B) = (ALL x:A. finite (B x))"
  by (blast intro: finite_UN_I finite_subset)


text {* Sigma of finite sets *}

lemma finite_SigmaI [simp]:
    "finite A ==> (!!a. a:A ==> finite (B a)) ==> finite (SIGMA a:A. B a)"
  by (unfold Sigma_def) (blast intro!: finite_UN_I)

lemma finite_cartesian_product: "[| finite A; finite B |] ==>
    finite (A <*> B)"
  by (rule finite_SigmaI)

lemma finite_Prod_UNIV:
    "finite (UNIV::'a set) ==> finite (UNIV::'b set) ==> finite (UNIV::('a * 'b) set)"
  apply (subgoal_tac "(UNIV:: ('a * 'b) set) = Sigma UNIV (%x. UNIV)")
   apply (erule ssubst)
   apply (erule finite_SigmaI, auto)
  done

lemma finite_cartesian_productD1:
     "[| finite (A <*> B); B \<noteq> {} |] ==> finite A"
apply (auto simp add: finite_conv_nat_seg_image) 
apply (drule_tac x=n in spec) 
apply (drule_tac x="fst o f" in spec) 
apply (auto simp add: o_def) 
 prefer 2 apply (force dest!: equalityD2) 
apply (drule equalityD1) 
apply (rename_tac y x)
apply (subgoal_tac "\<exists>k. k<n & f k = (x,y)") 
 prefer 2 apply force
apply clarify
apply (rule_tac x=k in image_eqI, auto)
done

lemma finite_cartesian_productD2:
     "[| finite (A <*> B); A \<noteq> {} |] ==> finite B"
apply (auto simp add: finite_conv_nat_seg_image) 
apply (drule_tac x=n in spec) 
apply (drule_tac x="snd o f" in spec) 
apply (auto simp add: o_def) 
 prefer 2 apply (force dest!: equalityD2) 
apply (drule equalityD1)
apply (rename_tac x y)
apply (subgoal_tac "\<exists>k. k<n & f k = (x,y)") 
 prefer 2 apply force
apply clarify
apply (rule_tac x=k in image_eqI, auto)
done


instance unit :: finite
proof
  have "finite {()}" by simp
  also have "{()} = UNIV" by auto
  finally show "finite (UNIV :: unit set)" .
qed

instance * :: (finite, finite) finite
proof
  show "finite (UNIV :: ('a \<times> 'b) set)"
  proof (rule finite_Prod_UNIV)
    show "finite (UNIV :: 'a set)" by (rule finite)
    show "finite (UNIV :: 'b set)" by (rule finite)
  qed
qed


text {* The powerset of a finite set *}

lemma finite_Pow_iff [iff]: "finite (Pow A) = finite A"
proof
  assume "finite (Pow A)"
  with _ have "finite ((%x. {x}) ` A)" by (rule finite_subset) blast
  thus "finite A" by (rule finite_imageD [unfolded inj_on_def]) simp
next
  assume "finite A"
  thus "finite (Pow A)"
    by induct (simp_all add: finite_UnI finite_imageI Pow_insert)
qed


lemma finite_UnionD: "finite(\<Union>A) \<Longrightarrow> finite A"
by(blast intro: finite_subset[OF subset_Pow_Union])


lemma finite_converse [iff]: "finite (r^-1) = finite r"
  apply (subgoal_tac "r^-1 = (%(x,y). (y,x))`r")
   apply simp
   apply (rule iffI)
    apply (erule finite_imageD [unfolded inj_on_def])
    apply (simp split add: split_split)
   apply (erule finite_imageI)
  apply (simp add: converse_def image_def, auto)
  apply (rule bexI)
   prefer 2 apply assumption
  apply simp
  done


text {* \paragraph{Finiteness of transitive closure} (Thanks to Sidi
Ehmety) *}

lemma finite_Field: "finite r ==> finite (Field r)"
  -- {* A finite relation has a finite field (@{text "= domain \<union> range"}. *}
  apply (induct set: Finites)
   apply (auto simp add: Field_def Domain_insert Range_insert)
  done

lemma trancl_subset_Field2: "r^+ <= Field r \<times> Field r"
  apply clarify
  apply (erule trancl_induct)
   apply (auto simp add: Field_def)
  done

lemma finite_trancl: "finite (r^+) = finite r"
  apply auto
   prefer 2
   apply (rule trancl_subset_Field2 [THEN finite_subset])
   apply (rule finite_SigmaI)
    prefer 3
    apply (blast intro: r_into_trancl' finite_subset)
   apply (auto simp add: finite_Field)
  done


subsection {* A fold functional for finite sets *}

text {* The intended behaviour is
@{text "fold f g z {x\<^isub>1, ..., x\<^isub>n} = f (g x\<^isub>1) (\<dots> (f (g x\<^isub>n) z)\<dots>)"}
if @{text f} is associative-commutative. For an application of @{text fold}
se the definitions of sums and products over finite sets.
*}

consts
  foldSet :: "('a => 'a => 'a) => ('b => 'a) => 'a => ('b set \<times> 'a) set"

inductive "foldSet f g z"
intros
emptyI [intro]: "({}, z) : foldSet f g z"
insertI [intro]:
     "\<lbrakk> x \<notin> A; (A, y) : foldSet f g z \<rbrakk>
      \<Longrightarrow> (insert x A, f (g x) y) : foldSet f g z"

inductive_cases empty_foldSetE [elim!]: "({}, x) : foldSet f g z"

constdefs
  fold :: "('a => 'a => 'a) => ('b => 'a) => 'a => 'b set => 'a"
  "fold f g z A == THE x. (A, x) : foldSet f g z"

text{*A tempting alternative for the definiens is
@{term "if finite A then THE x. (A, x) : foldSet f g e else e"}.
It allows the removal of finiteness assumptions from the theorems
@{text fold_commute}, @{text fold_reindex} and @{text fold_distrib}.
The proofs become ugly, with @{text rule_format}. It is not worth the effort.*}


lemma Diff1_foldSet:
  "(A - {x}, y) : foldSet f g z ==> x: A ==> (A, f (g x) y) : foldSet f g z"
by (erule insert_Diff [THEN subst], rule foldSet.intros, auto)

lemma foldSet_imp_finite: "(A, x) : foldSet f g z ==> finite A"
  by (induct set: foldSet) auto

lemma finite_imp_foldSet: "finite A ==> EX x. (A, x) : foldSet f g z"
  by (induct set: Finites) auto


subsubsection {* Commutative monoids *}

locale ACf =
  fixes f :: "'a => 'a => 'a"    (infixl "\<cdot>" 70)
  assumes commute: "x \<cdot> y = y \<cdot> x"
    and assoc: "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"

locale ACe = ACf +
  fixes e :: 'a
  assumes ident [simp]: "x \<cdot> e = x"

locale ACIf = ACf +
  assumes idem: "x \<cdot> x = x"

lemma (in ACf) left_commute: "x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
proof -
  have "x \<cdot> (y \<cdot> z) = (y \<cdot> z) \<cdot> x" by (simp only: commute)
  also have "... = y \<cdot> (z \<cdot> x)" by (simp only: assoc)
  also have "z \<cdot> x = x \<cdot> z" by (simp only: commute)
  finally show ?thesis .
qed

lemmas (in ACf) AC = assoc commute left_commute

lemma (in ACe) left_ident [simp]: "e \<cdot> x = x"
proof -
  have "x \<cdot> e = x" by (rule ident)
  thus ?thesis by (subst commute)
qed

lemma (in ACIf) idem2: "x \<cdot> (x \<cdot> y) = x \<cdot> y"
proof -
  have "x \<cdot> (x \<cdot> y) = (x \<cdot> x) \<cdot> y" by(simp add:assoc)
  also have "\<dots> = x \<cdot> y" by(simp add:idem)
  finally show ?thesis .
qed

lemmas (in ACIf) ACI = AC idem idem2

text{* Interpretation of locales: *}

interpretation AC_add: ACe ["op +" "0::'a::comm_monoid_add"]
by(auto intro: ACf.intro ACe_axioms.intro add_assoc add_commute)

interpretation AC_mult: ACe ["op *" "1::'a::comm_monoid_mult"]
  apply -
   apply (fast intro: ACf.intro mult_assoc mult_commute)
  apply (fastsimp intro: ACe_axioms.intro mult_assoc mult_commute)
  done


subsubsection{*From @{term foldSet} to @{term fold}*}

lemma image_less_Suc: "h ` {i. i < Suc m} = insert (h m) (h ` {i. i < m})"
by (auto simp add: less_Suc_eq) 

lemma insert_image_inj_on_eq:
     "[|insert (h m) A = h ` {i. i < Suc m}; h m \<notin> A; 
        inj_on h {i. i < Suc m}|] 
      ==> A = h ` {i. i < m}"
apply (auto simp add: image_less_Suc inj_on_def)
apply (blast intro: less_trans) 
done

lemma insert_inj_onE:
  assumes aA: "insert a A = h`{i::nat. i<n}" and anot: "a \<notin> A" 
      and inj_on: "inj_on h {i::nat. i<n}"
  shows "\<exists>hm m. inj_on hm {i::nat. i<m} & A = hm ` {i. i<m} & m < n"
proof (cases n)
  case 0 thus ?thesis using aA by auto
next
  case (Suc m)
  have nSuc: "n = Suc m" . 
  have mlessn: "m<n" by (simp add: nSuc)
  from aA obtain k where hkeq: "h k = a" and klessn: "k<n" by (blast elim!: equalityE)
  let ?hm = "swap k m h"
  have inj_hm: "inj_on ?hm {i. i < n}" using klessn mlessn 
    by (simp add: inj_on_swap_iff inj_on)
  show ?thesis
  proof (intro exI conjI)
    show "inj_on ?hm {i. i < m}" using inj_hm
      by (auto simp add: nSuc less_Suc_eq intro: subset_inj_on)
    show "m<n" by (rule mlessn)
    show "A = ?hm ` {i. i < m}" 
    proof (rule insert_image_inj_on_eq)
      show "inj_on (swap k m h) {i. i < Suc m}" using inj_hm nSuc by simp
      show "?hm m \<notin> A" by (simp add: swap_def hkeq anot) 
      show "insert (?hm m) A = ?hm ` {i. i < Suc m}"
	using aA hkeq nSuc klessn
	by (auto simp add: swap_def image_less_Suc fun_upd_image 
			   less_Suc_eq inj_on_image_set_diff [OF inj_on])
    qed
  qed
qed

lemma (in ACf) foldSet_determ_aux:
  "!!A x x' h. \<lbrakk> A = h`{i::nat. i<n}; inj_on h {i. i<n}; 
                (A,x) : foldSet f g z; (A,x') : foldSet f g z \<rbrakk>
   \<Longrightarrow> x' = x"
proof (induct n rule: less_induct)
  case (less n)
    have IH: "!!m h A x x'. 
               \<lbrakk>m<n; A = h ` {i. i<m}; inj_on h {i. i<m}; 
                (A,x) \<in> foldSet f g z; (A, x') \<in> foldSet f g z\<rbrakk> \<Longrightarrow> x' = x" .
    have Afoldx: "(A,x) \<in> foldSet f g z" and Afoldx': "(A,x') \<in> foldSet f g z"
     and A: "A = h`{i. i<n}" and injh: "inj_on h {i. i<n}" .
    show ?case
    proof (rule foldSet.cases [OF Afoldx])
      assume "(A, x) = ({}, z)"
      with Afoldx' show "x' = x" by blast
    next
      fix B b u
      assume "(A,x) = (insert b B, g b \<cdot> u)" and notinB: "b \<notin> B"
         and Bu: "(B,u) \<in> foldSet f g z"
      hence AbB: "A = insert b B" and x: "x = g b \<cdot> u" by auto
      show "x'=x" 
      proof (rule foldSet.cases [OF Afoldx'])
        assume "(A, x') = ({}, z)"
        with AbB show "x' = x" by blast
      next
	fix C c v
	assume "(A,x') = (insert c C, g c \<cdot> v)" and notinC: "c \<notin> C"
	   and Cv: "(C,v) \<in> foldSet f g z"
	hence AcC: "A = insert c C" and x': "x' = g c \<cdot> v" by auto
	from A AbB have Beq: "insert b B = h`{i. i<n}" by simp
        from insert_inj_onE [OF Beq notinB injh]
        obtain hB mB where inj_onB: "inj_on hB {i. i < mB}" 
                     and Beq: "B = hB ` {i. i < mB}"
                     and lessB: "mB < n" by auto 
	from A AcC have Ceq: "insert c C = h`{i. i<n}" by simp
        from insert_inj_onE [OF Ceq notinC injh]
        obtain hC mC where inj_onC: "inj_on hC {i. i < mC}"
                       and Ceq: "C = hC ` {i. i < mC}"
                       and lessC: "mC < n" by auto 
	show "x'=x"
	proof cases
          assume "b=c"
	  then moreover have "B = C" using AbB AcC notinB notinC by auto
	  ultimately show ?thesis  using Bu Cv x x' IH[OF lessC Ceq inj_onC]
            by auto
	next
	  assume diff: "b \<noteq> c"
	  let ?D = "B - {c}"
	  have B: "B = insert c ?D" and C: "C = insert b ?D"
	    using AbB AcC notinB notinC diff by(blast elim!:equalityE)+
	  have "finite A" by(rule foldSet_imp_finite[OF Afoldx])
	  with AbB have "finite ?D" by simp
	  then obtain d where Dfoldd: "(?D,d) \<in> foldSet f g z"
	    using finite_imp_foldSet by rules
	  moreover have cinB: "c \<in> B" using B by auto
	  ultimately have "(B,g c \<cdot> d) \<in> foldSet f g z"
	    by(rule Diff1_foldSet)
	  hence "g c \<cdot> d = u" by (rule IH [OF lessB Beq inj_onB Bu]) 
          moreover have "g b \<cdot> d = v"
	  proof (rule IH[OF lessC Ceq inj_onC Cv])
	    show "(C, g b \<cdot> d) \<in> foldSet f g z" using C notinB Dfoldd
	      by fastsimp
	  qed
	  ultimately show ?thesis using x x' by (auto simp: AC)
	qed
      qed
    qed
  qed


lemma (in ACf) foldSet_determ:
  "(A,x) : foldSet f g z ==> (A,y) : foldSet f g z ==> y = x"
apply (frule foldSet_imp_finite [THEN finite_imp_nat_seg_image_inj_on]) 
apply (blast intro: foldSet_determ_aux [rule_format])
done

lemma (in ACf) fold_equality: "(A, y) : foldSet f g z ==> fold f g z A = y"
  by (unfold fold_def) (blast intro: foldSet_determ)

text{* The base case for @{text fold}: *}

lemma fold_empty [simp]: "fold f g z {} = z"
  by (unfold fold_def) blast

lemma (in ACf) fold_insert_aux: "x \<notin> A ==>
    ((insert x A, v) : foldSet f g z) =
    (EX y. (A, y) : foldSet f g z & v = f (g x) y)"
  apply auto
  apply (rule_tac A1 = A and f1 = f in finite_imp_foldSet [THEN exE])
   apply (fastsimp dest: foldSet_imp_finite)
  apply (blast intro: foldSet_determ)
  done

text{* The recursion equation for @{text fold}: *}

lemma (in ACf) fold_insert[simp]:
    "finite A ==> x \<notin> A ==> fold f g z (insert x A) = f (g x) (fold f g z A)"
  apply (unfold fold_def)
  apply (simp add: fold_insert_aux)
  apply (rule the_equality)
  apply (auto intro: finite_imp_foldSet
    cong add: conj_cong simp add: fold_def [symmetric] fold_equality)
  done

lemma (in ACf) fold_rec:
assumes fin: "finite A" and a: "a:A"
shows "fold f g z A = f (g a) (fold f g z (A - {a}))"
proof-
  have A: "A = insert a (A - {a})" using a by blast
  hence "fold f g z A = fold f g z (insert a (A - {a}))" by simp
  also have "\<dots> = f (g a) (fold f g z (A - {a}))"
    by(rule fold_insert) (simp add:fin)+
  finally show ?thesis .
qed


text{* A simplified version for idempotent functions: *}

lemma (in ACIf) fold_insert_idem:
assumes finA: "finite A"
shows "fold f g z (insert a A) = g a \<cdot> fold f g z A"
proof cases
  assume "a \<in> A"
  then obtain B where A: "A = insert a B" and disj: "a \<notin> B"
    by(blast dest: mk_disjoint_insert)
  show ?thesis
  proof -
    from finA A have finB: "finite B" by(blast intro: finite_subset)
    have "fold f g z (insert a A) = fold f g z (insert a B)" using A by simp
    also have "\<dots> = (g a) \<cdot> (fold f g z B)"
      using finB disj by simp
    also have "\<dots> = g a \<cdot> fold f g z A"
      using A finB disj by(simp add:idem assoc[symmetric])
    finally show ?thesis .
  qed
next
  assume "a \<notin> A"
  with finA show ?thesis by simp
qed

lemma (in ACIf) foldI_conv_id:
  "finite A \<Longrightarrow> fold f g z A = fold f id z (g ` A)"
by(erule finite_induct)(simp_all add: fold_insert_idem del: fold_insert)

subsubsection{*Lemmas about @{text fold}*}

lemma (in ACf) fold_commute:
  "finite A ==> (!!z. f x (fold f g z A) = fold f g (f x z) A)"
  apply (induct set: Finites, simp)
  apply (simp add: left_commute [of x])
  done

lemma (in ACf) fold_nest_Un_Int:
  "finite A ==> finite B
    ==> fold f g (fold f g z B) A = fold f g (fold f g z (A Int B)) (A Un B)"
  apply (induct set: Finites, simp)
  apply (simp add: fold_commute Int_insert_left insert_absorb)
  done

lemma (in ACf) fold_nest_Un_disjoint:
  "finite A ==> finite B ==> A Int B = {}
    ==> fold f g z (A Un B) = fold f g (fold f g z B) A"
  by (simp add: fold_nest_Un_Int)

lemma (in ACf) fold_reindex:
assumes fin: "finite A"
shows "inj_on h A \<Longrightarrow> fold f g z (h ` A) = fold f (g \<circ> h) z A"
using fin apply induct
 apply simp
apply simp
done

lemma (in ACe) fold_Un_Int:
  "finite A ==> finite B ==>
    fold f g e A \<cdot> fold f g e B =
    fold f g e (A Un B) \<cdot> fold f g e (A Int B)"
  apply (induct set: Finites, simp)
  apply (simp add: AC insert_absorb Int_insert_left)
  done

corollary (in ACe) fold_Un_disjoint:
  "finite A ==> finite B ==> A Int B = {} ==>
    fold f g e (A Un B) = fold f g e A \<cdot> fold f g e B"
  by (simp add: fold_Un_Int)

lemma (in ACe) fold_UN_disjoint:
  "\<lbrakk> finite I; ALL i:I. finite (A i);
     ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {} \<rbrakk>
   \<Longrightarrow> fold f g e (UNION I A) =
       fold f (%i. fold f g e (A i)) e I"
  apply (induct set: Finites, simp, atomize)
  apply (subgoal_tac "ALL i:F. x \<noteq> i")
   prefer 2 apply blast
  apply (subgoal_tac "A x Int UNION F A = {}")
   prefer 2 apply blast
  apply (simp add: fold_Un_disjoint)
  done

text{*Fusion theorem, as described in
Graham Hutton's paper,
A Tutorial on the Universality and Expressiveness of Fold,
JFP 9:4 (355-372), 1999.*}
lemma (in ACf) fold_fusion:
      includes ACf g
      shows
	"finite A ==> 
	 (!!x y. h (g x y) = f x (h y)) ==>
         h (fold g j w A) = fold f j (h w) A"
  by (induct set: Finites, simp_all)

lemma (in ACf) fold_cong:
  "finite A \<Longrightarrow> (!!x. x:A ==> g x = h x) ==> fold f g z A = fold f h z A"
  apply (subgoal_tac "ALL C. C <= A --> (ALL x:C. g x = h x) --> fold f g z C = fold f h z C")
   apply simp
  apply (erule finite_induct, simp)
  apply (simp add: subset_insert_iff, clarify)
  apply (subgoal_tac "finite C")
   prefer 2 apply (blast dest: finite_subset [COMP swap_prems_rl])
  apply (subgoal_tac "C = insert x (C - {x})")
   prefer 2 apply blast
  apply (erule ssubst)
  apply (drule spec)
  apply (erule (1) notE impE)
  apply (simp add: Ball_def del: insert_Diff_single)
  done

lemma (in ACe) fold_Sigma: "finite A ==> ALL x:A. finite (B x) ==>
  fold f (%x. fold f (g x) e (B x)) e A =
  fold f (split g) e (SIGMA x:A. B x)"
apply (subst Sigma_def)
apply (subst fold_UN_disjoint, assumption, simp)
 apply blast
apply (erule fold_cong)
apply (subst fold_UN_disjoint, simp, simp)
 apply blast
apply simp
done

lemma (in ACe) fold_distrib: "finite A \<Longrightarrow>
   fold f (%x. f (g x) (h x)) e A = f (fold f g e A) (fold f h e A)"
apply (erule finite_induct, simp)
apply (simp add:AC)
done


subsection {* Generalized summation over a set *}

constdefs
  setsum :: "('a => 'b) => 'a set => 'b::comm_monoid_add"
  "setsum f A == if finite A then fold (op +) f 0 A else 0"

text{* Now: lot's of fancy syntax. First, @{term "setsum (%x. e) A"} is
written @{text"\<Sum>x\<in>A. e"}. *}

syntax
  "_setsum" :: "idt => 'a set => 'b => 'b::comm_monoid_add"    ("(3SUM _:_. _)" [0, 51, 10] 10)
syntax (xsymbols)
  "_setsum" :: "idt => 'a set => 'b => 'b::comm_monoid_add"    ("(3\<Sum>_\<in>_. _)" [0, 51, 10] 10)
syntax (HTML output)
  "_setsum" :: "idt => 'a set => 'b => 'b::comm_monoid_add"    ("(3\<Sum>_\<in>_. _)" [0, 51, 10] 10)

translations -- {* Beware of argument permutation! *}
  "SUM i:A. b" == "setsum (%i. b) A"
  "\<Sum>i\<in>A. b" == "setsum (%i. b) A"

text{* Instead of @{term"\<Sum>x\<in>{x. P}. e"} we introduce the shorter
 @{text"\<Sum>x|P. e"}. *}

syntax
  "_qsetsum" :: "idt \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3SUM _ |/ _./ _)" [0,0,10] 10)
syntax (xsymbols)
  "_qsetsum" :: "idt \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3\<Sum>_ | (_)./ _)" [0,0,10] 10)
syntax (HTML output)
  "_qsetsum" :: "idt \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3\<Sum>_ | (_)./ _)" [0,0,10] 10)

translations
  "SUM x|P. t" => "setsum (%x. t) {x. P}"
  "\<Sum>x|P. t" => "setsum (%x. t) {x. P}"

text{* Finally we abbreviate @{term"\<Sum>x\<in>A. x"} by @{text"\<Sum>A"}. *}

syntax
  "_Setsum" :: "'a set => 'a::comm_monoid_mult"  ("\<Sum>_" [1000] 999)

parse_translation {*
  let
    fun Setsum_tr [A] = Syntax.const "setsum" $ Abs ("", dummyT, Bound 0) $ A
  in [("_Setsum", Setsum_tr)] end;
*}

print_translation {*
let
  fun setsum_tr' [Abs(_,_,Bound 0), A] = Syntax.const "_Setsum" $ A
    | setsum_tr' [Abs(x,Tx,t), Const ("Collect",_) $ Abs(y,Ty,P)] = 
       if x<>y then raise Match
       else let val x' = Syntax.mark_bound x
                val t' = subst_bound(x',t)
                val P' = subst_bound(x',P)
            in Syntax.const "_qsetsum" $ Syntax.mark_bound x $ P' $ t' end
in
[("setsum", setsum_tr')]
end
*}

lemma setsum_empty [simp]: "setsum f {} = 0"
  by (simp add: setsum_def)

lemma setsum_insert [simp]:
    "finite F ==> a \<notin> F ==> setsum f (insert a F) = f a + setsum f F"
  by (simp add: setsum_def)

lemma setsum_infinite [simp]: "~ finite A ==> setsum f A = 0"
  by (simp add: setsum_def)

lemma setsum_reindex:
     "inj_on f B ==> setsum h (f ` B) = setsum (h \<circ> f) B"
by(auto simp add: setsum_def AC_add.fold_reindex dest!:finite_imageD)

lemma setsum_reindex_id:
     "inj_on f B ==> setsum f B = setsum id (f ` B)"
by (auto simp add: setsum_reindex)

lemma setsum_cong:
  "A = B ==> (!!x. x:B ==> f x = g x) ==> setsum f A = setsum g B"
by(fastsimp simp: setsum_def intro: AC_add.fold_cong)

lemma strong_setsum_cong[cong]:
  "A = B ==> (!!x. x:B =simp=> f x = g x)
   ==> setsum (%x. f x) A = setsum (%x. g x) B"
by(fastsimp simp: simp_implies_def setsum_def intro: AC_add.fold_cong)

lemma setsum_cong2: "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> setsum f A = setsum g A";
  by (rule setsum_cong[OF refl], auto);

lemma setsum_reindex_cong:
     "[|inj_on f A; B = f ` A; !!a. a:A \<Longrightarrow> g a = h (f a)|] 
      ==> setsum h B = setsum g A"
  by (simp add: setsum_reindex cong: setsum_cong)

lemma setsum_0[simp]: "setsum (%i. 0) A = 0"
apply (clarsimp simp: setsum_def)
apply (erule finite_induct, auto)
done

lemma setsum_0': "ALL a:A. f a = 0 ==> setsum f A = 0"
by(simp add:setsum_cong)

lemma setsum_Un_Int: "finite A ==> finite B ==>
  setsum g (A Un B) + setsum g (A Int B) = setsum g A + setsum g B"
  -- {* The reversed orientation looks more natural, but LOOPS as a simprule! *}
by(simp add: setsum_def AC_add.fold_Un_Int [symmetric])

lemma setsum_Un_disjoint: "finite A ==> finite B
  ==> A Int B = {} ==> setsum g (A Un B) = setsum g A + setsum g B"
by (subst setsum_Un_Int [symmetric], auto)

(*But we can't get rid of finite I. If infinite, although the rhs is 0, 
  the lhs need not be, since UNION I A could still be finite.*)
lemma setsum_UN_disjoint:
    "finite I ==> (ALL i:I. finite (A i)) ==>
        (ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {}) ==>
      setsum f (UNION I A) = (\<Sum>i\<in>I. setsum f (A i))"
by(simp add: setsum_def AC_add.fold_UN_disjoint cong: setsum_cong)

text{*No need to assume that @{term C} is finite.  If infinite, the rhs is
directly 0, and @{term "Union C"} is also infinite, hence the lhs is also 0.*}
lemma setsum_Union_disjoint:
  "[| (ALL A:C. finite A);
      (ALL A:C. ALL B:C. A \<noteq> B --> A Int B = {}) |]
   ==> setsum f (Union C) = setsum (setsum f) C"
apply (cases "finite C") 
 prefer 2 apply (force dest: finite_UnionD simp add: setsum_def)
  apply (frule setsum_UN_disjoint [of C id f])
 apply (unfold Union_def id_def, assumption+)
done

(*But we can't get rid of finite A. If infinite, although the lhs is 0, 
  the rhs need not be, since SIGMA A B could still be finite.*)
lemma setsum_Sigma: "finite A ==> ALL x:A. finite (B x) ==>
    (\<Sum>x\<in>A. (\<Sum>y\<in>B x. f x y)) =
    (\<Sum>z\<in>(SIGMA x:A. B x). f (fst z) (snd z))"
by(simp add:setsum_def AC_add.fold_Sigma split_def cong:setsum_cong)

text{*Here we can eliminate the finiteness assumptions, by cases.*}
lemma setsum_cartesian_product: 
   "(\<Sum>x\<in>A. (\<Sum>y\<in>B. f x y)) = (\<Sum>z\<in>A <*> B. f (fst z) (snd z))"
apply (cases "finite A") 
 apply (cases "finite B") 
  apply (simp add: setsum_Sigma)
 apply (cases "A={}", simp)
 apply (simp) 
apply (auto simp add: setsum_def
            dest: finite_cartesian_productD1 finite_cartesian_productD2) 
done

lemma setsum_addf: "setsum (%x. f x + g x) A = (setsum f A + setsum g A)"
by(simp add:setsum_def AC_add.fold_distrib)


subsubsection {* Properties in more restricted classes of structures *}

lemma setsum_SucD: "setsum f A = Suc n ==> EX a:A. 0 < f a"
  apply (case_tac "finite A")
   prefer 2 apply (simp add: setsum_def)
  apply (erule rev_mp)
  apply (erule finite_induct, auto)
  done

lemma setsum_eq_0_iff [simp]:
    "finite F ==> (setsum f F = 0) = (ALL a:F. f a = (0::nat))"
  by (induct set: Finites) auto

lemma setsum_Un_nat: "finite A ==> finite B ==>
    (setsum f (A Un B) :: nat) = setsum f A + setsum f B - setsum f (A Int B)"
  -- {* For the natural numbers, we have subtraction. *}
  by (subst setsum_Un_Int [symmetric], auto simp add: ring_eq_simps)

lemma setsum_Un: "finite A ==> finite B ==>
    (setsum f (A Un B) :: 'a :: ab_group_add) =
      setsum f A + setsum f B - setsum f (A Int B)"
  by (subst setsum_Un_Int [symmetric], auto simp add: ring_eq_simps)

lemma setsum_diff1_nat: "(setsum f (A - {a}) :: nat) =
    (if a:A then setsum f A - f a else setsum f A)"
  apply (case_tac "finite A")
   prefer 2 apply (simp add: setsum_def)
  apply (erule finite_induct)
   apply (auto simp add: insert_Diff_if)
  apply (drule_tac a = a in mk_disjoint_insert, auto)
  done

lemma setsum_diff1: "finite A \<Longrightarrow>
  (setsum f (A - {a}) :: ('a::ab_group_add)) =
  (if a:A then setsum f A - f a else setsum f A)"
  by (erule finite_induct) (auto simp add: insert_Diff_if)

lemma setsum_diff1'[rule_format]: "finite A \<Longrightarrow> a \<in> A \<longrightarrow> (\<Sum> x \<in> A. f x) = f a + (\<Sum> x \<in> (A - {a}). f x)"
  apply (erule finite_induct[where F=A and P="% A. (a \<in> A \<longrightarrow> (\<Sum> x \<in> A. f x) = f a + (\<Sum> x \<in> (A - {a}). f x))"])
  apply (auto simp add: insert_Diff_if add_ac)
  done

(* By Jeremy Siek: *)

lemma setsum_diff_nat: 
  assumes finB: "finite B"
  shows "B \<subseteq> A \<Longrightarrow> (setsum f (A - B) :: nat) = (setsum f A) - (setsum f B)"
using finB
proof (induct)
  show "setsum f (A - {}) = (setsum f A) - (setsum f {})" by simp
next
  fix F x assume finF: "finite F" and xnotinF: "x \<notin> F"
    and xFinA: "insert x F \<subseteq> A"
    and IH: "F \<subseteq> A \<Longrightarrow> setsum f (A - F) = setsum f A - setsum f F"
  from xnotinF xFinA have xinAF: "x \<in> (A - F)" by simp
  from xinAF have A: "setsum f ((A - F) - {x}) = setsum f (A - F) - f x"
    by (simp add: setsum_diff1_nat)
  from xFinA have "F \<subseteq> A" by simp
  with IH have "setsum f (A - F) = setsum f A - setsum f F" by simp
  with A have B: "setsum f ((A - F) - {x}) = setsum f A - setsum f F - f x"
    by simp
  from xnotinF have "A - insert x F = (A - F) - {x}" by auto
  with B have C: "setsum f (A - insert x F) = setsum f A - setsum f F - f x"
    by simp
  from finF xnotinF have "setsum f (insert x F) = setsum f F + f x" by simp
  with C have "setsum f (A - insert x F) = setsum f A - setsum f (insert x F)"
    by simp
  thus "setsum f (A - insert x F) = setsum f A - setsum f (insert x F)" by simp
qed

lemma setsum_diff:
  assumes le: "finite A" "B \<subseteq> A"
  shows "setsum f (A - B) = setsum f A - ((setsum f B)::('a::ab_group_add))"
proof -
  from le have finiteB: "finite B" using finite_subset by auto
  show ?thesis using finiteB le
    proof (induct)
      case empty
      thus ?case by auto
    next
      case (insert x F)
      thus ?case using le finiteB 
	by (simp add: Diff_insert[where a=x and B=F] setsum_diff1 insert_absorb)
    qed
  qed

lemma setsum_mono:
  assumes le: "\<And>i. i\<in>K \<Longrightarrow> f (i::'a) \<le> ((g i)::('b::{comm_monoid_add, pordered_ab_semigroup_add}))"
  shows "(\<Sum>i\<in>K. f i) \<le> (\<Sum>i\<in>K. g i)"
proof (cases "finite K")
  case True
  thus ?thesis using le
  proof (induct)
    case empty
    thus ?case by simp
  next
    case insert
    thus ?case using add_mono 
      by force
  qed
next
  case False
  thus ?thesis
    by (simp add: setsum_def)
qed

lemma setsum_strict_mono:
fixes f :: "'a \<Rightarrow> 'b::{pordered_cancel_ab_semigroup_add,comm_monoid_add}"
assumes fin_ne: "finite A"  "A \<noteq> {}"
shows "(!!x. x:A \<Longrightarrow> f x < g x) \<Longrightarrow> setsum f A < setsum g A"
using fin_ne
proof (induct rule: finite_ne_induct)
  case singleton thus ?case by simp
next
  case insert thus ?case by (auto simp: add_strict_mono)
qed

lemma setsum_negf:
 "setsum (%x. - (f x)::'a::ab_group_add) A = - setsum f A"
proof (cases "finite A")
  case True thus ?thesis by (induct set: Finites, auto)
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma setsum_subtractf:
 "setsum (%x. ((f x)::'a::ab_group_add) - g x) A =
  setsum f A - setsum g A"
proof (cases "finite A")
  case True thus ?thesis by (simp add: diff_minus setsum_addf setsum_negf)
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma setsum_nonneg:
assumes nn: "\<forall>x\<in>A. (0::'a::{pordered_ab_semigroup_add,comm_monoid_add}) \<le> f x"
shows "0 \<le> setsum f A"
proof (cases "finite A")
  case True thus ?thesis using nn
  apply (induct set: Finites, auto)
  apply (subgoal_tac "0 + 0 \<le> f x + setsum f F", simp)
  apply (blast intro: add_mono)
  done
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma setsum_nonpos:
assumes np: "\<forall>x\<in>A. f x \<le> (0::'a::{pordered_ab_semigroup_add,comm_monoid_add})"
shows "setsum f A \<le> 0"
proof (cases "finite A")
  case True thus ?thesis using np
  apply (induct set: Finites, auto)
  apply (subgoal_tac "f x + setsum f F \<le> 0 + 0", simp)
  apply (blast intro: add_mono)
  done
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma setsum_mono2:
fixes f :: "'a \<Rightarrow> 'b :: {pordered_ab_semigroup_add_imp_le,comm_monoid_add}"
assumes fin: "finite B" and sub: "A \<subseteq> B" and nn: "\<And>b. b \<in> B-A \<Longrightarrow> 0 \<le> f b"
shows "setsum f A \<le> setsum f B"
proof -
  have "setsum f A \<le> setsum f A + setsum f (B-A)"
    by(simp add: add_increasing2[OF setsum_nonneg] nn Ball_def)
  also have "\<dots> = setsum f (A \<union> (B-A))" using fin finite_subset[OF sub fin]
    by (simp add:setsum_Un_disjoint del:Un_Diff_cancel)
  also have "A \<union> (B-A) = B" using sub by blast
  finally show ?thesis .
qed

(* FIXME: this is distributitivty, name as such! *)

lemma setsum_mult: 
  fixes f :: "'a => ('b::semiring_0_cancel)"
  shows "r * setsum f A = setsum (%n. r * f n) A"
proof (cases "finite A")
  case True
  thus ?thesis
  proof (induct)
    case empty thus ?case by simp
  next
    case (insert x A) thus ?case by (simp add: right_distrib)
  qed
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma setsum_abs[iff]: 
  fixes f :: "'a => ('b::lordered_ab_group_abs)"
  shows "abs (setsum f A) \<le> setsum (%i. abs(f i)) A"
proof (cases "finite A")
  case True
  thus ?thesis
  proof (induct)
    case empty thus ?case by simp
  next
    case (insert x A)
    thus ?case by (auto intro: abs_triangle_ineq order_trans)
  qed
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma setsum_abs_ge_zero[iff]: 
  fixes f :: "'a => ('b::lordered_ab_group_abs)"
  shows "0 \<le> setsum (%i. abs(f i)) A"
proof (cases "finite A")
  case True
  thus ?thesis
  proof (induct)
    case empty thus ?case by simp
  next
    case (insert x A) thus ?case by (auto intro: order_trans)
  qed
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma abs_setsum_abs[simp]: 
  fixes f :: "'a => ('b::lordered_ab_group_abs)"
  shows "abs (\<Sum>a\<in>A. abs(f a)) = (\<Sum>a\<in>A. abs(f a))"
proof (cases "finite A")
  case True
  thus ?thesis
  proof (induct)
    case empty thus ?case by simp
  next
    case (insert a A)
    hence "\<bar>\<Sum>a\<in>insert a A. \<bar>f a\<bar>\<bar> = \<bar>\<bar>f a\<bar> + (\<Sum>a\<in>A. \<bar>f a\<bar>)\<bar>" by simp
    also have "\<dots> = \<bar>\<bar>f a\<bar> + \<bar>\<Sum>a\<in>A. \<bar>f a\<bar>\<bar>\<bar>"  using insert by simp
    also have "\<dots> = \<bar>f a\<bar> + \<bar>\<Sum>a\<in>A. \<bar>f a\<bar>\<bar>" by simp
    also have "\<dots> = (\<Sum>a\<in>insert a A. \<bar>f a\<bar>)" using insert by simp
    finally show ?case .
  qed
next
  case False thus ?thesis by (simp add: setsum_def)
qed


subsection {* Generalized product over a set *}

constdefs
  setprod :: "('a => 'b) => 'a set => 'b::comm_monoid_mult"
  "setprod f A == if finite A then fold (op *) f 1 A else 1"

syntax
  "_setprod" :: "idt => 'a set => 'b => 'b::comm_monoid_mult"  ("(3PROD _:_. _)" [0, 51, 10] 10)
syntax (xsymbols)
  "_setprod" :: "idt => 'a set => 'b => 'b::comm_monoid_mult"  ("(3\<Prod>_\<in>_. _)" [0, 51, 10] 10)
syntax (HTML output)
  "_setprod" :: "idt => 'a set => 'b => 'b::comm_monoid_mult"  ("(3\<Prod>_\<in>_. _)" [0, 51, 10] 10)

translations -- {* Beware of argument permutation! *}
  "PROD i:A. b" == "setprod (%i. b) A" 
  "\<Prod>i\<in>A. b" == "setprod (%i. b) A" 

text{* Instead of @{term"\<Prod>x\<in>{x. P}. e"} we introduce the shorter
 @{text"\<Prod>x|P. e"}. *}

syntax
  "_qsetprod" :: "idt \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3PROD _ |/ _./ _)" [0,0,10] 10)
syntax (xsymbols)
  "_qsetprod" :: "idt \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3\<Prod>_ | (_)./ _)" [0,0,10] 10)
syntax (HTML output)
  "_qsetprod" :: "idt \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3\<Prod>_ | (_)./ _)" [0,0,10] 10)

translations
  "PROD x|P. t" => "setprod (%x. t) {x. P}"
  "\<Prod>x|P. t" => "setprod (%x. t) {x. P}"

text{* Finally we abbreviate @{term"\<Prod>x\<in>A. x"} by @{text"\<Prod>A"}. *}

syntax
  "_Setprod" :: "'a set => 'a::comm_monoid_mult"  ("\<Prod>_" [1000] 999)

parse_translation {*
  let
    fun Setprod_tr [A] = Syntax.const "setprod" $ Abs ("", dummyT, Bound 0) $ A
  in [("_Setprod", Setprod_tr)] end;
*}
print_translation {*
let fun setprod_tr' [Abs(x,Tx,t), A] =
    if t = Bound 0 then Syntax.const "_Setprod" $ A else raise Match
in
[("setprod", setprod_tr')]
end
*}


lemma setprod_empty [simp]: "setprod f {} = 1"
  by (auto simp add: setprod_def)

lemma setprod_insert [simp]: "[| finite A; a \<notin> A |] ==>
    setprod f (insert a A) = f a * setprod f A"
by (simp add: setprod_def)

lemma setprod_infinite [simp]: "~ finite A ==> setprod f A = 1"
  by (simp add: setprod_def)

lemma setprod_reindex:
     "inj_on f B ==> setprod h (f ` B) = setprod (h \<circ> f) B"
by(auto simp: setprod_def AC_mult.fold_reindex dest!:finite_imageD)

lemma setprod_reindex_id: "inj_on f B ==> setprod f B = setprod id (f ` B)"
by (auto simp add: setprod_reindex)

lemma setprod_cong:
  "A = B ==> (!!x. x:B ==> f x = g x) ==> setprod f A = setprod g B"
by(fastsimp simp: setprod_def intro: AC_mult.fold_cong)

lemma strong_setprod_cong:
  "A = B ==> (!!x. x:B =simp=> f x = g x) ==> setprod f A = setprod g B"
by(fastsimp simp: simp_implies_def setprod_def intro: AC_mult.fold_cong)

lemma setprod_reindex_cong: "inj_on f A ==>
    B = f ` A ==> g = h \<circ> f ==> setprod h B = setprod g A"
  by (frule setprod_reindex, simp)


lemma setprod_1: "setprod (%i. 1) A = 1"
  apply (case_tac "finite A")
  apply (erule finite_induct, auto simp add: mult_ac)
  done

lemma setprod_1': "ALL a:F. f a = 1 ==> setprod f F = 1"
  apply (subgoal_tac "setprod f F = setprod (%x. 1) F")
  apply (erule ssubst, rule setprod_1)
  apply (rule setprod_cong, auto)
  done

lemma setprod_Un_Int: "finite A ==> finite B
    ==> setprod g (A Un B) * setprod g (A Int B) = setprod g A * setprod g B"
by(simp add: setprod_def AC_mult.fold_Un_Int[symmetric])

lemma setprod_Un_disjoint: "finite A ==> finite B
  ==> A Int B = {} ==> setprod g (A Un B) = setprod g A * setprod g B"
by (subst setprod_Un_Int [symmetric], auto)

lemma setprod_UN_disjoint:
    "finite I ==> (ALL i:I. finite (A i)) ==>
        (ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {}) ==>
      setprod f (UNION I A) = setprod (%i. setprod f (A i)) I"
by(simp add: setprod_def AC_mult.fold_UN_disjoint cong: setprod_cong)

lemma setprod_Union_disjoint:
  "[| (ALL A:C. finite A);
      (ALL A:C. ALL B:C. A \<noteq> B --> A Int B = {}) |] 
   ==> setprod f (Union C) = setprod (setprod f) C"
apply (cases "finite C") 
 prefer 2 apply (force dest: finite_UnionD simp add: setprod_def)
  apply (frule setprod_UN_disjoint [of C id f])
 apply (unfold Union_def id_def, assumption+)
done

lemma setprod_Sigma: "finite A ==> ALL x:A. finite (B x) ==>
    (\<Prod>x\<in>A. (\<Prod>y\<in> B x. f x y)) =
    (\<Prod>z\<in>(SIGMA x:A. B x). f (fst z) (snd z))"
by(simp add:setprod_def AC_mult.fold_Sigma split_def cong:setprod_cong)

text{*Here we can eliminate the finiteness assumptions, by cases.*}
lemma setprod_cartesian_product: 
     "(\<Prod>x\<in>A. (\<Prod>y\<in> B. f x y)) = (\<Prod>z\<in>(A <*> B). f (fst z) (snd z))"
apply (cases "finite A") 
 apply (cases "finite B") 
  apply (simp add: setprod_Sigma)
 apply (cases "A={}", simp)
 apply (simp add: setprod_1) 
apply (auto simp add: setprod_def
            dest: finite_cartesian_productD1 finite_cartesian_productD2) 
done

lemma setprod_timesf:
     "setprod (%x. f x * g x) A = (setprod f A * setprod g A)"
by(simp add:setprod_def AC_mult.fold_distrib)


subsubsection {* Properties in more restricted classes of structures *}

lemma setprod_eq_1_iff [simp]:
    "finite F ==> (setprod f F = 1) = (ALL a:F. f a = (1::nat))"
  by (induct set: Finites) auto

lemma setprod_zero:
     "finite A ==> EX x: A. f x = (0::'a::comm_semiring_1_cancel) ==> setprod f A = 0"
  apply (induct set: Finites, force, clarsimp)
  apply (erule disjE, auto)
  done

lemma setprod_nonneg [rule_format]:
     "(ALL x: A. (0::'a::ordered_idom) \<le> f x) --> 0 \<le> setprod f A"
  apply (case_tac "finite A")
  apply (induct set: Finites, force, clarsimp)
  apply (subgoal_tac "0 * 0 \<le> f x * setprod f F", force)
  apply (rule mult_mono, assumption+)
  apply (auto simp add: setprod_def)
  done

lemma setprod_pos [rule_format]: "(ALL x: A. (0::'a::ordered_idom) < f x)
     --> 0 < setprod f A"
  apply (case_tac "finite A")
  apply (induct set: Finites, force, clarsimp)
  apply (subgoal_tac "0 * 0 < f x * setprod f F", force)
  apply (rule mult_strict_mono, assumption+)
  apply (auto simp add: setprod_def)
  done

lemma setprod_nonzero [rule_format]:
    "(ALL x y. (x::'a::comm_semiring_1_cancel) * y = 0 --> x = 0 | y = 0) ==>
      finite A ==> (ALL x: A. f x \<noteq> (0::'a)) --> setprod f A \<noteq> 0"
  apply (erule finite_induct, auto)
  done

lemma setprod_zero_eq:
    "(ALL x y. (x::'a::comm_semiring_1_cancel) * y = 0 --> x = 0 | y = 0) ==>
     finite A ==> (setprod f A = (0::'a)) = (EX x: A. f x = 0)"
  apply (insert setprod_zero [of A f] setprod_nonzero [of A f], blast)
  done

lemma setprod_nonzero_field:
    "finite A ==> (ALL x: A. f x \<noteq> (0::'a::field)) ==> setprod f A \<noteq> 0"
  apply (rule setprod_nonzero, auto)
  done

lemma setprod_zero_eq_field:
    "finite A ==> (setprod f A = (0::'a::field)) = (EX x: A. f x = 0)"
  apply (rule setprod_zero_eq, auto)
  done

lemma setprod_Un: "finite A ==> finite B ==> (ALL x: A Int B. f x \<noteq> 0) ==>
    (setprod f (A Un B) :: 'a ::{field})
      = setprod f A * setprod f B / setprod f (A Int B)"
  apply (subst setprod_Un_Int [symmetric], auto)
  apply (subgoal_tac "finite (A Int B)")
  apply (frule setprod_nonzero_field [of "A Int B" f], assumption)
  apply (subst times_divide_eq_right [THEN sym], auto simp add: divide_self)
  done

lemma setprod_diff1: "finite A ==> f a \<noteq> 0 ==>
    (setprod f (A - {a}) :: 'a :: {field}) =
      (if a:A then setprod f A / f a else setprod f A)"
  apply (erule finite_induct)
   apply (auto simp add: insert_Diff_if)
  apply (subgoal_tac "f a * setprod f F / f a = setprod f F * f a / f a")
  apply (erule ssubst)
  apply (subst times_divide_eq_right [THEN sym])
  apply (auto simp add: mult_ac times_divide_eq_right divide_self)
  done

lemma setprod_inversef: "finite A ==>
    ALL x: A. f x \<noteq> (0::'a::{field,division_by_zero}) ==>
      setprod (inverse \<circ> f) A = inverse (setprod f A)"
  apply (erule finite_induct)
  apply (simp, simp)
  done

lemma setprod_dividef:
     "[|finite A;
        \<forall>x \<in> A. g x \<noteq> (0::'a::{field,division_by_zero})|]
      ==> setprod (%x. f x / g x) A = setprod f A / setprod g A"
  apply (subgoal_tac
         "setprod (%x. f x / g x) A = setprod (%x. f x * (inverse \<circ> g) x) A")
  apply (erule ssubst)
  apply (subst divide_inverse)
  apply (subst setprod_timesf)
  apply (subst setprod_inversef, assumption+, rule refl)
  apply (rule setprod_cong, rule refl)
  apply (subst divide_inverse, auto)
  done

subsection {* Finite cardinality *}

text {* This definition, although traditional, is ugly to work with:
@{text "card A == LEAST n. EX f. A = {f i | i. i < n}"}.
But now that we have @{text setsum} things are easy:
*}

constdefs
  card :: "'a set => nat"
  "card A == setsum (%x. 1::nat) A"

lemma card_empty [simp]: "card {} = 0"
  by (simp add: card_def)

lemma card_infinite [simp]: "~ finite A ==> card A = 0"
  by (simp add: card_def)

lemma card_eq_setsum: "card A = setsum (%x. 1) A"
by (simp add: card_def)

lemma card_insert_disjoint [simp]:
  "finite A ==> x \<notin> A ==> card (insert x A) = Suc(card A)"
by(simp add: card_def)

lemma card_insert_if:
    "finite A ==> card (insert x A) = (if x:A then card A else Suc(card(A)))"
  by (simp add: insert_absorb)

lemma card_0_eq [simp]: "finite A ==> (card A = 0) = (A = {})"
  apply auto
  apply (drule_tac a = x in mk_disjoint_insert, clarify, auto)
  done

lemma card_eq_0_iff: "(card A = 0) = (A = {} | ~ finite A)"
by auto

lemma card_Suc_Diff1: "finite A ==> x: A ==> Suc (card (A - {x})) = card A"
apply(rule_tac t = A in insert_Diff [THEN subst], assumption)
apply(simp del:insert_Diff_single)
done

lemma card_Diff_singleton:
    "finite A ==> x: A ==> card (A - {x}) = card A - 1"
  by (simp add: card_Suc_Diff1 [symmetric])

lemma card_Diff_singleton_if:
    "finite A ==> card (A-{x}) = (if x : A then card A - 1 else card A)"
  by (simp add: card_Diff_singleton)

lemma card_insert: "finite A ==> card (insert x A) = Suc (card (A - {x}))"
  by (simp add: card_insert_if card_Suc_Diff1)

lemma card_insert_le: "finite A ==> card A <= card (insert x A)"
  by (simp add: card_insert_if)

lemma card_mono: "\<lbrakk> finite B; A \<subseteq> B \<rbrakk> \<Longrightarrow> card A \<le> card B"
by (simp add: card_def setsum_mono2)

lemma card_seteq: "finite B ==> (!!A. A <= B ==> card B <= card A ==> A = B)"
  apply (induct set: Finites, simp, clarify)
  apply (subgoal_tac "finite A & A - {x} <= F")
   prefer 2 apply (blast intro: finite_subset, atomize)
  apply (drule_tac x = "A - {x}" in spec)
  apply (simp add: card_Diff_singleton_if split add: split_if_asm)
  apply (case_tac "card A", auto)
  done

lemma psubset_card_mono: "finite B ==> A < B ==> card A < card B"
  apply (simp add: psubset_def linorder_not_le [symmetric])
  apply (blast dest: card_seteq)
  done

lemma card_Un_Int: "finite A ==> finite B
    ==> card A + card B = card (A Un B) + card (A Int B)"
by(simp add:card_def setsum_Un_Int)

lemma card_Un_disjoint: "finite A ==> finite B
    ==> A Int B = {} ==> card (A Un B) = card A + card B"
  by (simp add: card_Un_Int)

lemma card_Diff_subset:
  "finite B ==> B <= A ==> card (A - B) = card A - card B"
by(simp add:card_def setsum_diff_nat)

lemma card_Diff1_less: "finite A ==> x: A ==> card (A - {x}) < card A"
  apply (rule Suc_less_SucD)
  apply (simp add: card_Suc_Diff1)
  done

lemma card_Diff2_less:
    "finite A ==> x: A ==> y: A ==> card (A - {x} - {y}) < card A"
  apply (case_tac "x = y")
   apply (simp add: card_Diff1_less)
  apply (rule less_trans)
   prefer 2 apply (auto intro!: card_Diff1_less)
  done

lemma card_Diff1_le: "finite A ==> card (A - {x}) <= card A"
  apply (case_tac "x : A")
   apply (simp_all add: card_Diff1_less less_imp_le)
  done

lemma card_psubset: "finite B ==> A \<subseteq> B ==> card A < card B ==> A < B"
by (erule psubsetI, blast)

lemma insert_partition:
  "\<lbrakk> x \<notin> F; \<forall>c1 \<in> insert x F. \<forall>c2 \<in> insert x F. c1 \<noteq> c2 \<longrightarrow> c1 \<inter> c2 = {} \<rbrakk>
  \<Longrightarrow> x \<inter> \<Union> F = {}"
by auto

(* main cardinality theorem *)
lemma card_partition [rule_format]:
     "finite C ==>  
        finite (\<Union> C) -->  
        (\<forall>c\<in>C. card c = k) -->   
        (\<forall>c1 \<in> C. \<forall>c2 \<in> C. c1 \<noteq> c2 --> c1 \<inter> c2 = {}) -->  
        k * card(C) = card (\<Union> C)"
apply (erule finite_induct, simp)
apply (simp add: card_insert_disjoint card_Un_disjoint insert_partition 
       finite_subset [of _ "\<Union> (insert x F)"])
done


lemma setsum_constant [simp]: "(\<Sum>x \<in> A. y) = of_nat(card A) * y"
apply (cases "finite A")
apply (erule finite_induct)
apply (auto simp add: ring_distrib add_ac)
done


lemma setprod_constant: "finite A ==> (\<Prod>x\<in> A. (y::'a::recpower)) = y^(card A)"
  apply (erule finite_induct)
  apply (auto simp add: power_Suc)
  done

lemma setsum_bounded:
  assumes le: "\<And>i. i\<in>A \<Longrightarrow> f i \<le> (K::'a::{comm_semiring_1_cancel, pordered_ab_semigroup_add})"
  shows "setsum f A \<le> of_nat(card A) * K"
proof (cases "finite A")
  case True
  thus ?thesis using le setsum_mono[where K=A and g = "%x. K"] by simp
next
  case False thus ?thesis by (simp add: setsum_def)
qed


subsubsection {* Cardinality of unions *}

lemma of_nat_id[simp]: "(of_nat n :: nat) = n"
by(induct n, auto)

lemma card_UN_disjoint:
    "finite I ==> (ALL i:I. finite (A i)) ==>
        (ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {}) ==>
      card (UNION I A) = (\<Sum>i\<in>I. card(A i))"
  apply (simp add: card_def del: setsum_constant)
  apply (subgoal_tac
           "setsum (%i. card (A i)) I = setsum (%i. (setsum (%x. 1) (A i))) I")
  apply (simp add: setsum_UN_disjoint del: setsum_constant)
  apply (simp cong: setsum_cong)
  done

lemma card_Union_disjoint:
  "finite C ==> (ALL A:C. finite A) ==>
        (ALL A:C. ALL B:C. A \<noteq> B --> A Int B = {}) ==>
      card (Union C) = setsum card C"
  apply (frule card_UN_disjoint [of C id])
  apply (unfold Union_def id_def, assumption+)
  done

subsubsection {* Cardinality of image *}

text{*The image of a finite set can be expressed using @{term fold}.*}
lemma image_eq_fold: "finite A ==> f ` A = fold (op Un) (%x. {f x}) {} A"
  apply (erule finite_induct, simp)
  apply (subst ACf.fold_insert) 
  apply (auto simp add: ACf_def) 
  done

lemma card_image_le: "finite A ==> card (f ` A) <= card A"
  apply (induct set: Finites, simp)
  apply (simp add: le_SucI finite_imageI card_insert_if)
  done

lemma card_image: "inj_on f A ==> card (f ` A) = card A"
by(simp add:card_def setsum_reindex o_def del:setsum_constant)

lemma endo_inj_surj: "finite A ==> f ` A \<subseteq> A ==> inj_on f A ==> f ` A = A"
  by (simp add: card_seteq card_image)

lemma eq_card_imp_inj_on:
  "[| finite A; card(f ` A) = card A |] ==> inj_on f A"
apply (induct rule:finite_induct, simp)
apply(frule card_image_le[where f = f])
apply(simp add:card_insert_if split:if_splits)
done

lemma inj_on_iff_eq_card:
  "finite A ==> inj_on f A = (card(f ` A) = card A)"
by(blast intro: card_image eq_card_imp_inj_on)


lemma card_inj_on_le:
    "[|inj_on f A; f ` A \<subseteq> B; finite B |] ==> card A \<le> card B"
apply (subgoal_tac "finite A") 
 apply (force intro: card_mono simp add: card_image [symmetric])
apply (blast intro: finite_imageD dest: finite_subset) 
done

lemma card_bij_eq:
    "[|inj_on f A; f ` A \<subseteq> B; inj_on g B; g ` B \<subseteq> A;
       finite A; finite B |] ==> card A = card B"
  by (auto intro: le_anti_sym card_inj_on_le)


subsubsection {* Cardinality of products *}

(*
lemma SigmaI_insert: "y \<notin> A ==>
  (SIGMA x:(insert y A). B x) = (({y} <*> (B y)) \<union> (SIGMA x: A. B x))"
  by auto
*)

lemma card_SigmaI [simp]:
  "\<lbrakk> finite A; ALL a:A. finite (B a) \<rbrakk>
  \<Longrightarrow> card (SIGMA x: A. B x) = (\<Sum>a\<in>A. card (B a))"
by(simp add:card_def setsum_Sigma del:setsum_constant)

lemma card_cartesian_product: "card (A <*> B) = card(A) * card(B)"
apply (cases "finite A") 
apply (cases "finite B") 
apply (auto simp add: card_eq_0_iff
            dest: finite_cartesian_productD1 finite_cartesian_productD2)
done

lemma card_cartesian_product_singleton:  "card({x} <*> A) = card(A)"
by (simp add: card_cartesian_product)



subsubsection {* Cardinality of the Powerset *}

lemma card_Pow: "finite A ==> card (Pow A) = Suc (Suc 0) ^ card A"  (* FIXME numeral 2 (!?) *)
  apply (induct set: Finites)
   apply (simp_all add: Pow_insert)
  apply (subst card_Un_disjoint, blast)
    apply (blast intro: finite_imageI, blast)
  apply (subgoal_tac "inj_on (insert x) (Pow F)")
   apply (simp add: card_image Pow_insert)
  apply (unfold inj_on_def)
  apply (blast elim!: equalityE)
  done

text {* Relates to equivalence classes.  Based on a theorem of
F. Kammüller's.  *}

lemma dvd_partition:
  "finite (Union C) ==>
    ALL c : C. k dvd card c ==>
    (ALL c1: C. ALL c2: C. c1 \<noteq> c2 --> c1 Int c2 = {}) ==>
  k dvd card (Union C)"
apply(frule finite_UnionD)
apply(rotate_tac -1)
  apply (induct set: Finites, simp_all, clarify)
  apply (subst card_Un_disjoint)
  apply (auto simp add: dvd_add disjoint_eq_subset_Compl)
  done


subsection{* A fold functional for non-empty sets *}

text{* Does not require start value. *}

consts
  fold1Set :: "('a => 'a => 'a) => ('a set \<times> 'a) set"

inductive "fold1Set f"
intros
  fold1Set_insertI [intro]:
   "\<lbrakk> (A,x) \<in> foldSet f id a; a \<notin> A \<rbrakk> \<Longrightarrow> (insert a A, x) \<in> fold1Set f"

constdefs
  fold1 :: "('a => 'a => 'a) => 'a set => 'a"
  "fold1 f A == THE x. (A, x) : fold1Set f"

lemma fold1Set_nonempty:
 "(A, x) : fold1Set f \<Longrightarrow> A \<noteq> {}"
by(erule fold1Set.cases, simp_all) 


inductive_cases empty_fold1SetE [elim!]: "({}, x) : fold1Set f"

inductive_cases insert_fold1SetE [elim!]: "(insert a X, x) : fold1Set f"


lemma fold1Set_sing [iff]: "(({a},b) : fold1Set f) = (a = b)"
  by (blast intro: foldSet.intros elim: foldSet.cases)

lemma fold1_singleton[simp]: "fold1 f {a} = a"
  by (unfold fold1_def) blast

lemma finite_nonempty_imp_fold1Set:
  "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> EX x. (A, x) : fold1Set f"
apply (induct A rule: finite_induct)
apply (auto dest: finite_imp_foldSet [of _ f id])  
done

text{*First, some lemmas about @{term foldSet}.*}

lemma (in ACf) foldSet_insert_swap:
assumes fold: "(A,y) \<in> foldSet f id b"
shows "b \<notin> A \<Longrightarrow> (insert b A, z \<cdot> y) \<in> foldSet f id z"
using fold
proof (induct rule: foldSet.induct)
  case emptyI thus ?case by (force simp add: fold_insert_aux commute)
next
  case (insertI A x y)
    have "(insert x (insert b A), x \<cdot> (z \<cdot> y)) \<in> foldSet f (\<lambda>u. u) z"
      using insertI by force  --{*how does @{term id} get unfolded?*}
    thus ?case by (simp add: insert_commute AC)
qed

lemma (in ACf) foldSet_permute_diff:
assumes fold: "(A,x) \<in> foldSet f id b"
shows "!!a. \<lbrakk>a \<in> A; b \<notin> A\<rbrakk> \<Longrightarrow> (insert b (A-{a}), x) \<in> foldSet f id a"
using fold
proof (induct rule: foldSet.induct)
  case emptyI thus ?case by simp
next
  case (insertI A x y)
  have "a = x \<or> a \<in> A" using insertI by simp
  thus ?case
  proof
    assume "a = x"
    with insertI show ?thesis
      by (simp add: id_def [symmetric], blast intro: foldSet_insert_swap) 
  next
    assume ainA: "a \<in> A"
    hence "(insert x (insert b (A - {a})), x \<cdot> y) \<in> foldSet f id a"
      using insertI by (force simp: id_def)
    moreover
    have "insert x (insert b (A - {a})) = insert b (insert x A - {a})"
      using ainA insertI by blast
    ultimately show ?thesis by (simp add: id_def)
  qed
qed

lemma (in ACf) fold1_eq_fold:
     "[|finite A; a \<notin> A|] ==> fold1 f (insert a A) = fold f id a A"
apply (simp add: fold1_def fold_def) 
apply (rule the_equality)
apply (best intro: foldSet_determ theI dest: finite_imp_foldSet [of _ f id]) 
apply (rule sym, clarify)
apply (case_tac "Aa=A")
 apply (best intro: the_equality foldSet_determ)  
apply (subgoal_tac "(A,x) \<in> foldSet f id a") 
 apply (best intro: the_equality foldSet_determ)  
apply (subgoal_tac "insert aa (Aa - {a}) = A") 
 prefer 2 apply (blast elim: equalityE) 
apply (auto dest: foldSet_permute_diff [where a=a]) 
done

lemma nonempty_iff: "(A \<noteq> {}) = (\<exists>x B. A = insert x B & x \<notin> B)"
apply safe
apply simp 
apply (drule_tac x=x in spec)
apply (drule_tac x="A-{x}" in spec, auto) 
done

lemma (in ACf) fold1_insert:
  assumes nonempty: "A \<noteq> {}" and A: "finite A" "x \<notin> A"
  shows "fold1 f (insert x A) = f x (fold1 f A)"
proof -
  from nonempty obtain a A' where "A = insert a A' & a ~: A'" 
    by (auto simp add: nonempty_iff)
  with A show ?thesis
    by (simp add: insert_commute [of x] fold1_eq_fold eq_commute) 
qed

lemma (in ACIf) fold1_insert_idem [simp]:
  assumes nonempty: "A \<noteq> {}" and A: "finite A" 
  shows "fold1 f (insert x A) = f x (fold1 f A)"
proof -
  from nonempty obtain a A' where A': "A = insert a A' & a ~: A'" 
    by (auto simp add: nonempty_iff)
  show ?thesis
  proof cases
    assume "a = x"
    thus ?thesis 
    proof cases
      assume "A' = {}"
      with prems show ?thesis by (simp add: idem) 
    next
      assume "A' \<noteq> {}"
      with prems show ?thesis
	by (simp add: fold1_insert assoc [symmetric] idem) 
    qed
  next
    assume "a \<noteq> x"
    with prems show ?thesis
      by (simp add: insert_commute fold1_eq_fold fold_insert_idem)
  qed
qed


text{* Now the recursion rules for definitions: *}

lemma fold1_singleton_def: "g \<equiv> fold1 f \<Longrightarrow> g {a} = a"
by(simp add:fold1_singleton)

lemma (in ACf) fold1_insert_def:
  "\<lbrakk> g \<equiv> fold1 f; finite A; x \<notin> A; A \<noteq> {} \<rbrakk> \<Longrightarrow> g(insert x A) = x \<cdot> (g A)"
by(simp add:fold1_insert)

lemma (in ACIf) fold1_insert_idem_def:
  "\<lbrakk> g \<equiv> fold1 f; finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> g(insert x A) = x \<cdot> (g A)"
by(simp add:fold1_insert_idem)

subsubsection{* Determinacy for @{term fold1Set} *}

text{*Not actually used!!*}

lemma (in ACf) foldSet_permute:
  "[|(insert a A, x) \<in> foldSet f id b; a \<notin> A; b \<notin> A|]
   ==> (insert b A, x) \<in> foldSet f id a"
apply (case_tac "a=b") 
apply (auto dest: foldSet_permute_diff) 
done

lemma (in ACf) fold1Set_determ:
  "(A, x) \<in> fold1Set f ==> (A, y) \<in> fold1Set f ==> y = x"
proof (clarify elim!: fold1Set.cases)
  fix A x B y a b
  assume Ax: "(A, x) \<in> foldSet f id a"
  assume By: "(B, y) \<in> foldSet f id b"
  assume anotA:  "a \<notin> A"
  assume bnotB:  "b \<notin> B"
  assume eq: "insert a A = insert b B"
  show "y=x"
  proof cases
    assume same: "a=b"
    hence "A=B" using anotA bnotB eq by (blast elim!: equalityE)
    thus ?thesis using Ax By same by (blast intro: foldSet_determ)
  next
    assume diff: "a\<noteq>b"
    let ?D = "B - {a}"
    have B: "B = insert a ?D" and A: "A = insert b ?D"
     and aB: "a \<in> B" and bA: "b \<in> A"
      using eq anotA bnotB diff by (blast elim!:equalityE)+
    with aB bnotB By
    have "(insert b ?D, y) \<in> foldSet f id a" 
      by (auto intro: foldSet_permute simp add: insert_absorb)
    moreover
    have "(insert b ?D, x) \<in> foldSet f id a"
      by (simp add: A [symmetric] Ax) 
    ultimately show ?thesis by (blast intro: foldSet_determ) 
  qed
qed

lemma (in ACf) fold1Set_equality: "(A, y) : fold1Set f ==> fold1 f A = y"
  by (unfold fold1_def) (blast intro: fold1Set_determ)

declare
  empty_foldSetE [rule del]   foldSet.intros [rule del]
  empty_fold1SetE [rule del]  insert_fold1SetE [rule del]
  -- {* No more proves involve these relations. *}

subsubsection{* Semi-Lattices *}

locale ACIfSL = ACIf +
  fixes below :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl "\<sqsubseteq>" 50)
  assumes below_def: "(x \<sqsubseteq> y) = (x\<cdot>y = x)"

locale ACIfSLlin = ACIfSL +
  assumes lin: "x\<cdot>y \<in> {x,y}"

lemma (in ACIfSL) below_refl[simp]: "x \<sqsubseteq> x"
by(simp add: below_def idem)

lemma (in ACIfSL) below_f_conv[simp]: "x \<sqsubseteq> y \<cdot> z = (x \<sqsubseteq> y \<and> x \<sqsubseteq> z)"
proof
  assume "x \<sqsubseteq> y \<cdot> z"
  hence xyzx: "x \<cdot> (y \<cdot> z) = x"  by(simp add: below_def)
  have "x \<cdot> y = x"
  proof -
    have "x \<cdot> y = (x \<cdot> (y \<cdot> z)) \<cdot> y" by(rule subst[OF xyzx], rule refl)
    also have "\<dots> = x \<cdot> (y \<cdot> z)" by(simp add:ACI)
    also have "\<dots> = x" by(rule xyzx)
    finally show ?thesis .
  qed
  moreover have "x \<cdot> z = x"
  proof -
    have "x \<cdot> z = (x \<cdot> (y \<cdot> z)) \<cdot> z" by(rule subst[OF xyzx], rule refl)
    also have "\<dots> = x \<cdot> (y \<cdot> z)" by(simp add:ACI)
    also have "\<dots> = x" by(rule xyzx)
    finally show ?thesis .
  qed
  ultimately show "x \<sqsubseteq> y \<and> x \<sqsubseteq> z" by(simp add: below_def)
next
  assume a: "x \<sqsubseteq> y \<and> x \<sqsubseteq> z"
  hence y: "x \<cdot> y = x" and z: "x \<cdot> z = x" by(simp_all add: below_def)
  have "x \<cdot> (y \<cdot> z) = (x \<cdot> y) \<cdot> z" by(simp add:assoc)
  also have "x \<cdot> y = x" using a by(simp_all add: below_def)
  also have "x \<cdot> z = x" using a by(simp_all add: below_def)
  finally show "x \<sqsubseteq> y \<cdot> z" by(simp_all add: below_def)
qed

lemma (in ACIfSLlin) above_f_conv:
 "x \<cdot> y \<sqsubseteq> z = (x \<sqsubseteq> z \<or> y \<sqsubseteq> z)"
proof
  assume a: "x \<cdot> y \<sqsubseteq> z"
  have "x \<cdot> y = x \<or> x \<cdot> y = y" using lin[of x y] by simp
  thus "x \<sqsubseteq> z \<or> y \<sqsubseteq> z"
  proof
    assume "x \<cdot> y = x" hence "x \<sqsubseteq> z" by(rule subst)(rule a) thus ?thesis ..
  next
    assume "x \<cdot> y = y" hence "y \<sqsubseteq> z" by(rule subst)(rule a) thus ?thesis ..
  qed
next
  assume "x \<sqsubseteq> z \<or> y \<sqsubseteq> z"
  thus "x \<cdot> y \<sqsubseteq> z"
  proof
    assume a: "x \<sqsubseteq> z"
    have "(x \<cdot> y) \<cdot> z = (x \<cdot> z) \<cdot> y" by(simp add:ACI)
    also have "x \<cdot> z = x" using a by(simp add:below_def)
    finally show "x \<cdot> y \<sqsubseteq> z" by(simp add:below_def)
  next
    assume a: "y \<sqsubseteq> z"
    have "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)" by(simp add:ACI)
    also have "y \<cdot> z = y" using a by(simp add:below_def)
    finally show "x \<cdot> y \<sqsubseteq> z" by(simp add:below_def)
  qed
qed


subsubsection{* Lemmas about @{text fold1} *}

lemma (in ACf) fold1_Un:
assumes A: "finite A" "A \<noteq> {}"
shows "finite B \<Longrightarrow> B \<noteq> {} \<Longrightarrow> A Int B = {} \<Longrightarrow>
       fold1 f (A Un B) = f (fold1 f A) (fold1 f B)"
using A
proof(induct rule:finite_ne_induct)
  case singleton thus ?case by(simp add:fold1_insert)
next
  case insert thus ?case by (simp add:fold1_insert assoc)
qed

lemma (in ACIf) fold1_Un2:
assumes A: "finite A" "A \<noteq> {}"
shows "finite B \<Longrightarrow> B \<noteq> {} \<Longrightarrow>
       fold1 f (A Un B) = f (fold1 f A) (fold1 f B)"
using A
proof(induct rule:finite_ne_induct)
  case singleton thus ?case by(simp add:fold1_insert_idem)
next
  case insert thus ?case by (simp add:fold1_insert_idem assoc)
qed

lemma (in ACf) fold1_in:
  assumes A: "finite (A)" "A \<noteq> {}" and elem: "\<And>x y. x\<cdot>y \<in> {x,y}"
  shows "fold1 f A \<in> A"
using A
proof (induct rule:finite_ne_induct)
  case singleton thus ?case by simp
next
  case insert thus ?case using elem by (force simp add:fold1_insert)
qed

lemma (in ACIfSL) below_fold1_iff:
assumes A: "finite A" "A \<noteq> {}"
shows "x \<sqsubseteq> fold1 f A = (\<forall>a\<in>A. x \<sqsubseteq> a)"
using A
by(induct rule:finite_ne_induct) simp_all

lemma (in ACIfSL) fold1_belowI:
assumes A: "finite A" "A \<noteq> {}"
shows "a \<in> A \<Longrightarrow> fold1 f A \<sqsubseteq> a"
using A
proof (induct rule:finite_ne_induct)
  case singleton thus ?case by simp
next
  case (insert x F)
  from insert(5) have "a = x \<or> a \<in> F" by simp
  thus ?case
  proof
    assume "a = x" thus ?thesis using insert by(simp add:below_def ACI)
  next
    assume "a \<in> F"
    hence bel: "fold1 f F \<sqsubseteq> a" by(rule insert)
    have "fold1 f (insert x F) \<cdot> a = x \<cdot> (fold1 f F \<cdot> a)"
      using insert by(simp add:below_def ACI)
    also have "fold1 f F \<cdot> a = fold1 f F"
      using bel  by(simp add:below_def ACI)
    also have "x \<cdot> \<dots> = fold1 f (insert x F)"
      using insert by(simp add:below_def ACI)
    finally show ?thesis  by(simp add:below_def)
  qed
qed

lemma (in ACIfSLlin) fold1_below_iff:
assumes A: "finite A" "A \<noteq> {}"
shows "fold1 f A \<sqsubseteq> x = (\<exists>a\<in>A. a \<sqsubseteq> x)"
using A
by(induct rule:finite_ne_induct)(simp_all add:above_f_conv)


subsubsection{* Lattices *}

locale Lattice = lattice +
  fixes Inf :: "'a set \<Rightarrow> 'a" ("\<Sqinter>_" [900] 900)
  and Sup :: "'a set \<Rightarrow> 'a" ("\<Squnion>_" [900] 900)
  defines "Inf == fold1 inf"  and "Sup == fold1 sup"

locale Distrib_Lattice = distrib_lattice + Lattice

text{* Lattices are semilattices *}

lemma (in Lattice) ACf_inf: "ACf inf"
by(blast intro: ACf.intro inf_commute inf_assoc)

lemma (in Lattice) ACf_sup: "ACf sup"
by(blast intro: ACf.intro sup_commute sup_assoc)

lemma (in Lattice) ACIf_inf: "ACIf inf"
apply(rule ACIf.intro)
apply(rule ACf_inf)
apply(rule ACIf_axioms.intro)
apply(rule inf_idem)
done

lemma (in Lattice) ACIf_sup: "ACIf sup"
apply(rule ACIf.intro)
apply(rule ACf_sup)
apply(rule ACIf_axioms.intro)
apply(rule sup_idem)
done

lemma (in Lattice) ACIfSL_inf: "ACIfSL inf (op \<sqsubseteq>)"
apply(rule ACIfSL.intro)
apply(rule ACf_inf)
apply(rule ACIf.axioms[OF ACIf_inf])
apply(rule ACIfSL_axioms.intro)
apply(rule iffI)
 apply(blast intro: antisym inf_le1 inf_le2 inf_least refl)
apply(erule subst)
apply(rule inf_le2)
done

lemma (in Lattice) ACIfSL_sup: "ACIfSL sup (%x y. y \<sqsubseteq> x)"
apply(rule ACIfSL.intro)
apply(rule ACf_sup)
apply(rule ACIf.axioms[OF ACIf_sup])
apply(rule ACIfSL_axioms.intro)
apply(rule iffI)
 apply(blast intro: antisym sup_ge1 sup_ge2 sup_greatest refl)
apply(erule subst)
apply(rule sup_ge2)
done


subsubsection{* Fold laws in lattices *}

lemma (in Lattice) Inf_le_Sup[simp]: "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> \<Sqinter>A \<sqsubseteq> \<Squnion>A"
apply(unfold Sup_def Inf_def)
apply(subgoal_tac "EX a. a:A")
prefer 2 apply blast
apply(erule exE)
apply(rule trans)
apply(erule (2) ACIfSL.fold1_belowI[OF ACIfSL_inf])
apply(erule (2) ACIfSL.fold1_belowI[OF ACIfSL_sup])
done

lemma (in Lattice) sup_Inf_absorb[simp]:
  "\<lbrakk> finite A; A \<noteq> {}; a \<in> A \<rbrakk> \<Longrightarrow> (a \<squnion> \<Sqinter>A) = a"
apply(subst sup_commute)
apply(simp add:Inf_def sup_absorb ACIfSL.fold1_belowI[OF ACIfSL_inf])
done

lemma (in Lattice) inf_Sup_absorb[simp]:
  "\<lbrakk> finite A; A \<noteq> {}; a \<in> A \<rbrakk> \<Longrightarrow> (a \<sqinter> \<Squnion>A) = a"
by(simp add:Sup_def inf_absorb ACIfSL.fold1_belowI[OF ACIfSL_sup])


lemma (in Distrib_Lattice) sup_Inf1_distrib:
assumes A: "finite A" "A \<noteq> {}"
shows "(x \<squnion> \<Sqinter>A) = \<Sqinter>{x \<squnion> a|a. a \<in> A}"
using A
proof (induct rule: finite_ne_induct)
  case singleton thus ?case by(simp add:Inf_def)
next
  case (insert y A)
  have fin: "finite {x \<squnion> a |a. a \<in> A}"
    by(fast intro: finite_surj[where f = "%a. x \<squnion> a", OF insert(1)])
  have "x \<squnion> \<Sqinter> (insert y A) = x \<squnion> (y \<sqinter> \<Sqinter> A)"
    using insert by(simp add:ACf.fold1_insert_def[OF ACf_inf Inf_def])
  also have "\<dots> = (x \<squnion> y) \<sqinter> (x \<squnion> \<Sqinter> A)" by(rule sup_inf_distrib1)
  also have "x \<squnion> \<Sqinter> A = \<Sqinter>{x \<squnion> a|a. a \<in> A}" using insert by simp
  also have "(x \<squnion> y) \<sqinter> \<dots> = \<Sqinter> (insert (x \<squnion> y) {x \<squnion> a |a. a \<in> A})"
    using insert by(simp add:ACIf.fold1_insert_idem_def[OF ACIf_inf Inf_def fin])
  also have "insert (x\<squnion>y) {x\<squnion>a |a. a \<in> A} = {x\<squnion>a |a. a \<in> insert y A}"
    by blast
  finally show ?case .
qed

lemma (in Distrib_Lattice) sup_Inf2_distrib:
assumes A: "finite A" "A \<noteq> {}" and B: "finite B" "B \<noteq> {}"
shows "(\<Sqinter>A \<squnion> \<Sqinter>B) = \<Sqinter>{a \<squnion> b|a b. a \<in> A \<and> b \<in> B}"
using A
proof (induct rule: finite_ne_induct)
  case singleton thus ?case
    by(simp add: sup_Inf1_distrib[OF B] fold1_singleton_def[OF Inf_def])
next
  case (insert x A)
  have finB: "finite {x \<squnion> b |b. b \<in> B}"
    by(fast intro: finite_surj[where f = "%b. x \<squnion> b", OF B(1)])
  have finAB: "finite {a \<squnion> b |a b. a \<in> A \<and> b \<in> B}"
  proof -
    have "{a \<squnion> b |a b. a \<in> A \<and> b \<in> B} = (UN a:A. UN b:B. {a \<squnion> b})"
      by blast
    thus ?thesis by(simp add: insert(1) B(1))
  qed
  have ne: "{a \<squnion> b |a b. a \<in> A \<and> b \<in> B} \<noteq> {}" using insert B by blast
  have "\<Sqinter>(insert x A) \<squnion> \<Sqinter>B = (x \<sqinter> \<Sqinter>A) \<squnion> \<Sqinter>B"
    using insert by(simp add:ACIf.fold1_insert_idem_def[OF ACIf_inf Inf_def])
  also have "\<dots> = (x \<squnion> \<Sqinter>B) \<sqinter> (\<Sqinter>A \<squnion> \<Sqinter>B)" by(rule sup_inf_distrib2)
  also have "\<dots> = \<Sqinter>{x \<squnion> b|b. b \<in> B} \<sqinter> \<Sqinter>{a \<squnion> b|a b. a \<in> A \<and> b \<in> B}"
    using insert by(simp add:sup_Inf1_distrib[OF B])
  also have "\<dots> = \<Sqinter>({x\<squnion>b |b. b \<in> B} \<union> {a\<squnion>b |a b. a \<in> A \<and> b \<in> B})"
    (is "_ = \<Sqinter>?M")
    using B insert
    by(simp add:Inf_def ACIf.fold1_Un2[OF ACIf_inf finB _ finAB ne])
  also have "?M = {a \<squnion> b |a b. a \<in> insert x A \<and> b \<in> B}"
    by blast
  finally show ?case .
qed


subsection{*Min and Max*}

text{* As an application of @{text fold1} we define the minimal and
maximal element of a (non-empty) set over a linear order. *}

constdefs
  Min :: "('a::linorder)set => 'a"
  "Min  ==  fold1 min"

  Max :: "('a::linorder)set => 'a"
  "Max  ==  fold1 max"


text{* Before we can do anything, we need to show that @{text min} and
@{text max} are ACI and the ordering is linear: *}

interpretation min: ACf ["min:: 'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a"]
apply(rule ACf.intro)
apply(auto simp:min_def)
done

interpretation min: ACIf ["min:: 'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a"]
apply(rule ACIf_axioms.intro)
apply(auto simp:min_def)
done

interpretation max: ACf ["max :: 'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a"]
apply(rule ACf.intro)
apply(auto simp:max_def)
done

interpretation max: ACIf ["max:: 'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a"]
apply(rule ACIf_axioms.intro)
apply(auto simp:max_def)
done

interpretation min:
  ACIfSL ["min:: 'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a" "op \<le>"]
apply(rule ACIfSL_axioms.intro)
apply(auto simp:min_def)
done

interpretation min:
  ACIfSLlin ["min :: 'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a" "op \<le>"]
apply(rule ACIfSLlin_axioms.intro)
apply(auto simp:min_def)
done

interpretation max:
  ACIfSL ["max :: 'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a" "%x y. y\<le>x"]
apply(rule ACIfSL_axioms.intro)
apply(auto simp:max_def)
done

interpretation max:
  ACIfSLlin ["max :: 'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a" "%x y. y\<le>x"]
apply(rule ACIfSLlin_axioms.intro)
apply(auto simp:max_def)
done

interpretation min_max:
  Lattice ["op \<le>" "min :: 'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a" "max" "Min" "Max"]
apply -
apply(rule Min_def)
apply(rule Max_def)
done


interpretation min_max:
  Distrib_Lattice ["op \<le>" "min :: 'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a" "max" "Min" "Max"]
.

text{* Now we instantiate the recursion equations and declare them
simplification rules: *}

(* Making Min (resp. Max) a defined parameter of a locale suitably
  extending ACIf could make the following interpretations more automatic. *)

declare
  fold1_singleton_def[OF Min_def, simp]
  min.fold1_insert_idem_def[OF Min_def, simp]
  fold1_singleton_def[OF Max_def, simp]
  max.fold1_insert_idem_def[OF Max_def, simp]

text{* Now we instantiate some @{text fold1} properties: *}

lemma Min_in [simp]:
  shows "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> Min A \<in> A"
using min.fold1_in
by(fastsimp simp: Min_def min_def)

lemma Max_in [simp]:
  shows "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> Max A \<in> A"
using max.fold1_in
by(fastsimp simp: Max_def max_def)

lemma Min_le [simp]: "\<lbrakk> finite A; A \<noteq> {}; x \<in> A \<rbrakk> \<Longrightarrow> Min A \<le> x"
by(simp add: Min_def min.fold1_belowI)

lemma Max_ge [simp]: "\<lbrakk> finite A; A \<noteq> {}; x \<in> A \<rbrakk> \<Longrightarrow> x \<le> Max A"
by(simp add: Max_def max.fold1_belowI)

lemma Min_ge_iff[simp]:
  "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> (x \<le> Min A) = (\<forall>a\<in>A. x \<le> a)"
by(simp add: Min_def min.below_fold1_iff)

lemma Max_le_iff[simp]:
  "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> (Max A \<le> x) = (\<forall>a\<in>A. a \<le> x)"
by(simp add: Max_def max.below_fold1_iff)

lemma Min_le_iff:
  "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> (Min A \<le> x) = (\<exists>a\<in>A. a \<le> x)"
by(simp add: Min_def min.fold1_below_iff)

lemma Max_ge_iff:
  "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> (x \<le> Max A) = (\<exists>a\<in>A. x \<le> a)"
by(simp add: Max_def max.fold1_below_iff)

end
