(* 
  Author:     Jeremy Dawson and Gerwin Klein, NICTA

  Consequences of type definition theorems, and of extended type definition. theorems
*)

header {* Type Definition Theorems *}

theory Misc_Typedef
imports Main
begin

section "More lemmas about normal type definitions"

lemma
  tdD1: "type_definition Rep Abs A \<Longrightarrow> \<forall>x. Rep x \<in> A" and
  tdD2: "type_definition Rep Abs A \<Longrightarrow> \<forall>x. Abs (Rep x) = x" and
  tdD3: "type_definition Rep Abs A \<Longrightarrow> \<forall>y. y \<in> A \<longrightarrow> Rep (Abs y) = y"
  by (auto simp: type_definition_def)

lemma td_nat_int: 
  "type_definition int nat (Collect (op <= 0))"
  unfolding type_definition_def by auto

context type_definition
begin

declare Rep [iff] Rep_inverse [simp] Rep_inject [simp]

lemma Abs_eqD: "Abs x = Abs y ==> x \<in> A ==> y \<in> A ==> x = y"
  by (simp add: Abs_inject)
   
lemma Abs_inverse': 
  "r : A ==> Abs r = a ==> Rep a = r"
  by (safe elim!: Abs_inverse)

lemma Rep_comp_inverse: 
  "Rep o f = g ==> Abs o g = f"
  using Rep_inverse by auto

lemma Rep_eqD [elim!]: "Rep x = Rep y ==> x = y"
  by simp

lemma Rep_inverse': "Rep a = r ==> Abs r = a"
  by (safe intro!: Rep_inverse)

lemma comp_Abs_inverse: 
  "f o Abs = g ==> g o Rep = f"
  using Rep_inverse by auto

lemma set_Rep: 
  "A = range Rep"
proof (rule set_eqI)
  fix x
  show "(x \<in> A) = (x \<in> range Rep)"
    by (auto dest: Abs_inverse [of x, symmetric])
qed  

lemma set_Rep_Abs: "A = range (Rep o Abs)"
proof (rule set_eqI)
  fix x
  show "(x \<in> A) = (x \<in> range (Rep o Abs))"
    by (auto dest: Abs_inverse [of x, symmetric])
qed  

lemma Abs_inj_on: "inj_on Abs A"
  unfolding inj_on_def 
  by (auto dest: Abs_inject [THEN iffD1])

lemma image: "Abs ` A = UNIV"
  by (auto intro!: image_eqI)

lemmas td_thm = type_definition_axioms

lemma fns1: 
  "Rep o fa = fr o Rep | fa o Abs = Abs o fr ==> Abs o fr o Rep = fa"
  by (auto dest: Rep_comp_inverse elim: comp_Abs_inverse simp: o_assoc)

lemmas fns1a = disjI1 [THEN fns1]
lemmas fns1b = disjI2 [THEN fns1]

lemma fns4:
  "Rep o fa o Abs = fr ==> 
   Rep o fa = fr o Rep & fa o Abs = Abs o fr"
  by auto

end

interpretation nat_int: type_definition int nat "Collect (op <= 0)"
  by (rule td_nat_int)

declare
  nat_int.Rep_cases [cases del]
  nat_int.Abs_cases [cases del]
  nat_int.Rep_induct [induct del]
  nat_int.Abs_induct [induct del]


subsection "Extended form of type definition predicate"

lemma td_conds:
  "norm o norm = norm ==> (fr o norm = norm o fr) = 
    (norm o fr o norm = fr o norm & norm o fr o norm = norm o fr)"
  apply safe
    apply (simp_all add: o_assoc [symmetric])
   apply (simp_all add: o_assoc)
  done

lemma fn_comm_power:
  "fa o tr = tr o fr ==> fa ^^ n o tr = tr o fr ^^ n" 
  apply (rule ext) 
  apply (induct n)
   apply (auto dest: fun_cong)
  done

lemmas fn_comm_power' =
  ext [THEN fn_comm_power, THEN fun_cong, unfolded o_def]


locale td_ext = type_definition +
  fixes norm
  assumes eq_norm: "\<And>x. Rep (Abs x) = norm x"
begin

lemma Abs_norm [simp]: 
  "Abs (norm x) = Abs x"
  using eq_norm [of x] by (auto elim: Rep_inverse')

lemma td_th:
  "g o Abs = f ==> f (Rep x) = g x"
  by (drule comp_Abs_inverse [symmetric]) simp

lemma eq_norm': "Rep o Abs = norm"
  by (auto simp: eq_norm)

lemma norm_Rep [simp]: "norm (Rep x) = Rep x"
  by (auto simp: eq_norm' intro: td_th)

lemmas td = td_thm

lemma set_iff_norm: "w : A <-> w = norm w"
  by (auto simp: set_Rep_Abs eq_norm' eq_norm [symmetric])

lemma inverse_norm: 
  "(Abs n = w) = (Rep w = norm n)"
  apply (rule iffI)
   apply (clarsimp simp add: eq_norm)
  apply (simp add: eq_norm' [symmetric])
  done

lemma norm_eq_iff: 
  "(norm x = norm y) = (Abs x = Abs y)"
  by (simp add: eq_norm' [symmetric])

lemma norm_comps: 
  "Abs o norm = Abs" 
  "norm o Rep = Rep" 
  "norm o norm = norm"
  by (auto simp: eq_norm' [symmetric] o_def)

lemmas norm_norm [simp] = norm_comps

lemma fns5: 
  "Rep o fa o Abs = fr ==> 
  fr o norm = fr & norm o fr = fr"
  by (fold eq_norm') auto

(* following give conditions for converses to td_fns1
  the condition (norm o fr o norm = fr o norm) says that 
  fr takes normalised arguments to normalised results,
  (norm o fr o norm = norm o fr) says that fr 
  takes norm-equivalent arguments to norm-equivalent results,
  (fr o norm = fr) says that fr 
  takes norm-equivalent arguments to the same result, and 
  (norm o fr = fr) says that fr takes any argument to a normalised result 
  *)
lemma fns2: 
  "Abs o fr o Rep = fa ==> 
   (norm o fr o norm = fr o norm) = (Rep o fa = fr o Rep)"
  apply (fold eq_norm')
  apply safe
   prefer 2
   apply (simp add: o_assoc)
  apply (rule ext)
  apply (drule_tac x="Rep x" in fun_cong)
  apply auto
  done

lemma fns3: 
  "Abs o fr o Rep = fa ==> 
   (norm o fr o norm = norm o fr) = (fa o Abs = Abs o fr)"
  apply (fold eq_norm')
  apply safe
   prefer 2
   apply (simp add: o_assoc [symmetric])
  apply (rule ext)
  apply (drule fun_cong)
  apply simp
  done

lemma fns: 
  "fr o norm = norm o fr ==> 
    (fa o Abs = Abs o fr) = (Rep o fa = fr o Rep)"
  apply safe
   apply (frule fns1b)
   prefer 2 
   apply (frule fns1a) 
   apply (rule fns3 [THEN iffD1])
     prefer 3
     apply (rule fns2 [THEN iffD1])
       apply (simp_all add: o_assoc [symmetric])
   apply (simp_all add: o_assoc)
  done

lemma range_norm:
  "range (Rep o Abs) = A"
  by (simp add: set_Rep_Abs)

end

lemmas td_ext_def' =
  td_ext_def [unfolded type_definition_def td_ext_axioms_def]

end

