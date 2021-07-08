(*  Title:      HOL/Quotient_Examples/Lift_Fun.thy
    Author:     Ondrej Kuncar
*)

section \<open>Example of lifting definitions with contravariant or co/contravariant type variables\<close>


theory Lift_Fun
imports Main "HOL-Library.Quotient_Syntax"
begin

text \<open>This file is meant as a test case. 
  It contains examples of lifting definitions with quotients that have contravariant 
  type variables or type variables which are covariant and contravariant in the same time.\<close>

subsection \<open>Contravariant type variables\<close>

text \<open>'a is a contravariant type variable and we are able to map over this variable
  in the following four definitions. This example is based on HOL/Fun.thy.\<close>

quotient_type
('a, 'b) fun' (infixr "\<rightarrow>" 55) = "'a \<Rightarrow> 'b" / "(=)" 
  by (simp add: identity_equivp)

quotient_definition "comp' :: ('b \<rightarrow> 'c) \<rightarrow> ('a \<rightarrow> 'b) \<rightarrow> 'a \<rightarrow> 'c"  is
  "comp :: ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" done

quotient_definition "fcomp' :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'c" is 
  fcomp done

quotient_definition "map_fun' :: ('c \<rightarrow> 'a) \<rightarrow> ('b \<rightarrow> 'd) \<rightarrow> ('a \<rightarrow> 'b) \<rightarrow> 'c \<rightarrow> 'd" 
  is "map_fun::('c \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'd" done

quotient_definition "inj_on' :: ('a \<rightarrow> 'b) \<rightarrow> 'a set \<rightarrow> bool" is inj_on done

quotient_definition "bij_betw' :: ('a \<rightarrow> 'b) \<rightarrow> 'a set \<rightarrow> 'b set \<rightarrow> bool" is bij_betw done


subsection \<open>Co/Contravariant type variables\<close> 

text \<open>'a is a covariant and contravariant type variable in the same time.
  The following example is a bit artificial. We haven't had a natural one yet.\<close>

quotient_type 'a endofun = "'a \<Rightarrow> 'a" / "(=)" by (simp add: identity_equivp)

definition map_endofun' :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('a => 'a) \<Rightarrow> ('b => 'b)"
  where "map_endofun' f g e = map_fun g f e"

quotient_definition "map_endofun :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a endofun \<Rightarrow> 'b endofun" is
  map_endofun' done

text \<open>Registration of the map function for 'a endofun.\<close>

functor map_endofun : map_endofun
proof -
  have "\<forall> x. abs_endofun (rep_endofun x) = x" using Quotient3_endofun by (auto simp: Quotient3_def)
  then show "map_endofun id id = id" 
    by (auto simp: map_endofun_def map_endofun'_def map_fun_def fun_eq_iff)
  
  have a:"\<forall> x. rep_endofun (abs_endofun x) = x" using Quotient3_endofun 
    Quotient3_rep_abs[of "(=)" abs_endofun rep_endofun] by blast
  show "\<And>f g h i. map_endofun f g \<circ> map_endofun h i = map_endofun (f \<circ> h) (i \<circ> g)"
    by (auto simp: map_endofun_def map_endofun'_def map_fun_def fun_eq_iff) (simp add: a o_assoc) 
qed

text \<open>Relator for 'a endofun.\<close>

definition
  rel_endofun' :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> bool" 
where
  "rel_endofun' R = (\<lambda>f g. (R ===> R) f g)"

quotient_definition "rel_endofun :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a endofun \<Rightarrow> 'b endofun \<Rightarrow> bool" is
  rel_endofun' done

lemma endofun_quotient:
assumes a: "Quotient3 R Abs Rep"
shows "Quotient3 (rel_endofun R) (map_endofun Abs Rep) (map_endofun Rep Abs)"
proof (intro Quotient3I)
  show "\<And>a. map_endofun Abs Rep (map_endofun Rep Abs a) = a"
    by (metis (opaque_lifting, no_types) a abs_o_rep id_apply map_endofun.comp map_endofun.id o_eq_dest_lhs)
next
  show "\<And>a. rel_endofun R (map_endofun Rep Abs a) (map_endofun Rep Abs a)"
  using fun_quotient3[OF a a, THEN Quotient3_rep_reflp]
  unfolding rel_endofun_def map_endofun_def map_fun_def o_def map_endofun'_def rel_endofun'_def id_def 
    by (metis (mono_tags) Quotient3_endofun rep_abs_rsp)
next
  have abs_to_eq: "\<And> x y. abs_endofun x = abs_endofun y \<Longrightarrow> x = y" 
  by (drule arg_cong[where f=rep_endofun]) (simp add: Quotient3_rep_abs[OF Quotient3_endofun])
  fix r s
  show "rel_endofun R r s =
          (rel_endofun R r r \<and>
           rel_endofun R s s \<and> map_endofun Abs Rep r = map_endofun Abs Rep s)"
    apply(auto simp add: rel_endofun_def rel_endofun'_def map_endofun_def map_endofun'_def)
    using fun_quotient3[OF a a,THEN Quotient3_refl1]
    apply metis
    using fun_quotient3[OF a a,THEN Quotient3_refl2]
    apply metis
    using fun_quotient3[OF a a, THEN Quotient3_rel]
    apply metis
    by (auto intro: fun_quotient3[OF a a, THEN Quotient3_rel, THEN iffD1] simp add: abs_to_eq)
qed

declare [[mapQ3 endofun = (rel_endofun, endofun_quotient)]]

quotient_definition "endofun_id_id :: ('a endofun) endofun" is "id :: ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" done

term  endofun_id_id
thm  endofun_id_id_def

quotient_type 'a endofun' = "'a endofun" / "(=)" by (simp add: identity_equivp)

text \<open>We have to map "'a endofun" to "('a endofun') endofun", i.e., mapping (lifting)
  over a type variable which is a covariant and contravariant type variable.\<close>

quotient_definition "endofun'_id_id :: ('a endofun') endofun'" is endofun_id_id done

term  endofun'_id_id
thm  endofun'_id_id_def


end
