(*  Title:      HOL/Quotient_Examples/Lift_Fun.thy
    Author:     Ondrej Kuncar
*)

header {* Example of lifting definitions with contravariant or co/contravariant type variables *}


theory Lift_Fun
imports Main
begin

text {* This file is meant as a test case for features introduced in the changeset 2d8949268303. 
  It contains examples of lifting definitions with quotients that have contravariant 
  type variables or type variables which are covariant and contravariant in the same time. *}

subsection {* Contravariant type variables *}

text {* 'a is a contravariant type variable and we are able to map over this variable
  in the following four definitions. This example is based on HOL/Fun.thy. *}

quotient_type
('a, 'b) fun' (infixr "\<rightarrow>" 55) = "'a \<Rightarrow> 'b" / "op =" 
  by (simp add: identity_equivp)

quotient_definition "comp' :: ('b \<rightarrow> 'c) \<rightarrow> ('a \<rightarrow> 'b) \<rightarrow> 'a \<rightarrow> 'c"  is
  "comp :: ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" done

quotient_definition "fcomp' :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'c" is 
  fcomp done

quotient_definition "map_fun' :: ('c \<rightarrow> 'a) \<rightarrow> ('b \<rightarrow> 'd) \<rightarrow> ('a \<rightarrow> 'b) \<rightarrow> 'c \<rightarrow> 'd" 
  is "map_fun::('c \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'd" done

quotient_definition "inj_on' :: ('a \<rightarrow> 'b) \<rightarrow> 'a set \<rightarrow> bool" is inj_on done

quotient_definition "bij_betw' :: ('a \<rightarrow> 'b) \<rightarrow> 'a set \<rightarrow> 'b set \<rightarrow> bool" is bij_betw done


subsection {* Co/Contravariant type variables *} 

text {* 'a is a covariant and contravariant type variable in the same time.
  The following example is a bit artificial. We haven't had a natural one yet. *}

quotient_type 'a endofun = "'a \<Rightarrow> 'a" / "op =" by (simp add: identity_equivp)

definition map_endofun' :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ('a => 'a) \<Rightarrow> ('b => 'b)"
  where "map_endofun' f g e = map_fun g f e"

quotient_definition "map_endofun :: ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a endofun \<Rightarrow> 'b endofun" is
  map_endofun' done

text {* Registration of the map function for 'a endofun. *}

enriched_type map_endofun : map_endofun
proof -
  have "\<forall> x. abs_endofun (rep_endofun x) = x" using Quotient_endofun by (auto simp: Quotient_def)
  then show "map_endofun id id = id" 
    by (auto simp: map_endofun_def map_endofun'_def map_fun_def fun_eq_iff)
  
  have a:"\<forall> x. rep_endofun (abs_endofun x) = x" using Quotient_endofun 
    Quotient_rep_abs[of "(op =)" abs_endofun rep_endofun] by blast
  show "\<And>f g h i. map_endofun f g \<circ> map_endofun h i = map_endofun (f \<circ> h) (i \<circ> g)"
    by (auto simp: map_endofun_def map_endofun'_def map_fun_def fun_eq_iff) (simp add: a o_assoc) 
qed

quotient_definition "endofun_id_id :: ('a endofun) endofun" is "id :: ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" done

term  endofun_id_id
thm  endofun_id_id_def

quotient_type 'a endofun' = "'a endofun" / "op =" by (simp add: identity_equivp)

text {* We have to map "'a endofun" to "('a endofun') endofun", i.e., mapping (lifting)
  over a type variable which is a covariant and contravariant type variable. *}

quotient_definition "endofun'_id_id :: ('a endofun') endofun'" is endofun_id_id done

term  endofun'_id_id
thm  endofun'_id_id_def


end
