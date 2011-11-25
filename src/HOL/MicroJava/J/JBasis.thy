(*  Title:      HOL/MicroJava/J/JBasis.thy
    Author:     David von Oheimb, TU Muenchen
*)

header {* 
  \chapter{Java Source Language}\label{cha:j}
  \isaheader{Some Auxiliary Definitions}
*}

theory JBasis imports Main "~~/src/HOL/Library/Transitive_Closure_Table" begin 

lemmas [simp] = Let_def

section "unique"
 
definition unique :: "('a \<times> 'b) list => bool" where
  "unique == distinct \<circ> map fst"


lemma fst_in_set_lemma: "(x, y) : set xys ==> x : fst ` set xys"
  by (induct xys) auto

lemma unique_Nil [simp]: "unique []"
  by (simp add: unique_def)

lemma unique_Cons [simp]: "unique ((x,y)#l) = (unique l & (!y. (x,y) ~: set l))"
  by (auto simp: unique_def dest: fst_in_set_lemma)

lemma unique_append: "unique l' ==> unique l ==>
    (!(x,y):set l. !(x',y'):set l'. x' ~= x) ==> unique (l @ l')"
  by (induct l) (auto dest: fst_in_set_lemma)

lemma unique_map_inj: "unique l ==> inj f ==> unique (map (%(k,x). (f k, g k x)) l)"
  by (induct l) (auto dest: fst_in_set_lemma simp add: inj_eq)


section "More about Maps"

lemma map_of_SomeI: "unique l ==> (k, x) : set l ==> map_of l k = Some x"
  by (induct l) auto

lemma Ball_set_table: "(\<forall>(x,y)\<in>set l. P x y) ==> (\<forall>x. \<forall>y. map_of l x = Some y --> P x y)"
  by (induct l) auto

lemma table_of_remap_SomeD:
  "map_of (map (\<lambda>((k,k'),x). (k,(k',x))) t) k = Some (k',x) ==>
    map_of t (k, k') = Some x"
  by (atomize (full), induct t) auto

end
