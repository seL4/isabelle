(*  Title:      HOL/MicroJava/J/JBasis.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 TU Muenchen

Some auxiliary definitions.
*)

theory JBasis = Main: 

lemmas [simp] = Let_def

section "unique"
 
constdefs

  unique  :: "('a \\<times> 'b) list => bool"
 "unique  == nodups \\<circ> map fst"


lemma fst_in_set_lemma [rule_format (no_asm)]: 
      "(x, y) : set xys --> x : fst ` set xys"
apply (induct_tac "xys")
apply  auto
done

lemma unique_Nil [simp]: "unique []"
apply (unfold unique_def)
apply (simp (no_asm))
done

lemma unique_Cons [simp]: "unique ((x,y)#l) = (unique l & (!y. (x,y) ~: set l))"
apply (unfold unique_def)
apply (auto dest: fst_in_set_lemma)
done

lemma unique_append [rule_format (no_asm)]: "unique l' ==> unique l --> 
 (!(x,y):set l. !(x',y'):set l'. x' ~= x) --> unique (l @ l')"
apply (induct_tac "l")
apply  (auto dest: fst_in_set_lemma)
done

lemma unique_map_inj [rule_format (no_asm)]: 
  "unique l --> inj f --> unique (map (%(k,x). (f k, g k x)) l)"
apply (induct_tac "l")
apply  (auto dest: fst_in_set_lemma simp add: inj_eq)
done

section "More about Maps"

lemma map_of_SomeI [rule_format (no_asm)]: 
  "unique l --> (k, x) : set l --> map_of l k = Some x"
apply (induct_tac "l")
apply  auto
done

lemma Ball_set_table_: 
  "(\\<forall>(x,y)\\<in>set l. P x y) --> (\\<forall>x. \\<forall>y. map_of l x = Some y --> P x y)"
apply(induct_tac "l")
apply(simp_all (no_asm))
apply safe
apply auto
done
lemmas Ball_set_table = Ball_set_table_ [THEN mp];

lemma table_of_remap_SomeD [rule_format (no_asm)]: 
"map_of (map (\<lambda>((k,k'),x). (k,(k',x))) t) k = Some (k',x) --> 
 map_of t (k, k') = Some x"
apply (induct_tac "t")
apply  auto
done

end

