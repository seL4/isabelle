(*  Title:      HOL/MicroJava/J/JBasis.ML
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 TU Muenchen
*)

(*###TO Product_Type*)
Goalw [split_def] "Eps (split P) = (SOME xy. P (fst xy) (snd xy))";
by (rtac refl 1);
qed "select_split";

Addsimps [Let_def];

bind_thm ("if_def2", read_instantiate [("P","\\<lambda>x. x")] split_if);

(* ### To HOL.ML *)
Goal "[| ?!x. P x; P y |] ==> Eps P = y"; 
by (rtac some_equality 1);
by  (atac 1);
by (etac ex1E 1);
by (etac all_dupE 1);
by (fast_tac HOL_cs 1);
qed "ex1_some_eq_trivial";


section "unique";

Goal "(x, y) : set xys --> x : fst ` set xys";
by (induct_tac "xys" 1);
by  Auto_tac;
qed_spec_mp "fst_in_set_lemma";

Goalw [unique_def] "unique []";
by (Simp_tac 1);
qed "unique_Nil";

Goalw [unique_def] "unique ((x,y)#l) = (unique l & (!y. (x,y) ~: set l))";
by  (auto_tac (claset() addDs [fst_in_set_lemma],simpset()));
qed "unique_Cons";

Addsimps [unique_Nil,unique_Cons];

Goal "unique l' ==> unique l --> \
\ (!(x,y):set l. !(x',y'):set l'. x' ~= x) --> unique (l @ l')";
by (induct_tac "l" 1);
by  (auto_tac (claset() addDs [fst_in_set_lemma],simpset()));
qed_spec_mp "unique_append";

Goal "unique l --> inj f --> unique (map (%(k,x). (f k, g k x)) l)";
by (induct_tac "l" 1);
by  (auto_tac (claset() addDs [fst_in_set_lemma],simpset()addsimps[inj_eq]));
qed_spec_mp "unique_map_inj";

(* More about Maps *)

(*###Addsimps [fun_upd_same, fun_upd_other];*)

Goal "unique l --> (k, x) : set l --> map_of l k = Some x";
by (induct_tac "l" 1);
by  Auto_tac;
qed_spec_mp "map_of_SomeI";

Goal "(\\<forall>(x,y)\\<in>set l. P x y) --> (\\<forall>x. \\<forall>y. map_of l x = Some y --> P x y)";
by(induct_tac "l" 1);
by(ALLGOALS Simp_tac);
by Safe_tac;
by Auto_tac;
bind_thm("Ball_set_table",result() RS mp);

Goal "map_of (map (\\<lambda>((k,k'),x). (k,(k',x))) t) k = Some (k',x) --> \
\map_of t (k, k') = Some x";
by (induct_tac "t" 1);
by  Auto_tac;
qed_spec_mp "table_of_remap_SomeD";

(* ### To Map.ML *)
Goal "map_of (map (\\<lambda>(a,b). (a,f b)) xs) x = option_map f (map_of xs x)";
by (induct_tac "xs" 1);
by Auto_tac;
qed "map_of_map";
