(*  Title:      HOL/UNITY/UNITYMisc.ML
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Some miscellaneous and add-hoc set theory concepts.

*)

(** Ad-hoc set-theory rules **)

Goal "Union(B) Int A = (UN b:B. b Int A)";
by Auto_tac;
qed "Int_Union_Union";

Goal "A Int Union(B) = (UN b:B. A Int b)";
by Auto_tac;
qed "Int_Union_Union2";


(** Needed in State theory for the current definition of variables 
where they are indexed by lists  **)

Goal "i:list(nat) ==> i:univ(0)";
by (dres_inst_tac [("B", "0")] list_into_univ 1);
by (blast_tac (claset() addIs [nat_into_univ]) 1);
by (assume_tac 1);
qed "list_nat_into_univ";


(** Simplication rules for Collect **)

(*Currently unused*)
Goal "{x:A. P(x)} Int B = {x : A Int B. P(x)}";
by Auto_tac;
qed "Collect_Int_left";

(*Currently unused*)
Goal "A Int {x:B. P(x)} = {x : A Int B. P(x)}";
by Auto_tac;
qed "Collect_Int_right";

Goal "{x:A. P(x) | Q(x)} = Collect(A, P) Un Collect(A, Q)";
by Auto_tac;
qed "Collect_disj_eq";

Goal "{x:A. P(x) & Q(x)} = Collect(A, P) Int Collect(A, Q)";
by Auto_tac;
qed "Collect_conj_eq";

Goal "Union(B) Int A = (UN C:B. C Int A)"; 
by (Blast_tac 1);
qed "Int_Union2";

Goal "A Int succ(k) = (if k : A then cons(k, A Int k) else A Int k)";
by Auto_tac;
qed "Int_succ_right";
