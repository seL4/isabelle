(*  Title:      HOLCF/IOA/meta_theory/IOA.thy
    ID:         $Id$
    Author:     Olaf Müller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

The theory of I/O automata in HOLCF.
*)  


val prems = goal HOL.thy "(P ==> Q-->R) ==> P&Q --> R";
  by (fast_tac (claset() addDs prems) 1);
qed "imp_conj_lemma";
