(*  Title:      HOL/MicroJava/JVM/Store.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen
*)

Goalw [newref_def]
 "hp x = None --> hp (newref hp) = None";
by (fast_tac (claset() addIs [someI2_ex] addss (simpset())) 1);
qed_spec_mp "newref_None";
