(*  Title:      HOLCF/IMP/HoareEx.thy
    ID:         $Id$
    Author:     Tobias Nipkow, TUM
    Copyright   1997 TUM

An example from the HOLCF paper by Mueller, Nipkow, Oheimb, Slotosch.
It demonstrates fixpoint reasoning by showing the correctness of the Hoare
rule for while-loops.
*)

HoareEx = Denotational +

types assn = state => bool

constdefs hoare_valid :: [assn,com,assn] => bool ("|= {(1_)}/ (_)/ {(1_)}" 50)
 "|= {A} c {B} == !s t. A s & D c `(Discr s) = Def t --> B t"

end
