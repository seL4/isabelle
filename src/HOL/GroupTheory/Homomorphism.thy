(*  Title:      HOL/GroupTheory/Homomorphism
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Homomorphisms of groups, rings, and automorphisms.
Sigma version with Locales
*)

Homomorphism = Ring + Bij +

consts
  Hom :: "('a grouptype * 'b grouptype * ('a => 'b)) set"

defs
  Hom_def "Hom == \\<Sigma>G \\<in> Group. \\<Sigma>H \\<in> Group. {Phi. Phi \\<in> (G.<cr>) \\<rightarrow> (H.<cr>) & 
                  (\\<forall>x \\<in> (G.<cr>) . \\<forall>y \\<in> (G.<cr>) . (Phi((G.<f>) x y) = (H.<f>) (Phi x)(Phi y)))}"

consts
  RingHom :: "(('a ringtype) * ('b ringtype) * ('a => 'b))set"
defs
  RingHom_def "RingHom == \\<Sigma>R1 \\<in> Ring. \\<Sigma>R2 \\<in> Ring. {Phi. Phi \\<in> (R1.<cr>) \\<rightarrow> (R2.<cr>) &
                   (\\<forall>x \\<in> (R1.<cr>). \\<forall>y \\<in> (R1.<cr>). (Phi((R1.<f>) x y) = (R2.<f>) (Phi x) (Phi y))) &
                   (\\<forall>x \\<in> (R1.<cr>). \\<forall>y \\<in> (R1.<cr>). (Phi((R1.<m>) x y) = (R2.<m>) (Phi x) (Phi y)))}"

consts
  GroupAuto :: "('a grouptype * ('a => 'a)) set"

defs
  GroupAuto_def "GroupAuto == \\<Sigma>G \\<in> Group. {Phi. (G,G,Phi)\\<in>Hom  &
                    inj_on Phi (G.<cr>) & Phi ` (G.<cr>) = (G.<cr>)}"

consts
  RingAuto :: "(('a ringtype) * ('a => 'a))set"

defs
  RingAuto_def "RingAuto == \\<Sigma>R \\<in> Ring. {Phi. (R,R,Phi)\\<in>RingHom &
                    inj_on Phi (R.<cr>) & Phi ` (R.<cr>) = (R.<cr>)}"

end