(*  Title:      HOL/GroupTheory/Homomorphism
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Homomorphisms of groups, rings, and automorphisms.
Sigma version with Locales
*)

Open_locale "bij";

Addsimps [B_def, o'_def, inv'_def];

Goal "[|x \\<in> S; f \\<in> B|] ==> EX x'. x = f x'";
by (dtac BijE2 1); 
by Auto_tac; 


Goal "[| f \\<in> B; g \\<in> S \\<rightarrow> S \\<rightarrow> S; x \\<in> S; y \\<in> S;\
\      \\<forall>x \\<in> S. \\<forall>y \\<in> S. f(g x y) = g (f x) (f y) |] \
\     ==> inv' f (g x y) = g (inv' f x) (inv' f y)";
by (subgoal_tac "EX x':S. EX y':S. x = f x' & y = f y'" 1);
by (blast_tac (claset() addDs [BijE2]) 2);
by (Clarify_tac 1); 
(*the next step could be avoided if we could re-orient the quanitifed 
  assumption, to rewrite g (f x') (f y') ...*)
by (rtac inj_onD 1);
by (etac BijE3 1);
by (asm_full_simp_tac (simpset() addsimps [f_Inv_f, Inv_f_f, BijE2, BijE3, 
                                  funcset_mem RS funcset_mem]) 1); 
by (ALLGOALS
    (asm_full_simp_tac
     (simpset() addsimps [funcset_mem RS funcset_mem, BijE2, Inv_mem])));
qed "Bij_op_lemma";

Goal "[| a \\<in> B; b \\<in> B; g \\<in> S \\<rightarrow> S \\<rightarrow> S; x \\<in> S; y \\<in> S; \
\       \\<forall>x \\<in> S. \\<forall>y \\<in> S. a (b (g x y)) = g (a (b x)) (a (b y)) |]  \
\     ==> (a o' b) (g x y) = g ((a o' b) x) ((a o' b) y)";
by (afs [o'_def, compose_eq, B_def, 
         funcset_mem RS funcset_mem] 1);
qed "Bij_comp_lemma";


Goal "[| R1 \\<in> Ring; R2 \\<in> Ring |]  \
\  ==> RingHom `` {R1} `` {R2} = \
\      {Phi. Phi \\<in> (R1.<cr>) \\<rightarrow> (R2.<cr>) & \
\            (\\<forall>x \\<in> (R1.<cr>). \\<forall>y \\<in> (R1.<cr>). \
\               (Phi((R1.<f>) x y) = (R2.<f>) (Phi x) (Phi y))) &\
\            (\\<forall>x \\<in> (R1.<cr>). \\<forall>y \\<in> (R1.<cr>). \
\               (Phi((R1.<m>) x y) = (R2.<m>) (Phi x) (Phi y)))}";
by (afs [Image_def,RingHom_def] 1);
qed "RingHom_apply";

(* derive the defining properties as single lemmas *)
Goal "(R1,R2,Phi) \\<in> RingHom ==> Phi \\<in> (R1.<cr>) \\<rightarrow> (R2.<cr>)";
by (afs [RingHom_def] 1);
qed "RingHom_imp_funcset";

Goal "[| (R1,R2,Phi) \\<in> RingHom; x \\<in> (R1.<cr>); y \\<in> (R1.<cr>) |]  \
\     ==> Phi((R1.<f>) x y) = (R2.<f>) (Phi x) (Phi y)";
by (afs [RingHom_def] 1);
qed "RingHom_preserves_rplus";

Goal "[| (R1,R2,Phi) \\<in> RingHom; x \\<in> (R1.<cr>); y \\<in> (R1.<cr>) |]  \
\     ==> Phi((R1.<m>) x y) = (R2.<m>) (Phi x) (Phi y)";
by (afs [RingHom_def] 1);
qed "RingHom_preserves_rmult";

Goal "[| R1 \\<in> Ring; R2 \\<in> Ring; Phi \\<in> (R1.<cr>) \\<rightarrow> (R2.<cr>); \
\        \\<forall>x \\<in> (R1.<cr>). \\<forall>y \\<in> (R1.<cr>). \
\          Phi((R1.<f>) x y) = (R2.<f>) (Phi x) (Phi y);\
\        \\<forall>x \\<in> (R1.<cr>). \\<forall>y \\<in> (R1.<cr>). \
\          Phi((R1.<m>) x y) = (R2.<m>) (Phi x) (Phi y)|]\
\    ==> (R1,R2,Phi) \\<in> RingHom";
by (afs [RingHom_def] 1);
qed "RingHomI";

Open_locale "ring";

val Ring_R = thm "Ring_R";
val rmult_def = thm "rmult_def";

Addsimps [simp_R, Ring_R];



(* RingAutomorphisms *)
Goal "RingAuto `` {R} = \
\ {Phi. (R,R,Phi)  \\<in> RingHom & inj_on Phi (R.<cr>) & Phi ` (R.<cr>) = (R.<cr>)}";
by (rewtac RingAuto_def);
by (afs [Image_def] 1);
qed "RingAuto_apply";

Goal "(R,Phi) \\<in> RingAuto  ==> (R, R, Phi)  \\<in> RingHom";
by (afs [RingAuto_def] 1);
qed "RingAuto_imp_RingHom";

Goal "(R,Phi) \\<in> RingAuto ==> inj_on Phi (R.<cr>)";
by (afs [RingAuto_def] 1);
qed "RingAuto_imp_inj_on";

Goal "(R,Phi) \\<in> RingAuto ==> Phi ` (R.<cr>) = (R.<cr>)";
by (afs [RingAuto_def] 1);
qed "RingAuto_imp_preserves_R";

Goal "(R,Phi) \\<in> RingAuto ==> Phi \\<in> (R.<cr>) \\<rightarrow> (R.<cr>)";
by (etac (RingAuto_imp_RingHom RS RingHom_imp_funcset) 1); 
qed "RingAuto_imp_funcset";

Goal "[| (R,R,Phi) \\<in> RingHom; \
\        inj_on Phi (R.<cr>); \
\        Phi ` (R.<cr>) = (R.<cr>) |]\
\     ==> (R,Phi) \\<in> RingAuto";
by (afs [RingAuto_def] 1);
qed "RingAutoI";


(* major result: RingAutomorphism builds a group *)
(* We prove that they are a subgroup of the bijection group.
   Note!!! Here we need "RingAuto `` {R} ~= {}", (as a result from the
   resolution with subgroupI). That is, this is an example where one might say
   the discipline of Pi types pays off, because there we have the proof basically
   already there (compare the Pi-version).
   Here in the Sigma version, we have to redo now the proofs (or slightly
   adapted verisions) of promoteRingHom and promoteRingAuto *)

Goal "RingAuto `` {R} ~= {}";
by (stac RingAuto_apply 1);
by Auto_tac; 
by (res_inst_tac [("x","%y: (R.<cr>). y")] exI 1);
by (auto_tac (claset(), simpset() addsimps [inj_on_def])); 
by (asm_full_simp_tac (simpset() addsimps [RingHom_def, restrictI, 
     R_binop_def, symmetric (rmult_def), rplus_closed, rmult_closed]) 1);
qed "RingAutoEx";

Goal "(R,f) \\<in> RingAuto ==> f \\<in> Bij (R.<cr>)";
by (afs [RingAuto_imp_RingHom RS RingHom_imp_funcset, RingAuto_imp_inj_on, 
                RingAuto_imp_preserves_R, export BijI] 1);
qed "RingAuto_Bij";
Addsimps [RingAuto_Bij];

Goal "[| (R,a) \\<in> RingAuto; (R,b) \\<in> RingAuto; \
\        g \\<in> (R.<cr>) \\<rightarrow> (R.<cr>) \\<rightarrow> (R.<cr>); x \\<in> carrier R; y \\<in> carrier R; \
\        \\<forall>Phi. (R,Phi) \\<in> RingAuto --> \
\          (\\<forall>x \\<in> (R.<cr>). \\<forall>y \\<in> (R.<cr>). Phi(g x y) = g(Phi x) (Phi y)) |] \
\     ==> compose (R.<cr>) a b (g x y) = \
\           g (compose (R.<cr>) a b x) (compose (R.<cr>) a b y)";
by (asm_simp_tac (simpset() addsimps [export Bij_comp_lemma, 
                                    RingAuto_imp_funcset RS funcset_mem]) 1);
qed "Auto_comp_lemma";

Goal "[|(R, a) \\<in> RingAuto; x \\<in> carrier R; y \\<in> carrier R|]  \
\     ==> Inv (carrier R) a (x ## y) =  \
\         Inv (carrier R) a x ## Inv (carrier R) a y"; 
by (rtac (export Bij_op_lemma) 1);
by (etac RingAuto_Bij 1);
by (rtac rplus_funcset 1);
by (assume_tac 1);
by (assume_tac 1);
by (asm_simp_tac (simpset() addsimps [R_binop_def RS sym, 
                         RingAuto_imp_RingHom RS RingHom_preserves_rplus]) 1);
qed "Inv_rplus_lemma";

Goal "(R,a) \\<in> RingAuto \
\     ==> (R, grouptype.inverse (BijGroup (carrier R)) a) \\<in> RingAuto";
by (rtac RingAutoI 1);
by (afs [BijGroup_def, export (restrict_Inv_Bij RS BijE3)] 2);
by (afs [BijGroup_def, export (restrict_Inv_Bij RS BijE2)] 2);
by (rtac RingHomI 1);
by (rtac (Ring_R) 1);
by (rtac (Ring_R) 1);
(* ...  ==> (BijGroup (R .<R>) .<inv>) a \\<in> (R .<R>) \\<rightarrow> (R .<R>) *)
by (asm_simp_tac (simpset() addsimps [BijGroup_def, 
                     export restrict_Inv_Bij RS export BijE1]) 1); 
by (asm_simp_tac (simpset() addsimps [BijGroup_def, R_binop_def, rplus_closed, Inv_rplus_lemma]) 1); 
by (afs [BijGroup_def, symmetric (rmult_def), rmult_closed] 1);
by (afs [export Bij_op_lemma, rmult_funcset, rmult_def, 
         RingAuto_imp_RingHom RS RingHom_preserves_rmult] 1);
qed "inverse_BijGroup_lemma";

Goal "[|(R, a) \\<in> RingAuto; (R, b) \\<in> RingAuto|]  \
\     ==> (R, bin_op (BijGroup (carrier R)) a b) \\<in> RingAuto";
by (afs [BijGroup_def] 1);
by (rtac RingAutoI 1);
by (rtac RingHomI 1);
by (rtac (Ring_R) 1);
by (rtac (Ring_R) 1);
by (afs [RingAuto_Bij,export compose_Bij,export BijE1] 1);
by (Clarify_tac 1); 
by (rtac Auto_comp_lemma 1);
by (ALLGOALS Asm_full_simp_tac);
by (asm_full_simp_tac (simpset() addsimps [R_binop_def, rplus_funcset]) 1); 
by (blast_tac (claset() addIs [RingAuto_imp_RingHom RS RingHom_preserves_rplus]) 1); 
by (Clarify_tac 1); 
by (rtac Auto_comp_lemma 1);
by (assume_tac 1); 
by (assume_tac 1); 
by (asm_full_simp_tac (simpset() addsimps [rmult_funcset]) 1); 
by (assume_tac 1); 
by (assume_tac 1); 
by (blast_tac (claset() addIs [RingAuto_imp_RingHom RS RingHom_preserves_rmult]) 1); 
(*       ==> inj_on (compose (R .<R>) a b) (R .<R>) *)
by (blast_tac (claset() delrules [equalityI]
			addIs [inj_on_compose, RingAuto_imp_inj_on, 
                          RingAuto_imp_funcset, RingAuto_imp_preserves_R]) 1); 
(*      ==> compose (R .<R>) a b ` (R .<R>) = (R .<R>) *)
by (blast_tac (claset() delrules [equalityI] 
      addIs [surj_compose, RingAuto_imp_funcset, RingAuto_imp_preserves_R]) 1);
qed "binop_BijGroup_lemma";


(* Ring automorphisms are a subgroup of the group of bijections over the 
   ring's carrier, and thus a group *)
Goal "RingAuto `` {R} <<= BijGroup (R.<cr>)";
by (rtac SubgroupI 1);
by (rtac (export Bij_are_Group) 1);
(* 1. RingAuto `` {R} <= (BijGroup (R .<R>) .<cr>) *)
by (afs [subset_def, BijGroup_def, Bij_def, 
         RingAuto_imp_RingHom RS RingHom_imp_funcset, RingAuto_imp_inj_on, 
         RingAuto_imp_preserves_R, Image_def] 1);
(* 1. !!R. R \\<in> Ring ==> RingAuto `` {R} ~= {} *)
by (rtac RingAutoEx 1);
by (auto_tac (claset(),
         simpset() addsimps [inverse_BijGroup_lemma, binop_BijGroup_lemma])); 
qed "RingAuto_SG_BijGroup";

Delsimps [simp_R, Ring_R];

Close_locale "ring";
Close_locale "group";

val RingAuto_are_Group = (export RingAuto_SG_BijGroup) RS (export Bij_are_Group RS SubgroupE2);
(* So far:
"[| ?R2 \\<in> Ring; group_of ?R2 \\<in> Group |]
   ==> (| carrier = RingAuto `` {?R2},
          bin_op =
            %x:RingAuto `` {?R2}.
               restrict ((BijGroup (?R2 .<cr>) .<f>) x) (RingAuto `` {?R2}),
          inverse = restrict (BijGroup (?R2 .<cr>) .<inv>) (RingAuto `` {?R2}),
          unit = BijGroup (?R2 .<cr>) .<e> |) \\<in> Group" *)

(* Unfortunately we have to eliminate the extra assumptions 
Now only group_of R \\<in> Group *)

Goal "R \\<in> Ring ==> group_of R \\<in> Group";
by (asm_full_simp_tac (simpset() addsimps [group_of_def]) 1); 
by (rtac Abel_imp_Group 1);
by (etac (export R_Abel) 1);
qed "R_Group";

Goal "R \\<in> Ring ==> (| carrier = RingAuto `` {R},\
\          bin_op =  %x:RingAuto `` {R}. %y: RingAuto `` {R}.\
\                             (BijGroup (R.<cr>) .<f>) x y ,\
\          inverse = %x: RingAuto `` {R}. (BijGroup (R.<cr>) .<inv>) x,\
\          unit = BijGroup (R.<cr>) .<e> |) \\<in> Group";
by (rtac (R_Group RSN (2, RingAuto_are_Group)) 1);
by (assume_tac 1);
by (assume_tac 1);
qed "RingAuto_are_Groupf";

(* "?R \\<in> Ring
   ==> (| carrier = RingAuto `` {?R},
          bin_op =
            %x:RingAuto `` {?R}.
               restrict ((BijGroup (?R .<cr>) .<f>) x) (RingAuto `` {?R}),
          inverse = restrict (BijGroup (?R .<cr>) .<inv>) (RingAuto `` {?R}),
          unit = BijGroup (?R .<cr>) .<e> |) \\<in> Group" *)
