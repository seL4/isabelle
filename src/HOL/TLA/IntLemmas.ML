(* 
    File:	 IntLemmas.ML
    Author:      Stephan Merz
    Copyright:   1998 University of Munich

Lemmas and tactics for "intensional" logics. 

Mostly a lifting of standard HOL lemmas. They are not required in standard
reasoning about intensional logics, which starts by unlifting proof goals
to the HOL level.
*)


qed_goal "substW" Intensional.thy
  "[| |- x = y; w |= P(x) |] ==> w |= P(y)"
  (fn [prem1,prem2] => [rtac (rewrite_rule ([prem1] RL [inteq_reflection]) prem2) 1]);
                        

(* Lift HOL rules to intensional reasoning *)

qed_goal "reflW" Intensional.thy "|- x = x"
  (fn _ => [Simp_tac 1]);

qed_goal "symW" Intensional.thy "|- s = t  ==>  |- t = s"
  (fn prems => [ cut_facts_tac prems 1,
                 rtac intI 1, dtac intD 1,
                 rewrite_goals_tac intensional_rews,
                 etac sym 1 ]);

qed_goal "not_symW" Intensional.thy "|- s ~= t  ==>  |- t ~= s"
  (fn prems => [ cut_facts_tac prems 1,
                 rtac intI 1, dtac intD 1,
                 rewrite_goals_tac intensional_rews,
                 etac not_sym 1 ]);

qed_goal "transW" Intensional.thy 
  "[| |- r = s; |- s = t |] ==> |- r = t"
  (fn prems => [ cut_facts_tac prems 1,
                 rtac intI 1, REPEAT (dtac intD 1),
                 rewrite_goals_tac intensional_rews,
                 etac trans 1,
                 atac 1 ]);

qed_goal "box_equalsW" Intensional.thy 
   "[| |- a = b; |- a = c; |- b = d |] ==> |- c = d"
   (fn prems => [ (rtac transW 1),
                  (rtac transW 1),
                  (rtac symW 1),
                  (REPEAT (resolve_tac prems 1)) ]);


(* NB: Antecedent is a standard HOL (non-intensional) formula. *)
qed_goal "fun_congW" Intensional.thy 
   "f = g ==> |- f<x> = g<x>"
   (fn prems => [ cut_facts_tac prems 1,
                  rtac intI 1,
                  rewrite_goals_tac intensional_rews,
                  etac fun_cong 1 ]);

qed_goal "fun_cong2W" Intensional.thy 
   "f = g ==> |- f<x,y> = g<x,y>"
   (fn prems => [ cut_facts_tac prems 1,
                  rtac intI 1,
                  Asm_full_simp_tac 1 ]);

qed_goal "fun_cong3W" Intensional.thy 
   "f = g ==> |- f<x,y,z> = g<x,y,z>"
   (fn prems => [ cut_facts_tac prems 1,
                  rtac intI 1,
                  Asm_full_simp_tac 1 ]);


qed_goal "arg_congW" Intensional.thy "|- x = y ==> |- f<x> = f<y>"
   (fn prems => [ cut_facts_tac prems 1,
                  rtac intI 1,
                  dtac intD 1,
                  rewrite_goals_tac intensional_rews,
                  etac arg_cong 1 ]);

qed_goal "arg_cong2W" Intensional.thy 
   "[| |- u = v; |- x = y |] ==> |- f<u,x> = f<v,y>"
   (fn prems => [ cut_facts_tac prems 1,
                  rtac intI 1,
                  REPEAT (dtac intD 1),
                  rewrite_goals_tac intensional_rews,
                  REPEAT (etac subst 1),
                  rtac refl 1 ]);

qed_goal "arg_cong3W" Intensional.thy 
   "[| |- r = s; |- u = v; |- x = y |] ==> |- f<r,u,x> = f<s,v,y>"
   (fn prems => [ cut_facts_tac prems 1,
                  rtac intI 1,
                  REPEAT (dtac intD 1),
                  rewrite_goals_tac intensional_rews,
                  REPEAT (etac subst 1),
                  rtac refl 1 ]);

qed_goal "congW" Intensional.thy 
   "[| f = g; |- x = y |] ==> |- f<x> = g<y>"
   (fn prems => [ rtac box_equalsW 1,
                  rtac reflW 3,
                  rtac arg_congW 1,
                  resolve_tac prems 1,
                  rtac fun_congW 1,
                  rtac sym 1,
                  resolve_tac prems 1 ]);

qed_goal "cong2W" Intensional.thy 
   "[| f = g; |- u = v; |- x = y |] ==> |- f<u,x> = g<v,y>"
   (fn prems => [ rtac box_equalsW 1,
                  rtac reflW 3,
                  rtac arg_cong2W 1,
                  REPEAT (resolve_tac prems 1),
                  rtac fun_cong2W 1,
                  rtac sym 1,
                  resolve_tac prems 1 ]);

qed_goal "cong3W" Intensional.thy 
   "[| f = g; |- r = s; |- u = v; |- x = y |] ==> |- f<r,u,x> = g<s,v,y>"
   (fn prems => [ rtac box_equalsW 1,
                  rtac reflW 3,
                  rtac arg_cong3W 1,
                  REPEAT (resolve_tac prems 1),
                  rtac fun_cong3W 1,
                  rtac sym 1,
                  resolve_tac prems 1 ]);


(** Lifted equivalence **)

(* Note the object-level implication in the hypothesis. Meta-level implication
   would be incorrect! *)
qed_goal "iffIW" Intensional.thy 
  "[| |- A --> B; |- B --> A |] ==> |- A = B"
  (fn prems => [ cut_facts_tac prems 1,
                 rewrite_goals_tac (Valid_def::intensional_rews),
                 Blast_tac 1 ]);

qed_goal "iffD2W" Intensional.thy 
  "[| |- P = Q; w |= Q |] ==> w |= P"
 (fn prems => [ cut_facts_tac prems 1,
	        rewrite_goals_tac (Valid_def::intensional_rews),
                Blast_tac 1 ]);

val iffD1W = symW RS iffD2W;

(** #True **)

qed_goal "eqTrueIW" Intensional.thy "|- P ==> |- P = #True"
  (fn prems => [cut_facts_tac prems 1,
                rtac intI 1,
                dtac intD 1,
		Asm_full_simp_tac 1]);

qed_goal "eqTrueEW" Intensional.thy "|- P = #True ==> |- P"
  (fn prems => [cut_facts_tac prems 1,
                rtac intI 1,
                dtac intD 1,
		Asm_full_simp_tac 1]);

(** #False **)

qed_goal "FalseEW" Intensional.thy "|- #False ==> |- P"
  (fn prems => [cut_facts_tac prems 1,
                rtac intI 1,
                dtac intD 1,
                rewrite_goals_tac intensional_rews,
                etac FalseE 1]);

qed_goal "False_neq_TrueW" Intensional.thy 
 "|- #False = #True ==> |- P"
 (fn [prem] => [rtac (prem RS eqTrueEW RS FalseEW) 1]);


(** Negation **)

(* Again use object-level implication *)
qed_goal "notIW" Intensional.thy "|- P --> #False ==> |- ~P"
  (fn prems => [cut_facts_tac prems 1,
		rewrite_goals_tac (Valid_def::intensional_rews),
		Blast_tac 1]);

qed_goal "notEWV" Intensional.thy 
  "[| |- ~P; |- P |] ==> |- R"
  (fn prems => [cut_facts_tac prems 1,
		rtac intI 1,
                REPEAT (dtac intD 1),
                rewrite_goals_tac intensional_rews,
                etac notE 1, atac 1]);

(* The following rule is stronger: It is enough to detect an 
   inconsistency at *some* world to conclude R. Note also that P and R
   are allowed to be (intensional) formulas of different types! *)

qed_goal "notEW" Intensional.thy 
   "[| w |= ~P; w |= P |] ==> |- R"
  (fn prems => [cut_facts_tac prems 1,
                rtac intI 1,
                rewrite_goals_tac intensional_rews,
                etac notE 1, atac 1]);

(** Implication **)

qed_goal "impIW" Intensional.thy "(!!w. (w |= A) ==> (w |= B)) ==> |- A --> B"
  (fn [prem] => [ rtac intI 1,
                 rewrite_goals_tac intensional_rews,
                 rtac impI 1,
                 etac prem 1 ]);


qed_goal "mpW" Intensional.thy "[| |- A --> B; w |= A |] ==> w |= B"
   (fn prems => [ cut_facts_tac prems 1,
                  dtac intD 1,
                  rewrite_goals_tac intensional_rews,
                  etac mp 1,
                  atac 1 ]);

qed_goal "impEW" Intensional.thy 
  "[| |- A --> B; w |= A; w |= B ==> w |= C |] ==> w |= C"
  (fn prems => [ (REPEAT (resolve_tac (prems@[mpW]) 1)) ]);

qed_goal "rev_mpW" Intensional.thy "[| w |= P; |- P --> Q |] ==> w |= Q"
  (fn prems => [ (REPEAT (resolve_tac (prems@[mpW]) 1)) ]);

qed_goalw "contraposW" Intensional.thy intensional_rews
  "[| w |= ~Q; |- P --> Q |] ==> w |= ~P"
  (fn [major,minor] => [rtac (major RS contrapos) 1,
                        etac rev_mpW 1,
                        rtac minor 1]);

qed_goal "iffEW" Intensional.thy
    "[| |- P = Q; [| |- P --> Q; |- Q --> P |] ==> R |] ==> R"
 (fn [p1,p2] => [REPEAT(ares_tac([p1 RS iffD2W, p1 RS iffD1W, p2, impIW])1)]);


(** Conjunction **)

qed_goalw "conjIW" Intensional.thy intensional_rews "[| w |= P; w |= Q |] ==> w |= P & Q"
  (fn prems => [REPEAT (resolve_tac ([conjI]@prems) 1)]);

qed_goal "conjunct1W" Intensional.thy "(w |= P & Q) ==> w |= P"
  (fn prems => [cut_facts_tac prems 1,
                rewrite_goals_tac intensional_rews,
                etac conjunct1 1]);

qed_goal "conjunct2W" Intensional.thy "(w |= P & Q) ==> w |= Q"
  (fn prems => [cut_facts_tac prems 1,
                rewrite_goals_tac intensional_rews,
                etac conjunct2 1]);

qed_goal "conjEW" Intensional.thy 
  "[| w |= P & Q; [| w |= P; w |= Q |] ==> w |= R |] ==> w |= R"
  (fn prems => [cut_facts_tac prems 1, resolve_tac prems 1,
	        etac conjunct1W 1, etac conjunct2W 1]);


(** Disjunction **)

qed_goalw "disjI1W" Intensional.thy intensional_rews "w |= P ==> w |= P | Q"
  (fn [prem] => [REPEAT (resolve_tac [disjI1,prem] 1)]);

qed_goalw "disjI2W" Intensional.thy intensional_rews "w |= Q ==> w |= P | Q"
  (fn [prem] => [REPEAT (resolve_tac [disjI2,prem] 1)]);

qed_goal "disjEW" Intensional.thy 
         "[| w |= P | Q; |- P --> R; |- Q --> R |] ==> w |= R"
  (fn prems => [cut_facts_tac prems 1,
                REPEAT (dtac intD 1),
                rewrite_goals_tac intensional_rews,
		Blast_tac 1]);

(** Classical propositional logic **)

qed_goalw "classicalW" Intensional.thy (Valid_def::intensional_rews)
  "!!P. |- ~P --> P  ==>  |- P"
  (fn prems => [Blast_tac 1]);

qed_goal "notnotDW" Intensional.thy "!!P. |- ~~P  ==>  |- P"
  (fn prems => [rtac intI 1,
                dtac intD 1,
                rewrite_goals_tac intensional_rews,
                etac notnotD 1]);

qed_goal "disjCIW" Intensional.thy "!!P Q. (w |= ~Q --> P) ==> (w |= P|Q)"
  (fn prems => [rewrite_goals_tac intensional_rews,
                Blast_tac 1]);

qed_goal "impCEW" Intensional.thy 
   "[| |- P --> Q; (w |= ~P) ==> (w |= R); (w |= Q) ==> (w |= R) |] ==> w |= R"
  (fn [a1,a2,a3] => 
    [rtac (excluded_middle RS disjE) 1,
     etac (rewrite_rule intensional_rews a2) 1,
     rtac a3 1,
     etac (a1 RS mpW) 1]);

qed_goalw "iffCEW" Intensional.thy intensional_rews
   "[| |- P = Q;      \
\      [| (w |= P); (w |= Q) |] ==> (w |= R);   \
\      [| (w |= ~P); (w |= ~Q) |] ==> (w |= R)  \
\   |] ==> w |= R"
   (fn [a1,a2,a3] =>
      [rtac iffCE 1,
       etac a2 2, atac 2,
       etac a3 2, atac 2,
       rtac (int_unlift a1) 1]);

qed_goal "case_split_thmW" Intensional.thy 
   "!!P. [| |- P --> Q; |- ~P --> Q |] ==> |- Q"
  (fn _ => [rewrite_goals_tac (Valid_def::intensional_rews),
	    Blast_tac 1]);

fun case_tacW a = res_inst_tac [("P",a)] case_split_thmW;


(** Rigid quantifiers **)

qed_goal "allIW" Intensional.thy "(!!x. |- P x) ==> |- ! x. P(x)"
  (fn [prem] => [rtac intI 1,
                 rewrite_goals_tac intensional_rews,
                 rtac allI 1,
                 rtac (prem RS intD) 1]);

qed_goal "specW" Intensional.thy "|- ! x. P x ==> |- P x"
  (fn prems => [cut_facts_tac prems 1,
                rtac intI 1,
                dtac intD 1,
                rewrite_goals_tac intensional_rews,
                etac spec 1]);


qed_goal "allEW" Intensional.thy 
         "[| |- ! x. P x;  |- P x ==> |- R |] ==> |- R"
 (fn major::prems=>
  [ (REPEAT (resolve_tac (prems @ [major RS specW]) 1)) ]);

qed_goal "all_dupEW" Intensional.thy 
    "[| |- ! x. P x;  [| |- P x; |- ! x. P x |] ==> |- R |] ==> |- R"
 (fn prems =>
  [ (REPEAT (resolve_tac (prems @ (prems RL [specW])) 1)) ]);


qed_goal "exIW" Intensional.thy "|- P x ==> |- ? x. P x"
  (fn [prem] => [rtac intI 1,
                 rewrite_goals_tac intensional_rews,
                 rtac exI 1,
                 rtac (prem RS intD) 1]);

qed_goal "exEW" Intensional.thy 
  "[| w |= ? x. P x; !!x. |- P x --> Q |] ==> w |= Q"
  (fn [major,minor] => [rtac exE 1,
                        rtac (rewrite_rule intensional_rews major) 1,
                        etac rev_mpW 1,
                        rtac minor 1]);

(** Classical quantifier reasoning **)

qed_goal "exCIW" Intensional.thy 
  "!!P. w |= (! x. ~P x) --> P a ==> w |= ? x. P x"
  (fn prems => [rewrite_goals_tac intensional_rews,
                Blast_tac 1]);

