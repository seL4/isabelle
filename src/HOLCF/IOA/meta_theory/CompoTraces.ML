(*  Title:      HOLCF/IOA/meta_theory/CompoTraces.ML
    ID:		$Id$
    Author:     Olaf M"uller
    Copyright   1996  TU Muenchen
 
Compositionality on Trace level.
*) 

simpset_ref () := simpset() setmksym (K None);

(* ---------------------------------------------------------------- *)
                   section "mksch rewrite rules";
(* ---------------------------------------------------------------- *)

bind_thm ("mksch_unfold", fix_prover2 thy mksch_def 
"mksch A B = (LAM tr schA schB. case tr of \
\       nil => nil\
\    | x##xs => \
\      (case x of  \ 
\        UU => UU  \
\      | Def y => \
\         (if y:act A then \
\             (if y:act B then \ 
\                   ((Takewhile (%a. a:int A)$schA) \
\                         @@(Takewhile (%a. a:int B)$schB) \
\                              @@(y>>(mksch A B$xs   \
\                                       $(TL$(Dropwhile (%a. a:int A)$schA))  \
\                                       $(TL$(Dropwhile (%a. a:int B)$schB))  \
\                    )))   \
\              else  \
\                 ((Takewhile (%a. a:int A)$schA)  \
\                      @@ (y>>(mksch A B$xs  \
\                              $(TL$(Dropwhile (%a. a:int A)$schA))  \
\                              $schB)))  \
\              )   \
\          else    \
\             (if y:act B then  \ 
\                 ((Takewhile (%a. a:int B)$schB)  \
\                       @@ (y>>(mksch A B$xs   \
\                              $schA   \
\                              $(TL$(Dropwhile (%a. a:int B)$schB))  \
\                              )))  \
\             else  \
\               UU  \
\             )  \
\         )  \
\       ))");


Goal "mksch A B$UU$schA$schB = UU";
by (stac mksch_unfold 1);
by (Simp_tac 1);
qed"mksch_UU";

Goal "mksch A B$nil$schA$schB = nil";
by (stac mksch_unfold 1);
by (Simp_tac 1);
qed"mksch_nil";

Goal "[|x:act A;x~:act B|]  \
\   ==> mksch A B$(x>>tr)$schA$schB = \
\         (Takewhile (%a. a:int A)$schA) \
\         @@ (x>>(mksch A B$tr$(TL$(Dropwhile (%a. a:int A)$schA)) \
\                             $schB))";
by (rtac trans 1);
by (stac mksch_unfold 1);
by (asm_full_simp_tac (simpset() addsimps [Consq_def,If_and_if]) 1);
by (simp_tac (simpset() addsimps [Consq_def]) 1);
qed"mksch_cons1";

Goal "[|x~:act A;x:act B|] \
\   ==> mksch A B$(x>>tr)$schA$schB = \
\        (Takewhile (%a. a:int B)$schB)  \
\         @@ (x>>(mksch A B$tr$schA$(TL$(Dropwhile (%a. a:int B)$schB))  \
\                            ))";
by (rtac trans 1);
by (stac mksch_unfold 1);
by (asm_full_simp_tac (simpset() addsimps [Consq_def,If_and_if]) 1);
by (simp_tac (simpset() addsimps [Consq_def]) 1);
qed"mksch_cons2";

Goal "[|x:act A;x:act B|] \
\   ==> mksch A B$(x>>tr)$schA$schB = \
\            (Takewhile (%a. a:int A)$schA) \
\         @@ ((Takewhile (%a. a:int B)$schB)  \
\         @@ (x>>(mksch A B$tr$(TL$(Dropwhile (%a. a:int A)$schA)) \
\                            $(TL$(Dropwhile (%a. a:int B)$schB))))  \
\             )";
by (rtac trans 1);
by (stac mksch_unfold 1);
by (asm_full_simp_tac (simpset() addsimps [Consq_def,If_and_if]) 1);
by (simp_tac (simpset() addsimps [Consq_def]) 1);
qed"mksch_cons3";

val compotr_simps =[mksch_UU,mksch_nil, mksch_cons1,mksch_cons2,mksch_cons3];

Addsimps compotr_simps;


(* ------------------------------------------------------------------ *)
(*                      The following lemmata aim for                 *)
(*               COMPOSITIONALITY   on    TRACE     Level             *)
(* ------------------------------------------------------------------ *)


(* ---------------------------------------------------------------------------- *)
                      section"Lemmata for ==>";                      
(* ---------------------------------------------------------------------------- *)

(* Consequence out of ext1_ext2_is_not_act1(2), which in turn are consequences out of 
   the compatibility of IOA, in particular out of the condition that internals are 
   really hidden. *)

Goal "(eB & ~eA --> ~A) -->       \
\         (A & (eA | eB)) = (eA & A)";
by (Fast_tac 1);
qed"compatibility_consequence1";


(* very similar to above, only the commutativity of | is used to make a slight change *)

Goal "(eB & ~eA --> ~A) -->       \
\         (A & (eB | eA)) = (eA & A)";
by (Fast_tac 1);
qed"compatibility_consequence2";


(* ---------------------------------------------------------------------------- *)
                      section"Lemmata for <==";                      
(* ---------------------------------------------------------------------------- *)


(* Lemma for substitution of looping assumption in another specific assumption *) 
val [p1,p2] = goal thy "[| f << (g x) ; x=(h x) |] ==> f << g (h x)";
by (cut_facts_tac [p1] 1);
by (etac (p2 RS subst) 1);
qed"subst_lemma1";

(* Lemma for substitution of looping assumption in another specific assumption *) 
val [p1,p2] = goal thy "[| (f x) = y >> g; x=(h x) |] ==> (f (h x)) = y >> g";
by (cut_facts_tac [p1] 1);
by (etac (p2 RS subst) 1);
qed"subst_lemma2";


Goal "!!A B. compatible A B ==> \
\   ! schA schB. Forall (%x. x:act (A||B)) tr \
\   --> Forall (%x. x:act (A||B)) (mksch A B$tr$schA$schB)";
by (Seq_induct_tac "tr" [Forall_def,sforall_def,mksch_def] 1); 
by (safe_tac set_cs);
by (asm_full_simp_tac (simpset() addsimps [actions_of_par]) 1);
by (case_tac "a:act A" 1);
by (case_tac "a:act B" 1);
(* a:A, a:B *)
by (Asm_full_simp_tac 1);
by (rtac (Forall_Conc_impl RS mp) 1);
by (asm_full_simp_tac (simpset() addsimps [ForallPTakewhileQ,intA_is_not_actB,int_is_act]) 1);
by (rtac (Forall_Conc_impl RS mp) 1);
by (asm_full_simp_tac (simpset() addsimps [ForallPTakewhileQ,intA_is_not_actB,int_is_act]) 1);
(* a:A,a~:B *)
by (Asm_full_simp_tac 1);
by (rtac (Forall_Conc_impl RS mp) 1);
by (asm_full_simp_tac (simpset() addsimps [ForallPTakewhileQ,intA_is_not_actB,int_is_act]) 1);
by (case_tac "a:act B" 1);
(* a~:A, a:B *)
by (Asm_full_simp_tac 1);
by (rtac (Forall_Conc_impl RS mp) 1);
by (asm_full_simp_tac (simpset() addsimps [ForallPTakewhileQ,intA_is_not_actB,int_is_act]) 1);
(* a~:A,a~:B *)
by Auto_tac;
qed_spec_mp"ForallAorB_mksch";

Goal "!!A B. compatible B A  ==> \
\   ! schA schB.  (Forall (%x. x:act B & x~:act A) tr \
\   --> Forall (%x. x:act B & x~:act A) (mksch A B$tr$schA$schB))";

by (Seq_induct_tac "tr" [Forall_def,sforall_def,mksch_def] 1);
by (safe_tac set_cs);
by (rtac (Forall_Conc_impl RS mp) 1);
by (asm_full_simp_tac (simpset() addsimps [ForallPTakewhileQ,
                            intA_is_not_actB,int_is_act]) 1);
qed_spec_mp "ForallBnAmksch";

Goal "!!A B. compatible A B ==> \
\   ! schA schB.  (Forall (%x. x:act A & x~:act B) tr \
\   --> Forall (%x. x:act A & x~:act B) (mksch A B$tr$schA$schB))";

by (Seq_induct_tac "tr" [Forall_def,sforall_def,mksch_def] 1);
by (safe_tac set_cs);
by (Asm_full_simp_tac 1);
by (rtac (Forall_Conc_impl RS mp) 1);
by (asm_full_simp_tac (simpset() addsimps [ForallPTakewhileQ,
                       intA_is_not_actB,int_is_act]) 1);
qed_spec_mp"ForallAnBmksch";

(* safe-tac makes too many case distinctions with this lemma in the next proof *)
Delsimps [FiniteConc];

Goal "[| Finite tr; is_asig(asig_of A); is_asig(asig_of B) |] ==> \
\   ! x y. Forall (%x. x:act A) x & Forall (%x. x:act B) y & \
\          Filter (%a. a:ext A)$x = Filter (%a. a:act A)$tr & \
\          Filter (%a. a:ext B)$y = Filter (%a. a:act B)$tr &\
\          Forall (%x. x:ext (A||B)) tr \
\          --> Finite (mksch A B$tr$x$y)";

by (etac Seq_Finite_ind  1);
by (Asm_full_simp_tac 1);
(* main case *)
by (Asm_full_simp_tac 1);
by (safe_tac set_cs);

(* a: act A; a: act B *)
by (forward_tac [sym RS antisym_less_inverse RS conjunct1 RS divide_Seq] 1);
by (forward_tac [sym RS antisym_less_inverse RS conjunct1 RS divide_Seq] 1);
back();
by (REPEAT (etac conjE 1));
(* Finite (tw iA x) and Finite (tw iB y) *)
by (asm_full_simp_tac (simpset() addsimps 
          [not_ext_is_int_or_not_act,FiniteConc]) 1);
(* now for conclusion IH applicable, but assumptions have to be transformed *)
by (dres_inst_tac [("x","x"),
                   ("g","Filter (%a. a:act A)$s")] subst_lemma2 1);
by (assume_tac 1);
by (dres_inst_tac [("x","y"),
                   ("g","Filter (%a. a:act B)$s")] subst_lemma2 1);
by (assume_tac 1);
(* IH *)
by (asm_full_simp_tac (simpset()
        addsimps [not_ext_is_int_or_not_act,ForallTL,ForallDropwhile]) 1);

(* a: act B; a~: act A *)
by (forward_tac [sym RS antisym_less_inverse RS conjunct1 RS divide_Seq] 1);

by (REPEAT (etac conjE 1));
(* Finite (tw iB y) *)
by (asm_full_simp_tac (simpset() addsimps 
          [not_ext_is_int_or_not_act,FiniteConc]) 1);
(* now for conclusion IH applicable, but assumptions have to be transformed *)
by (dres_inst_tac [("x","y"),
                   ("g","Filter (%a. a:act B)$s")] subst_lemma2 1);
by (assume_tac 1);
(* IH *)
by (asm_full_simp_tac (simpset()
       addsimps [not_ext_is_int_or_not_act,ForallTL,ForallDropwhile]) 1);

(* a~: act B; a: act A *)
by (forward_tac [sym RS antisym_less_inverse RS conjunct1 RS divide_Seq] 1);

by (REPEAT (etac conjE 1));
(* Finite (tw iA x) *)
by (asm_full_simp_tac (simpset() addsimps 
          [not_ext_is_int_or_not_act,FiniteConc]) 1);
(* now for conclusion IH applicable, but assumptions have to be transformed *)
by (dres_inst_tac [("x","x"),
                   ("g","Filter (%a. a:act A)$s")] subst_lemma2 1);
by (assume_tac 1);
(* IH *)
by (asm_full_simp_tac (simpset()
       addsimps [not_ext_is_int_or_not_act,ForallTL,ForallDropwhile]) 1);

(* a~: act B; a~: act A *)
by (fast_tac (claset() addSIs [ext_is_act] 
                      addss (simpset() addsimps [externals_of_par]) ) 1);
qed_spec_mp"FiniteL_mksch";

Addsimps [FiniteConc];


(* otherwise subst_lemma2 does not fit exactly, just to avoid a subst_lemma3 *)
Delsimps [FilterConc]; 

Goal " [| Finite bs; is_asig(asig_of A); is_asig(asig_of B);compatible A B|] ==>  \
\! y. Forall (%x. x:act B) y & Forall (%x. x:act B & x~:act A) bs &\
\    Filter (%a. a:ext B)$y = Filter (%a. a:act B)$(bs @@ z) \
\    --> (? y1 y2.  (mksch A B$(bs @@ z)$x$y) = (y1 @@ (mksch A B$z$x$y2)) & \
\                   Forall (%x. x:act B & x~:act A) y1 & \
\                   Finite y1 & y = (y1 @@ y2) & \
\                   Filter (%a. a:ext B)$y1 = bs)";
by (forw_inst_tac [("A1","A")] (compat_commute RS iffD1) 1);
by (etac Seq_Finite_ind  1);
by (REPEAT (rtac allI 1));
by (rtac impI 1);
by (res_inst_tac [("x","nil")] exI 1);
by (res_inst_tac [("x","y")] exI 1);
by (Asm_full_simp_tac 1);
(* main case *)
by (REPEAT (rtac allI 1));
by (rtac impI 1);
by (Asm_full_simp_tac 1);
by (REPEAT (etac conjE 1));
by (Asm_full_simp_tac 1);
(* divide_Seq on s *)
by (forward_tac [sym RS antisym_less_inverse RS conjunct1 RS divide_Seq] 1);
by (REPEAT (etac conjE 1));
(* transform assumption f eB y = f B (s@z) *)
by (dres_inst_tac [("x","y"),
                   ("g","Filter (%a. a:act B)$(s@@z)")] subst_lemma2 1);
by (assume_tac 1);
Addsimps [FilterConc]; 
by (asm_full_simp_tac (simpset() addsimps [not_ext_is_int_or_not_act]) 1);
(* apply IH *)
by (eres_inst_tac [("x","TL$(Dropwhile (%a. a:int B)$y)")] allE 1);
by (asm_full_simp_tac (simpset() addsimps [ForallTL,ForallDropwhile])1);
by (REPEAT (etac exE 1));
by (REPEAT (etac conjE 1));
by (Asm_full_simp_tac 1); 
(* for replacing IH in conclusion *)
by (rotate_tac ~2 1); 
by (Asm_full_simp_tac 1); 
(* instantiate y1a and y2a *)
by (res_inst_tac [("x","Takewhile (%a. a:int B)$y @@ a>>y1")] exI 1);
by (res_inst_tac [("x","y2")] exI 1);
(* elminate all obligations up to two depending on Conc_assoc *)
by (asm_full_simp_tac (simpset() addsimps [ForallPTakewhileQ, intA_is_not_actB,
             int_is_act,int_is_not_ext]) 1); 
by (simp_tac (simpset() addsimps [Conc_assoc]) 1); 
qed_spec_mp "reduceA_mksch1";

bind_thm("reduceA_mksch",conjI RSN (6,conjI RSN (5,reduceA_mksch1)));


(* otherwise subst_lemma2 does not fit exactly, just to avoid a subst_lemma3 *)
Delsimps [FilterConc]; 


Goal " [| Finite as; is_asig(asig_of A); is_asig(asig_of B);compatible A B|] ==>  \
\! x. Forall (%x. x:act A) x & Forall (%x. x:act A & x~:act B) as &\
\    Filter (%a. a:ext A)$x = Filter (%a. a:act A)$(as @@ z) \
\    --> (? x1 x2.  (mksch A B$(as @@ z)$x$y) = (x1 @@ (mksch A B$z$x2$y)) & \
\                   Forall (%x. x:act A & x~:act B) x1 & \
\                   Finite x1 & x = (x1 @@ x2) & \
\                   Filter (%a. a:ext A)$x1 = as)";
by (forw_inst_tac [("A1","A")] (compat_commute RS iffD1) 1);
by (etac Seq_Finite_ind  1);
by (REPEAT (rtac allI 1));
by (rtac impI 1);
by (res_inst_tac [("x","nil")] exI 1);
by (res_inst_tac [("x","x")] exI 1);
by (Asm_full_simp_tac 1);
(* main case *)
by (REPEAT (rtac allI 1));
by (rtac impI 1);
by (Asm_full_simp_tac 1);
by (REPEAT (etac conjE 1));
by (Asm_full_simp_tac 1);
(* divide_Seq on s *)
by (forward_tac [sym RS antisym_less_inverse RS conjunct1 RS divide_Seq] 1);
by (REPEAT (etac conjE 1));
(* transform assumption f eA x = f A (s@z) *)
by (dres_inst_tac [("x","x"),
                   ("g","Filter (%a. a:act A)$(s@@z)")] subst_lemma2 1);
by (assume_tac 1);
Addsimps [FilterConc]; 
by (asm_full_simp_tac (simpset() addsimps [not_ext_is_int_or_not_act]) 1);
(* apply IH *)
by (eres_inst_tac [("x","TL$(Dropwhile (%a. a:int A)$x)")] allE 1);
by (asm_full_simp_tac (simpset() addsimps [ForallTL,ForallDropwhile])1);
by (REPEAT (etac exE 1));
by (REPEAT (etac conjE 1));
by (Asm_full_simp_tac 1); 
(* for replacing IH in conclusion *)
by (rotate_tac ~2 1); 
by (Asm_full_simp_tac 1); 
(* instantiate y1a and y2a *)
by (res_inst_tac [("x","Takewhile (%a. a:int A)$x @@ a>>x1")] exI 1);
by (res_inst_tac [("x","x2")] exI 1);
(* elminate all obligations up to two depending on Conc_assoc *)
by (asm_full_simp_tac (simpset() addsimps [ForallPTakewhileQ, intA_is_not_actB,
             int_is_act,int_is_not_ext]) 1); 
by (simp_tac (simpset() addsimps [Conc_assoc]) 1); 
qed_spec_mp"reduceB_mksch1";

bind_thm("reduceB_mksch",conjI RSN (6,conjI RSN (5,reduceB_mksch1)));


(*


Goal "Finite y ==> ! z tr. Forall (%a.a:ext (A||B)) tr & \
\                             y = z @@ mksch A B$tr$a$b\
\                             --> Finite tr";
by (etac Seq_Finite_ind  1);
by Auto_tac;
by (Seq_case_simp_tac "tr" 1);
(* tr = UU *)
by (asm_full_simp_tac (simpset() addsimps [nil_is_Conc]) 1);
(* tr = nil *)
by Auto_tac;
(* tr = Conc *)
ren "s ss" 1;

by (case_tac "s:act A" 1);
by (case_tac "s:act B" 1);
by (rotate_tac ~2 1);
by (rotate_tac ~2 2);
by (asm_full_simp_tac (simpset() addsimps [nil_is_Conc,nil_is_Conc2]) 1);
by (asm_full_simp_tac (simpset() addsimps [nil_is_Conc,nil_is_Conc2]) 1);
by (case_tac "s:act B" 1);
by (rotate_tac ~2 1);
by (asm_full_simp_tac (simpset() addsimps [nil_is_Conc,nil_is_Conc2]) 1);
by (fast_tac (claset() addSIs [ext_is_act] 
                      addss (simpset() addsimps [externals_of_par]) ) 1);
(* main case *)
by (Seq_case_simp_tac "tr" 1);
(* tr = UU *)
by (asm_full_simp_tac (simpset() addsimps [Conc_Conc_eq]) 1);
by Auto_tac;
(* tr = nil ok *)
(* tr = Conc *)
by (Seq_case_simp_tac "z" 1);
(* z = UU ok *)
(* z = nil *)

(* z= Cons *)


by (case_tac "aaa:act A" 2);
by (case_tac "aaa:act B" 2);
by (rotate_tac ~2 2);
by (rotate_tac ~2 3);
by (asm_full_simp_tac (HOL_basic_ss addsimps [mksch_cons3]) 2);
by (eres_inst_tac [("x","sb@@Takewhile (%a. a: int A)$a @@ Takewhile (%a. a:int B)$b@@(aaa>>nil)")] allE 2);
by (eres_inst_tac [("x","sa")] allE 2);
by (asm_full_simp_tac (simpset() addsimps [Conc_assoc])2);



by (eres_inst_tac [("x","sa")] allE 1);
by (Asm_full_simp_tac 1);
by (case_tac "aaa:act A" 1);
by (case_tac "aaa:act B" 1);
by (rotate_tac ~2 1);
by (rotate_tac ~2 2);
by (asm_full_simp_tac (simpset() addsimps [Conc_Conc_eq]) 1);



Goal "(x>>xs = y @@ z) = ((y=nil & x>>xs=z) | (? ys. y=x>>ys & xs=ys@@z))";
by (Seq_case_simp_tac "y" 1);
by Auto_tac;
qed"Conc_Conc_eq";

Goal "!! (y::'a Seq).Finite y ==> ~ y= x@@UU";
by (etac Seq_Finite_ind 1);
by (Seq_case_simp_tac "x" 1);
by (Seq_case_simp_tac "x" 1);
by Auto_tac;
qed"FiniteConcUU1";

Goal "~ Finite ((x::'a Seq)@@UU)";
by (auto_tac (claset() addDs [FiniteConcUU1], simpset()));
qed"FiniteConcUU";

finiteR_mksch
  "Finite (mksch A B$tr$x$y) --> Finite tr"
*)


 
(*------------------------------------------------------------------------------------- *)
 section"Filtering external actions out of mksch(tr,schA,schB) yields the oracle tr";
(*                             structural induction
  ------------------------------------------------------------------------------------- *)

Goal 
"!! A B. [| compatible A B; compatible B A;\
\           is_asig(asig_of A); is_asig(asig_of B) |] ==> \
\ ! schA schB. Forall (%x. x:act A) schA & Forall (%x. x:act B) schB & \
\ Forall (%x. x:ext (A||B)) tr & \
\ Filter (%a. a:act A)$tr << Filter (%a. a:ext A)$schA &\
\ Filter (%a. a:act B)$tr << Filter (%a. a:ext B)$schB  \
\ --> Filter (%a. a:ext (A||B))$(mksch A B$tr$schA$schB) = tr";

by (Seq_induct_tac "tr" [Forall_def,sforall_def,mksch_def] 1);

(* main case *) 
(* splitting into 4 cases according to a:A, a:B *)
by (Asm_full_simp_tac 1);
by (safe_tac set_cs);

(* Case a:A, a:B *)
by (ftac divide_Seq 1);
by (ftac divide_Seq 1);
back();
by (REPEAT (etac conjE 1));
(* filtering internals of A in schA and of B in schB is nil *)
by (asm_full_simp_tac (simpset() addsimps 
          [not_ext_is_int_or_not_act,
           externals_of_par, intA_is_not_extB,int_is_not_ext]) 1);
(* conclusion of IH ok, but assumptions of IH have to be transformed *)
by (dres_inst_tac [("x","schA")] subst_lemma1 1);
by (assume_tac 1);
by (dres_inst_tac [("x","schB")] subst_lemma1 1);
by (assume_tac 1);
(* IH *)
by (asm_full_simp_tac (simpset() addsimps [not_ext_is_int_or_not_act,
                   ForallTL,ForallDropwhile]) 1);

(* Case a:A, a~:B *)
by (ftac divide_Seq 1);
by (REPEAT (etac conjE 1));
(* filtering internals of A is nil *)
by (asm_full_simp_tac (simpset() addsimps 
          [not_ext_is_int_or_not_act,
           externals_of_par, intA_is_not_extB,int_is_not_ext]) 1);
by (dres_inst_tac [("x","schA")] subst_lemma1 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [not_ext_is_int_or_not_act,
                    ForallTL,ForallDropwhile]) 1);

(* Case a:B, a~:A *)
by (ftac divide_Seq 1);
by (REPEAT (etac conjE 1));
(* filtering internals of A is nil *)
by (asm_full_simp_tac (simpset() addsimps 
          [not_ext_is_int_or_not_act,
           externals_of_par, intA_is_not_extB,int_is_not_ext]) 1);
by (dres_inst_tac [("x","schB")] subst_lemma1 1);
back();
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [not_ext_is_int_or_not_act,
                    ForallTL,ForallDropwhile]) 1);

(* Case a~:A, a~:B *)
by (fast_tac (claset() addSIs [ext_is_act] 
                      addss (simpset() addsimps [externals_of_par]) ) 1);
qed"FilterA_mksch_is_tr";



(*

***************************************************************8
With uncomplete take lemma rule should be reused afterwards !!!!!!!!!!!!!!!!!
**********************************************************************

(*---------------------------------------------------------------------------
              Filter of mksch(tr,schA,schB) to A is schA 
                             take lemma
  --------------------------------------------------------------------------- *)

Goal "!! A B. [| compatible A B; compatible B A; \
\ is_asig(asig_of A); is_asig(asig_of B) |] ==> \
\ Forall (%x. x:ext (A||B)) tr & \
\ Forall (%x. x:act A) schA & Forall (%x. x:act B) schB & \
\ Filter (%a. a:ext A)$schA = Filter (%a. a:act A)$tr &\
\ Filter (%a. a:ext B)$schB = Filter (%a. a:act B)$tr &\
\ LastActExtsch A schA & LastActExtsch B schB  \
\ --> Filter (%a. a:act A)$(mksch A B$tr$schA$schB) = schA";

by (res_inst_tac [("Q","%x. x:act B & x~:act A"),("x","tr")] take_lemma_less_induct 1);
by (REPEAT (etac conjE 1));

by (case_tac "Finite s" 1);

(* both sides of this equation are nil *)
by (subgoal_tac "schA=nil" 1);
by (Asm_simp_tac 1);
(* first side: mksch = nil *)
by (SELECT_GOAL (auto_tac (claset() addSIs [ForallQFilterPnil,ForallBnAmksch,FiniteL_mksch],
                           simpset())) 1);
(* second side: schA = nil *)
by (eres_inst_tac [("A","A")] LastActExtimplnil 1);
by (Asm_simp_tac 1);
by (SELECT_GOAL (auto_tac (claset() addSIs [ForallQFilterPnil],
                           simpset())) 1);

(* case ~ Finite s *)

(* both sides of this equation are UU *)
by (subgoal_tac "schA=UU" 1);
by (Asm_simp_tac 1);
(* first side: mksch = UU *)
by (SELECT_GOAL (auto_tac (claset() addSIs [ForallQFilterPUU,
                                           (finiteR_mksch RS mp COMP rev_contrapos),
                                            ForallBnAmksch],
                           simpset())) 1);
(* schA = UU *)
by (eres_inst_tac [("A","A")] LastActExtimplUU 1);
by (Asm_simp_tac 1);
by (SELECT_GOAL (auto_tac (claset() addSIs [ForallQFilterPUU],
                           simpset())) 1);

(* case" ~ Forall (%x.x:act B & x~:act A) s" *)

by (REPEAT (etac conjE 1));

(* bring in lemma reduceA_mksch *)
by (forw_inst_tac [("y","schB"),("x","schA")] reduceA_mksch 1);
by (REPEAT (atac 1));
by (REPEAT (etac exE 1));
by (REPEAT (etac conjE 1));

(* use reduceA_mksch to rewrite conclusion *)
by (hyp_subst_tac 1);
by (Asm_full_simp_tac  1);

(* eliminate the B-only prefix *)

by (subgoal_tac "(Filter (%a. a :act A)$y1) = nil" 1);
by (etac ForallQFilterPnil 2);
by (assume_tac 2);
by (Fast_tac 2);

(* Now real recursive step follows (in y) *)

by (Asm_full_simp_tac  1);
by (case_tac "y:act A" 1);
by (case_tac "y~:act B" 1);
by (rotate_tac ~2 1);
by (Asm_full_simp_tac 1);

by (subgoal_tac "Filter (%a. a:act A & a:ext B)$y1=nil" 1);
by (rotate_tac ~1 1);
by (Asm_full_simp_tac  1);
(* eliminate introduced subgoal 2 *)
by (etac ForallQFilterPnil 2);
by (assume_tac 2);
by (Fast_tac 2);
 
(* bring in divide Seq for s *)
by (forward_tac [sym RS antisym_less_inverse RS conjunct1 RS divide_Seq] 1);
by (REPEAT (etac conjE 1));

(* subst divide_Seq in conclusion, but only at the righest occurence *)
by (res_inst_tac [("t","schA")] ssubst 1);
back();
back();
back();
by (assume_tac 1);

(* reduce trace_takes from n to strictly smaller k *)
by (rtac take_reduction 1);

(* f A (tw iA) = tw ~eA *)
by (asm_full_simp_tac (simpset() addsimps [FilterPTakewhileQid,int_is_act,
                              not_ext_is_int_or_not_act]) 1);
by (rtac refl 1);

(* now conclusion fulfills induction hypothesis, but assumptions are not ready *)
(*

nacessary anymore ???????????????? 
by (rotate_tac ~10 1);

*)
(* assumption schB *)
by (asm_full_simp_tac (simpset() addsimps [ext_and_act]) 1);
(* assumption schA *)
by (dres_inst_tac [("x","schA"),
                   ("g","Filter (%a. a:act A)$s2")] subst_lemma2 1);
by (assume_tac 1);
by (Asm_full_simp_tac 1);
(* assumptions concerning LastActExtsch, cannot be rewritten, as LastActExtsmalli are looping  *)
by (dres_inst_tac [("sch","schA"),("P","%a. a:int A")] LastActExtsmall1 1);
by (dres_inst_tac [("sch1.0","y1")]  LastActExtsmall2 1);
by (assume_tac 1);

FIX: problem: schA and schB are not quantified in the new take lemma version !!!

by (Asm_full_simp_tac 1);

**********************************************************************************************
*)



(*--------------------------------------------------------------------------- *)

     section" Filter of mksch(tr,schA,schB) to A is schA -- take lemma proof";  
  
(*  --------------------------------------------------------------------------- *)



Goal "!! A B. [| compatible A B; compatible B A; \
\ is_asig(asig_of A); is_asig(asig_of B) |] ==> \
\ Forall (%x. x:ext (A||B)) tr & \
\ Forall (%x. x:act A) schA & Forall (%x. x:act B) schB & \
\ Filter (%a. a:ext A)$schA = Filter (%a. a:act A)$tr &\
\ Filter (%a. a:ext B)$schB = Filter (%a. a:act B)$tr &\
\ LastActExtsch A schA & LastActExtsch B schB  \
\ --> Filter (%a. a:act A)$(mksch A B$tr$schA$schB) = schA";

by (strip_tac 1);
by (resolve_tac seq.take_lemmas 1);
by (rtac mp 1);
by (assume_tac 2);
back();back();back();back();
by (res_inst_tac [("x","schA")] spec 1);
by (res_inst_tac [("x","schB")] spec 1);
by (res_inst_tac [("x","tr")] spec 1);
by (thin_tac' 5 1);
by (rtac nat_less_induct 1);
by (REPEAT (rtac allI 1));
ren "tr schB schA" 1;
by (strip_tac 1);
by (REPEAT (etac conjE 1));

by (case_tac "Forall (%x. x:act B & x~:act A) tr" 1);

by (rtac (seq_take_lemma RS iffD2 RS spec) 1);
by (thin_tac' 5 1);


by (case_tac "Finite tr" 1);

(* both sides of this equation are nil *)
by (subgoal_tac "schA=nil" 1);
by (Asm_simp_tac 1);
(* first side: mksch = nil *)
by (SELECT_GOAL (auto_tac (claset() addSIs [ForallQFilterPnil,ForallBnAmksch,FiniteL_mksch],
                           simpset())) 1);
(* second side: schA = nil *)
by (eres_inst_tac [("A","A")] LastActExtimplnil 1);
by (Asm_simp_tac 1);
by (eres_inst_tac [("Q","%x. x:act B & x~:act A")] ForallQFilterPnil 1);
by (assume_tac 1);
by (Fast_tac 1);

(* case ~ Finite s *)

(* both sides of this equation are UU *)
by (subgoal_tac "schA=UU" 1);
by (Asm_simp_tac 1);
(* first side: mksch = UU *)
by (SELECT_GOAL (auto_tac (claset() addSIs [ForallQFilterPUU,
        (finiteR_mksch RS mp COMP rev_contrapos),ForallBnAmksch],simpset())) 1);
(* schA = UU *)
by (eres_inst_tac [("A","A")] LastActExtimplUU 1);
by (Asm_simp_tac 1);
by (eres_inst_tac [("Q","%x. x:act B & x~:act A")] ForallQFilterPUU 1);
by (assume_tac 1);
by (Fast_tac 1);

(* case" ~ Forall (%x.x:act B & x~:act A) s" *)

by (dtac divide_Seq3 1);

by (REPEAT (etac exE 1));
by (REPEAT (etac conjE 1));
by (hyp_subst_tac 1);

(* bring in lemma reduceA_mksch *)
by (forw_inst_tac [("x","schA"),("y","schB"),("A","A"),("B","B")] reduceA_mksch 1);
by (REPEAT (atac 1));
by (REPEAT (etac exE 1));
by (REPEAT (etac conjE 1));

(* use reduceA_mksch to rewrite conclusion *)
by (hyp_subst_tac 1);
by (Asm_full_simp_tac  1);

(* eliminate the B-only prefix *)

by (subgoal_tac "(Filter (%a. a :act A)$y1) = nil" 1);
by (etac ForallQFilterPnil 2);
by (assume_tac 2);
by (Fast_tac 2);

(* Now real recursive step follows (in y) *)

by (Asm_full_simp_tac  1);
by (case_tac "x:act A" 1);
by (case_tac "x~:act B" 1);
by (rotate_tac ~2 1);
by (Asm_full_simp_tac 1);

by (subgoal_tac "Filter (%a. a:act A & a:ext B)$y1=nil" 1);
by (rotate_tac ~1 1);
by (Asm_full_simp_tac  1);
(* eliminate introduced subgoal 2 *)
by (etac ForallQFilterPnil 2);
by (assume_tac 2);
by (Fast_tac 2);
 
(* bring in divide Seq for s *)
by (forward_tac [sym RS antisym_less_inverse RS conjunct1 RS divide_Seq] 1);
by (REPEAT (etac conjE 1));

(* subst divide_Seq in conclusion, but only at the righest occurence *)
by (res_inst_tac [("t","schA")] ssubst 1);
back();
back();
back();
by (assume_tac 1);

(* reduce trace_takes from n to strictly smaller k *)
by (rtac take_reduction 1);

(* f A (tw iA) = tw ~eA *)
by (asm_full_simp_tac (simpset() addsimps [FilterPTakewhileQid,int_is_act,
                              not_ext_is_int_or_not_act]) 1);
by (rtac refl 1);
by (asm_full_simp_tac (simpset() addsimps [int_is_act,
                              not_ext_is_int_or_not_act]) 1);
by (rotate_tac ~11 1);

(* now conclusion fulfills induction hypothesis, but assumptions are not ready *)

(* assumption Forall tr *)
by (asm_full_simp_tac (simpset() addsimps [Forall_Conc]) 1);
(* assumption schB *)
by (asm_full_simp_tac (simpset() addsimps [Forall_Conc,ext_and_act]) 1);
by (REPEAT (etac conjE 1));
(* assumption schA *)
by (dres_inst_tac [("x","schA"),
                   ("g","Filter (%a. a:act A)$rs")] subst_lemma2 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [int_is_not_ext]) 1);
(* assumptions concerning LastActExtsch, cannot be rewritten, as LastActExtsmalli are looping  *)
by (dres_inst_tac [("sch","schA"),("P","%a. a:int A")] LastActExtsmall1 1);
by (forw_inst_tac [("sch1.0","y1")]  LastActExtsmall2 1);
by (assume_tac 1);

(* assumption Forall schA *)
by (dres_inst_tac [("s","schA"),
                   ("P","Forall (%x. x:act A)")] subst 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [ForallPTakewhileQ, int_is_act]) 1);

(* case x:actions(asig_of A) & x: actions(asig_of B) *)


by (rotate_tac ~2 1);
by (Asm_full_simp_tac  1);

by (subgoal_tac "Filter (%a. a:act A & a:ext B)$y1=nil" 1);
by (rotate_tac ~1 1);
by (Asm_full_simp_tac  1);
(* eliminate introduced subgoal 2 *)
by (etac ForallQFilterPnil 2);
by (assume_tac 2);
by (Fast_tac 2);

(* bring in divide Seq for s *)
by (forward_tac [sym RS antisym_less_inverse RS conjunct1 RS divide_Seq] 1);
by (REPEAT (etac conjE 1));

(* subst divide_Seq in conclusion, but only at the righest occurence *)
by (res_inst_tac [("t","schA")] ssubst 1);
back();
back();
back();
by (assume_tac 1);

(* f A (tw iA) = tw ~eA *)
by (asm_full_simp_tac (simpset() addsimps [FilterPTakewhileQid,int_is_act,
                              not_ext_is_int_or_not_act]) 1);

(* rewrite assumption forall and schB *)
by (rotate_tac 13 1);
by (asm_full_simp_tac (simpset() addsimps [ext_and_act]) 1);

(* divide_Seq for schB2 *)
by (forw_inst_tac [("y","y2")] (sym RS antisym_less_inverse RS conjunct1 RS divide_Seq) 1);
by (REPEAT (etac conjE 1));
(* assumption schA *)
by (dres_inst_tac [("x","schA"),
                   ("g","Filter (%a. a:act A)$rs")] subst_lemma2 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [int_is_not_ext]) 1);

(* f A (tw iB schB2) = nil *) 
by (asm_full_simp_tac (simpset() addsimps [int_is_not_ext,not_ext_is_int_or_not_act,
             intA_is_not_actB]) 1);


(* reduce trace_takes from n to strictly smaller k *)
by (rtac take_reduction 1);
by (rtac refl 1);
by (rtac refl 1);

(* now conclusion fulfills induction hypothesis, but assumptions are not all ready *)

(* assumption schB *)
by (dres_inst_tac [("x","y2"),
                   ("g","Filter (%a. a:act B)$rs")] subst_lemma2 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [intA_is_not_actB,int_is_not_ext]) 1);

(* conclusions concerning LastActExtsch, cannot be rewritten, as LastActExtsmalli are looping  *)
by (dres_inst_tac [("sch","schA"),("P","%a. a:int A")] LastActExtsmall1 1);
by (forw_inst_tac [("sch1.0","y1")]  LastActExtsmall2 1);
by (assume_tac 1);
by (dres_inst_tac [("sch","y2"),("P","%a. a:int B")] LastActExtsmall1 1);

(* assumption Forall schA, and Forall schA are performed by ForallTL,ForallDropwhile *)
by (asm_full_simp_tac (simpset() addsimps [ForallTL,ForallDropwhile]) 1);

(* case x~:A & x:B  *)
(* cannot occur, as just this case has been scheduled out before as the B-only prefix *)
by (case_tac "x:act B" 1);
by (Fast_tac 1);

(* case x~:A & x~:B  *)
(* cannot occur because of assumption: Forall (a:ext A | a:ext B) *)
by (rotate_tac ~9 1);
(* reduce forall assumption from tr to (x>>rs) *)
by (asm_full_simp_tac (simpset() addsimps [externals_of_par]) 1);
by (REPEAT (etac conjE 1));
by (fast_tac (claset() addSIs [ext_is_act]) 1);

qed"FilterAmksch_is_schA";



(*---------------------------------------------------------------------------  *)

   section" Filter of mksch(tr,schA,schB) to B is schB -- take lemma proof";
                
(*  --------------------------------------------------------------------------- *)



Goal "!! A B. [| compatible A B; compatible B A; \
\ is_asig(asig_of A); is_asig(asig_of B) |] ==> \
\ Forall (%x. x:ext (A||B)) tr & \
\ Forall (%x. x:act A) schA & Forall (%x. x:act B) schB & \
\ Filter (%a. a:ext A)$schA = Filter (%a. a:act A)$tr &\
\ Filter (%a. a:ext B)$schB = Filter (%a. a:act B)$tr &\
\ LastActExtsch A schA & LastActExtsch B schB  \
\ --> Filter (%a. a:act B)$(mksch A B$tr$schA$schB) = schB";

by (strip_tac 1);
by (resolve_tac seq.take_lemmas 1);
by (rtac mp 1);
by (assume_tac 2);
back();back();back();back();
by (res_inst_tac [("x","schA")] spec 1);
by (res_inst_tac [("x","schB")] spec 1);
by (res_inst_tac [("x","tr")] spec 1);
by (thin_tac' 5 1);
by (rtac nat_less_induct 1);
by (REPEAT (rtac allI 1));
ren "tr schB schA" 1;
by (strip_tac 1);
by (REPEAT (etac conjE 1));

by (case_tac "Forall (%x. x:act A & x~:act B) tr" 1);

by (rtac (seq_take_lemma RS iffD2 RS spec) 1);
by (thin_tac' 5 1);


by (case_tac "Finite tr" 1);

(* both sides of this equation are nil *)
by (subgoal_tac "schB=nil" 1);
by (Asm_simp_tac 1);
(* first side: mksch = nil *)
by (SELECT_GOAL (auto_tac (claset() addSIs [ForallQFilterPnil,ForallAnBmksch,FiniteL_mksch],
                           simpset())) 1);
(* second side: schA = nil *)
by (eres_inst_tac [("A","B")] LastActExtimplnil 1);
by (Asm_simp_tac 1);
by (eres_inst_tac [("Q","%x. x:act A & x~:act B")] ForallQFilterPnil 1);
by (assume_tac 1);
by (Fast_tac 1);

(* case ~ Finite tr *)

(* both sides of this equation are UU *)
by (subgoal_tac "schB=UU" 1);
by (Asm_simp_tac 1);
(* first side: mksch = UU *)
by (force_tac (claset() addSIs [ForallQFilterPUU,
                                (finiteR_mksch RS mp COMP rev_contrapos),
                                  ForallAnBmksch],
               simpset()) 1);
(* schA = UU *)
by (eres_inst_tac [("A","B")] LastActExtimplUU 1);
by (Asm_simp_tac 1);
by (eres_inst_tac [("Q","%x. x:act A & x~:act B")] ForallQFilterPUU 1);
by (assume_tac 1);
by (Fast_tac 1);

(* case" ~ Forall (%x.x:act B & x~:act A) s" *)

by (dtac divide_Seq3 1);

by (REPEAT (etac exE 1));
by (REPEAT (etac conjE 1));
by (hyp_subst_tac 1);

(* bring in lemma reduceB_mksch *)
by (forw_inst_tac [("y","schB"),("x","schA"),("A","A"),("B","B")] reduceB_mksch 1);
by (REPEAT (atac 1));
by (REPEAT (etac exE 1));
by (REPEAT (etac conjE 1));

(* use reduceB_mksch to rewrite conclusion *)
by (hyp_subst_tac 1);
by (Asm_full_simp_tac  1);

(* eliminate the A-only prefix *)

by (subgoal_tac "(Filter (%a. a :act B)$x1) = nil" 1);
by (etac ForallQFilterPnil 2);
by (assume_tac 2);
by (Fast_tac 2);

(* Now real recursive step follows (in x) *)

by (Asm_full_simp_tac  1);
by (case_tac "x:act B" 1);
by (case_tac "x~:act A" 1);
by (rotate_tac ~2 1);
by (Asm_full_simp_tac 1);

by (subgoal_tac "Filter (%a. a:act B & a:ext A)$x1=nil" 1);
by (rotate_tac ~1 1);
by (Asm_full_simp_tac  1);
(* eliminate introduced subgoal 2 *)
by (etac ForallQFilterPnil 2);
by (assume_tac 2);
by (Fast_tac 2);
 
(* bring in divide Seq for s *)
by (forward_tac [sym RS antisym_less_inverse RS conjunct1 RS divide_Seq] 1);
by (REPEAT (etac conjE 1));

(* subst divide_Seq in conclusion, but only at the righest occurence *)
by (res_inst_tac [("t","schB")] ssubst 1);
back();
back();
back();
by (assume_tac 1);

(* reduce trace_takes from n to strictly smaller k *)
by (rtac take_reduction 1);

(* f B (tw iB) = tw ~eB *)
by (asm_full_simp_tac (simpset() addsimps [FilterPTakewhileQid,int_is_act,
                              not_ext_is_int_or_not_act]) 1);
by (rtac refl 1);
by (asm_full_simp_tac (simpset() addsimps [int_is_act,
                              not_ext_is_int_or_not_act]) 1);
by (rotate_tac ~11 1);

(* now conclusion fulfills induction hypothesis, but assumptions are not ready *)

(* assumption Forall tr *)
by (asm_full_simp_tac (simpset() addsimps [Forall_Conc]) 1);
(* assumption schA *)
by (asm_full_simp_tac (simpset() addsimps [Forall_Conc,ext_and_act]) 1);
by (REPEAT (etac conjE 1));
(* assumption schB *)
by (dres_inst_tac [("x","schB"),
                   ("g","Filter (%a. a:act B)$rs")] subst_lemma2 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [int_is_not_ext]) 1);
(* assumptions concerning LastActExtsch, cannot be rewritten, as LastActExtsmalli are looping  *)
by (dres_inst_tac [("sch","schB"),("P","%a. a:int B")] LastActExtsmall1 1);
by (forw_inst_tac [("sch1.0","x1")]  LastActExtsmall2 1);
by (assume_tac 1);

(* assumption Forall schB *)
by (dres_inst_tac [("s","schB"),
                   ("P","Forall (%x. x:act B)")] subst 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [ForallPTakewhileQ, int_is_act]) 1);

(* case x:actions(asig_of A) & x: actions(asig_of B) *)


by (rotate_tac ~2 1);
by (Asm_full_simp_tac  1);

by (subgoal_tac "Filter (%a. a:act B & a:ext A)$x1=nil" 1);
by (rotate_tac ~1 1);
by (Asm_full_simp_tac  1);
(* eliminate introduced subgoal 2 *)
by (etac ForallQFilterPnil 2);
by (assume_tac 2);
by (Fast_tac 2);
 
(* bring in divide Seq for s *)
by (forward_tac [sym RS antisym_less_inverse RS conjunct1 RS divide_Seq] 1);
by (REPEAT (etac conjE 1));

(* subst divide_Seq in conclusion, but only at the righest occurence *)
by (res_inst_tac [("t","schB")] ssubst 1);
back();
back();
back();
by (assume_tac 1);

(* f B (tw iB) = tw ~eB *)
by (asm_full_simp_tac (simpset() addsimps [FilterPTakewhileQid,int_is_act,
                              not_ext_is_int_or_not_act]) 1);

(* rewrite assumption forall and schB *)
by (rotate_tac 13 1);
by (asm_full_simp_tac (simpset() addsimps [ext_and_act]) 1);

(* divide_Seq for schB2 *)
by (forw_inst_tac [("y","x2")] (sym RS antisym_less_inverse RS conjunct1 RS divide_Seq) 1);
by (REPEAT (etac conjE 1));
(* assumption schA *)
by (dres_inst_tac [("x","schB"),
                   ("g","Filter (%a. a:act B)$rs")] subst_lemma2 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [int_is_not_ext]) 1);

(* f B (tw iA schA2) = nil *) 
by (asm_full_simp_tac (simpset() addsimps [int_is_not_ext,not_ext_is_int_or_not_act,
             intA_is_not_actB]) 1);


(* reduce trace_takes from n to strictly smaller k *)
by (rtac take_reduction 1);
by (rtac refl 1);
by (rtac refl 1);

(* now conclusion fulfills induction hypothesis, but assumptions are not all ready *)

(* assumption schA *)
by (dres_inst_tac [("x","x2"),
                   ("g","Filter (%a. a:act A)$rs")] subst_lemma2 1);
by (assume_tac 1);
by (asm_full_simp_tac (simpset() addsimps [intA_is_not_actB,int_is_not_ext]) 1);

(* conclusions concerning LastActExtsch, cannot be rewritten, as LastActExtsmalli are looping  *)
by (dres_inst_tac [("sch","schB"),("P","%a. a:int B")] LastActExtsmall1 1);
by (forw_inst_tac [("sch1.0","x1")]  LastActExtsmall2 1);
by (assume_tac 1);
by (dres_inst_tac [("sch","x2"),("P","%a. a:int A")] LastActExtsmall1 1);

(* assumption Forall schA, and Forall schA are performed by ForallTL,ForallDropwhile *)
by (asm_full_simp_tac (simpset() addsimps [ForallTL,ForallDropwhile]) 1);

(* case x~:B & x:A  *)
(* cannot occur, as just this case has been scheduled out before as the B-only prefix *)
by (case_tac "x:act A" 1);
by (Fast_tac 1);

(* case x~:B & x~:A  *)
(* cannot occur because of assumption: Forall (a:ext A | a:ext B) *)
by (rotate_tac ~9 1);
(* reduce forall assumption from tr to (x>>rs) *)
by (asm_full_simp_tac (simpset() addsimps [externals_of_par]) 1);
by (REPEAT (etac conjE 1));
by (fast_tac (claset() addSIs [ext_is_act]) 1);

qed"FilterBmksch_is_schB";



(* ------------------------------------------------------------------ *)
         section"COMPOSITIONALITY on TRACE Level -- Main Theorem";
(* ------------------------------------------------------------------ *)
 
Goal 
"!! A B. [| is_trans_of A; is_trans_of B; compatible A B; compatible B A; \
\           is_asig(asig_of A); is_asig(asig_of B)|] \
\       ==>  (tr: traces(A||B)) = \
\            (Filter (%a. a:act A)$tr : traces A &\
\             Filter (%a. a:act B)$tr : traces B &\
\             Forall (%x. x:ext(A||B)) tr)";

by (simp_tac (simpset() addsimps [traces_def,has_trace_def]) 1);
by (safe_tac set_cs);
 
(* ==> *) 
(* There is a schedule of A *)
by (res_inst_tac [("x","Filter (%a. a:act A)$sch")] bexI 1);
by (asm_full_simp_tac (simpset() addsimps [compositionality_sch]) 2);
by (asm_full_simp_tac (simpset() addsimps [compatibility_consequence1,
                  externals_of_par,ext1_ext2_is_not_act1]) 1);
(* There is a schedule of B *)
by (res_inst_tac [("x","Filter (%a. a:act B)$sch")] bexI 1);
by (asm_full_simp_tac (simpset() addsimps [compositionality_sch]) 2);
by (asm_full_simp_tac (simpset() addsimps [compatibility_consequence2,
                  externals_of_par,ext1_ext2_is_not_act2]) 1);
(* Traces of A||B have only external actions from A or B *)  
by (rtac ForallPFilterP 1);

(* <== *)

(* replace schA and schB by Cut(schA) and Cut(schB) *)
by (dtac exists_LastActExtsch 1);
by (assume_tac 1);
by (dtac exists_LastActExtsch 1);
by (assume_tac 1);
by (REPEAT (etac exE 1));
by (REPEAT (etac conjE 1));
(* Schedules of A(B) have only actions of A(B) *)
by (dtac scheds_in_sig 1);
by (assume_tac 1);
by (dtac scheds_in_sig 1);
by (assume_tac 1);

ren "h1 h2 schA schB" 1;
(* mksch is exactly the construction of trA||B out of schA, schB, and the oracle tr,
   we need here *)
by (res_inst_tac [("x","mksch A B$tr$schA$schB")] bexI 1);

(* External actions of mksch are just the oracle *)
by (asm_full_simp_tac (simpset() addsimps [FilterA_mksch_is_tr RS spec RS spec RS mp]) 1);

(* mksch is a schedule -- use compositionality on sch-level *)
by (asm_full_simp_tac (simpset() addsimps [compositionality_sch]) 1);
by (asm_full_simp_tac (simpset() addsimps [FilterAmksch_is_schA,FilterBmksch_is_schB]) 1);
by (etac ForallAorB_mksch 1);
by (etac ForallPForallQ 1);
by (etac ext_is_act 1);
qed"compositionality_tr";



(* ------------------------------------------------------------------ *)
(*           COMPOSITIONALITY   on    TRACE         Level             *)
(*                            For Modules                             *)
(* ------------------------------------------------------------------ *)

Goalw [Traces_def,par_traces_def]

"!! A B. [| is_trans_of A; is_trans_of B; compatible A B; compatible B A; \
\           is_asig(asig_of A); is_asig(asig_of B)|] \
\==> Traces (A||B) = par_traces (Traces A) (Traces B)";

by (asm_full_simp_tac (simpset() addsimps [asig_of_par]) 1);
by (rtac set_ext 1);
by (asm_full_simp_tac (simpset() addsimps [compositionality_tr,externals_of_par]) 1);
qed"compositionality_tr_modules";


simpset_ref () := simpset() setmksym (Some o symmetric_fun);
