(*  Title:      HOLCF/IOA/meta_theory/CompoTraces.ML
    ID:        
    Author:     Olaf M"uller
    Copyright   1996  TU Muenchen

Compositionality on Trace level.
*) 

(* FIX:Proof and add in Sequence.ML *)
Addsimps [Finite_Conc];


(*
Addsimps [forall_cons];

Addsimps [(* LastActExtsmall1, LastActExtsmall2, looping !! *) ext_and_act];
*)

fun thin_tac' j =
  rotate_tac (j - 1) THEN'
  etac thin_rl THEN'
  rotate_tac (~ (j - 1));



(* ---------------------------------------------------------------- *)
                   section "mksch rewrite rules";
(* ---------------------------------------------------------------- *)




bind_thm ("mksch_unfold", fix_prover2 thy mksch_def 
"mksch A B = (LAM tr schA schB. case tr of \
\       nil => nil\
\    | x##xs => \
\      (case x of  \ 
\        Undef => UU  \
\      | Def y => \
\         (if y:act A then \
\             (if y:act B then \ 
\                   ((Takewhile (%a.a:int A)`schA) \
\                         @@(Takewhile (%a.a:int B)`schB) \
\                              @@(y>>(mksch A B`xs   \
\                                       `(TL`(Dropwhile (%a.a:int A)`schA))  \
\                                       `(TL`(Dropwhile (%a.a:int B)`schB))  \
\                    )))   \
\              else  \
\                 ((Takewhile (%a.a:int A)`schA)  \
\                      @@ (y>>(mksch A B`xs  \
\                              `(TL`(Dropwhile (%a.a:int A)`schA))  \
\                              `schB)))  \
\              )   \
\          else    \
\             (if y:act B then  \ 
\                 ((Takewhile (%a.a:int B)`schB)  \
\                       @@ (y>>(mksch A B`xs   \
\                              `schA   \
\                              `(TL`(Dropwhile (%a.a:int B)`schB))  \
\                              )))  \
\             else  \
\               UU  \
\             )  \
\         )  \
\       ))");


goal thy "mksch A B`UU`schA`schB = UU";
by (stac mksch_unfold 1);
by (Simp_tac 1);
qed"mksch_UU";

goal thy "mksch A B`nil`schA`schB = nil";
by (stac mksch_unfold 1);
by (Simp_tac 1);
qed"mksch_nil";

goal thy "!!x.[|x:act A;x~:act B|]  \
\   ==> mksch A B`(x>>tr)`schA`schB = \
\         (Takewhile (%a.a:int A)`schA) \
\         @@ (x>>(mksch A B`tr`(TL`(Dropwhile (%a.a:int A)`schA)) \
\                             `schB))";
br trans 1;
by (stac mksch_unfold 1);
by (asm_full_simp_tac (!simpset addsimps [Cons_def,If_and_if]) 1);
by (simp_tac (!simpset addsimps [Cons_def]) 1);
qed"mksch_cons1";

goal thy "!!x.[|x~:act A;x:act B|] \
\   ==> mksch A B`(x>>tr)`schA`schB = \
\        (Takewhile (%a.a:int B)`schB)  \
\         @@ (x>>(mksch A B`tr`schA`(TL`(Dropwhile (%a.a:int B)`schB))  \
\                            ))";
br trans 1;
by (stac mksch_unfold 1);
by (asm_full_simp_tac (!simpset addsimps [Cons_def,If_and_if]) 1);
by (simp_tac (!simpset addsimps [Cons_def]) 1);
qed"mksch_cons2";

goal thy "!!x.[|x:act A;x:act B|] \
\   ==> mksch A B`(x>>tr)`schA`schB = \
\            (Takewhile (%a.a:int A)`schA) \
\         @@ ((Takewhile (%a.a:int B)`schB)  \
\         @@ (x>>(mksch A B`tr`(TL`(Dropwhile (%a.a:int A)`schA)) \
\                            `(TL`(Dropwhile (%a.a:int B)`schB))))  \
\             )";
br trans 1;
by (stac mksch_unfold 1);
by (asm_full_simp_tac (!simpset addsimps [Cons_def,If_and_if]) 1);
by (simp_tac (!simpset addsimps [Cons_def]) 1);
qed"mksch_cons3";

val compotr_simps =[mksch_UU,mksch_nil, mksch_cons1,mksch_cons2,mksch_cons3];

Addsimps compotr_simps;


(* ------------------------------------------------------------------ *)
(*                      The following lemmata aim for                 *)
(*               COMPOSITIONALITY   on    TRACE     Level             *)
(* ------------------------------------------------------------------ *)


(* ---------------------------------------------------------------------------- *)
(*                  Specifics for "==>"                                         *)
(* ---------------------------------------------------------------------------- *)

(* Consequence out of ext1_ext2_is_not_act1(2), which in turn are consequences out of 
   the compatibility of IOA, in particular out of the condition that internals are 
   really hidden. *)

goal thy "(eB & ~eA --> ~A) -->       \
\         (A & (eA | eB)) = (eA & A)";
by (Fast_tac 1);
qed"compatibility_consequence1";


(* very similar to above, only the commutativity of | is used to make a slight change *)

goal thy "(eB & ~eA --> ~A) -->       \
\         (A & (eB | eA)) = (eA & A)";
by (Fast_tac 1);
qed"compatibility_consequence2";


goal thy "!!x. [| x = nil;  y = z|] ==> (x @@ y) = z";
auto();
qed"nil_and_tconc";

(* FIX: should be easy to get out of lemma before *)
goal thy "!!x. [| x = nil;  f`y = f`z|] ==> f`(x @@ y) = f`z";
auto();
qed"nil_and_tconc_f";

(* FIX: should be something like subst: or better improve simp_tac so that these lemmat are
        superfluid *)
goal thy "!!x. [| x1 = x2;  f`(x2 @@ y) = f`z|] ==> f`(x1 @@ y) = f`z";
auto();
qed"tconcf";



(*


(* -------------------------------------------------------------------------------- *)


goal thy "!!A B. compat_ioas A B ==> \
\   ! schA schB. Forall (%x. x:act (A||B)) tr \
\   --> Forall (%x. x:act (A||B)) (mksch A B`tr`schA`schB)";
by (Seq_induct_tac "tr" [Forall_def,sforall_def,mksch_def] 1); 
by (safe_tac set_cs);
by (asm_full_simp_tac (!simpset addsimps [actions_of_par]) 1);
by (case_tac "a:act A" 1);
by (case_tac "a:act B" 1);
(* a:A, a:B *)
by (Asm_full_simp_tac 1);
br (Forall_Conc_impl RS mp) 1;
by (asm_full_simp_tac (!simpset addsimps [ForallPTakewhileQ,intAisnotextB,int_is_act]) 1);
br (Forall_Conc_impl RS mp) 1;
by (asm_full_simp_tac (!simpset addsimps [ForallPTakewhileQ,intAisnotextB,int_is_act]) 1);
(* a:A,a~:B *)
by (Asm_full_simp_tac 1);
br (Forall_Conc_impl RS mp) 1;
by (asm_full_simp_tac (!simpset addsimps [ForallPTakewhileQ,intAisnotextB,int_is_act]) 1);
by (case_tac "a:act B" 1);
(* a~:A, a:B *)
by (Asm_full_simp_tac 1);
br (Forall_Conc_impl RS mp) 1;
by (asm_full_simp_tac (!simpset addsimps [ForallPTakewhileQ,intAisnotextB,int_is_act]) 1);
(* a~:A,a~:B *)
auto();
qed"ForallAorB_mksch";


goal thy "!!A B. compat_ioas A B ==> \
\   ! schA schB.  (Forall (%x. x:act B & x~:act A) tr \
\   --> Forall (%x. x:act B & x~:act A) (mksch A B`tr`schA`schB))";

by (Seq_induct_tac "tr" [Forall_def,sforall_def,mksch_def] 1);
by (safe_tac set_cs);
br (Forall_Conc_impl RS mp) 1;
by (asm_full_simp_tac (!simpset addsimps [ForallPTakewhileQ,intAisnotextB,int_is_act]) 1);
qed"ForallBnA_mksch";

goal thy "!!A B. compat_ioas B A ==> \
\   ! schA schB.  (Forall (%x. x:act A & x~:act B) tr \
\   --> Forall (%x. x:act A & x~:act B) (mksch A B`tr`schA`schB))";

by (Seq_induct_tac "tr" [Forall_def,sforall_def,mksch_def] 1);
by (safe_tac set_cs);
by (Asm_full_simp_tac 1);
br (Forall_Conc_impl RS mp) 1;
by (asm_full_simp_tac (!simpset addsimps [ForallPTakewhileQ,intAisnotextB,int_is_act]) 1);
qed"ForallAnB_mksch";


(* ------------------------------------------------------------------------------------ *)

(*
goal thy "!! tr. Finite tr ==> \
\   ! x y. Filter (%a. a:ext A)`x = Filter (%a. a:act A)`tr & \
\          Filter (%a. a:ext B)`y = Filter (%a. a:act B)`tr &\
\          Forall (%x. x:ext (A||B)) tr \
\          --> Finite (mksch A B`tr`x`y)";

be Seq_Finite_ind  1;
by (Asm_full_simp_tac 1);
(* main case *)
by (asm_full_simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (safe_tac set_cs);
by (Asm_full_simp_tac 1);



qed"FiniteL_mksch";

goal thy " !!bs. Finite bs ==>  \
\ Forall (%x. x:act B & x~:act A) bs &\
\ Filter (%a. a:ext B)`y = Filter (%a. a:act B)`(bs @@ z) \
\ --> (? y1 y2.  (mksch A B`(bs @@ z)`x`y) = (y1 @@ (mksch A B`z`x`y2)) & \
\                Forall (%x. x:act B & x~:act A) y1 & \
\                Finite y1 & y = (y1 @@ y2) & \
\                Filter (%a. a:ext B)`y1 = bs)";
be Seq_Finite_ind  1;
by (rtac impI 1);
by (res_inst_tac [("x","nil")] exI 1);
by (res_inst_tac [("x","y")] exI 1);
by (Asm_full_simp_tac 1);
(* main case *)
by (rtac impI 1);
by (Asm_full_simp_tac 1);
by (REPEAT (etac conjE 1));





qed"reduce_mksch";

*)


(* Lemma for substitution of looping assumption in another specific assumption *) 
val [p1,p2] = goal thy "[| f << (g x) ; x=(h x) |] ==> f << g (h x)";
by (cut_facts_tac [p1] 1);
be (p2 RS subst) 1;
qed"subst_lemma1";




 
(*---------------------------------------------------------------------------
    Filtering external actions out of mksch(tr,schA,schB) yields the oracle tr
                             structural induction
  --------------------------------------------------------------------------- *)

goal thy "! schA schB. compat_ioas A B & compat_ioas B A &\
\ is_asig(asig_of A) & is_asig(asig_of B) &\
\ Forall (%x.x:ext (A||B)) tr & \
\ Filter (%a.a:act A)`tr << Filter (%a.a:ext A)`schA &\
\ Filter (%a.a:act B)`tr << Filter (%a.a:ext B)`schB  \
\ --> Filter (%a.a:ext (A||B))`(mksch A B`tr`schA`schB) = tr";

by (Seq_induct_tac "tr" [Forall_def,sforall_def,mksch_def] 1);

(* main case *) 
(* splitting into 4 cases according to a:A, a:B *)
by (asm_full_simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (safe_tac set_cs);

(* Case a:A, a:B *)
by (forward_tac [divide_Seq] 1);
by (forward_tac [divide_Seq] 1);
back();
by (REPEAT (etac conjE 1));
(* filtering internals of A is nil *)
br nil_and_tconc 1;
br FilterPTakewhileQnil 1;
by (asm_full_simp_tac (!simpset addsimps [not_ext_is_int_FIX]) 1);
by (asm_full_simp_tac (!simpset addsimps [externals_of_par,
             intA_is_not_extB,int_is_not_ext]) 1);
(* end*)
(* filtering internals of B is nil *)
(* FIX: should be done by simp_tac and claset combined until end*)
br nil_and_tconc 1;
br FilterPTakewhileQnil 1;
by (asm_full_simp_tac (!simpset addsimps [not_ext_is_int_FIX]) 1);
by (asm_full_simp_tac (!simpset addsimps [externals_of_par,
             intA_is_not_extB,int_is_not_ext]) 1);
(* end*)
(* conclusion of IH ok, but assumptions of IH have to be transformed *)
by (dres_inst_tac [("x","schA")] subst_lemma1 1);
ba 1;
by (dres_inst_tac [("x","schB")] subst_lemma1 1);
ba 1;
by (asm_full_simp_tac (!simpset addsimps [not_ext_is_int_FIX,FilterPTakewhileQnil]) 1);

(* Case a:B, a~:A *)

by (forward_tac [divide_Seq] 1);
by (REPEAT (etac conjE 1));
(* filtering internals of A is nil *)
(* FIX: should be done by simp_tac and claset combined until end*)
br nil_and_tconc 1;
br FilterPTakewhileQnil 1;
by (asm_full_simp_tac (!simpset addsimps [not_ext_is_int_FIX]) 1);
by (asm_full_simp_tac (!simpset addsimps [externals_of_par,
             intA_is_not_extB,int_is_not_ext]) 1);
(* end*)
by (dres_inst_tac [("x","schB")] subst_lemma1 1);
back();
ba 1;
by (asm_full_simp_tac (!simpset addsimps [not_ext_is_int_FIX,FilterPTakewhileQnil]) 1);

(* Case a:A, a~:B *)

by (forward_tac [divide_Seq] 1);
by (REPEAT (etac conjE 1));
(* filtering internals of A is nil *)
(* FIX: should be done by simp_tac and claset combined until end*)
br nil_and_tconc 1;
br FilterPTakewhileQnil 1;
by (asm_full_simp_tac (!simpset addsimps [not_ext_is_int_FIX]) 1);
by (asm_full_simp_tac (!simpset addsimps [externals_of_par,
             intA_is_not_extB,int_is_not_ext]) 1);
(* end*)
by (dres_inst_tac [("x","schA")] subst_lemma1 1);
ba 1;
by (asm_full_simp_tac (!simpset addsimps [not_ext_is_int_FIX,FilterPTakewhileQnil]) 1);

(* Case a~:A, a~:B *)

by (fast_tac (!claset addSIs [ext_is_act] 
                      addss (!simpset addsimps [externals_of_par]) ) 1);
qed"filterA_mksch_is_tr";




goal thy "!!x y. [|x=UU; y=UU|] ==> x=y";
auto();
qed"both_UU"; 

goal thy "!!x y. [|x=nil; y=nil|] ==> x=y";
auto();
qed"both_nil";


(* FIX: does it exist already? *)
(* To eliminate representation a##xs, if only ~=UU & ~=nil is needed *)
goal thy "!!tr.  [|tr=a##xs; a~=UU |] ==> tr~=UU & tr~=nil";
 by (Asm_full_simp_tac 1);
qed"yields_not_UU_or_nil";





(*---------------------------------------------------------------------------
              Filter of mksch(tr,schA,schB) to A is schA 
                             take lemma
  --------------------------------------------------------------------------- *)

goal thy "compat_ioas A B &  compat_ioas B A &\
\ Forall (%x.x:ext (A||B)) tr & \
\ Filter (%a.a:ext A)`schA = Filter (%a.a:act A)`tr &\
\ Filter (%a.a:ext B)`schB = Filter (%a.a:act B)`tr &\
\ LastActExtsch schA & LastActExtsch schB  \
\ --> Filter (%a.a:act A)`(mksch A B`tr`schA`schB) = schA";


by (res_inst_tac [("Q","%x. x:act B & x~:act A")] take_lemma_less_induct 1);


(*---------------------------------------------------------------------------
              Filter of mksch(tr,schA,schB) to A is schA 
                             take lemma
  --------------------------------------------------------------------------- *)

goal thy "! schA schB tr. compat_ioas A B &  compat_ioas B A &\
\ forall (plift (%x.x:externals(asig_of (A||B)))) tr & \
\ tfilter`(plift (%a.a:externals(asig_of A)))`schA = tfilter`(plift (%a.a:actions(asig_of A)))`tr &\
\ tfilter`(plift (%a.a:externals(asig_of B)))`schB = tfilter`(plift (%a.a:actions(asig_of B)))`tr &\
\ LastActExtsch schA & LastActExtsch schB  \
\ --> trace_take n`(tfilter`(plift (%a.a:actions(asig_of A)))`(mksch A B`tr`schA`schB)) = trace_take n`schA";

by (res_inst_tac[("n","n")] less_induct 1);
by (REPEAT(rtac allI 1));
br impI 1;
by (REPEAT (etac conjE 1));
by (res_inst_tac [("x","tr")] trace.cases 1);

(* tr = UU *)
by (rotate_tac ~1 1);
by (Asm_full_simp_tac 1);
by (dtac LastActExtimplUU 1);
ba 1;
by (Asm_simp_tac 1);

(* tr = nil *)
by (rotate_tac ~1 1);
by (Asm_full_simp_tac 1);
by (dtac LastActExtimplnil 1);
ba 1;
by (Asm_simp_tac 1);

(* tr = t##ts *)

(* just to delete tr=a##xs, as we do not make induction on a but on an element in 
   xs we find later *)
by (dtac yields_not_UU_or_nil 1);
ba 1;
by (REPEAT (etac conjE 1));

(* FIX: or use equality "hd(f ~P x)=UU  =  fa P x" to make distinction on that *)
by (case_tac "forall (plift (%x.x:actions(asig_of B) & x~:actions(asig_of A))) tr" 1);
(* This case holds for whole streams, not only for takes *)
br (trace_take_lemma RS iffD2 RS spec) 1;

by (case_tac "tr : tfinite" 1);

(* FIX: Check if new trace lemmata with ==> instead of --> allow for simplifiaction instead
       of ares_tac in the following *)
br both_nil 1;
(* mksch = nil *)
by (REPEAT (ares_tac [forallQfilterPnil,forallBnA_mksch,finiteL_mksch] 1));
by (Fast_tac 1);
(* schA = nil *)
by (eres_inst_tac [("A","A")] LastActExtimplnil 1);
by (Asm_simp_tac 1);
br forallQfilterPnil 1;
ba 1;
back();
ba 1;
by (Fast_tac 1);

(* case tr~:tfinite *)

br both_UU 1;
(* mksch = UU *)
by (REPEAT (ares_tac [forallQfilterPUU,(finiteR_mksch RS mp COMP rev_contrapos),
                      forallBnA_mksch] 1));
by (Fast_tac 1);
(* schA = UU *)
by (eres_inst_tac [("A","A")] LastActExtimplUU 1);
by (Asm_simp_tac 1);
br forallQfilterPUU 1;
by (REPEAT (atac  1));
back();
by (Fast_tac 1);

(* case" ~ forall (plift (%x.x:actions(asig_of B) & x~:actions(asig_of A))) tr" *)

by (dtac divide_trace3 1);
by (REPEAT (atac 1));
by (REPEAT (etac exE 1));
by (REPEAT (etac conjE 1));

(* rewrite assuption for tr *)
by (hyp_subst_tac 1);
(* bring in lemma reduce_mksch *)
by (forw_inst_tac [("y","schB"),("x","schA")] reduce_mksch 1);
ba 1;
by (asm_simp_tac HOL_min_ss 1);
by (REPEAT (etac exE 1));
by (REPEAT (etac conjE 1));

(* use reduce_mksch to rewrite conclusion *)
by (hyp_subst_tac 1);
by (Asm_full_simp_tac  1);

(* eliminate the B-only prefix *)
(* FIX: Cannot be done by 
   by (asm_full_simp_tac (HOL_min_ss addsimps [forallQfilterPnil]) 1);
   as P&Q --> Q is looping. Perhaps forall (and other) operations not on predicates but on 
   sets because of this reason ?????? *)
br nil_and_tconc_f 1;
be forallQfilterPnil 1;
ba 1;
by (Fast_tac 1);

(* Now real recursive step follows (in Def x) *)

by (case_tac "x:actions(asig_of A)" 1);
by (case_tac "x~:actions(asig_of B)" 1);
by (rotate_tac ~2 1);
by (asm_full_simp_tac (!simpset addsimps [filter_rep])  1);

(* same problem as above for the B-onlu prefix *)
(* FIX: eliminate generated subgoal immeadiately ! (as in case below x:A & x: B *)
by (subgoal_tac "tfilter`(plift (%a. a : actions (asig_of A) & a : externals (asig_of B)))`y1=nil" 1);
by (rotate_tac ~1 1);
by (Asm_full_simp_tac  1);
(* eliminate introduced subgoal 2 *)
be forallQfilterPnil 2;
ba 2;
by (Fast_tac 2);
 
(* f A (tw iA) = tw iA *)
by (simp_tac (HOL_min_ss addsimps [filterPtakewhileQ,int_is_act]) 1);

by (forward_tac [sym RS antisym_less_inverse RS conjunct1 RS divide_trace] 1);
(* subst divide_trace in conlcusion, but only at the righest occurence *)
by (res_inst_tac [("t","schA")] ssubst 1);
back();
back();
back();
ba 1;
by (forward_tac [sym RS antisym_less_inverse RS conjunct1 RS divide_trace_finite] 1);

by (REPEAT (etac conjE 1));
(* reduce trace_takes from n to strictly smaller k *)
by (asm_full_simp_tac (!simpset addsimps [not_int_is_ext]) 1);
br take_reduction 1;
ba 1;
(* now conclusion fulfills induction hypothesis, but assumptions are not ready *)
by (rotate_tac ~10 1);
(* assumption forall and schB *)
by (asm_full_simp_tac (!simpset addsimps [tconc_cong,forall_cons,forall_tconc,ext_and_act]) 1);
(* assumption schA *)
by (dres_inst_tac [("x","schA"),
                   ("g","tfilter`(plift (%a. a : actions (asig_of A)))`rs")] lemma22 1);
ba 1;
by (asm_full_simp_tac (!simpset addsimps [tfiltertconc,not_int_is_ext,tfilterPtakewhileQ]) 1);
by (REPEAT (etac conjE 1));
(* assumptions concerning LastActExtsch, cannot be rewritten, as LastActExtsmalli are looping  *)
by (dres_inst_tac [("sch","schA"),("P","plift (%a. a : internals (asig_of A))")] LastActExtsmall1 1);
by (dres_inst_tac [("sch1.0","y1")]  LastActExtsmall2 1);
ba 1;
by (Asm_full_simp_tac 1);

(* case x:actions(asig_of A) & x: actions(asig_of B) *)
by (rotate_tac ~2 1);
by (asm_full_simp_tac (!simpset addsimps [filter_rep])  1);
by (subgoal_tac "tfilter`(plift (%a. a : actions (asig_of A) & a : externals (asig_of B)))`y1=nil" 1);
by (rotate_tac ~1 1);
by (Asm_full_simp_tac  1);
by (thin_tac' 1 1);
(* eliminate introduced subgoal 2 *)
be forallQfilterPnil 2;
ba 2;
by (Fast_tac 2);
 
(* f A (tw iA) = tw iA *)
by (simp_tac (HOL_min_ss addsimps [filterPtakewhileQ,int_is_act]) 1);

by (forward_tac [sym RS antisym_less_inverse RS conjunct1 RS divide_trace] 1);
(* subst divide_trace in conlcusion, but only at the righest occurence *)
by (res_inst_tac [("t","schA")] ssubst 1);
back();
back();
back();
ba 1;
by (forward_tac [sym RS antisym_less_inverse RS conjunct1 RS divide_trace_finite] 1);
by (REPEAT (etac conjE 1));
(* tidy up *)
by (thin_tac' 12 1);
by (thin_tac' 12 1);
by (thin_tac' 14 1);
by (thin_tac' 14 1);
by (rotate_tac ~8 1);
(* rewrite assumption forall and schB *)
by (asm_full_simp_tac (!simpset addsimps [tconc_cong,forall_cons,forall_tconc,ext_and_act]) 1);
(* divide_trace for schB2 *)
by (forw_inst_tac [("y","y2")] (sym RS antisym_less_inverse RS conjunct1 RS divide_trace) 1);
by (forw_inst_tac [("y","y2")](sym RS antisym_less_inverse RS conjunct1 RS divide_trace_finite) 1);
by (REPEAT (etac conjE 1));
by (rotate_tac ~6 1);
(* assumption schA *)
by (dres_inst_tac [("x","schA"),
                   ("g","tfilter`(plift (%a. a : actions (asig_of A)))`rs")] lemma22 1);
ba 1;
by (asm_full_simp_tac (!simpset addsimps [tfiltertconc,not_int_is_ext,tfilterPtakewhileQ]) 1);
by (REPEAT (etac conjE 1));
(* f A (tw iB schB2) = nil *) 

(* good luck: intAisnotextB is not looping *)
by (asm_full_simp_tac (!simpset addsimps [not_int_is_ext,tfilterPtakewhileQ,intAisnotextB]) 1);
(* reduce trace_takes from n to strictly smaller k *)
by (asm_full_simp_tac (!simpset addsimps [not_int_is_ext]) 1);
br take_reduction 1;
ba 1;
(* now conclusion fulfills induction hypothesis, but assumptions are not all ready *)
(* assumption schB *)
by (dres_inst_tac [("x","y2"),
                   ("g","tfilter`(plift (%a. a : actions (asig_of B)))`rs")] lemma22 1);
ba 1;
(* FIX: hey wonder: why does loopin rule for y2 here rewrites !!!!!!!!!!!!!!!!!!!!!!!!*)
by (asm_full_simp_tac (!simpset addsimps [not_int_is_ext,tfilterPtakewhileQ,intAisnotextB]) 1);
by (REPEAT (etac conjE 1));
(* conclusions concerning LastActExtsch, cannot be rewritten, as LastActExtsmalli are looping  *)
by (dres_inst_tac [("sch","schA"),("P","plift (%a. a : internals (asig_of A))")] LastActExtsmall1 1);
by (dres_inst_tac [("sch1.0","y1")]  LastActExtsmall2 1);
ba 1;
by (dres_inst_tac [("sch","y2"),("P","plift (%a. a : internals (asig_of B))")] LastActExtsmall1 1);
by (Asm_full_simp_tac 1);
 
(* case x~:A & x:B  *)
(* cannot occur, as just this case has been scheduled out before as the B-only prefix *)
by (case_tac "x:actions(asig_of B)" 1);
by (Fast_tac 1);

(* case x~:A & x~:B  *)
(* cannot occur because of assumption: forall (a:ext A | a:ext B) *)
by (rotate_tac ~8 1);
(* reduce forall assumption from tr to (Def x ## rs) *)
by (asm_full_simp_tac (!simpset addsimps [forall_cons,forall_tconc]) 1);
by (REPEAT (etac conjE 1));
by (asm_full_simp_tac (!simpset addsimps [externals_of_par]) 1);
by (fast_tac (!claset addSIs [ext_is_act]) 1);

qed"filterAmksch_is_schA";


goal thy "!! tr. [|compat_ioas A B ;  compat_ioas B A ;\
\ forall (plift (%x.x:externals(asig_of (A||B)))) tr ; \
\ tfilter`(plift (%a.a:externals(asig_of A)))`schA = tfilter`(plift (%a.a:actions(asig_of A)))`tr ;\
\ tfilter`(plift (%a.a:externals(asig_of B)))`schB = tfilter`(plift (%a.a:actions(asig_of B)))`tr ;\
\ LastActExtsch schA ; LastActExtsch schB |] \
\ ==> tfilter`(plift (%a.a:actions(asig_of A)))`(mksch A B`tr`schA`schB) = schA";

br trace.take_lemma 1;
by (asm_simp_tac (!simpset addsimps [filterAmksch_is_schA]) 1);
qed"filterAmkschschA";



(* ------------------------------------------------------------------ *)
(*                COMPOSITIONALITY   on    TRACE    Level             *)
(*                             Main Theorem                           *)
(* ------------------------------------------------------------------ *)
 
goal thy 
"!! A B. [| compat_ioas A B; compat_ioas B A; \
\           is_asig(asig_of A); is_asig(asig_of B)|] \
\       ==> traces(A||B) = \
\           { tr.(Filter (%a.a:act A)`tr : traces A &\
\                 Filter (%a.a:act B)`tr : traces B &\
\                 Forall (%x. x:ext(A||B)) tr) }";

by (simp_tac (!simpset addsimps [traces_def,has_trace_def]) 1);
br set_ext 1;
by (safe_tac set_cs);
 
(* ==> *) 
(* There is a schedule of A *)
by (res_inst_tac [("x","Filter (%a.a:act A)`sch")] bexI 1);
by (asm_full_simp_tac (!simpset addsimps [compositionality_sch]) 2);
by (asm_full_simp_tac (!simpset addsimps [compatibility_consequence1,
                  externals_of_par,ext1_ext2_is_not_act1]) 1);
(* There is a schedule of B *)
by (res_inst_tac [("x","Filter (%a.a:act B)`sch")] bexI 1);
by (asm_full_simp_tac (!simpset addsimps [compositionality_sch]) 2);
by (asm_full_simp_tac (!simpset addsimps [compatibility_consequence2,
                  externals_of_par,ext1_ext2_is_not_act2]) 1);
(* Traces of A||B have only external actions from A or B *)  
br ForallPFilterP 1;

(* <== *)

(* replace schA and schB by cutsch(schA) and cutsch(schB) *)
by (dtac exists_LastActExtsch 1);
ba 1;
by (dtac exists_LastActExtsch 1);
ba 1;
by (REPEAT (etac exE 1));
by (REPEAT (etac conjE 1));

(* mksch is exactly the construction of trA||B out of schA, schB, and the oracle tr,
   we need here *)
by (res_inst_tac [("x","mksch A B`tr`schb`schc")] bexI 1);

(* External actions of mksch are just the oracle *)
by (asm_full_simp_tac (!simpset addsimps [filterA_mksch_is_tr]) 1);

(* mksch is a schedule -- use compositionality on sch-level *)
by (asm_full_simp_tac (!simpset addsimps [compositionality_sch]) 1);

       das hier loopt: ForallPForallQ, ext_is_act,ForallAorB_mksch]) 1);






*)



(* -------------------------------------------------------------------------------
         Other useful things
  -------------------------------------------------------------------------------- *)


(* Lemmata not needed yet 
goal Trace.thy "!!x. nil<<x ==> nil=x";
by (res_inst_tac [("x","x")] trace.cases 1);
by (hyp_subst_tac 1);
by (etac antisym_less 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
by (hyp_subst_tac 1);
by (Asm_full_simp_tac 1);
qed"nil_less_is_nil";


*)




