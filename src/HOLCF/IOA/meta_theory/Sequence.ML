(*  Title:      HOLCF/IOA/meta_theory/Sequence.ML
    ID:        
    Author:     Olaf M"uller
    Copyright   1996  TU Muenchen

Theorems about Sequences over flat domains with lifted elements

*)


Addsimps [andalso_and,andalso_or];

(* ----------------------------------------------------------------------------------- *)

section "recursive equations of operators";

(* ---------------------------------------------------------------- *)
(*                               Map                                *)
(* ---------------------------------------------------------------- *)

goal thy "Map f`UU =UU";
by (simp_tac (!simpset addsimps [Map_def]) 1);
qed"Map_UU";

goal thy "Map f`nil =nil";
by (simp_tac (!simpset addsimps [Map_def]) 1);
qed"Map_nil";

goal thy "Map f`(x>>xs)=(f x) >> Map f`xs";
by (simp_tac (!simpset addsimps [Map_def, Cons_def,flift2_def]) 1);
qed"Map_cons";

(* ---------------------------------------------------------------- *)
(*                               Filter                             *)
(* ---------------------------------------------------------------- *)

goal thy "Filter P`UU =UU";
by (simp_tac (!simpset addsimps [Filter_def]) 1);
qed"Filter_UU";

goal thy "Filter P`nil =nil";
by (simp_tac (!simpset addsimps [Filter_def]) 1);
qed"Filter_nil";

goal thy "Filter P`(x>>xs)= (if P x then x>>(Filter P`xs) else Filter P`xs)"; 
by (simp_tac (!simpset addsimps [Filter_def, Cons_def,flift2_def,If_and_if]) 1);
qed"Filter_cons";

(* ---------------------------------------------------------------- *)
(*                               Forall                             *)
(* ---------------------------------------------------------------- *)

goal thy "Forall P UU";
by (simp_tac (!simpset addsimps [Forall_def,sforall_def]) 1);
qed"Forall_UU";

goal thy "Forall P nil";
by (simp_tac (!simpset addsimps [Forall_def,sforall_def]) 1);
qed"Forall_nil";

goal thy "Forall P (x>>xs)= (P x & Forall P xs)";
by (simp_tac (!simpset addsimps [Forall_def, sforall_def,
                                 Cons_def,flift2_def]) 1);
qed"Forall_cons";

(* ---------------------------------------------------------------- *)
(*                               Conc                               *)
(* ---------------------------------------------------------------- *)

goal thy "UU @@ y =UU";
by (Simp_tac 1);
qed"Conc_UU";

goal thy "nil @@ y =y";
by (Simp_tac 1);
qed"Conc_nil";

goal thy "(x>>xs) @@ y = x>>(xs @@y)"; 
by (simp_tac (!simpset addsimps [Cons_def]) 1);
qed"Conc_cons";

(* ---------------------------------------------------------------- *)
(*                               Takewhile                          *)
(* ---------------------------------------------------------------- *)

goal thy "Takewhile P`UU =UU";
by (simp_tac (!simpset addsimps [Takewhile_def]) 1);
qed"Takewhile_UU";

goal thy "Takewhile P`nil =nil";
by (simp_tac (!simpset addsimps [Takewhile_def]) 1);
qed"Takewhile_nil";

goal thy "Takewhile P`(x>>xs)= (if P x then x>>(Takewhile P`xs) else nil)"; 
by (simp_tac (!simpset addsimps [Takewhile_def, Cons_def,flift2_def,If_and_if]) 1);
qed"Takewhile_cons";

(* ---------------------------------------------------------------- *)
(*                               Dropwhile                          *)
(* ---------------------------------------------------------------- *)

goal thy "Dropwhile P`UU =UU";
by (simp_tac (!simpset addsimps [Dropwhile_def]) 1);
qed"Dropwhile_UU";

goal thy "Dropwhile P`nil =nil";
by (simp_tac (!simpset addsimps [Dropwhile_def]) 1);
qed"Dropwhile_nil";

goal thy "Dropwhile P`(x>>xs)= (if P x then Dropwhile P`xs else x>>xs)"; 
by (simp_tac (!simpset addsimps [Dropwhile_def, Cons_def,flift2_def,If_and_if]) 1);
qed"Dropwhile_cons";

(* ---------------------------------------------------------------- *)
(*                               Last                               *)
(* ---------------------------------------------------------------- *)


goal thy "Last`UU =UU";
by (simp_tac (!simpset addsimps [Last_def]) 1);
qed"Last_UU";

goal thy "Last`nil =UU";
by (simp_tac (!simpset addsimps [Last_def]) 1);
qed"Last_nil";

goal thy "Last`(x>>xs)= (if xs=nil then Def x else Last`xs)"; 
by (simp_tac (!simpset addsimps [Last_def, Cons_def]) 1);
by (res_inst_tac [("x","xs")] seq.cases 1);
by (asm_simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (REPEAT (Asm_simp_tac 1));
qed"Last_cons";


(* ---------------------------------------------------------------- *)
(*                               Flat                               *)
(* ---------------------------------------------------------------- *)

goal thy "Flat`UU =UU";
by (simp_tac (!simpset addsimps [Flat_def]) 1);
qed"Flat_UU";

goal thy "Flat`nil =nil";
by (simp_tac (!simpset addsimps [Flat_def]) 1);
qed"Flat_nil";

goal thy "Flat`(x##xs)= x @@ (Flat`xs)"; 
by (simp_tac (!simpset addsimps [Flat_def, Cons_def]) 1);
qed"Flat_cons";


(* ---------------------------------------------------------------- *)
(*                               Zip                                *)
(* ---------------------------------------------------------------- *)

goal thy "Zip = (LAM t1 t2. case t1 of \
\               nil   => nil \
\             | x##xs => (case t2 of \ 
\                          nil => UU  \
\                        | y##ys => (case x of \
\                                      Undef  => UU \
\                                    | Def a => (case y of \
\                                                  Undef => UU \
\                                                | Def b => Def (a,b)##(Zip`xs`ys)))))";
by (rtac trans 1);
br fix_eq2 1;
br Zip_def 1;
br beta_cfun 1;
by (Simp_tac 1);
qed"Zip_unfold";

goal thy "Zip`UU`y =UU";
by (stac Zip_unfold 1);
by (Simp_tac 1);
qed"Zip_UU1";

goal thy "!! x. x~=nil ==> Zip`x`UU =UU";
by (stac Zip_unfold 1);
by (Simp_tac 1);
by (res_inst_tac [("x","x")] seq.cases 1);
by (REPEAT (Asm_full_simp_tac 1));
qed"Zip_UU2";

goal thy "Zip`nil`y =nil";
by (stac Zip_unfold 1);
by (Simp_tac 1);
qed"Zip_nil";

goal thy "Zip`(x>>xs)`nil= UU"; 
by (stac Zip_unfold 1);
by (simp_tac (!simpset addsimps [Cons_def]) 1);
qed"Zip_cons_nil";

goal thy "Zip`(x>>xs)`(y>>ys)= (x,y) >> Zip`xs`ys"; 
br trans 1;
by (stac Zip_unfold 1);
by (Simp_tac 1);
(* FIX: Why Simp_tac 2 times. Does continuity in simpflication make job sometimes not 
  completely ready ? *)
by (simp_tac (!simpset addsimps [Cons_def]) 1);
qed"Zip_cons";


Delsimps [sfilter_UU,sfilter_nil,sfilter_cons,
          smap_UU,smap_nil,smap_cons,
          sforall2_UU,sforall2_nil,sforall2_cons,
          slast_UU,slast_nil,slast_cons,
          stakewhile_UU, stakewhile_nil, stakewhile_cons, 
          sdropwhile_UU, sdropwhile_nil, sdropwhile_cons,
          sflat_UU,sflat_nil,sflat_cons,
          szip_UU1,szip_UU2,szip_nil,szip_cons_nil,szip_cons];


Addsimps [Filter_UU,Filter_nil,Filter_cons,
          Map_UU,Map_nil,Map_cons,
          Forall_UU,Forall_nil,Forall_cons,
          Last_UU,Last_nil,Last_cons,
          Conc_UU,Conc_nil,Conc_cons,
          Takewhile_UU, Takewhile_nil, Takewhile_cons, 
          Dropwhile_UU, Dropwhile_nil, Dropwhile_cons,
          Zip_UU1,Zip_UU2,Zip_nil,Zip_cons_nil,Zip_cons];


(*

Can Filter with HOL predicate directly be defined as fixpoint ?

goal thy "Filter2 P = (LAM tr. case tr of  \
 \         nil   => nil \
 \       | x##xs => (case x of Undef => UU | Def y => \
\                   (if P y then y>>(Filter2 P`xs) else Filter2 P`xs)))";
by (rtac trans 1);
br fix_eq2 1;
br Filter2_def 1;
br beta_cfun 1;
by (Simp_tac 1);

is also possible, if then else has to be proven continuous and it would be nice if a case for 
Seq would be available.

*)


(* ------------------------------------------------------------------------------------- *)


section "Cons";

goal thy "a>>s = (Def a)##s";
by (simp_tac (!simpset addsimps [Cons_def]) 1);
qed"Cons_def2";

goal thy "x = UU | x = nil | (? a s. x = a >> s)";
by (simp_tac (!simpset addsimps [Cons_def2]) 1);
by (cut_facts_tac [seq.exhaust] 1);
by (fast_tac (HOL_cs addDs [not_Undef_is_Def RS iffD1]) 1);
qed"Seq_exhaust";


goal thy "!!P. [| x = UU ==> P; x = nil ==> P; !!a s. x = a >> s  ==> P |] ==> P";
by (cut_inst_tac [("x","x")] Seq_exhaust 1);
be disjE 1;
by (Asm_full_simp_tac 1);
be disjE 1;
by (Asm_full_simp_tac 1);
by (REPEAT (etac exE 1));
by (Asm_full_simp_tac 1);
qed"Seq_cases";

fun Seq_case_tac s i = res_inst_tac [("x",s)] Seq_cases i
	  THEN hyp_subst_tac i THEN hyp_subst_tac (i+1) THEN hyp_subst_tac (i+2);

(* on a>>s only simp_tac, as full_simp_tac is uncomplete and often causes errors *)
fun Seq_case_simp_tac s i = Seq_case_tac s i THEN Asm_simp_tac (i+2)
                                             THEN Asm_full_simp_tac (i+1)
                                             THEN Asm_full_simp_tac i;

goal thy "a>>s ~= UU";
by (stac Cons_def2 1);
by (resolve_tac seq.con_rews 1);
br Def_not_UU 1;
qed"Cons_not_UU";

goal thy "~(a>>x) << UU";
by (rtac notI 1);
by (dtac antisym_less 1);
by (Simp_tac 1);
by (asm_full_simp_tac (!simpset addsimps [Cons_not_UU]) 1);
qed"Cons_not_less_UU";

goal thy "~a>>s << nil";
by (stac Cons_def2 1);
by (resolve_tac seq.rews 1);
br Def_not_UU 1;
qed"Cons_not_less_nil";

goal thy "a>>s ~= nil";
by (stac Cons_def2 1);
by (resolve_tac seq.rews 1);
qed"Cons_not_nil";

goal thy "(a>>s = b>>t) = (a = b & s = t)";
by (simp_tac (HOL_ss addsimps [Cons_def2]) 1);
by (stac (hd lift.inject RS sym) 1);
back(); back();
by (rtac scons_inject_eq 1);
by (REPEAT(rtac Def_not_UU 1));
qed"Cons_inject_eq";

goal thy "(a>>s<<b>>t) = (a = b & s<<t)";
by (simp_tac (!simpset addsimps [Cons_def2]) 1);
by (stac (Def_inject_less_eq RS sym) 1);
back();
by (rtac iffI 1);
(* 1 *)
by (etac (hd seq.inverts) 1);
by (REPEAT(rtac Def_not_UU 1));
(* 2 *)
by (Asm_full_simp_tac 1);
by (etac conjE 1);
by (etac monofun_cfun_arg 1);
qed"Cons_inject_less_eq";

goal thy "seq_take (Suc n)`(a>>x) = a>> (seq_take n`x)";
by (simp_tac (!simpset addsimps [Cons_def]) 1);
qed"seq_take_Cons";

Addsimps [Cons_inject_eq,Cons_inject_less_eq,seq_take_Cons,
          Cons_not_UU,Cons_not_less_UU,Cons_not_less_nil,Cons_not_nil];


(* ----------------------------------------------------------------------------------- *)

section "induction";

goal thy "!! P. [| adm P; P UU; P nil; !! a s. P s ==> P (a>>s)|] ==> P x";
be seq.ind 1;
by (REPEAT (atac 1));
by (def_tac 1);
by (asm_full_simp_tac (!simpset addsimps [Cons_def]) 1);
qed"Seq_induct";

goal thy "!! P.[|P UU;P nil; !! a s. P s ==> P(a>>s) |]  \
\               ==> seq_finite x --> P x";
be seq_finite_ind 1;
by (REPEAT (atac 1));
by (def_tac 1);
by (asm_full_simp_tac (!simpset addsimps [Cons_def]) 1);
qed"Seq_FinitePartial_ind";

goal thy "!! P.[| Finite x; P nil; !! a s. [| Finite s; P s|] ==> P (a>>s) |] ==> P x";
be sfinite.induct 1;
ba 1;
by (def_tac 1);
by (asm_full_simp_tac (!simpset addsimps [Cons_def]) 1);
qed"Seq_Finite_ind"; 


(* rws are definitions to be unfolded for admissibility check *)
fun Seq_induct_tac s rws i = res_inst_tac [("x",s)] Seq_induct i
                         THEN (REPEAT_DETERM (CHANGED (Asm_simp_tac (i+1))))
                         THEN simp_tac (!simpset addsimps rws) i;

fun Seq_Finite_induct_tac i = etac Seq_Finite_ind i
                              THEN (REPEAT_DETERM (CHANGED (Asm_simp_tac i)));

fun pair_tac s = res_inst_tac [("p",s)] PairE
			  THEN' hyp_subst_tac THEN' Asm_full_simp_tac;

(* induction on a sequence of pairs with pairsplitting and simplification *)
fun pair_induct_tac s rws i = 
           res_inst_tac [("x",s)] Seq_induct i 
           THEN pair_tac "a" (i+3) 
           THEN (REPEAT_DETERM (CHANGED (Simp_tac (i+1)))) 
           THEN simp_tac (!simpset addsimps rws) i;



(* ------------------------------------------------------------------------------------ *)

section "HD,TL";

goal thy "HD`(x>>y) = Def x";
by (simp_tac (!simpset addsimps [Cons_def]) 1);
qed"HD_Cons";

goal thy "TL`(x>>y) = y";
by (simp_tac (!simpset addsimps [Cons_def]) 1);
qed"TL_Cons";

Addsimps [HD_Cons,TL_Cons];

(* ------------------------------------------------------------------------------------ *)

section "Finite, Partial, Infinite";

goal thy "Finite (a>>xs) = Finite xs";
by (simp_tac (!simpset addsimps [Cons_def2,Finite_cons]) 1);
qed"Finite_Cons";

Addsimps [Finite_Cons];

(* ------------------------------------------------------------------------------------ *)

section "Conc";

goal thy "!! x::'a Seq. Finite x ==> ((x @@ y) = (x @@ z)) = (y = z)";
by (Seq_Finite_induct_tac 1);
qed"Conc_cong";

(* ------------------------------------------------------------------------------------ *)

section "Last";

goal thy "!! s.Finite s ==> s~=nil --> Last`s~=UU";
by (Seq_Finite_induct_tac  1);
by (asm_simp_tac (!simpset setloop split_tac [expand_if]) 1);
qed"Finite_Last1";

goal thy "!! s. Finite s ==> Last`s=UU --> s=nil";
by (Seq_Finite_induct_tac  1);
by (asm_simp_tac (!simpset setloop split_tac [expand_if]) 1);
by (fast_tac HOL_cs 1);
qed"Finite_Last2";


(* ------------------------------------------------------------------------------------ *)


section "Filter, Conc";


goal thy "Filter P`(Filter Q`s) = Filter (%x. P x & Q x)`s";
by (Seq_induct_tac "s" [Filter_def] 1);
by (asm_full_simp_tac (!simpset setloop split_tac [expand_if] ) 1);
qed"FilterPQ";

goal thy "Filter P`(x @@ y) = (Filter P`x @@ Filter P`y)";
by (simp_tac (!simpset addsimps [Filter_def,sfiltersconc]) 1);
qed"FilterConc";

(* ------------------------------------------------------------------------------------ *)

section "Map";

goal thy "Map f`(Map g`s) = Map (f o g)`s";
by (Seq_induct_tac "s" [] 1);
qed"MapMap";

goal thy "Map f`(x@@y) = (Map f`x) @@ (Map f`y)";
by (Seq_induct_tac "x" [] 1);
qed"MapConc";

goal thy "Filter P`(Map f`x) = Map f`(Filter (P o f)`x)";
by (Seq_induct_tac "x" [] 1);
by (asm_full_simp_tac (!simpset setloop split_tac [expand_if] ) 1);
qed"MapFilter";


(* ------------------------------------------------------------------------------------ *)

section "Forall, Conc";


goal thy "Forall P ys & (! x. P x --> Q x) \
\         --> Forall Q ys";
by (Seq_induct_tac "ys" [Forall_def,sforall_def] 1);
qed"ForallPForallQ1";

bind_thm ("ForallPForallQ",impI RSN (2,allI RSN (2,conjI RS (ForallPForallQ1 RS mp))));

goal thy "(Forall P x & Forall P y) --> Forall P (x @@ y)";
by (Seq_induct_tac "x" [Forall_def,sforall_def] 1);
qed"Forall_Conc_impl";

goal thy "!! x. Finite x ==> Forall P (x @@ y) = (Forall P x & Forall P y)";
by (Seq_Finite_induct_tac  1);
qed"Forall_Conc";


(* ------------------------------------------------------------------------------------- *)

section "Forall, Filter";


goal thy "Forall P (Filter P`x)";
by (simp_tac (!simpset addsimps [Filter_def,Forall_def,forallPsfilterP]) 1);
qed"ForallPFilterP";

(* FIX: holds also in other direction, then equal to forallPfilterP *)
goal thy "Forall P x --> Filter P`x = x";
by (Seq_induct_tac "x" [Forall_def,sforall_def,Filter_def] 1);
qed"ForallPFilterPid1";

val ForallPFilterPid = standard (ForallPFilterPid1 RS mp);


(* holds also in <-- direction. FIX: prove that also *)

goal thy "!! P. Finite ys & Forall (%x. ~P x) ys \
\   --> Filter P`ys = nil ";
by (res_inst_tac[("x","ys")] Seq_induct 1);
(* adm *)
(* FIX: cont tfinite behandeln *)
br adm_all 1;
(* base cases *)
by (Simp_tac 1);
by (Simp_tac 1);
(* main case *)
by (asm_full_simp_tac (!simpset setloop split_tac [expand_if] ) 1);
qed"ForallnPFilterPnil1";

val ForallnPFilterPnil = standard (conjI RS (ForallnPFilterPnil1 RS mp));


(* FIX: holds also in <== direction *)
goal thy   "!! P. ~Finite ys & Forall (%x. ~P x) ys \
\                  --> Filter P`ys = UU ";
by (res_inst_tac[("x","ys")] Seq_induct 1);
(* adm *)
(* FIX: cont ~tfinite behandeln *)
br adm_all 1;
(* base cases *)
by (Simp_tac 1);
by (Simp_tac 1);
(* main case *)
by (asm_full_simp_tac (!simpset setloop split_tac [expand_if] ) 1);
qed"ForallnPFilterPUU1";

val ForallnPFilterPUU = standard (conjI RS (ForallnPFilterPUU1 RS mp));


goal thy  "!! Q P.[| Forall Q ys; Finite ys; !!x. Q x ==> ~P x|] \
\   ==> Filter P`ys = nil";
be ForallnPFilterPnil 1;
be ForallPForallQ 1;
auto();
qed"ForallQFilterPnil";

goal thy "!! Q P. [| ~Finite ys; Forall Q ys;  !!x. Q x ==> ~P x|] \
\   ==> Filter P`ys = UU ";
be ForallnPFilterPUU 1;
be ForallPForallQ 1;
auto();
qed"ForallQFilterPUU";



(* ------------------------------------------------------------------------------------- *)

section "Takewhile, Forall, Filter";


goal thy "Forall P (Takewhile P`x)";
by (simp_tac (!simpset addsimps [Forall_def,Takewhile_def,sforallPstakewhileP]) 1);
qed"ForallPTakewhileP";


goal thy"!! P. [| !!x. Q x==> P x |] ==> Forall P (Takewhile Q`x)";
br ForallPForallQ 1;
br ForallPTakewhileP 1;
auto();
qed"ForallPTakewhileQ";


goal thy  "!! Q P.[| Finite (Takewhile Q`ys); !!x. Q x ==> ~P x |] \
\   ==> Filter P`(Takewhile Q`ys) = nil";
be ForallnPFilterPnil 1;
br ForallPForallQ 1;
br ForallPTakewhileP 1;
auto();
qed"FilterPTakewhileQnil";

goal thy "!! Q P. [| !!x. Q x ==> P x |] ==> \
\            Filter P`(Takewhile Q`ys) = (Takewhile Q`ys)";
br ForallPFilterPid 1;
br ForallPForallQ 1;
br ForallPTakewhileP 1;
auto();
qed"FilterPTakewhileQid";

Addsimps [ForallPTakewhileP,ForallPTakewhileQ,
          FilterPTakewhileQnil,FilterPTakewhileQid];



(* ----------------------------------------------------------------------------------- *)


(*
section "admissibility";

goal thy "adm(%x.~Finite x)";
br admI 1;
bd spec 1;
be contrapos 1;

*)

(* ----------------------------------------------------------------------------------- *)

section "coinductive characterizations of Filter";


goal thy "HD`(Filter P`y) = Def x \
\         --> y = ((Takewhile (%x. ~P x)`y) @@ (x >> TL`(Dropwhile (%a.~P a)`y)))  \
\             & Finite (Takewhile (%x. ~ P x)`y)  & P x";

(* FIX: pay attention: is only admissible with chain-finite package to be added to 
        adm test *)
by (Seq_induct_tac "y" [] 1);
br adm_all 1;
by (Asm_full_simp_tac 1); 
by (case_tac "P a" 1);
by (Asm_full_simp_tac 1); 
br impI 1;
by (hyp_subst_tac 1);
by (Asm_full_simp_tac 1); 
(* ~ P a *)
by (Asm_full_simp_tac 1); 
br impI 1;
by (rotate_tac ~1 1);
by (Asm_full_simp_tac 1); 
by (REPEAT (etac conjE 1));
ba 1;
qed"divide_Seq_lemma";

goal thy "!! x. (x>>xs) << Filter P`y  \
\   ==> y = ((Takewhile (%a. ~ P a)`y) @@ (x >> TL`(Dropwhile (%a.~P a)`y))) \
\      & Finite (Takewhile (%a. ~ P a)`y)  & P x";
br (divide_Seq_lemma RS mp) 1;
by (dres_inst_tac [("fo","HD"),("xa","x>>xs")]  monofun_cfun_arg 1);
by (Asm_full_simp_tac 1); 
qed"divide_Seq";


goal thy "~Forall P y --> (? x. HD`(Filter (%a. ~P a)`y) = Def x)";
(* FIX: pay attention: is only admissible with chain-finite package to be added to 
        adm test *)
by (Seq_induct_tac "y" [] 1);
br adm_all 1;
by (case_tac "P a" 1);
by (Asm_full_simp_tac 1); 
by (Asm_full_simp_tac 1); 
qed"nForall_HDFilter";


goal thy "!!y. ~Forall P y  \
\  ==> ? x. y= (Takewhile P`y @@ (x >> TL`(Dropwhile P`y))) & \
\      Finite (Takewhile P`y) & (~ P x)";
bd (nForall_HDFilter RS mp) 1;
by (safe_tac set_cs);
by (res_inst_tac [("x","x")] exI 1);
by (cut_inst_tac [("P1","%x. ~ P x")] (divide_Seq_lemma RS mp) 1);
auto();
qed"divide_Seq2";


goal thy  "!! y. ~Forall P y \
\  ==> ? x bs rs. y= (bs @@ (x>>rs)) & Finite bs & Forall P bs & (~ P x)";
by (cut_inst_tac [] divide_Seq2 1);
auto();
qed"divide_Seq3";

Addsimps [FilterPQ,FilterConc,Conc_cong,Forall_Conc];


(* ------------------------------------------------------------------------------------- *)


section "take_lemma";

goal thy "(!n. seq_take n`x = seq_take n`x') = (x = x')";
by (rtac iffI 1);
br seq.take_lemma 1;
auto();
qed"seq_take_lemma";

(*

goal thy "Finite x & (! k. k < n --> seq_take k`y1 = seq_take k`y2) \
\   --> seq_take n`(x @@ (t>>y1)) =  seq_take n`(x @@ (t>>y2))";
br less_induct 1;


goal thy "!!x. Finite x ==> \
\  ((! k. k < n --> seq_take k`y1 = seq_take k`y2) \
\   --> seq_take n`(x @@ (t>>y1)) =  seq_take n`(x @@ (t>>y2)))";
by (Seq_Finite_induct_tac 1);
by (asm_full_simp_tac (!simpset setloop split_tac [expand_if] ) 1);


qed"take_reduction";
*)

goal thy "!! Q. [|!! s. [| Forall Q s; A s |] ==> (f s) = (g s) ; \
\           !! s1 s2 y. [| Forall Q s1; Finite s1; ~ Q y; A (s1 @@ y>>s2)|] \
\                         ==> (f (s1 @@ y>>s2)) = (g (s1 @@ y>>s2)) |] \
\              ==> A x --> (f x)=(g x)";
by (case_tac "Forall Q x" 1);
by (auto_tac (!claset addSDs [divide_Seq3],!simpset));
qed"take_lemma_principle1";

goal thy "!! Q. [|!! s. [| Forall Q s; A s |] ==> (f s) = (g s) ; \
\           !! s1 s2 y. [| Forall Q s1; Finite s1; ~ Q y; A (s1 @@ y>>s2)|] \
\                         ==> ! n. seq_take n`(f (s1 @@ y>>s2)) \
\                                = seq_take n`(g (s1 @@ y>>s2)) |] \
\              ==> A x --> (f x)=(g x)";
by (case_tac "Forall Q x" 1);
by (auto_tac (!claset addSDs [divide_Seq3],!simpset));
br seq.take_lemma 1;
auto();
qed"take_lemma_principle2";


(* Note: in the following proofs the ordering of proof steps is very 
         important, as otherwise either (Forall Q s1) would be in the IH as
         assumption (then rule useless) or it is not possible to strengthen 
         the IH by doing a forall closure of the sequence t (then rule also useless).
         This is also the reason why the induction rule (less_induct or nat_induct) has to 
         to be imbuilt into the rule, as induction has to be done early and the take lemma 
         has to be used in the trivial direction afterwards for the (Forall Q x) case.  *)

goal thy 
"!! Q. [|!! s. [| Forall Q s; A s |] ==> (f s) = (g s) ; \
\        !! s1 s2 y n. [| ! t. A t --> seq_take n`(f t) = seq_take n`(g t);\
\                         Forall Q s1; Finite s1; ~ Q y; A (s1 @@ y>>s2) |] \
\                         ==>   seq_take (Suc n)`(f (s1 @@ y>>s2)) \
\                             = seq_take (Suc n)`(g (s1 @@ y>>s2)) |] \
\              ==> A x --> (f x)=(g x)";
br impI 1;
br seq.take_lemma 1;
br mp 1;
ba 2;
by (res_inst_tac [("x","x")] spec 1);
br nat_induct 1;
by (Simp_tac 1);
br allI 1;
by (case_tac "Forall Q xa" 1);
by (SELECT_GOAL (auto_tac (!claset addSIs [seq_take_lemma RS iffD2 RS spec],
                           !simpset)) 1);
by (auto_tac (!claset addSDs [divide_Seq3],!simpset));
qed"take_lemma_induct";


goal thy 
"!! Q. [|!! s. [| Forall Q s; A s |] ==> (f s) = (g s) ; \
\        !! s1 s2 y n. [| ! t m. m < n --> A t --> seq_take m`(f t) = seq_take m`(g t);\
\                         Forall Q s1; Finite s1; ~ Q y; A (s1 @@ y>>s2) |] \
\                         ==>   seq_take n`(f (s1 @@ y>>s2)) \
\                             = seq_take n`(g (s1 @@ y>>s2)) |] \
\              ==> A x --> (f x)=(g x)";
br impI 1;
br seq.take_lemma 1;
br mp 1;
ba 2;
by (res_inst_tac [("x","x")] spec 1);
br less_induct 1;
br allI 1;
by (case_tac "Forall Q xa" 1);
by (SELECT_GOAL (auto_tac (!claset addSIs [seq_take_lemma RS iffD2 RS spec],
                           !simpset)) 1);
by (auto_tac (!claset addSDs [divide_Seq3],!simpset));
qed"take_lemma_less_induct";

goal thy 
"!! Q. [| A UU  ==> (f UU) = (g UU) ; \
\         A nil ==> (f nil) = (g nil) ; \
\         !! s y n. [| ! t. A t --> seq_take n`(f t) = seq_take n`(g t);\
\                    A (y>>s) |]   \
\                    ==>   seq_take (Suc n)`(f (y>>s)) \
\                        = seq_take (Suc n)`(g (y>>s)) |] \
\              ==> A x --> (f x)=(g x)";
br impI 1;
br seq.take_lemma 1;
br mp 1;
ba 2;
by (res_inst_tac [("x","x")] spec 1);
br nat_induct 1;
by (Simp_tac 1);
br allI 1;
by (Seq_case_simp_tac "xa" 1);
qed"take_lemma_in_eq_out";


(* ------------------------------------------------------------------------------------ *)

section "alternative take_lemma proofs";


(* --------------------------------------------------------------- *)
(*              Alternative Proof of FilterPQ                      *)
(* --------------------------------------------------------------- *)

Delsimps [FilterPQ];


(* In general: How to do this case without the same adm problems 
   as for the entire proof ? *) 
goal thy "Forall (%x.~(P x & Q x)) s \
\         --> Filter P`(Filter Q`s) =\
\             Filter (%x. P x & Q x)`s";

by (Seq_induct_tac "s" [Forall_def,sforall_def] 1);
by (asm_full_simp_tac (!simpset setloop split_tac [expand_if] ) 1);
qed"Filter_lemma1";

goal thy "!! s. Finite s ==>  \
\         (Forall (%x. (~P x) | (~ Q x)) s  \
\         --> Filter P`(Filter Q`s) = nil)";
by (Seq_Finite_induct_tac 1);
by (asm_full_simp_tac (!simpset setloop split_tac [expand_if] ) 1);
qed"Filter_lemma2";

goal thy "!! s. Finite s ==>  \
\         Forall (%x. (~P x) | (~ Q x)) s  \
\         --> Filter (%x.P x & Q x)`s = nil";
by (Seq_Finite_induct_tac 1);
by (asm_full_simp_tac (!simpset setloop split_tac [expand_if] ) 1);
qed"Filter_lemma3";


goal thy "Filter P`(Filter Q`s) = Filter (%x. P x & Q x)`s";
by (res_inst_tac [("A1","%x.True") 
                 ,("Q1","%x.~(P x & Q x)")]
                 (take_lemma_induct RS mp) 1);
(* FIX: rule always needs a back: eliminate *)
back();
(* FIX: better support for A = %.True *)
by (Fast_tac 3);
by (asm_full_simp_tac (!simpset addsimps [Filter_lemma1]) 1);
by (asm_full_simp_tac (!simpset addsimps [Filter_lemma2,Filter_lemma3] 
                                setloop split_tac [expand_if]) 1);
qed"FilterPQ_takelemma";

Addsimps [FilterPQ];


(* --------------------------------------------------------------- *)
(*              Alternative Proof of MapConc                       *)
(* --------------------------------------------------------------- *)

Delsimps [MapConc];

goal thy "Map f`(x@@y) = (Map f`x) @@ (Map f`y)";
by (res_inst_tac [("A1","%x.True"),("x1","x")] (take_lemma_in_eq_out RS mp) 1);
auto();
qed"MapConc_takelemma";

Addsimps [MapConc];

