(*  Title:      HOLCF/IOA/meta_theory/Sequence.ML
    ID:         $Id$
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

Goal "Map f$UU =UU";
by (simp_tac (simpset() addsimps [Map_def]) 1);
qed"Map_UU";

Goal "Map f$nil =nil";
by (simp_tac (simpset() addsimps [Map_def]) 1);
qed"Map_nil";

Goal "Map f$(x>>xs)=(f x) >> Map f$xs";
by (simp_tac (simpset() addsimps [Map_def, Consq_def,flift2_def]) 1);
qed"Map_cons";

(* ---------------------------------------------------------------- *)
(*                               Filter                             *)
(* ---------------------------------------------------------------- *)

Goal "Filter P$UU =UU";
by (simp_tac (simpset() addsimps [Filter_def]) 1);
qed"Filter_UU";

Goal "Filter P$nil =nil";
by (simp_tac (simpset() addsimps [Filter_def]) 1);
qed"Filter_nil";

Goal "Filter P$(x>>xs)= (if P x then x>>(Filter P$xs) else Filter P$xs)"; 
by (simp_tac (simpset() addsimps [Filter_def, Consq_def,flift2_def,If_and_if]) 1);
qed"Filter_cons";

(* ---------------------------------------------------------------- *)
(*                               Forall                             *)
(* ---------------------------------------------------------------- *)

Goal "Forall P UU";
by (simp_tac (simpset() addsimps [Forall_def,sforall_def]) 1);
qed"Forall_UU";

Goal "Forall P nil";
by (simp_tac (simpset() addsimps [Forall_def,sforall_def]) 1);
qed"Forall_nil";

Goal "Forall P (x>>xs)= (P x & Forall P xs)";
by (simp_tac (simpset() addsimps [Forall_def, sforall_def,
                                 Consq_def,flift2_def]) 1);
qed"Forall_cons";

(* ---------------------------------------------------------------- *)
(*                               Conc                               *)
(* ---------------------------------------------------------------- *)


Goal "(x>>xs) @@ y = x>>(xs @@y)"; 
by (simp_tac (simpset() addsimps [Consq_def]) 1);
qed"Conc_cons";

(* ---------------------------------------------------------------- *)
(*                               Takewhile                          *)
(* ---------------------------------------------------------------- *)

Goal "Takewhile P$UU =UU";
by (simp_tac (simpset() addsimps [Takewhile_def]) 1);
qed"Takewhile_UU";

Goal "Takewhile P$nil =nil";
by (simp_tac (simpset() addsimps [Takewhile_def]) 1);
qed"Takewhile_nil";

Goal "Takewhile P$(x>>xs)= (if P x then x>>(Takewhile P$xs) else nil)"; 
by (simp_tac (simpset() addsimps [Takewhile_def, Consq_def,flift2_def,If_and_if]) 1);
qed"Takewhile_cons";

(* ---------------------------------------------------------------- *)
(*                               Dropwhile                          *)
(* ---------------------------------------------------------------- *)

Goal "Dropwhile P$UU =UU";
by (simp_tac (simpset() addsimps [Dropwhile_def]) 1);
qed"Dropwhile_UU";

Goal "Dropwhile P$nil =nil";
by (simp_tac (simpset() addsimps [Dropwhile_def]) 1);
qed"Dropwhile_nil";

Goal "Dropwhile P$(x>>xs)= (if P x then Dropwhile P$xs else x>>xs)"; 
by (simp_tac (simpset() addsimps [Dropwhile_def, Consq_def,flift2_def,If_and_if]) 1);
qed"Dropwhile_cons";

(* ---------------------------------------------------------------- *)
(*                               Last                               *)
(* ---------------------------------------------------------------- *)


Goal "Last$UU =UU";
by (simp_tac (simpset() addsimps [Last_def]) 1);
qed"Last_UU";

Goal "Last$nil =UU";
by (simp_tac (simpset() addsimps [Last_def]) 1);
qed"Last_nil";

Goal "Last$(x>>xs)= (if xs=nil then Def x else Last$xs)"; 
by (simp_tac (simpset() addsimps [Last_def, Consq_def]) 1);
by (res_inst_tac [("x","xs")] seq.casedist 1);
by (Asm_simp_tac 1);
by (REPEAT (Asm_simp_tac 1));
qed"Last_cons";


(* ---------------------------------------------------------------- *)
(*                               Flat                               *)
(* ---------------------------------------------------------------- *)

Goal "Flat$UU =UU";
by (simp_tac (simpset() addsimps [Flat_def]) 1);
qed"Flat_UU";

Goal "Flat$nil =nil";
by (simp_tac (simpset() addsimps [Flat_def]) 1);
qed"Flat_nil";

Goal "Flat$(x##xs)= x @@ (Flat$xs)"; 
by (simp_tac (simpset() addsimps [Flat_def, Consq_def]) 1);
qed"Flat_cons";


(* ---------------------------------------------------------------- *)
(*                               Zip                                *)
(* ---------------------------------------------------------------- *)

Goal "Zip = (LAM t1 t2. case t1 of \
\               nil   => nil \
\             | x##xs => (case t2 of \ 
\                          nil => UU  \
\                        | y##ys => (case x of \
\                                      Undef  => UU \
\                                    | Def a => (case y of \
\                                                  Undef => UU \
\                                                | Def b => Def (a,b)##(Zip$xs$ys)))))";
by (rtac trans 1);
by (rtac fix_eq2 1);
by (rtac Zip_def 1);
by (rtac beta_cfun 1);
by (Simp_tac 1);
qed"Zip_unfold";

Goal "Zip$UU$y =UU";
by (stac Zip_unfold 1);
by (Simp_tac 1);
qed"Zip_UU1";

Goal "x~=nil ==> Zip$x$UU =UU";
by (stac Zip_unfold 1);
by (Simp_tac 1);
by (res_inst_tac [("x","x")] seq.casedist 1);
by (REPEAT (Asm_full_simp_tac 1));
qed"Zip_UU2";

Goal "Zip$nil$y =nil";
by (stac Zip_unfold 1);
by (Simp_tac 1);
qed"Zip_nil";

Goal "Zip$(x>>xs)$nil= UU"; 
by (stac Zip_unfold 1);
by (simp_tac (simpset() addsimps [Consq_def]) 1);
qed"Zip_cons_nil";

Goal "Zip$(x>>xs)$(y>>ys)= (x,y) >> Zip$xs$ys"; 
by (rtac trans 1);
by (stac Zip_unfold 1);
by (Simp_tac 1);
by (simp_tac (simpset() addsimps [Consq_def]) 1);
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
          Conc_cons,
          Takewhile_UU, Takewhile_nil, Takewhile_cons, 
          Dropwhile_UU, Dropwhile_nil, Dropwhile_cons,
          Zip_UU1,Zip_UU2,Zip_nil,Zip_cons_nil,Zip_cons];



(* ------------------------------------------------------------------------------------- *)


section "Cons";

Goal "a>>s = (Def a)##s";
by (simp_tac (simpset() addsimps [Consq_def]) 1);
qed"Consq_def2";

Goal "x = UU | x = nil | (? a s. x = a >> s)";
by (simp_tac (simpset() addsimps [Consq_def2]) 1);
by (cut_facts_tac [seq.exhaust] 1);
by (fast_tac (HOL_cs addDs [not_Undef_is_Def RS iffD1]) 1);
qed"Seq_exhaust";


Goal "!!P. [| x = UU ==> P; x = nil ==> P; !!a s. x = a >> s  ==> P |] ==> P";
by (cut_inst_tac [("x","x")] Seq_exhaust 1);
by (etac disjE 1);
by (Asm_full_simp_tac 1);
by (etac disjE 1);
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

Goal "a>>s ~= UU";
by (stac Consq_def2 1);
by (resolve_tac seq.con_rews 1);
by (rtac Def_not_UU 1);
qed"Cons_not_UU";


Goal "~(a>>x) << UU";
by (rtac notI 1);
by (dtac antisym_less 1);
by (Simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [Cons_not_UU]) 1);
qed"Cons_not_less_UU";

Goal "~a>>s << nil";
by (stac Consq_def2 1);
by (resolve_tac seq.rews 1);
by (rtac Def_not_UU 1);
qed"Cons_not_less_nil";

Goal "a>>s ~= nil";
by (stac Consq_def2 1);
by (resolve_tac seq.rews 1);
qed"Cons_not_nil";

Goal "nil ~= a>>s";
by (simp_tac (simpset() addsimps [Consq_def2]) 1);
qed"Cons_not_nil2";

Goal "(a>>s = b>>t) = (a = b & s = t)";
by (simp_tac (HOL_ss addsimps [Consq_def2]) 1);
by (stac (hd lift.inject RS sym) 1);
back(); back();
by (rtac scons_inject_eq 1);
by (REPEAT(rtac Def_not_UU 1));
qed"Cons_inject_eq";

Goal "(a>>s<<b>>t) = (a = b & s<<t)";
by (simp_tac (simpset() addsimps [Consq_def2]) 1);
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

Goal "seq_take (Suc n)$(a>>x) = a>> (seq_take n$x)";
by (simp_tac (simpset() addsimps [Consq_def]) 1);
qed"seq_take_Cons";

Addsimps [Cons_not_nil2,Cons_inject_eq,Cons_inject_less_eq,seq_take_Cons,
          Cons_not_UU,Cons_not_less_UU,Cons_not_less_nil,Cons_not_nil];

(* Instead of adding UU_neq_Cons every equation UU~=x could be changed to x~=UU *)
Goal "UU ~= x>>xs";
by (res_inst_tac [("s1","UU"),("t1","x>>xs")]  (sym RS rev_contrapos) 1);
by (REPEAT (Simp_tac 1));
qed"UU_neq_Cons";

Addsimps [UU_neq_Cons];


(* ----------------------------------------------------------------------------------- *)

section "induction";

Goal "!! P. [| adm P; P UU; P nil; !! a s. P s ==> P (a>>s)|] ==> P x";
by (etac seq.ind 1);
by (REPEAT (atac 1));
by (def_tac 1);
by (asm_full_simp_tac (simpset() addsimps [Consq_def]) 1);
qed"Seq_induct";

Goal "!! P.[|P UU;P nil; !! a s. P s ==> P(a>>s) |]  \
\               ==> seq_finite x --> P x";
by (etac seq_finite_ind 1);
by (REPEAT (atac 1));
by (def_tac 1);
by (asm_full_simp_tac (simpset() addsimps [Consq_def]) 1);
qed"Seq_FinitePartial_ind";

Goal "!! P.[| Finite x; P nil; !! a s. [| Finite s; P s|] ==> P (a>>s) |] ==> P x";
by (etac sfinite.induct 1);
by (assume_tac 1);
by (def_tac 1);
by (asm_full_simp_tac (simpset() addsimps [Consq_def]) 1);
qed"Seq_Finite_ind"; 


(* rws are definitions to be unfolded for admissibility check *)
fun Seq_induct_tac s rws i = res_inst_tac [("x",s)] Seq_induct i
                         THEN (REPEAT_DETERM (CHANGED (Asm_simp_tac (i+1))))
                         THEN simp_tac (simpset() addsimps rws) i;

fun Seq_Finite_induct_tac i = etac Seq_Finite_ind i
                              THEN (REPEAT_DETERM (CHANGED (Asm_simp_tac i)));

fun pair_tac s = res_inst_tac [("p",s)] PairE
			  THEN' hyp_subst_tac THEN' Asm_full_simp_tac;

(* induction on a sequence of pairs with pairsplitting and simplification *)
fun pair_induct_tac s rws i = 
           res_inst_tac [("x",s)] Seq_induct i 
           THEN pair_tac "a" (i+3) 
           THEN (REPEAT_DETERM (CHANGED (Simp_tac (i+1)))) 
           THEN simp_tac (simpset() addsimps rws) i;



(* ------------------------------------------------------------------------------------ *)

section "HD,TL";

Goal "HD$(x>>y) = Def x";
by (simp_tac (simpset() addsimps [Consq_def]) 1);
qed"HD_Cons";

Goal "TL$(x>>y) = y";
by (simp_tac (simpset() addsimps [Consq_def]) 1);
qed"TL_Cons";

Addsimps [HD_Cons,TL_Cons];

(* ------------------------------------------------------------------------------------ *)

section "Finite, Partial, Infinite";

Goal "Finite (a>>xs) = Finite xs";
by (simp_tac (simpset() addsimps [Consq_def2,Finite_cons]) 1);
qed"Finite_Cons";

Addsimps [Finite_Cons];
Goal "Finite (x::'a Seq) ==> Finite y --> Finite (x@@y)";
by (Seq_Finite_induct_tac 1);
qed"FiniteConc_1";

Goal "Finite (z::'a Seq) ==> !x y. z= x@@y --> (Finite x & Finite y)";
by (Seq_Finite_induct_tac 1);
(* nil*)
by (strip_tac 1);
by (Seq_case_simp_tac "x" 1);
by (Asm_full_simp_tac 1);
(* cons *)
by (strip_tac 1);
by (Seq_case_simp_tac "x" 1);
by (Seq_case_simp_tac "y" 1);
by (SELECT_GOAL (auto_tac (claset(),simpset()))1);
by (eres_inst_tac [("x","sa")] allE 1);
by (eres_inst_tac [("x","y")] allE 1);
by (Asm_full_simp_tac 1);
qed"FiniteConc_2";

Goal "Finite(x@@y) = (Finite (x::'a Seq) & Finite y)";
by (rtac iffI 1);
by (etac (FiniteConc_2 RS spec RS spec RS mp) 1);
by (rtac refl 1);
by (rtac (FiniteConc_1 RS mp) 1);
by Auto_tac;
qed"FiniteConc";

Addsimps [FiniteConc];


Goal "Finite s ==> Finite (Map f$s)";
by (Seq_Finite_induct_tac 1);
qed"FiniteMap1";

Goal "Finite s ==> ! t. (s = Map f$t) --> Finite t";
by (Seq_Finite_induct_tac 1);
by (strip_tac 1);
by (Seq_case_simp_tac "t" 1);
by (Asm_full_simp_tac 1);
(* main case *)
by Auto_tac;
by (Seq_case_simp_tac "t" 1);
by (Asm_full_simp_tac 1);
qed"FiniteMap2";

Goal "Finite (Map f$s) = Finite s";
by Auto_tac;
by (etac (FiniteMap2 RS spec RS mp) 1);
by (rtac refl 1);
by (etac FiniteMap1 1);
qed"Map2Finite";


Goal "Finite s ==> Finite (Filter P$s)";
by (Seq_Finite_induct_tac 1);
qed"FiniteFilter";


(* ----------------------------------------------------------------------------------- *)


section "admissibility";

(* Finite x is proven to be adm: Finite_flat shows that there are only chains of length one.
   Then the assumption that an _infinite_ chain exists (from admI2) is set to a contradiction 
   to Finite_flat *)

Goal "!! (x:: 'a Seq). Finite x ==> !y. Finite (y:: 'a Seq) & x<<y --> x=y";
by (Seq_Finite_induct_tac 1);
by (strip_tac 1);
by (etac conjE 1);
by (etac nil_less_is_nil 1);
(* main case *)
by Auto_tac;
by (Seq_case_simp_tac "y" 1);
by Auto_tac;
qed_spec_mp"Finite_flat";


Goal "adm(%(x:: 'a Seq).Finite x)";
by (rtac admI2 1);
by (eres_inst_tac [("x","0")] allE 1);
back();
by (etac exE 1);
by (REPEAT (etac conjE 1));
by (res_inst_tac [("x","0")] allE 1);
by (assume_tac 1);
by (eres_inst_tac [("x","j")] allE 1);
by (cut_inst_tac [("x","Y 0"),("y","Y j")] Finite_flat 1);
(* Generates a contradiction in subgoal 3 *)
by Auto_tac;
qed"adm_Finite";

Addsimps [adm_Finite];


(* ------------------------------------------------------------------------------------ *)

section "Conc";

Goal "!! x::'a Seq. Finite x ==> ((x @@ y) = (x @@ z)) = (y = z)";
by (Seq_Finite_induct_tac 1);
qed"Conc_cong";

Goal "(x @@ y) @@ z = (x::'a Seq) @@ y @@ z";
by (Seq_induct_tac "x" [] 1);
qed"Conc_assoc";

Goal "s@@ nil = s";
by (res_inst_tac[("x","s")] seq.ind 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (Asm_full_simp_tac 1);
qed"nilConc";

Addsimps [nilConc];

(* should be same as nil_is_Conc2 when all nils are turned to right side !! *)
Goal "(nil = x @@ y) = ((x::'a Seq)= nil & y = nil)";
by (Seq_case_simp_tac "x" 1);
by Auto_tac;
qed"nil_is_Conc";

Goal "(x @@ y = nil) = ((x::'a Seq)= nil & y = nil)";
by (Seq_case_simp_tac "x" 1);
by Auto_tac;
qed"nil_is_Conc2";


(* ------------------------------------------------------------------------------------ *)

section "Last";

Goal "Finite s ==> s~=nil --> Last$s~=UU";
by (Seq_Finite_induct_tac  1);
qed"Finite_Last1";

Goal "Finite s ==> Last$s=UU --> s=nil";
by (Seq_Finite_induct_tac  1);
by (fast_tac HOL_cs 1);
qed"Finite_Last2";


(* ------------------------------------------------------------------------------------ *)


section "Filter, Conc";


Goal "Filter P$(Filter Q$s) = Filter (%x. P x & Q x)$s";
by (Seq_induct_tac "s" [Filter_def] 1);
qed"FilterPQ";

Goal "Filter P$(x @@ y) = (Filter P$x @@ Filter P$y)";
by (simp_tac (simpset() addsimps [Filter_def,sfiltersconc]) 1);
qed"FilterConc";

(* ------------------------------------------------------------------------------------ *)

section "Map";

Goal "Map f$(Map g$s) = Map (f o g)$s";
by (Seq_induct_tac "s" [] 1);
qed"MapMap";

Goal "Map f$(x@@y) = (Map f$x) @@ (Map f$y)";
by (Seq_induct_tac "x" [] 1);
qed"MapConc";

Goal "Filter P$(Map f$x) = Map f$(Filter (P o f)$x)";
by (Seq_induct_tac "x" [] 1);
qed"MapFilter";

Goal "nil = (Map f$s) --> s= nil";
by (Seq_case_simp_tac "s" 1);
qed"nilMap";


Goal "Forall P (Map f$s) = Forall (P o f) s";
by (Seq_induct_tac "s" [Forall_def,sforall_def] 1);
qed"ForallMap";




(* ------------------------------------------------------------------------------------ *)

section "Forall";


Goal "Forall P ys & (! x. P x --> Q x) \
\         --> Forall Q ys";
by (Seq_induct_tac "ys" [Forall_def,sforall_def] 1);
qed"ForallPForallQ1";

bind_thm ("ForallPForallQ",impI RSN (2,allI RSN (2,conjI RS (ForallPForallQ1 RS mp))));

Goal "(Forall P x & Forall P y) --> Forall P (x @@ y)";
by (Seq_induct_tac "x" [Forall_def,sforall_def] 1);
qed"Forall_Conc_impl";

Goal "Finite x ==> Forall P (x @@ y) = (Forall P x & Forall P y)";
by (Seq_Finite_induct_tac  1);
qed"Forall_Conc";

Addsimps [Forall_Conc];

Goal "Forall P s  --> Forall P (TL$s)";
by (Seq_induct_tac "s" [Forall_def,sforall_def] 1);
qed"ForallTL1";

bind_thm ("ForallTL",ForallTL1 RS mp);

Goal "Forall P s  --> Forall P (Dropwhile Q$s)";
by (Seq_induct_tac "s" [Forall_def,sforall_def] 1);
qed"ForallDropwhile1";

bind_thm ("ForallDropwhile",ForallDropwhile1 RS mp);


(* only admissible in t, not if done in s *)

Goal "! s. Forall P s --> t<<s --> Forall P t";
by (Seq_induct_tac "t" [Forall_def,sforall_def] 1);
by (strip_tac 1); 
by (Seq_case_simp_tac "sa" 1);
by (Asm_full_simp_tac 1);
by Auto_tac;
qed"Forall_prefix";

bind_thm ("Forall_prefixclosed",Forall_prefix RS spec RS mp RS mp);


Goal "[| Finite h; Forall P s; s= h @@ t |] ==> Forall P t";
by Auto_tac;
qed"Forall_postfixclosed";


Goal "((! x. P x --> (Q x = R x)) & Forall P tr) --> Filter Q$tr = Filter R$tr";
by (Seq_induct_tac "tr" [Forall_def,sforall_def] 1);
qed"ForallPFilterQR1";

bind_thm("ForallPFilterQR",allI RS (conjI RS (ForallPFilterQR1 RS mp)));


(* ------------------------------------------------------------------------------------- *)

section "Forall, Filter";


Goal "Forall P (Filter P$x)";
by (simp_tac (simpset() addsimps [Filter_def,Forall_def,forallPsfilterP]) 1);
qed"ForallPFilterP";

(* holds also in other direction, then equal to forallPfilterP *)
Goal "Forall P x --> Filter P$x = x";
by (Seq_induct_tac "x" [Forall_def,sforall_def,Filter_def] 1);
qed"ForallPFilterPid1";

bind_thm("ForallPFilterPid",ForallPFilterPid1 RS mp);


(* holds also in other direction *)
Goal "!! ys . Finite ys ==> \
\   Forall (%x. ~P x) ys --> Filter P$ys = nil ";
by (Seq_Finite_induct_tac 1);
qed"ForallnPFilterPnil1";

bind_thm ("ForallnPFilterPnil",ForallnPFilterPnil1 RS mp);


(* holds also in other direction *)
Goal   "~Finite ys & Forall (%x. ~P x) ys \
\                  --> Filter P$ys = UU ";
by (Seq_induct_tac "ys" [Forall_def,sforall_def] 1);
qed"ForallnPFilterPUU1";

bind_thm ("ForallnPFilterPUU",conjI RS (ForallnPFilterPUU1 RS mp));


(* inverse of ForallnPFilterPnil *)

Goal "!! ys . Filter P$ys = nil --> \
\   (Forall (%x. ~P x) ys & Finite ys)";
by (res_inst_tac[("x","ys")] Seq_induct 1);
(* adm *)
(* FIX: not admissible, search other proof!! *)
by (rtac adm_all 1);
(* base cases *)
by (Simp_tac 1);
by (Simp_tac 1);
(* main case *)
by (Asm_full_simp_tac 1);
qed"FilternPnilForallP1";

bind_thm ("FilternPnilForallP",FilternPnilForallP1 RS mp);

(* inverse of ForallnPFilterPUU. proved by 2 lemmas because of adm problems *)

Goal "Finite ys ==> Filter P$ys ~= UU";
by (Seq_Finite_induct_tac 1);
qed"FilterUU_nFinite_lemma1";

Goal "~ Forall (%x. ~P x) ys --> Filter P$ys ~= UU";
by (Seq_induct_tac "ys" [Forall_def,sforall_def] 1);
qed"FilterUU_nFinite_lemma2";

Goal   "Filter P$ys = UU ==> \
\                (Forall (%x. ~P x) ys  & ~Finite ys)";
by (rtac conjI 1);
by (cut_inst_tac [] (FilterUU_nFinite_lemma2 RS mp COMP rev_contrapos) 1);
by Auto_tac;
by (blast_tac (claset() addSDs [FilterUU_nFinite_lemma1]) 1);
qed"FilternPUUForallP";


Goal  "!! Q P.[| Forall Q ys; Finite ys; !!x. Q x ==> ~P x|] \
\   ==> Filter P$ys = nil";
by (etac ForallnPFilterPnil 1);
by (etac ForallPForallQ 1);
by Auto_tac;
qed"ForallQFilterPnil";

Goal "!! Q P. [| ~Finite ys; Forall Q ys;  !!x. Q x ==> ~P x|] \
\   ==> Filter P$ys = UU ";
by (etac ForallnPFilterPUU 1);
by (etac ForallPForallQ 1);
by Auto_tac;
qed"ForallQFilterPUU";



(* ------------------------------------------------------------------------------------- *)

section "Takewhile, Forall, Filter";


Goal "Forall P (Takewhile P$x)";
by (simp_tac (simpset() addsimps [Forall_def,Takewhile_def,sforallPstakewhileP]) 1);
qed"ForallPTakewhileP";


Goal"!! P. [| !!x. Q x==> P x |] ==> Forall P (Takewhile Q$x)";
by (rtac ForallPForallQ 1);
by (rtac ForallPTakewhileP 1);
by Auto_tac;
qed"ForallPTakewhileQ";


Goal  "!! Q P.[| Finite (Takewhile Q$ys); !!x. Q x ==> ~P x |] \
\   ==> Filter P$(Takewhile Q$ys) = nil";
by (etac ForallnPFilterPnil 1);
by (rtac ForallPForallQ 1);
by (rtac ForallPTakewhileP 1);
by Auto_tac;
qed"FilterPTakewhileQnil";

Goal "!! Q P. [| !!x. Q x ==> P x |] ==> \
\            Filter P$(Takewhile Q$ys) = (Takewhile Q$ys)";
by (rtac ForallPFilterPid 1);
by (rtac ForallPForallQ 1);
by (rtac ForallPTakewhileP 1);
by Auto_tac;
qed"FilterPTakewhileQid";

Addsimps [ForallPTakewhileP,ForallPTakewhileQ,
          FilterPTakewhileQnil,FilterPTakewhileQid];

Goal "Takewhile P$(Takewhile P$s) = Takewhile P$s";
by (Seq_induct_tac "s" [Forall_def,sforall_def] 1);
qed"Takewhile_idempotent";

Goal "Forall P s --> Takewhile (%x. Q x | (~P x))$s = Takewhile Q$s";
by (Seq_induct_tac "s" [Forall_def,sforall_def] 1);
qed"ForallPTakewhileQnP";

Goal "Forall P s --> Dropwhile (%x. Q x | (~P x))$s = Dropwhile Q$s";
by (Seq_induct_tac "s" [Forall_def,sforall_def] 1);
qed"ForallPDropwhileQnP";

Addsimps [ForallPTakewhileQnP RS mp, ForallPDropwhileQnP RS mp];


Goal "Forall P s --> Takewhile P$(s @@ t) = s @@ (Takewhile P$t)";
by (Seq_induct_tac "s" [Forall_def,sforall_def] 1);
qed"TakewhileConc1";

bind_thm("TakewhileConc",TakewhileConc1 RS mp);

Goal "Finite s ==> Forall P s --> Dropwhile P$(s @@ t) = Dropwhile P$t";
by (Seq_Finite_induct_tac 1);
qed"DropwhileConc1";

bind_thm("DropwhileConc",DropwhileConc1 RS mp);



(* ----------------------------------------------------------------------------------- *)

section "coinductive characterizations of Filter";


Goal "HD$(Filter P$y) = Def x \
\         --> y = ((Takewhile (%x. ~P x)$y) @@ (x >> TL$(Dropwhile (%a.~P a)$y)))  \
\             & Finite (Takewhile (%x. ~ P x)$y)  & P x";

(* FIX: pay attention: is only admissible with chain-finite package to be added to 
        adm test and Finite f x admissibility *)
by (Seq_induct_tac "y" [] 1);
by (rtac adm_all 1);
by (Asm_full_simp_tac 1); 
by (case_tac "P a" 1);
 by (Asm_full_simp_tac 1); 
 by (Blast_tac 1);
(* ~ P a *)
by (Asm_full_simp_tac 1); 
qed"divide_Seq_lemma";

Goal "(x>>xs) << Filter P$y  \
\   ==> y = ((Takewhile (%a. ~ P a)$y) @@ (x >> TL$(Dropwhile (%a.~P a)$y))) \
\      & Finite (Takewhile (%a. ~ P a)$y)  & P x";
by (rtac (divide_Seq_lemma RS mp) 1);
by (dres_inst_tac [("fo","HD"),("xa","x>>xs")]  monofun_cfun_arg 1);
by (Asm_full_simp_tac 1); 
qed"divide_Seq";

 
Goal "~Forall P y --> (? x. HD$(Filter (%a. ~P a)$y) = Def x)";
(* Pay attention: is only admissible with chain-finite package to be added to 
        adm test *)
by (Seq_induct_tac "y" [Forall_def,sforall_def] 1);
qed"nForall_HDFilter";


Goal "~Forall P y  \
\  ==> ? x. y= (Takewhile P$y @@ (x >> TL$(Dropwhile P$y))) & \
\      Finite (Takewhile P$y) & (~ P x)";
by (dtac (nForall_HDFilter RS mp) 1);
by (safe_tac set_cs);
by (res_inst_tac [("x","x")] exI 1);
by (cut_inst_tac [("P1","%x. ~ P x")] (divide_Seq_lemma RS mp) 1);
by Auto_tac;
qed"divide_Seq2";


Goal  "~Forall P y \
\  ==> ? x bs rs. y= (bs @@ (x>>rs)) & Finite bs & Forall P bs & (~ P x)";
by (cut_inst_tac [] divide_Seq2 1);
(*Auto_tac no longer proves it*)
by (REPEAT (fast_tac (claset() addss (simpset())) 1));
qed"divide_Seq3";

Addsimps [FilterPQ,FilterConc,Conc_cong];


(* ------------------------------------------------------------------------------------- *)


section "take_lemma";

Goal "(!n. seq_take n$x = seq_take n$x') = (x = x')";
by (rtac iffI 1);
by (resolve_tac seq.take_lemmas 1);
by Auto_tac;
qed"seq_take_lemma";

Goal 
"  ! n. ((! k. k < n --> seq_take k$y1 = seq_take k$y2) \
\   --> seq_take n$(x @@ (t>>y1)) =  seq_take n$(x @@ (t>>y2)))";
by (Seq_induct_tac "x" [] 1);
by (strip_tac 1);
by (case_tac "n" 1);
by Auto_tac;
by (case_tac "n" 1);
by Auto_tac;
qed"take_reduction1";


Goal "!! n.[| x=y; s=t; !! k. k<n ==> seq_take k$y1 = seq_take k$y2|] \
\ ==> seq_take n$(x @@ (s>>y1)) =  seq_take n$(y @@ (t>>y2))";

by (auto_tac (claset() addSIs [take_reduction1 RS spec RS mp],simpset()));
qed"take_reduction";

(* ------------------------------------------------------------------
          take-lemma and take_reduction for << instead of = 
   ------------------------------------------------------------------ *)

Goal 
"  ! n. ((! k. k < n --> seq_take k$y1 << seq_take k$y2) \
\   --> seq_take n$(x @@ (t>>y1)) <<  seq_take n$(x @@ (t>>y2)))";
by (Seq_induct_tac "x" [] 1);
by (strip_tac 1);
by (case_tac "n" 1);
by Auto_tac;
by (case_tac "n" 1);
by Auto_tac;
qed"take_reduction_less1";


Goal "!! n.[| x=y; s=t;!! k. k<n ==> seq_take k$y1 << seq_take k$y2|] \
\ ==> seq_take n$(x @@ (s>>y1)) <<  seq_take n$(y @@ (t>>y2))";
by (auto_tac (claset() addSIs [take_reduction_less1 RS spec RS mp],simpset()));
qed"take_reduction_less";


val prems = goalw thy [seq.take_def]
"(!! n. seq_take n$s1 << seq_take n$s2)  ==> s1<<s2";

by (res_inst_tac [("t","s1")] (seq.reach RS subst)  1);
by (res_inst_tac [("t","s2")] (seq.reach RS subst)  1);
by (rtac (fix_def2 RS ssubst ) 1);
by (stac contlub_cfun_fun 1);
by (rtac chain_iterate 1);
by (stac contlub_cfun_fun 1);
by (rtac chain_iterate 1);
by (rtac lub_mono 1);
by (rtac (chain_iterate RS ch2ch_Rep_CFunL) 1);
by (rtac (chain_iterate RS ch2ch_Rep_CFunL) 1);
by (rtac allI 1);
by (resolve_tac prems 1);
qed"take_lemma_less1";


Goal "(!n. seq_take n$x << seq_take n$x') = (x << x')";
by (rtac iffI 1);
by (rtac take_lemma_less1 1);
by Auto_tac;
by (etac monofun_cfun_arg 1);
qed"take_lemma_less";

(* ------------------------------------------------------------------
          take-lemma proof principles
   ------------------------------------------------------------------ *)

Goal "!! Q. [|!! s. [| Forall Q s; A s |] ==> (f s) = (g s) ; \
\           !! s1 s2 y. [| Forall Q s1; Finite s1; ~ Q y; A (s1 @@ y>>s2)|] \
\                         ==> (f (s1 @@ y>>s2)) = (g (s1 @@ y>>s2)) |] \
\              ==> A x --> (f x)=(g x)";
by (case_tac "Forall Q x" 1);
by (auto_tac (claset() addSDs [divide_Seq3],simpset()));
qed"take_lemma_principle1";

Goal "!! Q. [|!! s. [| Forall Q s; A s |] ==> (f s) = (g s) ; \
\           !! s1 s2 y. [| Forall Q s1; Finite s1; ~ Q y; A (s1 @@ y>>s2)|] \
\                         ==> ! n. seq_take n$(f (s1 @@ y>>s2)) \
\                                = seq_take n$(g (s1 @@ y>>s2)) |] \
\              ==> A x --> (f x)=(g x)";
by (case_tac "Forall Q x" 1);
by (auto_tac (claset() addSDs [divide_Seq3],simpset()));
by (resolve_tac seq.take_lemmas 1);
by Auto_tac;
qed"take_lemma_principle2";


(* Note: in the following proofs the ordering of proof steps is very 
         important, as otherwise either (Forall Q s1) would be in the IH as
         assumption (then rule useless) or it is not possible to strengthen 
         the IH by doing a forall closure of the sequence t (then rule also useless).
         This is also the reason why the induction rule (nat_less_induct or nat_induct) has to 
         to be imbuilt into the rule, as induction has to be done early and the take lemma 
         has to be used in the trivial direction afterwards for the (Forall Q x) case.  *)

Goal 
"!! Q. [|!! s. [| Forall Q s; A s |] ==> (f s) = (g s) ; \
\        !! s1 s2 y n. [| ! t. A t --> seq_take n$(f t) = seq_take n$(g t);\
\                         Forall Q s1; Finite s1; ~ Q y; A (s1 @@ y>>s2) |] \
\                         ==>   seq_take (Suc n)$(f (s1 @@ y>>s2)) \
\                             = seq_take (Suc n)$(g (s1 @@ y>>s2)) |] \
\              ==> A x --> (f x)=(g x)";
by (rtac impI 1);
by (resolve_tac seq.take_lemmas 1);
by (rtac mp 1);
by (assume_tac 2);
by (res_inst_tac [("x","x")] spec 1);
by (rtac nat_induct 1);
by (Simp_tac 1);
by (rtac allI 1);
by (case_tac "Forall Q xa" 1);
by (SELECT_GOAL (auto_tac (claset() addSIs [seq_take_lemma RS iffD2 RS spec],
                           simpset())) 1);
by (auto_tac (claset() addSDs [divide_Seq3],simpset()));
qed"take_lemma_induct";


Goal 
"!! Q. [|!! s. [| Forall Q s; A s |] ==> (f s) = (g s) ; \
\        !! s1 s2 y n. [| ! t m. m < n --> A t --> seq_take m$(f t) = seq_take m$(g t);\
\                         Forall Q s1; Finite s1; ~ Q y; A (s1 @@ y>>s2) |] \
\                         ==>   seq_take n$(f (s1 @@ y>>s2)) \
\                             = seq_take n$(g (s1 @@ y>>s2)) |] \
\              ==> A x --> (f x)=(g x)";
by (rtac impI 1);
by (resolve_tac seq.take_lemmas 1);
by (rtac mp 1);
by (assume_tac 2);
by (res_inst_tac [("x","x")] spec 1);
by (rtac nat_less_induct 1);
by (rtac allI 1);
by (case_tac "Forall Q xa" 1);
by (SELECT_GOAL (auto_tac (claset() addSIs [seq_take_lemma RS iffD2 RS spec],
                           simpset())) 1);
by (auto_tac (claset() addSDs [divide_Seq3],simpset()));
qed"take_lemma_less_induct";


(*
local

fun qnt_tac i (tac, var) = tac THEN res_inst_tac [("x", var)] spec i;

fun add_frees tsig =
  let
    fun add (Free (x, T), vars) =
          if Type.of_sort tsig (T, HOLogic.termS) then x ins vars
          else vars
      | add (Abs (_, _, t), vars) = add (t, vars)
      | add (t $ u, vars) = add (t, add (u, vars))
      | add (_, vars) = vars;
   in add end;


in

(*Generalizes over all free variables, with the named var outermost.*)
fun all_frees_tac x i thm =
  let
    val tsig = #tsig (Sign.rep_sg (#sign (rep_thm thm)));
    val frees = add_frees tsig (nth_elem (i - 1, prems_of thm), [x]);
    val frees' = sort (op >) (frees \ x) @ [x];
  in
    foldl (qnt_tac i) (all_tac, frees') thm
  end;

end;


Goal 
"!! Q. [|!! s h1 h2. [| Forall Q s; A s h1 h2|] ==> (f s h1 h2) = (g s h1 h2) ; \
\  !! s1 s2 y n. [| ! t h1 h2 m. m < n --> (A t h1 h2) --> seq_take m$(f t h1 h2) = seq_take m$(g t h1 h2);\
\                         Forall Q s1; Finite s1; ~ Q y; A (s1 @@ y>>s2) h1 h2|] \
\                         ==>   seq_take n$(f (s1 @@ y>>s2) h1 h2) \
\                             = seq_take n$(g (s1 @@ y>>s2) h1 h2) |] \
\              ==> ! h1 h2. (A x h1 h2) --> (f x h1 h2)=(g x h1 h2)";
by (strip_tac 1);
by (resolve_tac seq.take_lemmas 1);
by (rtac mp 1);
by (assume_tac 2);
by (res_inst_tac [("x","h2a")] spec 1);
by (res_inst_tac [("x","h1a")] spec 1);
by (res_inst_tac [("x","x")] spec 1);
by (rtac nat_less_induct 1);
by (rtac allI 1);
by (case_tac "Forall Q xa" 1);
by (SELECT_GOAL (auto_tac (claset() addSIs [seq_take_lemma RS iffD2 RS spec],
                           simpset())) 1);
by (auto_tac (claset() addSDs [divide_Seq3],simpset()));
qed"take_lemma_less_induct";



Goal 
"!! Q. [|!! s. Forall Q s ==> P ((f s) = (g s)) ; \
\        !! s1 s2 y n. [| ! t m. m < n --> P (seq_take m$(f t) = seq_take m$(g t));\
\                         Forall Q s1; Finite s1; ~ Q y|] \
\                         ==>   P (seq_take n$(f (s1 @@ y>>s2)) \
\                                   = seq_take n$(g (s1 @@ y>>s2))) |] \
\              ==> P ((f x)=(g x))";

by (res_inst_tac [("t","f x = g x"),
                  ("s","!n. seq_take n$(f x) = seq_take n$(g x)")] subst 1);
by (rtac seq_take_lemma 1);

wie ziehe ich n durch P, d.h. evtl. ns in P muessen umbenannt werden.....


FIX

by (rtac nat_less_induct 1);
by (rtac allI 1);
by (case_tac "Forall Q xa" 1);
by (SELECT_GOAL (auto_tac (claset() addSIs [seq_take_lemma RS iffD2 RS spec],
                           simpset())) 1);
by (auto_tac (claset() addSDs [divide_Seq3],simpset()));
qed"take_lemma_less_induct";


*)


Goal 
"!! Q. [| A UU  ==> (f UU) = (g UU) ; \
\         A nil ==> (f nil) = (g nil) ; \
\         !! s y n. [| ! t. A t --> seq_take n$(f t) = seq_take n$(g t);\
\                    A (y>>s) |]   \
\                    ==>   seq_take (Suc n)$(f (y>>s)) \
\                        = seq_take (Suc n)$(g (y>>s)) |] \
\              ==> A x --> (f x)=(g x)";
by (rtac impI 1);
by (resolve_tac seq.take_lemmas 1);
by (rtac mp 1);
by (assume_tac 2);
by (res_inst_tac [("x","x")] spec 1);
by (rtac nat_induct 1);
by (Simp_tac 1);
by (rtac allI 1);
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
Goal "Forall (%x.~(P x & Q x)) s \
\         --> Filter P$(Filter Q$s) =\
\             Filter (%x. P x & Q x)$s";

by (Seq_induct_tac "s" [Forall_def,sforall_def] 1);
qed"Filter_lemma1";

Goal "Finite s ==>  \
\         (Forall (%x. (~P x) | (~ Q x)) s  \
\         --> Filter P$(Filter Q$s) = nil)";
by (Seq_Finite_induct_tac 1);
qed"Filter_lemma2";

Goal "Finite s ==>  \
\         Forall (%x. (~P x) | (~ Q x)) s  \
\         --> Filter (%x. P x & Q x)$s = nil";
by (Seq_Finite_induct_tac 1);
qed"Filter_lemma3";


Goal "Filter P$(Filter Q$s) = Filter (%x. P x & Q x)$s";
by (res_inst_tac [("A1","%x. True") 
                 ,("Q1","%x.~(P x & Q x)"),("x1","s")]
                 (take_lemma_induct RS mp) 1);
(* better support for A = %x. True *)
by (Fast_tac 3);
by (asm_full_simp_tac (simpset() addsimps [Filter_lemma1]) 1);
by (asm_full_simp_tac (simpset() addsimps [Filter_lemma2,Filter_lemma3]) 1);
qed"FilterPQ_takelemma";

Addsimps [FilterPQ];


(* --------------------------------------------------------------- *)
(*              Alternative Proof of MapConc                       *)
(* --------------------------------------------------------------- *)



Goal "Map f$(x@@y) = (Map f$x) @@ (Map f$y)";
by (res_inst_tac [("A1","%x. True"), ("x1","x")]
    (take_lemma_in_eq_out RS mp) 1);
by Auto_tac;
qed"MapConc_takelemma";


