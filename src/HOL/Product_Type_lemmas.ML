(*  Title:      HOL/Product_Type_lemmas.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Ordered Pairs, the Cartesian product type, the unit type
*)

(* ML bindings *)
val Pair_def  = thm "Pair_def";
val fst_def   = thm "fst_def";
val snd_def   = thm "snd_def";
val split_def = thm "split_def";
val prod_fun_def = thm "prod_fun_def";
val Sigma_def = thm "Sigma_def";
val Unity_def = thm "Unity_def";


(** unit **)

Goalw [Unity_def] "u = ()";
by (stac (rewrite_rule [thm"unit_def"] (thm"Rep_unit") RS singletonD RS sym) 1);
by (rtac (thm "Rep_unit_inverse" RS sym) 1);
qed "unit_eq";

(*simplification procedure for unit_eq.
  Cannot use this rule directly -- it loops!*)
local
  val unit_pat = Thm.cterm_of (Theory.sign_of (the_context ())) (Free ("x", HOLogic.unitT));
  val unit_meta_eq = standard (mk_meta_eq unit_eq);
  fun proc _ _ t =
    if HOLogic.is_unit t then None
    else Some unit_meta_eq;
in
  val unit_eq_proc = Simplifier.mk_simproc "unit_eq" [unit_pat] proc;
end;

Addsimprocs [unit_eq_proc];

Goal "(!!x::unit. PROP P x) == PROP P ()";
by (Simp_tac 1);
qed "unit_all_eq1";

Goal "(!!x::unit. PROP P) == PROP P";
by (rtac triv_forall_equality 1);
qed "unit_all_eq2";

Goal "P () ==> P x";
by (Simp_tac 1);
qed "unit_induct";

(*This rewrite counters the effect of unit_eq_proc on (%u::unit. f u),
  replacing it by f rather than by %u.f(). *)
Goal "(%u::unit. f()) = f";
by (rtac ext 1);
by (Simp_tac 1);
qed "unit_abs_eta_conv";
Addsimps [unit_abs_eta_conv];


(** prod **)

Goalw [thm "Prod_def"] "Pair_Rep a b : Prod";
by (EVERY1 [rtac CollectI, rtac exI, rtac exI, rtac refl]);
qed "ProdI";

Goalw [thm "Pair_Rep_def"] "Pair_Rep a b = Pair_Rep a' b' ==> a=a' & b=b'";
by (dtac (fun_cong RS fun_cong) 1);
by (Blast_tac 1);
qed "Pair_Rep_inject";

Goal "inj_on Abs_Prod Prod";
by (rtac inj_on_inverseI 1);
by (etac (thm "Abs_Prod_inverse") 1);
qed "inj_on_Abs_Prod";

val prems = Goalw [Pair_def]
    "[| (a, b) = (a',b');  [| a=a';  b=b' |] ==> R |] ==> R";
by (rtac (inj_on_Abs_Prod RS inj_onD RS Pair_Rep_inject RS conjE) 1);
by (REPEAT (ares_tac (prems@[ProdI]) 1));
qed "Pair_inject";

Goal "((a,b) = (a',b')) = (a=a' & b=b')";
by (blast_tac (claset() addSEs [Pair_inject]) 1);
qed "Pair_eq";
AddIffs [Pair_eq];

Goalw [fst_def] "fst (a,b) = a";
by (Blast_tac 1);
qed "fst_conv";
Goalw [snd_def] "snd (a,b) = b";
by (Blast_tac 1);
qed "snd_conv";
Addsimps [fst_conv, snd_conv];

Goal "fst (x, y) = a ==> x = a";
by (Asm_full_simp_tac 1);
qed "fst_eqD";
Goal "snd (x, y) = a ==> y = a";
by (Asm_full_simp_tac 1);
qed "snd_eqD";

Goalw [Pair_def] "? x y. p = (x,y)";
by (rtac (rewrite_rule [thm "Prod_def"] (thm "Rep_Prod") RS CollectE) 1);
by (EVERY1[etac exE, etac exE, rtac exI, rtac exI,
           rtac (thm "Rep_Prod_inverse" RS sym RS trans),  etac arg_cong]);
qed "PairE_lemma";

val [prem] = Goal "[| !!x y. p = (x,y) ==> Q |] ==> Q";
by (rtac (PairE_lemma RS exE) 1);
by (REPEAT (eresolve_tac [prem,exE] 1));
qed "PairE";

fun pair_tac s = EVERY' [res_inst_tac [("p",s)] PairE, hyp_subst_tac,
                         K prune_params_tac];

(* Do not add as rewrite rule: invalidates some proofs in IMP *)
Goal "p = (fst(p),snd(p))";
by (pair_tac "p" 1);
by (Asm_simp_tac 1);
qed "surjective_pairing";
Addsimps [surjective_pairing RS sym];

Goal "? x y. z = (x, y)";
by (rtac exI 1);
by (rtac exI 1);
by (rtac surjective_pairing 1);
qed "surj_pair";
Addsimps [surj_pair];

bind_thm ("split_paired_all",
  SplitPairedAll.rule (standard (surjective_pairing RS eq_reflection)));
bind_thms ("split_tupled_all", [split_paired_all, unit_all_eq2]);

(*
Addsimps [split_paired_all] does not work with simplifier
because it also affects premises in congrence rules,
where is can lead to premises of the form !!a b. ... = ?P(a,b)
which cannot be solved by reflexivity.
*)

(* replace parameters of product type by individual component parameters *)
val safe_full_simp_tac = generic_simp_tac true (true, false, false);
local (* filtering with exists_paired_all is an essential optimization *)
  fun exists_paired_all (Const ("all", _) $ Abs (_, T, t)) =
        can HOLogic.dest_prodT T orelse exists_paired_all t
    | exists_paired_all (t $ u) = exists_paired_all t orelse exists_paired_all u
    | exists_paired_all (Abs (_, _, t)) = exists_paired_all t
    | exists_paired_all _ = false;
  val ss = HOL_basic_ss
    addsimps [split_paired_all, unit_all_eq2, unit_abs_eta_conv]
    addsimprocs [unit_eq_proc];
in
  val split_all_tac = SUBGOAL (fn (t, i) =>
    if exists_paired_all t then safe_full_simp_tac ss i else no_tac);
  val unsafe_split_all_tac = SUBGOAL (fn (t, i) =>
    if exists_paired_all t then full_simp_tac ss i else no_tac);
  fun split_all th =
 if exists_paired_all (#prop (Thm.rep_thm th)) then full_simplify ss th else th;
end;

claset_ref() := claset() addSbefore ("split_all_tac", split_all_tac);

Goal "(!x. P x) = (!a b. P(a,b))";
by (Fast_tac 1);
qed "split_paired_All";
Addsimps [split_paired_All];
(* AddIffs is not a good idea because it makes Blast_tac loop *)

bind_thm ("prod_induct",
  allI RS (allI RS (split_paired_All RS iffD2)) RS spec);

Goal "(? x. P x) = (? a b. P(a,b))";
by (Fast_tac 1);
qed "split_paired_Ex";
Addsimps [split_paired_Ex];

Goalw [split_def] "split c (a,b) = c a b";
by (Simp_tac 1);
qed "split_conv";
Addsimps [split_conv];
bind_thm ("split", split_conv);                  (*for compatibility*)

bind_thm ("splitI", split_conv RS iffD2);
bind_thm ("splitD", split_conv RS iffD1);

(*Subsumes the old split_Pair when f is the identity function*)
Goal "split (%x y. f(x,y)) = f";
by (rtac ext 1);
by (pair_tac "x" 1);
by (Simp_tac 1);
qed "split_Pair_apply";

(*Can't be added to simpset: loops!*)
Goal "(THE x. P x) = (THE (a,b). P(a,b))";
by (simp_tac (simpset() addsimps [split_Pair_apply]) 1);
qed "split_paired_The";

Goalw [split_def] "The (split P) = (THE xy. P (fst xy) (snd xy))";
by (rtac refl 1);
qed "The_split";

Goal "!!s t. (s=t) = (fst(s)=fst(t) & snd(s)=snd(t))";
by (split_all_tac 1);
by (Asm_simp_tac 1);
qed "Pair_fst_snd_eq";

Goal "fst p = fst q ==> snd p = snd q ==> p = q";
by (asm_simp_tac (simpset() addsimps [Pair_fst_snd_eq]) 1);
qed "prod_eqI";
AddXIs [prod_eqI];

(*Prevents simplification of c: much faster*)
Goal "p=q ==> split c p = split c q";
by (etac arg_cong 1);
qed "split_weak_cong";

Goal "(%(x,y). f(x,y)) = f";
by (rtac ext 1);
by (split_all_tac 1);
by (rtac split_conv 1);
qed "split_eta";

val prems = Goal "(!!x y. f x y = g(x,y)) ==> (%(x,y). f x y) = g";
by (asm_simp_tac (simpset() addsimps prems@[split_eta]) 1);
qed "cond_split_eta";

(*simplification procedure for cond_split_eta.
  using split_eta a rewrite rule is not general enough, and using
  cond_split_eta directly would render some existing proofs very inefficient.
  similarly for split_beta. *)
local
  fun  Pair_pat k 0 (Bound m) = (m = k)
  |    Pair_pat k i (Const ("Pair",  _) $ Bound m $ t) = i > 0 andalso
                        m = k+i andalso Pair_pat k (i-1) t
  |    Pair_pat _ _ _ = false;
  fun no_args k i (Abs (_, _, t)) = no_args (k+1) i t
  |   no_args k i (t $ u) = no_args k i t andalso no_args k i u
  |   no_args k i (Bound m) = m < k orelse m > k+i
  |   no_args _ _ _ = true;
  fun split_pat tp i (Abs  (_,_,t)) = if tp 0 i t then Some (i,t) else None
  |   split_pat tp i (Const ("split", _) $ Abs (_, _, t)) = split_pat tp (i+1) t
  |   split_pat tp i _ = None;
  fun metaeq sg lhs rhs = mk_meta_eq (prove_goalw_cterm []
        (cterm_of sg (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs,rhs))))
        (K [simp_tac (HOL_basic_ss addsimps [cond_split_eta]) 1]));
  val sign = sign_of (the_context ());
  fun simproc name patstr = Simplifier.mk_simproc name
                [Thm.read_cterm sign (patstr, HOLogic.termT)];

  val beta_patstr = "split f z";
  val  eta_patstr = "split f";
  fun beta_term_pat k i (Abs (_, _, t)) = beta_term_pat (k+1) i t
  |   beta_term_pat k i (t $ u) = Pair_pat k i (t $ u) orelse
                        (beta_term_pat k i t andalso beta_term_pat k i u)
  |   beta_term_pat k i t = no_args k i t;
  fun  eta_term_pat k i (f $ arg) = no_args k i f andalso Pair_pat k i arg
  |    eta_term_pat _ _ _ = false;
  fun subst arg k i (Abs (x, T, t)) = Abs (x, T, subst arg (k+1) i t)
  |   subst arg k i (t $ u) = if Pair_pat k i (t $ u) then incr_boundvars k arg
                              else (subst arg k i t $ subst arg k i u)
  |   subst arg k i t = t;
  fun beta_proc sg _ (s as Const ("split", _) $ Abs (_, _, t) $ arg) =
        (case split_pat beta_term_pat 1 t of
        Some (i,f) => Some (metaeq sg s (subst arg 0 i f))
        | None => None)
  |   beta_proc _ _ _ = None;
  fun eta_proc sg _ (s as Const ("split", _) $ Abs (_, _, t)) =
        (case split_pat eta_term_pat 1 t of
          Some (_,ft) => Some (metaeq sg s (let val (f $ arg) = ft in f end))
        | None => None)
  |   eta_proc _ _ _ = None;
in
  val split_beta_proc = simproc "split_beta" beta_patstr beta_proc;
  val split_eta_proc  = simproc "split_eta"   eta_patstr  eta_proc;
end;

Addsimprocs [split_beta_proc,split_eta_proc];

Goal "(%(x,y). P x y) z = P (fst z) (snd z)";
by (stac surjective_pairing 1 THEN rtac split_conv 1);
qed "split_beta";

(*For use with split_tac and the simplifier*)
Goal "R (split c p) = (! x y. p = (x,y) --> R (c x y))";
by (stac surjective_pairing 1);
by (stac split_conv 1);
by (Blast_tac 1);
qed "split_split";

(* could be done after split_tac has been speeded up significantly:
simpset_ref() := simpset() addsplits [split_split];
   precompute the constants involved and don't do anything unless
   the current goal contains one of those constants
*)

Goal "R (split c p) = (~(? x y. p = (x,y) & (~R (c x y))))";
by (stac split_split 1);
by (Simp_tac 1);
qed "split_split_asm";

(** split used as a logical connective or set former **)

(*These rules are for use with blast_tac.
  Could instead call simp_tac/asm_full_simp_tac using split as rewrite.*)

Goal "!!p. [| !!a b. p=(a,b) ==> c a b |] ==> split c p";
by (split_all_tac 1);
by (Asm_simp_tac 1);
qed "splitI2";

Goal "!!p. [| !!a b. (a,b)=p ==> c a b x |] ==> split c p x";
by (split_all_tac 1);
by (Asm_simp_tac 1);
qed "splitI2'";

val prems = Goalw [split_def]
    "[| split c p;  !!x y. [| p = (x,y);  c x y |] ==> Q |] ==> Q";
by (REPEAT (resolve_tac (prems@[surjective_pairing]) 1));
qed "splitE";

val prems = Goalw [split_def]
    "[| split c p z;  !!x y. [| p = (x,y);  c x y z |] ==> Q |] ==> Q";
by (REPEAT (resolve_tac (prems@[surjective_pairing]) 1));
qed "splitE'";

val major::prems = Goal
    "[| Q (split P z);  !!x y. [|z = (x, y); Q (P x y)|] ==> R  \
\    |] ==> R";
by (REPEAT (resolve_tac (prems@[surjective_pairing]) 1));
by (rtac (split_beta RS subst) 1 THEN rtac major 1);
qed "splitE2";

Goal "split R (a,b) c ==> R a b c";
by (Asm_full_simp_tac 1);
qed "splitD'";

Goal "z: c a b ==> z: split c (a,b)";
by (Asm_simp_tac 1);
qed "mem_splitI";

Goal "!!p. [| !!a b. p=(a,b) ==> z: c a b |] ==> z: split c p";
by (split_all_tac 1);
by (Asm_simp_tac 1);
qed "mem_splitI2";

val prems = Goalw [split_def]
    "[| z: split c p;  !!x y. [| p = (x,y);  z: c x y |] ==> Q |] ==> Q";
by (REPEAT (resolve_tac (prems@[surjective_pairing]) 1));
qed "mem_splitE";

AddSIs [splitI, splitI2, splitI2', mem_splitI, mem_splitI2];
AddSEs [splitE, splitE', mem_splitE];

local (* filtering with exists_p_split is an essential optimization *)
  fun exists_p_split (Const ("split",_) $ _ $ (Const ("Pair",_)$_$_)) = true
    | exists_p_split (t $ u) = exists_p_split t orelse exists_p_split u
    | exists_p_split (Abs (_, _, t)) = exists_p_split t
    | exists_p_split _ = false;
  val ss = HOL_basic_ss addsimps [split_conv]
in 
val split_conv_tac = SUBGOAL (fn (t, i) =>
    if exists_p_split t then safe_full_simp_tac ss i else no_tac);
end;
(* This prevents applications of splitE for already splitted arguments leading 
   to quite time-consuming computations (in particular for nested tuples) *)
claset_ref() := claset() addSbefore ("split_conv_tac", split_conv_tac);

Goal "(%u. ? x y. u = (x, y) & P (x, y)) = P";
by (rtac ext 1);
by (Fast_tac 1);
qed "split_eta_SetCompr";
Addsimps [split_eta_SetCompr];

Goal "(%u. ? x y. u = (x, y) & P x y) = split P";
br ext 1;
by (Fast_tac 1);
qed "split_eta_SetCompr2";
Addsimps [split_eta_SetCompr2];

(* allows simplifications of nested splits in case of independent predicates *)
Goal "(%(a,b). P & Q a b) = (%ab. P & split Q ab)";
by (rtac ext 1);
by (Blast_tac 1);
qed "split_part";
Addsimps [split_part];

Goal "(THE (x',y'). x = x' & y = y') = (x,y)";
by (Blast_tac 1);
qed "The_split_eq";
Addsimps [The_split_eq];
(*
the following  would be slightly more general,
but cannot be used as rewrite rule:
### Cannot add premise as rewrite rule because it contains (type) unknowns:
### ?y = .x
Goal "[| P y; !!x. P x ==> x = y |] ==> (@(x',y). x = x' & P y) = (x,y)";
by (rtac some_equality 1);
by ( Simp_tac 1);
by (split_all_tac 1);
by (Asm_full_simp_tac 1);
qed "The_split_eq";
*)

Goal "!!x y. [|fst x = fst y; snd x = snd y|] ==> x = y";
by Auto_tac;
qed "injective_fst_snd";

(*** prod_fun -- action of the product functor upon functions ***)

Goalw [prod_fun_def] "prod_fun f g (a,b) = (f(a),g(b))";
by (rtac split_conv 1);
qed "prod_fun";
Addsimps [prod_fun];

Goal "prod_fun (f1 o f2) (g1 o g2) = ((prod_fun f1 g1) o (prod_fun f2 g2))";
by (rtac ext 1);
by (pair_tac "x" 1);
by (Asm_simp_tac 1);
qed "prod_fun_compose";

Goal "prod_fun (%x. x) (%y. y) = (%z. z)";
by (rtac ext 1);
by (pair_tac "z" 1);
by (Asm_simp_tac 1);
qed "prod_fun_ident";
Addsimps [prod_fun_ident];

Goal "(a,b):r ==> (f(a),g(b)) : (prod_fun f g)`r";
by (rtac image_eqI 1);
by (rtac (prod_fun RS sym) 1);
by (assume_tac 1);
qed "prod_fun_imageI";

val major::prems = Goal
    "[| c: (prod_fun f g)`r;  !!x y. [| c=(f(x),g(y));  (x,y):r |] ==> P  \
\    |] ==> P";
by (rtac (major RS imageE) 1);
by (res_inst_tac [("p","x")] PairE 1);
by (resolve_tac prems 1);
by (Blast_tac 2);
by (blast_tac (claset() addIs [prod_fun]) 1);
qed "prod_fun_imageE";

AddIs  [prod_fun_imageI];
AddSEs [prod_fun_imageE];


(*** Disjoint union of a family of sets - Sigma ***)

Goalw [Sigma_def] "[| a:A;  b:B(a) |] ==> (a,b) : Sigma A B";
by (REPEAT (ares_tac [singletonI,UN_I] 1));
qed "SigmaI";

AddSIs [SigmaI];

(*The general elimination rule*)
val major::prems = Goalw [Sigma_def]
    "[| c: Sigma A B;  \
\       !!x y.[| x:A;  y:B(x);  c=(x,y) |] ==> P \
\    |] ==> P";
by (cut_facts_tac [major] 1);
by (REPEAT (eresolve_tac [UN_E, singletonE] 1 ORELSE ares_tac prems 1)) ;
qed "SigmaE";

(** Elimination of (a,b):A*B -- introduces no eigenvariables **)

Goal "(a,b) : Sigma A B ==> a : A";
by (etac SigmaE 1);
by (REPEAT (eresolve_tac [asm_rl,Pair_inject,ssubst] 1)) ;
qed "SigmaD1";

Goal "(a,b) : Sigma A B ==> b : B(a)";
by (etac SigmaE 1);
by (REPEAT (eresolve_tac [asm_rl,Pair_inject,ssubst] 1)) ;
qed "SigmaD2";

val [major,minor]= Goal
    "[| (a,b) : Sigma A B;    \
\       [| a:A;  b:B(a) |] ==> P   \
\    |] ==> P";
by (rtac minor 1);
by (rtac (major RS SigmaD1) 1);
by (rtac (major RS SigmaD2) 1) ;
qed "SigmaE2";

AddSEs [SigmaE2, SigmaE];

val prems = Goal
    "[| A<=C;  !!x. x:A ==> B x <= D x |] ==> Sigma A B <= Sigma C D";
by (cut_facts_tac prems 1);
by (blast_tac (claset() addIs (prems RL [subsetD])) 1);
qed "Sigma_mono";

Goal "Sigma {} B = {}";
by (Blast_tac 1) ;
qed "Sigma_empty1";

Goal "A <*> {} = {}";
by (Blast_tac 1) ;
qed "Sigma_empty2";

Addsimps [Sigma_empty1,Sigma_empty2];

Goal "UNIV <*> UNIV = UNIV";
by Auto_tac;
qed "UNIV_Times_UNIV";
Addsimps [UNIV_Times_UNIV];

Goal "- (UNIV <*> A) = UNIV <*> (-A)";
by Auto_tac;
qed "Compl_Times_UNIV1";

Goal "- (A <*> UNIV) = (-A) <*> UNIV";
by Auto_tac;
qed "Compl_Times_UNIV2";

Addsimps [Compl_Times_UNIV1, Compl_Times_UNIV2];

Goal "((a,b): Sigma A B) = (a:A & b:B(a))";
by (Blast_tac 1);
qed "mem_Sigma_iff";
AddIffs [mem_Sigma_iff];

Goal "x:C ==> (A <*> C <= B <*> C) = (A <= B)";
by (Blast_tac 1);
qed "Times_subset_cancel2";

Goal "x:C ==> (A <*> C = B <*> C) = (A = B)";
by (blast_tac (claset() addEs [equalityE]) 1);
qed "Times_eq_cancel2";

Goal "Collect (split (%x y. P x & Q x y)) = (SIGMA x:Collect P. Collect (Q x))";
by (Fast_tac 1);
qed "SetCompr_Sigma_eq";

(*** Complex rules for Sigma ***)

Goal "{(a,b). P a & Q b} = Collect P <*> Collect Q";
by (Blast_tac 1);
qed "Collect_split";

Addsimps [Collect_split];

(*Suggested by Pierre Chartier*)
Goal "(UN (a,b):(A <*> B). E a <*> F b) = (UNION A E) <*> (UNION B F)";
by (Blast_tac 1);
qed "UN_Times_distrib";

Goal "(ALL z: Sigma A B. P z) = (ALL x:A. ALL y: B x. P(x,y))";
by (Fast_tac 1);
qed "split_paired_Ball_Sigma";
Addsimps [split_paired_Ball_Sigma];

Goal "(EX z: Sigma A B. P z) = (EX x:A. EX y: B x. P(x,y))";
by (Fast_tac 1);
qed "split_paired_Bex_Sigma";
Addsimps [split_paired_Bex_Sigma];

Goal "(SIGMA i:I Un J. C(i)) = (SIGMA i:I. C(i)) Un (SIGMA j:J. C(j))";
by (Blast_tac 1);
qed "Sigma_Un_distrib1";

Goal "(SIGMA i:I. A(i) Un B(i)) = (SIGMA i:I. A(i)) Un (SIGMA i:I. B(i))";
by (Blast_tac 1);
qed "Sigma_Un_distrib2";

Goal "(SIGMA i:I Int J. C(i)) = (SIGMA i:I. C(i)) Int (SIGMA j:J. C(j))";
by (Blast_tac 1);
qed "Sigma_Int_distrib1";

Goal "(SIGMA i:I. A(i) Int B(i)) = (SIGMA i:I. A(i)) Int (SIGMA i:I. B(i))";
by (Blast_tac 1);
qed "Sigma_Int_distrib2";

Goal "(SIGMA i:I - J. C(i)) = (SIGMA i:I. C(i)) - (SIGMA j:J. C(j))";
by (Blast_tac 1);
qed "Sigma_Diff_distrib1";

Goal "(SIGMA i:I. A(i) - B(i)) = (SIGMA i:I. A(i)) - (SIGMA i:I. B(i))";
by (Blast_tac 1);
qed "Sigma_Diff_distrib2";

Goal "Sigma (Union X) B = (UN A:X. Sigma A B)";
by (Blast_tac 1);
qed "Sigma_Union";

(*Non-dependent versions are needed to avoid the need for higher-order
  matching, especially when the rules are re-oriented*)
Goal "(A Un B) <*> C = (A <*> C) Un (B <*> C)";
by (Blast_tac 1);
qed "Times_Un_distrib1";

Goal "(A Int B) <*> C = (A <*> C) Int (B <*> C)";
by (Blast_tac 1);
qed "Times_Int_distrib1";

Goal "(A - B) <*> C = (A <*> C) - (B <*> C)";
by (Blast_tac 1);
qed "Times_Diff_distrib1";
