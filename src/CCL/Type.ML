(*  Title: 	CCL/types
    ID:         $Id$
    Author: 	Martin Coen, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

For types.thy.
*)

open Type;

val simp_type_defs = [Subtype_def,Unit_def,Bool_def,Plus_def,Sigma_def,Pi_def,
                      Lift_def,Tall_def,Tex_def];
val ind_type_defs = [Nat_def,List_def];

val simp_data_defs = [one_def,inl_def,inr_def];
val ind_data_defs = [zero_def,succ_def,nil_def,cons_def];

goal Set.thy "A <= B <-> (ALL x.x:A --> x:B)";
by (fast_tac set_cs 1);
val subsetXH = result();

(*** Exhaustion Rules ***)

fun mk_XH_tac thy defs rls s = prove_goalw thy defs s (fn _ => [cfast_tac rls 1]);
val XH_tac = mk_XH_tac Type.thy simp_type_defs [];

val EmptyXH = XH_tac "a : {} <-> False";
val SubtypeXH = XH_tac "a : {x:A.P(x)} <-> (a:A & P(a))";
val UnitXH = XH_tac "a : Unit          <-> a=one";
val BoolXH = XH_tac "a : Bool          <-> a=true | a=false";
val PlusXH = XH_tac "a : A+B           <-> (EX x:A.a=inl(x)) | (EX x:B.a=inr(x))";
val PiXH   = XH_tac "a : PROD x:A.B(x) <-> (EX b.a=lam x.b(x) & (ALL x:A.b(x):B(x)))";
val SgXH   = XH_tac "a : SUM x:A.B(x)  <-> (EX x:A.EX y:B(x).a=<x,y>)";

val XHs = [EmptyXH,SubtypeXH,UnitXH,BoolXH,PlusXH,PiXH,SgXH];

val LiftXH = XH_tac "a : [A] <-> (a=bot | a:A)";
val TallXH = XH_tac "a : TALL X.B(X) <-> (ALL X. a:B(X))";
val TexXH  = XH_tac "a : TEX X.B(X) <-> (EX X. a:B(X))";

val case_rls = XH_to_Es XHs;

(*** Canonical Type Rules ***)

fun mk_canT_tac thy xhs s = prove_goal thy s 
                 (fn prems => [fast_tac (set_cs addIs (prems @ (xhs RL [iffD2]))) 1]);
val canT_tac = mk_canT_tac Type.thy XHs;

val oneT   = canT_tac "one : Unit";
val trueT  = canT_tac "true : Bool";
val falseT = canT_tac "false : Bool";
val lamT   = canT_tac "[| !!x.x:A ==> b(x):B(x) |] ==> lam x.b(x) : Pi(A,B)";
val pairT  = canT_tac "[| a:A; b:B(a) |] ==> <a,b>:Sigma(A,B)";
val inlT   = canT_tac "a:A ==> inl(a) : A+B";
val inrT   = canT_tac "b:B ==> inr(b) : A+B";

val canTs = [oneT,trueT,falseT,pairT,lamT,inlT,inrT];

(*** Non-Canonical Type Rules ***)

local
val lemma = prove_goal Type.thy "[| a:B(u);  u=v |] ==> a : B(v)"
                   (fn prems => [cfast_tac prems 1]);
in
fun mk_ncanT_tac thy defs top_crls crls s = prove_goalw thy defs s 
  (fn major::prems => [(resolve_tac ([major] RL top_crls) 1),
                       (REPEAT_SOME (eresolve_tac (crls @ [exE,bexE,conjE,disjE]))),
                       (ALLGOALS (asm_simp_tac term_ss)),
                       (ALLGOALS (ares_tac (prems RL [lemma]) ORELSE' 
                                  eresolve_tac [bspec])),
                       (safe_tac (ccl_cs addSIs prems))]);
end;

val ncanT_tac = mk_ncanT_tac Type.thy [] case_rls case_rls;

val ifT = ncanT_tac 
     "[| b:Bool; b=true ==> t:A(true); b=false ==> u:A(false) |] ==> \
\     if b then t else u : A(b)";

val applyT = ncanT_tac 
    "[| f : Pi(A,B);  a:A |] ==> f ` a : B(a)";

val splitT = ncanT_tac 
    "[| p:Sigma(A,B); !!x y. [| x:A;  y:B(x); p=<x,y>  |] ==> c(x,y):C(<x,y>) |] ==>  \
\     split(p,c):C(p)";

val whenT = ncanT_tac 
     "[| p:A+B; !!x.[| x:A;  p=inl(x) |] ==> a(x):C(inl(x)); \
\               !!y.[| y:B;  p=inr(y) |] ==> b(y):C(inr(y)) |] ==> \
\     when(p,a,b) : C(p)";

val ncanTs = [ifT,applyT,splitT,whenT];

(*** Subtypes ***)

val SubtypeD1 = standard ((SubtypeXH RS iffD1) RS conjunct1);
val SubtypeD2 = standard ((SubtypeXH RS iffD1) RS conjunct2);

val prems = goal Type.thy
     "[| a:A;  P(a) |] ==> a : {x:A. P(x)}";
by (REPEAT (resolve_tac (prems@[SubtypeXH RS iffD2,conjI]) 1));
val SubtypeI = result();

val prems = goal Type.thy
     "[| a : {x:A. P(x)};  [| a:A;  P(a) |] ==> Q |] ==> Q";
by (REPEAT (resolve_tac (prems@[SubtypeD1,SubtypeD2]) 1));
val SubtypeE = result();

(*** Monotonicity ***)

goal Type.thy "mono (%X.X)";
by (REPEAT (ares_tac [monoI] 1));
val idM = result();

goal Type.thy "mono(%X.A)";
by (REPEAT (ares_tac [monoI,subset_refl] 1));
val constM = result();

val major::prems = goal Type.thy
    "mono(%X.A(X)) ==> mono(%X.[A(X)])";
br (subsetI RS monoI) 1;
bd (LiftXH RS iffD1) 1;
be disjE 1;
be (disjI1 RS (LiftXH RS iffD2)) 1;
br (disjI2 RS (LiftXH RS iffD2)) 1;
be (major RS monoD RS subsetD) 1;
ba 1;
val LiftM = result();

val prems = goal Type.thy
    "[| mono(%X.A(X)); !!x X. x:A(X) ==> mono(%X.B(X,x)) |] ==> \
\    mono(%X.Sigma(A(X),B(X)))";
by (REPEAT (ares_tac ([subsetI RS monoI] @ canTs) 1 ORELSE
            eresolve_tac ([bspec,exE,conjE,disjE,bexE] @ case_rls) 1 ORELSE
            (resolve_tac (prems RL [monoD RS subsetD]) 1 THEN assume_tac 1) ORELSE
            hyp_subst_tac 1));
val SgM = result();

val prems = goal Type.thy
    "[| !!x. x:A ==> mono(%X.B(X,x)) |] ==> mono(%X.Pi(A,B(X)))";
by (REPEAT (ares_tac ([subsetI RS monoI] @ canTs) 1 ORELSE
            eresolve_tac ([bspec,exE,conjE,disjE,bexE] @ case_rls) 1 ORELSE
            (resolve_tac (prems RL [monoD RS subsetD]) 1 THEN assume_tac 1) ORELSE
            hyp_subst_tac 1));
val PiM = result();

val prems = goal Type.thy
     "[| mono(%X.A(X));  mono(%X.B(X)) |] ==> mono(%X.A(X)+B(X))";
by (REPEAT (ares_tac ([subsetI RS monoI] @ canTs) 1 ORELSE
            eresolve_tac ([bspec,exE,conjE,disjE,bexE] @ case_rls) 1 ORELSE
            (resolve_tac (prems RL [monoD RS subsetD]) 1 THEN assume_tac 1) ORELSE
            hyp_subst_tac 1));
val PlusM = result();

(**************** RECURSIVE TYPES ******************)

(*** Conversion Rules for Fixed Points via monotonicity and Tarski ***)

goal Type.thy "mono(%X.Unit+X)";
by (REPEAT (ares_tac [PlusM,constM,idM] 1));
val NatM = result();
val def_NatB = result() RS (Nat_def RS def_lfp_Tarski);

goal Type.thy "mono(%X.(Unit+Sigma(A,%y.X)))";
by (REPEAT (ares_tac [PlusM,SgM,constM,idM] 1));
val ListM = result();
val def_ListB = result() RS (List_def RS def_lfp_Tarski);
val def_ListsB = result() RS (Lists_def RS def_gfp_Tarski);

goal Type.thy "mono(%X.({} + Sigma(A,%y.X)))";
by (REPEAT (ares_tac [PlusM,SgM,constM,idM] 1));
val IListsM = result();
val def_IListsB = result() RS (ILists_def RS def_gfp_Tarski);

val ind_type_eqs = [def_NatB,def_ListB,def_ListsB,def_IListsB];

(*** Exhaustion Rules ***)

fun mk_iXH_tac teqs ddefs rls s = prove_goalw Type.thy ddefs s 
           (fn _ => [resolve_tac (teqs RL [XHlemma1]) 1,
                     fast_tac (set_cs addSIs canTs addSEs case_rls) 1]);

val iXH_tac = mk_iXH_tac ind_type_eqs ind_data_defs [];

val NatXH  = iXH_tac "a : Nat <-> (a=zero | (EX x:Nat.a=succ(x)))";
val ListXH = iXH_tac "a : List(A) <-> (a=[] | (EX x:A.EX xs:List(A).a=x.xs))";
val ListsXH = iXH_tac "a : Lists(A) <-> (a=[] | (EX x:A.EX xs:Lists(A).a=x.xs))";
val IListsXH = iXH_tac "a : ILists(A) <-> (EX x:A.EX xs:ILists(A).a=x.xs)";

val iXHs = [NatXH,ListXH];
val icase_rls = XH_to_Es iXHs;

(*** Type Rules ***)

val icanT_tac = mk_canT_tac Type.thy iXHs;
val incanT_tac = mk_ncanT_tac Type.thy [] icase_rls case_rls;

val zeroT = icanT_tac "zero : Nat";
val succT = icanT_tac "n:Nat ==> succ(n) : Nat";
val nilT  = icanT_tac "[] : List(A)";
val consT = icanT_tac "[| h:A;  t:List(A) |] ==> h.t : List(A)";

val icanTs = [zeroT,succT,nilT,consT];

val ncaseT = incanT_tac 
     "[| n:Nat; n=zero ==> b:C(zero); \
\        !!x.[| x:Nat;  n=succ(x) |] ==> c(x):C(succ(x)) |] ==>  \
\     ncase(n,b,c) : C(n)";

val lcaseT = incanT_tac
     "[| l:List(A); l=[] ==> b:C([]); \
\        !!h t.[| h:A;  t:List(A); l=h.t |] ==> c(h,t):C(h.t) |] ==> \
\     lcase(l,b,c) : C(l)";

val incanTs = [ncaseT,lcaseT];

(*** Induction Rules ***)

val ind_Ms = [NatM,ListM];

fun mk_ind_tac ddefs tdefs Ms canTs case_rls s = prove_goalw Type.thy ddefs s 
     (fn major::prems => [resolve_tac (Ms RL ([major] RL (tdefs RL [def_induct]))) 1,
                          fast_tac (set_cs addSIs (prems @ canTs) addSEs case_rls) 1]);

val ind_tac = mk_ind_tac ind_data_defs ind_type_defs ind_Ms canTs case_rls;

val Nat_ind = ind_tac
     "[| n:Nat; P(zero); !!x.[| x:Nat; P(x) |] ==> P(succ(x)) |] ==>  \
\     P(n)";

val List_ind = ind_tac
     "[| l:List(A); P([]); \
\        !!x xs.[| x:A;  xs:List(A); P(xs) |] ==> P(x.xs) |] ==> \
\     P(l)";

val inds = [Nat_ind,List_ind];

(*** Primitive Recursive Rules ***)

fun mk_prec_tac inds s = prove_goal Type.thy s
     (fn major::prems => [resolve_tac ([major] RL inds) 1,
                          ALLGOALS (simp_tac term_ss THEN'
                                    fast_tac (set_cs addSIs prems))]);
val prec_tac = mk_prec_tac inds;

val nrecT = prec_tac
     "[| n:Nat; b:C(zero); \
\        !!x g.[| x:Nat; g:C(x) |] ==> c(x,g):C(succ(x)) |] ==>  \
\     nrec(n,b,c) : C(n)";

val lrecT = prec_tac
     "[| l:List(A); b:C([]); \
\        !!x xs g.[| x:A;  xs:List(A); g:C(xs) |] ==> c(x,xs,g):C(x.xs) |] ==>  \
\     lrec(l,b,c) : C(l)";

val precTs = [nrecT,lrecT];


(*** Theorem proving ***)

val [major,minor] = goal Type.thy
    "[| <a,b> : Sigma(A,B);  [| a:A;  b:B(a) |] ==> P   \
\    |] ==> P";
br (major RS (XH_to_E SgXH)) 1;
br minor 1;
by (ALLGOALS (fast_tac term_cs));
val SgE2 = result();

(* General theorem proving ignores non-canonical term-formers,             *)
(*         - intro rules are type rules for canonical terms                *)
(*         - elim rules are case rules (no non-canonical terms appear)     *)

val type_cs = term_cs addSIs (SubtypeI::(canTs @ icanTs))
                      addSEs (SubtypeE::(XH_to_Es XHs));


(*** Infinite Data Types ***)

val [mono] = goal Type.thy "mono(f) ==> lfp(f) <= gfp(f)";
br (lfp_lowerbound RS subset_trans) 1;
br (mono RS gfp_lemma3) 1;
br subset_refl 1;
val lfp_subset_gfp = result();

val prems = goal Type.thy
    "[| a:A;  !!x X.[| x:A;  ALL y:A.t(y):X |] ==> t(x) : B(X) |] ==> \
\    t(a) : gfp(B)";
br coinduct 1;
by (res_inst_tac [("P","%x.EX y:A.x=t(y)")] CollectI 1);
by (ALLGOALS (fast_tac (ccl_cs addSIs prems)));
val gfpI = result();

val rew::prem::prems = goal Type.thy
    "[| C==gfp(B);  a:A;  !!x X.[| x:A;  ALL y:A.t(y):X |] ==> t(x) : B(X) |] ==> \
\    t(a) : C";
by (rewtac rew);
by (REPEAT (ares_tac ((prem RS gfpI)::prems) 1));
val def_gfpI = result();

(* EG *)

val prems = goal Type.thy 
    "letrec g x be zero.g(x) in g(bot) : Lists(Nat)";
by (rtac (refl RS (XH_to_I UnitXH) RS (Lists_def RS def_gfpI)) 1);
br (letrecB RS ssubst) 1;
bw cons_def;
by (fast_tac type_cs 1);
result();
