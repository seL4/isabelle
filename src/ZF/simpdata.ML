(*  Title:      ZF/simpdata
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Rewriting for ZF set theory: specialized extraction of rewrites from theorems
*)

(*** New version of mk_rew_rules ***)

(*Should False yield False<->True, or should it solve goals some other way?*)

(*Analyse a theorem to atomic rewrite rules*)
fun atomize (conn_pairs, mem_pairs) th =
  let fun tryrules pairs t =
          case head_of t of
              Const(a,_) =>
                (case assoc(pairs,a) of
                     Some rls => flat (map (atomize (conn_pairs, mem_pairs))
                                       ([th] RL rls))
                   | None     => [th])
            | _ => [th]
  in case concl_of th of
         Const("Trueprop",_) $ P =>
            (case P of
                 Const("op :",_) $ a $ b => tryrules mem_pairs b
               | Const("True",_)         => []
               | Const("False",_)        => []
               | A => tryrules conn_pairs A)
       | _                       => [th]
  end;

(*Analyse a rigid formula*)
val ZF_conn_pairs =
  [("Ball",     [bspec]),
   ("All",      [spec]),
   ("op -->",   [mp]),
   ("op &",     [conjunct1,conjunct2])];

(*Analyse a:b, where b is rigid*)
val ZF_mem_pairs =
  [("Collect",  [CollectD1,CollectD2]),
   ("op -",     [DiffD1,DiffD2]),
   ("op Int",   [IntD1,IntD2])];

val ZF_atomize = atomize (ZF_conn_pairs, ZF_mem_pairs);

simpset_ref() :=
  simpset() setmksimps (map mk_eq o ZF_atomize o gen_all)
  addcongs [if_weak_cong]
  addsplits [split_if]
  setSolver (mk_solver "types" (fn prems => TCSET' (fn tcset => type_solver_tac tcset prems)));


(** Splitting IFs in the assumptions **)

Goal "P(if Q then x else y) <-> (~((Q & ~P(x)) | (~Q & ~P(y))))";
by (Simp_tac 1);
qed "split_if_asm";

bind_thms ("if_splits", [split_if, split_if_asm]);


(*** Miniscoping: pushing in big Unions, Intersections, quantifiers, etc. ***)

local
  (*For proving rewrite rules*)
  fun prover s = (print s;prove_goalw (the_context ()) [Inter_def] s
                  (fn _ => [Simp_tac 1,
                            ALLGOALS (blast_tac (claset() addSIs[equalityI]))]));

in

val ball_simps = map prover
    ["(ALL x:A. P(x) & Q)   <-> (ALL x:A. P(x)) & (A=0 | Q)",
     "(ALL x:A. P & Q(x))   <-> (A=0 | P) & (ALL x:A. Q(x))",
     "(ALL x:A. P(x) | Q)   <-> ((ALL x:A. P(x)) | Q)",
     "(ALL x:A. P | Q(x))   <-> (P | (ALL x:A. Q(x)))",
     "(ALL x:A. P --> Q(x)) <-> (P --> (ALL x:A. Q(x)))",
     "(ALL x:A. P(x) --> Q) <-> ((EX x:A. P(x)) --> Q)",
     "(ALL x:0.P(x)) <-> True",
     "(ALL x:succ(i).P(x)) <-> P(i) & (ALL x:i. P(x))",
     "(ALL x:cons(a,B).P(x)) <-> P(a) & (ALL x:B. P(x))",
     "(ALL x:RepFun(A,f). P(x)) <-> (ALL y:A. P(f(y)))",
     "(ALL x:Union(A).P(x)) <-> (ALL y:A. ALL x:y. P(x))",
     "(ALL x:Collect(A,Q).P(x)) <-> (ALL x:A. Q(x) --> P(x))",
     "(~(ALL x:A. P(x))) <-> (EX x:A. ~P(x))"];

val ball_conj_distrib =
    prover "(ALL x:A. P(x) & Q(x)) <-> ((ALL x:A. P(x)) & (ALL x:A. Q(x)))";

val bex_simps = map prover
    ["(EX x:A. P(x) & Q) <-> ((EX x:A. P(x)) & Q)",
     "(EX x:A. P & Q(x)) <-> (P & (EX x:A. Q(x)))",
     "(EX x:A. P(x) | Q) <-> (EX x:A. P(x)) | (A~=0 & Q)",
     "(EX x:A. P | Q(x)) <-> (A~=0 & P) | (EX x:A. Q(x))",
     "(EX x:A. P --> Q(x)) <-> ((A=0 | P) --> (EX x:A. Q(x)))",
     "(EX x:A. P(x) --> Q) <-> ((ALL x:A. P(x)) --> (A~=0 & Q))",
     "(EX x:0.P(x)) <-> False",
     "(EX x:succ(i).P(x)) <-> P(i) | (EX x:i. P(x))",
     "(EX x:cons(a,B).P(x)) <-> P(a) | (EX x:B. P(x))",
     "(EX x:RepFun(A,f). P(x)) <-> (EX y:A. P(f(y)))",
     "(EX x:Union(A).P(x)) <-> (EX y:A. EX x:y.  P(x))",
     "(EX x:Collect(A,Q).P(x)) <-> (EX x:A. Q(x) & P(x))",
     "(~(EX x:A. P(x))) <-> (ALL x:A. ~P(x))"];

val bex_disj_distrib =
    prover "(EX x:A. P(x) | Q(x)) <-> ((EX x:A. P(x)) | (EX x:A. Q(x)))";

val Rep_simps = map prover
    ["{x. y:0, R(x,y)} = 0",    (*Replace*)
     "{x:0. P(x)} = 0",         (*Collect*)
     "{x:A. P} = (if P then A else 0)",
     "RepFun(0,f) = 0",         (*RepFun*)
     "RepFun(succ(i),f) = cons(f(i), RepFun(i,f))",
     "RepFun(cons(a,B),f) = cons(f(a), RepFun(B,f))"]

val misc_simps = map prover
    ["0 Un A = A", "A Un 0 = A",
     "0 Int A = 0", "A Int 0 = 0",
     "0 - A = 0", "A - 0 = A",
     "Union(0) = 0",
     "Union(cons(b,A)) = b Un Union(A)",
     "Inter({b}) = b"]


val UN_simps = map prover
    ["(UN x:C. cons(a, B(x))) = (if C=0 then 0 else cons(a, UN x:C. B(x)))",
     "(UN x:C. A(x) Un B)   = (if C=0 then 0 else (UN x:C. A(x)) Un B)",
     "(UN x:C. A Un B(x))   = (if C=0 then 0 else A Un (UN x:C. B(x)))",
     "(UN x:C. A(x) Int B)  = ((UN x:C. A(x)) Int B)",
     "(UN x:C. A Int B(x))  = (A Int (UN x:C. B(x)))",
     "(UN x:C. A(x) - B)    = ((UN x:C. A(x)) - B)",
     "(UN x:C. A - B(x))    = (if C=0 then 0 else A - (INT x:C. B(x)))",
     "(UN x: Union(A). B(x)) = (UN y:A. UN x:y. B(x))",
     "(UN z: (UN x:A. B(x)). C(z)) = (UN  x:A. UN z: B(x). C(z))",
     "(UN x: RepFun(A,f). B(x))     = (UN a:A. B(f(a)))"];

val INT_simps = map prover
    ["(INT x:C. A(x) Int B) = (INT x:C. A(x)) Int B",
     "(INT x:C. A Int B(x)) = A Int (INT x:C. B(x))",
     "(INT x:C. A(x) - B)   = (INT x:C. A(x)) - B",
     "(INT x:C. A - B(x))   = (if C=0 then 0 else A - (UN x:C. B(x)))",
     "(INT x:C. cons(a, B(x))) = (if C=0 then 0 else cons(a, INT x:C. B(x)))",
     "(INT x:C. A(x) Un B)  = (if C=0 then 0 else (INT x:C. A(x)) Un B)",
     "(INT x:C. A Un B(x))  = (if C=0 then 0 else A Un (INT x:C. B(x)))"];

(** The _extend_simps rules are oriented in the opposite direction, to
    pull UN and INT outwards. **)

val UN_extend_simps = map prover
    ["cons(a, UN x:C. B(x)) = (if C=0 then {a} else (UN x:C. cons(a, B(x))))",
     "(UN x:C. A(x)) Un B   = (if C=0 then B else (UN x:C. A(x) Un B))",
     "A Un (UN x:C. B(x))   = (if C=0 then A else (UN x:C. A Un B(x)))",
     "((UN x:C. A(x)) Int B) = (UN x:C. A(x) Int B)",
     "(A Int (UN x:C. B(x))) = (UN x:C. A Int B(x))",
     "((UN x:C. A(x)) - B) = (UN x:C. A(x) - B)",
     "A - (INT x:C. B(x))    = (if C=0 then A else (UN x:C. A - B(x)))",
     "(UN y:A. UN x:y. B(x)) = (UN x: Union(A). B(x))",
     "(UN  x:A. UN z: B(x). C(z)) = (UN z: (UN x:A. B(x)). C(z))",
     "(UN a:A. B(f(a))) = (UN x: RepFun(A,f). B(x))"];

val INT_extend_simps = map prover
    ["(INT x:C. A(x)) Int B = (INT x:C. A(x) Int B)",
     "A Int (INT x:C. B(x)) = (INT x:C. A Int B(x))",
     "(INT x:C. A(x)) - B = (INT x:C. A(x) - B)",
     "A - (UN x:C. B(x))   = (if C=0 then A else (INT x:C. A - B(x)))",
     "cons(a, INT x:C. B(x)) = (if C=0 then {a} else (INT x:C. cons(a, B(x))))",
     "(INT x:C. A(x)) Un B  = (if C=0 then B else (INT x:C. A(x) Un B))",
     "A Un (INT x:C. B(x))  = (if C=0 then A else (INT x:C. A Un B(x)))"];

end;

bind_thms ("ball_simps", ball_simps);
bind_thm ("ball_conj_distrib", ball_conj_distrib);
bind_thms ("bex_simps", bex_simps);
bind_thm ("bex_disj_distrib", bex_disj_distrib);
bind_thms ("Rep_simps", Rep_simps);
bind_thms ("misc_simps", misc_simps);

Addsimps (ball_simps @ bex_simps @ Rep_simps @ misc_simps);

bind_thms ("UN_simps", UN_simps);
bind_thms ("INT_simps", INT_simps);

Addsimps (UN_simps @ INT_simps);

bind_thms ("UN_extend_simps", UN_extend_simps);
bind_thms ("INT_extend_simps", INT_extend_simps);


(** One-point rule for bounded quantifiers: see HOL/Set.ML **)

Goal "(EX x:A. x=a) <-> (a:A)";
by (Blast_tac 1);
qed "bex_triv_one_point1";

Goal "(EX x:A. a=x) <-> (a:A)";
by (Blast_tac 1);
qed "bex_triv_one_point2";

Goal "(EX x:A. x=a & P(x)) <-> (a:A & P(a))";
by (Blast_tac 1);
qed "bex_one_point1";

Goal "(EX x:A. a=x & P(x)) <-> (a:A & P(a))";
by (Blast_tac 1);
qed "bex_one_point2";

Goal "(ALL x:A. x=a --> P(x)) <-> (a:A --> P(a))";
by (Blast_tac 1);
qed "ball_one_point1";

Goal "(ALL x:A. a=x --> P(x)) <-> (a:A --> P(a))";
by (Blast_tac 1);
qed "ball_one_point2";

Addsimps [bex_triv_one_point1,bex_triv_one_point2,
          bex_one_point1,bex_one_point2,
          ball_one_point1,ball_one_point2];


local

val prove_bex_tac = rewtac Bex_def THEN Quantifier1.prove_one_point_ex_tac;
val rearrange_bex = Quantifier1.rearrange_bex prove_bex_tac;

val prove_ball_tac = rewtac Ball_def THEN Quantifier1.prove_one_point_all_tac;
val rearrange_ball = Quantifier1.rearrange_ball prove_ball_tac;

in

val defBEX_regroup = Simplifier.simproc (Theory.sign_of (the_context ()))
  "defined BEX" ["EX x:A. P(x) & Q(x)"] rearrange_bex;

val defBALL_regroup = Simplifier.simproc (Theory.sign_of (the_context ()))
  "defined BALL" ["ALL x:A. P(x) --> Q(x)"] rearrange_ball;

end;

Addsimprocs [defBALL_regroup, defBEX_regroup];


val ZF_ss = simpset();
