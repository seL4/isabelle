(*  Title:      ZF/simpdata
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Rewriting for ZF set theory: specialized extraction of rewrites from theorems
*)

(** Rewriting **)

local
  (*For proving rewrite rules*)
  fun prover s = (prove_goal thy s (fn _ => [Blast_tac 1]));

in

val ball_simps = map prover
    ["(ALL x:A. P(x) | Q)   <-> ((ALL x:A. P(x)) | Q)",
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
    ["{x. y:0, R(x,y)} = 0",	(*Replace*)
     "{x:0. P(x)} = 0",		(*Collect*)
     "{x:A. False} = 0",
     "{x:A. True} = A",
     "RepFun(0,f) = 0",		(*RepFun*)
     "RepFun(succ(i),f) = cons(f(i), RepFun(i,f))",
     "RepFun(cons(a,B),f) = cons(f(a), RepFun(B,f))"]

val misc_simps = map prover
    ["0 Un A = A",  "A Un 0 = A",
     "0 Int A = 0", "A Int 0 = 0",
     "0-A = 0",     "A-0 = A",
     "Union(0) = 0",
     "Union(cons(b,A)) = b Un Union(A)",
     "Inter({b}) = b"]

end;

Addsimps (ball_simps @ bex_simps @ Rep_simps @ misc_simps);


(** New version of mk_rew_rules **)

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

simpset_ref() := simpset() setmksimps (map mk_eq o ZF_atomize o gen_all)
                           addsplits [split_if]
                           setSolver Type_solver_tac;

val ZF_ss = simpset();
