(*  Title:      ZF/simpdata
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge

Rewriting for ZF set theory: specialized extraction of rewrites from theorems
*)

(** Rewriting **)

(*For proving rewrite rules*)
fun prove_fun s = 
    (writeln s;  prove_goal thy s
       (fn prems => [ (cut_facts_tac prems 1), 
                      (fast_tac (!claset addSIs [equalityI]) 1) ]));

(*Are all these really suitable?*)
val ball_simps = map prove_fun
    ["(ALL x:0.P(x)) <-> True",
     "(ALL x:succ(i).P(x)) <-> P(i) & (ALL x:i.P(x))",
     "(ALL x:cons(a,B).P(x)) <-> P(a) & (ALL x:B.P(x))",
     "(ALL x:RepFun(A,f). P(x)) <-> (ALL y:A. P(f(y)))",
     "(ALL x:Union(A).P(x)) <-> (ALL y:A. ALL x:y. P(x))",
     "(ALL x:Collect(A,Q).P(x)) <-> (ALL x:A. Q(x) --> P(x))"];

val bex_simps = map prove_fun
    ["(EX x:0.P(x)) <-> False",
     "(EX x:succ(i).P(x)) <-> P(i) | (EX x:i.P(x))",
     "(EX x:cons(a,B).P(x)) <-> P(a) | (EX x:B.P(x))",
     "(EX x:RepFun(A,f). P(x)) <-> (EX y:A. P(f(y)))",
     "(EX x:Union(A).P(x)) <-> (EX y:A. EX x:y.  P(x))",
     "(EX x:Collect(A,Q).P(x)) <-> (EX x:A. Q(x) & P(x))"];

Addsimps (ball_simps @ bex_simps);

Addsimps (map prove_fun
	  ["{x:0. P(x)} = 0",
	   "{x:A. False} = 0",
	   "{x:A. True} = A",
	   "RepFun(0,f) = 0",
	   "RepFun(succ(i),f) = cons(f(i), RepFun(i,f))",
	   "RepFun(cons(a,B),f) = cons(f(a), RepFun(B,f))"]);

Addsimps (map prove_fun
	  ["0 Un A = A",  "A Un 0 = A",
	   "0 Int A = 0", "A Int 0 = 0",
	   "0-A = 0",     "A-0 = A",
	   "Union(0) = 0",
	   "Union(cons(b,A)) = b Un Union(A)",
	   "Inter({b}) = b"]);

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

simpset := !simpset setmksimps (map mk_meta_eq o ZF_atomize o gen_all);

val ZF_ss = !simpset;
