(*  Title:      HOL/ex/mesontest
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Test data for the MESON proof procedure
   (Excludes the equality problems 51, 52, 56, 58)

Use the "mesonlog" shell script to process logs.

show_hyps := false;

proofs := 0;
by (rtac ccontr 1);
val [prem] = gethyps 1;
val nnf = make_nnf prem;
val xsko = skolemize nnf;
by (cut_facts_tac [xsko] 1 THEN REPEAT (etac exE 1));
val [_,sko] = gethyps 1;
val clauses = make_clauses [sko];       
val horns = make_horns clauses;
val goes = gocls clauses;

Goal "False";
by (resolve_tac goes 1);
proofs := 2;

by (prolog_step_tac horns 1);
by (iter_deepen_prolog_tac horns);
by (depth_prolog_tac horns);
by (best_prolog_tac size_of_subgoals horns);
*)

writeln"File HOL/ex/meson-test.";

context Main.thy;

(*Deep unifications can be required, esp. during transformation to clauses*)
val orig_trace_bound = !Unify.trace_bound
and orig_search_bound = !Unify.search_bound;
Unify.trace_bound := 20;
Unify.search_bound := 40;

(**** Interactive examples ****)

(*Generate nice names for Skolem functions*)
Logic.auto_rename := true; Logic.set_rename_prefix "a";


writeln"Problem 25";
Goal "(\\<exists>x. P x) &  \
\     (\\<forall>x. L x --> ~ (M x & R x)) &  \
\     (\\<forall>x. P x --> (M x & L x)) &   \
\     ((\\<forall>x. P x --> Q x) | (\\<exists>x. P x & R x))  \
\   --> (\\<exists>x. Q x & P x)";
by (rtac ccontr 1);
val [prem25] = gethyps 1;
val nnf25 = make_nnf prem25;
val xsko25 = skolemize nnf25;
by (cut_facts_tac [xsko25] 1 THEN REPEAT (etac exE 1));
val [_,sko25] = gethyps 1;
val clauses25 = make_clauses [sko25];   (*7 clauses*)
val horns25 = make_horns clauses25;     (*16 Horn clauses*)
val go25::_ = gocls clauses25;

Goal "False";
by (rtac go25 1);
by (depth_prolog_tac horns25);


writeln"Problem 26";
Goal "((\\<exists>x. p x) = (\\<exists>x. q x)) &     \
\     (\\<forall>x. \\<forall>y. p x & q y --> (r x = s y)) \
\ --> ((\\<forall>x. p x --> r x) = (\\<forall>x. q x --> s x))";
by (rtac ccontr 1);
val [prem26] = gethyps 1;
val nnf26 = make_nnf prem26;
val xsko26 = skolemize nnf26;
by (cut_facts_tac [xsko26] 1 THEN REPEAT (etac exE 1));
val [_,sko26] = gethyps 1;
val clauses26 = make_clauses [sko26];                   (*9 clauses*)
val horns26 = make_horns clauses26;                     (*24 Horn clauses*)
val go26::_ = gocls clauses26;

Goal "False";
by (rtac go26 1);
by (depth_prolog_tac horns26);  (*1.4 secs*)
(*Proof is of length 107!!*)


writeln"Problem 43  NOW PROVED AUTOMATICALLY!!";  (*16 Horn clauses*)
Goal "(\\<forall>x. \\<forall>y. q x y = (\\<forall>z. p z x = (p z y::bool)))  \
\     --> (\\<forall>x. (\\<forall>y. q x y = (q y x::bool)))";
by (rtac ccontr 1);
val [prem43] = gethyps 1;
val nnf43 = make_nnf prem43;
val xsko43 = skolemize nnf43;
by (cut_facts_tac [xsko43] 1 THEN REPEAT (etac exE 1));
val [_,sko43] = gethyps 1;
val clauses43 = make_clauses [sko43];   (*6*)
val horns43 = make_horns clauses43;     (*16*)
val go43::_ = gocls clauses43;

Goal "False";
by (rtac go43 1);
by (best_prolog_tac size_of_subgoals horns43);   (*1.6 secs*)

(* 
#1  (q x xa ==> ~ q x xa) ==> q xa x
#2  (q xa x ==> ~ q xa x) ==> q x xa
#3  (~ q x xa ==> q x xa) ==> ~ q xa x
#4  (~ q xa x ==> q xa x) ==> ~ q x xa
#5  [| ~ q ?U ?V ==> q ?U ?V; ~ p ?W ?U ==> p ?W ?U |] ==> p ?W ?V
#6  [| ~ p ?W ?U ==> p ?W ?U; p ?W ?V ==> ~ p ?W ?V |] ==> ~ q ?U ?V
#7  [| p ?W ?V ==> ~ p ?W ?V; ~ q ?U ?V ==> q ?U ?V |] ==> ~ p ?W ?U
#8  [| ~ q ?U ?V ==> q ?U ?V; ~ p ?W ?V ==> p ?W ?V |] ==> p ?W ?U
#9  [| ~ p ?W ?V ==> p ?W ?V; p ?W ?U ==> ~ p ?W ?U |] ==> ~ q ?U ?V
#10 [| p ?W ?U ==> ~ p ?W ?U; ~ q ?U ?V ==> q ?U ?V |] ==> ~ p ?W ?V
#11 [| p (xb ?U ?V) ?U ==> ~ p (xb ?U ?V) ?U;
       p (xb ?U ?V) ?V ==> ~ p (xb ?U ?V) ?V |] ==> q ?U ?V
#12 [| p (xb ?U ?V) ?V ==> ~ p (xb ?U ?V) ?V; q ?U ?V ==> ~ q ?U ?V |] ==>
    p (xb ?U ?V) ?U
#13 [| q ?U ?V ==> ~ q ?U ?V; p (xb ?U ?V) ?U ==> ~ p (xb ?U ?V) ?U |] ==>
    p (xb ?U ?V) ?V
#14 [| ~ p (xb ?U ?V) ?U ==> p (xb ?U ?V) ?U;
       ~ p (xb ?U ?V) ?V ==> p (xb ?U ?V) ?V |] ==> q ?U ?V
#15 [| ~ p (xb ?U ?V) ?V ==> p (xb ?U ?V) ?V; q ?U ?V ==> ~ q ?U ?V |] ==>
    ~ p (xb ?U ?V) ?U
#16 [| q ?U ?V ==> ~ q ?U ?V; ~ p (xb ?U ?V) ?U ==> p (xb ?U ?V) ?U |] ==>
    ~ p (xb ?U ?V) ?V

And here is the proof\\<forall> (Unkn is the start state after use of goal clause)
[Unkn, Res ([Thm "#14"], false, 1), Res ([Thm "#5"], false, 1),
   Res ([Thm "#1"], false, 1), Asm 1, Res ([Thm "#13"], false, 1), Asm 2,
   Asm 1, Res ([Thm "#13"], false, 1), Asm 1, Res ([Thm "#10"], false, 1),
   Res ([Thm "#16"], false, 1), Asm 2, Asm 1, Res ([Thm "#1"], false, 1),
   Asm 1, Res ([Thm "#14"], false, 1), Res ([Thm "#5"], false, 1),
   Res ([Thm "#2"], false, 1), Asm 1, Res ([Thm "#13"], false, 1), Asm 2,
   Asm 1, Res ([Thm "#8"], false, 1), Res ([Thm "#2"], false, 1), Asm 1,
   Res ([Thm "#12"], false, 1), Asm 2, Asm 1] : lderiv list
*)


(*Restore variable name preservation*)
Logic.auto_rename := false; 


(**** Batch test data ****)

(*Sample problems from 
  F. J. Pelletier, 
  Seventy-Five Problems for Testing Automatic Theorem Provers,
  J. Automated Reasoning 2 (1986), 191-216.
  Errata, JAR 4 (1988), 236-236.

The hardest problems -- judging by experience with several theorem provers,
including matrix ones -- are 34 and 43.
*)

writeln"Pelletier's examples";
(*1*)
Goal "(P --> Q)  =  (~Q --> ~P)";
by (meson_tac 1);
result();

(*2*)
Goal "(~ ~ P) =  P";
by (meson_tac 1);
result();

(*3*)
Goal "~(P-->Q) --> (Q-->P)";
by (meson_tac 1);
result();

(*4*)
Goal "(~P-->Q)  =  (~Q --> P)";
by (meson_tac 1);
result();

(*5*)
Goal "((P|Q)-->(P|R)) --> (P|(Q-->R))";
by (meson_tac 1);
result();

(*6*)
Goal "P | ~ P";
by (meson_tac 1);
result();

(*7*)
Goal "P | ~ ~ ~ P";
by (meson_tac 1);
result();

(*8.  Peirce's law*)
Goal "((P-->Q) --> P)  -->  P";
by (meson_tac 1);
result();

(*9*)
Goal "((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)";
by (meson_tac 1);
result();

(*10*)
Goal "(Q-->R) & (R-->P&Q) & (P-->Q|R) --> (P=Q)";
by (meson_tac 1);
result();

(*11.  Proved in each direction (incorrectly, says Pelletier!!)  *)
Goal "P=(P::bool)";
by (meson_tac 1);
result();

(*12.  "Dijkstra's law"*)
Goal "((P = Q) = R) = (P = (Q = R))";
by (meson_tac 1);
result();

(*13.  Distributive law*)
Goal "(P | (Q & R)) = ((P | Q) & (P | R))";
by (meson_tac 1);
result();

(*14*)
Goal "(P = Q) = ((Q | ~P) & (~Q|P))";
by (meson_tac 1);
result();

(*15*)
Goal "(P --> Q) = (~P | Q)";
by (meson_tac 1);
result();

(*16*)
Goal "(P-->Q) | (Q-->P)";
by (meson_tac 1);
result();

(*17*)
Goal "((P & (Q-->R))-->S)  =  ((~P | Q | S) & (~P | ~R | S))";
by (meson_tac 1);
result();

writeln"Classical Logic: examples with quantifiers";

Goal "(\\<forall>x. P x & Q x) = ((\\<forall>x. P x) & (\\<forall>x. Q x))";
by (meson_tac 1);
result(); 

Goal "(\\<exists>x. P --> Q x)  =  (P --> (\\<exists>x. Q x))";
by (meson_tac 1);
result(); 

Goal "(\\<exists>x. P x --> Q) = ((\\<forall>x. P x) --> Q)";
by (meson_tac 1);
result(); 

Goal "((\\<forall>x. P x) | Q)  =  (\\<forall>x. P x | Q)";
by (meson_tac 1);
result(); 

Goal "(\\<forall>x. P x --> P(f x))  &  P d --> P(f(f(f d)))";
by (meson_tac 1);
result();

(*Needs double instantiation of EXISTS*)
Goal "\\<exists>x. P x --> P a & P b";
by (meson_tac 1);
result();

Goal "\\<exists>z. P z --> (\\<forall>x. P x)";
by (meson_tac 1);
result();

writeln"Hard examples with quantifiers";

writeln"Problem 18";
Goal "\\<exists>y. \\<forall>x. P y --> P x";
by (meson_tac 1);
result(); 

writeln"Problem 19";
Goal "\\<exists>x. \\<forall>y z. (P y --> Q z) --> (P x --> Q x)";
by (meson_tac 1);
result();

writeln"Problem 20";
Goal "(\\<forall>x y. \\<exists>z. \\<forall>w. (P x & Q y --> R z & S w))     \
\   --> (\\<exists>x y. P x & Q y) --> (\\<exists>z. R z)";
by (meson_tac 1); 
result();

writeln"Problem 21";
Goal "(\\<exists>x. P --> Q x) & (\\<exists>x. Q x --> P) --> (\\<exists>x. P=Q x)";
by (meson_tac 1); 
result();

writeln"Problem 22";
Goal "(\\<forall>x. P = Q x)  -->  (P = (\\<forall>x. Q x))";
by (meson_tac 1); 
result();

writeln"Problem 23";
Goal "(\\<forall>x. P | Q x)  =  (P | (\\<forall>x. Q x))";
by (meson_tac 1);  
result();

writeln"Problem 24";  (*The first goal clause is useless*)
Goal "~(\\<exists>x. S x & Q x) & (\\<forall>x. P x --> Q x | R x) &  \
\     (~(\\<exists>x. P x) --> (\\<exists>x. Q x)) & (\\<forall>x. Q x | R x --> S x)  \
\   --> (\\<exists>x. P x & R x)";
by (meson_tac 1); 
result();

writeln"Problem 25";
Goal "(\\<exists>x. P x) &  \
\     (\\<forall>x. L x --> ~ (M x & R x)) &  \
\     (\\<forall>x. P x --> (M x & L x)) &   \
\     ((\\<forall>x. P x --> Q x) | (\\<exists>x. P x & R x))  \
\   --> (\\<exists>x. Q x & P x)";
by (meson_tac 1); 
result();

writeln"Problem 26";  (*24 Horn clauses*)
Goal "((\\<exists>x. p x) = (\\<exists>x. q x)) &     \
\     (\\<forall>x. \\<forall>y. p x & q y --> (r x = s y)) \
\ --> ((\\<forall>x. p x --> r x) = (\\<forall>x. q x --> s x))";
by (meson_tac 1); 
result();

writeln"Problem 27";    (*13 Horn clauses*)
Goal "(\\<exists>x. P x & ~Q x) &   \
\     (\\<forall>x. P x --> R x) &   \
\     (\\<forall>x. M x & L x --> P x) &   \
\     ((\\<exists>x. R x & ~ Q x) --> (\\<forall>x. L x --> ~ R x))  \
\     --> (\\<forall>x. M x --> ~L x)";
by (meson_tac 1); 
result();

writeln"Problem 28.  AMENDED";  (*14 Horn clauses*)
Goal "(\\<forall>x. P x --> (\\<forall>x. Q x)) &   \
\     ((\\<forall>x. Q x | R x) --> (\\<exists>x. Q x & S x)) &  \
\     ((\\<exists>x. S x) --> (\\<forall>x. L x --> M x))  \
\   --> (\\<forall>x. P x & L x --> M x)";
by (meson_tac 1);  
result();

writeln"Problem 29.  Essentially the same as Principia Mathematica *11.71";
        (*62 Horn clauses*)
Goal "(\\<exists>x. F x) & (\\<exists>y. G y)  \
\   --> ( ((\\<forall>x. F x --> H x) & (\\<forall>y. G y --> J y))  =   \
\         (\\<forall>x y. F x & G y --> H x & J y))";
by (meson_tac 1);          (*0.7 secs*)
result();

writeln"Problem 30";
Goal "(\\<forall>x. P x | Q x --> ~ R x) & \
\     (\\<forall>x. (Q x --> ~ S x) --> P x & R x)  \
\   --> (\\<forall>x. S x)";
by (meson_tac 1);  
result();

writeln"Problem 31";  (*10 Horn clauses; first negative clauses is useless*)
Goal "~(\\<exists>x. P x & (Q x | R x)) & \
\     (\\<exists>x. L x & P x) & \
\     (\\<forall>x. ~ R x --> M x)  \
\   --> (\\<exists>x. L x & M x)";
by (meson_tac 1);
result();

writeln"Problem 32";
Goal "(\\<forall>x. P x & (Q x | R x)-->S x) & \
\     (\\<forall>x. S x & R x --> L x) & \
\     (\\<forall>x. M x --> R x)  \
\   --> (\\<forall>x. P x & M x --> L x)";
by (meson_tac 1);
result();

writeln"Problem 33";  (*55 Horn clauses*)
Goal "(\\<forall>x. P a & (P x --> P b)-->P c)  =    \
\     (\\<forall>x. (~P a | P x | P c) & (~P a | ~P b | P c))";
by (meson_tac 1);          (*5.6 secs*)
result();

writeln"Problem 34  AMENDED (TWICE!!)"; (*924 Horn clauses*)
(*Andrews's challenge*)
Goal "((\\<exists>x. \\<forall>y. p x = p y)  =               \
\      ((\\<exists>x. q x) = (\\<forall>y. p y)))     =       \
\     ((\\<exists>x. \\<forall>y. q x = q y)  =               \
\      ((\\<exists>x. p x) = (\\<forall>y. q y)))";
by (meson_tac 1);          (*13 secs*)
result();

writeln"Problem 35";
Goal "\\<exists>x y. P x y -->  (\\<forall>u v. P u v)";
by (meson_tac 1);
result();

writeln"Problem 36";  (*15 Horn clauses*)
Goal "(\\<forall>x. \\<exists>y. J x y) & \
\     (\\<forall>x. \\<exists>y. G x y) & \
\     (\\<forall>x y. J x y | G x y -->       \
\     (\\<forall>z. J y z | G y z --> H x z))   \
\   --> (\\<forall>x. \\<exists>y. H x y)";
by (meson_tac 1);
result();

writeln"Problem 37";  (*10 Horn clauses*)
Goal "(\\<forall>z. \\<exists>w. \\<forall>x. \\<exists>y. \
\          (P x z --> P y w) & P y z & (P y w --> (\\<exists>u. Q u w))) & \
\     (\\<forall>x z. ~P x z --> (\\<exists>y. Q y z)) & \
\     ((\\<exists>x y. Q x y) --> (\\<forall>x. R x x))  \
\   --> (\\<forall>x. \\<exists>y. R x y)";
by (meson_tac 1);   (*causes unification tracing messages*)
result();

writeln"Problem 38";  (*Quite hard: 422 Horn clauses!!*)
Goal "(\\<forall>x. p a & (p x --> (\\<exists>y. p y & r x y)) -->            \
\          (\\<exists>z. \\<exists>w. p z & r x w & r w z))  =                 \
\     (\\<forall>x. (~p a | p x | (\\<exists>z. \\<exists>w. p z & r x w & r w z)) &  \
\           (~p a | ~(\\<exists>y. p y & r x y) |                      \
\            (\\<exists>z. \\<exists>w. p z & r x w & r w z)))";
by (safe_best_meson_tac 1);  (*10 secs; iter. deepening is slightly slower*)
result();

writeln"Problem 39";
Goal "~ (\\<exists>x. \\<forall>y. F y x = (~F y y))";
by (meson_tac 1);
result();

writeln"Problem 40.  AMENDED";
Goal "(\\<exists>y. \\<forall>x. F x y = F x x)  \
\     -->  ~ (\\<forall>x. \\<exists>y. \\<forall>z. F z y = (~F z x))";
by (meson_tac 1);
result();

writeln"Problem 41";
Goal "(\\<forall>z. (\\<exists>y. (\\<forall>x. f x y = (f x z & ~ f x x))))    \
\     --> ~ (\\<exists>z. \\<forall>x. f x z)";
by (meson_tac 1);
result();

writeln"Problem 42";
Goal "~ (\\<exists>y. \\<forall>x. p x y = (~ (\\<exists>z. p x z & p z x)))";
by (meson_tac 1);
result();

writeln"Problem 43  NOW PROVED AUTOMATICALLY!!";
Goal "(\\<forall>x. \\<forall>y. q x y = (\\<forall>z. p z x = (p z y::bool)))  \
\     --> (\\<forall>x. (\\<forall>y. q x y = (q y x::bool)))";
by (safe_best_meson_tac 1);     
(*1.6 secs; iter. deepening is slightly slower*)
result();

writeln"Problem 44";  (*13 Horn clauses; 7-step proof*)
Goal "(\\<forall>x. f x -->                                    \
\           (\\<exists>y. g y & h x y & (\\<exists>y. g y & ~ h x y)))  &   \
\     (\\<exists>x. j x & (\\<forall>y. g y --> h x y))               \
\     --> (\\<exists>x. j x & ~f x)";
by (meson_tac 1);
result();

writeln"Problem 45";  (*27 Horn clauses; 54-step proof*)
Goal "(\\<forall>x. f x & (\\<forall>y. g y & h x y --> j x y)        \
\           --> (\\<forall>y. g y & h x y --> k y)) &       \
\     ~ (\\<exists>y. l y & k y) &                                    \
\     (\\<exists>x. f x & (\\<forall>y. h x y --> l y)                        \
\               & (\\<forall>y. g y & h x y --> j x y))             \
\     --> (\\<exists>x. f x & ~ (\\<exists>y. g y & h x y))";
by (safe_best_meson_tac 1);     
(*1.6 secs; iter. deepening is slightly slower*)
result();

writeln"Problem 46";  (*26 Horn clauses; 21-step proof*)
Goal "(\\<forall>x. f x & (\\<forall>y. f y & h y x --> g y) --> g x) &      \
\     ((\\<exists>x. f x & ~g x) -->                                    \
\     (\\<exists>x. f x & ~g x & (\\<forall>y. f y & ~g y --> j x y))) &    \
\     (\\<forall>x y. f x & f y & h x y --> ~j y x)                    \
\     --> (\\<forall>x. f x --> g x)";
by (safe_best_meson_tac 1);     
(*1.7 secs; iter. deepening is slightly slower*)
result();

writeln"Problem 47.  Schubert's Steamroller";
        (*26 clauses; 63 Horn clauses
          87094 inferences so far.  Searching to depth 36*)
Goal "(\\<forall>x. P1 x --> P0 x) & (\\<exists>x. P1 x) &     \
\     (\\<forall>x. P2 x --> P0 x) & (\\<exists>x. P2 x) &     \
\     (\\<forall>x. P3 x --> P0 x) & (\\<exists>x. P3 x) &     \
\     (\\<forall>x. P4 x --> P0 x) & (\\<exists>x. P4 x) &     \
\     (\\<forall>x. P5 x --> P0 x) & (\\<exists>x. P5 x) &     \
\     (\\<forall>x. Q1 x --> Q0 x) & (\\<exists>x. Q1 x) &     \
\     (\\<forall>x. P0 x --> ((\\<forall>y. Q0 y-->R x y) |    \
\                      (\\<forall>y. P0 y & S y x &     \
\                           (\\<exists>z. Q0 z&R y z) --> R x y))) &   \
\     (\\<forall>x y. P3 y & (P5 x|P4 x) --> S x y) &        \
\     (\\<forall>x y. P3 x & P2 y --> S x y) &        \
\     (\\<forall>x y. P2 x & P1 y --> S x y) &        \
\     (\\<forall>x y. P1 x & (P2 y|Q1 y) --> ~R x y) &       \
\     (\\<forall>x y. P3 x & P4 y --> R x y) &        \
\     (\\<forall>x y. P3 x & P5 y --> ~R x y) &       \
\     (\\<forall>x. (P4 x|P5 x) --> (\\<exists>y. Q0 y & R x y))      \
\     --> (\\<exists>x y. P0 x & P0 y & (\\<exists>z. Q1 z & R y z & R x y))";
by (safe_best_meson_tac 1);     (*MUCH faster than iterative deepening*)
result();

(*The Los problem\\<exists> Circulated by John Harrison*)
Goal "(\\<forall>x y z. P x y & P y z --> P x z) &      \
\     (\\<forall>x y z. Q x y & Q y z --> Q x z) &             \
\     (\\<forall>x y. P x y --> P y x) &                       \
\     (\\<forall>x y. P x y | Q x y)                           \
\     --> (\\<forall>x y. P x y) | (\\<forall>x y. Q x y)";
by (safe_best_meson_tac 1);     (*2.3 secs; iter. deepening is VERY slow*)
result();

(*A similar example, suggested by Johannes Schumann and credited to Pelletier*)
Goal "(!x y z. P x y --> P y z --> P x z) --> \
\     (!x y z. Q x y --> Q y z --> Q x z) --> \
\     (!x y. Q x y --> Q y x) -->  (!x y. P x y | Q x y) --> \
\     (!x y. P x y) | (!x y. Q x y)";
by (safe_best_meson_tac 1);          (*2.7 secs*)
result();

writeln"Problem 50";  
(*What has this to do with equality?*)
Goal "(\\<forall>x. P a x | (\\<forall>y. P x y)) --> (\\<exists>x. \\<forall>y. P x y)";
by (meson_tac 1);
result();

writeln"Problem 55";

(*Non-equational version, from Manthey and Bry, CADE-9 (Springer, 1988).
  meson_tac cannot report who killed Agatha. *)
Goal "lives agatha & lives butler & lives charles & \
\     (killed agatha agatha | killed butler agatha | killed charles agatha) & \
\     (!x y. killed x y --> hates x y & ~richer x y) & \
\     (!x. hates agatha x --> ~hates charles x) & \
\     (hates agatha agatha & hates agatha charles) & \
\     (!x. lives x & ~richer x agatha --> hates butler x) & \
\     (!x. hates agatha x --> hates butler x) & \
\     (!x. ~hates x agatha | ~hates x butler | ~hates x charles) --> \
\     (\\<exists>x. killed x agatha)";
by (meson_tac 1);
result();

writeln"Problem 57";
Goal "P (f a b) (f b c) & P (f b c) (f a c) & \
\     (\\<forall>x y z. P x y & P y z --> P x z)    -->   P (f a b) (f a c)";
by (meson_tac 1);
result();

writeln"Problem 58";
(* Challenge found on info-hol *)
Goal "\\<forall>P Q R x. \\<exists>v w. \\<forall>y z. P x & Q y --> (P v | R w) & (R z --> Q v)";
by (meson_tac 1);
result();

writeln"Problem 59";
Goal "(\\<forall>x. P x = (~P(f x))) --> (\\<exists>x. P x & ~P(f x))";
by (meson_tac 1);
result();

writeln"Problem 60";
Goal "\\<forall>x. P x (f x) = (\\<exists>y. (\\<forall>z. P z y --> P z (f x)) & P x y)";
by (meson_tac 1);
result();

writeln"Problem 62 as corrected in JAR 18 (1997), page 135";
Goal "(ALL x. p a & (p x --> p(f x)) --> p(f(f x)))  =   \
\     (ALL x. (~ p a | p x | p(f(f x))) &                        \
\             (~ p a | ~ p(f x) | p(f(f x))))";
by (meson_tac 1);
result();


(** Charles Morgan's problems **)

val axa = "\\<forall>x y.   T(i x(i y x))";
val axb = "\\<forall>x y z. T(i(i x(i y z))(i(i x y)(i x z)))";
val axc = "\\<forall>x y.   T(i(i(n x)(n y))(i y x))";
val axd = "\\<forall>x y.   T(i x y) & T x --> T y";

fun axjoin ([],   q) = q
  | axjoin (p::ps, q) = "(" ^ p ^ ") --> (" ^ axjoin(ps,q) ^ ")";

Goal (axjoin([axa,axb,axd], "\\<forall>x. T(i x x)"));
by (meson_tac 1);  
result();

writeln"Problem 66";  
Goal (axjoin([axa,axb,axc,axd], "\\<forall>x. T(i x(n(n x)))"));
(*TOO SLOW, several minutes\\<forall> 
     208346 inferences so far.  Searching to depth 23
by (meson_tac 1);
result();
*)

writeln"Problem 67";  
Goal (axjoin([axa,axb,axc,axd], "\\<forall>x. T(i(n(n x)) x)"));
(*TOO SLOW: more than 3 minutes!
  51061 inferences so far.  Searching to depth 21
by (meson_tac 1);
result();
*)


(*Restore original values*)
Unify.trace_bound := orig_trace_bound;
Unify.search_bound := orig_search_bound;

writeln"Reached end of file.";

(*26 August 1992: loaded in 277 secs.  New Jersey v 75*)
