(* 
    File:	 Intensional.ML
    Author:      Stephan Merz
    Copyright:   1998 University of Munich

Lemmas and tactics for "intensional" logics.
*)

val intensional_rews = [unl_con,unl_lift,unl_lift2,unl_lift3,unl_Rall,unl_Rex,unl_Rex1];

qed_goalw "inteq_reflection" Intensional.thy  [Valid_def,unl_lift2]
  "|- x=y  ==>  (x==y)"
  (fn [prem] => [rtac eq_reflection 1, rtac ext 1, rtac (prem RS spec) 1 ]);

qed_goalw "intI" Intensional.thy [Valid_def] "(!!w. w |= A) ==> |- A"
  (fn [prem] => [REPEAT (resolve_tac [allI,prem] 1)]);

qed_goalw "intD" Intensional.thy [Valid_def] "|- A ==> w |= A"
  (fn [prem] => [rtac (prem RS spec) 1]);


(** Lift usual HOL simplifications to "intensional" level. **)
local

fun prover s = (prove_goal Intensional.thy s 
                 (fn _ => [rewrite_goals_tac (Valid_def::intensional_rews), 
                           blast_tac HOL_cs 1])) RS inteq_reflection

in

val int_simps = map prover
 [ "|- (x=x) = #True",
   "|- (~#True) = #False", "|- (~#False) = #True", "|- (~~ P) = P",
   "|- ((~P) = P) = #False", "|- (P = (~P)) = #False", 
   "|- (P ~= Q) = (P = (~Q))",
   "|- (#True=P) = P", "|- (P=#True) = P",
   "|- (#True --> P) = P", "|- (#False --> P) = #True", 
   "|- (P --> #True) = #True", "|- (P --> P) = #True",
   "|- (P --> #False) = (~P)", "|- (P --> ~P) = (~P)",
   "|- (P & #True) = P", "|- (#True & P) = P", 
   "|- (P & #False) = #False", "|- (#False & P) = #False", 
   "|- (P & P) = P", "|- (P & ~P) = #False", "|- (~P & P) = #False",
   "|- (P | #True) = #True", "|- (#True | P) = #True", 
   "|- (P | #False) = P", "|- (#False | P) = P", 
   "|- (P | P) = P", "|- (P | ~P) = #True", "|- (~P | P) = #True",
   "|- (! x. P) = P", "|- (? x. P) = P", 
   "|- (~Q --> ~P) = (P --> Q)",
   "|- (P|Q --> R) = ((P-->R)&(Q-->R))" ];
end;

qed_goal "TrueW" Intensional.thy "|- #True"
  (fn _ => [simp_tac (simpset() addsimps [Valid_def,unl_con]) 1]);

Addsimps (TrueW::intensional_rews);
Addsimps int_simps;
AddSIs [intI];
AddDs  [intD];


(* ======== Functions to "unlift" intensional implications into HOL rules ====== *)

(* Basic unlifting introduces a parameter "w" and applies basic rewrites, e.g.
   |- F = G    becomes   F w = G w
   |- F --> G  becomes   F w --> G w
*)

fun int_unlift th =
  rewrite_rule intensional_rews ((th RS intD) handle _ => th);

(* Turn  |- F = G  into meta-level rewrite rule  F == G *)
fun int_rewrite th = 
    zero_var_indexes (rewrite_rule intensional_rews (th RS inteq_reflection));

(* flattening turns "-->" into "==>" and eliminates conjunctions in the
   antecedent. For example,

         P & Q --> (R | S --> T)    becomes   [| P; Q; R | S |] ==> T

   Flattening can be useful with "intensional" lemmas (after unlifting).
   Naive resolution with mp and conjI may run away because of higher-order
   unification, therefore the code is a little awkward.
*)
fun flatten t =
  let 
    (* analogous to RS, but using matching instead of resolution *)
    fun matchres tha i thb =
      case Seq.chop (2, biresolution true [(false,tha)] i thb) of
	  ([th],_) => th
	| ([],_)   => raise THM("matchres: no match", i, [tha,thb])
	|      _   => raise THM("matchres: multiple unifiers", i, [tha,thb])

    (* match tha with some premise of thb *)
    fun matchsome tha thb =
      let fun hmatch 0 = raise THM("matchsome: no match", 0, [tha,thb])
	    | hmatch n = (matchres tha n thb) handle _ => hmatch (n-1)
      in hmatch (nprems_of thb) end

    fun hflatten t =
        case (concl_of t) of
          Const _ $ (Const ("op -->", _) $ _ $ _) => hflatten (t RS mp)
        | _ => (hflatten (matchsome conjI t)) handle _ => zero_var_indexes t
  in
    hflatten t
end;

fun int_use th =
    case (concl_of th) of
      Const _ $ (Const ("Intensional.Valid", _) $ _) =>
              ((flatten (int_unlift th)) handle _ => th)
    | _ => th;

(***
(* Make the simplifier accept "intensional" goals by either turning them into
   a meta-equality or by unlifting them.
*)

let 
  val ss = simpset_ref()
  fun try_rewrite th = (int_rewrite th) handle _ => (int_use th) handle _ => th
in 
  ss := !ss setmksimps ((mksimps mksimps_pairs) o try_rewrite)
end;
***)

(* ========================================================================= *)

qed_goal "Not_Rall" Intensional.thy
   "|- (~(! x. F x)) = (? x. ~F x)"
   (fn _ => [simp_tac (simpset() addsimps [Valid_def]) 1]);

qed_goal "Not_Rex" Intensional.thy
   "|- (~ (? x. F x)) = (! x. ~ F x)"
   (fn _ => [simp_tac (simpset() addsimps [Valid_def]) 1]);

(* IntLemmas.ML contains a collection of further lemmas about "intensional" logic.
   These are not loaded by default because they are not required for the
   standard proof procedures that first unlift proof goals to the HOL level.

use "IntLemmas.ML";

*)
