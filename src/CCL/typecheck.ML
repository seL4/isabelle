(*  Title: 	CCL/typecheck
    ID:         $Id$
    Author: 	Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

*)

(*** Lemmas for constructors and subtypes ***)

(* 0-ary constructors do not need additional rules as they are handled *)
(*                                      correctly by applying SubtypeI *)
(*
val Subtype_canTs = 
       let fun tac prems = cut_facts_tac prems 1 THEN
                REPEAT (ares_tac (SubtypeI::canTs@icanTs) 1 ORELSE
                        etac SubtypeE 1)
           fun solve s = prove_goal Type.thy s (fn prems => [tac prems])
       in map solve
           ["P(one) ==> one : {x:Unit.P(x)}",
            "P(true) ==> true : {x:Bool.P(x)}",
            "P(false) ==> false : {x:Bool.P(x)}",
            "a : {x:A. b:{y:B(a).P(<x,y>)}} ==> <a,b> : {x:Sigma(A,B).P(x)}",
            "a : {x:A.P(inl(x))} ==> inl(a) : {x:A+B.P(x)}",
            "b : {x:B.P(inr(x))} ==> inr(b) : {x:A+B.P(x)}",
            "P(zero) ==> zero : {x:Nat.P(x)}",
            "a : {x:Nat.P(succ(x))} ==> succ(a) : {x:Nat.P(x)}",
            "P([]) ==> [] : {x:List(A).P(x)}",
            "h : {x:A. t : {y:List(A).P(x$y)}} ==> h$t : {x:List(A).P(x)}"
        ] end;
*)
val Subtype_canTs = 
       let fun tac prems = cut_facts_tac prems 1 THEN
                REPEAT (ares_tac (SubtypeI::canTs@icanTs) 1 ORELSE
                        etac SubtypeE 1)
           fun solve s = prove_goal Type.thy s (fn prems => [tac prems])
       in map solve
           ["a : {x:A. b:{y:B(a).P(<x,y>)}} ==> <a,b> : {x:Sigma(A,B).P(x)}",
            "a : {x:A.P(inl(x))} ==> inl(a) : {x:A+B.P(x)}",
            "b : {x:B.P(inr(x))} ==> inr(b) : {x:A+B.P(x)}",
            "a : {x:Nat.P(succ(x))} ==> succ(a) : {x:Nat.P(x)}",
            "h : {x:A. t : {y:List(A).P(x$y)}} ==> h$t : {x:List(A).P(x)}"
        ] end;

val prems = goal Type.thy
     "[| f(t):B;  ~t=bot  |] ==> let x be t in f(x) : B";
by (cut_facts_tac prems 1);
by (etac (letB RS ssubst) 1);
by (assume_tac 1);
val letT = result();

val prems = goal Type.thy
     "[| a:A;  f : Pi(A,B)  |] ==> f ` a  : B(a)";
by (REPEAT (ares_tac (applyT::prems) 1));
val applyT2 = result();

val prems = goal Type.thy 
    "[| a:A;  a:A ==> P(a) |] ==> a : {x:A.P(x)}";
by (fast_tac (type_cs addSIs prems) 1);
val rcall_lemma1 = result();

val prems = goal Type.thy 
    "[| a:{x:A.Q(x)};  [| a:A; Q(a) |] ==> P(a) |] ==> a : {x:A.P(x)}";
by (cut_facts_tac prems 1);
by (fast_tac (type_cs addSIs prems) 1);
val rcall_lemma2 = result();

val rcall_lemmas = [asm_rl,rcall_lemma1,SubtypeD1,rcall_lemma2];

(***********************************TYPECHECKING*************************************)

fun bvars (Const("all",_) $ Abs(s,_,t)) l = bvars t (s::l)
  | bvars _ l = l;

fun get_bno l n (Const("all",_) $ Abs(s,_,t)) = get_bno (s::l) n t 
  | get_bno l n (Const("Trueprop",_) $ t) = get_bno l n t
  | get_bno l n (Const("Ball",_) $ _ $ Abs(s,_,t)) = get_bno (s::l) (n+1) t
  | get_bno l n (Const("op :",_) $ t $ _) = get_bno l n t
  | get_bno l n (t $ s) = get_bno l n t
  | get_bno l n (Bound m) = (m-length(l),n);

(* Not a great way of identifying induction hypothesis! *)
fun could_IH x = could_unify(x,hd (prems_of rcallT)) orelse
                 could_unify(x,hd (prems_of rcall2T)) orelse
                 could_unify(x,hd (prems_of rcall3T));

fun IHinst tac rls i = STATE (fn state =>
  let val (_,_,Bi,_) = dest_state(state,i);
      val bvs = bvars Bi [];
      val ihs = filter could_IH (Logic.strip_assums_hyp Bi);
      val rnames = map (fn x=>
                    let val (a,b) = get_bno [] 0 x
                    in (nth_elem(a,bvs),b) end) ihs;
      fun try_IHs [] = no_tac
        | try_IHs ((x,y)::xs) = tac [("g",x)] (nth_elem(y-1,rls)) i ORELSE (try_IHs xs);
  in try_IHs rnames end);

(*****)

val type_rls = canTs@icanTs@(applyT2::ncanTs)@incanTs@
               precTs@letrecTs@[letT]@Subtype_canTs;

fun is_rigid_prog t = 
     case (Logic.strip_assums_concl t) of 
        (Const("Trueprop",_) $ (Const("op :",_) $ a $ _)) => (term_vars a = [])
       | _ => false;

fun rcall_tac i = let fun tac ps rl i = res_inst_tac ps rl i THEN atac i;
                       in IHinst tac rcallTs i end THEN
                  eresolve_tac rcall_lemmas i;

fun raw_step_tac prems i = ares_tac (prems@type_rls) i ORELSE
                           rcall_tac i ORELSE
                           ematch_tac [SubtypeE] i ORELSE
                           match_tac [SubtypeI] i;

fun tc_step_tac prems i = STATE(fn state =>
          if (i>length(prems_of state)) 
             then no_tac
             else let val (_,_,c,_) = dest_state(state,i)
                  in if is_rigid_prog c then raw_step_tac prems i else no_tac
                  end);

fun typechk_tac rls i = SELECT_GOAL (REPEAT_FIRST (tc_step_tac rls)) i;

val tac = typechk_tac [] 1;


(*** Clean up Correctness Condictions ***)

val clean_ccs_tac = REPEAT_FIRST (eresolve_tac ([SubtypeE]@rmIHs) ORELSE'
                                 hyp_subst_tac);

val clean_ccs_tac = 
       let fun tac ps rl i = eres_inst_tac ps rl i THEN atac i;
       in TRY (REPEAT_FIRST (IHinst tac hyprcallTs ORELSE'
                       eresolve_tac ([asm_rl,SubtypeE]@rmIHs) ORELSE'
                       hyp_subst_tac)) end;

fun gen_ccs_tac rls i = SELECT_GOAL (REPEAT_FIRST (tc_step_tac rls) THEN
                                     clean_ccs_tac) i;


