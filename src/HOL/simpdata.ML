(*  Title:      HOL/simpdata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1991  University of Cambridge

Instantiation of the generic simplifier for HOL.
*)

(* legacy ML bindings - FIXME get rid of this *)

val Eq_FalseI = thm "Eq_FalseI";
val Eq_TrueI = thm "Eq_TrueI";
val de_Morgan_conj = thm "de_Morgan_conj";
val de_Morgan_disj = thm "de_Morgan_disj";
val iff_conv_conj_imp = thm "iff_conv_conj_imp";
val imp_cong = thm "imp_cong";
val imp_conv_disj = thm "imp_conv_disj";
val imp_disj1 = thm "imp_disj1";
val imp_disj2 = thm "imp_disj2";
val imp_disjL = thm "imp_disjL";
val simp_impliesI = thm "simp_impliesI";
val simp_implies_cong = thm "simp_implies_cong";
val simp_implies_def = thm "simp_implies_def";

local
  val uncurry = thm "uncurry"
  val iff_allI = thm "iff_allI"
  val iff_exI = thm "iff_exI"
  val all_comm = thm "all_comm"
  val ex_comm = thm "ex_comm"
in

(*** make simplification procedures for quantifier elimination ***)

structure Quantifier1 = Quantifier1Fun
(struct
  (*abstract syntax*)
  fun dest_eq((c as Const("op =",_)) $ s $ t) = SOME(c,s,t)
    | dest_eq _ = NONE;
  fun dest_conj((c as Const("op &",_)) $ s $ t) = SOME(c,s,t)
    | dest_conj _ = NONE;
  fun dest_imp((c as Const("op -->",_)) $ s $ t) = SOME(c,s,t)
    | dest_imp _ = NONE;
  val conj = HOLogic.conj
  val imp  = HOLogic.imp
  (*rules*)
  val iff_reflection = HOL.eq_reflection
  val iffI = HOL.iffI
  val iff_trans = HOL.trans
  val conjI= HOL.conjI
  val conjE= HOL.conjE
  val impI = HOL.impI
  val mp   = HOL.mp
  val uncurry = uncurry
  val exI  = HOL.exI
  val exE  = HOL.exE
  val iff_allI = iff_allI
  val iff_exI = iff_exI
  val all_comm = all_comm
  val ex_comm = ex_comm
end);

end;

val defEX_regroup =
  Simplifier.simproc (the_context ())
    "defined EX" ["EX x. P x"] Quantifier1.rearrange_ex;

val defALL_regroup =
  Simplifier.simproc (the_context ())
    "defined ALL" ["ALL x. P x"] Quantifier1.rearrange_all;


(* simproc for proving "(y = x) == False" from premise "~(x = y)" *)

val use_neq_simproc = ref true;

local
  val neq_to_EQ_False = thm "not_sym" RS Eq_FalseI;
  fun neq_prover sg ss (eq $ lhs $ rhs) =
    let
      fun test thm = (case #prop (rep_thm thm) of
                    _ $ (Not $ (eq' $ l' $ r')) =>
                      Not = HOLogic.Not andalso eq' = eq andalso
                      r' aconv lhs andalso l' aconv rhs
                  | _ => false)
    in if !use_neq_simproc then case find_first test (prems_of_ss ss)
     of NONE => NONE
      | SOME thm => SOME (thm RS neq_to_EQ_False)
     else NONE
    end
in

val neq_simproc = Simplifier.simproc (the_context ())
  "neq_simproc" ["x = y"] neq_prover;

end;


(* Simproc for Let *)

val use_let_simproc = ref true;

local
  val Let_folded = thm "Let_folded";
  val Let_unfold = thm "Let_unfold";
  val (f_Let_unfold,x_Let_unfold) =
      let val [(_$(f$x)$_)] = prems_of Let_unfold
      in (cterm_of (the_context ()) f,cterm_of (the_context ()) x) end
  val (f_Let_folded,x_Let_folded) =
      let val [(_$(f$x)$_)] = prems_of Let_folded
      in (cterm_of (the_context ()) f, cterm_of (the_context ()) x) end;
  val g_Let_folded =
      let val [(_$_$(g$_))] = prems_of Let_folded in cterm_of (the_context ()) g end;
in

val let_simproc =
  Simplifier.simproc (the_context ()) "let_simp" ["Let x f"]
   (fn sg => fn ss => fn t =>
     let val ctxt = Simplifier.the_context ss;
         val ([t'],ctxt') = Variable.import_terms false [t] ctxt;
     in Option.map (hd o Variable.export ctxt' ctxt o single)
      (case t' of (Const ("Let",_)$x$f) => (* x and f are already in normal form *)
         if not (!use_let_simproc) then NONE
         else if is_Free x orelse is_Bound x orelse is_Const x
         then SOME (thm "Let_def")
         else
          let
             val n = case f of (Abs (x,_,_)) => x | _ => "x";
             val cx = cterm_of sg x;
             val {T=xT,...} = rep_cterm cx;
             val cf = cterm_of sg f;
             val fx_g = Simplifier.rewrite ss (Thm.capply cf cx);
             val (_$_$g) = prop_of fx_g;
             val g' = abstract_over (x,g);
           in (if (g aconv g')
               then
                  let
                    val rl = cterm_instantiate [(f_Let_unfold,cf),(x_Let_unfold,cx)] Let_unfold;
                  in SOME (rl OF [fx_g]) end
               else if Term.betapply (f,x) aconv g then NONE (*avoid identity conversion*)
               else let
                     val abs_g'= Abs (n,xT,g');
                     val g'x = abs_g'$x;
                     val g_g'x = symmetric (beta_conversion false (cterm_of sg g'x));
                     val rl = cterm_instantiate
                               [(f_Let_folded,cterm_of sg f),(x_Let_folded,cx),
                                (g_Let_folded,cterm_of sg abs_g')]
                               Let_folded;
                   in SOME (rl OF [transitive fx_g g_g'x])
                   end)
           end
        | _ => NONE)
     end)

end

(*** Case splitting ***)

(*Make meta-equalities.  The operator below is Trueprop*)

fun mk_meta_eq r = r RS HOL.eq_reflection;
fun safe_mk_meta_eq r = mk_meta_eq r handle Thm.THM _ => r;

fun mk_eq th = case concl_of th of
        Const("==",_)$_$_       => th
    |   _$(Const("op =",_)$_$_) => mk_meta_eq th
    |   _$(Const("Not",_)$_)    => th RS Eq_FalseI
    |   _                       => th RS Eq_TrueI;
(* Expects Trueprop(.) if not == *)

fun mk_eq_True r =
  SOME (r RS HOL.meta_eq_to_obj_eq RS Eq_TrueI) handle Thm.THM _ => NONE;

(* Produce theorems of the form
  (P1 =simp=> ... =simp=> Pn => x == y) ==> (P1 =simp=> ... =simp=> Pn => x = y)
*)
fun lift_meta_eq_to_obj_eq i st =
  let
    val {sign, ...} = rep_thm st;
    fun count_imp (Const ("HOL.simp_implies", _) $ P $ Q) = 1 + count_imp Q
      | count_imp _ = 0;
    val j = count_imp (Logic.strip_assums_concl (List.nth (prems_of st, i - 1)))
  in if j = 0 then HOL.meta_eq_to_obj_eq
    else
      let
        val Ps = map (fn k => Free ("P" ^ string_of_int k, propT)) (1 upto j);
        fun mk_simp_implies Q = foldr (fn (R, S) =>
          Const ("HOL.simp_implies", propT --> propT --> propT) $ R $ S) Q Ps
        val aT = TFree ("'a", HOLogic.typeS);
        val x = Free ("x", aT);
        val y = Free ("y", aT)
      in Goal.prove_global (Thm.theory_of_thm st) []
        [mk_simp_implies (Logic.mk_equals (x, y))]
        (mk_simp_implies (HOLogic.mk_Trueprop (HOLogic.mk_eq (x, y))))
        (fn prems => EVERY
         [rewrite_goals_tac [simp_implies_def],
          REPEAT (ares_tac (HOL.meta_eq_to_obj_eq :: map (rewrite_rule [simp_implies_def]) prems) 1)])
      end
  end;

(*Congruence rules for = (instead of ==)*)
fun mk_meta_cong rl = zero_var_indexes
  (let val rl' = Seq.hd (TRYALL (fn i => fn st =>
     rtac (lift_meta_eq_to_obj_eq i st) i st) rl)
   in mk_meta_eq rl' handle THM _ =>
     if can Logic.dest_equals (concl_of rl') then rl'
     else error "Conclusion of congruence rules must be =-equality"
   end);

structure SplitterData =
struct
  structure Simplifier = Simplifier
  val mk_eq          = mk_eq
  val meta_eq_to_iff = HOL.meta_eq_to_obj_eq
  val iffD           = HOL.iffD2
  val disjE          = HOL.disjE
  val conjE          = HOL.conjE
  val exE            = HOL.exE
  val contrapos      = HOL.contrapos_nn
  val contrapos2     = HOL.contrapos_pp
  val notnotD        = HOL.notnotD
end;

structure Splitter = SplitterFun(SplitterData);

val split_tac        = Splitter.split_tac;
val split_inside_tac = Splitter.split_inside_tac;
val split_asm_tac    = Splitter.split_asm_tac;
val op addsplits     = Splitter.addsplits;
val op delsplits     = Splitter.delsplits;
val Addsplits        = Splitter.Addsplits;
val Delsplits        = Splitter.Delsplits;

val mksimps_pairs =
  [("op -->", [HOL.mp]), ("op &", [thm "conjunct1", thm "conjunct2"]),
   ("All", [HOL.spec]), ("True", []), ("False", []),
   ("HOL.If", [thm "if_bool_eq_conj" RS HOL.iffD1])];

(*
val mk_atomize:      (string * thm list) list -> thm -> thm list
looks too specific to move it somewhere else
*)
fun mk_atomize pairs =
  let fun atoms th =
        (case concl_of th of
           Const("Trueprop",_) $ p =>
             (case head_of p of
                Const(a,_) =>
                  (case AList.lookup (op =) pairs a of
                     SOME(rls) => List.concat (map atoms ([th] RL rls))
                   | NONE => [th])
              | _ => [th])
         | _ => [th])
  in atoms end;

fun mksimps pairs =
  (List.mapPartial (try mk_eq) o mk_atomize pairs o gen_all);

fun unsafe_solver_tac prems =
  (fn i => REPEAT_DETERM (match_tac [simp_impliesI] i)) THEN'
  FIRST'[resolve_tac(reflexive_thm :: HOL.TrueI :: HOL.refl :: prems), atac, etac HOL.FalseE];
val unsafe_solver = mk_solver "HOL unsafe" unsafe_solver_tac;

(*No premature instantiation of variables during simplification*)
fun safe_solver_tac prems =
  (fn i => REPEAT_DETERM (match_tac [simp_impliesI] i)) THEN'
  FIRST'[match_tac(reflexive_thm :: HOL.TrueI :: HOL.refl :: prems),
         eq_assume_tac, ematch_tac [HOL.FalseE]];
val safe_solver = mk_solver "HOL safe" safe_solver_tac;

val HOL_basic_ss =
  Simplifier.theory_context (the_context ()) empty_ss
    setsubgoaler asm_simp_tac
    setSSolver safe_solver
    setSolver unsafe_solver
    setmksimps (mksimps mksimps_pairs)
    setmkeqTrue mk_eq_True
    setmkcong mk_meta_cong;

fun unfold_tac ths =
  let val ss0 = Simplifier.clear_ss HOL_basic_ss addsimps ths
  in fn ss => ALLGOALS (full_simp_tac (Simplifier.inherit_context ss ss0)) end;

(*In general it seems wrong to add distributive laws by default: they
  might cause exponential blow-up.  But imp_disjL has been in for a while
  and cannot be removed without affecting existing proofs.  Moreover,
  rewriting by "(P|Q --> R) = ((P-->R)&(Q-->R))" might be justified on the
  grounds that it allows simplification of R in the two cases.*)

local
  val ex_simps = thms "ex_simps";
  val all_simps = thms "all_simps";
  val simp_thms = thms "simp_thms";
  val cases_simp = thm "cases_simp";
  val conj_assoc = thm "conj_assoc";
  val if_False = thm "if_False";
  val if_True = thm "if_True";
  val disj_assoc = thm "disj_assoc";
  val disj_not1 = thm "disj_not1";
  val if_cancel = thm "if_cancel";
  val if_eq_cancel = thm "if_eq_cancel";
  val True_implies_equals = thm "True_implies_equals";
in

val HOL_ss =
    HOL_basic_ss addsimps
     ([triv_forall_equality, (* prunes params *)
       True_implies_equals, (* prune asms `True' *)
       if_True, if_False, if_cancel, if_eq_cancel,
       imp_disjL, conj_assoc, disj_assoc,
       de_Morgan_conj, de_Morgan_disj, imp_disj1, imp_disj2, thm "not_imp",
       disj_not1, thm "not_all", thm "not_ex", cases_simp,
       thm "the_eq_trivial", HOL.the_sym_eq_trivial]
     @ ex_simps @ all_simps @ simp_thms)
     addsimprocs [defALL_regroup,defEX_regroup,neq_simproc,let_simproc]
     addcongs [imp_cong, simp_implies_cong]
     addsplits [thm "split_if"];

end;

fun hol_simplify rews = Simplifier.full_simplify (HOL_basic_ss addsimps rews);

(* default simpset *)
val simpsetup =
  (fn thy => (change_simpset_of thy (fn _ => HOL_ss); thy));


(*** integration of simplifier with classical reasoner ***)

structure Clasimp = ClasimpFun
 (structure Simplifier = Simplifier and Splitter = Splitter
  and Classical  = Classical and Blast = Blast
  val iffD1 = HOL.iffD1 val iffD2 = HOL.iffD2 val notE = HOL.notE);
open Clasimp;

val HOL_css = (HOL_cs, HOL_ss);



(*** A general refutation procedure ***)

(* Parameters:

   test: term -> bool
   tests if a term is at all relevant to the refutation proof;
   if not, then it can be discarded. Can improve performance,
   esp. if disjunctions can be discarded (no case distinction needed!).

   prep_tac: int -> tactic
   A preparation tactic to be applied to the goal once all relevant premises
   have been moved to the conclusion.

   ref_tac: int -> tactic
   the actual refutation tactic. Should be able to deal with goals
   [| A1; ...; An |] ==> False
   where the Ai are atomic, i.e. no top-level &, | or EX
*)

local
  val nnf_simpset =
    empty_ss setmkeqTrue mk_eq_True
    setmksimps (mksimps mksimps_pairs)
    addsimps [imp_conv_disj,iff_conv_conj_imp,de_Morgan_disj,de_Morgan_conj,
      thm "not_all", thm "not_ex", thm "not_not"];
  fun prem_nnf_tac i st =
    full_simp_tac (Simplifier.theory_context (Thm.theory_of_thm st) nnf_simpset) i st;
in
fun refute_tac test prep_tac ref_tac =
  let val refute_prems_tac =
        REPEAT_DETERM
              (eresolve_tac [HOL.conjE, HOL.exE] 1 ORELSE
               filter_prems_tac test 1 ORELSE
               etac HOL.disjE 1) THEN
        ((etac HOL.notE 1 THEN eq_assume_tac 1) ORELSE
         ref_tac 1);
  in EVERY'[TRY o filter_prems_tac test,
            REPEAT_DETERM o etac HOL.rev_mp, prep_tac, rtac HOL.ccontr, prem_nnf_tac,
            SELECT_GOAL (DEPTH_SOLVE refute_prems_tac)]
  end;
end;
