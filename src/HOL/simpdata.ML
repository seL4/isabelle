(*  Title:      HOL/simpdata.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1991  University of Cambridge

Instantiation of the generic simplifier for HOL.
*)

(** tools setup **)

structure Quantifier1 = Quantifier1Fun
(struct
  (*abstract syntax*)
  fun dest_eq ((c as Const("op =",_)) $ s $ t) = SOME (c, s, t)
    | dest_eq _ = NONE;
  fun dest_conj ((c as Const("op &",_)) $ s $ t) = SOME (c, s, t)
    | dest_conj _ = NONE;
  fun dest_imp ((c as Const("op -->",_)) $ s $ t) = SOME (c, s, t)
    | dest_imp _ = NONE;
  val conj = HOLogic.conj
  val imp  = HOLogic.imp
  (*rules*)
  val iff_reflection = thm "eq_reflection"
  val iffI = thm "iffI"
  val iff_trans = thm "trans"
  val conjI= thm "conjI"
  val conjE= thm "conjE"
  val impI = thm "impI"
  val mp   = thm "mp"
  val uncurry = thm "uncurry"
  val exI  = thm "exI"
  val exE  = thm "exE"
  val iff_allI = thm "iff_allI"
  val iff_exI = thm "iff_exI"
  val all_comm = thm "all_comm"
  val ex_comm = thm "ex_comm"
end);

structure Simpdata =
struct

local
  val eq_reflection = thm "eq_reflection"
in fun mk_meta_eq r = r RS eq_reflection end;
fun safe_mk_meta_eq r = mk_meta_eq r handle Thm.THM _ => r;

local
  val Eq_FalseI = thm "Eq_FalseI"
  val Eq_TrueI = thm "Eq_TrueI"
in fun mk_eq th = case concl_of th
  (*expects Trueprop if not == *)
  of Const ("==",_) $ _ $ _ => th
   | _ $ (Const ("op =", _) $ _ $ _) => mk_meta_eq th
   | _ $ (Const ("Not", _) $ _) => th RS Eq_FalseI
   | _ => th RS Eq_TrueI
end;

local
  val meta_eq_to_obj_eq = thm "meta_eq_to_obj_eq"
  val Eq_TrueI = thm "Eq_TrueI"
in fun mk_eq_True r =
  SOME (r RS meta_eq_to_obj_eq RS Eq_TrueI) handle Thm.THM _ => NONE;
end;

(* Produce theorems of the form
  (P1 =simp=> ... =simp=> Pn => x == y) ==> (P1 =simp=> ... =simp=> Pn => x = y)
*)
local
  val meta_eq_to_obj_eq = thm "meta_eq_to_obj_eq"
  val simp_implies_def = thm "simp_implies_def"
in fun lift_meta_eq_to_obj_eq i st =
  let
    fun count_imp (Const ("HOL.simp_implies", _) $ P $ Q) = 1 + count_imp Q
      | count_imp _ = 0;
    val j = count_imp (Logic.strip_assums_concl (List.nth (prems_of st, i - 1)))
  in if j = 0 then meta_eq_to_obj_eq
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
          REPEAT (ares_tac (meta_eq_to_obj_eq :: map (rewrite_rule [simp_implies_def]) prems) 1)])
      end
  end;
end;

(*Congruence rules for = (instead of ==)*)
fun mk_meta_cong rl = zero_var_indexes
  (let val rl' = Seq.hd (TRYALL (fn i => fn st =>
     rtac (lift_meta_eq_to_obj_eq i st) i st) rl)
   in mk_meta_eq rl' handle THM _ =>
     if can Logic.dest_equals (concl_of rl') then rl'
     else error "Conclusion of congruence rules must be =-equality"
   end);

fun mk_atomize pairs =
  let
    fun atoms thm =
      let
        fun res th = map (fn rl => th RS rl);   (*exception THM*)
        fun res_fixed rls =
          if Thm.maxidx_of (Thm.adjust_maxidx_thm ~1 thm) = ~1 then res thm rls
          else Variable.trade (K (fn [thm'] => res thm' rls)) (Variable.thm_context thm) [thm];
      in
        case concl_of thm
          of Const ("Trueprop", _) $ p => (case head_of p
            of Const (a, _) => (case AList.lookup (op =) pairs a
              of SOME rls => (maps atoms (res_fixed rls) handle THM _ => [thm])
              | NONE => [thm])
            | _ => [thm])
          | _ => [thm]
      end;
  in atoms end;

fun mksimps pairs =
  map_filter (try mk_eq) o mk_atomize pairs o gen_all;

local
  val simp_impliesI = thm "simp_impliesI"
  val TrueI = thm "TrueI"
  val FalseE = thm "FalseE"
  val refl = thm "refl"
in fun unsafe_solver_tac prems =
  (fn i => REPEAT_DETERM (match_tac [simp_impliesI] i)) THEN'
  FIRST'[resolve_tac(reflexive_thm :: TrueI :: refl :: prems), atac, etac FalseE];
end;
val unsafe_solver = mk_solver "HOL unsafe" unsafe_solver_tac;

(*No premature instantiation of variables during simplification*)
local
  val simp_impliesI = thm "simp_impliesI"
  val TrueI = thm "TrueI"
  val FalseE = thm "FalseE"
  val refl = thm "refl"
in fun safe_solver_tac prems =
  (fn i => REPEAT_DETERM (match_tac [simp_impliesI] i)) THEN'
  FIRST'[match_tac(reflexive_thm :: TrueI :: refl :: prems),
         eq_assume_tac, ematch_tac [FalseE]];
end;
val safe_solver = mk_solver "HOL safe" safe_solver_tac;

structure SplitterData =
struct
  structure Simplifier = Simplifier
  val mk_eq           = mk_eq
  val meta_eq_to_iff  = thm "meta_eq_to_obj_eq"
  val iffD            = thm "iffD2"
  val disjE           = thm "disjE"
  val conjE           = thm "conjE"
  val exE             = thm "exE"
  val contrapos       = thm "contrapos_nn"
  val contrapos2      = thm "contrapos_pp"
  val notnotD         = thm "notnotD"
end;

structure Splitter = SplitterFun(SplitterData);

(* integration of simplifier with classical reasoner *)

structure Clasimp = ClasimpFun
 (structure Simplifier = Simplifier and Splitter = Splitter
  and Classical  = Classical and Blast = Blast
  val iffD1 = thm "iffD1" val iffD2 = thm "iffD2" val notE = thm "notE");

val mksimps_pairs =
  [("op -->", [thm "mp"]), ("op &", [thm "conjunct1", thm "conjunct2"]),
   ("All", [thm "spec"]), ("True", []), ("False", []),
   ("HOL.If", [thm "if_bool_eq_conj" RS thm "iffD1"])];

val simpset_basic =
  Simplifier.theory_context (the_context ()) empty_ss
    setsubgoaler asm_simp_tac
    setSSolver safe_solver
    setSolver unsafe_solver
    setmksimps (mksimps mksimps_pairs)
    setmkeqTrue mk_eq_True
    setmkcong mk_meta_cong;

fun simplify rews = Simplifier.full_simplify (simpset_basic addsimps rews);

fun unfold_tac ths =
  let val ss0 = Simplifier.clear_ss simpset_basic addsimps ths
  in fn ss => ALLGOALS (full_simp_tac (Simplifier.inherit_context ss ss0)) end;



(** simprocs **)

(* simproc for proving "(y = x) == False" from premise "~(x = y)" *)

val use_neq_simproc = ref true;

local
  val thy = the_context ();
  val neq_to_EQ_False = thm "not_sym" RS thm "Eq_FalseI";
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

val neq_simproc = Simplifier.simproc thy "neq_simproc" ["x = y"] neq_prover;

end;


(* simproc for Let *)

val use_let_simproc = ref true;

local
  val thy = the_context ();
  val Let_folded = thm "Let_folded";
  val Let_unfold = thm "Let_unfold";
  val Let_def = thm "Let_def";
  val (f_Let_unfold, x_Let_unfold) =
      let val [(_$(f$x)$_)] = prems_of Let_unfold
      in (cterm_of thy f, cterm_of thy x) end
  val (f_Let_folded, x_Let_folded) =
      let val [(_$(f$x)$_)] = prems_of Let_folded
      in (cterm_of thy f, cterm_of thy x) end;
  val g_Let_folded =
      let val [(_$_$(g$_))] = prems_of Let_folded in cterm_of thy g end;
in

val let_simproc =
  Simplifier.simproc thy "let_simp" ["Let x f"]
   (fn sg => fn ss => fn t =>
     let val ctxt = Simplifier.the_context ss;
         val ([t'], ctxt') = Variable.import_terms false [t] ctxt;
     in Option.map (hd o Variable.export ctxt' ctxt o single)
      (case t' of (Const ("Let",_)$x$f) => (* x and f are already in normal form *)
         if not (!use_let_simproc) then NONE
         else if is_Free x orelse is_Bound x orelse is_Const x
         then SOME Let_def
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

end;


(* generic refutation procedure *)

(* parameters:

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
  val conjE = thm "conjE"
  val exE = thm "exE"
  val disjE = thm "disjE"
  val notE = thm "notE"
  val rev_mp = thm "rev_mp"
  val ccontr = thm "ccontr"
  val nnf_simpset =
    empty_ss setmkeqTrue mk_eq_True
    setmksimps (mksimps mksimps_pairs)
    addsimps [thm "imp_conv_disj", thm "iff_conv_conj_imp", thm "de_Morgan_disj", thm "de_Morgan_conj",
      thm "not_all", thm "not_ex", thm "not_not"];
  fun prem_nnf_tac i st =
    full_simp_tac (Simplifier.theory_context (Thm.theory_of_thm st) nnf_simpset) i st;
in
fun refute_tac test prep_tac ref_tac =
  let val refute_prems_tac =
        REPEAT_DETERM
              (eresolve_tac [conjE, exE] 1 ORELSE
               filter_prems_tac test 1 ORELSE
               etac disjE 1) THEN
        ((etac notE 1 THEN eq_assume_tac 1) ORELSE
         ref_tac 1);
  in EVERY'[TRY o filter_prems_tac test,
            REPEAT_DETERM o etac rev_mp, prep_tac, rtac ccontr, prem_nnf_tac,
            SELECT_GOAL (DEPTH_SOLVE refute_prems_tac)]
  end;
end;

val defALL_regroup =
  Simplifier.simproc (the_context ())
    "defined ALL" ["ALL x. P x"] Quantifier1.rearrange_all;

val defEX_regroup =
  Simplifier.simproc (the_context ())
    "defined EX" ["EX x. P x"] Quantifier1.rearrange_ex;


val simpset_simprocs = simpset_basic
  addsimprocs [defALL_regroup, defEX_regroup, neq_simproc, let_simproc]

end;

structure Splitter = Simpdata.Splitter;
structure Clasimp = Simpdata.Clasimp;
