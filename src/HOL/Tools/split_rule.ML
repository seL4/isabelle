(*  Title:      Tools/split_rule.ML
    ID:         $Id$
    Author:     Stefan Berghofer, David von Oheimb, and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Some tools for managing tupled arguments and abstractions in rules.
*)

signature BASIC_SPLIT_RULE =
sig
  val split_rule: thm -> thm
  val complete_split_rule: thm -> thm
end;

signature SPLIT_RULE =
sig
  include BASIC_SPLIT_RULE
  val split_rule_var: term * thm -> thm
  val split_rule_goal: string list list -> thm -> thm
  val setup: (theory -> theory) list
end;

structure SplitRule: SPLIT_RULE =
struct


(** theory context references **)

fun internal_split_const (Ta, Tb, Tc) =
  Const ("Product_Type.internal_split", [[Ta, Tb] ---> Tc, HOLogic.mk_prodT (Ta, Tb)] ---> Tc);

val internal_split_def = thm "internal_split_def";
val internal_split_conv = thm "internal_split_conv";



(** split rules **)

val eval_internal_split = hol_simplify [internal_split_def] o hol_simplify [internal_split_conv];
val remove_internal_split = eval_internal_split o split_all;


(*In ap_split S T u, term u expects separate arguments for the factors of S,
  with result type T.  The call creates a new term expecting one argument
  of type S.*)
fun ap_split (Type ("*", [T1, T2])) T3 u =
      internal_split_const (T1, T2, T3) $
      Abs ("v", T1,
          ap_split T2 T3
             ((ap_split T1 (HOLogic.prodT_factors T2 ---> T3) (incr_boundvars 1 u)) $
              Bound 0))
  | ap_split T T3 u = u;

(*Curries any Var of function type in the rule*)
fun split_rule_var' (t as Var (v, Type ("fun", [T1, T2])), rl) =
      let val T' = HOLogic.prodT_factors T1 ---> T2;
          val newt = ap_split T1 T2 (Var (v, T'));
          val cterm = Thm.cterm_of (#sign (Thm.rep_thm rl));
      in Thm.instantiate ([], [(cterm t, cterm newt)]) rl end
  | split_rule_var' (t, rl) = rl;


(* complete splitting of partially splitted rules *)

fun ap_split' (T::Ts) U u = Abs ("v", T, ap_split' Ts U
      (ap_split T (flat (map HOLogic.prodT_factors Ts) ---> U)
        (incr_boundvars 1 u) $ Bound 0))
  | ap_split' _ _ u = u;

fun complete_split_rule_var ((t as Var (v, T), ts), (rl, vs)) =
      let
        val cterm = Thm.cterm_of (#sign (Thm.rep_thm rl))
        val (Us', U') = strip_type T;
        val Us = take (length ts, Us');
        val U = drop (length ts, Us') ---> U';
        val T' = flat (map HOLogic.prodT_factors Us) ---> U;
        fun mk_tuple ((xs, insts), v as Var ((a, _), T)) =
              let
                val Ts = HOLogic.prodT_factors T;
                val ys = Term.variantlist (replicate (length Ts) a, xs);
              in (xs @ ys, (cterm v, cterm (HOLogic.mk_tuple T
                (map (Var o apfst (rpair 0)) (ys ~~ Ts))))::insts)
              end
          | mk_tuple (x, _) = x;
        val newt = ap_split' Us U (Var (v, T'));
        val cterm = Thm.cterm_of (#sign (Thm.rep_thm rl));
        val (vs', insts) = foldl mk_tuple ((vs, []), ts);
      in
        (instantiate ([], [(cterm t, cterm newt)] @ insts) rl, vs')
      end
  | complete_split_rule_var (_, x) = x;

fun collect_vars (vs, Abs (_, _, t)) = collect_vars (vs, t)
  | collect_vars (vs, t) = (case strip_comb t of
        (v as Var _, ts) => (v, ts)::vs
      | (t, ts) => foldl collect_vars (vs, ts));


val split_rule_var = Drule.standard o remove_internal_split o split_rule_var';

(*curries ALL function variables occurring in a rule's conclusion*)
fun split_rule rl =
  foldr split_rule_var' (Term.term_vars (concl_of rl), rl)
  |> remove_internal_split
  |> Drule.standard;

fun complete_split_rule rl =
  fst (foldr complete_split_rule_var
    (collect_vars ([], concl_of rl),
      (rl, map (fst o fst o dest_Var) (Term.term_vars (#prop (Thm.rep_thm rl))))))
  |> remove_internal_split
  |> Drule.standard
  |> RuleCases.save rl;


val split_rule_ss = HOL_basic_ss addsimps [split_conv, fst_conv, snd_conv];

fun split_rule_goal xss rl =
  let
    fun one_split i (th, s) = Tactic.rule_by_tactic (pair_tac s i) th;
    fun one_goal (xs, i) th = foldl (one_split i) (th, xs);
  in
    Drule.standard (Simplifier.full_simplify split_rule_ss (Library.foldln one_goal xss rl))
    |> RuleCases.save rl
  end;


(* attribute syntax *)

fun split_format x = Attrib.syntax
  (Args.mode "complete" >> K (Drule.rule_attribute (K complete_split_rule)) ||
    Args.and_list1 (Scan.lift (Scan.repeat Args.name))
      >> (fn xss => Drule.rule_attribute (K (split_rule_goal xss)))) x;

val setup =
 [Attrib.add_attributes
  [("split_format", (split_format, split_format),
    "split pair-typed subterms in premises, or function arguments")]];

end;

structure BasicSplitRule: BASIC_SPLIT_RULE = SplitRule;
open BasicSplitRule;
