(*  Title:      HOL/Tools/split_rule.ML
    Author:     Stefan Berghofer, David von Oheimb, and Markus Wenzel, TU Muenchen

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
  val split_rule_var: term -> thm -> thm
  val split_rule_goal: Proof.context -> string list list -> thm -> thm
  val setup: theory -> theory
end;

structure SplitRule: SPLIT_RULE =
struct



(** theory context references **)

val split_conv = thm "split_conv";
val fst_conv = thm "fst_conv";
val snd_conv = thm "snd_conv";

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
             ((ap_split T1 (HOLogic.flatten_tupleT T2 ---> T3) (incr_boundvars 1 u)) $
              Bound 0))
  | ap_split T T3 u = u;

(*Curries any Var of function type in the rule*)
fun split_rule_var' (t as Var (v, Type ("fun", [T1, T2]))) rl =
      let val T' = HOLogic.flatten_tupleT T1 ---> T2;
          val newt = ap_split T1 T2 (Var (v, T'));
          val cterm = Thm.cterm_of (Thm.theory_of_thm rl);
      in Thm.instantiate ([], [(cterm t, cterm newt)]) rl end
  | split_rule_var' t rl = rl;


(* complete splitting of partially splitted rules *)

fun ap_split' (T::Ts) U u = Abs ("v", T, ap_split' Ts U
      (ap_split T (List.concat (map HOLogic.flatten_tupleT Ts) ---> U)
        (incr_boundvars 1 u) $ Bound 0))
  | ap_split' _ _ u = u;

fun complete_split_rule_var (t as Var (v, T), ts) (rl, vs) =
      let
        val cterm = Thm.cterm_of (Thm.theory_of_thm rl)
        val (Us', U') = strip_type T;
        val Us = Library.take (length ts, Us');
        val U = Library.drop (length ts, Us') ---> U';
        val T' = List.concat (map HOLogic.flatten_tupleT Us) ---> U;
        fun mk_tuple (v as Var ((a, _), T)) (xs, insts) =
              let
                val Ts = HOLogic.flatten_tupleT T;
                val ys = Name.variant_list xs (replicate (length Ts) a);
              in (xs @ ys, (cterm v, cterm (HOLogic.mk_tuple T
                (map (Var o apfst (rpair 0)) (ys ~~ Ts))))::insts)
              end
          | mk_tuple _ x = x;
        val newt = ap_split' Us U (Var (v, T'));
        val cterm = Thm.cterm_of (Thm.theory_of_thm rl);
        val (vs', insts) = fold mk_tuple ts (vs, []);
      in
        (instantiate ([], [(cterm t, cterm newt)] @ insts) rl, vs')
      end
  | complete_split_rule_var _ x = x;

fun collect_vars (Abs (_, _, t)) = collect_vars t
  | collect_vars t =
      (case strip_comb t of
        (v as Var _, ts) => cons (v, ts)
      | (t, ts) => fold collect_vars ts);


val split_rule_var = (Drule.standard o remove_internal_split) oo split_rule_var';

(*curries ALL function variables occurring in a rule's conclusion*)
fun split_rule rl =
  fold_rev split_rule_var' (OldTerm.term_vars (concl_of rl)) rl
  |> remove_internal_split
  |> Drule.standard;

(*curries ALL function variables*)
fun complete_split_rule rl =
  let
    val prop = Thm.prop_of rl;
    val xs = Term.fold_aterms (fn Var ((x, _), _) => insert (op =) x | _ => I) prop [];
    val vars = collect_vars prop [];
  in
    fst (fold_rev complete_split_rule_var vars (rl, xs))
    |> remove_internal_split
    |> Drule.standard
    |> RuleCases.save rl
  end;


fun pair_tac ctxt s =
  res_inst_tac ctxt [(("p", 0), s)] @{thm PairE}
  THEN' hyp_subst_tac
  THEN' K prune_params_tac;

val split_rule_ss = HOL_basic_ss addsimps [split_conv, fst_conv, snd_conv];

fun split_rule_goal ctxt xss rl =
  let
    fun one_split i s = Tactic.rule_by_tactic (pair_tac ctxt s i);
    fun one_goal (i, xs) = fold (one_split (i + 1)) xs;
  in
    rl
    |> fold_index one_goal xss
    |> Simplifier.full_simplify split_rule_ss
    |> Drule.standard
    |> RuleCases.save rl
  end;


(* attribute syntax *)

(* FIXME dynamically scoped due to Args.name_source/pair_tac *)

val setup =
  Attrib.setup @{binding split_format}
    (Scan.lift
     (Args.parens (Args.$$$ "complete") >> K (Thm.rule_attribute (K complete_split_rule)) ||
      OuterParse.and_list1 (Scan.repeat Args.name_source)
        >> (fn xss => Thm.rule_attribute (fn context =>
            split_rule_goal (Context.proof_of context) xss))))
    "split pair-typed subterms in premises, or function arguments" #>
  Attrib.setup @{binding split_rule} (Scan.succeed (Thm.rule_attribute (K split_rule)))
    "curries ALL function variables occurring in a rule's conclusion";

end;

structure BasicSplitRule: BASIC_SPLIT_RULE = SplitRule;
open BasicSplitRule;
