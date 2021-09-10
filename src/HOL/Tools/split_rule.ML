(*  Title:      HOL/Tools/split_rule.ML
    Author:     Stefan Berghofer, David von Oheimb, and Markus Wenzel, TU Muenchen

Some tools for managing tupled arguments and abstractions in rules.
*)

signature SPLIT_RULE =
sig
  val split_rule_var: Proof.context -> term -> thm -> thm
  val split_rule: Proof.context -> thm -> thm
  val complete_split_rule: Proof.context -> thm -> thm
end;

structure Split_Rule: SPLIT_RULE =
struct

(** split rules **)

fun internal_case_prod_const (Ta, Tb, Tc) =
  Const (\<^const_name>\<open>Product_Type.internal_case_prod\<close>,
    [[Ta, Tb] ---> Tc, HOLogic.mk_prodT (Ta, Tb)] ---> Tc);

fun eval_internal_split ctxt =
  hol_simplify ctxt @{thms internal_case_prod_def} o
  hol_simplify ctxt @{thms internal_case_prod_conv};

fun remove_internal_split ctxt = eval_internal_split ctxt o split_all ctxt;


(*In ap_split S T u, term u expects separate arguments for the factors of S,
  with result type T.  The call creates a new term expecting one argument
  of type S.*)
fun ap_split (Type (\<^type_name>\<open>Product_Type.prod\<close>, [T1, T2])) T3 u =
      internal_case_prod_const (T1, T2, T3) $
      Abs ("v", T1,
          ap_split T2 T3
             ((ap_split T1 (HOLogic.flatten_tupleT T2 ---> T3) (incr_boundvars 1 u)) $
              Bound 0))
  | ap_split _ T3 u = u;

(*Curries any Var of function type in the rule*)
fun split_rule_var' ctxt (t as Var (v, Type ("fun", [T1, T2]))) rl =
      let val T' = HOLogic.flatten_tupleT T1 ---> T2;
          val newt = ap_split T1 T2 (Var (v, T'));
      in Thm.instantiate (TVars.empty, Vars.make [(dest_Var t, Thm.cterm_of ctxt newt)]) rl end
  | split_rule_var' _ _ rl = rl;


(* complete splitting of partially split rules *)

fun ap_split' (T::Ts) U u = Abs ("v", T, ap_split' Ts U
      (ap_split T (maps HOLogic.flatten_tupleT Ts ---> U)
        (incr_boundvars 1 u) $ Bound 0))
  | ap_split' _ _ u = u;

fun complete_split_rule_var ctxt (t as Var (v, T), ts) (rl, vs) =
      let
        val (Us', U') = strip_type T;
        val Us = take (length ts) Us';
        val U = drop (length ts) Us' ---> U';
        val T' = maps HOLogic.flatten_tupleT Us ---> U;
        fun mk_tuple (v as Var ((a, _), T)) (xs, insts) =
              let
                val Ts = HOLogic.flatten_tupleT T;
                val ys = Name.variant_list xs (replicate (length Ts) a);
              in
                (xs @ ys,
                  (dest_Var v,
                    Thm.cterm_of ctxt (HOLogic.mk_ptuple (HOLogic.flat_tupleT_paths T) T
                      (map (Var o apfst (rpair 0)) (ys ~~ Ts)))) :: insts)
              end
          | mk_tuple _ x = x;
        val newt = ap_split' Us U (Var (v, T'));
        val (vs', insts) = fold mk_tuple ts (vs, []);
      in
        (Drule.instantiate_normalize
          (TVars.empty, Vars.make (((v, T), Thm.cterm_of ctxt newt) :: insts)) rl, vs')
      end
  | complete_split_rule_var _ _ x = x;

fun collect_vars (Abs (_, _, t)) = collect_vars t
  | collect_vars t =
      (case strip_comb t of
        (v as Var _, ts) => cons (v, ts)
      | (_, ts) => fold collect_vars ts);


fun split_rule_var ctxt =
  (Drule.export_without_context o remove_internal_split ctxt) oo split_rule_var' ctxt;

(*curries ALL function variables occurring in a rule's conclusion*)
fun split_rule ctxt rl =
  fold_rev (split_rule_var' ctxt) (Misc_Legacy.term_vars (Thm.concl_of rl)) rl
  |> remove_internal_split ctxt
  |> Drule.export_without_context;

(*curries ALL function variables*)
fun complete_split_rule ctxt rl =
  let
    val prop = Thm.prop_of rl;
    val xs = Term.fold_aterms (fn Var ((x, _), _) => insert (op =) x | _ => I) prop [];
    val vars = collect_vars prop [];
  in
    fst (fold_rev (complete_split_rule_var ctxt) vars (rl, xs))
    |> remove_internal_split ctxt
    |> Drule.export_without_context
    |> Rule_Cases.save rl
  end;


(* attribute syntax *)

val _ =
  Theory.setup
   (Attrib.setup \<^binding>\<open>split_format\<close>
      (Scan.lift (Args.parens (Args.$$$ "complete")
        >> K (Thm.rule_attribute [] (complete_split_rule o Context.proof_of))))
      "split pair-typed subterms in premises, or function arguments" #>
    Attrib.setup \<^binding>\<open>split_rule\<close>
      (Scan.succeed (Thm.rule_attribute [] (split_rule o Context.proof_of)))
      "curries ALL function variables occurring in a rule's conclusion");

end;

