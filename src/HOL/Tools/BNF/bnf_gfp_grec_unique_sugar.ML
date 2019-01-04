(*  Title:      HOL/Tools/BNF/bnf_gfp_grec_unique_sugar.ML
    Author:     Jasmin Blanchette, Inria, LORIA, MPII
    Copyright   2016

Proof method for proving uniqueness of corecursive equations ("corec_unique").
*)

signature BNF_GFP_GREC_UNIQUE_SUGAR =
sig
  val corec_unique_tac: Proof.context -> int -> tactic
end;

structure BNF_GFP_Grec_Unique_Sugar : BNF_GFP_GREC_UNIQUE_SUGAR =
struct

open BNF_Util
open BNF_GFP_Grec
open BNF_GFP_Grec_Sugar_Util
open BNF_GFP_Grec_Sugar

fun corec_unique_tac ctxt =
  Subgoal.FOCUS (fn {context = ctxt, prems, concl, ...} =>
    let
      (* Workaround for odd name clash for goals with "x" in their context *)
      val (_, ctxt) = ctxt
        |> yield_singleton (mk_Frees "x") \<^typ>\<open>unit\<close>;

      val code_thm = (if null prems then error "No premise" else hd prems)
        |> Object_Logic.rulify ctxt;
      val code_goal = Thm.prop_of code_thm;

      val (fun_t, args) = strip_comb (fst (HOLogic.dest_eq (HOLogic.dest_Trueprop code_goal)))
        handle TERM _ => error "Wrong format for first premise";

      val _ = is_Free fun_t orelse
        error ("Expected free variable as function in premise, found " ^
          Syntax.string_of_term ctxt fun_t);
      val _ =
        (case filter_out is_Var args of
          [] => ()
        | arg :: _ =>
          error ("Expected universal variable as argument to function in premise, found " ^
            Syntax.string_of_term ctxt arg));

      val fun_T = fastype_of fun_t;
      val (arg_Ts, res_T) = strip_type fun_T;

      val num_args_in_concl = length (snd (strip_comb (fst (HOLogic.dest_eq
          (HOLogic.dest_Trueprop (Thm.term_of concl))))))
        handle TERM _ => error "Wrong format for conclusion";

      val (corec_info, corec_parse_info) =
        (case maybe_corec_info_of ctxt res_T of
          SOME (info as {buffer, ...}) => (info, corec_parse_info_of ctxt arg_Ts res_T buffer)
        | NONE => error ("No corecursor for " ^ quote (Syntax.string_of_typ ctxt res_T) ^
          " (use " ^ quote (#1 \<^command_keyword>\<open>coinduction_upto\<close>) ^ " to derive it)"));

      val Type (fpT_name, _) = res_T;

      val parsed_eq = parse_corec_equation ctxt [fun_t] code_goal;
      val explored_eq =
        explore_corec_equation ctxt false false "" fun_t corec_parse_info res_T parsed_eq;

      val ((_, corecUU_arg), _) = build_corecUU_arg_and_goals false fun_t explored_eq ctxt;
      val eq_corecUU = derive_eq_corecUU ctxt corec_info fun_t corecUU_arg code_thm;

      val unique' = derive_unique ctxt Morphism.identity code_goal corec_info fpT_name eq_corecUU
        |> funpow num_args_in_concl (fn thm => thm RS fun_cong);
    in
      HEADGOAL ((K all_tac APPEND' rtac ctxt sym) THEN' rtac ctxt unique' THEN'
        REPEAT_DETERM_N num_args_in_concl o rtac ctxt ext)
    end) ctxt THEN'
  etac ctxt thin_rl;

end;
