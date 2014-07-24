(*  Title:      HOL/Tools/Lifting/lifting_term.ML
    Author:     Ondrej Kuncar

Proves Quotient theorem.
*)

signature LIFTING_TERM =
sig
  exception QUOT_THM of typ * typ * Pretty.T
  exception PARAM_QUOT_THM of typ * Pretty.T
  exception MERGE_TRANSFER_REL of Pretty.T
  exception CHECK_RTY of typ * typ

  val instantiate_rtys: Proof.context -> typ * typ -> typ * typ

  val prove_quot_thm: Proof.context -> typ * typ -> thm

  val abs_fun: Proof.context -> typ * typ -> term

  val equiv_relation: Proof.context -> typ * typ -> term

  val prove_param_quot_thm: Proof.context -> typ -> thm * (typ * thm) list * Proof.context

  val generate_parametrized_relator: Proof.context -> typ -> term * term list

  val merge_transfer_relations: Proof.context -> cterm -> thm

  val parametrize_transfer_rule: Proof.context -> thm -> thm
end

structure Lifting_Term: LIFTING_TERM =
struct
open Lifting_Util

infix 0 MRSL

exception QUOT_THM_INTERNAL of Pretty.T
exception QUOT_THM of typ * typ * Pretty.T
exception PARAM_QUOT_THM of typ * Pretty.T
exception MERGE_TRANSFER_REL of Pretty.T
exception CHECK_RTY of typ * typ

fun match ctxt err ty_pat ty =
  let
    val thy = Proof_Context.theory_of ctxt
  in
    Sign.typ_match thy (ty_pat, ty) Vartab.empty
      handle Type.TYPE_MATCH => err ctxt ty_pat ty
  end

fun equiv_match_err ctxt ty_pat ty =
  let
    val ty_pat_str = Syntax.string_of_typ ctxt ty_pat
    val ty_str = Syntax.string_of_typ ctxt ty
  in
    raise QUOT_THM_INTERNAL (Pretty.block
      [Pretty.str ("The quotient type " ^ quote ty_str),
       Pretty.brk 1,
       Pretty.str ("and the quotient type pattern " ^ quote ty_pat_str),
       Pretty.brk 1,
       Pretty.str "don't match."])
  end

fun get_quot_data ctxt s =
  case Lifting_Info.lookup_quotients ctxt s of
    SOME qdata => qdata
  | NONE => raise QUOT_THM_INTERNAL (Pretty.block 
    [Pretty.str ("No quotient type " ^ quote s), 
     Pretty.brk 1, 
     Pretty.str "found."])

fun get_quot_thm ctxt s =
  let
    val thy = Proof_Context.theory_of ctxt
  in
    Thm.transfer thy (#quot_thm (get_quot_data ctxt s))
  end

fun has_pcrel_info ctxt s = is_some (#pcr_info (get_quot_data ctxt s))

fun get_pcrel_info ctxt s =
  case #pcr_info (get_quot_data ctxt s) of
    SOME pcr_info => pcr_info
  | NONE => raise QUOT_THM_INTERNAL (Pretty.block 
    [Pretty.str ("No parametrized correspondce relation for " ^ quote s), 
     Pretty.brk 1, 
     Pretty.str "found."])

fun get_pcrel_def ctxt s =
  let
    val thy = Proof_Context.theory_of ctxt
  in
    Thm.transfer thy (#pcrel_def (get_pcrel_info ctxt s))
  end

fun get_pcr_cr_eq ctxt s =
  let
    val thy = Proof_Context.theory_of ctxt
  in
    Thm.transfer thy (#pcr_cr_eq (get_pcrel_info ctxt s))
  end

fun get_rel_quot_thm ctxt s =
   let
    val thy = Proof_Context.theory_of ctxt
  in
    (case Lifting_Info.lookup_quot_maps ctxt s of
      SOME map_data => Thm.transfer thy (#rel_quot_thm map_data)
    | NONE => raise QUOT_THM_INTERNAL (Pretty.block 
      [Pretty.str ("No relator for the type " ^ quote s), 
       Pretty.brk 1,
       Pretty.str "found."]))
  end

fun get_rel_distr_rules ctxt s tm =
  let
    val thy = Proof_Context.theory_of ctxt
  in
    (case Lifting_Info.lookup_relator_distr_data ctxt s of
      SOME rel_distr_thm => (
        case tm of
          Const (@{const_name POS}, _) => map (Thm.transfer thy) (#pos_distr_rules rel_distr_thm)
          | Const (@{const_name NEG}, _) => map (Thm.transfer thy) (#neg_distr_rules rel_distr_thm)
      )
    | NONE => raise QUOT_THM_INTERNAL (Pretty.block 
      [Pretty.str ("No relator distr. data for the type " ^ quote s), 
       Pretty.brk 1,
       Pretty.str "found."]))
  end

fun is_id_quot thm = (prop_of thm = prop_of @{thm identity_quotient})

fun zip_Tvars ctxt type_name rty_Tvars qty_Tvars =
  case try (get_rel_quot_thm ctxt) type_name of
    NONE => rty_Tvars ~~ qty_Tvars
    | SOME rel_quot_thm =>
      let 
        fun quot_term_absT quot_term = 
          let 
            val (_, abs, _, _) = (dest_Quotient o HOLogic.dest_Trueprop) quot_term
          in
            fastype_of abs
          end

        fun equiv_univ_err ctxt ty_pat ty =
          let
            val ty_pat_str = Syntax.string_of_typ ctxt ty_pat
            val ty_str = Syntax.string_of_typ ctxt ty
          in
            raise QUOT_THM_INTERNAL (Pretty.block
              [Pretty.str ("The type " ^ quote ty_str),
               Pretty.brk 1,
               Pretty.str ("and the relator type pattern " ^ quote ty_pat_str),
               Pretty.brk 1,
               Pretty.str "don't unify."])
          end

        fun raw_match (TVar (v, S), T) subs =
              (case Vartab.defined subs v of
                false => Vartab.update_new (v, (S, T)) subs
              | true => subs)
          | raw_match (Type (_, Ts), Type (_, Us)) subs =
              raw_matches (Ts, Us) subs
          | raw_match _ subs = subs
        and raw_matches (T :: Ts, U :: Us) subs = raw_matches (Ts, Us) (raw_match (T, U) subs)
          | raw_matches _ subs = subs

        val rty = Type (type_name, rty_Tvars)
        val qty = Type (type_name, qty_Tvars)
        val rel_quot_thm_concl = (Logic.strip_imp_concl o prop_of) rel_quot_thm
        val schematic_rel_absT = quot_term_absT rel_quot_thm_concl;
        val thy = Proof_Context.theory_of ctxt
        val absT = rty --> qty
        val schematic_absT = 
          absT 
          |> Logic.type_map (singleton (Variable.polymorphic ctxt))
          |> Logic.incr_tvar (maxidx_of_typ schematic_rel_absT + 1) 
            (* because absT can already contain schematic variables from rty patterns *)
        val maxidx = Term.maxidx_of_typs [schematic_rel_absT, schematic_absT]
        val _ = Sign.typ_unify thy (schematic_rel_absT, schematic_absT) (Vartab.empty,maxidx)
          handle Type.TUNIFY => equiv_univ_err ctxt schematic_rel_absT schematic_absT
        val subs = raw_match (schematic_rel_absT, absT) Vartab.empty
        val rel_quot_thm_prems = (Logic.strip_imp_prems o prop_of) rel_quot_thm
      in
        map (dest_funT o 
             Envir.subst_type subs o
             quot_term_absT) 
          rel_quot_thm_prems
      end

fun rty_is_TVar ctxt qty = (is_TVar o fst o quot_thm_rty_qty o get_quot_thm ctxt o Tname) qty

fun instantiate_rtys ctxt (rty, (qty as Type (qty_name, _))) =
  let
    val quot_thm = get_quot_thm ctxt qty_name
    val (rty_pat, qty_pat) = quot_thm_rty_qty quot_thm

    fun inst_rty (Type (s, tys), Type (s', tys')) = 
        if s = s' then Type (s', map inst_rty (tys ~~ tys'))
        else raise QUOT_THM_INTERNAL (Pretty.block 
          [Pretty.str "The type",
           Pretty.brk 1,
           Syntax.pretty_typ ctxt rty,
           Pretty.brk 1,
           Pretty.str ("is not a raw type for the quotient type " ^ quote qty_name ^ ";"),
           Pretty.brk 1,
           Pretty.str "the correct raw type must be an instance of",
           Pretty.brk 1,
           Syntax.pretty_typ ctxt rty_pat])
      | inst_rty (t as Type (_, _), TFree _) = t
      | inst_rty ((TVar _), rty) = rty
      | inst_rty ((TFree _), rty) = rty
      | inst_rty (_, _) = error "check_raw_types: we should not be here"

    val qtyenv = match ctxt equiv_match_err qty_pat qty
  in
    (inst_rty (rty_pat, rty), Envir.subst_type qtyenv rty_pat)
  end
  | instantiate_rtys _ _ = error "instantiate_rtys: not Type"

fun prove_schematic_quot_thm ctxt (rty, qty) =
  let
    fun lifting_step (rty, qty) =
      let
        val (rty', rtyq) = instantiate_rtys ctxt (rty, qty)
        val (rty's, rtyqs) = if rty_is_TVar ctxt qty then ([rty'],[rtyq]) 
          else (Targs rty', Targs rtyq) 
        val args = map (prove_schematic_quot_thm ctxt) (rty's ~~ rtyqs)
      in
        if forall is_id_quot args
        then
          get_quot_thm ctxt (Tname qty)
        else
          let
            val quot_thm = get_quot_thm ctxt (Tname qty)
            val rel_quot_thm = if rty_is_TVar ctxt qty then the_single args else
              args MRSL (get_rel_quot_thm ctxt (Tname rty))
          in
            [rel_quot_thm, quot_thm] MRSL @{thm Quotient_compose}
         end
      end
  in
    (case (rty, qty) of
      (Type (s, tys), Type (s', tys')) =>
        if s = s'
        then
          let
            val args = map (prove_schematic_quot_thm ctxt) (zip_Tvars ctxt s tys tys')
          in
            if forall is_id_quot args
            then
              @{thm identity_quotient}
            else
              args MRSL (get_rel_quot_thm ctxt s)
          end
        else
          lifting_step (rty, qty)
      | (_, Type (s', tys')) => 
        (case try (get_quot_thm ctxt) s' of
          SOME quot_thm => 
            let
              val rty_pat = (fst o quot_thm_rty_qty) quot_thm
            in
              lifting_step (rty_pat, qty)              
            end
          | NONE =>
            let                                               
              val rty_pat = Type (s', map (fn _ => TFree ("a",[])) tys')
            in
              prove_schematic_quot_thm ctxt (rty_pat, qty)
            end)
      | _ => @{thm identity_quotient})
  end
  handle QUOT_THM_INTERNAL pretty_msg => raise QUOT_THM (rty, qty, pretty_msg)

fun force_qty_type thy qty quot_thm =
  let
    val (_, qty_schematic) = quot_thm_rty_qty quot_thm
    val match_env = Sign.typ_match thy (qty_schematic, qty) Vartab.empty
    fun prep_ty thy (x, (S, ty)) =
      (ctyp_of thy (TVar (x, S)), ctyp_of thy ty)
    val ty_inst = Vartab.fold (cons o (prep_ty thy)) match_env []
  in
    Thm.instantiate (ty_inst, []) quot_thm
  end

fun check_rty_type ctxt rty quot_thm =
  let  
    val thy = Proof_Context.theory_of ctxt
    val (rty_forced, _) = quot_thm_rty_qty quot_thm
    val rty_schematic = Logic.type_map (singleton (Variable.polymorphic ctxt)) rty
    val _ = Sign.typ_match thy (rty_schematic, rty_forced) Vartab.empty
      handle Type.TYPE_MATCH => raise CHECK_RTY (rty_schematic, rty_forced)
  in
    ()
  end

(*
  The function tries to prove that rty and qty form a quotient.

  Returns: Quotient theorem; an abstract type of the theorem is exactly
    qty, a representation type of the theorem is an instance of rty in general.
*)

fun prove_quot_thm ctxt (rty, qty) =
  let
    val thy = Proof_Context.theory_of ctxt
    val schematic_quot_thm = prove_schematic_quot_thm ctxt (rty, qty)
    val quot_thm = force_qty_type thy qty schematic_quot_thm
    val _ = check_rty_type ctxt rty quot_thm
  in
    quot_thm
  end

(*
  Computes the composed abstraction function for rty and qty.
*)

fun abs_fun ctxt (rty, qty) =
  quot_thm_abs (prove_quot_thm ctxt (rty, qty))

(*
  Computes the composed equivalence relation for rty and qty.
*)

fun equiv_relation ctxt (rty, qty) =
  quot_thm_rel (prove_quot_thm ctxt (rty, qty))

val get_fresh_Q_t =
  let
    val Q_t = @{term "Trueprop (Quotient R Abs Rep T)"}
    val frees_Q_t = Term.add_free_names Q_t []
    val tfrees_Q_t = rev (Term.add_tfree_names Q_t [])
  in
    fn ctxt =>
    let
      fun rename_free_var tab (Free (name, typ)) = Free (the_default name (AList.lookup op= tab name),typ)
        | rename_free_var _ t = t
      
      fun rename_free_vars tab = map_aterms (rename_free_var tab)
      
      fun rename_free_tvars tab =
        map_types (map_type_tfree (fn (name, sort) => TFree (the_default name (AList.lookup op= tab name), sort)))
      
      val (new_frees_Q_t, ctxt) = Variable.variant_fixes frees_Q_t ctxt
      val tab_frees = frees_Q_t ~~ new_frees_Q_t
      
      val (new_tfrees_Q_t, ctxt) = Variable.invent_types (replicate (length tfrees_Q_t) []) ctxt
      val tab_tfrees = tfrees_Q_t ~~ (fst o split_list) new_tfrees_Q_t

      val renamed_Q_t = rename_free_vars tab_frees Q_t
      val renamed_Q_t = rename_free_tvars tab_tfrees renamed_Q_t
    in
      (renamed_Q_t, ctxt)
    end
  end

(*
  For the given type, it proves a composed Quotient map theorem, where for each type variable
  extra Quotient assumption is generated. E.g., for 'a list it generates exactly
  the Quotient map theorem for the list type. The function generalizes this for the whole
  type universe. New fresh variables in the assumptions are fixed in the returned context.

  Returns: the composed Quotient map theorem and list mapping each type variable in ty
  to the corresponding assumption in the returned theorem.
*)

fun prove_param_quot_thm ctxt ty = 
  let 
    fun generate (ty as Type (s, tys)) (table_ctxt as (table, ctxt)) =
      if null tys 
      then 
        let 
          val thy = Proof_Context.theory_of ctxt
          val instantiated_id_quot_thm = instantiate' [SOME (ctyp_of thy ty)] [] @{thm identity_quotient}
        in
          (instantiated_id_quot_thm, (table, ctxt)) 
        end
      else
        let
          val (args, table_ctxt) = fold_map generate tys table_ctxt
        in
          (args MRSL (get_rel_quot_thm ctxt s), table_ctxt)
        end 
      | generate ty (table, ctxt) =
        if AList.defined (op=) table ty 
        then (the (AList.lookup (op=) table ty), (table, ctxt))
        else 
          let
            val thy = Proof_Context.theory_of ctxt
            val (Q_t, ctxt') = get_fresh_Q_t ctxt
            val Q_thm = Thm.assume (cterm_of thy Q_t)
            val table' = (ty, Q_thm)::table
          in
            (Q_thm, (table', ctxt'))
          end

    val (param_quot_thm, (table, ctxt)) = generate ty ([], ctxt)
  in
    (param_quot_thm, rev table, ctxt)
  end
  handle QUOT_THM_INTERNAL pretty_msg => raise PARAM_QUOT_THM (ty, pretty_msg)

(*
  It computes a parametrized relator for the given type ty. E.g., for 'a dlist:
  list_all2 ?R OO cr_dlist with parameters [?R].
  
  Returns: the definitional term and list of parameters (relations).
*)

fun generate_parametrized_relator ctxt ty =
  let
    val orig_ctxt = ctxt
    val (quot_thm, table, ctxt) = prove_param_quot_thm ctxt ty
    val parametrized_relator = quot_thm_crel quot_thm
    val args = map (fn (_, q_thm) => quot_thm_crel q_thm) table
    val exported_terms = Variable.exportT_terms ctxt orig_ctxt (parametrized_relator :: args)
  in
    (hd exported_terms, tl exported_terms)
  end

(* Parametrization *)

local
  fun get_lhs rule = (Thm.dest_fun o Thm.dest_arg o strip_imp_concl o cprop_of) rule;
  
  fun no_imp _ = raise CTERM ("no implication", []);
  
  infix 0 else_imp

  fun (cv1 else_imp cv2) ct =
    (cv1 ct
      handle THM _ => cv2 ct
        | CTERM _ => cv2 ct
        | TERM _ => cv2 ct
        | TYPE _ => cv2 ct);
  
  fun first_imp cvs = fold_rev (curry op else_imp) cvs no_imp
  
  fun rewr_imp rule ct = 
    let
      val rule1 = Thm.incr_indexes (#maxidx (Thm.rep_cterm ct) + 1) rule;
      val lhs_rule = get_lhs rule1;
      val rule2 = Thm.rename_boundvars (Thm.term_of lhs_rule) (Thm.term_of ct) rule1;
      val lhs_ct = Thm.dest_fun ct
    in
        Thm.instantiate (Thm.match (lhs_rule, lhs_ct)) rule2
          handle Pattern.MATCH => raise CTERM ("rewr_imp", [lhs_rule, lhs_ct])
   end
  
  fun rewrs_imp rules = first_imp (map rewr_imp rules)
in

  (*
    ctm - of the form "[POS|NEG] (par_R OO T) t f) ?X", where par_R is a parametricity transfer 
    relation for t and T is a transfer relation between t and f, which consists only from
    parametrized transfer relations (i.e., pcr_?) and equalities op=. POS or NEG encodes
    co-variance or contra-variance.
    
    The function merges par_R OO T using definitions of parametrized correspondence relations
    (e.g., (rel_S R) OO (pcr_T op=) --> pcr_T R using the definition pcr_T R = (rel_S R) OO cr_T).
  *)

  fun merge_transfer_relations ctxt ctm =
    let
      val ctm = Thm.dest_arg ctm
      val tm = term_of ctm
      val rel = (hd o get_args 2) tm
  
      fun same_constants (Const (n1,_)) (Const (n2,_)) = n1 = n2
        | same_constants _ _  = false
      
      fun prove_extra_assms ctxt ctm distr_rule =
        let
          fun prove_assm assm = try (Goal.prove ctxt [] [] (term_of assm))
            (fn _ => SOLVED' (REPEAT_ALL_NEW (resolve_tac (Transfer.get_transfer_raw ctxt))) 1)
  
          fun is_POS_or_NEG ctm =
            case (head_of o term_of o Thm.dest_arg) ctm of
              Const (@{const_name POS}, _) => true
              | Const (@{const_name NEG}, _) => true
              | _ => false
  
          val inst_distr_rule = rewr_imp distr_rule ctm
          val extra_assms = filter_out is_POS_or_NEG (cprems_of inst_distr_rule)
          val proved_assms = map_interrupt prove_assm extra_assms
        in
          Option.map (curry op OF inst_distr_rule) proved_assms
        end
        handle CTERM _ => NONE
  
      fun cannot_merge_error_msg () = Pretty.block
         [Pretty.str "Rewriting (merging) of this term has failed:",
          Pretty.brk 1,
          Syntax.pretty_term ctxt rel]
  
    in
      case get_args 2 rel of
          [Const (@{const_name "HOL.eq"}, _), _] => rewrs_imp @{thms neg_eq_OO pos_eq_OO} ctm
          | [_, Const (@{const_name "HOL.eq"}, _)] => rewrs_imp @{thms neg_OO_eq pos_OO_eq} ctm
          | [_, trans_rel] =>
            let
              val (rty', qty) = (relation_types o fastype_of) trans_rel
            in
              if same_type_constrs (rty', qty) then
                let
                  val distr_rules = get_rel_distr_rules ctxt ((fst o dest_Type) rty') (head_of tm)
                  val distr_rule = get_first (prove_extra_assms ctxt ctm) distr_rules
                in
                  case distr_rule of
                    NONE => raise MERGE_TRANSFER_REL (cannot_merge_error_msg ())
                    | SOME distr_rule =>  (map (merge_transfer_relations ctxt) (cprems_of distr_rule)) 
                      MRSL distr_rule
                end
              else
                let 
                  val pcrel_def = get_pcrel_def ctxt ((fst o dest_Type) qty)
                  val pcrel_const = (head_of o fst o Logic.dest_equals o prop_of) pcrel_def
                in
                  if same_constants pcrel_const (head_of trans_rel) then
                    let
                      val unfolded_ctm = Thm.rhs_of (Conv.arg1_conv (Conv.arg_conv (Conv.rewr_conv pcrel_def)) ctm)
                      val distr_rule = rewrs_imp @{thms POS_pcr_rule NEG_pcr_rule} unfolded_ctm
                      val result = (map (merge_transfer_relations ctxt) (cprems_of distr_rule)) MRSL distr_rule
                      val fold_pcr_rel = Conv.rewr_conv (Thm.symmetric pcrel_def)
                    in  
                      Conv.fconv_rule (HOLogic.Trueprop_conv (Conv.combination_conv 
                        (Conv.arg_conv (Conv.arg_conv fold_pcr_rel)) fold_pcr_rel)) result
                    end
                  else
                    raise MERGE_TRANSFER_REL (Pretty.str "Non-parametric correspondence relation used.")
                end
            end
    end
    handle QUOT_THM_INTERNAL pretty_msg => raise MERGE_TRANSFER_REL pretty_msg
end

(*
  It replaces cr_T by pcr_T op= in the transfer relation. For composed
  abstract types, it replaces T_rel R OO cr_T by pcr_T R. If the parametrized
  correspondce relation does not exist, the original relation is kept.

  thm - a transfer rule
*)

fun parametrize_transfer_rule ctxt thm =
  let
    fun parametrize_relation_conv ctm =
      let
        val (rty, qty) = (relation_types o fastype_of) (term_of ctm)
      in
        if same_type_constrs (rty, qty) then
          if forall op= (Targs rty ~~ Targs qty) then
            Conv.all_conv ctm
          else
            all_args_conv parametrize_relation_conv ctm
        else
          if is_Type qty then
            let
              val q = (fst o dest_Type) qty
            in
              let
                val (rty', rtyq) = instantiate_rtys ctxt (rty, qty)
                val (rty's, rtyqs) = if rty_is_TVar ctxt qty then ([rty'],[rtyq]) 
                  else (Targs rty', Targs rtyq)
              in
                if forall op= (rty's ~~ rtyqs) then
                  let
                    val pcr_cr_eq = (Thm.symmetric o mk_meta_eq) (get_pcr_cr_eq ctxt q)
                  in      
                    Conv.rewr_conv pcr_cr_eq ctm
                  end
                  handle QUOT_THM_INTERNAL _ => Conv.all_conv ctm
                else
                  if has_pcrel_info ctxt q then
                    let 
                      val pcrel_def = Thm.symmetric (get_pcrel_def ctxt q)
                    in
                      (Conv.rewr_conv pcrel_def then_conv all_args_conv parametrize_relation_conv) ctm
                    end
                  else Conv.arg1_conv (all_args_conv parametrize_relation_conv) ctm
              end  
            end
          else Conv.all_conv ctm
      end
    in
      Conv.fconv_rule (HOLogic.Trueprop_conv (Conv.fun2_conv parametrize_relation_conv)) thm
    end
end
