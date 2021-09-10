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

  type 'a fold_quot_thm = { constr: typ -> thm * 'a -> thm * 'a, lift: typ -> thm * 'a -> thm * 'a, 
  comp_lift: typ -> thm * 'a -> thm * 'a }

  type quotients = Lifting_Info.quotient Symtab.table
  
  val force_qty_type: Proof.context -> typ -> thm -> thm

  val prove_schematic_quot_thm: 'a fold_quot_thm -> quotients -> Proof.context -> 
    typ * typ -> 'a -> thm * 'a

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

type quotients = Lifting_Info.quotient Symtab.table

fun match ctxt err ty_pat ty =
  Sign.typ_match (Proof_Context.theory_of ctxt) (ty_pat, ty) Vartab.empty
    handle Type.TYPE_MATCH => err ctxt ty_pat ty

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

fun get_quot_data (quotients: quotients) s =
  case Symtab.lookup quotients s of
    SOME qdata => qdata
  | NONE => raise QUOT_THM_INTERNAL (Pretty.block 
    [Pretty.str ("No quotient type " ^ quote s), 
     Pretty.brk 1, 
     Pretty.str "found."])

fun get_quot_thm quotients ctxt s =
  Thm.transfer' ctxt (#quot_thm (get_quot_data quotients s))

fun has_pcrel_info quotients s = is_some (#pcr_info (get_quot_data quotients s))

fun get_pcrel_info quotients s =
  case #pcr_info (get_quot_data quotients s) of
    SOME pcr_info => pcr_info
  | NONE => raise QUOT_THM_INTERNAL (Pretty.block 
    [Pretty.str ("No parametrized correspondce relation for " ^ quote s), 
     Pretty.brk 1, 
     Pretty.str "found."])

fun get_pcrel_def quotients ctxt s =
  Thm.transfer' ctxt (#pcrel_def (get_pcrel_info quotients s))

fun get_pcr_cr_eq quotients ctxt s =
  Thm.transfer' ctxt (#pcr_cr_eq (get_pcrel_info quotients s))

fun get_rel_quot_thm ctxt s =
  (case Lifting_Info.lookup_quot_maps ctxt s of
    SOME map_data => Thm.transfer' ctxt (#rel_quot_thm map_data)
  | NONE => raise QUOT_THM_INTERNAL (Pretty.block 
      [Pretty.str ("No relator for the type " ^ quote s), 
       Pretty.brk 1,
       Pretty.str "found."]))
  
fun get_rel_distr_rules ctxt s tm =
  (case Lifting_Info.lookup_relator_distr_data ctxt s of
    SOME rel_distr_thm =>
      (case tm of
        Const (\<^const_name>\<open>POS\<close>, _) => map (Thm.transfer' ctxt) (#pos_distr_rules rel_distr_thm)
      | Const (\<^const_name>\<open>NEG\<close>, _) => map (Thm.transfer' ctxt) (#neg_distr_rules rel_distr_thm))
  | NONE => raise QUOT_THM_INTERNAL (Pretty.block
      [Pretty.str ("No relator distr. data for the type " ^ quote s), 
       Pretty.brk 1,
       Pretty.str "found."]))

fun is_id_quot thm = Thm.eq_thm_prop (thm, @{thm identity_quotient})

fun zip_Tvars ctxt0 type_name rty_Tvars qty_Tvars =
  case try (get_rel_quot_thm ctxt0) type_name of
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
        val rel_quot_thm_concl = (Logic.strip_imp_concl o Thm.prop_of) rel_quot_thm
        val schematic_rel_absT = quot_term_absT rel_quot_thm_concl;
        val absT = rty --> qty
        val schematic_absT = 
          absT 
          |> Logic.type_map (singleton (Variable.polymorphic ctxt0))
          |> Logic.incr_tvar (maxidx_of_typ schematic_rel_absT + 1) 
            (* because absT can already contain schematic variables from rty patterns *)
        val maxidx = Term.maxidx_of_typs [schematic_rel_absT, schematic_absT]
        val _ =
          Sign.typ_unify (Proof_Context.theory_of ctxt0) (schematic_rel_absT, schematic_absT)
            (Vartab.empty, maxidx)
          handle Type.TUNIFY => equiv_univ_err ctxt0 schematic_rel_absT schematic_absT
        val subs = raw_match (schematic_rel_absT, absT) Vartab.empty
        val rel_quot_thm_prems = (Logic.strip_imp_prems o Thm.prop_of) rel_quot_thm
      in
        map (dest_funT o Envir.subst_type subs o quot_term_absT) rel_quot_thm_prems
      end

fun gen_rty_is_TVar quotients ctxt qty =
  qty |> Tname |> get_quot_thm quotients ctxt
  |> quot_thm_rty_qty |> fst |> is_TVar

fun gen_instantiate_rtys quotients ctxt (rty, (qty as Type (qty_name, _))) =
  let
    val quot_thm = get_quot_thm quotients ctxt qty_name
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
  | gen_instantiate_rtys _ _ _ = error "gen_instantiate_rtys: not Type"

fun instantiate_rtys ctxt (rty, qty) = 
  gen_instantiate_rtys (Lifting_Info.get_quotients ctxt) ctxt (rty, qty)

type 'a fold_quot_thm = { constr: typ -> thm * 'a -> thm * 'a, lift: typ -> thm * 'a -> thm * 'a, 
  comp_lift: typ -> thm * 'a -> thm * 'a }

fun prove_schematic_quot_thm (actions: 'a fold_quot_thm) quotients ctxt (rty, qty) fold_val =
  let
    fun lifting_step (rty, qty) =
      let
        val (rty', rtyq) = gen_instantiate_rtys quotients ctxt (rty, qty)
        val (rty's, rtyqs) = if gen_rty_is_TVar quotients ctxt qty then ([rty'],[rtyq]) 
          else (Targs rty', Targs rtyq) 
        val (args, fold_val) = 
          fold_map (prove_schematic_quot_thm actions quotients ctxt) (rty's ~~ rtyqs) fold_val
      in
        if forall is_id_quot args
        then
          let
            val quot_thm = get_quot_thm quotients ctxt (Tname qty)
          in
            #lift actions qty (quot_thm, fold_val)
          end
        else
          let
            val quot_thm = get_quot_thm quotients ctxt (Tname qty)
            val rel_quot_thm = if gen_rty_is_TVar quotients ctxt qty then the_single args else
              args MRSL (get_rel_quot_thm ctxt (Tname rty))
            val comp_quot_thm = [rel_quot_thm, quot_thm] MRSL @{thm Quotient_compose}
          in
            #comp_lift actions qty (comp_quot_thm, fold_val)
         end
      end
  in
    (case (rty, qty) of
      (Type (s, tys), Type (s', tys')) =>
        if s = s'
        then
          let
            val (args, fold_val) = 
              fold_map (prove_schematic_quot_thm actions quotients ctxt) 
                (zip_Tvars ctxt s tys tys') fold_val
          in
            if forall is_id_quot args
            then
              (@{thm identity_quotient}, fold_val)
            else
              let
                val quot_thm = args MRSL (get_rel_quot_thm ctxt s)
              in
                #constr actions qty (quot_thm, fold_val)
              end
          end
        else
          lifting_step (rty, qty)
      | (_, Type (s', tys')) => 
        (case try (get_quot_thm quotients ctxt) s' of
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
              prove_schematic_quot_thm actions quotients ctxt (rty_pat, qty) fold_val
            end)
      | _ => (@{thm identity_quotient}, fold_val)
      )
  end
  handle QUOT_THM_INTERNAL pretty_msg => raise QUOT_THM (rty, qty, pretty_msg)

fun force_qty_type ctxt qty quot_thm =
  let
    val (_, qty_schematic) = quot_thm_rty_qty quot_thm
    val match_env = Sign.typ_match (Proof_Context.theory_of ctxt) (qty_schematic, qty) Vartab.empty
    fun prep_ty (x, (S, ty)) = ((x, S), Thm.ctyp_of ctxt ty)
    val ty_inst = Vartab.fold (cons o prep_ty) match_env []
  in Thm.instantiate (TVars.make ty_inst, Vars.empty) quot_thm end

fun check_rty_type ctxt rty quot_thm =
  let  
    val (rty_forced, _) = quot_thm_rty_qty quot_thm
    val rty_schematic = Logic.type_map (singleton (Variable.polymorphic ctxt)) rty
    val _ = Sign.typ_match (Proof_Context.theory_of ctxt) (rty_schematic, rty_forced) Vartab.empty
      handle Type.TYPE_MATCH => raise CHECK_RTY (rty_schematic, rty_forced)
  in () end

(*
  The function tries to prove that rty and qty form a quotient.

  Returns: Quotient theorem; an abstract type of the theorem is exactly
    qty, a representation type of the theorem is an instance of rty in general.
*)


local
  val id_actions = { constr = K I, lift = K I, comp_lift = K I }
in
  fun prove_quot_thm ctxt (rty, qty) =
    let
      val quotients = Lifting_Info.get_quotients ctxt
      val (schematic_quot_thm, _) = prove_schematic_quot_thm id_actions quotients ctxt (rty, qty) ()
      val quot_thm = force_qty_type ctxt qty schematic_quot_thm
      val _ = check_rty_type ctxt rty quot_thm
    in quot_thm end
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
    val Q_t = \<^term>\<open>Trueprop (Quotient R Abs Rep T)\<close>
    val frees_Q_t = Term.add_free_names Q_t []
    val tfrees_Q_t = rev (Term.add_tfree_names Q_t [])
  in
    fn ctxt =>
      let
        fun rename_free_var tab (Free (name, typ)) =
              Free (the_default name (AList.lookup op= tab name), typ)
          | rename_free_var _ t = t

        fun rename_free_vars tab = map_aterms (rename_free_var tab)

        fun rename_free_tvars tab =
          map_types (map_type_tfree (fn (name, sort) =>
            TFree (the_default name (AList.lookup op= tab name), sort)))

        val (new_frees_Q_t, ctxt') = Variable.variant_fixes frees_Q_t ctxt
        val tab_frees = frees_Q_t ~~ new_frees_Q_t

        val (new_tfrees_Q_t, ctxt'') = Variable.invent_types (replicate (length tfrees_Q_t) []) ctxt'
        val tab_tfrees = tfrees_Q_t ~~ (fst o split_list) new_tfrees_Q_t

        val renamed_Q_t = rename_free_vars tab_frees Q_t
        val renamed_Q_t = rename_free_tvars tab_tfrees renamed_Q_t
      in
        (renamed_Q_t, ctxt'')
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

fun prove_param_quot_thm ctxt0 ty = 
  let 
    fun generate (ty as Type (s, tys)) (table, ctxt) =
          if null tys then
            let 
              val instantiated_id_quot_thm =
                Thm.instantiate' [SOME (Thm.ctyp_of ctxt ty)] [] @{thm identity_quotient}
            in (instantiated_id_quot_thm, (table, ctxt)) end
          else
            let val (args, table_ctxt') = fold_map generate tys (table, ctxt)
            in (args MRSL (get_rel_quot_thm ctxt s), table_ctxt') end
      | generate ty (table, ctxt) =
          if AList.defined (op =) table ty
          then (the (AList.lookup (op =) table ty), (table, ctxt))
          else
            let
              val (Q_t, ctxt') = get_fresh_Q_t ctxt
              val Q_thm = Thm.assume (Thm.cterm_of ctxt' Q_t)
              val table' = (ty, Q_thm) :: table
            in (Q_thm, (table', ctxt')) end

    val (param_quot_thm, (table, ctxt1)) = generate ty ([], ctxt0)
  in (param_quot_thm, rev table, ctxt1) end
  handle QUOT_THM_INTERNAL pretty_msg => raise PARAM_QUOT_THM (ty, pretty_msg)

(*
  It computes a parametrized relator for the given type ty. E.g., for 'a dlist:
  list_all2 ?R OO cr_dlist with parameters [?R].
  
  Returns: the definitional term and list of parameters (relations).
*)

fun generate_parametrized_relator ctxt ty =
  let
    val (quot_thm, table, ctxt') = prove_param_quot_thm ctxt ty
    val parametrized_relator = quot_thm_crel quot_thm
    val args = map (fn (_, q_thm) => quot_thm_crel q_thm) table
    val exported_terms = Variable.exportT_terms ctxt' ctxt (parametrized_relator :: args)
  in
    (hd exported_terms, tl exported_terms)
  end

(* Parametrization *)

local
  fun get_lhs rule = (Thm.dest_fun o Thm.dest_arg o strip_imp_concl o Thm.cprop_of) rule;
  
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
      val rule1 = Thm.incr_indexes (Thm.maxidx_of_cterm ct + 1) rule;
      val lhs_rule = get_lhs rule1;
      val rule2 = Thm.rename_boundvars (Thm.term_of lhs_rule) (Thm.term_of ct) rule1;
      val lhs_ct = Thm.dest_fun ct
    in
        Thm.instantiate (Thm.match (lhs_rule, lhs_ct)) rule2
          handle Pattern.MATCH => raise CTERM ("rewr_imp", [lhs_rule, lhs_ct])
   end
  
  fun rewrs_imp rules = first_imp (map rewr_imp rules)
in

  fun gen_merge_transfer_relations quotients ctxt0 ctm =
    let
      val ctm = Thm.dest_arg ctm
      val tm = Thm.term_of ctm
      val rel = (hd o get_args 2) tm
  
      fun same_constants (Const (n1,_)) (Const (n2,_)) = n1 = n2
        | same_constants _ _  = false
      
      fun prove_extra_assms ctxt ctm distr_rule =
        let
          fun prove_assm assm =
            try (Goal.prove ctxt [] [] (Thm.term_of assm)) (fn {context = goal_ctxt, ...} =>
              SOLVED' (REPEAT_ALL_NEW (resolve_tac goal_ctxt (Transfer.get_transfer_raw goal_ctxt))) 1)
  
          fun is_POS_or_NEG ctm =
            case (head_of o Thm.term_of o Thm.dest_arg) ctm of
              Const (\<^const_name>\<open>POS\<close>, _) => true
            | Const (\<^const_name>\<open>NEG\<close>, _) => true
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
          Syntax.pretty_term ctxt0 rel]
  
    in
      case get_args 2 rel of
          [Const (\<^const_name>\<open>HOL.eq\<close>, _), _] => rewrs_imp @{thms neg_eq_OO pos_eq_OO} ctm
          | [_, Const (\<^const_name>\<open>HOL.eq\<close>, _)] => rewrs_imp @{thms neg_OO_eq pos_OO_eq} ctm
          | [_, trans_rel] =>
            let
              val (rty', qty) = (relation_types o fastype_of) trans_rel
            in
              if same_type_constrs (rty', qty) then
                let
                  val distr_rules = get_rel_distr_rules ctxt0 ((fst o dest_Type) rty') (head_of tm)
                  val distr_rule = get_first (prove_extra_assms ctxt0 ctm) distr_rules
                in
                  case distr_rule of
                    NONE => raise MERGE_TRANSFER_REL (cannot_merge_error_msg ())
                  | SOME distr_rule =>
                      map (gen_merge_transfer_relations quotients ctxt0) (cprems_of distr_rule)
                        MRSL distr_rule
                end
              else
                let 
                  val pcrel_def = get_pcrel_def quotients ctxt0 ((fst o dest_Type) qty)
                  val pcrel_const = (head_of o fst o Logic.dest_equals o Thm.prop_of) pcrel_def
                in
                  if same_constants pcrel_const (head_of trans_rel) then
                    let
                      val unfolded_ctm = Thm.rhs_of (Conv.arg1_conv (Conv.arg_conv (Conv.rewr_conv pcrel_def)) ctm)
                      val distr_rule = rewrs_imp @{thms POS_pcr_rule NEG_pcr_rule} unfolded_ctm
                      val result = (map (gen_merge_transfer_relations quotients ctxt0) 
                        (cprems_of distr_rule)) MRSL distr_rule
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

  (*
    ctm - of the form "[POS|NEG] (par_R OO T) t f) ?X", where par_R is a parametricity transfer 
    relation for t and T is a transfer relation between t and f, which consists only from
    parametrized transfer relations (i.e., pcr_?) and equalities op=. POS or NEG encodes
    co-variance or contra-variance.
    
    The function merges par_R OO T using definitions of parametrized correspondence relations
    (e.g., (rel_S R) OO (pcr_T op=) --> pcr_T R using the definition pcr_T R = (rel_S R) OO cr_T).
  *)

  fun merge_transfer_relations ctxt ctm =
    gen_merge_transfer_relations (Lifting_Info.get_quotients ctxt) ctxt ctm
end

fun gen_parametrize_transfer_rule quotients ctxt thm =
  let
    fun parametrize_relation_conv ctm =
      let
        val (rty, qty) = (relation_types o fastype_of) (Thm.term_of ctm)
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
                val (rty', rtyq) = gen_instantiate_rtys quotients ctxt (rty, qty)
                val (rty's, rtyqs) = if gen_rty_is_TVar quotients ctxt qty then ([rty'],[rtyq]) 
                  else (Targs rty', Targs rtyq)
              in
                if forall op= (rty's ~~ rtyqs) then
                  let
                    val pcr_cr_eq = (Thm.symmetric o mk_meta_eq) (get_pcr_cr_eq quotients ctxt q)
                  in      
                    Conv.rewr_conv pcr_cr_eq ctm
                  end
                  handle QUOT_THM_INTERNAL _ => Conv.all_conv ctm
                else
                  if has_pcrel_info quotients q then
                    let 
                      val pcrel_def = Thm.symmetric (get_pcrel_def quotients ctxt q)
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

(*
  It replaces cr_T by pcr_T op= in the transfer relation. For composed
  abstract types, it replaces T_rel R OO cr_T by pcr_T R. If the parametrized
  correspondce relation does not exist, the original relation is kept.

  thm - a transfer rule
*)

fun parametrize_transfer_rule ctxt thm = 
  gen_parametrize_transfer_rule (Lifting_Info.get_quotients ctxt) ctxt thm

end
