(*  Title:      HOL/Tools/datatype_simprocs.ML
    Author:     Manuel Eberl, TU München

Simproc to automatically rewrite equalities of datatype values "lhs = rhs" to "False" if
either side is a proper subterm of the other.
*)

signature DATATYPE_SIMPROCS = sig
  val no_proper_subterm_proc : Simplifier.proc
end

structure Datatype_Simprocs : DATATYPE_SIMPROCS = struct

exception NOT_APPLICABLE

val size_neq_imp_neq_thm = @{thm HOL.Eq_FalseI[OF size_neq_size_imp_neq]}

fun get_bnf_sugar ctxt s =
  case BNF_FP_Def_Sugar.fp_sugar_of ctxt s of
    SOME sugar => sugar
  | NONE => raise NOT_APPLICABLE

(*
  Checks if the given type contains any of the given datatypes (with only type variables
  as arguments). This allows discovering which arguments of a datatype constructor are
  recursive and which are not.
*)
fun contains_datatypes T_names =
  let
    fun go (Type (s, Ts)) =
      (member op= T_names s andalso forall is_TVar Ts)
      orelse exists go Ts
      | go _ = false
  in
    go
  end

fun mk_ctor T_names t =
  let
    val name = t |> dest_Const |> fst
    val (argTs, _) = strip_type (fastype_of t)
    val active_poss = map (contains_datatypes T_names) argTs
  in
    (name, active_poss)
  end

(*
  Returns a pair of constructor name and a boolean list indicating whether each
  constructor argument is or is recursive. E.g. the first parameter of "Cons" for lists is
  non-recursive and the second one is.
*)
fun get_ctors T_names (sugar : BNF_FP_Def_Sugar.fp_sugar) =
  sugar
  |> #fp_ctr_sugar
  |> #ctr_defs
  |> map (Thm.concl_of #> Logic.dest_equals #> fst #> mk_ctor T_names)

fun get_mutuals (sugar : BNF_FP_Def_Sugar.fp_sugar) =
  sugar
  |> #fp_res
  |> #Ts
  |> map dest_Type_name

fun get_ctors_mutuals ctxt sugar =
  let
    val mutuals = sugar |> get_mutuals
  in
    mutuals |> map (get_bnf_sugar ctxt #> get_ctors mutuals) |> flat
  end

fun get_size_info ctxt s =
  case BNF_LFP_Size.size_of ctxt s of
    SOME info => info
  | NONE => raise NOT_APPLICABLE

fun is_comb (_ $ _) = true
  | is_comb _ = false

(* simproc will not be used for these types *)
val forbidden_types =
  ([@{typ "bool"}, @{typ "nat"}, @{typ "'a \<times> 'b"}, @{typ "'a + 'b"}]
   |> map dest_Type_name)
  @ ["List.list", "Option.option"]

(* FIXME: possible improvements:
   - support for nested datatypes
   - replace size-based proof with proper subexpression relation
*)
fun no_proper_subterm_proc ctxt ct =
  let
    val (clhs, crhs) = ct |> Thm.dest_comb |> apfst (Thm.dest_comb #> snd)
    val (lhs, rhs) = apply2 Thm.term_of (clhs, crhs)
    val cT = Thm.ctyp_of_cterm clhs    
    val T = Thm.typ_of cT
    val (T_name, T_args) = dest_Type T

    val _ = if member op= forbidden_types T_name then raise NOT_APPLICABLE else ()
    val _ = if lhs aconv rhs then raise NOT_APPLICABLE else ()

    val sugar = get_bnf_sugar ctxt T_name
    val (_, (_, size_eq_thms, _)) = get_size_info ctxt T_name
    val ctors = get_ctors_mutuals ctxt sugar

    (* Descend into the term t along datatype constructors, but only along those constructor
       arguments that are actually recursive *)
    fun is_subterm s t =
      let
        fun go t =
          s aconv t orelse (is_comb t andalso go' (strip_comb t))
        and go' (Const (c, _), ts) = (
              case AList.lookup op= ctors c of
                NONE => false
              | SOME poss => exists (fn (b, t) => b andalso go t) (poss ~~ ts))
          | go' _ = false
      in
        go t
      end
    val _ = if not (is_subterm lhs rhs) andalso not (is_subterm rhs lhs) then
      raise NOT_APPLICABLE else ()
  in
    size_neq_imp_neq_thm
    |> Drule.instantiate'_normalize [SOME cT] [SOME clhs, SOME crhs]
    |> rewrite_goals_rule ctxt (map (fn thm => thm RS @{thm eq_reflection}) size_eq_thms)
    |> Tactic.rule_by_tactic ctxt (HEADGOAL (Lin_Arith.simple_tac ctxt))
    |> SOME
  end
  handle NOT_APPLICABLE => NONE
    | CTERM _ => NONE
    | TERM _ => NONE
    | TYPE _ => NONE
    | THM _ => NONE

end
