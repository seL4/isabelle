(*  Title:      HOL/Nunchaku/Tools/nunchaku_translate.ML
    Author:     Jasmin Blanchette, VU Amsterdam
    Copyright   2015, 2016, 2017

Translation of Isabelle/HOL problems to Nunchaku.
*)

signature NUNCHAKU_TRANSLATE =
sig
  type isa_problem = Nunchaku_Collect.isa_problem
  type ty = Nunchaku_Problem.ty
  type nun_problem = Nunchaku_Problem.nun_problem

  val flip_quote: string -> string
  val lowlevel_str_of_ty: ty -> string

  val nun_problem_of_isa: Proof.context -> isa_problem -> nun_problem
end;

structure Nunchaku_Translate : NUNCHAKU_TRANSLATE =
struct

open Nunchaku_Util;
open Nunchaku_Collect;
open Nunchaku_Problem;

fun flip_quote s =
  (case try (unprefix "'") s of
    SOME s' => s'
  | NONE => prefix "'" s);

fun lowlevel_str_of_ty (NType (id, tys)) =
  (if null tys then "" else encode_args (map lowlevel_str_of_ty tys)) ^ id;

fun strip_nun_abs 0 tm = ([], tm)
  | strip_nun_abs n (NAbs (var, body)) =
    strip_nun_abs (n - 1) body
    |>> cons var;

val strip_nun_comb =
  let
    fun strip args (NApp (func, arg)) = strip (arg :: args) func
      | strip args tm = (tm, args);
  in
    strip []
  end;

fun ty_of_isa (Type (s, Ts)) =
    let val tys = map ty_of_isa Ts in
      (case s of
        @{type_name bool} => prop_ty
      | @{type_name fun} => NType (nun_arrow, tys)
      | _ =>
        let
          val args = map lowlevel_str_of_ty tys;
          val id = nun_tconst_of_str args s;
        in
          NType (id, [])
        end)
    end
  | ty_of_isa (TFree (s, _)) = NType (nun_tfree_of_str (flip_quote s), [])
  | ty_of_isa (TVar _) = raise Fail "unexpected TVar";

fun gen_tm_of_isa in_prop ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt;

    fun id_of_const (x as (s, _)) =
      let val args = map (lowlevel_str_of_ty o ty_of_isa) (Sign.const_typargs thy x) in
        nun_const_of_str args s
      end;

    fun tm_of_branch ctr_id var_count f_arg_tm =
      let val (vars, body) = strip_nun_abs var_count f_arg_tm in
        (ctr_id, vars, body)
      end;

    fun tm_of bounds (Const (x as (s, T))) =
        (case try (dest_co_datatype_case ctxt) x of
          SOME ctrs =>
          let
            val num_f_args = length ctrs;
            val min_args = num_f_args + 1;
            val var_counts = map (num_binder_types o snd) ctrs;

            val dummy_free = Free (Name.uu, T);
            val tm = tm_of bounds dummy_free;
            val tm' = eta_expandN_tm min_args tm;
            val (vars, body) = strip_nun_abs min_args tm';
            val (_, (f_args, obj :: other_args)) = strip_nun_comb body ||> chop num_f_args;
            val f_args' = map2 eta_expandN_tm var_counts f_args;

            val ctr_ids = map id_of_const ctrs;
          in
            NMatch (obj, @{map 3} tm_of_branch ctr_ids var_counts f_args')
            |> rcomb_tms other_args
            |> abs_tms vars
          end
        | NONE =>
          if s = @{const_name unreachable} andalso in_prop then
            let val ty = ty_of_isa T in
              napps (NConst (nun_asserting, [ty], mk_arrows_ty ([ty, prop_ty], ty)),
                [NConst (id_of_const x, [], ty), NConst (nun_false, [], prop_ty)])
            end
          else
            let
              val id =
                (case s of
                  @{const_name All} => nun_forall
                | @{const_name conj} => nun_conj
                | @{const_name disj} => nun_disj
                | @{const_name HOL.eq} => nun_equals
                | @{const_name Eps} => nun_choice
                | @{const_name Ex} => nun_exists
                | @{const_name False} => nun_false
                | @{const_name If} => nun_if
                | @{const_name implies} => nun_implies
                | @{const_name Not} => nun_not
                | @{const_name The} => nun_unique
                | @{const_name The_unsafe} => nun_unique_unsafe
                | @{const_name True} => nun_true
                | _ => id_of_const x);
            in
              NConst (id, [], ty_of_isa T)
            end)
      | tm_of _ (Free (s, T)) = NConst (nun_free_of_str s, [], ty_of_isa T)
      | tm_of _ (Var ((s, _), T)) = NConst (nun_var_of_str s, [], ty_of_isa T)
      | tm_of bounds (Abs (s, T, t)) =
        let
          val (s', bounds') = Name.variant s bounds;
          val x = Var ((s', 0), T);
        in
          NAbs (tm_of bounds' x, tm_of bounds' (subst_bound (x, t)))
        end
      | tm_of bounds (t $ u) = NApp (tm_of bounds t, tm_of bounds u)
      | tm_of _ (Bound _) = raise Fail "unexpected Bound";
  in
    t
    |> tm_of Name.context
    |> eta_expand_builtin_tm
  end;

val tm_of_isa = gen_tm_of_isa false;
val prop_of_isa = gen_tm_of_isa true;

fun nun_copy_spec_of_isa_typedef ctxt {abs_typ, rep_typ, wrt, abs, rep} =
  {abs_ty = ty_of_isa abs_typ, rep_ty = ty_of_isa rep_typ, subset = SOME (tm_of_isa ctxt wrt),
   quotient = NONE, abs = tm_of_isa ctxt abs, rep = tm_of_isa ctxt rep};

fun nun_copy_spec_of_isa_quotient ctxt {abs_typ, rep_typ, wrt, abs, rep} =
  {abs_ty = ty_of_isa abs_typ, rep_ty = ty_of_isa rep_typ, subset = NONE,
   quotient = SOME (tm_of_isa ctxt wrt), abs = tm_of_isa ctxt abs, rep = tm_of_isa ctxt rep};

fun nun_ctr_of_isa ctxt ctr =
  {ctr = tm_of_isa ctxt ctr, arg_tys = map ty_of_isa (binder_types (fastype_of ctr))};

fun nun_co_data_spec_of_isa ctxt {typ, ctrs} =
  {ty = ty_of_isa typ, ctrs = map (nun_ctr_of_isa ctxt) ctrs};

fun nun_const_spec_of_isa ctxt {const, props} =
  {const = tm_of_isa ctxt const, props = map (prop_of_isa ctxt) props};

fun nun_rec_spec_of_isa ctxt {const, props, ...} =
  {const = tm_of_isa ctxt const, props = map (prop_of_isa ctxt) props};

fun nun_consts_spec_of_isa ctxt {consts, props} =
  {consts = map (tm_of_isa ctxt) consts, props = map (prop_of_isa ctxt) props};

fun nun_problem_of_isa ctxt {commandss, sound, complete} =
  let
    fun cmd_of cmd =
      (case cmd of
        ITVal (T, cards) => NTVal (ty_of_isa T, cards)
      | ITypedef spec => NCopy (nun_copy_spec_of_isa_typedef ctxt spec)
      | IQuotient spec => NCopy (nun_copy_spec_of_isa_quotient ctxt spec)
      | ICoData (fp, specs) =>
        BNF_Util.case_fp fp NData NCodata (map (nun_co_data_spec_of_isa ctxt) specs)
      | IVal t => NVal (tm_of_isa ctxt t, ty_of_isa (fastype_of t))
      | ICoPred (fp, wf, specs) =>
        (if wf then curry NPred true
         else if fp = BNF_Util.Least_FP then curry NPred false
         else NCopred) (map (nun_const_spec_of_isa ctxt) specs)
      | IRec specs => NRec (map (nun_rec_spec_of_isa ctxt) specs)
      | ISpec spec => NSpec (nun_consts_spec_of_isa ctxt spec)
      | IAxiom prop => NAxiom (prop_of_isa ctxt prop)
      | IGoal prop => NGoal (prop_of_isa ctxt prop)
      | IEval t => NEval (tm_of_isa ctxt t));
  in
    {commandss = map (map cmd_of) commandss, sound = sound, complete = complete}
  end;

end;
