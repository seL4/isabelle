(*  Title:      HOL/Tools/BNF/bnf_lfp_rec_sugar_more.ML
    Author:     Lorenz Panny, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

More recursor sugar.
*)

structure BNF_LFP_Rec_Sugar_More : sig end =
struct

open BNF_Util
open BNF_Def
open BNF_FP_Util
open BNF_FP_Def_Sugar
open BNF_FP_N2M_Sugar
open BNF_LFP_Rec_Sugar

fun is_new_datatype ctxt s =
  (case fp_sugar_of ctxt s of SOME {fp = Least_FP, ...} => true | _ => false);

fun basic_lfp_sugar_of ({T, fp_res = {xtor_co_iterss = ctor_iterss, ...}, fp_res_index, ctr_defs,
    ctr_sugar, co_iters = iters, co_iter_thmss = iter_thmss, ...} : fp_sugar) =
  {T = T, fp_res_index = fp_res_index,
   ctor_recT = fastype_of (co_rec_of (nth ctor_iterss fp_res_index)), ctr_defs = ctr_defs,
   ctr_sugar = ctr_sugar, recx = co_rec_of iters, rec_thms = co_rec_of iter_thmss};

fun get_basic_lfp_sugars bs arg_Ts get_indices callssss0 lthy0 =
  let
    val ((missing_arg_Ts, perm0_kks,
          fp_sugars as {nested_bnfs, co_inducts = [induct_thm], ...} :: _, (lfp_sugar_thms, _)),
         lthy) =
      nested_to_mutual_fps Least_FP bs arg_Ts get_indices callssss0 lthy0;
    val nested_map_idents = map (unfold_thms lthy @{thms id_def} o map_id0_of_bnf) nested_bnfs;
    val nested_map_comps = map map_comp_of_bnf nested_bnfs;
  in
    (missing_arg_Ts, perm0_kks, map basic_lfp_sugar_of fp_sugars, nested_map_idents,
     nested_map_comps, induct_thm, is_some lfp_sugar_thms, lthy)
  end;

exception NOT_A_MAP of term;

fun ill_formed_rec_call ctxt t =
  error ("Ill-formed recursive call: " ^ quote (Syntax.string_of_term ctxt t));
fun invalid_map ctxt t =
  error ("Invalid map function in " ^ quote (Syntax.string_of_term ctxt t));
fun unexpected_rec_call ctxt t =
  error ("Unexpected recursive call: " ^ quote (Syntax.string_of_term ctxt t));

fun massage_nested_rec_call ctxt has_call raw_massage_fun bound_Ts y y' =
  let
    fun check_no_call t = if has_call t then unexpected_rec_call ctxt t else ();

    val typof = curry fastype_of1 bound_Ts;
    val build_map_fst = build_map ctxt (fst_const o fst);

    val yT = typof y;
    val yU = typof y';

    fun y_of_y' () = build_map_fst (yU, yT) $ y';
    val elim_y = Term.map_aterms (fn t => if t = y then y_of_y' () else t);

    fun massage_mutual_fun U T t =
      (case t of
        Const (@{const_name comp}, _) $ t1 $ t2 =>
        mk_comp bound_Ts (tap check_no_call t1, massage_mutual_fun U T t2)
      | _ =>
        if has_call t then
          (case try HOLogic.dest_prodT U of
            SOME (U1, U2) => if U1 = T then raw_massage_fun T U2 t else invalid_map ctxt t
          | NONE => invalid_map ctxt t)
        else
          mk_comp bound_Ts (t, build_map_fst (U, T)));

    fun massage_map (Type (_, Us)) (Type (s, Ts)) t =
        (case try (dest_map ctxt s) t of
          SOME (map0, fs) =>
          let
            val Type (_, ran_Ts) = range_type (typof t);
            val map' = mk_map (length fs) Us ran_Ts map0;
            val fs' = map_flattened_map_args ctxt s (map3 massage_map_or_map_arg Us Ts) fs;
          in
            Term.list_comb (map', fs')
          end
        | NONE => raise NOT_A_MAP t)
      | massage_map _ _ t = raise NOT_A_MAP t
    and massage_map_or_map_arg U T t =
      if T = U then
        tap check_no_call t
      else
        massage_map U T t
        handle NOT_A_MAP _ => massage_mutual_fun U T t;

    fun massage_call (t as t1 $ t2) =
        if has_call t then
          if t2 = y then
            massage_map yU yT (elim_y t1) $ y'
            handle NOT_A_MAP t' => invalid_map ctxt t'
          else
            let val (g, xs) = Term.strip_comb t2 in
              if g = y then
                if exists has_call xs then unexpected_rec_call ctxt t2
                else Term.list_comb (massage_call (mk_compN (length xs) bound_Ts (t1, y)), xs)
              else
                ill_formed_rec_call ctxt t
            end
        else
          elim_y t
      | massage_call t = if t = y then y_of_y' () else ill_formed_rec_call ctxt t;
  in
    massage_call
  end;

val _ = Theory.setup (register_lfp_rec_extension
  {is_new_datatype = is_new_datatype, get_basic_lfp_sugars = get_basic_lfp_sugars,
   massage_nested_rec_call = massage_nested_rec_call});

end;
