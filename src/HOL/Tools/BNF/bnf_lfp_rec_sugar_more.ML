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

val nested_simps = @{thms o_def[abs_def] id_def split fst_conv snd_conv};

fun is_new_datatype ctxt s =
  (case fp_sugar_of ctxt s of SOME {fp = Least_FP, ...} => true | _ => false);

fun basic_lfp_sugar_of C fun_arg_Tsss ({T, fp_res_index, ctr_defs, ctr_sugar, co_rec = recx,
    co_rec_thms = rec_thms, ...} : fp_sugar) =
  {T = T, fp_res_index = fp_res_index, C = C, fun_arg_Tsss = fun_arg_Tsss, ctr_defs = ctr_defs,
   ctr_sugar = ctr_sugar, recx = recx, rec_thms = rec_thms};

fun get_basic_lfp_sugars bs arg_Ts callers callssss0 lthy0 =
  let
    val ((missing_arg_Ts, perm0_kks,
          fp_sugars as {fp_nesting_bnfs, common_co_inducts = [common_induct], ...} :: _,
          (lfp_sugar_thms, _)), lthy) =
      nested_to_mutual_fps (K true) Least_FP bs arg_Ts callers callssss0 lthy0;

    val induct_attrs = (case lfp_sugar_thms of SOME ((_, _, attrs), _) => attrs | NONE => []);

    val Ts = map #T fp_sugars;
    val Xs = map #X fp_sugars;
    val Cs = map (body_type o fastype_of o #co_rec) fp_sugars;
    val Xs_TCs = Xs ~~ (Ts ~~ Cs);

    fun zip_recT (Type (s, Us)) = [Type (s, map (HOLogic.mk_tupleT o zip_recT) Us)]
      | zip_recT U =
        (case AList.lookup (op =) Xs_TCs U of
          SOME (T, C) => [T, C]
        | NONE => [U]);

    val ctrXs_Tsss = map #ctrXs_Tss fp_sugars;
    val fun_arg_Tssss = map (map (map zip_recT)) ctrXs_Tsss;

    val fp_nesting_map_ident0s = map map_ident0_of_bnf fp_nesting_bnfs;
    val fp_nesting_map_comps = map map_comp_of_bnf fp_nesting_bnfs;
  in
    (missing_arg_Ts, perm0_kks, map3 basic_lfp_sugar_of Cs fun_arg_Tssss fp_sugars,
     fp_nesting_map_ident0s, fp_nesting_map_comps, common_induct, induct_attrs,
     is_some lfp_sugar_thms, lthy)
  end;

exception NO_MAP of term;

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
    val build_map_fst = build_map ctxt [] (fst_const o fst);

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
        | NONE => raise NO_MAP t)
      | massage_map _ _ t = raise NO_MAP t
    and massage_map_or_map_arg U T t =
      if T = U then
        tap check_no_call t
      else
        massage_map U T t
        handle NO_MAP _ => massage_mutual_fun U T t;

    fun massage_call (t as t1 $ t2) =
        if has_call t then
          if t2 = y then
            massage_map yU yT (elim_y t1) $ y'
            handle NO_MAP t' => invalid_map ctxt t'
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

fun rewrite_map_arg get_ctr_pos rec_type res_type =
  let
    val pT = HOLogic.mk_prodT (rec_type, res_type);

    fun subst d (t as Bound d') = t |> d = SOME d' ? curry (op $) (fst_const pT)
      | subst d (Abs (v, T, b)) =
        Abs (v, if d = SOME ~1 then pT else T, subst (Option.map (Integer.add 1) d) b)
      | subst d t =
        let
          val (u, vs) = strip_comb t;
          val ctr_pos = try (get_ctr_pos o fst o dest_Free) u |> the_default ~1;
        in
          if ctr_pos >= 0 then
            if d = SOME ~1 andalso length vs = ctr_pos then
              Term.list_comb (permute_args ctr_pos (snd_const pT), vs)
            else if length vs > ctr_pos andalso is_some d andalso
                d = try (fn Bound n => n) (nth vs ctr_pos) then
              Term.list_comb (snd_const pT $ nth vs ctr_pos, map (subst d) (nth_drop ctr_pos vs))
            else
              raise PRIMREC ("recursive call not directly applied to constructor argument", [t])
          else
            Term.list_comb (u, map (subst (d |> d = SOME ~1 ? K NONE)) vs)
        end
  in
    subst (SOME ~1)
  end;

fun rewrite_nested_rec_call ctxt has_call get_ctr_pos =
  massage_nested_rec_call ctxt has_call (rewrite_map_arg get_ctr_pos);

val _ = Theory.setup (register_lfp_rec_extension
  {nested_simps = nested_simps, is_new_datatype = is_new_datatype,
   get_basic_lfp_sugars = get_basic_lfp_sugars, rewrite_nested_rec_call = rewrite_nested_rec_call});

end;
