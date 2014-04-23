(*  Title:      HOL/Tools/BNF/bnf_lfp_size.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2014

Generation of size functions for new-style datatypes.
*)

signature BNF_LFP_SIZE =
sig
  val register_size: string -> string -> thm list -> thm list -> theory -> theory
  val lookup_size: theory -> string -> (string * (thm list * thm list)) option
end;

structure BNF_LFP_Size : BNF_LFP_SIZE =
struct

open BNF_Util
open BNF_Tactics
open BNF_Def
open BNF_FP_Def_Sugar

val size_N = "size_"

val rec_o_mapN = "rec_o_map"
val sizeN = "size"
val size_o_mapN = "size_o_map"

structure Data = Theory_Data
(
  type T = (string * (thm list * thm list)) Symtab.table;
  val empty = Symtab.empty;
  val extend = I
  fun merge data = Symtab.merge (K true) data;
);

fun register_size T_name size_name size_simps size_o_maps =
  Data.map (Symtab.update (T_name, (size_name, (size_simps, size_o_maps))));

val lookup_size = Symtab.lookup o Data.get;

val zero_nat = @{const zero_class.zero (nat)};

fun mk_plus_nat (t1, t2) = Const (@{const_name Groups.plus},
  HOLogic.natT --> HOLogic.natT --> HOLogic.natT) $ t1 $ t2;

fun mk_to_natT T = T --> HOLogic.natT;

fun mk_abs_zero_nat T = Term.absdummy T zero_nat;

fun pointfill ctxt th = unfold_thms ctxt [o_apply] (th RS fun_cong);

fun mk_unabs_def_unused_0 n =
  funpow n (fn thm => thm RS @{thm fun_cong_unused_0} handle THM _ => thm RS fun_cong);

val rec_o_map_simp_thms =
  @{thms o_def id_apply case_prod_app case_sum_o_map_sum case_prod_o_map_prod
      BNF_Comp.id_bnf_comp_def};

fun mk_rec_o_map_tac ctxt rec_def pre_map_defs abs_inverses ctor_rec_o_map =
  unfold_thms_tac ctxt [rec_def] THEN
  HEADGOAL (rtac (ctor_rec_o_map RS trans) THEN'
    K (PRIMITIVE (Conv.fconv_rule Thm.eta_long_conversion)) THEN' asm_simp_tac
      (ss_only (pre_map_defs @ distinct Thm.eq_thm_prop abs_inverses @ rec_o_map_simp_thms) ctxt));

val size_o_map_simp_thms =
  @{thms prod_inj_map inj_on_id snd_comp_apfst[unfolded apfst_def]};

fun mk_size_o_map_tac ctxt size_def rec_o_map inj_maps size_maps =
  unfold_thms_tac ctxt [size_def] THEN
  HEADGOAL (rtac (rec_o_map RS trans) THEN'
    asm_simp_tac (ss_only (inj_maps @ size_maps @ size_o_map_simp_thms) ctxt)) THEN
  IF_UNSOLVED (unfold_thms_tac ctxt @{thms o_def} THEN HEADGOAL (rtac refl));

fun generate_size (fp_sugars as ({T = Type (_, As), BT = Type (_, Bs), fp = Least_FP,
        fp_res = {bnfs = fp_bnfs, xtor_co_rec_o_map_thms = ctor_rec_o_maps, ...}, nested_bnfs, ...}
      : fp_sugar) :: _) thy =
    let
      val data = Data.get thy;

      val Ts = map #T fp_sugars
      val T_names = map (fst o dest_Type) Ts;
      val nn = length Ts;

      val B_ify = Term.typ_subst_atomic (As ~~ Bs);

      val recs = map #co_rec fp_sugars;
      val rec_thmss = map #co_rec_thms fp_sugars;
      val rec_Ts as rec_T1 :: _ = map fastype_of recs;
      val rec_arg_Ts = binder_fun_types rec_T1;
      val Cs = map body_type rec_Ts;
      val Cs_rho = map (rpair HOLogic.natT) Cs;
      val substCnatT = Term.subst_atomic_types Cs_rho;

      val f_Ts = map mk_to_natT As;
      val f_TsB = map mk_to_natT Bs;
      val num_As = length As;

      val f_names = map (prefix "f" o string_of_int) (1 upto num_As);
      val fs = map2 (curry Free) f_names f_Ts;
      val fsB = map2 (curry Free) f_names f_TsB;
      val As_fs = As ~~ fs;

      val size_names = map (Long_Name.map_base_name (prefix size_N)) T_names;

      fun is_pair_C @{type_name prod} [_, T'] = member (op =) Cs T'
        | is_pair_C _ _ = false;

      fun mk_size_of_typ (T as TFree _) =
          pair (case AList.lookup (op =) As_fs T of
              SOME f => f
            | NONE => if member (op =) Cs T then Term.absdummy T (Bound 0) else mk_abs_zero_nat T)
        | mk_size_of_typ (T as Type (s, Ts)) =
          if is_pair_C s Ts then
            pair (snd_const T)
          else if exists (exists_subtype_in As) Ts then
            (case Symtab.lookup data s of
              SOME (size_name, (_, size_o_maps as _ :: _)) =>
              let
                val (args, size_o_mapss') = split_list (map (fn T => mk_size_of_typ T []) Ts);
                val size_const = Const (size_name, map fastype_of args ---> mk_to_natT T);
              in
                fold (union Thm.eq_thm) (size_o_maps :: size_o_mapss')
                #> pair (Term.list_comb (size_const, args))
              end
            | _ => pair (mk_abs_zero_nat T))
          else
            pair (mk_abs_zero_nat T);

      fun mk_size_of_arg t =
        mk_size_of_typ (fastype_of t) #>> (fn s => substCnatT (betapply (s, t)));

      fun mk_size_arg rec_arg_T size_o_maps =
        let
          val x_Ts = binder_types rec_arg_T;
          val m = length x_Ts;
          val x_names = map (prefix "x" o string_of_int) (1 upto m);
          val xs = map2 (curry Free) x_names x_Ts;
          val (summands, size_o_maps') =
            fold_map mk_size_of_arg xs size_o_maps
            |>> remove (op =) zero_nat;
          val sum =
            if null summands then HOLogic.zero
            else foldl1 mk_plus_nat (summands @ [HOLogic.Suc_zero]);
        in
          (fold_rev Term.lambda (map substCnatT xs) sum, size_o_maps')
        end;

      fun mk_size_rhs recx size_o_maps =
        let val (args, size_o_maps') = fold_map mk_size_arg rec_arg_Ts size_o_maps in
          (fold_rev Term.lambda fs (Term.list_comb (substCnatT recx, args)), size_o_maps')
        end;

      fun mk_def_binding f =
        Binding.conceal o Binding.name o Thm.def_name o f o Long_Name.base_name;

      val (size_rhss, nested_size_o_maps) = fold_map mk_size_rhs recs [];
      val size_Ts = map fastype_of size_rhss;
      val size_consts = map2 (curry Const) size_names size_Ts;
      val size_constsB = map (Term.map_types B_ify) size_consts;
      val size_def_bs = map (mk_def_binding I) size_names;

      val (size_defs, thy2) =
        thy
        |> Sign.add_consts (map (fn (s, T) => (Binding.name (Long_Name.base_name s), T, NoSyn))
          (size_names ~~ size_Ts))
        |> Global_Theory.add_defs false (map Thm.no_attributes (size_def_bs ~~
          map Logic.mk_equals (size_consts ~~ size_rhss)));

      val zeros = map mk_abs_zero_nat As;

      val overloaded_size_rhss = map (fn c => Term.list_comb (c, zeros)) size_consts;
      val overloaded_size_Ts = map fastype_of overloaded_size_rhss;
      val overloaded_size_consts = map (curry Const @{const_name size}) overloaded_size_Ts;
      val overloaded_size_def_bs = map (mk_def_binding (suffix "_overloaded")) size_names;

      fun define_overloaded_size def_b lhs0 rhs lthy =
        let
          val Free (c, _) = Syntax.check_term lthy lhs0;
          val (thm, lthy') = lthy
            |> Local_Theory.define ((Binding.name c, NoSyn), ((def_b, []), rhs))
            |-> (fn (t, (_, thm)) => Spec_Rules.add Spec_Rules.Equational ([t], [thm]) #> pair thm);
          val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy');
          val thm' = singleton (Proof_Context.export lthy' ctxt_thy) thm;
        in (thm', lthy') end;

      val (overloaded_size_defs, thy3) = thy2
        |> Class.instantiation (T_names, map dest_TFree As, [HOLogic.class_size])
        |> fold_map3 define_overloaded_size overloaded_size_def_bs overloaded_size_consts
          overloaded_size_rhss
        ||> Class.prove_instantiation_instance (K (Class.intro_classes_tac []))
        ||> Local_Theory.exit_global;

      val thy3_ctxt = Proof_Context.init_global thy3;

      val size_defs' =
        map (mk_unabs_def (num_As + 1) o (fn thm => thm RS meta_eq_to_obj_eq)) size_defs;
      val size_defs_unused_0 =
        map (mk_unabs_def_unused_0 (num_As + 1) o (fn thm => thm RS meta_eq_to_obj_eq)) size_defs;
      val overloaded_size_defs' =
        map (mk_unabs_def 1 o (fn thm => thm RS meta_eq_to_obj_eq)) overloaded_size_defs;

      val nested_size_maps = map (pointfill thy3_ctxt) nested_size_o_maps @ nested_size_o_maps;
      val all_inj_maps = map inj_map_of_bnf (fp_bnfs @ nested_bnfs);

      fun derive_size_simp size_def' simp0 =
        (trans OF [size_def', simp0])
        |> Simplifier.asm_full_simplify (ss_only (@{thms inj_on_convol_id snd_o_convol} @
          all_inj_maps @ nested_size_maps) thy3_ctxt)
        |> fold_thms thy3_ctxt size_defs_unused_0;
      fun derive_overloaded_size_simp size_def' simp0 =
        (trans OF [size_def', simp0])
        |> unfold_thms thy3_ctxt @{thms add_0_left add_0_right}
        |> fold_thms thy3_ctxt overloaded_size_defs';

      val size_simpss = map2 (map o derive_size_simp) size_defs' rec_thmss;
      val size_simps = flat size_simpss;
      val overloaded_size_simpss =
        map2 (map o derive_overloaded_size_simp) overloaded_size_defs' size_simpss;

      val ABs = As ~~ Bs;
      val g_names = map (prefix "g" o string_of_int) (1 upto num_As);
      val gs = map2 (curry Free) g_names (map (op -->) ABs);

      val liveness = map (op <>) ABs;
      val live_gs = AList.find (op =) (gs ~~ liveness) true;
      val live = length live_gs;

      val maps0 = map map_of_bnf fp_bnfs;

      (* This disables much of the functionality of the size extension within a locale. It is not
         clear how to make the code below work with locales, given that interpretations are based on
         theories. *)
      val has_hyps = not (null (Thm.hyps_of (hd (hd rec_thmss))));

      val (rec_o_map_thmss, size_o_map_thmss) =
        if has_hyps orelse live = 0 then
          `I (replicate nn [])
        else
          let
            val pre_bnfs = map #pre_bnf fp_sugars;
            val pre_map_defs = map map_def_of_bnf pre_bnfs;
            val abs_inverses = map (#abs_inverse o #absT_info) fp_sugars;
            val rec_defs = map #co_rec_def fp_sugars;

            val gmaps = map (fn map0 => Term.list_comb (mk_map live As Bs map0, live_gs)) maps0;

            val num_rec_args = length rec_arg_Ts;
            val h_Ts = map B_ify rec_arg_Ts;
            val h_names = map (prefix "h" o string_of_int) (1 upto num_rec_args);
            val hs = map2 (curry Free) h_names h_Ts;
            val hrecs = map (fn recx => Term.list_comb (Term.map_types B_ify recx, hs)) recs;

            val rec_o_map_lhss = map2 (curry HOLogic.mk_comp) hrecs gmaps;

            val ABgs = ABs ~~ gs;

            fun mk_rec_arg_arg (x as Free (_, T)) =
              let val U = B_ify T in
                if T = U then x else build_map thy3_ctxt (the o AList.lookup (op =) ABgs) (T, U) $ x
              end;

            fun mk_rec_o_map_arg rec_arg_T h =
              let
                val x_Ts = binder_types rec_arg_T;
                val m = length x_Ts;
                val x_names = map (prefix "x" o string_of_int) (1 upto m);
                val xs = map2 (curry Free) x_names x_Ts;
                val xs' = map mk_rec_arg_arg xs;
              in
                fold_rev Term.lambda xs (Term.list_comb (h, xs'))
              end;

            fun mk_rec_o_map_rhs recx =
              let val args = map2 mk_rec_o_map_arg rec_arg_Ts hs in
                Term.list_comb (recx, args)
              end;

            val rec_o_map_rhss = map mk_rec_o_map_rhs recs;

            val rec_o_map_goals =
              map2 (HOLogic.mk_Trueprop oo curry HOLogic.mk_eq) rec_o_map_lhss rec_o_map_rhss;
            val rec_o_map_thms =
              map3 (fn goal => fn rec_def => fn ctor_rec_o_map =>
                  Goal.prove_global thy3 [] [] goal (fn {context = ctxt, ...} =>
                    mk_rec_o_map_tac ctxt rec_def pre_map_defs abs_inverses ctor_rec_o_map)
                  |> Thm.close_derivation)
                rec_o_map_goals rec_defs ctor_rec_o_maps;

            val size_o_map_conds =
              if exists (can Logic.dest_implies o Thm.prop_of) nested_size_o_maps then
                map (HOLogic.mk_Trueprop o mk_inj) live_gs
              else
                [];

            val fsizes = map (fn size_constB => Term.list_comb (size_constB, fsB)) size_constsB;
            val size_o_map_lhss = map2 (curry HOLogic.mk_comp) fsizes gmaps;

            val fgs = map2 (fn fB => fn g as Free (_, Type (_, [A, B])) =>
              if A = B then fB else HOLogic.mk_comp (fB, g)) fsB gs;
            val size_o_map_rhss = map (fn c => Term.list_comb (c, fgs)) size_consts;

            val size_o_map_goals =
              map2 (curry Logic.list_implies size_o_map_conds o HOLogic.mk_Trueprop oo
                curry HOLogic.mk_eq) size_o_map_lhss size_o_map_rhss;
            val size_o_map_thms =
              map3 (fn goal => fn size_def => fn rec_o_map =>
                  Goal.prove_global thy3 [] [] goal (fn {context = ctxt, ...} =>
                    mk_size_o_map_tac ctxt size_def rec_o_map all_inj_maps nested_size_maps)
                  |> Thm.close_derivation)
                size_o_map_goals size_defs rec_o_map_thms;
          in
            pairself (map single) (rec_o_map_thms, size_o_map_thms)
          end;

      val (_, thy4) = thy3
        |> fold_map4 (fn T_name => fn size_simps => fn rec_o_map_thms => fn size_o_map_thms =>
            if has_hyps then
              pair []
            else
              let val qualify = Binding.qualify true (Long_Name.base_name T_name) in
                Global_Theory.note_thmss ""
                  ([((qualify (Binding.name rec_o_mapN), []), [(rec_o_map_thms, [])]),
                    ((qualify (Binding.name sizeN),
                       [Simplifier.simp_add, Nitpick_Simps.add, Thm.declaration_attribute
                          (fn thm => Context.mapping (Code.add_default_eqn thm) I)]),
                     [(size_simps, [])]),
                    ((qualify (Binding.name size_o_mapN), []), [(size_o_map_thms, [])])]
                   |> filter_out (forall (null o fst) o snd))
              end)
          T_names (map2 append size_simpss overloaded_size_simpss) rec_o_map_thmss size_o_map_thmss
        ||> Spec_Rules.add_global Spec_Rules.Equational (size_consts, size_simps);
    in
      thy4
      |> Data.map (fold2 (fn T_name => fn size_name =>
          Symtab.update_new (T_name, (size_name, (size_simps, flat size_o_map_thmss))))
        T_names size_names)
    end
  | generate_size _ thy = thy;

val _ = Theory.setup (fp_sugar_interpretation generate_size);

end;
