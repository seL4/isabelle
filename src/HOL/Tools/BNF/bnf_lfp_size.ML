(*  Title:      HOL/Tools/BNF/bnf_lfp_size.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2014

Generation of size functions for datatypes.
*)

signature BNF_LFP_SIZE =
sig
  val register_size: string -> string -> thm -> thm list -> thm list -> local_theory -> local_theory
  val register_size_global: string -> string -> thm -> thm list -> thm list -> theory -> theory
  val size_of: Proof.context -> string -> (string * (thm * thm list * thm list)) option
  val size_of_global: theory -> string -> (string * (thm * thm list * thm list)) option
end;

structure BNF_LFP_Size : BNF_LFP_SIZE =
struct

open BNF_Util
open BNF_Tactics
open BNF_Def
open BNF_FP_Def_Sugar

val size_N = "size_";
val sizeN = "size";
val size_genN = "size_gen";
val size_gen_o_mapN = "size_gen_o_map";
val size_neqN = "size_neq";

val nitpicksimp_attrs = @{attributes [nitpick_simp]};
val simp_attrs = @{attributes [simp]};

fun mk_plus_nat (t1, t2) = Const (\<^const_name>\<open>Groups.plus\<close>,
  HOLogic.natT --> HOLogic.natT --> HOLogic.natT) $ t1 $ t2;

fun mk_to_natT T = T --> HOLogic.natT;

fun mk_abs_zero_nat T = Term.absdummy T HOLogic.zero;

fun mk_unabs_def_unused_0 n =
  funpow n (fn thm => thm RS @{thm fun_cong_unused_0} handle THM _ => thm RS fun_cong);

structure Data = Generic_Data
(
  type T = (string * (thm * thm list * thm list)) Symtab.table;
  val empty = Symtab.empty;
  val extend = I
  fun merge data = Symtab.merge (K true) data;
);

fun check_size_type thy T_name size_name =
  let
    val n = Sign.arity_number thy T_name;
    val As = map (fn s => TFree (s, \<^sort>\<open>type\<close>)) (Name.invent Name.context Name.aT n);
    val T = Type (T_name, As);
    val size_T = map mk_to_natT As ---> mk_to_natT T;
    val size_const = Const (size_name, size_T);
  in
    can (Thm.global_cterm_of thy) size_const orelse
    error ("Constant " ^ quote size_name ^ " registered as size function for " ^ quote T_name ^
      " must have type\n" ^ quote (Syntax.string_of_typ_global thy size_T))
  end;

fun register_size T_name size_name overloaded_size_def size_simps size_gen_o_maps lthy =
  (check_size_type (Proof_Context.theory_of lthy) T_name size_name;
   Context.proof_map (Data.map (Symtab.update
       (T_name, (size_name, (overloaded_size_def, size_simps, size_gen_o_maps)))))
     lthy);

fun register_size_global T_name size_name overloaded_size_def size_simps size_gen_o_maps thy =
  (check_size_type thy T_name size_name;
   Context.theory_map (Data.map (Symtab.update
       (T_name, (size_name, (overloaded_size_def, size_simps, size_gen_o_maps)))))
     thy);

val size_of = Symtab.lookup o Data.get o Context.Proof;
val size_of_global = Symtab.lookup o Data.get o Context.Theory;

fun all_overloaded_size_defs_of ctxt =
  Symtab.fold (fn (_, (_, (overloaded_size_def, _, _))) =>
      can (Logic.dest_equals o Thm.prop_of) overloaded_size_def ? cons overloaded_size_def)
    (Data.get (Context.Proof ctxt)) [];

val size_gen_o_map_simps = @{thms inj_on_id snd_comp_apfst[simplified apfst_def]};

fun mk_size_gen_o_map_tac ctxt size_def rec_o_map inj_maps size_maps =
  unfold_thms_tac ctxt [size_def] THEN
  HEADGOAL (rtac ctxt (rec_o_map RS trans) THEN'
    asm_simp_tac (ss_only (inj_maps @ size_maps @ size_gen_o_map_simps) ctxt)) THEN
  IF_UNSOLVED (unfold_thms_tac ctxt @{thms id_def o_def} THEN HEADGOAL (rtac ctxt refl));

fun mk_size_neq ctxt cts exhaust sizes =
  HEADGOAL (rtac ctxt (infer_instantiate' ctxt (map SOME cts) exhaust)) THEN
  ALLGOALS (hyp_subst_tac ctxt) THEN
  unfold_thms_tac ctxt (@{thm neq0_conv} :: sizes) THEN
  ALLGOALS (REPEAT_DETERM o (rtac ctxt @{thm zero_less_Suc} ORELSE'
    rtac ctxt @{thm trans_less_add2}));

fun generate_datatype_size (fp_sugars as ({T = Type (_, As), BT = Type (_, Bs), fp = Least_FP,
        fp_res = {bnfs = fp_bnfs, ...}, fp_nesting_bnfs, live_nesting_bnfs,
        fp_co_induct_sugar = SOME _, ...} : fp_sugar) :: _)
      lthy0 =
    let
      val data = Data.get (Context.Proof lthy0);

      val Ts = map #T fp_sugars
      val T_names = map (fst o dest_Type) Ts;
      val nn = length Ts;

      val B_ify = Term.typ_subst_atomic (As ~~ Bs);

      val recs = map (#co_rec o the o #fp_co_induct_sugar) fp_sugars;
      val rec_thmss = map (#co_rec_thms o the o #fp_co_induct_sugar) fp_sugars;
      val rec_Ts as rec_T1 :: _ = map fastype_of recs;
      val rec_arg_Ts = binder_fun_types rec_T1;
      val Cs = map body_type rec_Ts;
      val Cs_rho = map (rpair HOLogic.natT) Cs;
      val substCnatT = Term.subst_atomic_types Cs_rho;

      val f_Ts = map mk_to_natT As;
      val f_TsB = map mk_to_natT Bs;
      val num_As = length As;

      fun variant_names n pre = fst (Variable.variant_fixes (replicate n pre) lthy0);

      val f_names = variant_names num_As "f";
      val fs = map2 (curry Free) f_names f_Ts;
      val fsB = map2 (curry Free) f_names f_TsB;
      val As_fs = As ~~ fs;

      val size_bs =
        map ((fn base => Binding.qualify false base (Binding.name (prefix size_N base))) o
          Long_Name.base_name) T_names;

      fun is_prod_C \<^type_name>\<open>prod\<close> [_, T'] = member (op =) Cs T'
        | is_prod_C _ _ = false;

      fun mk_size_of_typ (T as TFree _) =
          pair (case AList.lookup (op =) As_fs T of
              SOME f => f
            | NONE => if member (op =) Cs T then Term.absdummy T (Bound 0) else mk_abs_zero_nat T)
        | mk_size_of_typ (T as Type (s, Ts)) =
          if is_prod_C s Ts then
            pair (snd_const T)
          else if exists (exists_subtype_in (As @ Cs)) Ts then
            (case Symtab.lookup data s of
              SOME (size_name, (_, _, size_gen_o_maps)) =>
              let
                val (args, size_gen_o_mapss') = fold_map mk_size_of_typ Ts [];
                val size_T = map fastype_of args ---> mk_to_natT T;
                val size_const = Const (size_name, size_T);
              in
                append (size_gen_o_maps :: size_gen_o_mapss')
                #> pair (Term.list_comb (size_const, args))
              end
            | _ => pair (mk_abs_zero_nat T))
          else
            pair (mk_abs_zero_nat T);

      fun mk_size_of_arg t =
        mk_size_of_typ (fastype_of t) #>> (fn s => substCnatT (betapply (s, t)));

      fun is_recursive_or_plain_case Ts =
        exists (exists_subtype_in Cs) Ts orelse forall (not o exists_subtype_in As) Ts;

      (* We want the size function to enjoy the following properties:

          1. The size of a list should coincide with its length.
          2. All the nonrecursive constructors of a type should have the same size.
          3. Each constructor through which nested recursion takes place should count as at least
             one in the generic size function.
          4. The "size" function should be definable as "size_t (%_. 0) ... (%_. 0)", where "size_t"
             is the generic function.

         This explains the somewhat convoluted logic ahead. *)

      val base_case =
        if forall (is_recursive_or_plain_case o binder_types) rec_arg_Ts then HOLogic.zero
        else HOLogic.Suc_zero;

      fun mk_size_arg rec_arg_T =
        let
          val x_Ts = binder_types rec_arg_T;
          val m = length x_Ts;
          val x_names = variant_names m "x";
          val xs = map2 (curry Free) x_names x_Ts;
          val (summands, size_gen_o_mapss) =
            fold_map mk_size_of_arg xs []
            |>> remove (op =) HOLogic.zero;
          val sum =
            if null summands then base_case else foldl1 mk_plus_nat (summands @ [HOLogic.Suc_zero]);
        in
          append size_gen_o_mapss
          #> pair (fold_rev Term.lambda (map substCnatT xs) sum)
        end;

      fun mk_size_rhs recx =
        fold_map mk_size_arg rec_arg_Ts
        #>> (fn args => fold_rev Term.lambda fs (Term.list_comb (substCnatT recx, args)));

      val maybe_conceal_def_binding = Thm.def_binding
        #> not (Config.get lthy0 bnf_internals) ? Binding.concealed;

      val (size_rhss, nested_size_gen_o_mapss) = fold_map mk_size_rhs recs [];
      val size_Ts = map fastype_of size_rhss;

      val nested_size_gen_o_maps_complete = forall (not o null) nested_size_gen_o_mapss;
      val nested_size_gen_o_maps = fold (union Thm.eq_thm_prop) nested_size_gen_o_mapss [];

      val ((raw_size_consts, raw_size_defs), (lthy1, lthy1_old)) = lthy0
        |> (snd o Local_Theory.begin_nested)
        |> apfst split_list o @{fold_map 2} (fn b => fn rhs =>
            Local_Theory.define ((b, NoSyn), ((maybe_conceal_def_binding b, []), rhs))
            #>> apsnd snd)
          size_bs size_rhss
        ||> `Local_Theory.end_nested;

      val phi = Proof_Context.export_morphism lthy1_old lthy1;

      val size_defs = map (Morphism.thm phi) raw_size_defs;

      val size_consts0 = map (Morphism.term phi) raw_size_consts;
      val size_consts = map2 retype_const_or_free size_Ts size_consts0;
      val size_constsB = map (Term.map_types B_ify) size_consts;

      val zeros = map mk_abs_zero_nat As;

      val overloaded_size_rhss = map (fn c => Term.list_comb (c, zeros)) size_consts;
      val overloaded_size_Ts = map fastype_of overloaded_size_rhss;
      val overloaded_size_consts = map (curry Const \<^const_name>\<open>size\<close>) overloaded_size_Ts;
      val overloaded_size_def_bs =
        map (maybe_conceal_def_binding o Binding.suffix_name "_overloaded") size_bs;

      fun define_overloaded_size def_b lhs0 rhs lthy =
        let
          val Free (c, _) = Syntax.check_term lthy lhs0;
          val ((_, (_, thm)), lthy') = lthy
            |> Local_Theory.define ((Binding.name c, NoSyn), ((def_b, []), rhs));
          val thy_ctxt = Proof_Context.init_global (Proof_Context.theory_of lthy');
          val thm' = singleton (Proof_Context.export lthy' thy_ctxt) thm;
        in (thm', lthy') end;

      val (overloaded_size_defs, lthy2) = lthy1
        |> Local_Theory.background_theory_result
          (Class.instantiation (T_names, map dest_TFree As, [HOLogic.class_size])
           #> @{fold_map 3} define_overloaded_size overloaded_size_def_bs overloaded_size_consts
             overloaded_size_rhss
           ##> Class.prove_instantiation_instance (fn ctxt => Class.intro_classes_tac ctxt [])
           ##> Local_Theory.exit_global);

      val size_defs' =
        map (mk_unabs_def (num_As + 1) o HOLogic.mk_obj_eq) size_defs;
      val size_defs_unused_0 =
        map (mk_unabs_def_unused_0 (num_As + 1) o HOLogic.mk_obj_eq) size_defs;
      val overloaded_size_defs' =
        map (mk_unabs_def 1 o HOLogic.mk_obj_eq) overloaded_size_defs;

      val nested_size_maps =
        map (mk_pointful lthy2) nested_size_gen_o_maps @ nested_size_gen_o_maps;
      val all_inj_maps =
        @{thm prod.inj_map} :: map inj_map_of_bnf (fp_bnfs @ fp_nesting_bnfs @ live_nesting_bnfs)
        |> distinct Thm.eq_thm_prop;

      fun derive_size_simp size_def' simp0 =
        (trans OF [size_def', simp0])
        |> Simplifier.asm_full_simplify (ss_only (@{thms inj_on_convol_ident id_def o_def
          snd_conv} @ all_inj_maps @ nested_size_maps) lthy2)
        |> Local_Defs.fold lthy2 size_defs_unused_0;

      fun derive_overloaded_size_simp overloaded_size_def' simp0 =
        (trans OF [overloaded_size_def', simp0])
        |> unfold_thms lthy2 @{thms add_0_left add_0_right}
        |> Local_Defs.fold lthy2 (overloaded_size_defs @ all_overloaded_size_defs_of lthy2);

      val size_simpss = map2 (map o derive_size_simp) size_defs' rec_thmss;
      val size_simps = flat size_simpss;
      val overloaded_size_simpss =
        map2 (map o derive_overloaded_size_simp) overloaded_size_defs' size_simpss;
      val overloaded_size_simps = flat overloaded_size_simpss;
      val size_thmss = map2 append size_simpss overloaded_size_simpss;
      val size_gen_thmss = size_simpss;

      fun rhs_is_zero thm =
        let val Const (trueprop, _) $ (Const (eq, _) $ _ $ rhs) = Thm.prop_of thm in
          trueprop = \<^const_name>\<open>Trueprop\<close> andalso eq = \<^const_name>\<open>HOL.eq\<close> andalso
          rhs = HOLogic.zero
        end;

      val size_neq_thmss = @{map 3} (fn fp_sugar => fn size => fn size_thms =>
        if exists rhs_is_zero size_thms then
          []
        else
          let
            val (xs, _) = mk_Frees "x" (binder_types (fastype_of size)) lthy2;
            val goal =
              HOLogic.mk_Trueprop (BNF_LFP_Util.mk_not_eq (list_comb (size, xs)) HOLogic.zero);
            val vars = Variable.add_free_names lthy2 goal [];
            val thm =
              Goal.prove_sorry lthy2 vars [] goal (fn {context = ctxt, ...} =>
                mk_size_neq ctxt (map (Thm.cterm_of lthy2) xs)
                (#exhaust (#ctr_sugar (#fp_ctr_sugar fp_sugar))) size_thms)
              |> single
              |> map (Thm.close_derivation \<^here>);
          in thm end) fp_sugars overloaded_size_consts overloaded_size_simpss;

      val ABs = As ~~ Bs;
      val g_names = variant_names num_As "g";
      val gs = map2 (curry Free) g_names (map (op -->) ABs);

      val liveness = map (op <>) ABs;
      val live_gs = AList.find (op =) (gs ~~ liveness) true;
      val live = length live_gs;

      val maps0 = map map_of_bnf fp_bnfs;

      val size_gen_o_map_thmss =
        if live = 0 then
          replicate nn []
        else
          let
            val gmaps = map (fn map0 => Term.list_comb (mk_map live As Bs map0, live_gs)) maps0;

            val size_gen_o_map_conds =
              if exists (can Logic.dest_implies o Thm.prop_of) nested_size_gen_o_maps then
                map (HOLogic.mk_Trueprop o mk_inj) live_gs
              else
                [];

            val fsizes = map (fn size_constB => Term.list_comb (size_constB, fsB)) size_constsB;
            val size_gen_o_map_lhss = map2 (curry HOLogic.mk_comp) fsizes gmaps;

            val fgs = map2 (fn fB => fn g as Free (_, Type (_, [A, B])) =>
              if A = B then fB else HOLogic.mk_comp (fB, g)) fsB gs;
            val size_gen_o_map_rhss = map (fn c => Term.list_comb (c, fgs)) size_consts;

            val size_gen_o_map_goals =
              map2 (fold_rev (fold_rev Logic.all) [fsB, gs] o
                curry Logic.list_implies size_gen_o_map_conds o HOLogic.mk_Trueprop oo
                curry HOLogic.mk_eq) size_gen_o_map_lhss size_gen_o_map_rhss;

            val rec_o_maps =
              fold_rev (curry (op @) o #co_rec_o_maps o the o #fp_co_induct_sugar) fp_sugars [];

            val size_gen_o_map_thmss =
              if nested_size_gen_o_maps_complete
                 andalso forall (fn TFree (_, S) => S = \<^sort>\<open>type\<close>) As then
                @{map 3} (fn goal => fn size_def => fn rec_o_map =>
                    Goal.prove_sorry lthy2 [] [] goal (fn {context = ctxt, ...} =>
                      mk_size_gen_o_map_tac ctxt size_def rec_o_map all_inj_maps nested_size_maps)
                    |> Thm.close_derivation \<^here>
                    |> single)
                  size_gen_o_map_goals size_defs rec_o_maps
              else
                replicate nn [];
          in
            size_gen_o_map_thmss
          end;

      val massage_multi_notes =
        maps (fn (thmN, thmss, attrs) =>
          map2 (fn T_name => fn thms =>
              ((Binding.qualify true (Long_Name.base_name T_name) (Binding.name thmN), attrs),
               [(thms, [])]))
            T_names thmss)
        #> filter_out (null o fst o hd o snd);

      val notes =
        [(sizeN, size_thmss, nitpicksimp_attrs @ simp_attrs),
         (size_genN, size_gen_thmss, []),
         (size_gen_o_mapN, size_gen_o_map_thmss, []),
         (size_neqN, size_neq_thmss, [])]
        |> massage_multi_notes;

      val (noted, lthy3) =
        lthy2
        |> Spec_Rules.add Binding.empty Spec_Rules.equational size_consts size_simps
        |> Spec_Rules.add Binding.empty Spec_Rules.equational
            overloaded_size_consts overloaded_size_simps
        |> Code.declare_default_eqns (map (rpair true) (flat size_thmss))
          (*Ideally, this would be issued only if the "code" plugin is enabled.*)
        |> Local_Theory.notes notes;

      val phi0 = substitute_noted_thm noted;
    in
      lthy3
      |> Local_Theory.declaration {syntax = false, pervasive = true}
        (fn phi => Data.map (@{fold 3} (fn T_name => fn Const (size_name, _) =>
            fn overloaded_size_def =>
               let val morph = Morphism.thm (phi0 $> phi) in
                 Symtab.update (T_name, (size_name, (morph overloaded_size_def,
                   map morph overloaded_size_simps, maps (map morph) size_gen_o_map_thmss)))
               end)
           T_names size_consts overloaded_size_defs))
    end
  | generate_datatype_size _ lthy = lthy;

val size_plugin = Plugin_Name.declare_setup \<^binding>\<open>size\<close>;
val _ = Theory.setup (fp_sugars_interpretation size_plugin generate_datatype_size);

end;
