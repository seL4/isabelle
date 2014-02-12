(*  Title:      HOL/Tools/Ctr_Sugar/ctr_sugar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013

Wrapping existing freely generated type's constructors.
*)

signature CTR_SUGAR =
sig
  type ctr_sugar =
    {ctrs: term list,
     casex: term,
     discs: term list,
     selss: term list list,
     exhaust: thm,
     nchotomy: thm,
     injects: thm list,
     distincts: thm list,
     case_thms: thm list,
     case_cong: thm,
     weak_case_cong: thm,
     split: thm,
     split_asm: thm,
     disc_thmss: thm list list,
     discIs: thm list,
     sel_thmss: thm list list,
     disc_excludesss: thm list list list,
     disc_exhausts: thm list,
     sel_exhausts: thm list,
     collapses: thm list,
     expands: thm list,
     sel_splits: thm list,
     sel_split_asms: thm list,
     case_eq_ifs: thm list};

  val morph_ctr_sugar: morphism -> ctr_sugar -> ctr_sugar
  val transfer_ctr_sugar: Proof.context -> ctr_sugar -> ctr_sugar
  val ctr_sugar_of: Proof.context -> string -> ctr_sugar option
  val ctr_sugars_of: Proof.context -> ctr_sugar list
  val ctr_sugar_of_case: Proof.context -> string -> ctr_sugar option
  val register_ctr_sugar: string -> ctr_sugar -> local_theory -> local_theory
  val register_ctr_sugar_global: string -> ctr_sugar -> theory -> theory

  val rep_compat_prefix: string

  val mk_half_pairss: 'a list * 'a list -> ('a * 'a) list list
  val join_halves: int -> 'a list list -> 'a list list -> 'a list * 'a list list list

  val mk_ctr: typ list -> term -> term
  val mk_case: typ list -> typ -> term -> term
  val mk_disc_or_sel: typ list -> term -> term
  val name_of_ctr: term -> string
  val name_of_disc: term -> string
  val dest_ctr: Proof.context -> string -> term -> term * term list
  val dest_case: Proof.context -> string -> typ list -> term ->
    (ctr_sugar * term list * term list) option

  val wrap_free_constructors: ({prems: thm list, context: Proof.context} -> tactic) list list ->
    (((bool * (bool * bool)) * term list) * binding) *
      (binding list * (binding list list * (binding * term) list list)) -> local_theory ->
    ctr_sugar * local_theory
  val parse_wrap_free_constructors_options: (bool * (bool * bool)) parser
  val parse_bound_term: (binding * string) parser
end;

structure Ctr_Sugar : CTR_SUGAR =
struct

open Ctr_Sugar_Util
open Ctr_Sugar_Tactics
open Ctr_Sugar_Code

type ctr_sugar =
  {ctrs: term list,
   casex: term,
   discs: term list,
   selss: term list list,
   exhaust: thm,
   nchotomy: thm,
   injects: thm list,
   distincts: thm list,
   case_thms: thm list,
   case_cong: thm,
   weak_case_cong: thm,
   split: thm,
   split_asm: thm,
   disc_thmss: thm list list,
   discIs: thm list,
   sel_thmss: thm list list,
   disc_excludesss: thm list list list,
   disc_exhausts: thm list,
   sel_exhausts: thm list,
   collapses: thm list,
   expands: thm list,
   sel_splits: thm list,
   sel_split_asms: thm list,
   case_eq_ifs: thm list};

fun morph_ctr_sugar phi {ctrs, casex, discs, selss, exhaust, nchotomy, injects, distincts,
    case_thms, case_cong, weak_case_cong, split, split_asm, disc_thmss, discIs, sel_thmss,
    disc_excludesss, disc_exhausts, sel_exhausts, collapses, expands, sel_splits, sel_split_asms,
    case_eq_ifs} =
  {ctrs = map (Morphism.term phi) ctrs,
   casex = Morphism.term phi casex,
   discs = map (Morphism.term phi) discs,
   selss = map (map (Morphism.term phi)) selss,
   exhaust = Morphism.thm phi exhaust,
   nchotomy = Morphism.thm phi nchotomy,
   injects = map (Morphism.thm phi) injects,
   distincts = map (Morphism.thm phi) distincts,
   case_thms = map (Morphism.thm phi) case_thms,
   case_cong = Morphism.thm phi case_cong,
   weak_case_cong = Morphism.thm phi weak_case_cong,
   split = Morphism.thm phi split,
   split_asm = Morphism.thm phi split_asm,
   disc_thmss = map (map (Morphism.thm phi)) disc_thmss,
   discIs = map (Morphism.thm phi) discIs,
   sel_thmss = map (map (Morphism.thm phi)) sel_thmss,
   disc_excludesss = map (map (map (Morphism.thm phi))) disc_excludesss,
   disc_exhausts = map (Morphism.thm phi) disc_exhausts,
   sel_exhausts = map (Morphism.thm phi) sel_exhausts,
   collapses = map (Morphism.thm phi) collapses,
   expands = map (Morphism.thm phi) expands,
   sel_splits = map (Morphism.thm phi) sel_splits,
   sel_split_asms = map (Morphism.thm phi) sel_split_asms,
   case_eq_ifs = map (Morphism.thm phi) case_eq_ifs};

val transfer_ctr_sugar =
  morph_ctr_sugar o Morphism.transfer_morphism o Proof_Context.theory_of;

structure Data = Generic_Data
(
  type T = ctr_sugar Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (K true) data;
);

fun ctr_sugar_of ctxt =
  Symtab.lookup (Data.get (Context.Proof ctxt))
  #> Option.map (transfer_ctr_sugar ctxt);

fun ctr_sugars_of ctxt =
  Symtab.fold (cons o transfer_ctr_sugar ctxt o snd) (Data.get (Context.Proof ctxt)) [];

fun ctr_sugar_of_case ctxt s =
  find_first (fn {casex = Const (s', _), ...} => s' = s | _ => false) (ctr_sugars_of ctxt);

fun register_ctr_sugar key ctr_sugar =
  Local_Theory.declaration {syntax = false, pervasive = true}
    (fn phi => Data.map (Symtab.default (key, morph_ctr_sugar phi ctr_sugar)));

fun register_ctr_sugar_global key ctr_sugar =
  Context.theory_map (Data.map (Symtab.default (key, ctr_sugar)));

val rep_compat_prefix = "new";

val isN = "is_";
val unN = "un_";
fun mk_unN 1 1 suf = unN ^ suf
  | mk_unN _ l suf = unN ^ suf ^ string_of_int l;

val caseN = "case";
val case_congN = "case_cong";
val case_eq_ifN = "case_eq_if";
val collapseN = "collapse";
val disc_excludeN = "disc_exclude";
val disc_exhaustN = "disc_exhaust";
val discN = "disc";
val discIN = "discI";
val distinctN = "distinct";
val exhaustN = "exhaust";
val expandN = "expand";
val injectN = "inject";
val nchotomyN = "nchotomy";
val selN = "sel";
val sel_exhaustN = "sel_exhaust";
val sel_splitN = "sel_split";
val sel_split_asmN = "sel_split_asm";
val splitN = "split";
val splitsN = "splits";
val split_asmN = "split_asm";
val weak_case_cong_thmsN = "weak_case_cong";

val cong_attrs = @{attributes [cong]};
val dest_attrs = @{attributes [dest]};
val safe_elim_attrs = @{attributes [elim!]};
val iff_attrs = @{attributes [iff]};
val inductsimp_attrs = @{attributes [induct_simp]};
val nitpicksimp_attrs = @{attributes [nitpick_simp]};
val simp_attrs = @{attributes [simp]};
val code_nitpicksimp_attrs = Code.add_default_eqn_attrib :: nitpicksimp_attrs;
val code_nitpicksimp_simp_attrs = code_nitpicksimp_attrs @ simp_attrs;

fun unflat_lookup eq xs ys = map (fn xs' => permute_like eq xs xs' ys);

fun mk_half_pairss' _ ([], []) = []
  | mk_half_pairss' indent (x :: xs, _ :: ys) =
    indent @ fold_rev (cons o single o pair x) ys (mk_half_pairss' ([] :: indent) (xs, ys));

fun mk_half_pairss p = mk_half_pairss' [[]] p;

fun join_halves n half_xss other_half_xss =
  (splice (flat half_xss) (flat other_half_xss),
   map2 (map2 append) (Library.chop_groups n half_xss)
     (transpose (Library.chop_groups n other_half_xss)));

fun mk_undefined T = Const (@{const_name undefined}, T);

fun mk_ctr Ts t =
  let val Type (_, Ts0) = body_type (fastype_of t) in
    subst_nonatomic_types (Ts0 ~~ Ts) t
  end;

fun mk_case Ts T t =
  let val (Type (_, Ts0), body) = strip_type (fastype_of t) |>> List.last in
    subst_nonatomic_types ((body, T) :: (Ts0 ~~ Ts)) t
  end;

fun mk_disc_or_sel Ts t =
  subst_nonatomic_types (snd (Term.dest_Type (domain_type (fastype_of t))) ~~ Ts) t;

fun name_of_const what t =
  (case head_of t of
    Const (s, _) => s
  | Free (s, _) => s
  | _ => error ("Cannot extract name of " ^ what));

val name_of_ctr = name_of_const "constructor";

val notN = "not_";
val eqN = "eq_";
val neqN = "neq_";

fun name_of_disc t =
  (case head_of t of
    Abs (_, _, @{const Not} $ (t' $ Bound 0)) =>
    Long_Name.map_base_name (prefix notN) (name_of_disc t')
  | Abs (_, _, Const (@{const_name HOL.eq}, _) $ Bound 0 $ t') =>
    Long_Name.map_base_name (prefix eqN) (name_of_disc t')
  | Abs (_, _, @{const Not} $ (Const (@{const_name HOL.eq}, _) $ Bound 0 $ t')) =>
    Long_Name.map_base_name (prefix neqN) (name_of_disc t')
  | t' => name_of_const "destructor" t');

val base_name_of_ctr = Long_Name.base_name o name_of_ctr;

fun dest_ctr ctxt s t =
  let val (f, args) = Term.strip_comb t in
    (case ctr_sugar_of ctxt s of
      SOME {ctrs, ...} =>
      (case find_first (can (fo_match ctxt f)) ctrs of
        SOME f' => (f', args)
      | NONE => raise Fail "dest_ctr")
    | NONE => raise Fail "dest_ctr")
  end;

fun dest_case ctxt s Ts t =
  (case Term.strip_comb t of
    (Const (c, _), args as _ :: _) =>
    (case ctr_sugar_of ctxt s of
      SOME (ctr_sugar as {casex = Const (case_name, _), discs = discs0, selss = selss0, ...}) =>
      if case_name = c then
        let val n = length discs0 in
          if n < length args then
            let
              val (branches, obj :: leftovers) = chop n args;
              val discs = map (mk_disc_or_sel Ts) discs0;
              val selss = map (map (mk_disc_or_sel Ts)) selss0;
              val conds = map (rapp obj) discs;
              val branch_argss = map (fn sels => map (rapp obj) sels @ leftovers) selss;
              val branches' = map2 (curry Term.betapplys) branches branch_argss;
            in
              SOME (ctr_sugar, conds, branches')
            end
          else
            NONE
        end
      else
        NONE
    | _ => NONE)
  | _ => NONE);

fun eta_expand_arg xs f_xs = fold_rev Term.lambda xs f_xs;

fun prepare_wrap_free_constructors prep_term ((((no_discs_sels, (no_code, rep_compat)), raw_ctrs),
    raw_case_binding), (raw_disc_bindings, (raw_sel_bindingss, raw_sel_defaultss))) no_defs_lthy =
  let
    (* TODO: sanity checks on arguments *)

    val n = length raw_ctrs;
    val ks = 1 upto n;

    val _ = if n > 0 then () else error "No constructors specified";

    val ctrs0 = map (prep_term no_defs_lthy) raw_ctrs;
    val sel_defaultss =
      pad_list [] n (map (map (apsnd (prep_term no_defs_lthy))) raw_sel_defaultss);

    val Type (fcT_name, As0) = body_type (fastype_of (hd ctrs0));
    val fc_b_name = Long_Name.base_name fcT_name;
    val fc_b = Binding.name fc_b_name;

    fun qualify mandatory =
      Binding.qualify mandatory fc_b_name o (rep_compat ? Binding.qualify false rep_compat_prefix);

    fun dest_TFree_or_TVar (TFree sS) = sS
      | dest_TFree_or_TVar (TVar ((s, _), S)) = (s, S)
      | dest_TFree_or_TVar _ = error "Invalid type argument";

    val (unsorted_As, B) =
      no_defs_lthy
      |> variant_tfrees (map (fst o dest_TFree_or_TVar) As0)
      ||> the_single o fst o mk_TFrees 1;

    val As = map2 (resort_tfree o snd o dest_TFree_or_TVar) As0 unsorted_As;

    val fcT = Type (fcT_name, As);
    val ctrs = map (mk_ctr As) ctrs0;
    val ctr_Tss = map (binder_types o fastype_of) ctrs;

    val ms = map length ctr_Tss;

    val raw_disc_bindings' = pad_list Binding.empty n raw_disc_bindings;

    fun can_definitely_rely_on_disc k = not (Binding.is_empty (nth raw_disc_bindings' (k - 1)));
    fun can_rely_on_disc k =
      can_definitely_rely_on_disc k orelse (k = 1 andalso not (can_definitely_rely_on_disc 2));
    fun should_omit_disc_binding k = n = 1 orelse (n = 2 andalso can_rely_on_disc (3 - k));

    fun is_disc_binding_valid b =
      not (Binding.is_empty b orelse Binding.eq_name (b, equal_binding));

    val standard_disc_binding = Binding.name o prefix isN o base_name_of_ctr;

    val disc_bindings =
      raw_disc_bindings'
      |> map4 (fn k => fn m => fn ctr => fn disc =>
        qualify false
          (if Binding.is_empty disc then
             if should_omit_disc_binding k then disc else standard_disc_binding ctr
           else if Binding.eq_name (disc, equal_binding) then
             if m = 0 then disc
             else error "Cannot use \"=\" syntax for discriminating nonnullary constructor"
           else if Binding.eq_name (disc, standard_binding) then
             standard_disc_binding ctr
           else
             disc)) ks ms ctrs0;

    fun standard_sel_binding m l = Binding.name o mk_unN m l o base_name_of_ctr;

    val sel_bindingss =
      pad_list [] n raw_sel_bindingss
      |> map3 (fn ctr => fn m => map2 (fn l => fn sel =>
        qualify false
          (if Binding.is_empty sel orelse Binding.eq_name (sel, standard_binding) then
            standard_sel_binding m l ctr
          else
            sel)) (1 upto m) o pad_list Binding.empty m) ctrs0 ms;

    val case_Ts = map (fn Ts => Ts ---> B) ctr_Tss;

    val ((((((((xss, xss'), yss), fs), gs), [u', v']), [w]), (p, p')), names_lthy) = no_defs_lthy |>
      mk_Freess' "x" ctr_Tss
      ||>> mk_Freess "y" ctr_Tss
      ||>> mk_Frees "f" case_Ts
      ||>> mk_Frees "g" case_Ts
      ||>> (apfst (map (rpair fcT)) oo Variable.variant_fixes) [fc_b_name, fc_b_name ^ "'"]
      ||>> mk_Frees "z" [B]
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "P") HOLogic.boolT;

    val u = Free u';
    val v = Free v';
    val q = Free (fst p', mk_pred1T B);

    val xctrs = map2 (curry Term.list_comb) ctrs xss;
    val yctrs = map2 (curry Term.list_comb) ctrs yss;

    val xfs = map2 (curry Term.list_comb) fs xss;
    val xgs = map2 (curry Term.list_comb) gs xss;

    (* TODO: Eta-expension is for compatibility with the old datatype package (but it also provides
       nicer names). Consider removing. *)
    val eta_fs = map2 eta_expand_arg xss xfs;
    val eta_gs = map2 eta_expand_arg xss xgs;

    val case_binding =
      qualify false
        (if Binding.is_empty raw_case_binding orelse
            Binding.eq_name (raw_case_binding, standard_binding) then
           Binding.prefix_name (caseN ^ "_") fc_b
         else
           raw_case_binding);

    fun mk_case_disj xctr xf xs =
      list_exists_free xs (HOLogic.mk_conj (HOLogic.mk_eq (u, xctr), HOLogic.mk_eq (w, xf)));

    val case_rhs = fold_rev (fold_rev Term.lambda) [fs, [u]]
      (Const (@{const_name The}, (B --> HOLogic.boolT) --> B) $
         Term.lambda w (Library.foldr1 HOLogic.mk_disj (map3 mk_case_disj xctrs xfs xss)));

    val ((raw_case, (_, raw_case_def)), (lthy', lthy)) = no_defs_lthy
      |> Local_Theory.define ((case_binding, NoSyn),
        ((Binding.conceal (Thm.def_binding case_binding), []), case_rhs))
      ||> `Local_Theory.restore;

    val phi = Proof_Context.export_morphism lthy lthy';

    val case_def = Morphism.thm phi raw_case_def;

    val case0 = Morphism.term phi raw_case;
    val casex = mk_case As B case0;

    val fcase = Term.list_comb (casex, fs);

    val ufcase = fcase $ u;
    val vfcase = fcase $ v;

    val eta_fcase = Term.list_comb (casex, eta_fs);
    val eta_gcase = Term.list_comb (casex, eta_gs);

    val eta_ufcase = eta_fcase $ u;
    val eta_vgcase = eta_gcase $ v;

    fun mk_uu_eq () = HOLogic.mk_eq (u, u);

    val uv_eq = mk_Trueprop_eq (u, v);

    val exist_xs_u_eq_ctrs =
      map2 (fn xctr => fn xs => list_exists_free xs (HOLogic.mk_eq (u, xctr))) xctrs xss;

    val unique_disc_no_def = TrueI; (*arbitrary marker*)
    val alternate_disc_no_def = FalseE; (*arbitrary marker*)

    fun alternate_disc_lhs get_udisc k =
      HOLogic.mk_not
        (let val b = nth disc_bindings (k - 1) in
           if is_disc_binding_valid b then get_udisc b (k - 1) else nth exist_xs_u_eq_ctrs (k - 1)
         end);

    val (all_sels_distinct, discs, selss, disc_defs, sel_defs, sel_defss, lthy') =
      if no_discs_sels then
        (true, [], [], [], [], [], lthy)
      else
        let
          fun disc_free b = Free (Binding.name_of b, mk_pred1T fcT);

          fun disc_spec b exist_xs_u_eq_ctr = mk_Trueprop_eq (disc_free b $ u, exist_xs_u_eq_ctr);

          fun alternate_disc k =
            Term.lambda u (alternate_disc_lhs (K o rapp u o disc_free) (3 - k));

          fun mk_sel_case_args b proto_sels T =
            map2 (fn Ts => fn k =>
              (case AList.lookup (op =) proto_sels k of
                NONE =>
                (case AList.lookup Binding.eq_name (rev (nth sel_defaultss (k - 1))) b of
                  NONE => fold_rev (Term.lambda o curry Free Name.uu) Ts (mk_undefined T)
                | SOME t => t |> Type.constraint (Ts ---> T) |> Syntax.check_term lthy)
              | SOME (xs, x) => fold_rev Term.lambda xs x)) ctr_Tss ks;

          fun sel_spec b proto_sels =
            let
              val _ =
                (case duplicates (op =) (map fst proto_sels) of
                   k :: _ => error ("Duplicate selector name " ^ quote (Binding.name_of b) ^
                     " for constructor " ^
                     quote (Syntax.string_of_term lthy (nth ctrs (k - 1))))
                 | [] => ())
              val T =
                (case distinct (op =) (map (fastype_of o snd o snd) proto_sels) of
                  [T] => T
                | T :: T' :: _ => error ("Inconsistent range type for selector " ^
                    quote (Binding.name_of b) ^ ": " ^ quote (Syntax.string_of_typ lthy T) ^ " vs. "
                    ^ quote (Syntax.string_of_typ lthy T')));
            in
              mk_Trueprop_eq (Free (Binding.name_of b, fcT --> T) $ u,
                Term.list_comb (mk_case As T case0, mk_sel_case_args b proto_sels T) $ u)
            end;

          val sel_bindings = flat sel_bindingss;
          val uniq_sel_bindings = distinct Binding.eq_name sel_bindings;
          val all_sels_distinct = (length uniq_sel_bindings = length sel_bindings);

          val sel_binding_index =
            if all_sels_distinct then 1 upto length sel_bindings
            else map (fn b => find_index (curry Binding.eq_name b) uniq_sel_bindings) sel_bindings;

          val proto_sels = flat (map3 (fn k => fn xs => map (fn x => (k, (xs, x)))) ks xss xss);
          val sel_infos =
            AList.group (op =) (sel_binding_index ~~ proto_sels)
            |> sort (int_ord o pairself fst)
            |> map snd |> curry (op ~~) uniq_sel_bindings;
          val sel_bindings = map fst sel_infos;

          fun unflat_selss xs = unflat_lookup Binding.eq_name sel_bindings xs sel_bindingss;

          val (((raw_discs, raw_disc_defs), (raw_sels, raw_sel_defs)), (lthy', lthy)) =
            lthy
            |> apfst split_list o fold_map3 (fn k => fn exist_xs_u_eq_ctr => fn b =>
                if Binding.is_empty b then
                  if n = 1 then pair (Term.lambda u (mk_uu_eq ()), unique_disc_no_def)
                  else pair (alternate_disc k, alternate_disc_no_def)
                else if Binding.eq_name (b, equal_binding) then
                  pair (Term.lambda u exist_xs_u_eq_ctr, refl)
                else
                  Specification.definition (SOME (b, NONE, NoSyn),
                    ((Thm.def_binding b, []), disc_spec b exist_xs_u_eq_ctr)) #>> apsnd snd)
              ks exist_xs_u_eq_ctrs disc_bindings
            ||>> apfst split_list o fold_map (fn (b, proto_sels) =>
              Specification.definition (SOME (b, NONE, NoSyn),
                ((Thm.def_binding b, []), sel_spec b proto_sels)) #>> apsnd snd) sel_infos
            ||> `Local_Theory.restore;

          val phi = Proof_Context.export_morphism lthy lthy';

          val disc_defs = map (Morphism.thm phi) raw_disc_defs;
          val sel_defs = map (Morphism.thm phi) raw_sel_defs;
          val sel_defss = unflat_selss sel_defs;

          val discs0 = map (Morphism.term phi) raw_discs;
          val selss0 = unflat_selss (map (Morphism.term phi) raw_sels);

          val discs = map (mk_disc_or_sel As) discs0;
          val selss = map (map (mk_disc_or_sel As)) selss0;
        in
          (all_sels_distinct, discs, selss, disc_defs, sel_defs, sel_defss, lthy')
        end;

    fun mk_imp_p Qs = Logic.list_implies (Qs, HOLogic.mk_Trueprop p);

    val exhaust_goal =
      let fun mk_prem xctr xs = fold_rev Logic.all xs (mk_imp_p [mk_Trueprop_eq (u, xctr)]) in
        fold_rev Logic.all [p, u] (mk_imp_p (map2 mk_prem xctrs xss))
      end;

    val inject_goalss =
      let
        fun mk_goal _ _ [] [] = []
          | mk_goal xctr yctr xs ys =
            [fold_rev Logic.all (xs @ ys) (mk_Trueprop_eq (HOLogic.mk_eq (xctr, yctr),
              Library.foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_eq) xs ys)))];
      in
        map4 mk_goal xctrs yctrs xss yss
      end;

    val half_distinct_goalss =
      let
        fun mk_goal ((xs, xc), (xs', xc')) =
          fold_rev Logic.all (xs @ xs')
            (HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (xc, xc'))));
      in
        map (map mk_goal) (mk_half_pairss (`I (xss ~~ xctrs)))
      end;

    val goalss = [exhaust_goal] :: inject_goalss @ half_distinct_goalss;

    fun after_qed thmss lthy =
      let
        val ([exhaust_thm], (inject_thmss, half_distinct_thmss)) = (hd thmss, chop n (tl thmss));

        val inject_thms = flat inject_thmss;

        val rho_As = map (pairself (certifyT lthy)) (map Logic.varifyT_global As ~~ As);

        fun inst_thm t thm =
          Drule.instantiate' [] [SOME (certify lthy t)]
            (Thm.instantiate (rho_As, []) (Drule.zero_var_indexes thm));

        val uexhaust_thm = inst_thm u exhaust_thm;

        val exhaust_cases = map base_name_of_ctr ctrs;

        val other_half_distinct_thmss = map (map (fn thm => thm RS not_sym)) half_distinct_thmss;

        val (distinct_thms, (distinct_thmsss', distinct_thmsss)) =
          join_halves n half_distinct_thmss other_half_distinct_thmss ||> `transpose;

        val nchotomy_thm =
          let
            val goal =
              HOLogic.mk_Trueprop (HOLogic.mk_all (fst u', snd u',
                Library.foldr1 HOLogic.mk_disj exist_xs_u_eq_ctrs));
          in
            Goal.prove_sorry lthy [] [] goal (fn _ => mk_nchotomy_tac n exhaust_thm)
            |> Thm.close_derivation
          end;

        val case_thms =
          let
            val goals =
              map3 (fn xctr => fn xf => fn xs =>
                fold_rev Logic.all (fs @ xs) (mk_Trueprop_eq (fcase $ xctr, xf))) xctrs xfs xss;
          in
            map4 (fn k => fn goal => fn injects => fn distinctss =>
                Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, ...} =>
                  mk_case_tac ctxt n k case_def injects distinctss)
                |> Thm.close_derivation)
              ks goals inject_thmss distinct_thmsss
          end;

        val (case_cong_thm, weak_case_cong_thm) =
          let
            fun mk_prem xctr xs xf xg =
              fold_rev Logic.all xs (Logic.mk_implies (mk_Trueprop_eq (v, xctr),
                mk_Trueprop_eq (xf, xg)));

            val goal =
              Logic.list_implies (uv_eq :: map4 mk_prem xctrs xss xfs xgs,
                 mk_Trueprop_eq (eta_ufcase, eta_vgcase));
            val weak_goal = Logic.mk_implies (uv_eq, mk_Trueprop_eq (ufcase, vfcase));
          in
            (Goal.prove_sorry lthy [] [] goal (fn _ => mk_case_cong_tac lthy uexhaust_thm case_thms),
             Goal.prove_sorry lthy [] [] weak_goal (K (etac arg_cong 1)))
            |> pairself (Thm.close_derivation #> singleton (Proof_Context.export names_lthy lthy))
          end;

        val split_lhs = q $ ufcase;

        fun mk_split_conjunct xctr xs f_xs =
          list_all_free xs (HOLogic.mk_imp (HOLogic.mk_eq (u, xctr), q $ f_xs));
        fun mk_split_disjunct xctr xs f_xs =
          list_exists_free xs (HOLogic.mk_conj (HOLogic.mk_eq (u, xctr),
            HOLogic.mk_not (q $ f_xs)));

        fun mk_split_goal xctrs xss xfs =
          mk_Trueprop_eq (split_lhs, Library.foldr1 HOLogic.mk_conj
            (map3 mk_split_conjunct xctrs xss xfs));
        fun mk_split_asm_goal xctrs xss xfs =
          mk_Trueprop_eq (split_lhs, HOLogic.mk_not (Library.foldr1 HOLogic.mk_disj
            (map3 mk_split_disjunct xctrs xss xfs)));

        fun prove_split selss goal =
          Goal.prove_sorry lthy [] [] goal (fn _ =>
            mk_split_tac lthy uexhaust_thm case_thms selss inject_thmss distinct_thmsss)
          |> Thm.close_derivation
          |> singleton (Proof_Context.export names_lthy lthy);

        fun prove_split_asm asm_goal split_thm =
          Goal.prove_sorry lthy [] [] asm_goal (fn {context = ctxt, ...} =>
            mk_split_asm_tac ctxt split_thm)
          |> Thm.close_derivation
          |> singleton (Proof_Context.export names_lthy lthy);

        val (split_thm, split_asm_thm) =
          let
            val goal = mk_split_goal xctrs xss xfs;
            val asm_goal = mk_split_asm_goal xctrs xss xfs;

            val thm = prove_split (replicate n []) goal;
            val asm_thm = prove_split_asm asm_goal thm;
          in
            (thm, asm_thm)
          end;

        val (all_sel_thms, sel_thmss, disc_thmss, nontriv_disc_thms, discI_thms, nontriv_discI_thms,
             disc_exclude_thms, disc_exclude_thmsss, disc_exhaust_thms, sel_exhaust_thms,
             all_collapse_thms, safe_collapse_thms, expand_thms, sel_split_thms, sel_split_asm_thms,
             case_eq_if_thms) =
          if no_discs_sels then
            ([], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [])
          else
            let
              val udiscs = map (rapp u) discs;
              val uselss = map (map (rapp u)) selss;
              val usel_ctrs = map2 (curry Term.list_comb) ctrs uselss;
              val usel_fs = map2 (curry Term.list_comb) fs uselss;

              val vdiscs = map (rapp v) discs;
              val vselss = map (map (rapp v)) selss;

              fun make_sel_thm xs' case_thm sel_def =
                zero_var_indexes (Drule.gen_all (Drule.rename_bvars' (map (SOME o fst) xs')
                    (Drule.forall_intr_vars (case_thm RS (sel_def RS trans)))));

              val sel_thmss = map3 (map oo make_sel_thm) xss' case_thms sel_defss;

              fun has_undefined_rhs thm =
                (case snd (HOLogic.dest_eq (HOLogic.dest_Trueprop (prop_of thm))) of
                  Const (@{const_name undefined}, _) => true
                | _ => false);

              val all_sel_thms =
                (if all_sels_distinct andalso forall null sel_defaultss then
                   flat sel_thmss
                 else
                   map_product (fn s => fn (xs', c) => make_sel_thm xs' c s) sel_defs
                     (xss' ~~ case_thms))
                |> filter_out has_undefined_rhs;

              fun mk_unique_disc_def () =
                let
                  val m = the_single ms;
                  val goal = mk_Trueprop_eq (mk_uu_eq (), the_single exist_xs_u_eq_ctrs);
                in
                  Goal.prove_sorry lthy [] [] goal (fn _ => mk_unique_disc_def_tac m uexhaust_thm)
                  |> Thm.close_derivation
                  |> singleton (Proof_Context.export names_lthy lthy)
                end;

              fun mk_alternate_disc_def k =
                let
                  val goal =
                    mk_Trueprop_eq (alternate_disc_lhs (K (nth udiscs)) (3 - k),
                      nth exist_xs_u_eq_ctrs (k - 1));
                in
                  Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, ...} =>
                    mk_alternate_disc_def_tac ctxt k (nth disc_defs (2 - k))
                      (nth distinct_thms (2 - k)) uexhaust_thm)
                  |> Thm.close_derivation
                  |> singleton (Proof_Context.export names_lthy lthy)
                end;

              val has_alternate_disc_def =
                exists (fn def => Thm.eq_thm_prop (def, alternate_disc_no_def)) disc_defs;

              val disc_defs' =
                map2 (fn k => fn def =>
                  if Thm.eq_thm_prop (def, unique_disc_no_def) then mk_unique_disc_def ()
                  else if Thm.eq_thm_prop (def, alternate_disc_no_def) then mk_alternate_disc_def k
                  else def) ks disc_defs;

              val discD_thms = map (fn def => def RS iffD1) disc_defs';
              val discI_thms =
                map2 (fn m => fn def => funpow m (fn thm => exI RS thm) (def RS iffD2)) ms
                  disc_defs';
              val not_discI_thms =
                map2 (fn m => fn def => funpow m (fn thm => allI RS thm)
                    (unfold_thms lthy @{thms not_ex} (def RS @{thm ssubst[of _ _ Not]})))
                  ms disc_defs';

              val (disc_thmss', disc_thmss) =
                let
                  fun mk_thm discI _ [] = refl RS discI
                    | mk_thm _ not_discI [distinct] = distinct RS not_discI;
                  fun mk_thms discI not_discI distinctss = map (mk_thm discI not_discI) distinctss;
                in
                  map3 mk_thms discI_thms not_discI_thms distinct_thmsss' |> `transpose
                end;

              val nontriv_disc_thms =
                flat (map2 (fn b => if is_disc_binding_valid b then I else K [])
                  disc_bindings disc_thmss);

              fun is_discI_boring b =
                (n = 1 andalso Binding.is_empty b) orelse Binding.eq_name (b, equal_binding);

              val nontriv_discI_thms =
                flat (map2 (fn b => if is_discI_boring b then K [] else single) disc_bindings
                  discI_thms);

              val (disc_exclude_thms, (disc_exclude_thmsss', disc_exclude_thmsss)) =
                let
                  fun mk_goal [] = []
                    | mk_goal [((_, udisc), (_, udisc'))] =
                      [Logic.all u (Logic.mk_implies (HOLogic.mk_Trueprop udisc,
                         HOLogic.mk_Trueprop (HOLogic.mk_not udisc')))];

                  fun prove tac goal =
                    Goal.prove_sorry lthy [] [] goal (K tac)
                    |> Thm.close_derivation;

                  val half_pairss = mk_half_pairss (`I (ms ~~ discD_thms ~~ udiscs));

                  val half_goalss = map mk_goal half_pairss;
                  val half_thmss =
                    map3 (fn [] => K (K []) | [goal] => fn [(((m, discD), _), _)] =>
                        fn disc_thm => [prove (mk_half_disc_exclude_tac lthy m discD disc_thm) goal])
                      half_goalss half_pairss (flat disc_thmss');

                  val other_half_goalss = map (mk_goal o map swap) half_pairss;
                  val other_half_thmss =
                    map2 (map2 (prove o mk_other_half_disc_exclude_tac)) half_thmss
                      other_half_goalss;
                in
                  join_halves n half_thmss other_half_thmss ||> `transpose
                  |>> has_alternate_disc_def ? K []
                end;

              val disc_exhaust_thm =
                let
                  fun mk_prem udisc = mk_imp_p [HOLogic.mk_Trueprop udisc];
                  val goal = fold_rev Logic.all [p, u] (mk_imp_p (map mk_prem udiscs));
                in
                  Goal.prove_sorry lthy [] [] goal (fn _ =>
                    mk_disc_exhaust_tac n exhaust_thm discI_thms)
                  |> Thm.close_derivation
                end;

              val (safe_collapse_thms, all_collapse_thms) =
                let
                  fun mk_goal m udisc usel_ctr =
                    let
                      val prem = HOLogic.mk_Trueprop udisc;
                      val concl = mk_Trueprop_eq ((usel_ctr, u) |> m = 0 ? swap);
                    in
                      (prem aconv concl, Logic.all u (Logic.mk_implies (prem, concl)))
                    end;
                  val (trivs, goals) = map3 mk_goal ms udiscs usel_ctrs |> split_list;
                  val thms =
                    map5 (fn m => fn discD => fn sel_thms => fn triv => fn goal =>
                        Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, ...} =>
                          mk_collapse_tac ctxt m discD sel_thms ORELSE HEADGOAL atac)
                        |> Thm.close_derivation
                        |> not triv ? perhaps (try (fn thm => refl RS thm)))
                      ms discD_thms sel_thmss trivs goals;
                in
                  (map_filter (fn (true, _) => NONE | (false, thm) => SOME thm) (trivs ~~ thms),
                   thms)
                end;

              val swapped_all_collapse_thms =
                map2 (fn m => fn thm => if m = 0 then thm else thm RS sym) ms all_collapse_thms;

              val sel_exhaust_thm =
                let
                  fun mk_prem usel_ctr = mk_imp_p [mk_Trueprop_eq (u, usel_ctr)];
                  val goal = fold_rev Logic.all [p, u] (mk_imp_p (map mk_prem usel_ctrs));
                in
                  Goal.prove_sorry lthy [] [] goal (fn _ =>
                    mk_sel_exhaust_tac n disc_exhaust_thm swapped_all_collapse_thms)
                  |> Thm.close_derivation
                end;

              val expand_thm =
                let
                  fun mk_prems k udisc usels vdisc vsels =
                    (if k = n then [] else [mk_Trueprop_eq (udisc, vdisc)]) @
                    (if null usels then
                       []
                     else
                       [Logic.list_implies
                          (if n = 1 then [] else map HOLogic.mk_Trueprop [udisc, vdisc],
                             HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                               (map2 (curry HOLogic.mk_eq) usels vsels)))]);

                  val goal =
                    Library.foldr Logic.list_implies
                      (map5 mk_prems ks udiscs uselss vdiscs vselss, uv_eq);
                  val uncollapse_thms =
                    map2 (fn thm => fn [] => thm | _ => thm RS sym) all_collapse_thms uselss;
                in
                  Goal.prove_sorry lthy [] [] goal (fn _ =>
                    mk_expand_tac lthy n ms (inst_thm u disc_exhaust_thm)
                      (inst_thm v disc_exhaust_thm) uncollapse_thms disc_exclude_thmsss
                      disc_exclude_thmsss')
                  |> Thm.close_derivation
                  |> singleton (Proof_Context.export names_lthy lthy)
                end;

              val (sel_split_thm, sel_split_asm_thm) =
                let
                  val zss = map (K []) xss;
                  val goal = mk_split_goal usel_ctrs zss usel_fs;
                  val asm_goal = mk_split_asm_goal usel_ctrs zss usel_fs;

                  val thm = prove_split sel_thmss goal;
                  val asm_thm = prove_split_asm asm_goal thm;
                in
                  (thm, asm_thm)
                end;

              val case_eq_if_thm =
                let
                  val goal = mk_Trueprop_eq (ufcase, mk_IfN B udiscs usel_fs);
                in
                  Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, ...} =>
                    mk_case_eq_if_tac ctxt n uexhaust_thm case_thms disc_thmss' sel_thmss)
                  |> Thm.close_derivation
                  |> singleton (Proof_Context.export names_lthy lthy)
                end;
            in
              (all_sel_thms, sel_thmss, disc_thmss, nontriv_disc_thms, discI_thms,
               nontriv_discI_thms, disc_exclude_thms, disc_exclude_thmsss, [disc_exhaust_thm],
               [sel_exhaust_thm], all_collapse_thms, safe_collapse_thms, [expand_thm],
               [sel_split_thm], [sel_split_asm_thm], [case_eq_if_thm])
            end;

        val exhaust_case_names_attr = Attrib.internal (K (Rule_Cases.case_names exhaust_cases));
        val cases_type_attr = Attrib.internal (K (Induct.cases_type fcT_name));

        val anonymous_notes =
          [(map (fn th => th RS notE) distinct_thms, safe_elim_attrs),
           (map (fn th => th RS @{thm eq_False[THEN iffD2]}
              handle THM _ => th RS @{thm eq_True[THEN iffD2]}) nontriv_disc_thms,
            code_nitpicksimp_attrs)]
          |> map (fn (thms, attrs) => ((Binding.empty, attrs), [(thms, [])]));

        val notes =
          [(caseN, case_thms, code_nitpicksimp_simp_attrs),
           (case_congN, [case_cong_thm], []),
           (case_eq_ifN, case_eq_if_thms, []),
           (collapseN, safe_collapse_thms, simp_attrs),
           (discN, nontriv_disc_thms, simp_attrs),
           (discIN, nontriv_discI_thms, []),
           (disc_excludeN, disc_exclude_thms, dest_attrs),
           (disc_exhaustN, disc_exhaust_thms, [exhaust_case_names_attr]),
           (distinctN, distinct_thms, simp_attrs @ inductsimp_attrs),
           (exhaustN, [exhaust_thm], [exhaust_case_names_attr, cases_type_attr]),
           (expandN, expand_thms, []),
           (injectN, inject_thms, iff_attrs @ inductsimp_attrs),
           (nchotomyN, [nchotomy_thm], []),
           (selN, all_sel_thms, code_nitpicksimp_simp_attrs),
           (sel_exhaustN, sel_exhaust_thms, [exhaust_case_names_attr]),
           (sel_splitN, sel_split_thms, []),
           (sel_split_asmN, sel_split_asm_thms, []),
           (splitN, [split_thm], []),
           (split_asmN, [split_asm_thm], []),
           (splitsN, [split_thm, split_asm_thm], []),
           (weak_case_cong_thmsN, [weak_case_cong_thm], cong_attrs)]
          |> filter_out (null o #2)
          |> map (fn (thmN, thms, attrs) =>
            ((qualify true (Binding.name thmN), attrs), [(thms, [])]));

        val ctr_sugar =
          {ctrs = ctrs, casex = casex, discs = discs, selss = selss, exhaust = exhaust_thm,
           nchotomy = nchotomy_thm, injects = inject_thms, distincts = distinct_thms,
           case_thms = case_thms, case_cong = case_cong_thm, weak_case_cong = weak_case_cong_thm,
           split = split_thm, split_asm = split_asm_thm, disc_thmss = disc_thmss,
           discIs = discI_thms, sel_thmss = sel_thmss, disc_excludesss = disc_exclude_thmsss,
           disc_exhausts = disc_exhaust_thms, sel_exhausts = sel_exhaust_thms,
           collapses = all_collapse_thms, expands = expand_thms, sel_splits = sel_split_thms,
           sel_split_asms = sel_split_asm_thms, case_eq_ifs = case_eq_if_thms};
      in
        (ctr_sugar,
         lthy
         |> not rep_compat ?
            Local_Theory.declaration {syntax = false, pervasive = true}
              (fn phi => Case_Translation.register
                 (Morphism.term phi casex) (map (Morphism.term phi) ctrs))
         |> Local_Theory.background_theory (fold (fold Code.del_eqn) [disc_defs, sel_defs])
         |> not no_code ?
            Local_Theory.declaration {syntax = false, pervasive = false}
              (fn phi => Context.mapping
                (add_ctr_code fcT_name (map (Morphism.typ phi) As)
                  (map (dest_Const o Morphism.term phi) ctrs) (Morphism.fact phi inject_thms)
                  (Morphism.fact phi distinct_thms) (Morphism.fact phi case_thms))
                I)
         |> Local_Theory.notes (anonymous_notes @ notes) |> snd
         |> register_ctr_sugar fcT_name ctr_sugar)
      end;
  in
    (goalss, after_qed, lthy')
  end;

fun wrap_free_constructors tacss = (fn (goalss, after_qed, lthy) =>
  map2 (map2 (Thm.close_derivation oo Goal.prove_sorry lthy [] [])) goalss tacss
  |> (fn thms => after_qed thms lthy)) oo prepare_wrap_free_constructors (K I);

val wrap_free_constructors_cmd = (fn (goalss, after_qed, lthy) =>
  Proof.theorem NONE (snd oo after_qed) (map (map (rpair [])) goalss) lthy) oo
  prepare_wrap_free_constructors Syntax.read_term;

fun parse_bracket_list parser = @{keyword "["} |-- Parse.list parser --|  @{keyword "]"};

val parse_bindings = parse_bracket_list parse_binding;
val parse_bindingss = parse_bracket_list parse_bindings;

val parse_bound_term = (parse_binding --| @{keyword ":"}) -- Parse.term;
val parse_bound_terms = parse_bracket_list parse_bound_term;
val parse_bound_termss = parse_bracket_list parse_bound_terms;

val parse_wrap_free_constructors_options =
  Scan.optional (@{keyword "("} |-- Parse.list1
        (Parse.reserved "no_discs_sels" >> K 0 || Parse.reserved "no_code" >> K 1 ||
         Parse.reserved "rep_compat" >> K 2) --| @{keyword ")"}
      >> (fn js => (member (op =) js 0, (member (op =) js 1, member (op =) js 2))))
    (false, (false, false));

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "wrap_free_constructors"}
    "wrap an existing freely generated type's constructors"
    ((parse_wrap_free_constructors_options -- (@{keyword "["} |-- Parse.list Parse.term --|
        @{keyword "]"}) --
      parse_binding -- Scan.optional (parse_bindings -- Scan.optional (parse_bindingss --
        Scan.optional parse_bound_termss []) ([], [])) ([], ([], [])))
     >> wrap_free_constructors_cmd);

end;
