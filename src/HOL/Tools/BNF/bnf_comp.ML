(*  Title:      HOL/Tools/BNF/bnf_comp.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Composition of bounded natural functors.
*)

signature BNF_COMP =
sig
  val ID_bnf: BNF_Def.bnf
  val DEADID_bnf: BNF_Def.bnf

  type comp_cache
  type unfold_set

  val empty_comp_cache: comp_cache
  val empty_unfolds: unfold_set

  exception BAD_DEAD of typ * typ

  val bnf_of_typ: BNF_Def.inline_policy -> (binding -> binding) ->
    ((string * sort) list list -> (string * sort) list) -> (string * sort) list ->
    (string * sort) list -> typ -> (comp_cache * unfold_set) * local_theory ->
    (BNF_Def.bnf * (typ list * typ list)) * ((comp_cache * unfold_set) * local_theory)
  val default_comp_sort: (string * sort) list list -> (string * sort) list
  val normalize_bnfs: (int -> binding -> binding) -> ''a list list -> ''a list ->
    (''a list list -> ''a list) -> BNF_Def.bnf list -> (comp_cache * unfold_set) * local_theory ->
    (int list list * ''a list) * (BNF_Def.bnf list * ((comp_cache * unfold_set) * local_theory))

  type absT_info =
    {absT: typ,
     repT: typ,
     abs: term,
     rep: term,
     abs_inject: thm,
     abs_inverse: thm,
     type_definition: thm}

  val morph_absT_info: morphism -> absT_info -> absT_info
  val mk_absT: theory -> typ -> typ -> typ -> typ
  val mk_repT: typ -> typ -> typ -> typ
  val mk_abs: typ -> term -> term
  val mk_rep: typ -> term -> term
  val seal_bnf: (binding -> binding) -> unfold_set -> binding -> typ list -> BNF_Def.bnf ->
    local_theory -> (BNF_Def.bnf * (typ list * absT_info)) * local_theory
end;

structure BNF_Comp : BNF_COMP =
struct

open BNF_Def
open BNF_Util
open BNF_Tactics
open BNF_Comp_Tactics

val ID_bnf = the (bnf_of @{context} "BNF_Comp.ID");
val DEADID_bnf = the (bnf_of @{context} "BNF_Comp.DEADID");

type comp_cache = (bnf * (typ list * typ list)) Typtab.table;

fun key_of_types s Ts = Type (s, Ts);
fun key_of_typess s = key_of_types s o map (key_of_types "");
fun typ_of_int n = Type (string_of_int n, []);
fun typ_of_bnf bnf =
  key_of_typess "" [[T_of_bnf bnf], lives_of_bnf bnf, sort Term_Ord.typ_ord (deads_of_bnf bnf)];

fun key_of_kill n bnf = key_of_types "k" [typ_of_int n, typ_of_bnf bnf];
fun key_of_lift n bnf = key_of_types "l" [typ_of_int n, typ_of_bnf bnf];
fun key_of_permute src dest bnf =
  key_of_types "p" (map typ_of_int src @ map typ_of_int dest @ [typ_of_bnf bnf]);
fun key_of_compose oDs Dss Ass outer inners =
  key_of_types "c" (map (key_of_typess "") [[oDs], Dss, Ass, [map typ_of_bnf (outer :: inners)]]);

fun cache_comp_simple key cache (bnf, (unfold_set, lthy)) =
  (bnf, ((Typtab.update (key, (bnf, ([], []))) cache, unfold_set), lthy));

fun cache_comp key (bnf_Ds_As, ((cache, unfold_set), lthy)) =
  (bnf_Ds_As, ((Typtab.update (key, bnf_Ds_As) cache, unfold_set), lthy));

(* TODO: Replace by "BNF_Defs.defs list"? *)
type unfold_set = {
  map_unfolds: thm list,
  set_unfoldss: thm list list,
  rel_unfolds: thm list
};

val empty_comp_cache = Typtab.empty;
val empty_unfolds = {map_unfolds = [], set_unfoldss = [], rel_unfolds = []};

fun add_to_thms thms new = thms |> not (Thm.is_reflexive new) ? insert Thm.eq_thm new;
fun adds_to_thms thms news = insert (eq_set Thm.eq_thm) (no_reflexive news) thms;

fun add_to_unfolds map sets rel
  {map_unfolds, set_unfoldss, rel_unfolds} =
  {map_unfolds = add_to_thms map_unfolds map,
    set_unfoldss = adds_to_thms set_unfoldss sets,
    rel_unfolds = add_to_thms rel_unfolds rel};

fun add_bnf_to_unfolds bnf =
  add_to_unfolds (map_def_of_bnf bnf) (set_defs_of_bnf bnf) (rel_def_of_bnf bnf);

val bdTN = "bdT";

fun mk_killN n = "_kill" ^ string_of_int n;
fun mk_liftN n = "_lift" ^ string_of_int n;
fun mk_permuteN src dest =
  "_permute_" ^ implode (map string_of_int src) ^ "_" ^ implode (map string_of_int dest);


(*copied from Envir.expand_term_free*)
fun expand_term_const defs =
  let
    val eqs = map ((fn ((x, U), u) => (x, (U, u))) o apfst dest_Const) defs;
    val get = fn Const (x, _) => AList.lookup (op =) eqs x | _ => NONE;
  in Envir.expand_term get end;

val id_bnf_comp_def = @{thm id_bnf_comp_def};
val expand_id_bnf_comp_def =
  expand_term_const [Thm.prop_of id_bnf_comp_def |> Logic.dest_equals];

fun is_sum_prod_natLeq (Const (@{const_name csum}, _) $ t $ u) = forall is_sum_prod_natLeq [t, u]
  | is_sum_prod_natLeq (Const (@{const_name cprod}, _) $ t $ u) = forall is_sum_prod_natLeq [t, u]
  | is_sum_prod_natLeq t = t aconv @{term natLeq};

fun clean_compose_bnf const_policy qualify b outer inners (unfold_set, lthy) =
  let
    val olive = live_of_bnf outer;
    val onwits = nwits_of_bnf outer;
    val odead = dead_of_bnf outer;
    val inner = hd inners;
    val ilive = live_of_bnf inner;
    val ideads = map dead_of_bnf inners;
    val inwitss = map nwits_of_bnf inners;

    (* TODO: check olive = length inners > 0,
                   forall inner from inners. ilive = live,
                   forall inner from inners. idead = dead  *)

    val (oDs, lthy1) = apfst (map TFree)
      (Variable.invent_types (replicate odead @{sort type}) lthy);
    val (Dss, lthy2) = apfst (map (map TFree))
      (fold_map Variable.invent_types (map (fn n => replicate n @{sort type}) ideads) lthy1);
    val (Ass, lthy3) = apfst (replicate ilive o map TFree)
      (Variable.invent_types (replicate ilive @{sort type}) lthy2);
    val As = if ilive > 0 then hd Ass else [];
    val Ass_repl = replicate olive As;
    val (Bs, names_lthy) = apfst (map TFree)
      (Variable.invent_types (replicate ilive @{sort type}) lthy3);
    val Bss_repl = replicate olive Bs;

    val ((((fs', Qs'), Asets), xs), _) = names_lthy
      |> apfst snd o mk_Frees' "f" (map2 (curry op -->) As Bs)
      ||>> apfst snd o mk_Frees' "Q" (map2 mk_pred2T As Bs)
      ||>> mk_Frees "A" (map HOLogic.mk_setT As)
      ||>> mk_Frees "x" As;

    val CAs = map3 mk_T_of_bnf Dss Ass_repl inners;
    val CCA = mk_T_of_bnf oDs CAs outer;
    val CBs = map3 mk_T_of_bnf Dss Bss_repl inners;
    val outer_sets = mk_sets_of_bnf (replicate olive oDs) (replicate olive CAs) outer;
    val inner_setss = map3 mk_sets_of_bnf (map (replicate ilive) Dss) (replicate olive Ass) inners;
    val inner_bds = map3 mk_bd_of_bnf Dss Ass_repl inners;
    val outer_bd = mk_bd_of_bnf oDs CAs outer;

    (*%f1 ... fn. outer.map (inner_1.map f1 ... fn) ... (inner_m.map f1 ... fn)*)
    val mapx = fold_rev Term.abs fs'
      (Term.list_comb (mk_map_of_bnf oDs CAs CBs outer,
        map2 (fn Ds => (fn f => Term.list_comb (f, map Bound (ilive - 1 downto 0))) o
          mk_map_of_bnf Ds As Bs) Dss inners));
    (*%Q1 ... Qn. outer.rel (inner_1.rel Q1 ... Qn) ... (inner_m.rel Q1 ... Qn)*)
    val rel = fold_rev Term.abs Qs'
      (Term.list_comb (mk_rel_of_bnf oDs CAs CBs outer,
        map2 (fn Ds => (fn f => Term.list_comb (f, map Bound (ilive - 1 downto 0))) o
          mk_rel_of_bnf Ds As Bs) Dss inners));

    (*Union o collect {outer.set_1 ... outer.set_m} o outer.map inner_1.set_i ... inner_m.set_i*)
    (*Union o collect {image inner_1.set_i o outer.set_1 ... image inner_m.set_i o outer.set_m}*)
    fun mk_set i =
      let
        val (setTs, T) = `(replicate olive o HOLogic.mk_setT) (nth As i);
        val outer_set = mk_collect
          (mk_sets_of_bnf (replicate olive oDs) (replicate olive setTs) outer)
          (mk_T_of_bnf oDs setTs outer --> HOLogic.mk_setT T);
        val inner_sets = map (fn sets => nth sets i) inner_setss;
        val outer_map = mk_map_of_bnf oDs CAs setTs outer;
        val map_inner_sets = Term.list_comb (outer_map, inner_sets);
        val collect_image = mk_collect
          (map2 (fn f => fn set => HOLogic.mk_comp (mk_image f, set)) inner_sets outer_sets)
          (CCA --> HOLogic.mk_setT T);
      in
        (Library.foldl1 HOLogic.mk_comp [mk_Union T, outer_set, map_inner_sets],
        HOLogic.mk_comp (mk_Union T, collect_image))
      end;

    val (sets, sets_alt) = map_split mk_set (0 upto ilive - 1);

    fun mk_simplified_set set =
      let
        val setT = fastype_of set;
        val var_set' = Const (@{const_name id_bnf_comp}, setT --> setT) $ Var ((Name.uu, 0), setT);
        val goal = mk_Trueprop_eq (var_set', set);
        fun tac {context = ctxt, prems = _} =
          mk_simplified_set_tac ctxt (collect_set_map_of_bnf outer);
        val set'_eq_set =
          Goal.prove names_lthy [] [] goal tac
          |> Thm.close_derivation;
        val set' = fst (HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of set'_eq_set)));
      in
        (set', set'_eq_set)
      end;

    val (sets', set'_eq_sets) =
      map_split mk_simplified_set sets
      ||> Proof_Context.export names_lthy lthy;

    (*(inner_1.bd +c ... +c inner_m.bd) *c outer.bd*)
    val bd = mk_cprod (Library.foldr1 (uncurry mk_csum) inner_bds) outer_bd;

    val (bd', bd_ordIso_natLeq_thm_opt) =
      if is_sum_prod_natLeq bd then
        let
          val bd' = @{term natLeq};
          val bd_bd' = HOLogic.mk_prod (bd, bd');
          val ordIso = Const (@{const_name ordIso}, HOLogic.mk_setT (fastype_of bd_bd'));
          val goal = mk_Trueprop_mem (bd_bd', ordIso);
        in
          (bd', SOME (Goal.prove_sorry lthy [] [] goal (K bd_ordIso_natLeq_tac)
            |> Thm.close_derivation))
        end
      else
        (bd, NONE);

    fun map_id0_tac _ =
      mk_comp_map_id0_tac (map_id0_of_bnf outer) (map_cong0_of_bnf outer)
        (map map_id0_of_bnf inners);

    fun map_comp0_tac _ =
      mk_comp_map_comp0_tac (map_comp0_of_bnf outer) (map_cong0_of_bnf outer)
        (map map_comp0_of_bnf inners);

    fun mk_single_set_map0_tac i ctxt =
      mk_comp_set_map0_tac ctxt (nth set'_eq_sets i) (map_comp0_of_bnf outer)
        (map_cong0_of_bnf outer) (collect_set_map_of_bnf outer)
        (map ((fn thms => nth thms i) o set_map0_of_bnf) inners);

    val set_map0_tacs = map mk_single_set_map0_tac (0 upto ilive - 1);

    fun bd_card_order_tac _ =
      mk_comp_bd_card_order_tac (map bd_card_order_of_bnf inners) (bd_card_order_of_bnf outer);

    fun bd_cinfinite_tac _ =
      mk_comp_bd_cinfinite_tac (bd_cinfinite_of_bnf inner) (bd_cinfinite_of_bnf outer);

    val set_alt_thms =
      if Config.get lthy quick_and_dirty then
        []
      else
        map (fn goal =>
          Goal.prove_sorry lthy [] [] goal
            (fn {context = ctxt, prems = _} =>
              mk_comp_set_alt_tac ctxt (collect_set_map_of_bnf outer))
          |> Thm.close_derivation)
        (map2 (curry (HOLogic.mk_Trueprop o HOLogic.mk_eq)) sets sets_alt);

    fun map_cong0_tac ctxt =
      mk_comp_map_cong0_tac ctxt set'_eq_sets set_alt_thms (map_cong0_of_bnf outer)
        (map map_cong0_of_bnf inners);

    val set_bd_tacs =
      if Config.get lthy quick_and_dirty then
        replicate ilive (K all_tac)
      else
        let
          val outer_set_bds = set_bd_of_bnf outer;
          val inner_set_bdss = map set_bd_of_bnf inners;
          val inner_bd_Card_orders = map bd_Card_order_of_bnf inners;
          fun single_set_bd_thm i j =
            @{thm comp_single_set_bd} OF [nth inner_bd_Card_orders j, nth (nth inner_set_bdss j) i,
              nth outer_set_bds j]
          val single_set_bd_thmss =
            map ((fn f => map f (0 upto olive - 1)) o single_set_bd_thm) (0 upto ilive - 1);
        in
          map3 (fn set'_eq_set => fn set_alt => fn single_set_bds => fn ctxt =>
            mk_comp_set_bd_tac ctxt set'_eq_set bd_ordIso_natLeq_thm_opt set_alt single_set_bds)
          set'_eq_sets set_alt_thms single_set_bd_thmss
        end;

    val in_alt_thm =
      let
        val inx = mk_in Asets sets CCA;
        val in_alt = mk_in (map2 (mk_in Asets) inner_setss CAs) outer_sets CCA;
        val goal = fold_rev Logic.all Asets (mk_Trueprop_eq (inx, in_alt));
      in
        Goal.prove_sorry lthy [] [] goal
          (fn {context = ctxt, prems = _} => mk_comp_in_alt_tac ctxt set_alt_thms)
        |> Thm.close_derivation
      end;

    fun le_rel_OO_tac _ = mk_le_rel_OO_tac (le_rel_OO_of_bnf outer) (rel_mono_of_bnf outer)
      (map le_rel_OO_of_bnf inners);

    fun rel_OO_Grp_tac ctxt =
      let
        val outer_rel_Grp = rel_Grp_of_bnf outer RS sym;
        val outer_rel_cong = rel_cong_of_bnf outer;
        val thm =
          (trans OF [in_alt_thm RS @{thm OO_Grp_cong},
             trans OF [@{thm arg_cong2[of _ _ _ _ relcompp]} OF
               [trans OF [outer_rel_Grp RS @{thm arg_cong[of _ _ conversep]},
                 rel_conversep_of_bnf outer RS sym], outer_rel_Grp],
               trans OF [rel_OO_of_bnf outer RS sym, outer_rel_cong OF
                 (map (fn bnf => rel_OO_Grp_of_bnf bnf RS sym) inners)]]] RS sym);
      in
        unfold_thms_tac ctxt set'_eq_sets THEN rtac thm 1
      end;

    val tacs = zip_axioms map_id0_tac map_comp0_tac map_cong0_tac set_map0_tacs bd_card_order_tac
      bd_cinfinite_tac set_bd_tacs le_rel_OO_tac rel_OO_Grp_tac;

    val outer_wits = mk_wits_of_bnf (replicate onwits oDs) (replicate onwits CAs) outer;

    val inner_witss = map (map (fn (I, wit) => Term.list_comb (wit, map (nth xs) I)))
      (map3 (fn Ds => fn n => mk_wits_of_bnf (replicate n Ds) (replicate n As))
        Dss inwitss inners);

    val inner_witsss = map (map (nth inner_witss) o fst) outer_wits;

    val wits = (inner_witsss, (map (single o snd) outer_wits))
      |-> map2 (fold (map_product (fn iwit => fn owit => owit $ iwit)))
      |> flat
      |> map (`(fn t => Term.add_frees t []))
      |> minimize_wits
      |> map (fn (frees, t) => fold absfree frees t);

    fun wit_tac ctxt =
      mk_comp_wit_tac ctxt set'_eq_sets (wit_thms_of_bnf outer) (collect_set_map_of_bnf outer)
        (maps wit_thms_of_bnf inners);

    val (bnf', lthy') =
      bnf_def const_policy (K Dont_Note) true qualify tacs wit_tac (SOME (oDs @ flat Dss))
        Binding.empty Binding.empty [] ((((((b, CCA), mapx), sets'), bd'), wits), SOME rel) lthy;

    val phi =
      Morphism.thm_morphism "BNF" (unfold_thms lthy' [id_bnf_comp_def])
      $> Morphism.term_morphism "BNF" expand_id_bnf_comp_def;

    val bnf'' = morph_bnf phi bnf';
  in
    (bnf'', (add_bnf_to_unfolds bnf'' unfold_set, lthy'))
  end;

(* Killing live variables *)

fun raw_kill_bnf qualify n bnf (accum as (unfold_set, lthy)) =
  if n = 0 then (bnf, accum) else
  let
    val b = Binding.suffix_name (mk_killN n) (name_of_bnf bnf);
    val live = live_of_bnf bnf;
    val dead = dead_of_bnf bnf;
    val nwits = nwits_of_bnf bnf;

    (* TODO: check 0 < n <= live *)

    val (Ds, lthy1) = apfst (map TFree)
      (Variable.invent_types (replicate dead @{sort type}) lthy);
    val ((killedAs, As), lthy2) = apfst (`(take n) o map TFree)
      (Variable.invent_types (replicate live @{sort type}) lthy1);
    val (Bs, _(*lthy3*)) = apfst (append killedAs o map TFree)
      (Variable.invent_types (replicate (live - n) @{sort type}) lthy2);

    val ((Asets, lives), _(*names_lthy*)) = lthy
      |> mk_Frees "A" (map HOLogic.mk_setT (drop n As))
      ||>> mk_Frees "x" (drop n As);
    val xs = map (fn T => HOLogic.choice_const T $ absdummy T @{term True}) killedAs @ lives;

    val T = mk_T_of_bnf Ds As bnf;

    (*bnf.map id ... id*)
    val mapx = Term.list_comb (mk_map_of_bnf Ds As Bs bnf, map HOLogic.id_const killedAs);
    (*bnf.rel (op =) ... (op =)*)
    val rel = Term.list_comb (mk_rel_of_bnf Ds As Bs bnf, map HOLogic.eq_const killedAs);

    val bnf_sets = mk_sets_of_bnf (replicate live Ds) (replicate live As) bnf;
    val sets = drop n bnf_sets;

    val bd = mk_bd_of_bnf Ds As bnf;

    fun map_id0_tac _ = rtac (map_id0_of_bnf bnf) 1;
    fun map_comp0_tac ctxt =
      unfold_thms_tac ctxt ((map_comp0_of_bnf bnf RS sym) ::
        @{thms comp_assoc id_comp comp_id}) THEN rtac refl 1;
    fun map_cong0_tac ctxt =
      mk_kill_map_cong0_tac ctxt n (live - n) (map_cong0_of_bnf bnf);
    val set_map0_tacs = map (fn thm => fn _ => rtac thm 1) (drop n (set_map0_of_bnf bnf));
    fun bd_card_order_tac _ = rtac (bd_card_order_of_bnf bnf) 1;
    fun bd_cinfinite_tac _ = rtac (bd_cinfinite_of_bnf bnf) 1;
    val set_bd_tacs = map (fn thm => fn _ => rtac thm 1) (drop n (set_bd_of_bnf bnf));

    val in_alt_thm =
      let
        val inx = mk_in Asets sets T;
        val in_alt = mk_in (map HOLogic.mk_UNIV killedAs @ Asets) bnf_sets T;
        val goal = fold_rev Logic.all Asets (mk_Trueprop_eq (inx, in_alt));
      in
        Goal.prove_sorry lthy [] [] goal (K kill_in_alt_tac) |> Thm.close_derivation
      end;

    fun le_rel_OO_tac ctxt =
      EVERY' [rtac @{thm ord_le_eq_trans}, rtac (le_rel_OO_of_bnf bnf)] 1 THEN
      unfold_thms_tac ctxt @{thms eq_OO} THEN rtac refl 1;

    fun rel_OO_Grp_tac _ =
      let
        val rel_Grp = rel_Grp_of_bnf bnf RS sym
        val thm =
          (trans OF [in_alt_thm RS @{thm OO_Grp_cong},
            trans OF [@{thm arg_cong2[of _ _ _ _ relcompp]} OF
              [trans OF [rel_Grp RS @{thm arg_cong[of _ _ conversep]},
                rel_conversep_of_bnf bnf RS sym], rel_Grp],
              trans OF [rel_OO_of_bnf bnf RS sym, rel_cong_of_bnf bnf OF
                (replicate n @{thm trans[OF Grp_UNIV_id[OF refl] eq_alt[symmetric]]} @
                 replicate (live - n) @{thm Grp_fst_snd})]]] RS sym);
      in
        rtac thm 1
      end;

    val tacs = zip_axioms map_id0_tac map_comp0_tac map_cong0_tac set_map0_tacs bd_card_order_tac
      bd_cinfinite_tac set_bd_tacs le_rel_OO_tac rel_OO_Grp_tac;

    val bnf_wits = mk_wits_of_bnf (replicate nwits Ds) (replicate nwits As) bnf;

    val wits = map (fn t => fold absfree (Term.add_frees t []) t)
      (map (fn (I, wit) => Term.list_comb (wit, map (nth xs) I)) bnf_wits);

    fun wit_tac _ = mk_simple_wit_tac (wit_thms_of_bnf bnf);

    val (bnf', lthy') =
      bnf_def Smart_Inline (K Dont_Note) true qualify tacs wit_tac (SOME (killedAs @ Ds))
        Binding.empty Binding.empty [] ((((((b, T), mapx), sets), bd), wits), SOME rel) lthy;
  in
    (bnf', (add_bnf_to_unfolds bnf' unfold_set, lthy'))
  end;

fun kill_bnf qualify n bnf (accum as ((cache, unfold_set), lthy)) =
  let val key = key_of_kill n bnf in
    (case Typtab.lookup cache key of
      SOME (bnf, _) => (bnf, accum)
    | NONE => cache_comp_simple key cache (raw_kill_bnf qualify n bnf (unfold_set, lthy)))
  end;

(* Adding dummy live variables *)

fun raw_lift_bnf qualify n bnf (accum as (unfold_set, lthy)) =
  if n = 0 then (bnf, accum) else
  let
    val b = Binding.suffix_name (mk_liftN n) (name_of_bnf bnf);
    val live = live_of_bnf bnf;
    val dead = dead_of_bnf bnf;
    val nwits = nwits_of_bnf bnf;

    (* TODO: check 0 < n *)

    val (Ds, lthy1) = apfst (map TFree)
      (Variable.invent_types (replicate dead @{sort type}) lthy);
    val ((newAs, As), lthy2) = apfst (chop n o map TFree)
      (Variable.invent_types (replicate (n + live) @{sort type}) lthy1);
    val ((newBs, Bs), _(*lthy3*)) = apfst (chop n o map TFree)
      (Variable.invent_types (replicate (n + live) @{sort type}) lthy2);

    val (Asets, _(*names_lthy*)) = lthy
      |> mk_Frees "A" (map HOLogic.mk_setT (newAs @ As));

    val T = mk_T_of_bnf Ds As bnf;

    (*%f1 ... fn. bnf.map*)
    val mapx =
      fold_rev Term.absdummy (map2 (curry op -->) newAs newBs) (mk_map_of_bnf Ds As Bs bnf);
    (*%Q1 ... Qn. bnf.rel*)
    val rel = fold_rev Term.absdummy (map2 mk_pred2T newAs newBs) (mk_rel_of_bnf Ds As Bs bnf);

    val bnf_sets = mk_sets_of_bnf (replicate live Ds) (replicate live As) bnf;
    val sets = map (fn A => absdummy T (HOLogic.mk_set A [])) newAs @ bnf_sets;

    val bd = mk_bd_of_bnf Ds As bnf;

    fun map_id0_tac _ = rtac (map_id0_of_bnf bnf) 1;
    fun map_comp0_tac ctxt =
      unfold_thms_tac ctxt ((map_comp0_of_bnf bnf RS sym) ::
        @{thms comp_assoc id_comp comp_id}) THEN rtac refl 1;
    fun map_cong0_tac ctxt =
      rtac (map_cong0_of_bnf bnf) 1 THEN REPEAT_DETERM_N live (Goal.assume_rule_tac ctxt 1);
    val set_map0_tacs =
      if Config.get lthy quick_and_dirty then
        replicate (n + live) (K all_tac)
      else
        replicate n (K empty_natural_tac) @
        map (fn thm => fn _ => rtac thm 1) (set_map0_of_bnf bnf);
    fun bd_card_order_tac _ = rtac (bd_card_order_of_bnf bnf) 1;
    fun bd_cinfinite_tac _ = rtac (bd_cinfinite_of_bnf bnf) 1;
    val set_bd_tacs =
      if Config.get lthy quick_and_dirty then
        replicate (n + live) (K all_tac)
      else
        replicate n (K (mk_lift_set_bd_tac (bd_Card_order_of_bnf bnf))) @
        (map (fn thm => fn _ => rtac thm 1) (set_bd_of_bnf bnf));

    val in_alt_thm =
      let
        val inx = mk_in Asets sets T;
        val in_alt = mk_in (drop n Asets) bnf_sets T;
        val goal = fold_rev Logic.all Asets (mk_Trueprop_eq (inx, in_alt));
      in
        Goal.prove_sorry lthy [] [] goal (K lift_in_alt_tac) |> Thm.close_derivation
      end;

    fun le_rel_OO_tac _ = rtac (le_rel_OO_of_bnf bnf) 1;

    fun rel_OO_Grp_tac _ = mk_simple_rel_OO_Grp_tac (rel_OO_Grp_of_bnf bnf) in_alt_thm;

    val tacs = zip_axioms map_id0_tac map_comp0_tac map_cong0_tac set_map0_tacs bd_card_order_tac
      bd_cinfinite_tac set_bd_tacs le_rel_OO_tac rel_OO_Grp_tac;

    val wits = map snd (mk_wits_of_bnf (replicate nwits Ds) (replicate nwits As) bnf);

    fun wit_tac _ = mk_simple_wit_tac (wit_thms_of_bnf bnf);

    val (bnf', lthy') =
      bnf_def Smart_Inline (K Dont_Note) true qualify tacs wit_tac (SOME Ds) Binding.empty
        Binding.empty [] ((((((b, T), mapx), sets), bd), wits), SOME rel) lthy;
  in
    (bnf', (add_bnf_to_unfolds bnf' unfold_set, lthy'))
  end;

fun lift_bnf qualify n bnf (accum as ((cache, unfold_set), lthy)) =
  let val key = key_of_lift n bnf in
    (case Typtab.lookup cache key of
      SOME (bnf, _) => (bnf, accum)
    | NONE => cache_comp_simple key cache (raw_lift_bnf qualify n bnf (unfold_set, lthy)))
  end;

(* Changing the order of live variables *)

fun raw_permute_bnf qualify src dest bnf (accum as (unfold_set, lthy)) =
  if src = dest then (bnf, accum) else
  let
    val b = Binding.suffix_name (mk_permuteN src dest) (name_of_bnf bnf);
    val live = live_of_bnf bnf;
    val dead = dead_of_bnf bnf;
    val nwits = nwits_of_bnf bnf;

    fun permute xs = permute_like_unique (op =) src dest xs;
    fun unpermute xs = permute_like_unique (op =) dest src xs;

    val (Ds, lthy1) = apfst (map TFree)
      (Variable.invent_types (replicate dead @{sort type}) lthy);
    val (As, lthy2) = apfst (map TFree)
      (Variable.invent_types (replicate live @{sort type}) lthy1);
    val (Bs, _(*lthy3*)) = apfst (map TFree)
      (Variable.invent_types (replicate live @{sort type}) lthy2);

    val (Asets, _(*names_lthy*)) = lthy
      |> mk_Frees "A" (map HOLogic.mk_setT (permute As));

    val T = mk_T_of_bnf Ds As bnf;

    (*%f(1) ... f(n). bnf.map f\<sigma>(1) ... f\<sigma>(n)*)
    val mapx = fold_rev Term.absdummy (permute (map2 (curry op -->) As Bs))
      (Term.list_comb (mk_map_of_bnf Ds As Bs bnf, unpermute (map Bound (live - 1 downto 0))));
    (*%Q(1) ... Q(n). bnf.rel Q\<sigma>(1) ... Q\<sigma>(n)*)
    val rel = fold_rev Term.absdummy (permute (map2 mk_pred2T As Bs))
      (Term.list_comb (mk_rel_of_bnf Ds As Bs bnf, unpermute (map Bound (live - 1 downto 0))));

    val bnf_sets = mk_sets_of_bnf (replicate live Ds) (replicate live As) bnf;
    val sets = permute bnf_sets;

    val bd = mk_bd_of_bnf Ds As bnf;

    fun map_id0_tac _ = rtac (map_id0_of_bnf bnf) 1;
    fun map_comp0_tac _ = rtac (map_comp0_of_bnf bnf) 1;
    fun map_cong0_tac ctxt =
      rtac (map_cong0_of_bnf bnf) 1 THEN REPEAT_DETERM_N live (Goal.assume_rule_tac ctxt 1);
    val set_map0_tacs = permute (map (fn thm => fn _ => rtac thm 1) (set_map0_of_bnf bnf));
    fun bd_card_order_tac _ = rtac (bd_card_order_of_bnf bnf) 1;
    fun bd_cinfinite_tac _ = rtac (bd_cinfinite_of_bnf bnf) 1;
    val set_bd_tacs = permute (map (fn thm => fn _ => rtac thm 1) (set_bd_of_bnf bnf));

    val in_alt_thm =
      let
        val inx = mk_in Asets sets T;
        val in_alt = mk_in (unpermute Asets) bnf_sets T;
        val goal = fold_rev Logic.all Asets (mk_Trueprop_eq (inx, in_alt));
      in
        Goal.prove_sorry lthy [] [] goal (K (mk_permute_in_alt_tac src dest))
        |> Thm.close_derivation
      end;

    fun le_rel_OO_tac _ = rtac (le_rel_OO_of_bnf bnf) 1;

    fun rel_OO_Grp_tac _ = mk_simple_rel_OO_Grp_tac (rel_OO_Grp_of_bnf bnf) in_alt_thm;

    val tacs = zip_axioms map_id0_tac map_comp0_tac map_cong0_tac set_map0_tacs bd_card_order_tac
      bd_cinfinite_tac set_bd_tacs le_rel_OO_tac rel_OO_Grp_tac;

    val wits = map snd (mk_wits_of_bnf (replicate nwits Ds) (replicate nwits As) bnf);

    fun wit_tac _ = mk_simple_wit_tac (wit_thms_of_bnf bnf);

    val (bnf', lthy') =
      bnf_def Smart_Inline (K Dont_Note) true qualify tacs wit_tac (SOME Ds) Binding.empty
        Binding.empty [] ((((((b, T), mapx), sets), bd), wits), SOME rel) lthy;
  in
    (bnf', (add_bnf_to_unfolds bnf' unfold_set, lthy'))
  end;

fun permute_bnf qualify src dest bnf (accum as ((cache, unfold_set), lthy)) =
  let val key = key_of_permute src dest bnf in
    (case Typtab.lookup cache key of
      SOME (bnf, _) => (bnf, accum)
    | NONE => cache_comp_simple key cache (raw_permute_bnf qualify src dest bnf (unfold_set, lthy)))
  end;

(* Composition pipeline *)

fun permute_and_kill qualify n src dest bnf =
  permute_bnf qualify src dest bnf
  #> uncurry (kill_bnf qualify n);

fun lift_and_permute qualify n src dest bnf =
  lift_bnf qualify n bnf
  #> uncurry (permute_bnf qualify src dest);

fun normalize_bnfs qualify Ass Ds sort bnfs accum =
  let
    val before_kill_src = map (fn As => 0 upto (length As - 1)) Ass;
    val kill_poss = map (find_indices op = Ds) Ass;
    val live_poss = map2 (subtract op =) kill_poss before_kill_src;
    val before_kill_dest = map2 append kill_poss live_poss;
    val kill_ns = map length kill_poss;
    val (inners', accum') =
      fold_map5 (fn i => permute_and_kill (qualify i))
        (if length bnfs = 1 then [0] else (1 upto length bnfs))
        kill_ns before_kill_src before_kill_dest bnfs accum;

    val Ass' = map2 (map o nth) Ass live_poss;
    val As = sort Ass';
    val after_lift_dest = replicate (length Ass') (0 upto (length As - 1));
    val old_poss = map (map (fn x => find_index (fn y => x = y) As)) Ass';
    val new_poss = map2 (subtract op =) old_poss after_lift_dest;
    val after_lift_src = map2 append new_poss old_poss;
    val lift_ns = map (fn xs => length As - length xs) Ass';
  in
    ((kill_poss, As), fold_map5 (fn i => lift_and_permute (qualify i))
      (if length bnfs = 1 then [0] else 1 upto length bnfs)
      lift_ns after_lift_src after_lift_dest inners' accum')
  end;

fun default_comp_sort Ass =
  Library.sort (Term_Ord.typ_ord o pairself TFree) (fold (fold (insert (op =))) Ass []);

fun raw_compose_bnf const_policy qualify sort outer inners oDs Dss tfreess accum =
  let
    val b = name_of_bnf outer;

    val Ass = map (map Term.dest_TFree) tfreess;
    val Ds = fold (fold Term.add_tfreesT) (oDs :: Dss) [];

    val ((kill_poss, As), (inners', ((cache', unfold_set'), lthy'))) =
      normalize_bnfs qualify Ass Ds sort inners accum;

    val Ds = oDs @ flat (map3 (append oo map o nth) tfreess kill_poss Dss);
    val As = map TFree As;
  in
    apfst (rpair (Ds, As))
      (apsnd (apfst (pair cache'))
        (clean_compose_bnf const_policy (qualify 0) b outer inners' (unfold_set', lthy')))
  end;

fun compose_bnf const_policy qualify sort outer inners oDs Dss tfreess (accum as ((cache, _), _)) =
  let val key = key_of_compose oDs Dss tfreess outer inners in
    (case Typtab.lookup cache key of
      SOME bnf_Ds_As => (bnf_Ds_As, accum)
    | NONE =>
      cache_comp key (raw_compose_bnf const_policy qualify sort outer inners oDs Dss tfreess accum))
  end;

(* Hide the type of the bound (optimization) and unfold the definitions (nicer to the user) *)

type absT_info =
  {absT: typ,
   repT: typ,
   abs: term,
   rep: term,
   abs_inject: thm,
   abs_inverse: thm,
   type_definition: thm};

fun morph_absT_info phi
  {absT, repT, abs, rep, abs_inject, abs_inverse, type_definition} =
  {absT = Morphism.typ phi absT,
   repT = Morphism.typ phi repT,
   abs = Morphism.term phi abs,
   rep = Morphism.term phi rep,
   abs_inject = Morphism.thm phi abs_inject,
   abs_inverse = Morphism.thm phi abs_inverse,
   type_definition = Morphism.thm phi type_definition};

fun mk_absT thy repT absT repU =
  let
    val rho = Vartab.fold (cons o apsnd snd) (Sign.typ_match thy (repT, repU) Vartab.empty) [];
  in Term.typ_subst_TVars rho absT end
  handle Type.TYPE_MATCH => raise Term.TYPE ("mk_absT", [repT, absT, repU], []);

fun mk_repT absT repT absU =
  if absT = repT then absU
  else
    (case (absT, absU) of
      (Type (C, Ts), Type (C', Us)) =>
        if C = C' then Term.typ_subst_atomic (Ts ~~ Us) repT
        else raise Term.TYPE ("mk_repT", [absT, repT, absT], [])
    | _ => raise Term.TYPE ("mk_repT", [absT, repT, absT], []));

fun mk_abs_or_rep _ absU (Const (@{const_name id_bnf_comp}, _)) =
    Const (@{const_name id_bnf_comp}, absU --> absU)
  | mk_abs_or_rep getT (Type (_, Us)) abs =
    let val Ts = snd (dest_Type (getT (fastype_of abs)))
    in Term.subst_atomic_types (Ts ~~ Us) abs end;

val mk_abs = mk_abs_or_rep range_type;
val mk_rep = mk_abs_or_rep domain_type;

val smart_max_inline_type_size = 5; (*FUDGE*)

fun maybe_typedef (b, As, mx) set opt_morphs tac =
  let
    val repT = HOLogic.dest_setT (fastype_of set);
    val inline = Term.size_of_typ repT <= smart_max_inline_type_size;
  in
    if inline then
      pair (repT,
        (@{const_name id_bnf_comp}, @{const_name id_bnf_comp},
         @{thm type_definition_id_bnf_comp_UNIV},
         @{thm type_definition.Abs_inverse[OF type_definition_id_bnf_comp_UNIV]},
         @{thm type_definition.Abs_inject[OF type_definition_id_bnf_comp_UNIV]},
         @{thm type_definition.Abs_cases[OF type_definition_id_bnf_comp_UNIV]}))
    else
      typedef (b, As, mx) set opt_morphs tac
      #>> (fn (T_name, ({Rep_name, Abs_name, ...},
          {type_definition, Abs_inverse, Abs_inject, Abs_cases, ...}) : Typedef.info) =>
        (Type (T_name, map TFree As),
          (Rep_name, Abs_name, type_definition, Abs_inverse, Abs_inject, Abs_cases)))
  end;

fun seal_bnf qualify (unfold_set : unfold_set) b Ds bnf lthy =
  let
    val live = live_of_bnf bnf;
    val nwits = nwits_of_bnf bnf;

    val (As, lthy1) = apfst (map TFree)
      (Variable.invent_types (replicate live @{sort type}) (fold Variable.declare_typ Ds lthy));
    val (Bs, _) = apfst (map TFree)
      (Variable.invent_types (replicate live @{sort type}) lthy1);

    val (((fs, fs'), (Rs, Rs')), _(*names_lthy*)) = lthy
      |> mk_Frees' "f" (map2 (curry op -->) As Bs)
      ||>> mk_Frees' "R" (map2 mk_pred2T As Bs);

    val repTA = mk_T_of_bnf Ds As bnf;
    val T_bind = qualify b;
    val TA_params = Term.add_tfreesT repTA [];
    val ((TA, (Rep_name, Abs_name, type_definition, Abs_inverse, Abs_inject, _)), lthy) =
      maybe_typedef (T_bind, TA_params, NoSyn)
        (HOLogic.mk_UNIV repTA) NONE (EVERY' [rtac exI, rtac UNIV_I] 1) lthy;

    val repTB = mk_T_of_bnf Ds Bs bnf;
    val TB = Term.typ_subst_atomic (As ~~ Bs) TA;
    val RepA = Const (Rep_name, TA --> repTA);
    val RepB = Const (Rep_name, TB --> repTB);
    val AbsA = Const (Abs_name, repTA --> TA);
    val AbsB = Const (Abs_name, repTB --> TB);
    val Abs_inject' = Abs_inject OF @{thms UNIV_I UNIV_I};
    val Abs_inverse' = Abs_inverse OF @{thms UNIV_I};

    val absT_info = {absT = TA, repT = repTA, abs = AbsA, rep = RepA, abs_inject = Abs_inject',
      abs_inverse = Abs_inverse', type_definition = type_definition};

    val bnf_map = fold_rev Term.absfree fs' (HOLogic.mk_comp (HOLogic.mk_comp (AbsB,
      Term.list_comb (mk_map_of_bnf Ds As Bs bnf, fs)), RepA));
    val bnf_sets = map ((fn t => HOLogic.mk_comp (t, RepA)))
      (mk_sets_of_bnf (replicate live Ds) (replicate live As) bnf);
    val bnf_bd = mk_bd_of_bnf Ds As bnf;
    val bnf_rel = fold_rev Term.absfree Rs' (mk_vimage2p RepA RepB $
      (Term.list_comb (mk_rel_of_bnf Ds As Bs bnf, Rs)));

    (*bd may depend only on dead type variables*)
    val bd_repT = fst (dest_relT (fastype_of bnf_bd));
    val bdT_bind = qualify (Binding.suffix_name ("_" ^ bdTN) b);
    val params = Term.add_tfreesT bd_repT [];
    val all_deads = map TFree (fold Term.add_tfreesT Ds []);

    val ((bdT, (_, Abs_bd_name, _, _, Abs_bdT_inject, Abs_bdT_cases)), lthy) =
      maybe_typedef (bdT_bind, params, NoSyn)
        (HOLogic.mk_UNIV bd_repT) NONE (EVERY' [rtac exI, rtac UNIV_I] 1) lthy;

    val (bnf_bd', bd_ordIso, bd_card_order, bd_cinfinite) =
      if bdT = bd_repT then (bnf_bd, bd_Card_order_of_bnf bnf RS @{thm ordIso_refl},
        bd_card_order_of_bnf bnf, bd_cinfinite_of_bnf bnf)
      else
        let
          val bnf_bd' = mk_dir_image bnf_bd (Const (Abs_bd_name, bd_repT --> bdT));

          val Abs_bdT_inj = mk_Abs_inj_thm Abs_bdT_inject;
          val Abs_bdT_bij = mk_Abs_bij_thm lthy Abs_bdT_inj Abs_bdT_cases;

          val bd_ordIso = @{thm dir_image} OF [Abs_bdT_inj, bd_Card_order_of_bnf bnf];
          val bd_card_order =
            @{thm card_order_dir_image} OF [Abs_bdT_bij, bd_card_order_of_bnf bnf];
          val bd_cinfinite =
            (@{thm Cinfinite_cong} OF [bd_ordIso, bd_Cinfinite_of_bnf bnf]) RS conjunct1;
        in
          (bnf_bd', bd_ordIso, bd_card_order, bd_cinfinite)
        end;

    fun map_id0_tac _ =
      rtac (@{thm type_copy_map_id0} OF [type_definition, map_id0_of_bnf bnf]) 1;
    fun map_comp0_tac _ =
      rtac (@{thm type_copy_map_comp0} OF [type_definition, map_comp0_of_bnf bnf]) 1;
    fun map_cong0_tac _ =
      EVERY' (rtac @{thm type_copy_map_cong0} :: rtac (map_cong0_of_bnf bnf) ::
        map (fn i => EVERY' [select_prem_tac live (dtac meta_spec) i, etac meta_mp,
          etac (o_apply RS equalityD2 RS set_mp)]) (1 upto live)) 1;
    fun set_map0_tac thm _ =
      rtac (@{thm type_copy_set_map0} OF [type_definition, thm]) 1;
    val set_bd_tacs = map (fn thm => fn _ => rtac (@{thm ordLeq_ordIso_trans} OF
        [thm, bd_ordIso] RS @{thm type_copy_set_bd}) 1) (set_bd_of_bnf bnf);
    fun le_rel_OO_tac _ =
      rtac (le_rel_OO_of_bnf bnf RS @{thm vimage2p_relcompp_mono}) 1;
    fun rel_OO_Grp_tac ctxt =
      (rtac (rel_OO_Grp_of_bnf bnf RS @{thm vimage2p_cong} RS trans) THEN'
      SELECT_GOAL (unfold_thms_tac ctxt [o_apply,
        type_definition RS @{thm type_copy_vimage2p_Grp_Rep},
        type_definition RS @{thm vimage2p_relcompp_converse}]) THEN' rtac refl) 1;

    val tacs = zip_axioms map_id0_tac map_comp0_tac map_cong0_tac
      (map set_map0_tac (set_map0_of_bnf bnf)) (K (rtac bd_card_order 1)) (K (rtac bd_cinfinite 1))
      set_bd_tacs le_rel_OO_tac rel_OO_Grp_tac;

    val bnf_wits = map (fn (I, t) =>
        fold Term.absdummy (map (nth As) I)
          (AbsA $ Term.list_comb (t, map Bound (0 upto length I - 1))))
      (mk_wits_of_bnf (replicate nwits Ds) (replicate nwits As) bnf);

    fun wit_tac _ = ALLGOALS (dtac (type_definition RS @{thm type_copy_wit})) THEN
      mk_simple_wit_tac (wit_thms_of_bnf bnf);

    val (bnf', lthy') =
      bnf_def Hardly_Inline (user_policy Dont_Note) true qualify tacs wit_tac (SOME all_deads)
        Binding.empty Binding.empty []
        ((((((b, TA), bnf_map), bnf_sets), bnf_bd'), bnf_wits), SOME bnf_rel) lthy;

    val unfolds = @{thm id_bnf_comp_apply} ::
      (#map_unfolds unfold_set @ flat (#set_unfoldss unfold_set) @ #rel_unfolds unfold_set);

    val bnf'' = bnf' |> morph_bnf_defs (Morphism.thm_morphism "BNF" (unfold_thms lthy' unfolds));

    val map_def = map_def_of_bnf bnf'';
    val set_defs = set_defs_of_bnf bnf'';
    val rel_def = rel_def_of_bnf bnf'';

    val bnf_b = qualify b;
    val def_qualify =
      Thm.def_binding o Binding.conceal o Binding.qualify false (Binding.name_of bnf_b);
    fun mk_prefix_binding pre = Binding.prefix_name (pre ^ "_") bnf_b;
    val map_b = def_qualify (mk_prefix_binding mapN);
    val rel_b = def_qualify (mk_prefix_binding relN);
    val set_bs = if live = 1 then [def_qualify (mk_prefix_binding setN)]
      else map (fn i => def_qualify (mk_prefix_binding (mk_setN i))) (1 upto live);

    val notes = (map_b, map_def) :: (rel_b, rel_def) :: (set_bs ~~ set_defs)
      |> map (fn (b, def) => ((b, []), [([def], [])]))
    val lthy'' = lthy' |> Local_Theory.notes notes |> snd
  in
    ((bnf'', (all_deads, absT_info)), lthy'')
  end;

exception BAD_DEAD of typ * typ;

fun bnf_of_typ _ _ _ _ Ds0 (T as TFree T') accum =
    (if member (op =) Ds0 T' then (DEADID_bnf, ([T], [])) else (ID_bnf, ([], [T])), accum)
  | bnf_of_typ _ _ _ _ _ (TVar _) _ = error "Unexpected schematic variable"
  | bnf_of_typ const_policy qualify' sort Xs Ds0 (T as Type (C, Ts)) (accum as (_, lthy)) =
    let
      fun check_bad_dead ((_, (deads, _)), _) =
        let val Ds = fold Term.add_tfreesT deads [] in
          (case Library.inter (op =) Ds Xs of [] => ()
          | X :: _ => raise BAD_DEAD (TFree X, T))
        end;

      val tfrees = subtract (op =) Ds0 (Term.add_tfreesT T []);
      val bnf_opt = if null tfrees then NONE else bnf_of lthy C;
    in
      (case bnf_opt of
        NONE => ((DEADID_bnf, ([T], [])), accum)
      | SOME bnf =>
        if forall (can Term.dest_TFree) Ts andalso length Ts = length tfrees then
          let
            val T' = T_of_bnf bnf;
            val deads = deads_of_bnf bnf;
            val lives = lives_of_bnf bnf;
            val tvars' = Term.add_tvarsT T' [];
            val Ds_As =
              pairself (map (Term.typ_subst_TVars (map fst tvars' ~~ map TFree tfrees)))
                (deads, lives);
          in ((bnf, Ds_As), accum) end
        else
          let
            val name = Long_Name.base_name C;
            fun qualify i =
              let val namei = name ^ nonzero_string_of_int i;
              in qualify' o Binding.qualify true namei end;
            val odead = dead_of_bnf bnf;
            val olive = live_of_bnf bnf;
            val oDs_pos = find_indices op = [TFree ("dead", [])] (snd (Term.dest_Type
              (mk_T_of_bnf (replicate odead (TFree ("dead", []))) (replicate olive dummyT) bnf)));
            val oDs = map (nth Ts) oDs_pos;
            val Ts' = map (nth Ts) (subtract (op =) oDs_pos (0 upto length Ts - 1));
            val ((inners, (Dss, Ass)), (accum', lthy')) =
              apfst (apsnd split_list o split_list)
                (fold_map2 (fn i => bnf_of_typ Smart_Inline (qualify i) sort Xs Ds0)
                (if length Ts' = 1 then [0] else (1 upto length Ts')) Ts' accum);
          in
            compose_bnf const_policy qualify sort bnf inners oDs Dss Ass (accum', lthy')
          end)
      |> tap check_bad_dead
    end;

end;
