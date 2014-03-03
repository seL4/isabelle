(*  Title:      HOL/Tools/BNF/bnf_comp.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Composition of bounded natural functors.
*)

val inline_ref = Unsynchronized.ref true;

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
    (string * sort) list -> typ -> (comp_cache * unfold_set) * Proof.context ->
    (BNF_Def.bnf * (typ list * typ list)) * ((comp_cache * unfold_set) * Proof.context)
  val default_comp_sort: (string * sort) list list -> (string * sort) list
  val normalize_bnfs: (int -> binding -> binding) -> ''a list list -> ''a list ->
    (''a list list -> ''a list) -> BNF_Def.bnf list -> unfold_set -> Proof.context ->
    (int list list * ''a list) * (BNF_Def.bnf list * (unfold_set * Proof.context))

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
    Proof.context -> (BNF_Def.bnf * (typ list * absT_info)) * local_theory
end;

structure BNF_Comp : BNF_COMP =
struct

open BNF_Def
open BNF_Util
open BNF_Tactics
open BNF_Comp_Tactics

val ID_bnf = the (bnf_of @{context} "Basic_BNFs.ID");
val DEADID_bnf = the (bnf_of @{context} "Basic_BNFs.DEADID");

type comp_cache = (bnf * (typ list * typ list)) Typtab.table;

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
      (Variable.invent_types (replicate odead HOLogic.typeS) lthy);
    val (Dss, lthy2) = apfst (map (map TFree))
        (fold_map Variable.invent_types (map (fn n => replicate n HOLogic.typeS) ideads) lthy1);
    val (Ass, lthy3) = apfst (replicate ilive o map TFree)
      (Variable.invent_types (replicate ilive HOLogic.typeS) lthy2);
    val As = if ilive > 0 then hd Ass else [];
    val Ass_repl = replicate olive As;
    val (Bs, _(*lthy4*)) = apfst (map TFree)
      (Variable.invent_types (replicate ilive HOLogic.typeS) lthy3);
    val Bss_repl = replicate olive Bs;

    val ((((fs', Qs'), Asets), xs), _(*names_lthy*)) = lthy
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

    (*(inner_1.bd +c ... +c inner_m.bd) *c outer.bd*)
    val bd = mk_cprod (Library.foldr1 (uncurry mk_csum) inner_bds) outer_bd;

    val (bd', bd_ordIso_natLeq_thm_opt) =
      if is_sum_prod_natLeq bd then
        let
          val bd' = @{term natLeq};
          val bd_bd' = HOLogic.mk_prod (bd, bd');
          val ordIso = Const (@{const_name ordIso}, HOLogic.mk_setT (fastype_of bd_bd'));
          val goal = HOLogic.mk_Trueprop (HOLogic.mk_mem (bd_bd', ordIso));
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

    fun mk_single_set_map0_tac i _ =
      mk_comp_set_map0_tac (map_comp0_of_bnf outer) (map_cong0_of_bnf outer)
        (collect_set_map_of_bnf outer)
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

    fun map_cong0_tac _ =
      mk_comp_map_cong0_tac set_alt_thms (map_cong0_of_bnf outer) (map map_cong0_of_bnf inners);

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
          map2 (fn set_alt => fn single_set_bds => fn ctxt =>
            mk_comp_set_bd_tac ctxt bd_ordIso_natLeq_thm_opt set_alt single_set_bds)
          set_alt_thms single_set_bd_thmss
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

    fun rel_OO_Grp_tac _ =
      let
        val outer_rel_Grp = rel_Grp_of_bnf outer RS sym;
        val outer_rel_cong = rel_cong_of_bnf outer;
        val thm =
          (trans OF [in_alt_thm RS @{thm OO_Grp_cong},
             trans OF [@{thm arg_cong2[of _ _ _ _ relcompp]} OF
               [trans OF [outer_rel_Grp RS @{thm arg_cong[of _ _ conversep]},
                 rel_conversep_of_bnf outer RS sym], outer_rel_Grp],
               trans OF [rel_OO_of_bnf outer RS sym, outer_rel_cong OF
                 (map (fn bnf => rel_OO_Grp_of_bnf bnf RS sym) inners)]]] RS sym)
          (*|> unfold_thms lthy (rel_def_of_bnf outer :: map rel_def_of_bnf inners)*);
      in
        rtac thm 1
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
      mk_comp_wit_tac ctxt (wit_thms_of_bnf outer) (collect_set_map_of_bnf outer)
        (maps wit_thms_of_bnf inners);

    val (bnf', lthy') =
      bnf_def const_policy (K Dont_Note) qualify tacs wit_tac (SOME (oDs @ flat Dss)) Binding.empty
        Binding.empty [] ((((((b, CCA), mapx), sets), bd'), wits), SOME rel) lthy;
  in
    (bnf', (add_bnf_to_unfolds bnf' unfold_set, lthy'))
  end;

(* Killing live variables *)

fun kill_bnf qualify n bnf (unfold_set, lthy) = if n = 0 then (bnf, (unfold_set, lthy)) else
  let
    val b = Binding.suffix_name (mk_killN n) (name_of_bnf bnf);
    val live = live_of_bnf bnf;
    val dead = dead_of_bnf bnf;
    val nwits = nwits_of_bnf bnf;

    (* TODO: check 0 < n <= live *)

    val (Ds, lthy1) = apfst (map TFree)
      (Variable.invent_types (replicate dead HOLogic.typeS) lthy);
    val ((killedAs, As), lthy2) = apfst (`(take n) o map TFree)
      (Variable.invent_types (replicate live HOLogic.typeS) lthy1);
    val (Bs, _(*lthy3*)) = apfst (append killedAs o map TFree)
      (Variable.invent_types (replicate (live - n) HOLogic.typeS) lthy2);

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
      bnf_def Smart_Inline (K Dont_Note) qualify tacs wit_tac (SOME (killedAs @ Ds)) Binding.empty
        Binding.empty [] ((((((b, T), mapx), sets), bd), wits), SOME rel) lthy;
  in
    (bnf', (add_bnf_to_unfolds bnf' unfold_set, lthy'))
  end;

(* Adding dummy live variables *)

fun lift_bnf qualify n bnf (unfold_set, lthy) = if n = 0 then (bnf, (unfold_set, lthy)) else
  let
    val b = Binding.suffix_name (mk_liftN n) (name_of_bnf bnf);
    val live = live_of_bnf bnf;
    val dead = dead_of_bnf bnf;
    val nwits = nwits_of_bnf bnf;

    (* TODO: check 0 < n *)

    val (Ds, lthy1) = apfst (map TFree)
      (Variable.invent_types (replicate dead HOLogic.typeS) lthy);
    val ((newAs, As), lthy2) = apfst (chop n o map TFree)
      (Variable.invent_types (replicate (n + live) HOLogic.typeS) lthy1);
    val ((newBs, Bs), _(*lthy3*)) = apfst (chop n o map TFree)
      (Variable.invent_types (replicate (n + live) HOLogic.typeS) lthy2);

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
      bnf_def Smart_Inline (K Dont_Note) qualify tacs wit_tac (SOME Ds) Binding.empty Binding.empty
        [] ((((((b, T), mapx), sets), bd), wits), SOME rel) lthy;
  in
    (bnf', (add_bnf_to_unfolds bnf' unfold_set, lthy'))
  end;

(* Changing the order of live variables *)

fun permute_bnf qualify src dest bnf (unfold_set, lthy) =
  if src = dest then (bnf, (unfold_set, lthy)) else
  let
    val b = Binding.suffix_name (mk_permuteN src dest) (name_of_bnf bnf);
    val live = live_of_bnf bnf;
    val dead = dead_of_bnf bnf;
    val nwits = nwits_of_bnf bnf;

    fun permute xs = permute_like_unique (op =) src dest xs;
    fun unpermute xs = permute_like_unique (op =) dest src xs;

    val (Ds, lthy1) = apfst (map TFree)
      (Variable.invent_types (replicate dead HOLogic.typeS) lthy);
    val (As, lthy2) = apfst (map TFree)
      (Variable.invent_types (replicate live HOLogic.typeS) lthy1);
    val (Bs, _(*lthy3*)) = apfst (map TFree)
      (Variable.invent_types (replicate live HOLogic.typeS) lthy2);

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
      bnf_def Smart_Inline (K Dont_Note) qualify tacs wit_tac (SOME Ds) Binding.empty Binding.empty
        [] ((((((b, T), mapx), sets), bd), wits), SOME rel) lthy;
  in
    (bnf', (add_bnf_to_unfolds bnf' unfold_set, lthy'))
  end;

(* Composition pipeline *)

fun permute_and_kill qualify n src dest bnf =
  permute_bnf qualify src dest bnf
  #> uncurry (kill_bnf qualify n);

fun lift_and_permute qualify n src dest bnf =
  lift_bnf qualify n bnf
  #> uncurry (permute_bnf qualify src dest);

fun normalize_bnfs qualify Ass Ds sort bnfs unfold_set lthy =
  let
    val before_kill_src = map (fn As => 0 upto (length As - 1)) Ass;
    val kill_poss = map (find_indices op = Ds) Ass;
    val live_poss = map2 (subtract op =) kill_poss before_kill_src;
    val before_kill_dest = map2 append kill_poss live_poss;
    val kill_ns = map length kill_poss;
    val (inners', (unfold_set', lthy')) =
      fold_map5 (fn i => permute_and_kill (qualify i))
        (if length bnfs = 1 then [0] else (1 upto length bnfs))
        kill_ns before_kill_src before_kill_dest bnfs (unfold_set, lthy);

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
      lift_ns after_lift_src after_lift_dest inners' (unfold_set', lthy'))
  end;

fun default_comp_sort Ass =
  Library.sort (Term_Ord.typ_ord o pairself TFree) (fold (fold (insert (op =))) Ass []);

fun compose_bnf const_policy qualify sort outer inners oDs Dss tfreess (unfold_set, lthy) =
  let
    val b = name_of_bnf outer;

    val Ass = map (map Term.dest_TFree) tfreess;
    val Ds = fold (fold Term.add_tfreesT) (oDs :: Dss) [];

    val ((kill_poss, As), (inners', (unfold_set', lthy'))) =
      normalize_bnfs qualify Ass Ds sort inners unfold_set lthy;

    val Ds = oDs @ flat (map3 (append oo map o nth) tfreess kill_poss Dss);
    val As = map TFree As;
  in
    apfst (rpair (Ds, As))
      (clean_compose_bnf const_policy (qualify 0) b outer inners' (unfold_set', lthy'))
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
  let val rho = Vartab.fold (cons o apsnd snd) (Sign.typ_match thy (repT, repU) Vartab.empty) [];
  in Term.typ_subst_TVars rho absT end;

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
         @{thm type_definition.Abs_inject[OF type_definition_id_bnf_comp_UNIV]}))
    else
      typedef (b, As, mx) set opt_morphs tac
      #>> (fn (T_name, ({Rep_name, Abs_name, ...},
          {type_definition, Abs_inverse, Abs_inject, ...}) : Typedef.info) =>
        (Type (T_name, map TFree As), (Rep_name, Abs_name, type_definition, Abs_inverse, Abs_inject)))
  end;

fun seal_bnf qualify (unfold_set : unfold_set) b Ds bnf lthy =
  let
    val live = live_of_bnf bnf;
    val nwits = nwits_of_bnf bnf;

    val (As, lthy1) = apfst (map TFree)
      (Variable.invent_types (replicate live HOLogic.typeS) (fold Variable.declare_typ Ds lthy));
    val (Bs, _) = apfst (map TFree)
      (Variable.invent_types (replicate live HOLogic.typeS) lthy1);

    val (((fs, fs'), (Rs, Rs')), _(*names_lthy*)) = lthy
      |> mk_Frees' "f" (map2 (curry op -->) As Bs)
      ||>> mk_Frees' "R" (map2 mk_pred2T As Bs)

    val map_unfolds = #map_unfolds unfold_set;
    val set_unfoldss = #set_unfoldss unfold_set;
    val rel_unfolds = #rel_unfolds unfold_set;

    val expand_maps =
      fold expand_term_const (map (single o Logic.dest_equals o Thm.prop_of) map_unfolds);
    val expand_sets =
      fold expand_term_const (map (map (Logic.dest_equals o Thm.prop_of)) set_unfoldss);
    val expand_rels =
      fold expand_term_const (map (single o Logic.dest_equals o Thm.prop_of) rel_unfolds);
    fun unfold_maps ctxt = fold (unfold_thms ctxt o single) map_unfolds;
    fun unfold_sets ctxt = fold (unfold_thms ctxt) set_unfoldss;
    fun unfold_rels ctxt = unfold_thms ctxt rel_unfolds;
    fun unfold_all ctxt = unfold_sets ctxt o unfold_maps ctxt o unfold_rels ctxt;

    val repTA = mk_T_of_bnf Ds As bnf;
    val T_bind = qualify b;
    val TA_params = Term.add_tfreesT repTA [];
    val ((TA, (Rep_name, Abs_name, type_definition, Abs_inverse, Abs_inject)), lthy) =
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
      Term.list_comb (expand_maps (mk_map_of_bnf Ds As Bs bnf), fs)), RepA));
    val bnf_sets = map ((fn t => HOLogic.mk_comp (t, RepA)) o expand_maps o expand_sets)
      (mk_sets_of_bnf (replicate live Ds) (replicate live As) bnf);
    val bnf_bd = mk_bd_of_bnf Ds As bnf;
    val bnf_rel = fold_rev Term.absfree Rs' (mk_vimage2p RepA RepB $
      (Term.list_comb (expand_rels (mk_rel_of_bnf Ds As Bs bnf), Rs)));

    (*bd may depend only on dead type variables*)
    val bd_repT = fst (dest_relT (fastype_of bnf_bd));
    val bdT_bind = qualify (Binding.suffix_name ("_" ^ bdTN) b);
    val params = Term.add_tfreesT bd_repT [];
    val deads = map TFree params;
    val all_deads = map TFree (fold Term.add_tfreesT Ds []);

    val ((bdT_name, (bdT_glob_info, bdT_loc_info)), lthy) =
      typedef (bdT_bind, params, NoSyn)
        (HOLogic.mk_UNIV bd_repT) NONE (EVERY' [rtac exI, rtac UNIV_I] 1) lthy;

    val bnf_bd' = mk_dir_image bnf_bd
      (Const (#Abs_name bdT_glob_info, bd_repT --> Type (bdT_name, deads)))

    val Abs_bdT_inj = mk_Abs_inj_thm (#Abs_inject bdT_loc_info);
    val Abs_bdT_bij = mk_Abs_bij_thm lthy Abs_bdT_inj (#Abs_cases bdT_loc_info);

    val bd_ordIso = @{thm dir_image} OF [Abs_bdT_inj, bd_Card_order_of_bnf bnf];
    val bd_card_order =
      @{thm card_order_dir_image} OF [Abs_bdT_bij, bd_card_order_of_bnf bnf];
    val bd_cinfinite =
      (@{thm Cinfinite_cong} OF [bd_ordIso, bd_Cinfinite_of_bnf bnf]) RS conjunct1;

    fun map_id0_tac ctxt =
      rtac (@{thm type_copy_map_id0} OF [type_definition, unfold_maps ctxt (map_id0_of_bnf bnf)]) 1;
    fun map_comp0_tac ctxt =
      rtac (@{thm type_copy_map_comp0} OF
        [type_definition, unfold_maps ctxt (map_comp0_of_bnf bnf)]) 1;
    fun map_cong0_tac ctxt =
      EVERY' (rtac @{thm type_copy_map_cong0} :: rtac (unfold_all ctxt (map_cong0_of_bnf bnf)) ::
        map (fn i => EVERY' [select_prem_tac live (dtac meta_spec) i, etac meta_mp,
          etac (o_apply RS equalityD2 RS set_mp)]) (1 upto live)) 1;
    fun set_map0_tac thm ctxt =
      rtac (@{thm type_copy_set_map0} OF [type_definition, unfold_all ctxt thm]) 1;
    val set_bd_tacs = map (fn thm => fn ctxt => rtac (@{thm ordLeq_ordIso_trans} OF
        [unfold_sets ctxt thm, bd_ordIso] RS @{thm type_copy_set_bd}) 1)
      (set_bd_of_bnf bnf);
    fun le_rel_OO_tac ctxt =
      rtac (unfold_rels ctxt (le_rel_OO_of_bnf bnf) RS @{thm vimage2p_relcompp_mono}) 1;
    fun rel_OO_Grp_tac ctxt =
      (rtac (unfold_all ctxt (rel_OO_Grp_of_bnf bnf) RS @{thm vimage2p_cong} RS trans) THEN'
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

    fun wit_tac ctxt = ALLGOALS (dtac (type_definition RS @{thm type_copy_wit})) THEN
      mk_simple_wit_tac (map (unfold_all ctxt) (wit_thms_of_bnf bnf));

    val (bnf', lthy') =
      bnf_def Hardly_Inline (user_policy Dont_Note) qualify tacs wit_tac (SOME all_deads)
        Binding.empty Binding.empty []
        ((((((b, TA), bnf_map), bnf_sets), bnf_bd'), bnf_wits), SOME bnf_rel) lthy;
  in
    ((bnf', (all_deads, absT_info)), lthy')
  end;

fun key_of_types Ts = Type ("", Ts);
val key_of_typess = key_of_types o map key_of_types;
fun key_of_comp oDs Dss Ass T = key_of_types (map key_of_typess [[oDs], Dss, Ass, [[T]]]);

fun cache_comp key cache (bnf_dead_lives, (unfold_set, lthy)) =
  (bnf_dead_lives, ((Typtab.update (key, bnf_dead_lives) cache, unfold_set), lthy));

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
            val deads_lives =
              pairself (map (Term.typ_subst_TVars (map fst tvars' ~~ map TFree tfrees)))
                (deads, lives);
          in ((bnf, deads_lives), accum) end
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
            val ((inners, (Dss, Ass)), ((cache', unfold_set'), lthy')) =
              apfst (apsnd split_list o split_list)
                (fold_map2 (fn i => bnf_of_typ Smart_Inline (qualify i) sort Xs Ds0)
                (if length Ts' = 1 then [0] else (1 upto length Ts')) Ts' accum);
            val key = key_of_comp oDs Dss Ass T;
          in
            (case Typtab.lookup cache' key of
              SOME bnf_deads_lives => (bnf_deads_lives, accum)
            | NONE =>
              (unfold_set', lthy')
              |> compose_bnf const_policy qualify sort bnf inners oDs Dss Ass
              |> cache_comp key cache')
          end)
      |> tap check_bad_dead
    end;

end;
