(*  Title:      HOL/Codatatype/Tools/bnf_comp.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Composition of bounded natural functors.
*)

signature BNF_COMP =
sig
  type unfold_thms
  val empty_unfold: unfold_thms
  val map_unfolds_of: unfold_thms -> thm list
  val set_unfoldss_of: unfold_thms -> thm list list
  val rel_unfolds_of: unfold_thms -> thm list
  val pred_unfolds_of: unfold_thms -> thm list

  val default_comp_sort: (string * sort) list list -> (string * sort) list
  val bnf_of_typ: BNF_Def.const_policy -> binding -> (binding -> binding) ->
    ((string * sort) list list -> (string * sort) list) -> typ -> unfold_thms * Proof.context ->
    (BNF_Def.BNF * (typ list * typ list)) * (unfold_thms * Proof.context)
  val bnf_of_typ_cmd: binding * string -> Proof.context -> Proof.context
  val seal_bnf: unfold_thms -> binding -> typ list -> BNF_Def.BNF -> Proof.context ->
    BNF_Def.BNF * local_theory
  val normalize_bnfs: (int -> binding -> binding) -> ''a list list -> ''a list ->
    (''a list list -> ''a list) -> BNF_Def.BNF list -> unfold_thms -> Proof.context ->
    (int list list * ''a list) * (BNF_Def.BNF list * (unfold_thms * Proof.context))
end;

structure BNF_Comp : BNF_COMP =
struct

open BNF_Def
open BNF_Util
open BNF_Tactics
open BNF_Comp_Tactics

type unfold_thms = {
  map_unfolds: thm list,
  set_unfoldss: thm list list,
  rel_unfolds: thm list,
  pred_unfolds: thm list
};

fun add_to_thms thms NONE = thms
  | add_to_thms thms (SOME new) = if Thm.is_reflexive new then thms else insert Thm.eq_thm new thms;
fun adds_to_thms thms NONE = thms
  | adds_to_thms thms (SOME news) = insert (eq_set Thm.eq_thm) (filter_refl news) thms;

fun mk_unfold_thms maps setss rels preds =
  {map_unfolds = maps, set_unfoldss = setss, rel_unfolds = rels, pred_unfolds = preds};

val empty_unfold = mk_unfold_thms [] [] [] [];

fun add_to_unfold_opt map_opt sets_opt rel_opt pred_opt
  {map_unfolds = maps, set_unfoldss = setss, rel_unfolds = rels, pred_unfolds = preds} = {
    map_unfolds = add_to_thms maps map_opt,
    set_unfoldss = adds_to_thms setss sets_opt,
    rel_unfolds = add_to_thms rels rel_opt,
    pred_unfolds = add_to_thms preds pred_opt};

fun add_to_unfold map sets rel pred =
  add_to_unfold_opt (SOME map) (SOME sets) (SOME rel) (SOME pred);

val map_unfolds_of = #map_unfolds;
val set_unfoldss_of = #set_unfoldss;
val rel_unfolds_of = #rel_unfolds;
val pred_unfolds_of = #pred_unfolds;

val bdTN = "bdT";

val compN = "comp_"
fun mk_killN n = "kill" ^ string_of_int n ^ "_";
fun mk_liftN n = "lift" ^ string_of_int n ^ "_";
fun mk_permuteN src dest =
  "permute_" ^ implode (map string_of_int src) ^ "_" ^ implode (map string_of_int dest) ^ "_";

val no_thm = refl;
val Collect_split_box_equals = box_equals RS @{thm Collect_split_cong};
val abs_pred_sym = sym RS @{thm abs_pred_def};
val abs_pred_sym_pred_abs = abs_pred_sym RS @{thm pred_def_abs};

(*copied from Envir.expand_term_free*)
fun expand_term_const defs =
  let
    val eqs = map ((fn ((x, U), u) => (x, (U, u))) o apfst dest_Const) defs;
    val get = fn Const (x, _) => AList.lookup (op =) eqs x | _ => NONE;
  in Envir.expand_term get end;

fun clean_compose_bnf const_policy qualify b outer inners (unfold, lthy) =
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

    val (((fs', Asets), xs), _(*names_lthy*)) = lthy
      |> apfst snd o mk_Frees' "f" (map2 (curry (op -->)) As Bs)
      ||>> mk_Frees "A" (map (HOLogic.mk_setT) As)
      ||>> mk_Frees "x" As;

    val CAs = map3 mk_T_of_bnf Dss Ass_repl inners;
    val CCA = mk_T_of_bnf oDs CAs outer;
    val CBs = map3 mk_T_of_bnf Dss Bss_repl inners;
    val outer_sets = mk_sets_of_bnf (replicate olive oDs) (replicate olive CAs) outer;
    val inner_setss = map3 mk_sets_of_bnf (map (replicate ilive) Dss) (replicate olive Ass) inners;
    val inner_bds = map3 mk_bd_of_bnf Dss Ass_repl inners;
    val outer_bd = mk_bd_of_bnf oDs CAs outer;

    (*%f1 ... fn. outer.map (inner_1.map f1 ... fn) ... (inner_m.map f1 ... fn)*)
    val comp_map = fold_rev Term.abs fs'
      (Term.list_comb (mk_map_of_bnf oDs CAs CBs outer,
        map2 (fn Ds => (fn f => Term.list_comb (f, map Bound ((ilive - 1) downto 0))) o
          mk_map_of_bnf Ds As Bs) Dss inners));

    (*Union o collect {outer.set_1 ... outer.set_m} o outer.map inner_1.set_i ... inner_m.set_i*)
    (*Union o collect {image inner_1.set_i o outer.set_1 ... image inner_m.set_i o outer.set_m}*)
    fun mk_comp_set i =
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

    val (comp_sets, comp_sets_alt) = map_split mk_comp_set (0 upto ilive - 1);

    (*(inner_1.bd +c ... +c inner_m.bd) *c outer.bd*)
    val comp_bd = Term.absdummy CCA (mk_cprod
      (Library.foldr1 (uncurry mk_csum) inner_bds) outer_bd);

    fun comp_map_id_tac {context = ctxt, ...} =
      let
        (*order the theorems by reverse size to prevent bad interaction with nonconfluent rewrite
          rules*)
        val thms = (map map_id_of_bnf inners
          |> map (`(Term.size_of_term o Thm.prop_of))
          |> sort (rev_order o int_ord o pairself fst)
          |> map snd) @ [map_id_of_bnf outer];
      in
        (EVERY' (map (fn thm => subst_tac ctxt [thm]) thms) THEN' rtac refl) 1
      end;

    fun comp_map_comp_tac _ =
      mk_comp_map_comp_tac (map_comp_of_bnf outer) (map_cong_of_bnf outer)
        (map map_comp_of_bnf inners);

    fun mk_single_comp_set_natural_tac i _ =
      mk_comp_set_natural_tac (map_comp_of_bnf outer) (map_cong_of_bnf outer)
        (collect_set_natural_of_bnf outer)
        (map ((fn thms => nth thms i) o set_natural_of_bnf) inners);

    val comp_set_natural_tacs = map mk_single_comp_set_natural_tac (0 upto ilive - 1);

    fun comp_bd_card_order_tac _ =
      mk_comp_bd_card_order_tac (map bd_card_order_of_bnf inners) (bd_card_order_of_bnf outer);

    fun comp_bd_cinfinite_tac _ =
      mk_comp_bd_cinfinite_tac (bd_cinfinite_of_bnf inner) (bd_cinfinite_of_bnf outer);

    val comp_set_alt_thms =
      if ! quick_and_dirty then
        replicate ilive no_thm
      else
        map (fn goal => Skip_Proof.prove lthy [] [] goal
        (fn {context, ...} => (mk_comp_set_alt_tac context (collect_set_natural_of_bnf outer))))
        (map2 (curry (HOLogic.mk_Trueprop o HOLogic.mk_eq)) comp_sets comp_sets_alt);

    fun comp_map_cong_tac _ =
      mk_comp_map_cong_tac comp_set_alt_thms (map_cong_of_bnf outer) (map map_cong_of_bnf inners);

    val comp_set_bd_tacs =
      if ! quick_and_dirty then
        replicate (length comp_set_alt_thms) (K all_tac)
      else
        let
          val outer_set_bds = set_bd_of_bnf outer;
          val inner_set_bdss = map set_bd_of_bnf inners;
          val inner_bd_Card_orders = map bd_Card_order_of_bnf inners;
          fun comp_single_set_bd_thm i j =
            @{thm comp_single_set_bd} OF [nth inner_bd_Card_orders j, nth (nth inner_set_bdss j) i,
              nth outer_set_bds j]
          val single_set_bd_thmss =
            map ((fn f => map f (0 upto olive - 1)) o comp_single_set_bd_thm) (0 upto ilive - 1);
        in
          map2 (fn comp_set_alt => fn single_set_bds => fn {context, ...} =>
            mk_comp_set_bd_tac context comp_set_alt single_set_bds)
          comp_set_alt_thms single_set_bd_thmss
        end;

    val comp_in_alt_thm =
      if ! quick_and_dirty then
        no_thm
      else
        let
          val comp_in = mk_in Asets comp_sets CCA;
          val comp_in_alt = mk_in (map2 (mk_in Asets) inner_setss CAs) outer_sets CCA;
          val goal =
            fold_rev Logic.all Asets
              (HOLogic.mk_Trueprop (HOLogic.mk_eq (comp_in, comp_in_alt)));
        in
          Skip_Proof.prove lthy [] [] goal
            (fn {context, ...} => mk_comp_in_alt_tac context comp_set_alt_thms)
        end;

    fun comp_in_bd_tac _ =
      mk_comp_in_bd_tac comp_in_alt_thm (map in_bd_of_bnf inners) (in_bd_of_bnf outer)
        (map bd_Cinfinite_of_bnf inners) (bd_Card_order_of_bnf outer);

    fun comp_map_wpull_tac _ =
      mk_map_wpull_tac comp_in_alt_thm (map map_wpull_of_bnf inners) (map_wpull_of_bnf outer);

    val tacs = [comp_map_id_tac, comp_map_comp_tac, comp_map_cong_tac] @ comp_set_natural_tacs @
      [comp_bd_card_order_tac, comp_bd_cinfinite_tac] @ comp_set_bd_tacs @
      [comp_in_bd_tac, comp_map_wpull_tac];

    val outer_wits = mk_wits_of_bnf (replicate onwits oDs) (replicate onwits CAs) outer;

    val inner_witss = map (map (fn (I, wit) => Term.list_comb (wit, map (nth xs) I)))
      (map3 (fn Ds => fn n => mk_wits_of_bnf (replicate n Ds) (replicate n As))
        Dss inwitss inners);

    val inner_witsss = map (map (nth inner_witss) o fst) outer_wits;

    val comp_wits = (inner_witsss, (map (single o snd) outer_wits))
      |-> map2 (fold (map_product (fn iwit => fn owit => owit $ iwit)))
      |> flat
      |> map (`(fn t => Term.add_frees t []))
      |> minimize_wits
      |> map (fn (frees, t) => fold absfree frees t);

    fun wit_tac {context = ctxt, ...} =
      mk_comp_wit_tac ctxt (wit_thms_of_bnf outer) (collect_set_natural_of_bnf outer)
        (maps wit_thms_of_bnf inners);

    val (bnf', lthy') =
      add_bnf const_policy (K Derive_Some_Facts) qualify tacs wit_tac (SOME (oDs @ flat Dss))
        ((((b, comp_map), comp_sets), comp_bd), comp_wits) lthy;

    val outer_rel_Gr = rel_Gr_of_bnf outer RS sym;
    val outer_rel_cong = rel_cong_of_bnf outer;

    val comp_rel_unfold_thm =
      trans OF [rel_def_of_bnf bnf',
        trans OF [comp_in_alt_thm RS @{thm subst_rel_def},
          trans OF [@{thm arg_cong2[of _ _ _ _ relcomp]} OF
            [trans OF [outer_rel_Gr RS @{thm arg_cong[of _ _ converse]},
              rel_converse_of_bnf outer RS sym], outer_rel_Gr],
            trans OF [rel_O_of_bnf outer RS sym, outer_rel_cong OF
              (map (fn bnf => rel_def_of_bnf bnf RS sym) inners)]]]];

    val comp_pred_unfold_thm = Collect_split_box_equals OF [comp_rel_unfold_thm,
      pred_def_of_bnf bnf' RS abs_pred_sym,
        trans OF [outer_rel_cong OF (map (fn bnf => pred_def_of_bnf bnf RS abs_pred_sym) inners),
          pred_def_of_bnf outer RS abs_pred_sym]];

    val unfold' = add_to_unfold (map_def_of_bnf bnf') (set_defs_of_bnf bnf')
      comp_rel_unfold_thm comp_pred_unfold_thm unfold;
  in
    (bnf', (unfold', lthy'))
  end;

fun clean_compose_bnf_cmd (outer, inners) lthy =
  let
    val outer = the (bnf_of lthy outer)
    val inners = map (the o bnf_of lthy) inners
    val b = name_of_bnf outer
      |> Binding.prefix_name compN
      |> Binding.suffix_name ("_" ^ implode (map (Binding.name_of o name_of_bnf) inners));
  in
    (snd o snd) (clean_compose_bnf Dont_Inline I b outer inners
      (empty_unfold, lthy))
  end;

(* Killing live variables *)

fun killN_bnf qualify n bnf (unfold, lthy) = if n = 0 then (bnf, (unfold, lthy)) else
  let
    val b = Binding.prefix_name (mk_killN n) (name_of_bnf bnf);
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
      |> mk_Frees "A" (map (HOLogic.mk_setT) (drop n As))
      ||>> mk_Frees "x" (drop n As);
    val xs = map (fn T => HOLogic.choice_const T $ absdummy T @{term True}) killedAs @ lives;

    val T = mk_T_of_bnf Ds As bnf;

    (*bnf.map id ... id*)
    val killN_map = Term.list_comb (mk_map_of_bnf Ds As Bs bnf, map HOLogic.id_const killedAs);

    val bnf_sets = mk_sets_of_bnf (replicate live Ds) (replicate live As) bnf;
    val killN_sets = drop n bnf_sets;

    (*(|UNIV :: A1 set| +c ... +c |UNIV :: An set|) *c bnf.bd*)
    val bnf_bd = mk_bd_of_bnf Ds As bnf;
    val killN_bd = mk_cprod
      (Library.foldr1 (uncurry mk_csum) (map (mk_card_of o HOLogic.mk_UNIV) killedAs)) bnf_bd;

    fun killN_map_id_tac _ = rtac (map_id_of_bnf bnf) 1;
    fun killN_map_comp_tac {context, ...} =
      Local_Defs.unfold_tac context ((map_comp_of_bnf bnf RS sym) :: @{thms o_assoc id_o o_id}) THEN
      rtac refl 1;
    fun killN_map_cong_tac {context, ...} =
      mk_killN_map_cong_tac context n (live - n) (map_cong_of_bnf bnf);
    val killN_set_natural_tacs =
      map (fn thm => fn _ => rtac thm 1) (drop n (set_natural_of_bnf bnf));
    fun killN_bd_card_order_tac _ = mk_killN_bd_card_order_tac n (bd_card_order_of_bnf bnf);
    fun killN_bd_cinfinite_tac _ = mk_killN_bd_cinfinite_tac (bd_Cinfinite_of_bnf bnf);
    val killN_set_bd_tacs =
      map (fn thm => fn _ => mk_killN_set_bd_tac (bd_Card_order_of_bnf bnf) thm)
        (drop n (set_bd_of_bnf bnf));

    val killN_in_alt_thm =
      if ! quick_and_dirty then
        no_thm
      else
        let
          val killN_in = mk_in Asets killN_sets T;
          val killN_in_alt = mk_in (map HOLogic.mk_UNIV killedAs @ Asets) bnf_sets T;
          val goal =
            fold_rev Logic.all Asets (HOLogic.mk_Trueprop (HOLogic.mk_eq (killN_in, killN_in_alt)));
        in
          Skip_Proof.prove lthy [] [] goal (K killN_in_alt_tac)
        end;

    fun killN_in_bd_tac _ =
      mk_killN_in_bd_tac n (live > n) killN_in_alt_thm (in_bd_of_bnf bnf)
         (bd_Card_order_of_bnf bnf) (bd_Cinfinite_of_bnf bnf) (bd_Cnotzero_of_bnf bnf);
    fun killN_map_wpull_tac _ =
      mk_map_wpull_tac killN_in_alt_thm [] (map_wpull_of_bnf bnf);

    val tacs = [killN_map_id_tac, killN_map_comp_tac, killN_map_cong_tac] @ killN_set_natural_tacs @
      [killN_bd_card_order_tac, killN_bd_cinfinite_tac] @ killN_set_bd_tacs @
      [killN_in_bd_tac, killN_map_wpull_tac];

    val wits = mk_wits_of_bnf (replicate nwits Ds) (replicate nwits As) bnf;

    val killN_wits = map (fn t => fold absfree (Term.add_frees t []) t)
      (map (fn (I, wit) => Term.list_comb (wit, map (nth xs) I)) wits);

    fun wit_tac _ = mk_simple_wit_tac (wit_thms_of_bnf bnf);

    val (bnf', lthy') =
      add_bnf Smart_Inline (K Derive_Some_Facts) qualify tacs wit_tac (SOME (killedAs @ Ds))
        ((((b, killN_map), killN_sets), Term.absdummy T killN_bd), killN_wits) lthy;

    val rel_Gr = rel_Gr_of_bnf bnf RS sym;

    val killN_rel_unfold_thm =
      trans OF [rel_def_of_bnf bnf',
        trans OF [killN_in_alt_thm RS @{thm subst_rel_def},
          trans OF [@{thm arg_cong2[of _ _ _ _ relcomp]} OF
            [trans OF [rel_Gr RS @{thm arg_cong[of _ _ converse]}, rel_converse_of_bnf bnf RS sym],
              rel_Gr],
            trans OF [rel_O_of_bnf bnf RS sym, rel_cong_of_bnf bnf OF
              (replicate n @{thm trans[OF Gr_UNIV_id[OF refl] Id_alt[symmetric]]} @
               replicate (live - n) @{thm Gr_fst_snd})]]]];

    val killN_pred_unfold_thm = Collect_split_box_equals OF
      [Local_Defs.unfold lthy' @{thms Id_def'} killN_rel_unfold_thm,
        pred_def_of_bnf bnf' RS abs_pred_sym, pred_def_of_bnf bnf RS abs_pred_sym];

    val unfold' = add_to_unfold (map_def_of_bnf bnf') (set_defs_of_bnf bnf')
      killN_rel_unfold_thm killN_pred_unfold_thm unfold;
  in
    (bnf', (unfold', lthy'))
  end;

fun killN_bnf_cmd (n, raw_bnf) lthy =
  (snd o snd) (killN_bnf I n (the (bnf_of lthy raw_bnf)) (empty_unfold, lthy));

(* Adding dummy live variables *)

fun liftN_bnf qualify n bnf (unfold, lthy) = if n = 0 then (bnf, (unfold, lthy)) else
  let
    val b = Binding.prefix_name (mk_liftN n) (name_of_bnf bnf);
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
      |> mk_Frees "A" (map (HOLogic.mk_setT) (newAs @ As));

    val T = mk_T_of_bnf Ds As bnf;

    (*%f1 ... fn. bnf.map*)
    val liftN_map =
      fold_rev Term.absdummy (map2 (curry (op -->)) newAs newBs) (mk_map_of_bnf Ds As Bs bnf);

    val bnf_sets = mk_sets_of_bnf (replicate live Ds) (replicate live As) bnf;
    val liftN_sets = map (fn A => absdummy T (HOLogic.mk_set A [])) newAs @ bnf_sets;

    val liftN_bd = mk_bd_of_bnf Ds As bnf;

    fun liftN_map_id_tac _ = rtac (map_id_of_bnf bnf) 1;
    fun liftN_map_comp_tac {context, ...} =
      Local_Defs.unfold_tac context ((map_comp_of_bnf bnf RS sym) :: @{thms o_assoc id_o o_id}) THEN
      rtac refl 1;
    fun liftN_map_cong_tac {context, ...} =
      rtac (map_cong_of_bnf bnf) 1 THEN REPEAT_DETERM_N live (Goal.assume_rule_tac context 1);
    val liftN_set_natural_tacs =
      if ! quick_and_dirty then
        replicate (n + live) (K all_tac)
      else
        replicate n (K empty_natural_tac) @
        map (fn thm => fn _ => rtac thm 1) (set_natural_of_bnf bnf);
    fun liftN_bd_card_order_tac _ = rtac (bd_card_order_of_bnf bnf) 1;
    fun liftN_bd_cinfinite_tac _ = rtac (bd_cinfinite_of_bnf bnf) 1;
    val liftN_set_bd_tacs =
      if ! quick_and_dirty then
        replicate (n + live) (K all_tac)
      else
        replicate n (K (mk_liftN_set_bd_tac (bd_Card_order_of_bnf bnf))) @
        (map (fn thm => fn _ => rtac thm 1) (set_bd_of_bnf bnf));

    val liftN_in_alt_thm =
      if ! quick_and_dirty then
        no_thm
      else
        let
          val liftN_in = mk_in Asets liftN_sets T;
          val liftN_in_alt = mk_in (drop n Asets) bnf_sets T;
          val goal =
            fold_rev Logic.all Asets (HOLogic.mk_Trueprop (HOLogic.mk_eq (liftN_in, liftN_in_alt)))
        in
          Skip_Proof.prove lthy [] [] goal (K liftN_in_alt_tac)
        end;

    fun liftN_in_bd_tac _ =
      mk_liftN_in_bd_tac n liftN_in_alt_thm (in_bd_of_bnf bnf) (bd_Card_order_of_bnf bnf);
    fun liftN_map_wpull_tac _ =
      mk_map_wpull_tac liftN_in_alt_thm [] (map_wpull_of_bnf bnf);

    val tacs = [liftN_map_id_tac, liftN_map_comp_tac, liftN_map_cong_tac] @ liftN_set_natural_tacs @
      [liftN_bd_card_order_tac, liftN_bd_cinfinite_tac] @ liftN_set_bd_tacs @
      [liftN_in_bd_tac, liftN_map_wpull_tac];

    val liftN_wits = map snd (mk_wits_of_bnf (replicate nwits Ds) (replicate nwits As) bnf);

    fun wit_tac _ = mk_simple_wit_tac (wit_thms_of_bnf bnf);

    val (bnf', lthy') =
      add_bnf Smart_Inline (K Derive_Some_Facts) qualify tacs wit_tac (SOME Ds)
        ((((b, liftN_map), liftN_sets), Term.absdummy T liftN_bd), liftN_wits) lthy;

    val liftN_rel_unfold_thm =
      trans OF [rel_def_of_bnf bnf',
        trans OF [liftN_in_alt_thm RS @{thm subst_rel_def}, rel_def_of_bnf bnf RS sym]];

    val liftN_pred_unfold_thm = Collect_split_box_equals OF [liftN_rel_unfold_thm,
      pred_def_of_bnf bnf' RS abs_pred_sym, pred_def_of_bnf bnf RS abs_pred_sym];

    val unfold' = add_to_unfold (map_def_of_bnf bnf') (set_defs_of_bnf bnf')
      liftN_rel_unfold_thm liftN_pred_unfold_thm unfold;
  in
    (bnf', (unfold', lthy'))
  end;

fun liftN_bnf_cmd (n, raw_bnf) lthy =
  (snd o snd) (liftN_bnf I n (the (bnf_of lthy raw_bnf)) (empty_unfold, lthy));

(* Changing the order of live variables *)

fun permute_bnf qualify src dest bnf (unfold, lthy) = if src = dest then (bnf, (unfold, lthy)) else
  let
    val b = Binding.prefix_name (mk_permuteN src dest) (name_of_bnf bnf);
    val live = live_of_bnf bnf;
    val dead = dead_of_bnf bnf;
    val nwits = nwits_of_bnf bnf;
    fun permute xs = mk_permute src dest xs;
    fun permute_rev xs = mk_permute dest src xs;

    val (Ds, lthy1) = apfst (map TFree)
      (Variable.invent_types (replicate dead HOLogic.typeS) lthy);
    val (As, lthy2) = apfst (map TFree)
      (Variable.invent_types (replicate live HOLogic.typeS) lthy1);
    val (Bs, _(*lthy3*)) = apfst (map TFree)
      (Variable.invent_types (replicate live HOLogic.typeS) lthy2);

    val (Asets, _(*names_lthy*)) = lthy
      |> mk_Frees "A" (map (HOLogic.mk_setT) (permute As));

    val T = mk_T_of_bnf Ds As bnf;

    (*%f(1) ... f(n). bnf.map f\<sigma>(1) ... f\<sigma>(n)*)
    val permute_map = fold_rev Term.absdummy (permute (map2 (curry op -->) As Bs))
      (Term.list_comb (mk_map_of_bnf Ds As Bs bnf,
        permute_rev (map Bound ((live - 1) downto 0))));

    val bnf_sets = mk_sets_of_bnf (replicate live Ds) (replicate live As) bnf;
    val permute_sets = permute bnf_sets;

    val permute_bd = mk_bd_of_bnf Ds As bnf;

    fun permute_map_id_tac _ = rtac (map_id_of_bnf bnf) 1;
    fun permute_map_comp_tac _ = rtac (map_comp_of_bnf bnf) 1;
    fun permute_map_cong_tac {context, ...} =
      rtac (map_cong_of_bnf bnf) 1 THEN REPEAT_DETERM_N live (Goal.assume_rule_tac context 1);
    val permute_set_natural_tacs =
      permute (map (fn thm => fn _ => rtac thm 1) (set_natural_of_bnf bnf));
    fun permute_bd_card_order_tac _ = rtac (bd_card_order_of_bnf bnf) 1;
    fun permute_bd_cinfinite_tac _ = rtac (bd_cinfinite_of_bnf bnf) 1;
    val permute_set_bd_tacs = permute (map (fn thm => fn _ => rtac thm 1) (set_bd_of_bnf bnf));

    val permute_in_alt_thm =
      if ! quick_and_dirty then
        no_thm
      else
        let
          val permute_in = mk_in Asets permute_sets T;
          val permute_in_alt = mk_in (permute_rev Asets) bnf_sets T;
          val goal =
            fold_rev Logic.all Asets
              (HOLogic.mk_Trueprop (HOLogic.mk_eq (permute_in, permute_in_alt)));
        in
          Skip_Proof.prove lthy [] [] goal (K (mk_permute_in_alt_tac src dest))
        end;

    fun permute_in_bd_tac _ =
      mk_permute_in_bd_tac src dest permute_in_alt_thm (in_bd_of_bnf bnf)
        (bd_Card_order_of_bnf bnf);
    fun permute_map_wpull_tac _ =
      mk_map_wpull_tac permute_in_alt_thm [] (map_wpull_of_bnf bnf);

    val tacs = [permute_map_id_tac, permute_map_comp_tac, permute_map_cong_tac] @
      permute_set_natural_tacs @ [permute_bd_card_order_tac, permute_bd_cinfinite_tac] @
      permute_set_bd_tacs @ [permute_in_bd_tac, permute_map_wpull_tac];

    val permute_wits = map snd (mk_wits_of_bnf (replicate nwits Ds) (replicate nwits As) bnf);

    fun wit_tac _ = mk_simple_wit_tac (wit_thms_of_bnf bnf);

    val (bnf', lthy') =
      add_bnf Smart_Inline (K Derive_Some_Facts) qualify tacs wit_tac (SOME Ds)
        ((((b, permute_map), permute_sets), Term.absdummy T permute_bd), permute_wits) lthy;

    val permute_rel_unfold_thm =
      trans OF [rel_def_of_bnf bnf',
        trans OF [permute_in_alt_thm RS @{thm subst_rel_def}, rel_def_of_bnf bnf RS sym]];

    val permute_pred_unfold_thm = Collect_split_box_equals OF [permute_rel_unfold_thm,
      pred_def_of_bnf bnf' RS abs_pred_sym, pred_def_of_bnf bnf RS abs_pred_sym];

    val unfold' = add_to_unfold (map_def_of_bnf bnf') (set_defs_of_bnf bnf')
      permute_rel_unfold_thm permute_pred_unfold_thm unfold;
  in
    (bnf', (unfold', lthy'))
  end;

fun permute_bnf_cmd ((src, dest), raw_bnf) lthy =
  (snd o snd) (permute_bnf I src dest (the (bnf_of lthy raw_bnf))
    (empty_unfold, lthy));

(* Hide the type of the bound (optimization) and unfold the definitions (nicer to the user) *)

fun seal_bnf unfold b Ds bnf lthy =
  let
    val live = live_of_bnf bnf;
    val nwits = nwits_of_bnf bnf;

    val (As, lthy1) = apfst (map TFree)
      (Variable.invent_types (replicate live HOLogic.typeS) (fold Variable.declare_typ Ds lthy));
    val (Bs, _) = apfst (map TFree)
      (Variable.invent_types (replicate live HOLogic.typeS) lthy1);

    val map_unfolds = filter_refl (map_unfolds_of unfold);
    val set_unfoldss = map filter_refl (set_unfoldss_of unfold);

    val expand_maps = fold expand_term_const (map (single o Logic.dest_equals o Thm.prop_of)
      map_unfolds);
    val expand_sets = fold expand_term_const (map (map (Logic.dest_equals o Thm.prop_of))
      set_unfoldss);
    val unfold_maps = fold (Local_Defs.unfold lthy o single) map_unfolds;
    val unfold_sets = fold (Local_Defs.unfold lthy) set_unfoldss;
    val unfold_defs = unfold_sets o unfold_maps;
    val bnf_map = expand_maps (mk_map_of_bnf Ds As Bs bnf);
    val bnf_sets = map (expand_maps o expand_sets)
      (mk_sets_of_bnf (replicate live Ds) (replicate live As) bnf);
    val bnf_bd = mk_bd_of_bnf Ds As bnf;
    val T = mk_T_of_bnf Ds As bnf;

    (*bd should only depend on dead type variables!*)
    val bd_repT = fst (dest_relT (fastype_of bnf_bd));
    val bdT_bind = Binding.suffix_name ("_" ^ bdTN) b;
    val params = fold Term.add_tfreesT Ds [];

    val ((bdT_name, (bdT_glob_info, bdT_loc_info)), (lthy', lthy)) =
      lthy
      |> Typedef.add_typedef true NONE (bdT_bind, params, NoSyn)
        (HOLogic.mk_UNIV bd_repT) NONE (EVERY' [rtac exI, rtac UNIV_I] 1)
      ||> `Local_Theory.restore;

    val phi = Proof_Context.export_morphism lthy lthy';

    val bnf_bd' = mk_dir_image bnf_bd
      (Const (#Abs_name bdT_glob_info, bd_repT --> Type (bdT_name, map TFree params)))

    val set_def = Morphism.thm phi (the (#set_def bdT_loc_info));
    val Abs_inject = Morphism.thm phi (#Abs_inject bdT_loc_info);
    val Abs_cases = Morphism.thm phi (#Abs_cases bdT_loc_info);

    val Abs_bdT_inj = mk_Abs_inj_thm set_def Abs_inject;
    val Abs_bdT_bij = mk_Abs_bij_thm lthy' set_def Abs_inject Abs_cases;

    val bd_ordIso = @{thm dir_image} OF [Abs_bdT_inj, bd_Card_order_of_bnf bnf];
    val bd_card_order =
      @{thm card_order_dir_image} OF [Abs_bdT_bij, bd_card_order_of_bnf bnf];
    val bd_cinfinite =
      (@{thm Cinfinite_cong} OF [bd_ordIso, bd_Cinfinite_of_bnf bnf]) RS conjunct1;

    val set_bds =
      map (fn thm => @{thm ordLeq_ordIso_trans} OF [thm, bd_ordIso]) (set_bd_of_bnf bnf);
    val in_bd =
      @{thm ordLeq_ordIso_trans} OF [in_bd_of_bnf bnf,
        @{thm cexp_cong2_Cnotzero} OF [bd_ordIso, if live = 0 then
          @{thm ctwo_Cnotzero} else @{thm ctwo_Cnotzero} RS @{thm csum_Cnotzero2},
            bd_Card_order_of_bnf bnf]];

    fun mk_tac thm {context = ctxt, prems = _} = (rtac (unfold_defs thm) THEN'
      SOLVE o REPEAT_DETERM o (atac ORELSE' Goal.assume_rule_tac ctxt)) 1;
    val tacs =
      map mk_tac ([map_id_of_bnf bnf, map_comp_of_bnf bnf, map_cong_of_bnf bnf] @
        set_natural_of_bnf bnf) @
      map K [rtac bd_card_order 1, rtac bd_cinfinite 1] @
      map mk_tac (set_bds @ [in_bd, map_wpull_of_bnf bnf]);

    val bnf_wits = map snd (mk_wits_of_bnf (replicate nwits Ds) (replicate nwits As) bnf);

    fun wit_tac _ = mk_simple_wit_tac (map unfold_defs (wit_thms_of_bnf bnf));

    val (bnf', lthy') = add_bnf Hardly_Inline (K Derive_All_Facts) I tacs wit_tac NONE
        ((((b, bnf_map), bnf_sets), Term.absdummy T bnf_bd'), bnf_wits) lthy;

    val defs' = filter_refl (map_def_of_bnf bnf' :: set_defs_of_bnf bnf');
    val unfold_defs' = unfold_defs o Local_Defs.unfold lthy' defs';

    val rel_def = unfold_defs' (rel_def_of_bnf bnf');
    val rel_unfold = Local_Defs.unfold lthy'
      (map unfold_defs (filter_refl (rel_unfolds_of unfold))) rel_def;

    val unfold_defs'' =
      unfold_defs' o (Local_Defs.unfold lthy' (filter_refl [rel_def_of_bnf bnf']));

    val pred_def = unfold_defs'' (pred_def_of_bnf bnf' RS abs_pred_sym_pred_abs);
    val pred_unfold = Local_Defs.unfold lthy'
      (map unfold_defs (filter_refl (pred_unfolds_of unfold))) pred_def;

    fun note thmN thms =
      snd o Local_Theory.note
        ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), thms);
  in
    (bnf', lthy'
      |> note rel_unfoldN [rel_unfold]
      |> note pred_unfoldN [pred_unfold])
  end;

(* Composition pipeline *)

fun permute_and_kill qualify n src dest bnf =
  bnf
  |> permute_bnf qualify src dest
  #> uncurry (killN_bnf qualify n);

fun lift_and_permute qualify n src dest bnf =
  bnf
  |> liftN_bnf qualify n
  #> uncurry (permute_bnf qualify src dest);

fun normalize_bnfs qualify Ass Ds sort bnfs unfold lthy =
  let
    val before_kill_src = map (fn As => 0 upto (length As - 1)) Ass;
    val kill_poss = map (find_indices Ds) Ass;
    val live_poss = map2 (subtract (op =)) kill_poss before_kill_src;
    val before_kill_dest = map2 append kill_poss live_poss;
    val kill_ns = map length kill_poss;
    val (inners', (unfold', lthy')) =
      fold_map5 (fn i => permute_and_kill (qualify i))
        (if length bnfs = 1 then [0] else (1 upto length bnfs))
        kill_ns before_kill_src before_kill_dest bnfs (unfold, lthy);

    val Ass' = map2 (map o nth) Ass live_poss;
    val As = sort Ass';
    val after_lift_dest = replicate (length Ass') (0 upto (length As - 1));
    val old_poss = map (map (fn x => find_index (fn y => x = y) As)) Ass';
    val new_poss = map2 (subtract (op =)) old_poss after_lift_dest;
    val after_lift_src = map2 append new_poss old_poss;
    val lift_ns = map (fn xs => length As - length xs) Ass';
  in
    ((kill_poss, As), fold_map5 (fn i => lift_and_permute (qualify i))
      (if length bnfs = 1 then [0] else (1 upto length bnfs))
      lift_ns after_lift_src after_lift_dest inners' (unfold', lthy'))
  end;

fun default_comp_sort Ass =
  Library.sort (Term_Ord.typ_ord o pairself TFree) (fold (fold (insert (op =))) Ass []);

fun compose_bnf const_policy qualify' b sort outer inners oDs Dss tfreess (unfold, lthy) =
  let
    val name = Binding.name_of b;
    fun qualify i bind =
      let val namei = if i > 0 then name ^ string_of_int i else name;
      in
        if member (op =) (#2 (Binding.dest bind)) (namei, true) then qualify' bind
        else qualify' (Binding.prefix_name namei bind)
      end;

    val Ass = map (map dest_TFree) tfreess;
    val Ds = fold (fold Term.add_tfreesT) (oDs :: Dss) [];

    val ((kill_poss, As), (inners', (unfold', lthy'))) =
      normalize_bnfs qualify Ass Ds sort inners unfold lthy;

    val Ds = oDs @ flat (map3 (append oo map o nth) tfreess kill_poss Dss);
    val As = map TFree As;
  in
    apfst (rpair (Ds, As)) (clean_compose_bnf const_policy I b outer inners' (unfold', lthy'))
  end;

fun compose_bnf_cmd (((((b, outer), inners), oDs), Dss), Ass) lthy = (snd o snd)
  (compose_bnf Dont_Inline I b default_comp_sort (the (bnf_of lthy outer))
    (map (the o bnf_of lthy) inners)
    (map (Syntax.read_typ lthy) oDs) (map (map (Syntax.read_typ lthy)) Dss)
    (map (map (Syntax.read_typ lthy)) Ass) (empty_unfold, lthy));

fun bnf_of_typ _ _ _ _ (T as TFree _) (unfold, lthy) =
    ((Basic_BNFs.ID_bnf, ([], [T])), (add_to_unfold_opt NONE NONE
      (SOME Basic_BNFs.ID_rel_def) (SOME Basic_BNFs.ID_pred_def) unfold, lthy))
  | bnf_of_typ _ _ _ _ (TVar _) _ = error "Unexpected schematic variable"
  | bnf_of_typ const_policy b qualify' sort (T as Type (C, Ts)) (unfold, lthy) =
    let val tfrees = Term.add_tfreesT T [];
    in
      if null tfrees then
        ((Basic_BNFs.DEADID_bnf, ([T], [])), (unfold, lthy))
      else if forall (can Term.dest_TFree) Ts andalso length Ts = length tfrees then let
        val bnf = the (bnf_of lthy (Long_Name.base_name C));
        val T' = T_of_bnf bnf;
        val deads = deads_of_bnf bnf;
        val lives = lives_of_bnf bnf;
        val tvars' = Term.add_tvarsT T' [];
        val deads_lives =
          pairself (map (Term.typ_subst_TVars (map fst tvars' ~~ map TFree tfrees)))
          (deads, lives);
      val rel_def = rel_def_of_bnf bnf;
      val unfold' = add_to_unfold_opt NONE NONE (SOME (rel_def RS sym))
        (SOME (Local_Defs.unfold lthy [rel_def] (pred_def_of_bnf bnf) RS sym)) unfold;
      in ((bnf, deads_lives), (unfold', lthy)) end
      else
        let
          (* FIXME: we should allow several BNFs with the same base name *)
          val Tname = Long_Name.base_name C;
          val name = Binding.name_of b ^ "_" ^ Tname;
          fun qualify i bind =
            let val namei = if i > 0 then name ^ string_of_int i else name;
            in
              if member (op =) (#2 (Binding.dest bind)) (namei, true) then qualify' bind
              else qualify' (Binding.prefix_name namei bind)
            end;
          val outer = the (bnf_of lthy Tname);
          val odead = dead_of_bnf outer;
          val olive = live_of_bnf outer;
          val oDs_pos = find_indices [TFree ("dead", [])]
            (snd (dest_Type
              (mk_T_of_bnf (replicate odead (TFree ("dead", []))) (replicate olive dummyT) outer)));
          val oDs = map (nth Ts) oDs_pos;
          val Ts' = map (nth Ts) (subtract (op =) oDs_pos (0 upto length Ts - 1));
          val ((inners, (Dss, Ass)), (unfold', lthy')) =
            apfst (apsnd split_list o split_list)
              (fold_map2 (fn i =>
                  bnf_of_typ Smart_Inline (Binding.name (name ^ string_of_int i)) (qualify i) sort)
                (if length Ts' = 1 then [0] else (1 upto length Ts'))
                Ts' (unfold, lthy));
        in
          compose_bnf const_policy (qualify 0) b sort outer inners oDs Dss Ass (unfold', lthy')
        end
    end;

fun bnf_of_typ_cmd (b, rawT) lthy = (snd o snd)
  (bnf_of_typ Dont_Inline b I default_comp_sort (Syntax.read_typ lthy rawT)
    (empty_unfold, lthy));

val _ =
  Outer_Syntax.local_theory @{command_spec "bnf_of_typ"} "parse a type as composition of BNFs"
    (((Parse.binding --| Parse.$$$ "=") -- Parse.typ) >> bnf_of_typ_cmd);

end;
