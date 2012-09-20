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

  val bnf_of_typ: BNF_Def.const_policy -> (binding -> binding) ->
    ((string * sort) list list -> (string * sort) list) -> typ -> unfold_thms * Proof.context ->
    (BNF_Def.BNF * (typ list * typ list)) * (unfold_thms * Proof.context)
  val default_comp_sort: (string * sort) list list -> (string * sort) list
  val normalize_bnfs: (int -> binding -> binding) -> ''a list list -> ''a list ->
    (''a list list -> ''a list) -> BNF_Def.BNF list -> unfold_thms -> Proof.context ->
    (int list list * ''a list) * (BNF_Def.BNF list * (unfold_thms * Proof.context))
  val seal_bnf: unfold_thms -> binding -> typ list -> BNF_Def.BNF -> Proof.context ->
    (BNF_Def.BNF * typ list) * local_theory
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
  rel_unfolds: thm list
};

fun add_to_thms thms NONE = thms
  | add_to_thms thms (SOME new) = if Thm.is_reflexive new then thms else insert Thm.eq_thm new thms;
fun adds_to_thms thms NONE = thms
  | adds_to_thms thms (SOME news) = insert (eq_set Thm.eq_thm) (filter_out_refl news) thms;

fun mk_unfold_thms maps setss rels = {map_unfolds = maps, set_unfoldss = setss, rel_unfolds = rels};

val empty_unfold = mk_unfold_thms [] [] [];

fun add_to_unfold_opt map_opt sets_opt rel_opt
  {map_unfolds = maps, set_unfoldss = setss, rel_unfolds = rels} = {
    map_unfolds = add_to_thms maps map_opt,
    set_unfoldss = adds_to_thms setss sets_opt,
    rel_unfolds = add_to_thms rels rel_opt};

fun add_to_unfold map sets rel = add_to_unfold_opt (SOME map) (SOME sets) (SOME rel);

val map_unfolds_of = #map_unfolds;
val set_unfoldss_of = #set_unfoldss;
val rel_unfolds_of = #rel_unfolds;

val bdTN = "bdT";

fun mk_killN n = "_kill" ^ string_of_int n;
fun mk_liftN n = "_lift" ^ string_of_int n;
fun mk_permuteN src dest =
  "_permute_" ^ implode (map string_of_int src) ^ "_" ^ implode (map string_of_int dest);

val subst_rel_def = @{thm subst_rel_def};

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

    val ((((fs', Rs'), Asets), xs), _(*names_lthy*)) = lthy
      |> apfst snd o mk_Frees' "f" (map2 (curry (op -->)) As Bs)
      ||>> apfst snd o mk_Frees' "R" (map2 (curry mk_relT) As Bs)
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
        map2 (fn Ds => (fn f => Term.list_comb (f, map Bound ((ilive - 1) downto 0))) o
          mk_map_of_bnf Ds As Bs) Dss inners));
    (*%R1 ... Rn. outer.rel (inner_1.rel R1 ... Rn) ... (inner_m.rel R1 ... Rn)*)
    val rel = fold_rev Term.abs Rs'
      (Term.list_comb (mk_rel_of_bnf oDs CAs CBs outer,
        map2 (fn Ds => (fn f => Term.list_comb (f, map Bound ((ilive - 1) downto 0))) o
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
    val bd = Term.absdummy CCA (mk_cprod (Library.foldr1 (uncurry mk_csum) inner_bds) outer_bd);

    fun map_id_tac {context = ctxt, ...} =
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

    fun map_comp_tac _ =
      mk_comp_map_comp_tac (map_comp_of_bnf outer) (map_cong_of_bnf outer)
        (map map_comp_of_bnf inners);

    fun mk_single_set_natural_tac i _ =
      mk_comp_set_natural_tac (map_comp_of_bnf outer) (map_cong_of_bnf outer)
        (collect_set_natural_of_bnf outer)
        (map ((fn thms => nth thms i) o set_natural_of_bnf) inners);

    val set_natural_tacs = map mk_single_set_natural_tac (0 upto ilive - 1);

    fun bd_card_order_tac _ =
      mk_comp_bd_card_order_tac (map bd_card_order_of_bnf inners) (bd_card_order_of_bnf outer);

    fun bd_cinfinite_tac _ =
      mk_comp_bd_cinfinite_tac (bd_cinfinite_of_bnf inner) (bd_cinfinite_of_bnf outer);

    val set_alt_thms =
      if ! quick_and_dirty then
        []
      else
        map (fn goal =>
          Skip_Proof.prove lthy [] [] goal
            (fn {context, ...} => (mk_comp_set_alt_tac context (collect_set_natural_of_bnf outer)))
          |> Thm.close_derivation)
        (map2 (curry (HOLogic.mk_Trueprop o HOLogic.mk_eq)) sets sets_alt);

    fun map_cong_tac _ =
      mk_comp_map_cong_tac set_alt_thms (map_cong_of_bnf outer) (map map_cong_of_bnf inners);

    val set_bd_tacs =
      if ! quick_and_dirty then
        replicate (length set_alt_thms) (K all_tac)
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
          map2 (fn set_alt => fn single_set_bds => fn {context, ...} =>
            mk_comp_set_bd_tac context set_alt single_set_bds)
          set_alt_thms single_set_bd_thmss
        end;

    val in_alt_thm =
      let
        val inx = mk_in Asets sets CCA;
        val in_alt = mk_in (map2 (mk_in Asets) inner_setss CAs) outer_sets CCA;
        val goal = fold_rev Logic.all Asets (mk_Trueprop_eq (inx, in_alt));
      in
        Skip_Proof.prove lthy [] [] goal
          (fn {context, ...} => mk_comp_in_alt_tac context set_alt_thms)
        |> Thm.close_derivation
      end;

    fun in_bd_tac _ =
      mk_comp_in_bd_tac in_alt_thm (map in_bd_of_bnf inners) (in_bd_of_bnf outer)
        (map bd_Cinfinite_of_bnf inners) (bd_Card_order_of_bnf outer);

    fun map_wpull_tac _ =
      mk_map_wpull_tac in_alt_thm (map map_wpull_of_bnf inners) (map_wpull_of_bnf outer);

    fun rel_O_Gr_tac _ =
      let
        val outer_rel_Gr = rel_Gr_of_bnf outer RS sym;
        val outer_rel_cong = rel_cong_of_bnf outer;
      in
        rtac (trans OF [in_alt_thm RS subst_rel_def,
                trans OF [@{thm arg_cong2[of _ _ _ _ relcomp]} OF
                  [trans OF [outer_rel_Gr RS @{thm arg_cong[of _ _ converse]},
                    rel_converse_of_bnf outer RS sym], outer_rel_Gr],
                  trans OF [rel_O_of_bnf outer RS sym, outer_rel_cong OF
                    (map (fn bnf => rel_O_Gr_of_bnf bnf RS sym) inners)]]] RS sym) 1
      end

    val tacs = zip_goals map_id_tac map_comp_tac map_cong_tac set_natural_tacs bd_card_order_tac
      bd_cinfinite_tac set_bd_tacs in_bd_tac map_wpull_tac rel_O_Gr_tac;

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

    fun wit_tac {context = ctxt, ...} =
      mk_comp_wit_tac ctxt (wit_thms_of_bnf outer) (collect_set_natural_of_bnf outer)
        (maps wit_thms_of_bnf inners);

    val (bnf', lthy') =
      bnf_def const_policy (K Derive_Some_Facts) qualify tacs wit_tac (SOME (oDs @ flat Dss))
        (((((b, mapx), sets), bd), wits), SOME rel) lthy;

    val unfold' = add_to_unfold (map_def_of_bnf bnf') (set_defs_of_bnf bnf') (rel_def_of_bnf bnf')
      unfold;
  in
    (bnf', (unfold', lthy'))
  end;

(* Killing live variables *)

fun kill_bnf qualify n bnf (unfold, lthy) = if n = 0 then (bnf, (unfold, lthy)) else
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
    (*bnf.rel Id ... Id*)
    val rel = Term.list_comb (mk_rel_of_bnf Ds As Bs bnf, map Id_const killedAs);

    val bnf_sets = mk_sets_of_bnf (replicate live Ds) (replicate live As) bnf;
    val sets = drop n bnf_sets;

    (*(|UNIV :: A1 set| +c ... +c |UNIV :: An set|) *c bnf.bd*)
    val bnf_bd = mk_bd_of_bnf Ds As bnf;
    val bd = mk_cprod
      (Library.foldr1 (uncurry mk_csum) (map (mk_card_of o HOLogic.mk_UNIV) killedAs)) bnf_bd;

    fun map_id_tac _ = rtac (map_id_of_bnf bnf) 1;
    fun map_comp_tac {context, ...} =
      Local_Defs.unfold_tac context ((map_comp_of_bnf bnf RS sym) :: @{thms o_assoc id_o o_id}) THEN
      rtac refl 1;
    fun map_cong_tac {context, ...} =
      mk_kill_map_cong_tac context n (live - n) (map_cong_of_bnf bnf);
    val set_natural_tacs = map (fn thm => fn _ => rtac thm 1) (drop n (set_natural_of_bnf bnf));
    fun bd_card_order_tac _ = mk_kill_bd_card_order_tac n (bd_card_order_of_bnf bnf);
    fun bd_cinfinite_tac _ = mk_kill_bd_cinfinite_tac (bd_Cinfinite_of_bnf bnf);
    val set_bd_tacs =
      map (fn thm => fn _ => mk_kill_set_bd_tac (bd_Card_order_of_bnf bnf) thm)
        (drop n (set_bd_of_bnf bnf));

    val in_alt_thm =
      let
        val inx = mk_in Asets sets T;
        val in_alt = mk_in (map HOLogic.mk_UNIV killedAs @ Asets) bnf_sets T;
        val goal = fold_rev Logic.all Asets (mk_Trueprop_eq (inx, in_alt));
      in
        Skip_Proof.prove lthy [] [] goal (K kill_in_alt_tac) |> Thm.close_derivation
      end;

    fun in_bd_tac _ =
      mk_kill_in_bd_tac n (live > n) in_alt_thm (in_bd_of_bnf bnf) (bd_Card_order_of_bnf bnf)
        (bd_Cinfinite_of_bnf bnf) (bd_Cnotzero_of_bnf bnf);
    fun map_wpull_tac _ = mk_map_wpull_tac in_alt_thm [] (map_wpull_of_bnf bnf);

    fun rel_O_Gr_tac _ =
      let
        val rel_Gr = rel_Gr_of_bnf bnf RS sym
      in
        rtac (trans OF [in_alt_thm RS subst_rel_def,
                trans OF [@{thm arg_cong2[of _ _ _ _ relcomp]} OF
                  [trans OF [rel_Gr RS @{thm arg_cong[of _ _ converse]},
                    rel_converse_of_bnf bnf RS sym], rel_Gr],
                  trans OF [rel_O_of_bnf bnf RS sym, rel_cong_of_bnf bnf OF
                    (replicate n @{thm trans[OF Gr_UNIV_id[OF refl] Id_alt[symmetric]]} @
                     replicate (live - n) @{thm Gr_fst_snd})]]] RS sym) 1
      end;

    val tacs = zip_goals map_id_tac map_comp_tac map_cong_tac set_natural_tacs bd_card_order_tac
      bd_cinfinite_tac set_bd_tacs in_bd_tac map_wpull_tac rel_O_Gr_tac;

    val bnf_wits = mk_wits_of_bnf (replicate nwits Ds) (replicate nwits As) bnf;

    val wits = map (fn t => fold absfree (Term.add_frees t []) t)
      (map (fn (I, wit) => Term.list_comb (wit, map (nth xs) I)) bnf_wits);

    fun wit_tac _ = mk_simple_wit_tac (wit_thms_of_bnf bnf);

    val (bnf', lthy') =
      bnf_def Smart_Inline (K Derive_Some_Facts) qualify tacs wit_tac (SOME (killedAs @ Ds))
        (((((b, mapx), sets), Term.absdummy T bd), wits), SOME rel) lthy;

    val unfold' = add_to_unfold (map_def_of_bnf bnf') (set_defs_of_bnf bnf') (rel_def_of_bnf bnf')
      unfold;
  in
    (bnf', (unfold', lthy'))
  end;

(* Adding dummy live variables *)

fun lift_bnf qualify n bnf (unfold, lthy) = if n = 0 then (bnf, (unfold, lthy)) else
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
      fold_rev Term.absdummy (map2 (curry (op -->)) newAs newBs) (mk_map_of_bnf Ds As Bs bnf);
    (*%R1 ... Rn. bnf.rel*)
    val rel =
      fold_rev Term.absdummy (map2 (curry mk_relT) newAs newBs) (mk_rel_of_bnf Ds As Bs bnf);

    val bnf_sets = mk_sets_of_bnf (replicate live Ds) (replicate live As) bnf;
    val sets = map (fn A => absdummy T (HOLogic.mk_set A [])) newAs @ bnf_sets;

    val bd = mk_bd_of_bnf Ds As bnf;

    fun map_id_tac _ = rtac (map_id_of_bnf bnf) 1;
    fun map_comp_tac {context, ...} =
      Local_Defs.unfold_tac context ((map_comp_of_bnf bnf RS sym) :: @{thms o_assoc id_o o_id}) THEN
      rtac refl 1;
    fun map_cong_tac {context, ...} =
      rtac (map_cong_of_bnf bnf) 1 THEN REPEAT_DETERM_N live (Goal.assume_rule_tac context 1);
    val set_natural_tacs =
      if ! quick_and_dirty then
        replicate (n + live) (K all_tac)
      else
        replicate n (K empty_natural_tac) @
        map (fn thm => fn _ => rtac thm 1) (set_natural_of_bnf bnf);
    fun bd_card_order_tac _ = rtac (bd_card_order_of_bnf bnf) 1;
    fun bd_cinfinite_tac _ = rtac (bd_cinfinite_of_bnf bnf) 1;
    val set_bd_tacs =
      if ! quick_and_dirty then
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
        Skip_Proof.prove lthy [] [] goal (K lift_in_alt_tac) |> Thm.close_derivation
      end;

    fun in_bd_tac _ = mk_lift_in_bd_tac n in_alt_thm (in_bd_of_bnf bnf) (bd_Card_order_of_bnf bnf);
    fun map_wpull_tac _ = mk_map_wpull_tac in_alt_thm [] (map_wpull_of_bnf bnf);

    fun rel_O_Gr_tac _ =
      rtac (trans OF [rel_O_Gr_of_bnf bnf, in_alt_thm RS subst_rel_def RS sym]) 1;

    val tacs = zip_goals map_id_tac map_comp_tac map_cong_tac set_natural_tacs bd_card_order_tac
      bd_cinfinite_tac set_bd_tacs in_bd_tac map_wpull_tac rel_O_Gr_tac;

    val wits = map snd (mk_wits_of_bnf (replicate nwits Ds) (replicate nwits As) bnf);

    fun wit_tac _ = mk_simple_wit_tac (wit_thms_of_bnf bnf);

    val (bnf', lthy') =
      bnf_def Smart_Inline (K Derive_Some_Facts) qualify tacs wit_tac (SOME Ds)
        (((((b, mapx), sets), Term.absdummy T bd), wits), SOME rel) lthy;

    val unfold' = add_to_unfold (map_def_of_bnf bnf') (set_defs_of_bnf bnf') (rel_def_of_bnf bnf')
      unfold;
  in
    (bnf', (unfold', lthy'))
  end;

(* Changing the order of live variables *)

fun permute_bnf qualify src dest bnf (unfold, lthy) = if src = dest then (bnf, (unfold, lthy)) else
  let
    val b = Binding.suffix_name (mk_permuteN src dest) (name_of_bnf bnf);
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
      |> mk_Frees "A" (map HOLogic.mk_setT (permute As));

    val T = mk_T_of_bnf Ds As bnf;

    (*%f(1) ... f(n). bnf.map f\<sigma>(1) ... f\<sigma>(n)*)
    val mapx = fold_rev Term.absdummy (permute (map2 (curry op -->) As Bs))
      (Term.list_comb (mk_map_of_bnf Ds As Bs bnf, permute_rev (map Bound ((live - 1) downto 0))));
    (*%R(1) ... R(n). bnf.rel R\<sigma>(1) ... R\<sigma>(n)*)
    val rel = fold_rev Term.absdummy (permute (map2 (curry mk_relT) As Bs))
      (Term.list_comb (mk_rel_of_bnf Ds As Bs bnf, permute_rev (map Bound ((live - 1) downto 0))));

    val bnf_sets = mk_sets_of_bnf (replicate live Ds) (replicate live As) bnf;
    val sets = permute bnf_sets;

    val bd = mk_bd_of_bnf Ds As bnf;

    fun map_id_tac _ = rtac (map_id_of_bnf bnf) 1;
    fun map_comp_tac _ = rtac (map_comp_of_bnf bnf) 1;
    fun map_cong_tac {context, ...} =
      rtac (map_cong_of_bnf bnf) 1 THEN REPEAT_DETERM_N live (Goal.assume_rule_tac context 1);
    val set_natural_tacs = permute (map (fn thm => fn _ => rtac thm 1) (set_natural_of_bnf bnf));
    fun bd_card_order_tac _ = rtac (bd_card_order_of_bnf bnf) 1;
    fun bd_cinfinite_tac _ = rtac (bd_cinfinite_of_bnf bnf) 1;
    val set_bd_tacs = permute (map (fn thm => fn _ => rtac thm 1) (set_bd_of_bnf bnf));

    val in_alt_thm =
      let
        val inx = mk_in Asets sets T;
        val in_alt = mk_in (permute_rev Asets) bnf_sets T;
        val goal = fold_rev Logic.all Asets (mk_Trueprop_eq (inx, in_alt));
      in
        Skip_Proof.prove lthy [] [] goal (K (mk_permute_in_alt_tac src dest))
        |> Thm.close_derivation
      end;

    fun in_bd_tac _ =
      mk_permute_in_bd_tac src dest in_alt_thm (in_bd_of_bnf bnf) (bd_Card_order_of_bnf bnf);
    fun map_wpull_tac _ = mk_map_wpull_tac in_alt_thm [] (map_wpull_of_bnf bnf);

    fun rel_O_Gr_tac _ =
      rtac (trans OF [rel_O_Gr_of_bnf bnf, in_alt_thm RS subst_rel_def RS sym]) 1;

    val tacs = zip_goals map_id_tac map_comp_tac map_cong_tac set_natural_tacs bd_card_order_tac
      bd_cinfinite_tac set_bd_tacs in_bd_tac map_wpull_tac rel_O_Gr_tac;

    val wits = map snd (mk_wits_of_bnf (replicate nwits Ds) (replicate nwits As) bnf);

    fun wit_tac _ = mk_simple_wit_tac (wit_thms_of_bnf bnf);

    val (bnf', lthy') =
      bnf_def Smart_Inline (K Derive_Some_Facts) qualify tacs wit_tac (SOME Ds)
        (((((b, mapx), sets), Term.absdummy T bd), wits), SOME rel) lthy;

    val unfold' = add_to_unfold (map_def_of_bnf bnf') (set_defs_of_bnf bnf') (rel_def_of_bnf bnf')
      unfold;
  in
    (bnf', (unfold', lthy'))
  end;

(* Composition pipeline *)

fun permute_and_kill qualify n src dest bnf =
  bnf
  |> permute_bnf qualify src dest
  #> uncurry (kill_bnf qualify n);

fun lift_and_permute qualify n src dest bnf =
  bnf
  |> lift_bnf qualify n
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

fun compose_bnf const_policy qualify sort outer inners oDs Dss tfreess (unfold, lthy) =
  let
    val b = name_of_bnf outer;

    val Ass = map (map Term.dest_TFree) tfreess;
    val Ds = fold (fold Term.add_tfreesT) (oDs :: Dss) [];

    val ((kill_poss, As), (inners', (unfold', lthy'))) =
      normalize_bnfs qualify Ass Ds sort inners unfold lthy;

    val Ds = oDs @ flat (map3 (append oo map o nth) tfreess kill_poss Dss);
    val As = map TFree As;
  in
    apfst (rpair (Ds, As))
      (clean_compose_bnf const_policy (qualify 0) b outer inners' (unfold', lthy'))
  end;

(* Hide the type of the bound (optimization) and unfold the definitions (nicer to the user) *)

fun seal_bnf unfold b Ds bnf lthy =
  let
    val live = live_of_bnf bnf;
    val nwits = nwits_of_bnf bnf;

    val (As, lthy1) = apfst (map TFree)
      (Variable.invent_types (replicate live HOLogic.typeS) (fold Variable.declare_typ Ds lthy));
    val (Bs, _) = apfst (map TFree)
      (Variable.invent_types (replicate live HOLogic.typeS) lthy1);

    val map_unfolds = filter_out_refl (map_unfolds_of unfold);
    val set_unfoldss = map filter_out_refl (set_unfoldss_of unfold);
    val rel_unfolds = filter_out_refl (rel_unfolds_of unfold);

    val expand_maps = fold expand_term_const (map (single o Logic.dest_equals o Thm.prop_of)
      map_unfolds);
    val expand_sets = fold expand_term_const (map (map (Logic.dest_equals o Thm.prop_of))
      set_unfoldss);
    val expand_rels = fold expand_term_const (map (single o Logic.dest_equals o Thm.prop_of)
      rel_unfolds);
    val unfold_maps = fold (Local_Defs.unfold lthy o single) map_unfolds;
    val unfold_sets = fold (Local_Defs.unfold lthy) set_unfoldss;
    val unfold_defs = unfold_sets o unfold_maps;
    val bnf_map = expand_maps (mk_map_of_bnf Ds As Bs bnf);
    val bnf_sets = map (expand_maps o expand_sets)
      (mk_sets_of_bnf (replicate live Ds) (replicate live As) bnf);
    val bnf_bd = mk_bd_of_bnf Ds As bnf;
    val bnf_rel = expand_rels (mk_rel_of_bnf Ds As Bs bnf);
    val T = mk_T_of_bnf Ds As bnf;

    (*bd should only depend on dead type variables!*)
    val bd_repT = fst (dest_relT (fastype_of bnf_bd));
    val bdT_bind = Binding.suffix_name ("_" ^ bdTN) b;
    val params = fold Term.add_tfreesT Ds [];
    val deads = map TFree params;

    val ((bdT_name, (bdT_glob_info, bdT_loc_info)), lthy) =
      typedef false NONE (bdT_bind, params, NoSyn)
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

    val set_bds =
      map (fn thm => @{thm ordLeq_ordIso_trans} OF [thm, bd_ordIso]) (set_bd_of_bnf bnf);
    val in_bd =
      @{thm ordLeq_ordIso_trans} OF [in_bd_of_bnf bnf,
        @{thm cexp_cong2_Cnotzero} OF [bd_ordIso, if live = 0 then
          @{thm ctwo_Cnotzero} else @{thm ctwo_Cnotzero} RS @{thm csum_Cnotzero2},
            bd_Card_order_of_bnf bnf]];

    fun mk_tac thm {context = ctxt, prems = _} = (rtac (unfold_defs thm) THEN'
      SOLVE o REPEAT_DETERM o (atac ORELSE' Goal.assume_rule_tac ctxt)) 1;

    val tacs = zip_goals (mk_tac (map_id_of_bnf bnf)) (mk_tac (map_comp_of_bnf bnf))
      (mk_tac (map_cong_of_bnf bnf)) (map mk_tac (set_natural_of_bnf bnf))
      (K (rtac bd_card_order 1)) (K (rtac bd_cinfinite 1)) (map mk_tac set_bds) (mk_tac in_bd)
      (mk_tac (map_wpull_of_bnf bnf)) (mk_tac (rel_O_Gr_of_bnf bnf));

    val bnf_wits = map snd (mk_wits_of_bnf (replicate nwits Ds) (replicate nwits As) bnf);

    fun wit_tac _ = mk_simple_wit_tac (map unfold_defs (wit_thms_of_bnf bnf));

    val policy = user_policy Derive_All_Facts;

    val (bnf', lthy') = bnf_def Hardly_Inline policy I tacs wit_tac (SOME deads)
      (((((b, bnf_map), bnf_sets), Term.absdummy T bnf_bd'), bnf_wits), SOME bnf_rel) lthy;
  in
    ((bnf', deads), lthy')
  end;

val ID_bnf = the (bnf_of @{context} "Basic_BNFs.ID");
val DEADID_bnf = the (bnf_of @{context} "Basic_BNFs.DEADID");

fun bnf_of_typ _ _ _ (T as TFree _) accum = ((ID_bnf, ([], [T])), accum)
  | bnf_of_typ _ _ _ (TVar _) _ = error "Unexpected schematic variable"
  | bnf_of_typ const_policy qualify' sort (T as Type (C, Ts)) (unfold, lthy) =
    let
      val tfrees = Term.add_tfreesT T [];
      val bnf_opt = if null tfrees then NONE else bnf_of lthy C;
    in
      (case bnf_opt of
        NONE => ((DEADID_bnf, ([T], [])), (unfold, lthy))
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
          in ((bnf, deads_lives), (unfold, lthy)) end
        else
          let
            val name = Long_Name.base_name C;
            fun qualify i =
              let val namei = name ^ nonzero_string_of_int i;
              in qualify' o Binding.qualify true namei end;
            val odead = dead_of_bnf bnf;
            val olive = live_of_bnf bnf;
            val oDs_pos = find_indices [TFree ("dead", [])] (snd (Term.dest_Type
              (mk_T_of_bnf (replicate odead (TFree ("dead", []))) (replicate olive dummyT) bnf)));
            val oDs = map (nth Ts) oDs_pos;
            val Ts' = map (nth Ts) (subtract (op =) oDs_pos (0 upto length Ts - 1));
            val ((inners, (Dss, Ass)), (unfold', lthy')) =
              apfst (apsnd split_list o split_list)
                (fold_map2 (fn i => bnf_of_typ Smart_Inline (qualify i) sort)
                (if length Ts' = 1 then [0] else (1 upto length Ts')) Ts' (unfold, lthy));
          in
            compose_bnf const_policy qualify sort bnf inners oDs Dss Ass (unfold', lthy')
          end)
    end;

end;
