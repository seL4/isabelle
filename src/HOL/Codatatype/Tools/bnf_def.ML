(*  Title:      HOL/Codatatype/Tools/bnf_def.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Definition of bounded natural functors.
*)

signature BNF_DEF =
sig
  type BNF
  type nonemptiness_witness = {I: int list, wit: term, prop: thm list}

  val bnf_of: Proof.context -> string -> BNF option
  val register_bnf: string -> (BNF * local_theory) -> (BNF * local_theory)

  val name_of_bnf: BNF -> binding
  val T_of_bnf: BNF -> typ
  val live_of_bnf: BNF -> int
  val lives_of_bnf: BNF -> typ list
  val dead_of_bnf: BNF -> int
  val deads_of_bnf: BNF -> typ list
  val nwits_of_bnf: BNF -> int

  val mapN: string
  val setN: string
  val predN: string
  val relN: string
  val mk_setN: int -> string

  val map_of_bnf: BNF -> term

  val mk_T_of_bnf: typ list -> typ list -> BNF -> typ
  val mk_bd_of_bnf: typ list -> typ list -> BNF -> term
  val mk_map_of_bnf: typ list -> typ list -> typ list -> BNF -> term
  val mk_pred_of_bnf: typ list -> typ list -> typ list -> BNF -> term
  val mk_rel_of_bnf: typ list -> typ list -> typ list -> BNF -> term
  val mk_sets_of_bnf: typ list list -> typ list list -> BNF -> term list
  val mk_wits_of_bnf: typ list list -> typ list list -> BNF -> (int list * term) list

  val bd_Card_order_of_bnf: BNF -> thm
  val bd_Cinfinite_of_bnf: BNF -> thm
  val bd_Cnotzero_of_bnf: BNF -> thm
  val bd_card_order_of_bnf: BNF -> thm
  val bd_cinfinite_of_bnf: BNF -> thm
  val collect_set_natural_of_bnf: BNF -> thm
  val in_bd_of_bnf: BNF -> thm
  val in_cong_of_bnf: BNF -> thm
  val in_mono_of_bnf: BNF -> thm
  val in_rel_of_bnf: BNF -> thm
  val map_comp'_of_bnf: BNF -> thm
  val map_comp_of_bnf: BNF -> thm
  val map_cong_of_bnf: BNF -> thm
  val map_def_of_bnf: BNF -> thm
  val map_id'_of_bnf: BNF -> thm
  val map_id_of_bnf: BNF -> thm
  val map_wppull_of_bnf: BNF -> thm
  val map_wpull_of_bnf: BNF -> thm
  val pred_def_of_bnf: BNF -> thm
  val rel_def_of_bnf: BNF -> thm
  val rel_Gr_of_bnf: BNF -> thm
  val rel_Id_of_bnf: BNF -> thm
  val rel_O_of_bnf: BNF -> thm
  val rel_O_Gr_of_bnf: BNF -> thm
  val rel_cong_of_bnf: BNF -> thm
  val rel_converse_of_bnf: BNF -> thm
  val rel_mono_of_bnf: BNF -> thm
  val set_bd_of_bnf: BNF -> thm list
  val set_defs_of_bnf: BNF -> thm list
  val set_natural'_of_bnf: BNF -> thm list
  val set_natural_of_bnf: BNF -> thm list
  val sets_of_bnf: BNF -> term list
  val wit_thms_of_bnf: BNF -> thm list
  val wit_thmss_of_bnf: BNF -> thm list list

  val mk_witness: int list * term -> thm list -> nonemptiness_witness
  val minimize_wits: (''a list * 'b) list -> (''a list * 'b) list
  val wits_of_bnf: BNF -> nonemptiness_witness list

  val zip_axioms: 'a -> 'a -> 'a -> 'a list -> 'a -> 'a -> 'a list -> 'a -> 'a -> 'a -> 'a list

  datatype const_policy = Dont_Inline | Hardly_Inline | Smart_Inline | Do_Inline
  datatype fact_policy =
    Derive_Few_Facts | Derive_All_Facts | Derive_All_Facts_Note_Most | Note_All_Facts_and_Axioms
  val bnf_note_all: bool Config.T
  val user_policy: fact_policy -> Proof.context -> fact_policy

  val print_bnfs: Proof.context -> unit
  val bnf_def: const_policy -> (Proof.context -> fact_policy) -> (binding -> binding) ->
    ({prems: thm list, context: Proof.context} -> tactic) list ->
    ({prems: thm list, context: Proof.context} -> tactic) -> typ list option ->
    ((((binding * term) * term list) * term) * term list) * term option -> local_theory ->
    BNF * local_theory
end;

structure BNF_Def : BNF_DEF =
struct

open BNF_Util
open BNF_Tactics
open BNF_Def_Tactics

type axioms = {
  map_id: thm,
  map_comp: thm,
  map_cong: thm,
  set_natural: thm list,
  bd_card_order: thm,
  bd_cinfinite: thm,
  set_bd: thm list,
  in_bd: thm,
  map_wpull: thm,
  rel_O_Gr: thm
};

fun mk_axioms' (((((((((id, comp), cong), nat), c_o), cinf), set_bd), in_bd), wpull), rel) =
  {map_id = id, map_comp = comp, map_cong = cong, set_natural = nat, bd_card_order = c_o,
   bd_cinfinite = cinf, set_bd = set_bd, in_bd = in_bd, map_wpull = wpull, rel_O_Gr = rel};

fun dest_cons [] = raise Empty
  | dest_cons (x :: xs) = (x, xs);

fun mk_axioms n thms = thms
  |> map the_single
  |> dest_cons
  ||>> dest_cons
  ||>> dest_cons
  ||>> chop n
  ||>> dest_cons
  ||>> dest_cons
  ||>> chop n
  ||>> dest_cons
  ||>> dest_cons
  ||> the_single
  |> mk_axioms';

fun zip_axioms mid mcomp mcong snat bdco bdinf sbd inbd wpull rel =
  [mid, mcomp, mcong] @ snat @ [bdco, bdinf] @ sbd @ [inbd, wpull, rel];

fun dest_axioms {map_id, map_comp, map_cong, set_natural, bd_card_order, bd_cinfinite, set_bd,
  in_bd, map_wpull, rel_O_Gr} =
  zip_axioms map_id map_comp map_cong set_natural bd_card_order bd_cinfinite set_bd in_bd map_wpull
    rel_O_Gr;

fun map_axioms f {map_id, map_comp, map_cong, set_natural, bd_card_order, bd_cinfinite, set_bd,
  in_bd, map_wpull, rel_O_Gr} =
  {map_id = f map_id,
    map_comp = f map_comp,
    map_cong = f map_cong,
    set_natural = map f set_natural,
    bd_card_order = f bd_card_order,
    bd_cinfinite = f bd_cinfinite,
    set_bd = map f set_bd,
    in_bd = f in_bd,
    map_wpull = f map_wpull,
    rel_O_Gr = f rel_O_Gr};

val morph_axioms = map_axioms o Morphism.thm;

type defs = {
  map_def: thm,
  set_defs: thm list,
  pred_def: thm,
  rel_def: thm
}

fun mk_defs map sets pred rel = {map_def = map, set_defs = sets, pred_def = pred, rel_def = rel};

fun map_defs f {map_def, set_defs, pred_def, rel_def} =
  {map_def = f map_def, set_defs = map f set_defs, pred_def = f pred_def, rel_def = f rel_def};

val morph_defs = map_defs o Morphism.thm;

type facts = {
  bd_Card_order: thm,
  bd_Cinfinite: thm,
  bd_Cnotzero: thm,
  collect_set_natural: thm lazy,
  in_cong: thm lazy,
  in_mono: thm lazy,
  in_rel: thm lazy,
  map_comp': thm lazy,
  map_id': thm lazy,
  map_wppull: thm lazy,
  rel_cong: thm lazy,
  rel_mono: thm lazy,
  rel_Id: thm lazy,
  rel_Gr: thm lazy,
  rel_converse: thm lazy,
  rel_O: thm lazy,
  set_natural': thm lazy list
};

fun mk_facts bd_Card_order bd_Cinfinite bd_Cnotzero
    collect_set_natural in_cong in_mono in_rel map_comp' map_id' map_wppull
    rel_cong rel_mono rel_Id rel_Gr rel_converse rel_O set_natural' = {
  bd_Card_order = bd_Card_order,
  bd_Cinfinite = bd_Cinfinite,
  bd_Cnotzero = bd_Cnotzero,
  collect_set_natural = collect_set_natural,
  in_cong = in_cong,
  in_mono = in_mono,
  in_rel = in_rel,
  map_comp' = map_comp',
  map_id' = map_id',
  map_wppull = map_wppull,
  rel_cong = rel_cong,
  rel_mono = rel_mono,
  rel_Id = rel_Id,
  rel_Gr = rel_Gr,
  rel_converse = rel_converse,
  rel_O = rel_O,
  set_natural' = set_natural'};

fun map_facts f {
  bd_Card_order,
  bd_Cinfinite,
  bd_Cnotzero,
  collect_set_natural,
  in_cong,
  in_mono,
  in_rel,
  map_comp',
  map_id',
  map_wppull,
  rel_cong,
  rel_mono,
  rel_Id,
  rel_Gr,
  rel_converse,
  rel_O,
  set_natural'} =
  {bd_Card_order = f bd_Card_order,
    bd_Cinfinite = f bd_Cinfinite,
    bd_Cnotzero = f bd_Cnotzero,
    collect_set_natural = Lazy.map f collect_set_natural,
    in_cong = Lazy.map f in_cong,
    in_mono = Lazy.map f in_mono,
    in_rel = Lazy.map f in_rel,
    map_comp' = Lazy.map f map_comp',
    map_id' = Lazy.map f map_id',
    map_wppull = Lazy.map f map_wppull,
    rel_cong = Lazy.map f rel_cong,
    rel_mono = Lazy.map f rel_mono,
    rel_Id = Lazy.map f rel_Id,
    rel_Gr = Lazy.map f rel_Gr,
    rel_converse = Lazy.map f rel_converse,
    rel_O = Lazy.map f rel_O,
    set_natural' = map (Lazy.map f) set_natural'};

val morph_facts = map_facts o Morphism.thm;

type nonemptiness_witness = {
  I: int list,
  wit: term,
  prop: thm list
};

fun mk_witness (I, wit) prop = {I = I, wit = wit, prop = prop};
fun map_witness f g {I, wit, prop} = {I = I, wit = f wit, prop = map g prop};
fun morph_witness phi = map_witness (Morphism.term phi) (Morphism.thm phi);

datatype BNF = BNF of {
  name: binding,
  T: typ,
  live: int,
  lives: typ list, (*source type variables of map, only for composition*)
  lives': typ list, (*target type variables of map, only for composition*)
  dead: int,
  deads: typ list, (*only for composition*)
  map: term,
  sets: term list,
  bd: term,
  axioms: axioms,
  defs: defs,
  facts: facts,
  nwits: int,
  wits: nonemptiness_witness list,
  pred: term,
  rel: term
};

(* getters *)

fun rep_bnf (BNF bnf) = bnf;
val name_of_bnf = #name o rep_bnf;
val T_of_bnf = #T o rep_bnf;
fun mk_T_of_bnf Ds Ts bnf =
  let val bnf_rep = rep_bnf bnf
  in Term.typ_subst_atomic ((#deads bnf_rep ~~ Ds) @ (#lives bnf_rep ~~ Ts)) (#T bnf_rep) end;
val live_of_bnf = #live o rep_bnf;
val lives_of_bnf = #lives o rep_bnf;
val dead_of_bnf = #dead o rep_bnf;
val deads_of_bnf = #deads o rep_bnf;
val axioms_of_bnf = #axioms o rep_bnf;
val facts_of_bnf = #facts o rep_bnf;
val nwits_of_bnf = #nwits o rep_bnf;
val wits_of_bnf = #wits o rep_bnf;

(*terms*)
val map_of_bnf = #map o rep_bnf;
val sets_of_bnf = #sets o rep_bnf;
fun mk_map_of_bnf Ds Ts Us bnf =
  let val bnf_rep = rep_bnf bnf;
  in
    Term.subst_atomic_types
      ((#deads bnf_rep ~~ Ds) @ (#lives bnf_rep ~~ Ts) @ (#lives' bnf_rep ~~ Us)) (#map bnf_rep)
  end;
fun mk_sets_of_bnf Dss Tss bnf =
  let val bnf_rep = rep_bnf bnf;
  in
    map2 (fn (Ds, Ts) => Term.subst_atomic_types
      ((#deads bnf_rep ~~ Ds) @ (#lives bnf_rep ~~ Ts))) (Dss ~~ Tss) (#sets bnf_rep)
  end;
val bd_of_bnf = #bd o rep_bnf;
fun mk_bd_of_bnf Ds Ts bnf =
  let val bnf_rep = rep_bnf bnf;
  in Term.subst_atomic_types ((#deads bnf_rep ~~ Ds) @ (#lives bnf_rep ~~ Ts)) (#bd bnf_rep) end;
fun mk_wits_of_bnf Dss Tss bnf =
  let
    val bnf_rep = rep_bnf bnf;
    val wits = map (fn x => (#I x, #wit x)) (#wits bnf_rep);
  in
    map2 (fn (Ds, Ts) => apsnd (Term.subst_atomic_types
      ((#deads bnf_rep ~~ Ds) @ (#lives bnf_rep ~~ Ts)))) (Dss ~~ Tss) wits
  end;
val pred_of_bnf = #pred o rep_bnf;
fun mk_pred_of_bnf Ds Ts Us bnf =
  let val bnf_rep = rep_bnf bnf;
  in
    Term.subst_atomic_types
      ((#deads bnf_rep ~~ Ds) @ (#lives bnf_rep ~~ Ts) @ (#lives' bnf_rep ~~ Us)) (#pred bnf_rep)
  end;
val rel_of_bnf = #rel o rep_bnf;
fun mk_rel_of_bnf Ds Ts Us bnf =
  let val bnf_rep = rep_bnf bnf;
  in
    Term.subst_atomic_types
      ((#deads bnf_rep ~~ Ds) @ (#lives bnf_rep ~~ Ts) @ (#lives' bnf_rep ~~ Us)) (#rel bnf_rep)
  end;

(*thms*)
val bd_card_order_of_bnf = #bd_card_order o #axioms o rep_bnf;
val bd_cinfinite_of_bnf = #bd_cinfinite o #axioms o rep_bnf;
val bd_Card_order_of_bnf = #bd_Card_order o #facts o rep_bnf;
val bd_Cinfinite_of_bnf = #bd_Cinfinite o #facts o rep_bnf;
val bd_Cnotzero_of_bnf = #bd_Cnotzero o #facts o rep_bnf;
val collect_set_natural_of_bnf = Lazy.force o #collect_set_natural o #facts o rep_bnf;
val in_bd_of_bnf = #in_bd o #axioms o rep_bnf;
val in_cong_of_bnf = Lazy.force o #in_cong o #facts o rep_bnf;
val in_mono_of_bnf = Lazy.force o #in_mono o #facts o rep_bnf;
val in_rel_of_bnf = Lazy.force o #in_rel o #facts o rep_bnf;
val map_def_of_bnf = #map_def o #defs o rep_bnf;
val map_id_of_bnf = #map_id o #axioms o rep_bnf;
val map_id'_of_bnf = Lazy.force o #map_id' o #facts o rep_bnf;
val map_comp_of_bnf = #map_comp o #axioms o rep_bnf;
val map_comp'_of_bnf = Lazy.force o #map_comp' o #facts o rep_bnf;
val map_cong_of_bnf = #map_cong o #axioms o rep_bnf;
val map_wppull_of_bnf = Lazy.force o #map_wppull o #facts o rep_bnf;
val map_wpull_of_bnf = #map_wpull o #axioms o rep_bnf;
val pred_def_of_bnf = #pred_def o #defs o rep_bnf;
val rel_cong_of_bnf = Lazy.force o #rel_cong o #facts o rep_bnf;
val rel_mono_of_bnf = Lazy.force o #rel_mono o #facts o rep_bnf;
val rel_def_of_bnf = #rel_def o #defs o rep_bnf;
val rel_Id_of_bnf = Lazy.force o #rel_Id o #facts o rep_bnf;
val rel_Gr_of_bnf = Lazy.force o #rel_Gr o #facts o rep_bnf;
val rel_converse_of_bnf = Lazy.force o #rel_converse o #facts o rep_bnf;
val rel_O_of_bnf = Lazy.force o #rel_O o #facts o rep_bnf;
val rel_O_Gr_of_bnf = #rel_O_Gr o #axioms o rep_bnf;
val set_bd_of_bnf = #set_bd o #axioms o rep_bnf;
val set_defs_of_bnf = #set_defs o #defs o rep_bnf;
val set_natural_of_bnf = #set_natural o #axioms o rep_bnf;
val set_natural'_of_bnf = map Lazy.force o #set_natural' o #facts o rep_bnf;
val wit_thms_of_bnf = maps #prop o wits_of_bnf;
val wit_thmss_of_bnf = map #prop o wits_of_bnf;

fun mk_bnf name T live lives lives' dead deads map sets bd axioms defs facts wits pred rel =
  BNF {name = name, T = T,
       live = live, lives = lives, lives' = lives', dead = dead, deads = deads,
       map = map, sets = sets, bd = bd,
       axioms = axioms, defs = defs, facts = facts,
       nwits = length wits, wits = wits, pred = pred, rel = rel};

fun morph_bnf phi (BNF {name = name, T = T, live = live, lives = lives, lives' = lives',
  dead = dead, deads = deads, map = map, sets = sets, bd = bd,
  axioms = axioms, defs = defs, facts = facts,
  nwits = nwits, wits = wits, pred = pred, rel = rel}) =
  BNF {name = Morphism.binding phi name, T = Morphism.typ phi T,
    live = live, lives = List.map (Morphism.typ phi) lives,
    lives' = List.map (Morphism.typ phi) lives',
    dead = dead, deads = List.map (Morphism.typ phi) deads,
    map = Morphism.term phi map, sets = List.map (Morphism.term phi) sets,
    bd = Morphism.term phi bd,
    axioms = morph_axioms phi axioms,
    defs = morph_defs phi defs,
    facts = morph_facts phi facts,
    nwits = nwits,
    wits = List.map (morph_witness phi) wits,
    pred = Morphism.term phi pred, rel = Morphism.term phi rel};

fun eq_bnf (BNF {T = T1, live = live1, dead = dead1, ...},
  BNF {T = T2, live = live2, dead = dead2, ...}) =
  Type.could_unify (T1, T2) andalso live1 = live2 andalso dead1 = dead2;

structure Data = Generic_Data
(
  type T = BNF Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge eq_bnf;
);

val bnf_of = Symtab.lookup o Data.get o Context.Proof;



(* Utilities *)

fun normalize_set insts instA set =
  let
    val (T, T') = dest_funT (fastype_of set);
    val A = fst (Term.dest_TVar (HOLogic.dest_setT T'));
    val params = Term.add_tvar_namesT T [];
  in Term.subst_TVars ((A :: params) ~~ (instA :: insts)) set end;

fun normalize_pred ctxt instTs instA instB pred =
  let
    val thy = Proof_Context.theory_of ctxt;
    val tyenv =
      Sign.typ_match thy (fastype_of pred, Library.foldr (op -->) (instTs, mk_pred2T instA instB))
        Vartab.empty;
  in Envir.subst_term (tyenv, Vartab.empty) pred end
  handle Type.TYPE_MATCH => error "Bad predicator";

fun normalize_rel ctxt instTs instA instB rel =
  let
    val thy = Proof_Context.theory_of ctxt;
    val tyenv =
      Sign.typ_match thy (fastype_of rel, Library.foldr (op -->) (instTs, mk_relT (instA, instB)))
        Vartab.empty;
  in Envir.subst_term (tyenv, Vartab.empty) rel end
  handle Type.TYPE_MATCH => error "Bad relator";

fun normalize_wit insts CA As wit =
  let
    fun strip_param (Ts, T as Type (@{type_name fun}, [T1, T2])) =
        if Type.raw_instance (CA, T) then (Ts, T) else strip_param (T1 :: Ts, T2)
      | strip_param x = x;
    val (Ts, T) = strip_param ([], fastype_of wit);
    val subst = Term.add_tvar_namesT T [] ~~ insts;
    fun find y = find_index (fn x => x = y) As;
  in
    (map (find o Term.typ_subst_TVars subst) (rev Ts), Term.subst_TVars subst wit)
  end;

fun minimize_wits wits =
 let
   fun minimize done [] = done
     | minimize done ((I, wit) :: todo) =
       if exists (fn (J, _) => subset (op =) (J, I)) (done @ todo)
       then minimize done todo
       else minimize ((I, wit) :: done) todo;
 in minimize [] wits end;



(* Names *)

val mapN = "map";
val setN = "set";
fun mk_setN i = setN ^ nonzero_string_of_int i;
val bdN = "bd";
val witN = "wit";
fun mk_witN i = witN ^ nonzero_string_of_int i;
val predN = "pred";
val relN = "rel";

val bd_card_orderN = "bd_card_order";
val bd_cinfiniteN = "bd_cinfinite";
val bd_Card_orderN = "bd_Card_order";
val bd_CinfiniteN = "bd_Cinfinite";
val bd_CnotzeroN = "bd_Cnotzero";
val collect_set_naturalN = "collect_set_natural";
val in_bdN = "in_bd";
val in_monoN = "in_mono";
val in_relN = "in_rel";
val map_idN = "map_id";
val map_id'N = "map_id'";
val map_compN = "map_comp";
val map_comp'N = "map_comp'";
val map_congN = "map_cong";
val map_wpullN = "map_wpull";
val rel_IdN = "rel_Id";
val rel_GrN = "rel_Gr";
val rel_converseN = "rel_converse";
val rel_monoN = "rel_mono"
val rel_ON = "rel_comp";
val rel_O_GrN = "rel_comp_Gr";
val set_naturalN = "set_natural";
val set_natural'N = "set_natural'";
val set_bdN = "set_bd";

datatype const_policy = Dont_Inline | Hardly_Inline | Smart_Inline | Do_Inline;

datatype fact_policy =
  Derive_Few_Facts | Derive_All_Facts | Derive_All_Facts_Note_Most | Note_All_Facts_and_Axioms;

val bnf_note_all = Attrib.setup_config_bool @{binding bnf_note_all} (K false);

fun user_policy policy ctxt =
  if Config.get ctxt bnf_note_all then Note_All_Facts_and_Axioms else policy;

val smart_max_inline_size = 25; (*FUDGE*)


(* Define new BNFs *)

fun prepare_def const_policy mk_fact_policy qualify prep_term Ds_opt
  (((((raw_b, raw_map), raw_sets), raw_bd_Abs), raw_wits), raw_pred_opt) no_defs_lthy =
  let
    val fact_policy = mk_fact_policy no_defs_lthy;
    val b = qualify raw_b;
    val live = length raw_sets;
    val nwits = length raw_wits;

    val map_rhs = prep_term no_defs_lthy raw_map;
    val set_rhss = map (prep_term no_defs_lthy) raw_sets;
    val (bd_rhsT, bd_rhs) = (case prep_term no_defs_lthy raw_bd_Abs of
      Abs (_, T, t) => (T, t)
    | _ => error "Bad bound constant");
    val wit_rhss = map (prep_term no_defs_lthy) raw_wits;

    fun err T =
      error ("Trying to register the type " ^ quote (Syntax.string_of_typ no_defs_lthy T) ^
        " as unnamed BNF");

    val (b, key) =
      if Binding.eq_name (b, Binding.empty) then
        (case bd_rhsT of
          Type (C, Ts) => if forall (is_some o try dest_TFree) Ts
            then (Binding.qualified_name C, C) else err bd_rhsT
        | T => err T)
      else (b, Local_Theory.full_name no_defs_lthy b);

    fun maybe_define user_specified (b, rhs) lthy =
      let
        val inline =
          (user_specified orelse fact_policy = Derive_Few_Facts) andalso
          (case const_policy of
            Dont_Inline => false
          | Hardly_Inline => Term.is_Free rhs orelse Term.is_Const rhs
          | Smart_Inline => Term.size_of_term rhs <= smart_max_inline_size
          | Do_Inline => true)
      in
        if inline then
          ((rhs, Drule.reflexive_thm), lthy)
        else
          let val b = b () in
            apfst (apsnd snd) (Local_Theory.define ((b, NoSyn), ((Thm.def_binding b, []), rhs))
              lthy)
          end
      end;

    fun maybe_restore lthy_old lthy =
      lthy |> not (pointer_eq (lthy_old, lthy)) ? Local_Theory.restore;

    val map_bind_def = (fn () => Binding.suffix_name ("_" ^ mapN) b, map_rhs);
    val set_binds_defs =
      let
        val bs = if live = 1 then [fn () => Binding.suffix_name ("_" ^ setN) b]
          else map (fn i => fn () => Binding.suffix_name ("_" ^ mk_setN i) b) (1 upto live)
      in map2 pair bs set_rhss end;
    val bd_bind_def = (fn () => Binding.suffix_name ("_" ^ bdN) b, bd_rhs);
    val wit_binds_defs =
      let
        val bs = if nwits = 1 then [fn () => Binding.suffix_name ("_" ^ witN) b]
          else map (fn i => fn () => Binding.suffix_name ("_" ^ mk_witN i) b) (1 upto nwits);
      in map2 pair bs wit_rhss end;

    val (((((bnf_map_term, raw_map_def),
      (bnf_set_terms, raw_set_defs)),
      (bnf_bd_term, raw_bd_def)),
      (bnf_wit_terms, raw_wit_defs)), (lthy, lthy_old)) =
        no_defs_lthy
        |> maybe_define true map_bind_def
        ||>> apfst split_list o fold_map (maybe_define true) set_binds_defs
        ||>> maybe_define true bd_bind_def
        ||>> apfst split_list o fold_map (maybe_define true) wit_binds_defs
        ||> `(maybe_restore no_defs_lthy);

    val phi = Proof_Context.export_morphism lthy_old lthy;

    val bnf_map_def = Morphism.thm phi raw_map_def;
    val bnf_set_defs = map (Morphism.thm phi) raw_set_defs;
    val bnf_bd_def = Morphism.thm phi raw_bd_def;
    val bnf_wit_defs = map (Morphism.thm phi) raw_wit_defs;

    val bnf_map = Morphism.term phi bnf_map_term;

    (*TODO: handle errors*)
    (*simple shape analysis of a map function*)
    val ((alphas, betas), (CA, _)) =
      fastype_of bnf_map
      |> strip_typeN live
      |>> map_split dest_funT
      ||> dest_funT
      handle TYPE _ => error "Bad map function";

    val CA_params = map TVar (Term.add_tvarsT CA []);

    val bnf_sets = map2 (normalize_set CA_params) alphas (map (Morphism.term phi) bnf_set_terms);
    val bdT = Morphism.typ phi bd_rhsT;
    val bnf_bd =
      Term.subst_TVars (Term.add_tvar_namesT bdT [] ~~ CA_params) (Morphism.term phi bnf_bd_term);
    val bnf_wits = map (normalize_wit CA_params CA alphas o Morphism.term phi) bnf_wit_terms;

    (*TODO: assert Ds = (TVars of bnf_map) \ (alphas @ betas) as sets*)
    val deads = (case Ds_opt of
      NONE => subtract (op =) (alphas @ betas) (map TVar (Term.add_tvars bnf_map []))
    | SOME Ds => map (Morphism.typ phi) Ds);
    val dead = length deads;

    (*TODO: further checks of type of bnf_map*)
    (*TODO: check types of bnf_sets*)
    (*TODO: check type of bnf_bd*)
    (*TODO: check type of bnf_pred*)

    val ((((((((((As', Bs'), Cs), Ds), B1Ts), B2Ts), domTs), ranTs), ranTs'), ranTs''),
      (Ts, T)) = lthy
      |> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees dead
      ||>> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees live
      ||> fst o mk_TFrees 1
      ||> the_single
      ||> `(replicate live);

    fun mk_bnf_map As' Bs' =
      Term.subst_atomic_types ((deads ~~ Ds) @ (alphas ~~ As') @ (betas ~~ Bs')) bnf_map;
    fun mk_bnf_t As' = Term.subst_atomic_types ((deads ~~ Ds) @ (alphas ~~ As'));
    fun mk_bnf_T As' = Term.typ_subst_atomic ((deads ~~ Ds) @ (alphas ~~ As'));

    val (setRTs, RTs) = map_split (`HOLogic.mk_setT o HOLogic.mk_prodT) (As' ~~ Bs');
    val setRTsAsCs = map (HOLogic.mk_setT o HOLogic.mk_prodT) (As' ~~ Cs);
    val setRTsBsCs = map (HOLogic.mk_setT o HOLogic.mk_prodT) (Bs' ~~ Cs);
    val setRT's = map (HOLogic.mk_setT o HOLogic.mk_prodT) (Bs' ~~ As');
    val self_setRTs = map (HOLogic.mk_setT o HOLogic.mk_prodT) (As' ~~ As');
    val QTs = map2 mk_pred2T As' Bs';

    val CA' = mk_bnf_T As' CA;
    val CB' = mk_bnf_T Bs' CA;
    val CC' = mk_bnf_T Cs CA;
    val CRs' = mk_bnf_T RTs CA;
    val CA'CB' = HOLogic.mk_prodT (CA', CB');

    val bnf_map_AsAs = mk_bnf_map As' As';
    val bnf_map_AsBs = mk_bnf_map As' Bs';
    val bnf_map_AsCs = mk_bnf_map As' Cs;
    val bnf_map_BsCs = mk_bnf_map Bs' Cs;
    val bnf_sets_As = map (mk_bnf_t As') bnf_sets;
    val bnf_sets_Bs = map (mk_bnf_t Bs') bnf_sets;
    val bnf_bd_As = mk_bnf_t As' bnf_bd;
    val bnf_wit_As = map (apsnd (mk_bnf_t As')) bnf_wits;

    val (((((((((((((((((((((((((fs, fs_copy), gs), hs), p), (x, x')), (y, y')), (z, z')), zs), As),
      As_copy), Xs), B1s), B2s), f1s), f2s), e1s), e2s), p1s), p2s), bs), (Rs, Rs')), Rs_copy), Ss),
      (Qs, Qs')), _) = lthy
      |> mk_Frees "f" (map2 (curry (op -->)) As' Bs')
      ||>> mk_Frees "f" (map2 (curry (op -->)) As' Bs')
      ||>> mk_Frees "g" (map2 (curry (op -->)) Bs' Cs)
      ||>> mk_Frees "h" (map2 (curry (op -->)) As' Ts)
      ||>> yield_singleton (mk_Frees "p") CA'CB'
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "x") CA'
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "y") CB'
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "z") CRs'
      ||>> mk_Frees "z" As'
      ||>> mk_Frees "A" (map HOLogic.mk_setT As')
      ||>> mk_Frees "A" (map HOLogic.mk_setT As')
      ||>> mk_Frees "A" (map HOLogic.mk_setT domTs)
      ||>> mk_Frees "B1" (map HOLogic.mk_setT B1Ts)
      ||>> mk_Frees "B2" (map HOLogic.mk_setT B2Ts)
      ||>> mk_Frees "f1" (map2 (curry (op -->)) B1Ts ranTs)
      ||>> mk_Frees "f2" (map2 (curry (op -->)) B2Ts ranTs)
      ||>> mk_Frees "e1" (map2 (curry (op -->)) B1Ts ranTs')
      ||>> mk_Frees "e2" (map2 (curry (op -->)) B2Ts ranTs'')
      ||>> mk_Frees "p1" (map2 (curry (op -->)) domTs B1Ts)
      ||>> mk_Frees "p2" (map2 (curry (op -->)) domTs B2Ts)
      ||>> mk_Frees "b" As'
      ||>> mk_Frees' "R" setRTs
      ||>> mk_Frees "R" setRTs
      ||>> mk_Frees "S" setRTsBsCs
      ||>> mk_Frees' "Q" QTs;

    (*Gr (in R1 .. Rn) (map fst .. fst)^-1 O Gr (in R1 .. Rn) (map snd .. snd)*)
    val O_Gr =
      let
        val map1 = Term.list_comb (mk_bnf_map RTs As', map fst_const RTs);
        val map2 = Term.list_comb (mk_bnf_map RTs Bs', map snd_const RTs);
        val bnf_in = mk_in (map Free Rs') (map (mk_bnf_t RTs) bnf_sets) CRs';
      in
        mk_rel_comp (mk_converse (mk_Gr bnf_in map1), mk_Gr bnf_in map2)
      end;

    fun mk_predicate_of_set x_name y_name t =
      let
        val (T, U) = HOLogic.dest_prodT (HOLogic.dest_setT (fastype_of t));
        val x = Free (x_name, T);
        val y = Free (y_name, U);
      in fold_rev Term.lambda [x, y] (HOLogic.mk_mem (HOLogic.mk_prod (x, y), t)) end;

    val pred_rhs = (case raw_pred_opt of
        NONE =>
        fold_rev absfree Qs' (mk_predicate_of_set (fst x') (fst y')
          (Term.list_comb (fold_rev Term.absfree Rs' O_Gr, map3 (fn Q => fn T => fn U =>
          HOLogic.Collect_const (HOLogic.mk_prodT (T, U)) $ HOLogic.mk_split Q) Qs As' Bs')))
      | SOME raw_pred => prep_term no_defs_lthy raw_pred);

    val pred_bind_def = (fn () => Binding.suffix_name ("_" ^ predN) b, pred_rhs);

    val ((bnf_pred_term, raw_pred_def), (lthy, lthy_old)) =
      lthy
      |> maybe_define (is_some raw_pred_opt) pred_bind_def
      ||> `(maybe_restore lthy);

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val bnf_pred_def = Morphism.thm phi raw_pred_def;
    val bnf_pred = Morphism.term phi bnf_pred_term;

    fun mk_bnf_pred QTs CA' CB' = normalize_pred lthy QTs CA' CB' bnf_pred;

    val pred = mk_bnf_pred QTs CA' CB';

    val rel_rhs =
      fold_rev Term.absfree Rs' (HOLogic.Collect_const CA'CB' $
        Term.lambda p (Term.list_comb (pred, map (mk_predicate_of_set (fst x') (fst y')) Rs) $
        HOLogic.mk_fst p $ HOLogic.mk_snd p));

    val rel_bind_def = (fn () => Binding.suffix_name ("_" ^ relN) b, rel_rhs);

    val ((bnf_rel_term, raw_rel_def), (lthy, lthy_old)) =
      lthy
      |> maybe_define false rel_bind_def
      ||> `(maybe_restore lthy);

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val bnf_rel_def = Morphism.thm phi raw_rel_def;
    val bnf_rel = Morphism.term phi bnf_rel_term;

    fun mk_bnf_rel setRTs CA' CB' = normalize_rel lthy setRTs CA' CB' bnf_rel;

    val rel = mk_bnf_rel setRTs CA' CB';

    val _ = case no_reflexive (raw_map_def :: raw_set_defs @ [raw_bd_def] @
        raw_wit_defs @ [raw_pred_def, raw_rel_def]) of
        [] => ()
      | defs => Proof_Display.print_consts true lthy_old (K false)
          (map (dest_Free o fst o Logic.dest_equals o prop_of) defs);

    val map_id_goal =
      let
        val bnf_map_app_id = Term.list_comb (bnf_map_AsAs, map HOLogic.id_const As');
      in
        HOLogic.mk_Trueprop
          (HOLogic.mk_eq (bnf_map_app_id, HOLogic.id_const CA'))
      end;

    val map_comp_goal =
      let
        val bnf_map_app_comp = Term.list_comb (bnf_map_AsCs, map2 (curry HOLogic.mk_comp) gs fs);
        val comp_bnf_map_app = HOLogic.mk_comp
          (Term.list_comb (bnf_map_BsCs, gs),
           Term.list_comb (bnf_map_AsBs, fs));
      in
        fold_rev Logic.all (fs @ gs) (mk_Trueprop_eq (bnf_map_app_comp, comp_bnf_map_app))
      end;

    val map_cong_goal =
      let
        fun mk_prem z set f f_copy =
          Logic.all z (Logic.mk_implies
            (HOLogic.mk_Trueprop (HOLogic.mk_mem (z, set $ x)),
            mk_Trueprop_eq (f $ z, f_copy $ z)));
        val prems = map4 mk_prem zs bnf_sets_As fs fs_copy;
        val eq = HOLogic.mk_eq (Term.list_comb (bnf_map_AsBs, fs) $ x,
          Term.list_comb (bnf_map_AsBs, fs_copy) $ x);
      in
        fold_rev Logic.all (x :: fs @ fs_copy)
          (Logic.list_implies (prems, HOLogic.mk_Trueprop eq))
      end;

    val set_naturals_goal =
      let
        fun mk_goal setA setB f =
          let
            val set_comp_map =
              HOLogic.mk_comp (setB, Term.list_comb (bnf_map_AsBs, fs));
            val image_comp_set = HOLogic.mk_comp (mk_image f, setA);
          in
            fold_rev Logic.all fs (mk_Trueprop_eq (set_comp_map, image_comp_set))
          end;
      in
        map3 mk_goal bnf_sets_As bnf_sets_Bs fs
      end;

    val card_order_bd_goal = HOLogic.mk_Trueprop (mk_card_order bnf_bd_As);

    val cinfinite_bd_goal = HOLogic.mk_Trueprop (mk_cinfinite bnf_bd_As);

    val set_bds_goal =
      let
        fun mk_goal set =
          Logic.all x (HOLogic.mk_Trueprop (mk_ordLeq (mk_card_of (set $ x)) bnf_bd_As));
      in
        map mk_goal bnf_sets_As
      end;

    val in_bd_goal =
      let
        val bd = mk_cexp
          (if live = 0 then ctwo
            else mk_csum (Library.foldr1 (uncurry mk_csum) (map mk_card_of As)) ctwo)
          bnf_bd_As;
      in
        fold_rev Logic.all As
          (HOLogic.mk_Trueprop (mk_ordLeq (mk_card_of (mk_in As bnf_sets_As CA')) bd))
      end;

    val map_wpull_goal =
      let
        val prems = map HOLogic.mk_Trueprop
          (map8 mk_wpull Xs B1s B2s f1s f2s (replicate live NONE) p1s p2s);
        val CX = mk_bnf_T domTs CA;
        val CB1 = mk_bnf_T B1Ts CA;
        val CB2 = mk_bnf_T B2Ts CA;
        val bnf_sets_CX = map2 (normalize_set (map (mk_bnf_T domTs) CA_params)) domTs bnf_sets;
        val bnf_sets_CB1 = map2 (normalize_set (map (mk_bnf_T B1Ts) CA_params)) B1Ts bnf_sets;
        val bnf_sets_CB2 = map2 (normalize_set (map (mk_bnf_T B2Ts) CA_params)) B2Ts bnf_sets;
        val bnf_map_app_f1 = Term.list_comb (mk_bnf_map B1Ts ranTs, f1s);
        val bnf_map_app_f2 = Term.list_comb (mk_bnf_map B2Ts ranTs, f2s);
        val bnf_map_app_p1 = Term.list_comb (mk_bnf_map domTs B1Ts, p1s);
        val bnf_map_app_p2 = Term.list_comb (mk_bnf_map domTs B2Ts, p2s);

        val map_wpull = mk_wpull (mk_in Xs bnf_sets_CX CX)
          (mk_in B1s bnf_sets_CB1 CB1) (mk_in B2s bnf_sets_CB2 CB2)
          bnf_map_app_f1 bnf_map_app_f2 NONE bnf_map_app_p1 bnf_map_app_p2;
      in
        fold_rev Logic.all (Xs @ B1s @ B2s @ f1s @ f2s @ p1s @ p2s)
          (Logic.list_implies (prems, HOLogic.mk_Trueprop map_wpull))
      end;

    val rel_O_Gr_goal = fold_rev Logic.all Rs (mk_Trueprop_eq (Term.list_comb (rel, Rs), O_Gr));

    val goals = zip_axioms map_id_goal map_comp_goal map_cong_goal set_naturals_goal
      card_order_bd_goal cinfinite_bd_goal set_bds_goal in_bd_goal map_wpull_goal rel_O_Gr_goal;

    fun mk_wit_goals (I, wit) =
      let
        val xs = map (nth bs) I;
        fun wit_goal i =
          let
            val z = nth zs i;
            val set_wit = nth bnf_sets_As i $ Term.list_comb (wit, xs);
            val concl = HOLogic.mk_Trueprop
              (if member (op =) I i then HOLogic.mk_eq (z, nth bs i)
              else @{term False});
          in
            fold_rev Logic.all (z :: xs)
              (Logic.mk_implies (HOLogic.mk_Trueprop (HOLogic.mk_mem (z, set_wit)), concl))
          end;
      in
        map wit_goal (0 upto live - 1)
      end;

    val wit_goalss = map mk_wit_goals bnf_wit_As;

    fun after_qed thms lthy =
      let
        val (axioms, wit_thms) = apfst (mk_axioms live) (chop (length goals) thms);

        val bd_Card_order = #bd_card_order axioms RS @{thm conjunct2[OF card_order_on_Card_order]};
        val bd_Cinfinite = @{thm conjI} OF [#bd_cinfinite axioms, bd_Card_order];
        val bd_Cnotzero = bd_Cinfinite RS @{thm Cinfinite_Cnotzero};

        fun mk_lazy f = if fact_policy <> Derive_Few_Facts then Lazy.value (f ()) else Lazy.lazy f;

        fun mk_collect_set_natural () =
          let
            val defT = mk_bnf_T Ts CA --> HOLogic.mk_setT T;
            val collect_map = HOLogic.mk_comp
              (mk_collect (map (mk_bnf_t Ts) bnf_sets) defT,
              Term.list_comb (mk_bnf_map As' Ts, hs));
            val image_collect = mk_collect
              (map2 (fn h => fn set => HOLogic.mk_comp (mk_image h, set)) hs bnf_sets_As)
              defT;
            (*collect {set1 ... setm} o map f1 ... fm = collect {f1` o set1 ... fm` o setm}*)
            val goal = fold_rev Logic.all hs (mk_Trueprop_eq (collect_map, image_collect));
          in
            Skip_Proof.prove lthy [] [] goal
              (fn {context = ctxt, ...} => mk_collect_set_natural_tac ctxt (#set_natural axioms))
            |> Thm.close_derivation
          end;

        val collect_set_natural = mk_lazy mk_collect_set_natural;

        fun mk_in_mono () =
          let
            val prems_mono = map2 (HOLogic.mk_Trueprop oo mk_subset) As As_copy;
            val in_mono_goal =
              fold_rev Logic.all (As @ As_copy)
                (Logic.list_implies (prems_mono, HOLogic.mk_Trueprop
                  (mk_subset (mk_in As bnf_sets_As CA') (mk_in As_copy bnf_sets_As CA'))));
          in
            Skip_Proof.prove lthy [] [] in_mono_goal (K (mk_in_mono_tac live))
            |> Thm.close_derivation
          end;

        val in_mono = mk_lazy mk_in_mono;

        fun mk_in_cong () =
          let
            val prems_cong = map2 (HOLogic.mk_Trueprop oo curry HOLogic.mk_eq) As As_copy;
            val in_cong_goal =
              fold_rev Logic.all (As @ As_copy)
                (Logic.list_implies (prems_cong, HOLogic.mk_Trueprop
                  (HOLogic.mk_eq (mk_in As bnf_sets_As CA', mk_in As_copy bnf_sets_As CA'))));
          in
            Skip_Proof.prove lthy [] [] in_cong_goal (K ((TRY o hyp_subst_tac THEN' rtac refl) 1))
            |> Thm.close_derivation
          end;

        val in_cong = mk_lazy mk_in_cong;

        val map_id' = mk_lazy (fn () => mk_id' (#map_id axioms));
        val map_comp' = mk_lazy (fn () => mk_comp' (#map_comp axioms));

        val set_natural' =
          map (fn thm => mk_lazy (fn () => mk_set_natural' thm)) (#set_natural axioms);

        fun mk_map_wppull () =
          let
            val prems = if live = 0 then [] else
              [HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
                (map8 mk_wpull Xs B1s B2s f1s f2s (map SOME (e1s ~~ e2s)) p1s p2s))];
            val CX = mk_bnf_T domTs CA;
            val CB1 = mk_bnf_T B1Ts CA;
            val CB2 = mk_bnf_T B2Ts CA;
            val bnf_sets_CX =
              map2 (normalize_set (map (mk_bnf_T domTs) CA_params)) domTs bnf_sets;
            val bnf_sets_CB1 =
              map2 (normalize_set (map (mk_bnf_T B1Ts) CA_params)) B1Ts bnf_sets;
            val bnf_sets_CB2 =
              map2 (normalize_set (map (mk_bnf_T B2Ts) CA_params)) B2Ts bnf_sets;
            val bnf_map_app_f1 = Term.list_comb (mk_bnf_map B1Ts ranTs, f1s);
            val bnf_map_app_f2 = Term.list_comb (mk_bnf_map B2Ts ranTs, f2s);
            val bnf_map_app_e1 = Term.list_comb (mk_bnf_map B1Ts ranTs', e1s);
            val bnf_map_app_e2 = Term.list_comb (mk_bnf_map B2Ts ranTs'', e2s);
            val bnf_map_app_p1 = Term.list_comb (mk_bnf_map domTs B1Ts, p1s);
            val bnf_map_app_p2 = Term.list_comb (mk_bnf_map domTs B2Ts, p2s);

            val concl = mk_wpull (mk_in Xs bnf_sets_CX CX)
              (mk_in B1s bnf_sets_CB1 CB1) (mk_in B2s bnf_sets_CB2 CB2)
              bnf_map_app_f1 bnf_map_app_f2 (SOME (bnf_map_app_e1, bnf_map_app_e2))
              bnf_map_app_p1 bnf_map_app_p2;

            val goal =
              fold_rev Logic.all (Xs @ B1s @ B2s @ f1s @ f2s @ e1s @ e2s @ p1s @ p2s)
                (Logic.list_implies (prems, HOLogic.mk_Trueprop concl))
          in
            Skip_Proof.prove lthy [] [] goal
              (fn _ => mk_map_wppull_tac (#map_id axioms) (#map_cong axioms)
                (#map_wpull axioms) (Lazy.force map_comp') (map Lazy.force set_natural'))
            |> Thm.close_derivation
          end;

        val rel_O_Grs = no_refl [#rel_O_Gr axioms];

        val map_wppull = mk_lazy mk_map_wppull;

        fun mk_rel_Gr () =
          let
            val lhs = Term.list_comb (rel, map2 mk_Gr As fs);
            val rhs = mk_Gr (mk_in As bnf_sets_As CA') (Term.list_comb (bnf_map_AsBs, fs));
            val goal = fold_rev Logic.all (As @ fs) (mk_Trueprop_eq (lhs, rhs));
          in
            Skip_Proof.prove lthy [] [] goal
              (mk_rel_Gr_tac rel_O_Grs (#map_id axioms) (#map_cong axioms) (Lazy.force map_id')
                (Lazy.force map_comp') (map Lazy.force set_natural'))
            |> Thm.close_derivation
          end;

        val rel_Gr = mk_lazy mk_rel_Gr;

        fun mk_rel_prems f = map2 (HOLogic.mk_Trueprop oo f) Rs Rs_copy
        fun mk_rel_concl f = HOLogic.mk_Trueprop
          (f (Term.list_comb (rel, Rs), Term.list_comb (rel, Rs_copy)));

        fun mk_rel_mono () =
          let
            val mono_prems = mk_rel_prems mk_subset;
            val mono_concl = mk_rel_concl (uncurry mk_subset);
          in
            Skip_Proof.prove lthy [] []
              (fold_rev Logic.all (Rs @ Rs_copy) (Logic.list_implies (mono_prems, mono_concl)))
              (mk_rel_mono_tac rel_O_Grs (Lazy.force in_mono))
            |> Thm.close_derivation
          end;

        fun mk_rel_cong () =
          let
            val cong_prems = mk_rel_prems (curry HOLogic.mk_eq);
            val cong_concl = mk_rel_concl HOLogic.mk_eq;
          in
            Skip_Proof.prove lthy [] []
              (fold_rev Logic.all (Rs @ Rs_copy) (Logic.list_implies (cong_prems, cong_concl)))
              (fn _ => (TRY o hyp_subst_tac THEN' rtac refl) 1)
            |> Thm.close_derivation
          end;

        val rel_mono = mk_lazy mk_rel_mono;
        val rel_cong = mk_lazy mk_rel_cong;

        fun mk_rel_Id () =
          let val relAsAs = mk_bnf_rel self_setRTs CA' CA' in
            Skip_Proof.prove lthy [] []
              (HOLogic.mk_Trueprop
                (HOLogic.mk_eq (Term.list_comb (relAsAs, map Id_const As'), Id_const CA')))
              (mk_rel_Id_tac live (Lazy.force rel_Gr) (#map_id axioms))
            |> Thm.close_derivation
          end;

        val rel_Id = mk_lazy mk_rel_Id;

        fun mk_rel_converse () =
          let
            val relBsAs = mk_bnf_rel setRT's CB' CA';
            val lhs = Term.list_comb (relBsAs, map mk_converse Rs);
            val rhs = mk_converse (Term.list_comb (rel, Rs));
            val le_goal = fold_rev Logic.all Rs (HOLogic.mk_Trueprop (mk_subset lhs rhs));
            val le_thm = Skip_Proof.prove lthy [] [] le_goal
              (mk_rel_converse_le_tac rel_O_Grs (Lazy.force rel_Id) (#map_cong axioms)
                (Lazy.force map_comp') (map Lazy.force set_natural'))
              |> Thm.close_derivation
            val goal = fold_rev Logic.all Rs (mk_Trueprop_eq (lhs, rhs));
          in
            Skip_Proof.prove lthy [] [] goal (fn _ => mk_rel_converse_tac le_thm)
            |> Thm.close_derivation
          end;

        val rel_converse = mk_lazy mk_rel_converse;

        fun mk_rel_O () =
          let
            val relAsCs = mk_bnf_rel setRTsAsCs CA' CC';
            val relBsCs = mk_bnf_rel setRTsBsCs CB' CC';
            val lhs = Term.list_comb (relAsCs, map2 (curry mk_rel_comp) Rs Ss);
            val rhs = mk_rel_comp (Term.list_comb (rel, Rs), Term.list_comb (relBsCs, Ss));
            val goal = fold_rev Logic.all (Rs @ Ss) (mk_Trueprop_eq (lhs, rhs));
          in
            Skip_Proof.prove lthy [] [] goal
              (mk_rel_O_tac rel_O_Grs (Lazy.force rel_Id) (#map_cong axioms)
                (Lazy.force map_wppull) (Lazy.force map_comp') (map Lazy.force set_natural'))
            |> Thm.close_derivation
          end;

        val rel_O = mk_lazy mk_rel_O;

        fun mk_in_rel () =
          let
            val bnf_in = mk_in Rs (map (mk_bnf_t RTs) bnf_sets) CRs';
            val map1 = Term.list_comb (mk_bnf_map RTs As', map fst_const RTs);
            val map2 = Term.list_comb (mk_bnf_map RTs Bs', map snd_const RTs);
            val map_fst_eq = HOLogic.mk_eq (map1 $ z, x);
            val map_snd_eq = HOLogic.mk_eq (map2 $ z, y);
            val lhs = HOLogic.mk_mem (HOLogic.mk_prod (x, y), Term.list_comb (rel, Rs));
            val rhs =
              HOLogic.mk_exists (fst z', snd z', HOLogic.mk_conj (HOLogic.mk_mem (z, bnf_in),
                HOLogic.mk_conj (map_fst_eq, map_snd_eq)));
            val goal =
              fold_rev Logic.all (x :: y :: Rs) (mk_Trueprop_eq (lhs, rhs));
          in
            Skip_Proof.prove lthy [] [] goal (mk_in_rel_tac rel_O_Grs (length bnf_sets))
            |> Thm.close_derivation
          end;

        val in_rel = mk_lazy mk_in_rel;

        val defs = mk_defs bnf_map_def bnf_set_defs bnf_pred_def bnf_rel_def;

        val facts = mk_facts bd_Card_order bd_Cinfinite bd_Cnotzero collect_set_natural
          in_cong in_mono in_rel map_comp' map_id' map_wppull
          rel_cong rel_mono rel_Id rel_Gr rel_converse rel_O set_natural';

        val wits = map2 mk_witness bnf_wits wit_thms;

        val bnf_pred = Term.subst_atomic_types
          ((Ds ~~ deads) @ (As' ~~ alphas) @ (Bs' ~~ betas)) pred;
        val bnf_rel = Term.subst_atomic_types
          ((Ds ~~ deads) @ (As' ~~ alphas) @ (Bs' ~~ betas)) rel;

        val bnf = mk_bnf b CA live alphas betas dead deads bnf_map bnf_sets bnf_bd axioms defs facts
          wits bnf_pred bnf_rel;
      in
        (bnf, lthy
          |> (if fact_policy = Note_All_Facts_and_Axioms then
                let
                  val witNs = if length wits = 1 then [witN] else map mk_witN (1 upto length wits);
                  val notes =
                    [(bd_card_orderN, [#bd_card_order axioms]),
                    (bd_cinfiniteN, [#bd_cinfinite axioms]),
                    (bd_Card_orderN, [#bd_Card_order facts]),
                    (bd_CinfiniteN, [#bd_Cinfinite facts]),
                    (bd_CnotzeroN, [#bd_Cnotzero facts]),
                    (collect_set_naturalN, [Lazy.force (#collect_set_natural facts)]),
                    (in_bdN, [#in_bd axioms]),
                    (in_monoN, [Lazy.force (#in_mono facts)]),
                    (in_relN, [Lazy.force (#in_rel facts)]),
                    (map_compN, [#map_comp axioms]),
                    (map_idN, [#map_id axioms]),
                    (map_wpullN, [#map_wpull axioms]),
                    (set_naturalN, #set_natural axioms),
                    (set_bdN, #set_bd axioms)] @
                    map2 pair witNs wit_thms
                    |> map (fn (thmN, thms) =>
                      ((qualify (Binding.qualify true (Binding.name_of b) (Binding.name thmN)), []),
                      [(thms, [])]));
                in
                  Local_Theory.notes notes #> snd
                end
              else
                I)
          |> (if fact_policy = Note_All_Facts_and_Axioms orelse
                 fact_policy = Derive_All_Facts_Note_Most then
                let
                  val notes =
                    [(map_congN, [#map_cong axioms]),
                    (rel_O_GrN, rel_O_Grs),
                    (rel_IdN, [Lazy.force (#rel_Id facts)]),
                    (rel_GrN, [Lazy.force (#rel_Gr facts)]),
                    (rel_converseN, [Lazy.force (#rel_converse facts)]),
                    (rel_monoN, [Lazy.force (#rel_mono facts)]),
                    (rel_ON, [Lazy.force (#rel_O facts)]),
                    (map_id'N, [Lazy.force (#map_id' facts)]),
                    (map_comp'N, [Lazy.force (#map_comp' facts)]),
                    (set_natural'N, map Lazy.force (#set_natural' facts))]
                    |> filter_out (null o #2)
                    |> map (fn (thmN, thms) =>
                      ((qualify (Binding.qualify true (Binding.name_of b) (Binding.name thmN)), []),
                      [(thms, [])]));
                in
                  Local_Theory.notes notes #> snd
                end
              else
                I))
      end;

    val one_step_defs =
      no_reflexive (bnf_map_def :: bnf_bd_def :: bnf_set_defs @ bnf_wit_defs @ [bnf_pred_def,
        bnf_rel_def]);
  in
    (key, goals, wit_goalss, after_qed, lthy, one_step_defs)
  end;

fun register_bnf key (bnf, lthy) =
  (bnf, Local_Theory.declaration {syntax = false, pervasive = true}
    (fn phi => Data.map (Symtab.update_new (key, morph_bnf phi bnf))) lthy);

(* TODO: Once the invariant "nwits > 0" holds, remove "mk_conjunction_balanced'" and "rtac TrueI"
   below *)
fun mk_conjunction_balanced' [] = @{prop True}
  | mk_conjunction_balanced' ts = Logic.mk_conjunction_balanced ts;

fun bnf_def const_policy fact_policy qualify tacs wit_tac Ds =
  (fn (_, goals, wit_goalss, after_qed, lthy, one_step_defs) =>
  let
    val wits_tac =
      K (TRYALL Goal.conjunction_tac) THEN' K (TRYALL (rtac TrueI)) THEN'
      mk_unfold_defs_then_tac lthy one_step_defs wit_tac;
    val wit_goals = map mk_conjunction_balanced' wit_goalss;
    val wit_thms =
      Skip_Proof.prove lthy [] [] (mk_conjunction_balanced' wit_goals) wits_tac
      |> Conjunction.elim_balanced (length wit_goals)
      |> map2 (Conjunction.elim_balanced o length) wit_goalss
      |> map (map (Thm.close_derivation o Thm.forall_elim_vars 0));
  in
    map2 (Thm.close_derivation oo Skip_Proof.prove lthy [] [])
      goals (map (mk_unfold_defs_then_tac lthy one_step_defs) tacs)
    |> (fn thms => after_qed (map single thms @ wit_thms) lthy)
  end) oo prepare_def const_policy fact_policy qualify (K I) Ds;

val bnf_def_cmd = (fn (key, goals, wit_goals, after_qed, lthy, defs) =>
  Proof.unfolding ([[(defs, [])]])
    (Proof.theorem NONE (snd o register_bnf key oo after_qed)
      (map (single o rpair []) goals @ map (map (rpair [])) wit_goals) lthy)) oo
  prepare_def Do_Inline (user_policy Derive_All_Facts_Note_Most) I Syntax.read_term NONE;

fun print_bnfs ctxt =
  let
    fun pretty_set sets i = Pretty.block
      [Pretty.str (mk_setN (i + 1) ^ ":"), Pretty.brk 1,
          Pretty.quote (Syntax.pretty_term ctxt (nth sets i))];

    fun pretty_bnf (key, BNF {T = T, map = map, sets = sets, bd = bd,
      live = live, lives = lives, dead = dead, deads = deads, ...}) =
      Pretty.big_list
        (Pretty.string_of (Pretty.block [Pretty.str key, Pretty.str ":", Pretty.brk 1,
          Pretty.quote (Syntax.pretty_typ ctxt T)]))
        ([Pretty.block [Pretty.str "live:", Pretty.brk 1, Pretty.str (string_of_int live),
            Pretty.brk 3, Pretty.list "[" "]" (List.map (Syntax.pretty_typ ctxt) lives)],
          Pretty.block [Pretty.str "dead:", Pretty.brk 1, Pretty.str (string_of_int dead),
            Pretty.brk 3, Pretty.list "[" "]" (List.map (Syntax.pretty_typ ctxt) deads)],
          Pretty.block [Pretty.str (mapN ^ ":"), Pretty.brk 1,
            Pretty.quote (Syntax.pretty_term ctxt map)]] @
          List.map (pretty_set sets) (0 upto length sets - 1) @
          [Pretty.block [Pretty.str (bdN ^ ":"), Pretty.brk 1,
            Pretty.quote (Syntax.pretty_term ctxt bd)]]);
  in
    Pretty.big_list "BNFs:" (map pretty_bnf (Symtab.dest (Data.get (Context.Proof ctxt))))
    |> Pretty.writeln
  end;

val _ =
  Outer_Syntax.improper_command @{command_spec "print_bnfs"} "print all BNFs"
    (Scan.succeed (Toplevel.keep (print_bnfs o Toplevel.context_of)));

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "bnf_def"} "define a BNF for an existing type"
    ((parse_opt_binding_colon -- Parse.term --
       (@{keyword "["} |-- Parse.list Parse.term --| @{keyword "]"}) -- Parse.term --
       (@{keyword "["} |-- Parse.list Parse.term --| @{keyword "]"}) -- Scan.option Parse.term)
       >> bnf_def_cmd);

end;
