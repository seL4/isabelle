(*  Title:      HOL/Tools/BNF/bnf_def.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Martin Desharnais, TU Muenchen
    Copyright   2012, 2013, 2014

Definition of bounded natural functors.
*)

signature BNF_DEF =
sig
  type bnf
  type nonemptiness_witness = {I: int list, wit: term, prop: thm list}

  val morph_bnf: morphism -> bnf -> bnf
  val morph_bnf_defs: morphism -> bnf -> bnf
  val permute_deads: (typ list -> typ list) -> bnf -> bnf
  val transfer_bnf: theory -> bnf -> bnf
  val bnf_of: Proof.context -> string -> bnf option
  val bnf_of_global: theory -> string -> bnf option
  val bnf_interpretation: string -> (bnf -> local_theory -> local_theory) -> theory -> theory
  val interpret_bnf: (string -> bool) -> bnf -> local_theory -> local_theory
  val register_bnf_raw: string -> bnf -> local_theory -> local_theory
  val register_bnf: (string -> bool) -> string -> bnf -> local_theory -> local_theory

  val name_of_bnf: bnf -> binding
  val T_of_bnf: bnf -> typ
  val live_of_bnf: bnf -> int
  val lives_of_bnf: bnf -> typ list
  val dead_of_bnf: bnf -> int
  val deads_of_bnf: bnf -> typ list
  val bd_of_bnf: bnf -> term
  val nwits_of_bnf: bnf -> int

  val mapN: string
  val predN: string
  val relN: string
  val setN: string
  val mk_setN: int -> string
  val mk_witN: int -> string

  val map_of_bnf: bnf -> term
  val pred_of_bnf: bnf -> term
  val rel_of_bnf: bnf -> term
  val sets_of_bnf: bnf -> term list

  val mk_T_of_bnf: typ list -> typ list -> bnf -> typ
  val mk_bd_of_bnf: typ list -> typ list -> bnf -> term
  val mk_map_of_bnf: typ list -> typ list -> typ list -> bnf -> term
  val mk_pred_of_bnf: typ list -> typ list -> bnf -> term
  val mk_rel_of_bnf: typ list -> typ list -> typ list -> bnf -> term
  val mk_sets_of_bnf: typ list list -> typ list list -> bnf -> term list
  val mk_wits_of_bnf: typ list list -> typ list list -> bnf -> (int list * term) list

  val bd_Card_order_of_bnf: bnf -> thm
  val bd_Cinfinite_of_bnf: bnf -> thm
  val bd_Cnotzero_of_bnf: bnf -> thm
  val bd_card_order_of_bnf: bnf -> thm
  val bd_cinfinite_of_bnf: bnf -> thm
  val collect_set_map_of_bnf: bnf -> thm
  val in_bd_of_bnf: bnf -> thm
  val in_cong_of_bnf: bnf -> thm
  val in_mono_of_bnf: bnf -> thm
  val in_rel_of_bnf: bnf -> thm
  val inj_map_of_bnf: bnf -> thm
  val inj_map_strong_of_bnf: bnf -> thm
  val le_rel_OO_of_bnf: bnf -> thm
  val map_comp0_of_bnf: bnf -> thm
  val map_comp_of_bnf: bnf -> thm
  val map_cong0_of_bnf: bnf -> thm
  val map_cong_of_bnf: bnf -> thm
  val map_cong_pred_of_bnf: bnf -> thm
  val map_cong_simp_of_bnf: bnf -> thm
  val map_def_of_bnf: bnf -> thm
  val map_id0_of_bnf: bnf -> thm
  val map_id_of_bnf: bnf -> thm
  val map_ident0_of_bnf: bnf -> thm
  val map_ident_of_bnf: bnf -> thm
  val map_transfer_of_bnf: bnf -> thm
  val pred_cong0_of_bnf: bnf -> thm
  val pred_cong_of_bnf: bnf -> thm
  val pred_cong_simp_of_bnf: bnf -> thm
  val pred_def_of_bnf: bnf -> thm
  val pred_map_of_bnf: bnf -> thm
  val pred_mono_strong0_of_bnf: bnf -> thm
  val pred_mono_strong_of_bnf: bnf -> thm
  val pred_mono_of_bnf: bnf -> thm
  val pred_set_of_bnf: bnf -> thm
  val pred_rel_of_bnf: bnf -> thm
  val pred_transfer_of_bnf: bnf -> thm
  val pred_True_of_bnf: bnf -> thm
  val rel_Grp_of_bnf: bnf -> thm
  val rel_OO_Grp_of_bnf: bnf -> thm
  val rel_OO_of_bnf: bnf -> thm
  val rel_cong0_of_bnf: bnf -> thm
  val rel_cong_of_bnf: bnf -> thm
  val rel_cong_simp_of_bnf: bnf -> thm
  val rel_conversep_of_bnf: bnf -> thm
  val rel_def_of_bnf: bnf -> thm
  val rel_eq_of_bnf: bnf -> thm
  val rel_flip_of_bnf: bnf -> thm
  val rel_map_of_bnf: bnf -> thm list
  val rel_mono_of_bnf: bnf -> thm
  val rel_mono_strong0_of_bnf: bnf -> thm
  val rel_mono_strong_of_bnf: bnf -> thm
  val rel_eq_onp_of_bnf: bnf -> thm
  val rel_refl_of_bnf: bnf -> thm
  val rel_refl_strong_of_bnf: bnf -> thm
  val rel_reflp_of_bnf: bnf -> thm
  val rel_symp_of_bnf: bnf -> thm
  val rel_transfer_of_bnf: bnf -> thm
  val rel_transp_of_bnf: bnf -> thm
  val set_bd_of_bnf: bnf -> thm list
  val set_defs_of_bnf: bnf -> thm list
  val set_map0_of_bnf: bnf -> thm list
  val set_map_of_bnf: bnf -> thm list
  val set_transfer_of_bnf: bnf -> thm list
  val wit_thms_of_bnf: bnf -> thm list
  val wit_thmss_of_bnf: bnf -> thm list list

  val mk_map: int -> typ list -> typ list -> term -> term
  val mk_pred: typ list -> term -> term
  val mk_rel: int -> typ list -> typ list -> term -> term
  val mk_set: typ list -> term -> term
  val build_map: Proof.context -> typ list -> typ list -> (typ * typ -> term) -> typ * typ -> term
  val build_rel: (string * (int * term)) list -> Proof.context -> typ list -> typ list ->
    (typ * typ -> term) -> typ * typ -> term
  val build_set: Proof.context -> typ -> typ -> term
  val flatten_type_args_of_bnf: bnf -> 'a -> 'a list -> 'a list
  val map_flattened_map_args: Proof.context -> string -> (term list -> 'a list) -> term list ->
    'a list

  val mk_witness: int list * term -> thm list -> nonemptiness_witness
  val mk_wit_goals: term list -> term list -> term list -> int list * term -> term list
  val minimize_wits: (''a list * 'b) list -> (''a list * 'b) list
  val wits_of_bnf: bnf -> nonemptiness_witness list

  val zip_axioms: 'a -> 'a -> 'a -> 'a list -> 'a -> 'a -> 'a list -> 'a -> 'a -> 'a -> 'a list

  datatype inline_policy = Dont_Inline | Hardly_Inline | Smart_Inline | Do_Inline
  datatype fact_policy = Dont_Note | Note_Some | Note_All

  val bnf_internals: bool Config.T
  val bnf_timing: bool Config.T
  val user_policy: fact_policy -> Proof.context -> fact_policy
  val note_bnf_thms: fact_policy -> (binding -> binding) -> binding -> bnf -> local_theory ->
    bnf * local_theory
  val note_bnf_defs: bnf -> local_theory -> bnf * local_theory

  val print_bnfs: Proof.context -> unit
  val prepare_def: inline_policy -> (Proof.context -> fact_policy) -> bool ->
    (binding -> binding) -> (Proof.context -> 'a -> typ) -> (Proof.context -> 'b -> term) ->
    typ list option -> binding -> binding -> binding -> binding list ->
    ((((((binding * 'a) * 'b) * 'b list) * 'b) * 'b list) * 'b option) * 'b option ->
    Proof.context ->
    string * term list * ((Proof.context -> thm list -> tactic) option * term list list) *
    ((thm list -> thm list list) -> thm list list -> Proof.context -> bnf * local_theory) *
    local_theory * thm list
  val define_bnf_consts: inline_policy -> fact_policy -> bool -> typ list option ->
    binding -> binding -> binding -> binding list ->
    ((((((binding * typ) * term) * term list) * term) * term list) * term option) * term option ->
    local_theory ->
      ((typ list * typ list * typ list * typ) *
       (term * term list * term * (int list * term) list * term * term) *
       (thm * thm list * thm * thm list * thm * thm) *
       ((typ list -> typ list -> typ list -> term) *
        (typ list -> typ list -> term -> term) *
        (typ list -> typ list -> typ -> typ) *
        (typ list -> typ list -> typ list -> term) *
        (typ list -> typ list -> term) *
        (typ list -> typ list -> typ list -> term) *
        (typ list -> typ list -> term))) * local_theory

  val bnf_def: inline_policy -> (Proof.context -> fact_policy) -> bool -> (binding -> binding) ->
    (Proof.context -> tactic) list -> (Proof.context -> tactic) -> typ list option -> binding ->
    binding -> binding -> binding list ->
    ((((((binding * typ) * term) * term list) * term) * term list) * term option) * term option ->
    local_theory -> bnf * local_theory
  val bnf_cmd: (((((((binding * string) * string) * string list) * string) * string list)
      * string option) * string option) * (Proof.context -> Plugin_Name.filter) ->
    Proof.context -> Proof.state
end;

structure BNF_Def : BNF_DEF =
struct

open BNF_Util
open BNF_Tactics
open BNF_Def_Tactics

val fundefcong_attrs = @{attributes [fundef_cong]};
val mono_attrs = @{attributes [mono]};

type axioms = {
  map_id0: thm,
  map_comp0: thm,
  map_cong0: thm,
  set_map0: thm list,
  bd_card_order: thm,
  bd_cinfinite: thm,
  set_bd: thm list,
  le_rel_OO: thm,
  rel_OO_Grp: thm,
  pred_set: thm
};

fun mk_axioms' (((((((((id, comp), cong), map), c_o), cinf), set_bd), le_rel_OO), rel), pred) =
  {map_id0 = id, map_comp0 = comp, map_cong0 = cong, set_map0 = map, bd_card_order = c_o,
   bd_cinfinite = cinf, set_bd = set_bd, le_rel_OO = le_rel_OO, rel_OO_Grp = rel, pred_set = pred};

fun dest_cons [] = raise List.Empty
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

fun zip_axioms mid mcomp mcong smap bdco bdinf sbd le_rel_OO rel pred =
  [mid, mcomp, mcong] @ smap @ [bdco, bdinf] @ sbd @ [le_rel_OO, rel, pred];

fun map_axioms f {map_id0, map_comp0, map_cong0, set_map0, bd_card_order, bd_cinfinite, set_bd,
  le_rel_OO, rel_OO_Grp, pred_set} =
  {map_id0 = f map_id0,
    map_comp0 = f map_comp0,
    map_cong0 = f map_cong0,
    set_map0 = map f set_map0,
    bd_card_order = f bd_card_order,
    bd_cinfinite = f bd_cinfinite,
    set_bd = map f set_bd,
    le_rel_OO = f le_rel_OO,
    rel_OO_Grp = f rel_OO_Grp,
    pred_set = f pred_set};

val morph_axioms = map_axioms o Morphism.thm;

type defs = {
  map_def: thm,
  set_defs: thm list,
  rel_def: thm,
  pred_def: thm
}

fun mk_defs map sets rel pred = {map_def = map, set_defs = sets, rel_def = rel, pred_def = pred};

fun map_defs f {map_def, set_defs, rel_def, pred_def} =
  {map_def = f map_def, set_defs = map f set_defs, rel_def = f rel_def, pred_def = f pred_def};

val morph_defs = map_defs o Morphism.thm;

type facts = {
  bd_Card_order: thm,
  bd_Cinfinite: thm,
  bd_Cnotzero: thm,
  collect_set_map: thm lazy,
  in_bd: thm lazy,
  in_cong: thm lazy,
  in_mono: thm lazy,
  in_rel: thm lazy,
  inj_map: thm lazy,
  inj_map_strong: thm lazy,
  map_comp: thm lazy,
  map_cong: thm lazy,
  map_cong_simp: thm lazy,
  map_cong_pred: thm lazy,
  map_id: thm lazy,
  map_ident0: thm lazy,
  map_ident: thm lazy,
  map_transfer: thm lazy,
  rel_eq: thm lazy,
  rel_flip: thm lazy,
  set_map: thm lazy list,
  rel_cong0: thm lazy,
  rel_cong: thm lazy,
  rel_cong_simp: thm lazy,
  rel_map: thm list lazy,
  rel_mono: thm lazy,
  rel_mono_strong0: thm lazy,
  rel_mono_strong: thm lazy,
  set_transfer: thm list lazy,
  rel_Grp: thm lazy,
  rel_conversep: thm lazy,
  rel_OO: thm lazy,
  rel_refl: thm lazy,
  rel_refl_strong: thm lazy,
  rel_reflp: thm lazy,
  rel_symp: thm lazy,
  rel_transp: thm lazy,
  rel_transfer: thm lazy,
  rel_eq_onp: thm lazy,
  pred_transfer: thm lazy,
  pred_True: thm lazy,
  pred_map: thm lazy,
  pred_rel: thm lazy,
  pred_mono_strong0: thm lazy,
  pred_mono_strong: thm lazy,
  pred_mono: thm lazy,
  pred_cong0: thm lazy,
  pred_cong: thm lazy,
  pred_cong_simp: thm lazy
};

fun mk_facts bd_Card_order bd_Cinfinite bd_Cnotzero collect_set_map in_bd in_cong in_mono in_rel
    inj_map inj_map_strong map_comp map_cong map_cong_simp map_cong_pred map_id map_ident0 map_ident
    map_transfer rel_eq rel_flip set_map rel_cong0 rel_cong rel_cong_simp rel_map rel_mono
    rel_mono_strong0 rel_mono_strong set_transfer rel_Grp rel_conversep rel_OO rel_refl
    rel_refl_strong rel_reflp rel_symp rel_transp rel_transfer rel_eq_onp pred_transfer pred_True
    pred_map pred_rel pred_mono_strong0 pred_mono_strong pred_mono pred_cong0 pred_cong
    pred_cong_simp = {
  bd_Card_order = bd_Card_order,
  bd_Cinfinite = bd_Cinfinite,
  bd_Cnotzero = bd_Cnotzero,
  collect_set_map = collect_set_map,
  in_bd = in_bd,
  in_cong = in_cong,
  in_mono = in_mono,
  in_rel = in_rel,
  inj_map = inj_map,
  inj_map_strong = inj_map_strong,
  map_comp = map_comp,
  map_cong = map_cong,
  map_cong_simp = map_cong_simp,
  map_cong_pred = map_cong_pred,
  map_id = map_id,
  map_ident0 = map_ident0,
  map_ident = map_ident,
  map_transfer = map_transfer,
  rel_eq = rel_eq,
  rel_flip = rel_flip,
  set_map = set_map,
  rel_cong0 = rel_cong0,
  rel_cong = rel_cong,
  rel_cong_simp = rel_cong_simp,
  rel_map = rel_map,
  rel_mono = rel_mono,
  rel_mono_strong0 = rel_mono_strong0,
  rel_mono_strong = rel_mono_strong,
  rel_transfer = rel_transfer,
  rel_Grp = rel_Grp,
  rel_conversep = rel_conversep,
  rel_OO = rel_OO,
  rel_refl = rel_refl,
  rel_refl_strong = rel_refl_strong,
  rel_reflp = rel_reflp,
  rel_symp = rel_symp,
  rel_transp = rel_transp,
  set_transfer = set_transfer,
  rel_eq_onp = rel_eq_onp,
  pred_transfer = pred_transfer,
  pred_True = pred_True,
  pred_map = pred_map,
  pred_rel = pred_rel,
  pred_mono_strong0 = pred_mono_strong0,
  pred_mono_strong = pred_mono_strong,
  pred_mono = pred_mono,
  pred_cong0 = pred_cong0,
  pred_cong = pred_cong,
  pred_cong_simp = pred_cong_simp};

fun map_facts f {
  bd_Card_order,
  bd_Cinfinite,
  bd_Cnotzero,
  collect_set_map,
  in_bd,
  in_cong,
  in_mono,
  in_rel,
  inj_map,
  inj_map_strong,
  map_comp,
  map_cong,
  map_cong_simp,
  map_cong_pred,
  map_id,
  map_ident0,
  map_ident,
  map_transfer,
  rel_eq,
  rel_flip,
  set_map,
  rel_cong0,
  rel_cong,
  rel_cong_simp,
  rel_map,
  rel_mono,
  rel_mono_strong0,
  rel_mono_strong,
  rel_transfer,
  rel_Grp,
  rel_conversep,
  rel_OO,
  rel_refl,
  rel_refl_strong,
  rel_reflp,
  rel_symp,
  rel_transp,
  set_transfer,
  rel_eq_onp,
  pred_transfer,
  pred_True,
  pred_map,
  pred_rel,
  pred_mono_strong0,
  pred_mono_strong,
  pred_mono,
  pred_cong0,
  pred_cong,
  pred_cong_simp} =
  {bd_Card_order = f bd_Card_order,
    bd_Cinfinite = f bd_Cinfinite,
    bd_Cnotzero = f bd_Cnotzero,
    collect_set_map = Lazy.map f collect_set_map,
    in_bd = Lazy.map f in_bd,
    in_cong = Lazy.map f in_cong,
    in_mono = Lazy.map f in_mono,
    in_rel = Lazy.map f in_rel,
    inj_map = Lazy.map f inj_map,
    inj_map_strong = Lazy.map f inj_map_strong,
    map_comp = Lazy.map f map_comp,
    map_cong = Lazy.map f map_cong,
    map_cong_simp = Lazy.map f map_cong_simp,
    map_cong_pred = Lazy.map f map_cong_pred,
    map_id = Lazy.map f map_id,
    map_ident0 = Lazy.map f map_ident0,
    map_ident = Lazy.map f map_ident,
    map_transfer = Lazy.map f map_transfer,
    rel_eq = Lazy.map f rel_eq,
    rel_flip = Lazy.map f rel_flip,
    set_map = map (Lazy.map f) set_map,
    rel_cong0 = Lazy.map f rel_cong0,
    rel_cong = Lazy.map f rel_cong,
    rel_cong_simp = Lazy.map f rel_cong_simp,
    rel_map = Lazy.map (map f) rel_map,
    rel_mono = Lazy.map f rel_mono,
    rel_mono_strong0 = Lazy.map f rel_mono_strong0,
    rel_mono_strong = Lazy.map f rel_mono_strong,
    rel_transfer = Lazy.map f rel_transfer,
    rel_Grp = Lazy.map f rel_Grp,
    rel_conversep = Lazy.map f rel_conversep,
    rel_OO = Lazy.map f rel_OO,
    rel_refl = Lazy.map f rel_refl,
    rel_refl_strong = Lazy.map f rel_refl_strong,
    rel_reflp = Lazy.map f rel_reflp,
    rel_symp = Lazy.map f rel_symp,
    rel_transp = Lazy.map f rel_transp,
    set_transfer = Lazy.map (map f) set_transfer,
    rel_eq_onp = Lazy.map f rel_eq_onp,
    pred_transfer = Lazy.map f pred_transfer,
    pred_True = Lazy.map f pred_True,
    pred_map = Lazy.map f pred_map,
    pred_rel = Lazy.map f pred_rel,
    pred_mono_strong0 = Lazy.map f pred_mono_strong0,
    pred_mono_strong = Lazy.map f pred_mono_strong,
    pred_mono = Lazy.map f pred_mono,
    pred_cong0 = Lazy.map f pred_cong0,
    pred_cong = Lazy.map f pred_cong,
    pred_cong_simp = Lazy.map f pred_cong_simp};

val morph_facts = map_facts o Morphism.thm;

type nonemptiness_witness = {
  I: int list,
  wit: term,
  prop: thm list
};

fun mk_witness (I, wit) prop = {I = I, wit = wit, prop = prop};
fun map_witness f g {I, wit, prop} = {I = I, wit = f wit, prop = map g prop};
fun morph_witness phi = map_witness (Morphism.term phi) (Morphism.thm phi);

datatype bnf = BNF of {
  name: binding,
  T: typ,
  live: int,
  lives: typ list, (*source type variables of map*)
  lives': typ list, (*target type variables of map*)
  dead: int,
  deads: typ list,
  map: term,
  sets: term list,
  bd: term,
  axioms: axioms,
  defs: defs,
  facts: facts,
  nwits: int,
  wits: nonemptiness_witness list,
  rel: term,
  pred: term
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

fun flatten_type_args_of_bnf bnf dead_x xs =
  let
    val Type (_, Ts) = T_of_bnf bnf;
    val lives = lives_of_bnf bnf;
    val deads = deads_of_bnf bnf;
  in
    permute_like_unique (op =) (deads @ lives) Ts (replicate (length deads) dead_x @ xs)
  end;

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
val rel_of_bnf = #rel o rep_bnf;
fun mk_rel_of_bnf Ds Ts Us bnf =
  let val bnf_rep = rep_bnf bnf;
  in
    Term.subst_atomic_types
      ((#deads bnf_rep ~~ Ds) @ (#lives bnf_rep ~~ Ts) @ (#lives' bnf_rep ~~ Us)) (#rel bnf_rep)
  end;
val pred_of_bnf = #pred o rep_bnf;
fun mk_pred_of_bnf Ds Ts bnf =
  let val bnf_rep = rep_bnf bnf;
  in
    Term.subst_atomic_types
      ((#deads bnf_rep ~~ Ds) @ (#lives bnf_rep ~~ Ts)) (#pred bnf_rep)
  end;

(*thms*)
val bd_Card_order_of_bnf = #bd_Card_order o #facts o rep_bnf;
val bd_Cinfinite_of_bnf = #bd_Cinfinite o #facts o rep_bnf;
val bd_Cnotzero_of_bnf = #bd_Cnotzero o #facts o rep_bnf;
val bd_card_order_of_bnf = #bd_card_order o #axioms o rep_bnf;
val bd_cinfinite_of_bnf = #bd_cinfinite o #axioms o rep_bnf;
val collect_set_map_of_bnf = Lazy.force o #collect_set_map o #facts o rep_bnf;
val in_bd_of_bnf = Lazy.force o #in_bd o #facts o rep_bnf;
val in_cong_of_bnf = Lazy.force o #in_cong o #facts o rep_bnf;
val in_mono_of_bnf = Lazy.force o #in_mono o #facts o rep_bnf;
val in_rel_of_bnf = Lazy.force o #in_rel o #facts o rep_bnf;
val inj_map_of_bnf = Lazy.force o #inj_map o #facts o rep_bnf;
val inj_map_strong_of_bnf = Lazy.force o #inj_map_strong o #facts o rep_bnf;
val le_rel_OO_of_bnf = #le_rel_OO o #axioms o rep_bnf;
val map_comp0_of_bnf = #map_comp0 o #axioms o rep_bnf;
val map_comp_of_bnf = Lazy.force o #map_comp o #facts o rep_bnf;
val map_cong0_of_bnf = #map_cong0 o #axioms o rep_bnf;
val map_cong_of_bnf = Lazy.force o #map_cong o #facts o rep_bnf;
val map_cong_pred_of_bnf = Lazy.force o #map_cong_pred o #facts o rep_bnf;
val map_cong_simp_of_bnf = Lazy.force o #map_cong_simp o #facts o rep_bnf;
val map_def_of_bnf = #map_def o #defs o rep_bnf;
val map_id0_of_bnf = #map_id0 o #axioms o rep_bnf;
val map_id_of_bnf = Lazy.force o #map_id o #facts o rep_bnf;
val map_ident0_of_bnf = Lazy.force o #map_ident0 o #facts o rep_bnf;
val map_ident_of_bnf = Lazy.force o #map_ident o #facts o rep_bnf;
val map_transfer_of_bnf = Lazy.force o #map_transfer o #facts o rep_bnf;
val rel_eq_onp_of_bnf = Lazy.force o #rel_eq_onp o #facts o rep_bnf;
val pred_def_of_bnf = #pred_def o #defs o rep_bnf;
val pred_map_of_bnf = Lazy.force o #pred_map o #facts o rep_bnf;
val pred_mono_strong0_of_bnf = Lazy.force o #pred_mono_strong0 o #facts o rep_bnf;
val pred_mono_strong_of_bnf = Lazy.force o #pred_mono_strong o #facts o rep_bnf;
val pred_mono_of_bnf = Lazy.force o #pred_mono o #facts o rep_bnf;
val pred_cong0_of_bnf = Lazy.force o #pred_cong0 o #facts o rep_bnf;
val pred_cong_of_bnf = Lazy.force o #pred_cong o #facts o rep_bnf;
val pred_cong_simp_of_bnf = Lazy.force o #pred_cong_simp o #facts o rep_bnf;
val pred_rel_of_bnf = Lazy.force o #pred_rel o #facts o rep_bnf;
val pred_set_of_bnf = #pred_set o #axioms o rep_bnf;
val pred_transfer_of_bnf = Lazy.force o #pred_transfer o #facts o rep_bnf;
val pred_True_of_bnf = Lazy.force o #pred_True o #facts o rep_bnf;
val rel_Grp_of_bnf = Lazy.force o #rel_Grp o #facts o rep_bnf;
val rel_OO_Grp_of_bnf = #rel_OO_Grp o #axioms o rep_bnf;
val rel_OO_of_bnf = Lazy.force o #rel_OO o #facts o rep_bnf;
val rel_cong0_of_bnf = Lazy.force o #rel_cong0 o #facts o rep_bnf;
val rel_cong_of_bnf = Lazy.force o #rel_cong o #facts o rep_bnf;
val rel_cong_simp_of_bnf = Lazy.force o #rel_cong_simp o #facts o rep_bnf;
val rel_conversep_of_bnf = Lazy.force o #rel_conversep o #facts o rep_bnf;
val rel_def_of_bnf = #rel_def o #defs o rep_bnf;
val rel_eq_of_bnf = Lazy.force o #rel_eq o #facts o rep_bnf;
val rel_flip_of_bnf = Lazy.force o #rel_flip o #facts o rep_bnf;
val rel_map_of_bnf = Lazy.force o #rel_map o #facts o rep_bnf;
val rel_mono_of_bnf = Lazy.force o #rel_mono o #facts o rep_bnf;
val rel_mono_strong0_of_bnf = Lazy.force o #rel_mono_strong0 o #facts o rep_bnf;
val rel_mono_strong_of_bnf = Lazy.force o #rel_mono_strong o #facts o rep_bnf;
val rel_refl_of_bnf = Lazy.force o #rel_refl o #facts o rep_bnf;
val rel_refl_strong_of_bnf = Lazy.force o #rel_refl_strong o #facts o rep_bnf;
val rel_reflp_of_bnf = Lazy.force o #rel_reflp o #facts o rep_bnf;
val rel_symp_of_bnf = Lazy.force o #rel_symp o #facts o rep_bnf;
val rel_transfer_of_bnf = Lazy.force o #rel_transfer o #facts o rep_bnf;
val rel_transp_of_bnf = Lazy.force o #rel_transp o #facts o rep_bnf;
val set_bd_of_bnf = #set_bd o #axioms o rep_bnf;
val set_defs_of_bnf = #set_defs o #defs o rep_bnf;
val set_map0_of_bnf = #set_map0 o #axioms o rep_bnf;
val set_map_of_bnf = map Lazy.force o #set_map o #facts o rep_bnf;
val set_transfer_of_bnf = Lazy.force o #set_transfer o #facts o rep_bnf;
val wit_thms_of_bnf = maps #prop o wits_of_bnf;
val wit_thmss_of_bnf = map #prop o wits_of_bnf;

fun mk_bnf name T live lives lives' dead deads map sets bd axioms defs facts wits rel pred =
  BNF {name = name, T = T,
       live = live, lives = lives, lives' = lives', dead = dead, deads = deads,
       map = map, sets = sets, bd = bd,
       axioms = axioms, defs = defs, facts = facts,
       nwits = length wits, wits = wits, rel = rel, pred = pred};

fun map_bnf f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
  (BNF {name = name, T = T, live = live, lives = lives, lives' = lives',
  dead = dead, deads = deads, map = map, sets = sets, bd = bd,
  axioms = axioms, defs = defs, facts = facts,
  nwits = nwits, wits = wits, rel = rel, pred = pred}) =
  BNF {name = f1 name, T = f2 T,
       live = f3 live, lives = f4 lives, lives' = f5 lives', dead = f6 dead, deads = f7 deads,
       map = f8 map, sets = f9 sets, bd = f10 bd,
       axioms = f11 axioms, defs = f12 defs, facts = f13 facts,
       nwits = f14 nwits, wits = f15 wits, rel = f16 rel, pred = f17 pred};

fun morph_bnf phi =
  let
    val Tphi = Morphism.typ phi;
    val tphi = Morphism.term phi;
  in
    map_bnf (Morphism.binding phi) Tphi I (map Tphi) (map Tphi) I (map Tphi) tphi (map tphi) tphi
      (morph_axioms phi) (morph_defs phi) (morph_facts phi) I (map (morph_witness phi)) tphi tphi
  end;

fun morph_bnf_defs phi = map_bnf I I I I I I I I I I I (morph_defs phi) I I I I I;

fun permute_deads perm = map_bnf I I I I I I perm I I I I I I I I I I;

val transfer_bnf = morph_bnf o Morphism.transfer_morphism;

structure Data = Generic_Data
(
  type T = bnf Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (K true) data;
);

fun bnf_of_generic context =
  Option.map (transfer_bnf (Context.theory_of context)) o Symtab.lookup (Data.get context);

val bnf_of = bnf_of_generic o Context.Proof;
val bnf_of_global = bnf_of_generic o Context.Theory;


(* Utilities *)

fun normalize_set insts instA set =
  let
    val (T, T') = dest_funT (fastype_of set);
    val A = fst (Term.dest_TVar (HOLogic.dest_setT T'));
    val params = Term.add_tvar_namesT T [];
  in Term.subst_TVars ((A :: params) ~~ (instA :: insts)) set end;

fun normalize_rel ctxt instTs instA instB rel =
  let
    val thy = Proof_Context.theory_of ctxt;
    val tyenv =
      Sign.typ_match thy (fastype_of rel, Library.foldr (op -->) (instTs, mk_pred2T instA instB))
        Vartab.empty;
  in Envir.subst_term (tyenv, Vartab.empty) rel end
  handle Type.TYPE_MATCH => error "Bad relator";

fun normalize_pred ctxt instTs instA pred =
  let
    val thy = Proof_Context.theory_of ctxt;
    val tyenv =
      Sign.typ_match thy (fastype_of pred, Library.foldr (op -->) (instTs, mk_pred1T instA))
        Vartab.empty;
  in Envir.subst_term (tyenv, Vartab.empty) pred end
  handle Type.TYPE_MATCH => error "Bad predicator";

fun normalize_wit insts CA As wit =
  let
    fun strip_param (Ts, T as Type (\<^type_name>\<open>fun\<close>, [T1, T2])) =
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

fun mk_map live Ts Us t =
  let val (Type (_, Ts0), Type (_, Us0)) = strip_typeN (live + 1) (fastype_of t) |>> List.last in
    Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) t
  end;

fun mk_pred Ts t =
  let val Type (_, Ts0) = domain_type (body_fun_type (fastype_of t)) in
    Term.subst_atomic_types (Ts0 ~~ Ts) t
  end;
val mk_set = mk_pred;

fun mk_rel live Ts Us t =
  let val [Type (_, Ts0), Type (_, Us0)] = binder_types (snd (strip_typeN live (fastype_of t))) in
    Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) t
  end;

fun build_map_or_rel mk const of_bnf dest pre_cst_table ctxt simple_Ts simple_Us build_simple =
  let
    fun build (TU as (T, U)) =
      if exists (curry (op =) T) simple_Ts orelse exists (curry (op =) U) simple_Us then
        build_simple TU
      else if T = U andalso not (exists_subtype_in simple_Ts T) andalso
          not (exists_subtype_in simple_Us U) then
        const T
      else
        (case TU of
          (Type (s, Ts), Type (s', Us)) =>
          if s = s' then
            let
              fun recurse (live, cst0) =
                let
                  val cst = mk live Ts Us cst0;
                  val TUs' = map dest (fst (strip_typeN live (fastype_of cst)));
                in Term.list_comb (cst, map build TUs') end;
            in
              (case AList.lookup (op =) pre_cst_table s of
                NONE =>
                (case bnf_of ctxt s of
                  SOME bnf => recurse (live_of_bnf bnf, of_bnf bnf)
                | NONE => build_simple TU)
              | SOME entry => recurse entry)
            end
          else
            build_simple TU
        | _ => build_simple TU);
  in build end;

val build_map = build_map_or_rel mk_map HOLogic.id_const map_of_bnf dest_funT
  [(\<^type_name>\<open>set\<close>, (1, \<^term>\<open>image\<close>))];
val build_rel = build_map_or_rel mk_rel HOLogic.eq_const rel_of_bnf dest_pred2T o append
  [(\<^type_name>\<open>set\<close>, (1, \<^term>\<open>rel_set\<close>)), (\<^type_name>\<open>fun\<close>, (2, \<^term>\<open>rel_fun\<close>))];

fun build_set ctxt A =
  let
    fun build T =
      Abs (Name.uu, T,
        if T = A then
          HOLogic.mk_set A [Bound 0]
        else
          (case T of
            Type (s, Ts) =>
            let
              val sets = map (mk_set Ts) (sets_of_bnf (the (bnf_of ctxt s)))
                |> filter (exists_subtype_in [A] o range_type o fastype_of);
              val set_apps = map (fn set => Term.betapply (set, Bound 0)) sets;

              fun recurse set_app =
                let val Type (\<^type_name>\<open>set\<close>, [elemT]) = fastype_of set_app in
                  if elemT = A then set_app else mk_UNION set_app (build elemT)
                end;
            in
              if null set_apps then HOLogic.mk_set A []
              else Library.foldl1 mk_union (map recurse set_apps)
            end
          | _ => HOLogic.mk_set A []));
  in build end;

fun map_flattened_map_args ctxt s map_args fs =
  let
    val flat_fs = flatten_type_args_of_bnf (the (bnf_of ctxt s)) Term.dummy fs;
    val flat_fs' = map_args flat_fs;
  in
    permute_like_unique (op aconv) flat_fs fs flat_fs'
  end;


(* Names *)

val mapN = "map";
val setN = "set";
fun mk_setN i = setN ^ nonzero_string_of_int i;
val bdN = "bd";
val witN = "wit";
fun mk_witN i = witN ^ nonzero_string_of_int i;
val relN = "rel";
val predN = "pred";

val bd_Card_orderN = "bd_Card_order";
val bd_CinfiniteN = "bd_Cinfinite";
val bd_CnotzeroN = "bd_Cnotzero";
val bd_card_orderN = "bd_card_order";
val bd_cinfiniteN = "bd_cinfinite";
val collect_set_mapN = "collect_set_map";
val in_bdN = "in_bd";
val in_monoN = "in_mono";
val in_relN = "in_rel";
val inj_mapN = "inj_map";
val inj_map_strongN = "inj_map_strong";
val map_comp0N = "map_comp0";
val map_compN = "map_comp";
val map_cong0N = "map_cong0";
val map_congN = "map_cong";
val map_cong_simpN = "map_cong_simp";
val map_cong_predN = "map_cong_pred";
val map_id0N = "map_id0";
val map_idN = "map_id";
val map_identN = "map_ident";
val map_transferN = "map_transfer";
val pred_mono_strong0N = "pred_mono_strong0";
val pred_mono_strongN = "pred_mono_strong";
val pred_monoN = "pred_mono";
val pred_transferN = "pred_transfer";
val pred_TrueN = "pred_True";
val pred_mapN = "pred_map";
val pred_relN = "pred_rel";
val pred_setN = "pred_set";
val pred_congN = "pred_cong";
val pred_cong_simpN = "pred_cong_simp";
val rel_GrpN = "rel_Grp";
val rel_comppN = "rel_compp";
val rel_compp_GrpN = "rel_compp_Grp";
val rel_congN = "rel_cong";
val rel_cong_simpN = "rel_cong_simp";
val rel_conversepN = "rel_conversep";
val rel_eqN = "rel_eq";
val rel_eq_onpN = "rel_eq_onp";
val rel_flipN = "rel_flip";
val rel_mapN = "rel_map";
val rel_monoN = "rel_mono";
val rel_mono_strong0N = "rel_mono_strong0";
val rel_mono_strongN = "rel_mono_strong";
val rel_reflN = "rel_refl";
val rel_refl_strongN = "rel_refl_strong";
val rel_reflpN = "rel_reflp";
val rel_sympN = "rel_symp";
val rel_transferN = "rel_transfer";
val rel_transpN = "rel_transp";
val set_bdN = "set_bd";
val set_map0N = "set_map0";
val set_mapN = "set_map";
val set_transferN = "set_transfer";

datatype inline_policy = Dont_Inline | Hardly_Inline | Smart_Inline | Do_Inline;

datatype fact_policy = Dont_Note | Note_Some | Note_All;

val bnf_internals = Attrib.setup_config_bool \<^binding>\<open>bnf_internals\<close> (K false);
val bnf_timing = Attrib.setup_config_bool \<^binding>\<open>bnf_timing\<close> (K false);

fun user_policy policy ctxt = if Config.get ctxt bnf_internals then Note_All else policy;

val smart_max_inline_term_size = 25; (*FUDGE*)

fun note_bnf_thms fact_policy qualify0 bnf_b bnf lthy =
  let
    val axioms = axioms_of_bnf bnf;
    val facts = facts_of_bnf bnf;
    val wits = wits_of_bnf bnf;
    val qualify =
      let val qs = Binding.path_of bnf_b;
      in fold_rev (fn (s, mand) => Binding.qualify mand s) qs #> qualify0 end;

    fun note_if_note_all (noted0, lthy0) =
      let
        val witNs = if length wits = 1 then [witN] else map mk_witN (1 upto length wits);
        val notes =
          [(bd_card_orderN, [#bd_card_order axioms]),
           (bd_cinfiniteN, [#bd_cinfinite axioms]),
           (bd_Card_orderN, [#bd_Card_order facts]),
           (bd_CinfiniteN, [#bd_Cinfinite facts]),
           (bd_CnotzeroN, [#bd_Cnotzero facts]),
           (collect_set_mapN, [Lazy.force (#collect_set_map facts)]),
           (in_bdN, [Lazy.force (#in_bd facts)]),
           (in_monoN, [Lazy.force (#in_mono facts)]),
           (map_comp0N, [#map_comp0 axioms]),
           (rel_mono_strong0N, [Lazy.force (#rel_mono_strong0 facts)]),
           (pred_mono_strong0N, [Lazy.force (#pred_mono_strong0 facts)]),
           (set_map0N, #set_map0 axioms),
           (set_bdN, #set_bd axioms)] @
          (witNs ~~ wit_thmss_of_bnf bnf)
          |> map (fn (thmN, thms) =>
            ((qualify (Binding.qualify true (Binding.name_of bnf_b) (Binding.name thmN)), []),
             [(thms, [])]));
      in
        Local_Theory.notes notes lthy0 |>> append noted0
      end;

    fun note_unless_dont_note (noted0, lthy0) =
      let
        val notes =
          [(in_relN, [Lazy.force (#in_rel facts)], []),
           (inj_mapN, [Lazy.force (#inj_map facts)], []),
           (inj_map_strongN, [Lazy.force (#inj_map_strong facts)], []),
           (map_compN, [Lazy.force (#map_comp facts)], []),
           (map_cong0N, [#map_cong0 axioms], []),
           (map_congN, [Lazy.force (#map_cong facts)], fundefcong_attrs),
           (map_cong_simpN, [Lazy.force (#map_cong_simp facts)], []),
           (map_cong_predN, [Lazy.force (#map_cong_pred facts)], []),
           (map_idN, [Lazy.force (#map_id facts)], []),
           (map_id0N, [#map_id0 axioms], []),
           (map_transferN, [Lazy.force (#map_transfer facts)], []),
           (map_identN, [Lazy.force (#map_ident facts)], []),
           (pred_mono_strongN, [Lazy.force (#pred_mono_strong facts)], []),
           (pred_monoN, [Lazy.force (#pred_mono facts)], []),
           (pred_congN, [Lazy.force (#pred_cong facts)], fundefcong_attrs),
           (pred_cong_simpN, [Lazy.force (#pred_cong_simp facts)], []),
           (pred_mapN, [Lazy.force (#pred_map facts)], []),
           (pred_relN, [Lazy.force (#pred_rel facts)], []),
           (pred_transferN, [Lazy.force (#pred_transfer facts)], []),
           (pred_TrueN, [Lazy.force (#pred_True facts)], []),
           (pred_setN, [#pred_set axioms], []),
           (rel_comppN, [Lazy.force (#rel_OO facts)], []),
           (rel_compp_GrpN, no_refl [#rel_OO_Grp axioms], []),
           (rel_conversepN, [Lazy.force (#rel_conversep facts)], []),
           (rel_eqN, [Lazy.force (#rel_eq facts)], []),
           (rel_eq_onpN, [Lazy.force (#rel_eq_onp facts)], []),
           (rel_flipN, [Lazy.force (#rel_flip facts)], []),
           (rel_GrpN, [Lazy.force (#rel_Grp facts)], []),
           (rel_mapN, Lazy.force (#rel_map facts), []),
           (rel_monoN, [Lazy.force (#rel_mono facts)], mono_attrs),
           (rel_mono_strongN, [Lazy.force (#rel_mono_strong facts)], []),
           (rel_congN, [Lazy.force (#rel_cong facts)], fundefcong_attrs),
           (rel_cong_simpN, [Lazy.force (#rel_cong_simp facts)], []),
           (rel_reflN, [Lazy.force (#rel_refl facts)], []),
           (rel_refl_strongN, [Lazy.force (#rel_refl_strong facts)], []),
           (rel_reflpN, [Lazy.force (#rel_reflp facts)], []),
           (rel_sympN, [Lazy.force (#rel_symp facts)], []),
           (rel_transpN, [Lazy.force (#rel_transp facts)], []),
           (rel_transferN, [Lazy.force (#rel_transfer facts)], []),
           (set_mapN, map Lazy.force (#set_map facts), []),
           (set_transferN, Lazy.force (#set_transfer facts), [])]
          |> filter_out (null o #2)
          |> map (fn (thmN, thms, attrs) =>
            ((qualify (Binding.qualify true (Binding.name_of bnf_b) (Binding.name thmN)), attrs),
             [(thms, [])]));
      in
        Local_Theory.notes notes lthy0 |>> append noted0
      end;
  in
    ([], lthy)
    |> fact_policy = Note_All ? note_if_note_all
    |> fact_policy <> Dont_Note ? note_unless_dont_note
    |>> (fn [] => bnf | noted => morph_bnf (substitute_noted_thm noted) bnf)
  end;

fun note_bnf_defs bnf lthy =
  let
    fun mk_def_binding cst_of =
      Thm.def_binding (Binding.qualified_name (dest_Const (cst_of bnf) |> fst));
    val notes =
      [(mk_def_binding map_of_bnf, map_def_of_bnf bnf),
       (mk_def_binding rel_of_bnf, rel_def_of_bnf bnf),
       (mk_def_binding pred_of_bnf, pred_def_of_bnf bnf)] @
      @{map 2} (pair o mk_def_binding o K) (sets_of_bnf bnf) (set_defs_of_bnf bnf)
      |> map (fn (b, thm) => ((b, []), [([thm], [])]));
  in
    lthy
    |> Local_Theory.notes notes
    |>> (fn noted => morph_bnf (substitute_noted_thm noted) bnf)
  end;

fun mk_wit_goals zs bs sets (I, wit) =
  let
    val xs = map (nth bs) I;
    fun wit_goal i =
      let
        val z = nth zs i;
        val set_wit = nth sets i $ Term.list_comb (wit, xs);
        val concl = HOLogic.mk_Trueprop
          (if member (op =) I i then HOLogic.mk_eq (z, nth bs i) else \<^term>\<open>False\<close>);
      in
        fold_rev Logic.all (z :: xs) (Logic.mk_implies (mk_Trueprop_mem (z, set_wit), concl))
      end;
  in
    map wit_goal (0 upto length sets - 1)
  end;


(* Define new BNFs *)

fun define_bnf_consts const_policy fact_policy internal Ds_opt map_b rel_b pred_b set_bs
    (((((((bnf_b, T_rhs), map_rhs), set_rhss), bd_rhs), wit_rhss), rel_rhs_opt), pred_rhs_opt)
    no_defs_lthy =
  let
    val live = length set_rhss;

    val def_qualify = Binding.qualify false (Binding.name_of bnf_b);

    fun mk_prefix_binding pre = Binding.prefix_name (pre ^ "_") bnf_b;

    fun maybe_define user_specified (b, rhs) lthy =
      let
        val inline =
          (user_specified orelse fact_policy = Dont_Note) andalso
          (case const_policy of
            Dont_Inline => false
          | Hardly_Inline => Term.is_Free rhs orelse Term.is_Const rhs
          | Smart_Inline => Term.size_of_term rhs <= smart_max_inline_term_size
          | Do_Inline => true);
      in
        if inline then
          ((rhs, Drule.reflexive_thm), lthy)
        else
          let val b = b () in
            apfst (apsnd snd)
              ((if internal then Local_Theory.define_internal else Local_Theory.define)
                ((b, NoSyn), ((Binding.concealed (Thm.def_binding b), []), rhs)) lthy)
          end
      end;

    val map_bind_def =
      (fn () => def_qualify (if Binding.is_empty map_b then mk_prefix_binding mapN else map_b),
         map_rhs);
    val set_binds_defs =
      let
        fun set_name i get_b =
          (case try (nth set_bs) (i - 1) of
            SOME b => if Binding.is_empty b then get_b else K b
          | NONE => get_b) #> def_qualify;
        val bs = if live = 1 then [set_name 1 (fn () => mk_prefix_binding setN)]
          else map (fn i => set_name i (fn () => mk_prefix_binding (mk_setN i))) (1 upto live);
      in bs ~~ set_rhss end;
    val bd_bind_def = (fn () => def_qualify (mk_prefix_binding bdN), bd_rhs);

    val ((((bnf_map_term, raw_map_def),
      (bnf_set_terms, raw_set_defs)),
      (bnf_bd_term, raw_bd_def)), (lthy, lthy_old)) =
        no_defs_lthy
        |> (snd o Local_Theory.begin_nested)
        |> maybe_define true map_bind_def
        ||>> apfst split_list o fold_map (maybe_define true) set_binds_defs
        ||>> maybe_define true bd_bind_def
        ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;

    val bnf_map_def = Morphism.thm phi raw_map_def;
    val bnf_set_defs = map (Morphism.thm phi) raw_set_defs;
    val bnf_bd_def = Morphism.thm phi raw_bd_def;

    val bnf_map = Morphism.term phi bnf_map_term;

    (*TODO: handle errors*)
    (*simple shape analysis of a map function*)
    val ((alphas, betas), (Calpha, _)) =
      fastype_of bnf_map
      |> strip_typeN live
      |>> map_split dest_funT
      ||> dest_funT
      handle TYPE _ => error "Bad map function";

    val Calpha_params = map TVar (Term.add_tvarsT Calpha []);

    val bnf_T = Morphism.typ phi T_rhs;
    val bad_args = Term.add_tfreesT bnf_T [];
    val _ = null bad_args orelse error ("Locally fixed type arguments " ^
      commas_quote (map (Syntax.string_of_typ no_defs_lthy o TFree) bad_args));

    val bnf_sets =
      map2 (normalize_set Calpha_params) alphas (map (Morphism.term phi) bnf_set_terms);
    val bnf_bd =
      Term.subst_TVars (Term.add_tvar_namesT bnf_T [] ~~ Calpha_params)
        (Morphism.term phi bnf_bd_term);

    (*TODO: assert Ds = (TVars of bnf_map) \ (alphas @ betas) as sets*)
    val deads = (case Ds_opt of
      NONE => subtract (op =) (alphas @ betas) (map TVar (Term.add_tvars bnf_map []))
    | SOME Ds => map (Morphism.typ phi) Ds);

    (*TODO: further checks of type of bnf_map*)
    (*TODO: check types of bnf_sets*)
    (*TODO: check type of bnf_bd*)
    (*TODO: check type of bnf_rel*)

    fun mk_bnf_map Ds As' Bs' =
      Term.subst_atomic_types ((deads ~~ Ds) @ (alphas ~~ As') @ (betas ~~ Bs')) bnf_map;
    fun mk_bnf_t Ds As' = Term.subst_atomic_types ((deads ~~ Ds) @ (alphas ~~ As'));
    fun mk_bnf_T Ds As' = Term.typ_subst_atomic ((deads ~~ Ds) @ (alphas ~~ As'));

    val (((As, Bs), unsorted_Ds), names_lthy) = lthy
      |> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees (length deads);

    val Ds = map2 (resort_tfree_or_tvar o Type.sort_of_atyp) deads unsorted_Ds;

    val RTs = map2 (curry HOLogic.mk_prodT) As Bs;
    val pred2RTs = map2 mk_pred2T As Bs;
    val (Rs, Rs') = names_lthy |> mk_Frees' "R" pred2RTs |> fst;
    val CA = mk_bnf_T Ds As Calpha;
    val CR = mk_bnf_T Ds RTs Calpha;
    val setRs =
      @{map 3} (fn R => fn T => fn U =>
          HOLogic.Collect_const (HOLogic.mk_prodT (T, U)) $ HOLogic.mk_case_prod R) Rs As Bs;

    (*Grp (in (Collect (split R1) .. Collect (split Rn))) (map fst .. fst)^--1 OO
      Grp (in (Collect (split R1) .. Collect (split Rn))) (map snd .. snd)*)
    val rel_spec =
      let
        val map1 = Term.list_comb (mk_bnf_map Ds RTs As, map fst_const RTs);
        val map2 = Term.list_comb (mk_bnf_map Ds RTs Bs, map snd_const RTs);
        val bnf_in = mk_in setRs (map (mk_bnf_t Ds RTs) bnf_sets) CR;
      in
        mk_rel_compp (mk_conversep (mk_Grp bnf_in map1), mk_Grp bnf_in map2)
        |> fold_rev Term.absfree Rs'
      end;

    val rel_rhs = the_default rel_spec rel_rhs_opt;

    val rel_bind_def =
      (fn () => def_qualify (if Binding.is_empty rel_b then mk_prefix_binding relN else rel_b),
         rel_rhs);

    val pred_spec =
      if live = 0 then Term.absdummy (mk_bnf_T Ds As Calpha) \<^term>\<open>True\<close> else
      let
        val sets = map (mk_bnf_t Ds As) bnf_sets;
        val argTs = map mk_pred1T As;
        val T = mk_bnf_T Ds As Calpha;
        val ((Ps, Ps'), x) = lthy
          |> mk_Frees' "P" argTs
          ||>> yield_singleton (mk_Frees "x") T
          |> fst;
        val conjs = map2 (fn set => fn P => mk_Ball (set $ x) P) sets Ps;
      in
        fold_rev Term.absfree Ps'
          (Term.absfree (dest_Free x) (Library.foldr1 HOLogic.mk_conj conjs))
      end;

    val pred_rhs = the_default pred_spec pred_rhs_opt;

    val pred_bind_def =
      (fn () => def_qualify (if Binding.is_empty pred_b then mk_prefix_binding predN else pred_b),
         pred_rhs);

    val wit_rhss =
      if null wit_rhss then
        [fold_rev Term.absdummy As (Term.list_comb (mk_bnf_map Ds As As,
          map2 (fn T => fn i => Term.absdummy T (Bound i)) As (live downto 1)) $
          Const (\<^const_name>\<open>undefined\<close>, CA))]
      else wit_rhss;
    val nwits = length wit_rhss;
    val wit_binds_defs =
      let
        val bs = if nwits = 1 then [fn () => def_qualify (mk_prefix_binding witN)]
          else map (fn i => fn () => def_qualify (mk_prefix_binding (mk_witN i))) (1 upto nwits);
      in bs ~~ wit_rhss end;

    val ((((bnf_rel_term, raw_rel_def), (bnf_pred_term, raw_pred_def)),
        (bnf_wit_terms, raw_wit_defs)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> maybe_define (is_some rel_rhs_opt) rel_bind_def
      ||>> maybe_define (is_some pred_rhs_opt) pred_bind_def
      ||>> apfst split_list o fold_map (maybe_define (not (null wit_rhss))) wit_binds_defs
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val bnf_rel_def = Morphism.thm phi raw_rel_def;
    val bnf_rel = Morphism.term phi bnf_rel_term;
    fun mk_bnf_rel Ds As' Bs' =
      normalize_rel lthy (map2 mk_pred2T As' Bs') (mk_bnf_T Ds As' Calpha) (mk_bnf_T Ds Bs' Calpha)
        bnf_rel;

    val bnf_pred_def = Morphism.thm phi raw_pred_def;
    val bnf_pred = Morphism.term phi bnf_pred_term;
    fun mk_bnf_pred Ds As' =
      normalize_pred lthy (map mk_pred1T As') (mk_bnf_T Ds As' Calpha) bnf_pred;

    val bnf_wit_defs = map (Morphism.thm phi) raw_wit_defs;
    val bnf_wits =
      map (normalize_wit Calpha_params Calpha alphas o Morphism.term phi) bnf_wit_terms;

    fun mk_rel_spec Ds' As' Bs' =
      Term.subst_atomic_types ((Ds ~~ Ds') @ (As ~~ As') @ (Bs ~~ Bs')) rel_spec;

    fun mk_pred_spec Ds' As' =
      Term.subst_atomic_types ((Ds ~~ Ds') @ (As ~~ As')) pred_spec;
  in
    (((alphas, betas, deads, Calpha),
     (bnf_map, bnf_sets, bnf_bd, bnf_wits, bnf_rel, bnf_pred),
     (bnf_map_def, bnf_set_defs, bnf_bd_def, bnf_wit_defs, bnf_rel_def, bnf_pred_def),
     (mk_bnf_map, mk_bnf_t, mk_bnf_T, mk_bnf_rel, mk_bnf_pred, mk_rel_spec, mk_pred_spec)), lthy)
  end;

fun prepare_def const_policy mk_fact_policy internal qualify prep_typ prep_term Ds_opt map_b rel_b
  pred_b set_bs (((((((raw_bnf_b, raw_bnf_T), raw_map), raw_sets), raw_bd), raw_wits), raw_rel_opt),
    raw_pred_opt) no_defs_lthy =
  let
    val fact_policy = mk_fact_policy no_defs_lthy;
    val bnf_b = qualify raw_bnf_b;
    val live = length raw_sets;

    val T_rhs = prep_typ no_defs_lthy raw_bnf_T;
    val map_rhs = prep_term no_defs_lthy raw_map;
    val set_rhss = map (prep_term no_defs_lthy) raw_sets;
    val bd_rhs = prep_term no_defs_lthy raw_bd;
    val wit_rhss = map (prep_term no_defs_lthy) raw_wits;
    val rel_rhs_opt = Option.map (prep_term no_defs_lthy) raw_rel_opt;
    val pred_rhs_opt = Option.map (prep_term no_defs_lthy) raw_pred_opt;

    fun err T =
      error ("Trying to register the type " ^ quote (Syntax.string_of_typ no_defs_lthy T) ^
        " as unnamed BNF");

    val (bnf_b, key) =
      if Binding.is_empty bnf_b then
        (case T_rhs of
          Type (C, Ts) =>
          if forall (can dest_TFree) Ts andalso not (has_duplicates (op =) Ts) then
            (Binding.qualified_name C, C)
          else
            err T_rhs
        | T => err T)
      else
        (bnf_b, Local_Theory.full_name no_defs_lthy bnf_b);

    val (((alphas, betas, deads, Calpha),
     (bnf_map, bnf_sets, bnf_bd, bnf_wits, bnf_rel, bnf_pred),
     (bnf_map_def, bnf_set_defs, bnf_bd_def, bnf_wit_defs, bnf_rel_def, bnf_pred_def),
     (mk_bnf_map_Ds, mk_bnf_t_Ds, mk_bnf_T_Ds, _, _, mk_rel_spec, mk_pred_spec)), lthy) =
       define_bnf_consts const_policy fact_policy internal Ds_opt map_b rel_b pred_b set_bs
         (((((((bnf_b, T_rhs), map_rhs), set_rhss), bd_rhs), wit_rhss), rel_rhs_opt), pred_rhs_opt)
         no_defs_lthy;

    val dead = length deads;

    val (((((((As', Bs'), Cs), unsorted_Ds), Es), B1Ts), B2Ts), (Ts, T)) = lthy
      |> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees dead
      ||>> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees live
      ||> fst o mk_TFrees 1
      ||> the_single
      ||> `(replicate live);

    val Ds = map2 (resort_tfree_or_tvar o Type.sort_of_atyp) deads unsorted_Ds;

    val mk_bnf_map = mk_bnf_map_Ds Ds;
    val mk_bnf_t = mk_bnf_t_Ds Ds;
    val mk_bnf_T = mk_bnf_T_Ds Ds;

    val pred1PTs = map mk_pred1T As';
    val pred1QTs = map mk_pred1T Bs';
    val pred2RTs = map2 mk_pred2T As' Bs';
    val pred2RTsAsCs = map2 mk_pred2T As' Cs;
    val pred2RTsBsCs = map2 mk_pred2T Bs' Cs;
    val pred2RTsBsEs = map2 mk_pred2T Bs' Es;
    val pred2RTsCsBs = map2 mk_pred2T Cs Bs';
    val pred2RTsCsEs = map2 mk_pred2T Cs Es;
    val pred2RT's = map2 mk_pred2T Bs' As';
    val self_pred2RTs = map2 mk_pred2T As' As';
    val transfer_domRTs = map2 mk_pred2T As' B1Ts;
    val transfer_ranRTs = map2 mk_pred2T Bs' B2Ts;

    val CA' = mk_bnf_T As' Calpha;
    val CB' = mk_bnf_T Bs' Calpha;
    val CC' = mk_bnf_T Cs Calpha;
    val CE' = mk_bnf_T Es Calpha;
    val CB1 = mk_bnf_T B1Ts Calpha;
    val CB2 = mk_bnf_T B2Ts Calpha;

    val bnf_map_AsAs = mk_bnf_map As' As';
    val bnf_map_AsBs = mk_bnf_map As' Bs';
    val bnf_map_AsCs = mk_bnf_map As' Cs;
    val bnf_map_BsCs = mk_bnf_map Bs' Cs;
    val bnf_sets_As = map (mk_bnf_t As') bnf_sets;
    val bnf_sets_Bs = map (mk_bnf_t Bs') bnf_sets;
    val bnf_bd_As = mk_bnf_t As' bnf_bd;
    fun mk_bnf_rel RTs CA CB = normalize_rel lthy RTs CA CB bnf_rel;
    fun mk_bnf_pred PTs CA = normalize_pred lthy PTs CA bnf_pred;

    val ((((((((((((((((((((((((((fs, fs'), gs), hs), is), x), x'), y), y'), zs), zs'), ys), As),
      As_copy), bs), (Ps, Ps')), Ps_copy), Qs), Rs), Rs_copy), Ss), S_AsCs), S_CsBs), S_BsEs),
      transfer_domRs), transfer_ranRs), _) = lthy
      |> mk_Frees "f" (map2 (curry op -->) As' Bs')
      ||>> mk_Frees "f" (map2 (curry op -->) As' Bs')
      ||>> mk_Frees "g" (map2 (curry op -->) Bs' Cs)
      ||>> mk_Frees "h" (map2 (curry op -->) As' Ts)
      ||>> mk_Frees "i" (map2 (curry op -->) As' Cs)
      ||>> yield_singleton (mk_Frees "x") CA'
      ||>> yield_singleton (mk_Frees "x") CA'
      ||>> yield_singleton (mk_Frees "y") CB'
      ||>> yield_singleton (mk_Frees "y") CB'
      ||>> mk_Frees "z" As'
      ||>> mk_Frees "z" As'
      ||>> mk_Frees "y" Bs'
      ||>> mk_Frees "A" (map HOLogic.mk_setT As')
      ||>> mk_Frees "A" (map HOLogic.mk_setT As')
      ||>> mk_Frees "b" As'
      ||>> mk_Frees' "P" pred1PTs
      ||>> mk_Frees "P" pred1PTs
      ||>> mk_Frees "Q" pred1QTs
      ||>> mk_Frees "R" pred2RTs
      ||>> mk_Frees "R" pred2RTs
      ||>> mk_Frees "S" pred2RTsBsCs
      ||>> mk_Frees "S" pred2RTsAsCs
      ||>> mk_Frees "S" pred2RTsCsBs
      ||>> mk_Frees "S" pred2RTsBsEs
      ||>> mk_Frees "R" transfer_domRTs
      ||>> mk_Frees "S" transfer_ranRTs;

    val fs_copy = map2 (retype_const_or_free o fastype_of) fs gs;
    val x_copy = retype_const_or_free CA' y';
    val y_copy = retype_const_or_free CB' x';

    val rel = mk_bnf_rel pred2RTs CA' CB';
    val pred = mk_bnf_pred pred1PTs CA';
    val pred' = mk_bnf_pred pred1QTs CB';
    val relCsEs = mk_bnf_rel pred2RTsCsEs CC' CE';
    val relAsAs = mk_bnf_rel self_pred2RTs CA' CA';
    val bnf_wit_As = map (apsnd (mk_bnf_t As')) bnf_wits;

    val map_id0_goal =
      let val bnf_map_app_id = Term.list_comb (bnf_map_AsAs, map HOLogic.id_const As') in
        mk_Trueprop_eq (bnf_map_app_id, HOLogic.id_const CA')
      end;

    val map_comp0_goal =
      let
        val bnf_map_app_comp = Term.list_comb (bnf_map_AsCs, map2 (curry HOLogic.mk_comp) gs fs);
        val comp_bnf_map_app = HOLogic.mk_comp
          (Term.list_comb (bnf_map_BsCs, gs), Term.list_comb (bnf_map_AsBs, fs));
      in
        fold_rev Logic.all (fs @ gs) (mk_Trueprop_eq (bnf_map_app_comp, comp_bnf_map_app))
      end;

    fun mk_map_cong_prem mk_implies x z set f f_copy =
      Logic.all z (mk_implies (mk_Trueprop_mem (z, set $ x), mk_Trueprop_eq (f $ z, f_copy $ z)));

    val map_cong0_goal =
      let
        val prems = @{map 4} (mk_map_cong_prem Logic.mk_implies x) zs bnf_sets_As fs fs_copy;
        val eq = mk_Trueprop_eq (Term.list_comb (bnf_map_AsBs, fs) $ x,
          Term.list_comb (bnf_map_AsBs, fs_copy) $ x);
      in
        fold_rev Logic.all (x :: fs @ fs_copy) (Logic.list_implies (prems, eq))
      end;

    val set_map0s_goal =
      let
        fun mk_goal setA setB f =
          let
            val set_comp_map = HOLogic.mk_comp (setB, Term.list_comb (bnf_map_AsBs, fs));
            val image_comp_set = HOLogic.mk_comp (mk_image f, setA);
          in
            fold_rev Logic.all fs (mk_Trueprop_eq (set_comp_map, image_comp_set))
          end;
      in
        @{map 3} mk_goal bnf_sets_As bnf_sets_Bs fs
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

    val relAsCs = mk_bnf_rel pred2RTsAsCs CA' CC';
    val relBsCs = mk_bnf_rel pred2RTsBsCs CB' CC';
    val relCsBs = mk_bnf_rel pred2RTsCsBs CC' CB';
    val rel_OO_lhs = Term.list_comb (relAsCs, map2 (curry mk_rel_compp) Rs Ss);
    val rel_OO_rhs = mk_rel_compp (Term.list_comb (rel, Rs), Term.list_comb (relBsCs, Ss));
    val le_rel_OO_goal =
      fold_rev Logic.all (Rs @ Ss) (HOLogic.mk_Trueprop (mk_leq rel_OO_rhs rel_OO_lhs));

    val rel_OO_Grp_goal = fold_rev Logic.all Rs (mk_Trueprop_eq (Term.list_comb (rel, Rs),
      Term.list_comb (mk_rel_spec Ds As' Bs', Rs)));

    val pred_set_goal = fold_rev Logic.all Ps (mk_Trueprop_eq (Term.list_comb (pred, Ps),
      Term.list_comb (mk_pred_spec Ds As', Ps)));

    val goals = zip_axioms map_id0_goal map_comp0_goal map_cong0_goal set_map0s_goal
      card_order_bd_goal cinfinite_bd_goal set_bds_goal le_rel_OO_goal rel_OO_Grp_goal pred_set_goal;

    val mk_wit_goals = mk_wit_goals bs zs bnf_sets_As;
    fun triv_wit_tac ctxt = mk_trivial_wit_tac ctxt bnf_wit_defs;

    val wit_goalss =
      (if null raw_wits then SOME triv_wit_tac else NONE, map mk_wit_goals bnf_wit_As);

    fun after_qed mk_wit_thms thms lthy =
      let
        val (axioms, nontriv_wit_thms) = apfst (mk_axioms live) (chop (length goals) thms);

        val bd_Card_order = #bd_card_order axioms RS @{thm conjunct2[OF card_order_on_Card_order]};
        val bd_Cinfinite = @{thm conjI} OF [#bd_cinfinite axioms, bd_Card_order];
        val bd_Cnotzero = bd_Cinfinite RS @{thm Cinfinite_Cnotzero};

        fun mk_collect_set_map () =
          let
            val defT = mk_bnf_T Ts Calpha --> HOLogic.mk_setT T;
            val collect_map = HOLogic.mk_comp (mk_collect (map (mk_bnf_t Ts) bnf_sets) defT,
              Term.list_comb (mk_bnf_map As' Ts, hs));
            val image_collect = mk_collect
              (map2 (fn h => fn set => HOLogic.mk_comp (mk_image h, set)) hs bnf_sets_As) defT;
            (*collect {set1 ... setm} o map f1 ... fm = collect {f1` o set1 ... fm` o setm}*)
            val goal = fold_rev Logic.all hs (mk_Trueprop_eq (collect_map, image_collect));
          in
            Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} =>
              mk_collect_set_map_tac ctxt (#set_map0 axioms))
            |> Thm.close_derivation \<^here>
          end;

        val collect_set_map = Lazy.lazy mk_collect_set_map;

        fun mk_in_mono () =
          let
            val prems_mono = map2 (HOLogic.mk_Trueprop oo mk_leq) As As_copy;
            val in_mono_goal =
              fold_rev Logic.all (As @ As_copy)
                (Logic.list_implies (prems_mono, HOLogic.mk_Trueprop
                  (mk_leq (mk_in As bnf_sets_As CA') (mk_in As_copy bnf_sets_As CA'))));
          in
            Goal.prove_sorry lthy [] [] in_mono_goal (fn {context = ctxt, prems = _} =>
              mk_in_mono_tac ctxt live)
            |> Thm.close_derivation \<^here>
          end;

        val in_mono = Lazy.lazy mk_in_mono;

        fun mk_in_cong () =
          let
            val prems_cong = map2 (curry mk_Trueprop_eq) As As_copy;
            val in_cong_goal =
              fold_rev Logic.all (As @ As_copy)
                (Logic.list_implies (prems_cong,
                  mk_Trueprop_eq (mk_in As bnf_sets_As CA', mk_in As_copy bnf_sets_As CA')));
          in
            Goal.prove_sorry lthy [] [] in_cong_goal
              (fn {context = ctxt, prems = _} => (TRY o hyp_subst_tac ctxt THEN' rtac ctxt refl) 1)
            |> Thm.close_derivation \<^here>
          end;

        val in_cong = Lazy.lazy mk_in_cong;

        val map_id = Lazy.lazy (fn () => mk_map_id (#map_id0 axioms));
        val map_ident0 = Lazy.lazy (fn () => mk_map_ident lthy (#map_id0 axioms));
        val map_ident = Lazy.lazy (fn () => mk_map_ident lthy (Lazy.force map_id));
        val map_comp = Lazy.lazy (fn () => mk_map_comp (#map_comp0 axioms));

        fun mk_map_cong mk_implies () =
          let
            val prem0 = mk_Trueprop_eq (x, x_copy);
            val prems = @{map 4} (mk_map_cong_prem mk_implies x_copy) zs bnf_sets_As fs fs_copy;
            val eq = mk_Trueprop_eq (Term.list_comb (bnf_map_AsBs, fs) $ x,
              Term.list_comb (bnf_map_AsBs, fs_copy) $ x_copy);
            val goal = fold_rev Logic.all (x :: x_copy :: fs @ fs_copy)
              (Logic.list_implies (prem0 :: prems, eq));
          in
            Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} =>
              unfold_thms_tac ctxt @{thms simp_implies_def} THEN
              mk_map_cong_tac ctxt (#map_cong0 axioms))
            |> Thm.close_derivation \<^here>
          end;

        val map_cong = Lazy.lazy (mk_map_cong Logic.mk_implies);
        val map_cong_simp = Lazy.lazy (mk_map_cong (fn (a, b) => \<^term>\<open>simp_implies\<close> $ a $ b));

        fun mk_inj_map () =
          let
            val prems = map (HOLogic.mk_Trueprop o mk_inj) fs;
            val concl = HOLogic.mk_Trueprop (mk_inj (Term.list_comb (bnf_map_AsBs, fs)));
            val goal = fold_rev Logic.all fs (Logic.list_implies (prems, concl));
          in
            Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} =>
              mk_inj_map_tac ctxt live (Lazy.force map_id) (Lazy.force map_comp) (#map_cong0 axioms)
                (Lazy.force map_cong))
            |> Thm.close_derivation \<^here>
          end;

        val inj_map = Lazy.lazy mk_inj_map;

        val set_map = map (fn thm => Lazy.lazy (fn () => mk_set_map thm)) (#set_map0 axioms);

        val wit_thms =
          if null nontriv_wit_thms then mk_wit_thms (map Lazy.force set_map) else nontriv_wit_thms;

        fun mk_in_bd () =
          let
            val bdT = fst (dest_relT (fastype_of bnf_bd_As));
            val bdTs = replicate live bdT;
            val bd_bnfT = mk_bnf_T bdTs Calpha;
            val surj_imp_ordLeq_inst = (if live = 0 then TrueI else
              let
                val ranTs = map (fn AT => mk_sumT (AT, HOLogic.unitT)) As';
                val funTs = map (fn T => bdT --> T) ranTs;
                val ran_bnfT = mk_bnf_T ranTs Calpha;
                val (revTs, Ts) = `rev (bd_bnfT :: funTs);
                val cTs = map (SOME o Thm.ctyp_of lthy) [ran_bnfT,
                  Library.foldr1 HOLogic.mk_prodT Ts];
                val tinst = fold (fn T => fn t =>
                  HOLogic.mk_case_prod (Term.absdummy T t)) (tl revTs)
                    (Term.absdummy (hd revTs) (Term.list_comb (mk_bnf_map bdTs ranTs,
                      map Bound (live - 1 downto 0)) $ Bound live));
                val cts = [NONE, SOME (Thm.cterm_of lthy tinst)];
              in
                Thm.instantiate' cTs cts @{thm surj_imp_ordLeq}
              end);
            val bd = mk_cexp
              (if live = 0 then ctwo
                else mk_csum (Library.foldr1 (uncurry mk_csum) (map mk_card_of As)) ctwo)
              (mk_csum bnf_bd_As (mk_card_of (HOLogic.mk_UNIV bd_bnfT)));
            val in_bd_goal =
              fold_rev Logic.all As
                (HOLogic.mk_Trueprop (mk_ordLeq (mk_card_of (mk_in As bnf_sets_As CA')) bd));
          in
            Goal.prove_sorry lthy [] [] in_bd_goal
              (fn {context = ctxt, prems = _} => mk_in_bd_tac ctxt live surj_imp_ordLeq_inst
                (Lazy.force map_comp) (Lazy.force map_id) (#map_cong0 axioms)
                (map Lazy.force set_map) (#set_bd axioms) (#bd_card_order axioms)
                bd_Card_order bd_Cinfinite bd_Cnotzero)
            |> Thm.close_derivation \<^here>
          end;

        val in_bd = Lazy.lazy mk_in_bd;

        val rel_OO_Grp = #rel_OO_Grp axioms;
        val rel_OO_Grps = no_refl [rel_OO_Grp];

        fun mk_rel_Grp () =
          let
            val lhs = Term.list_comb (rel, map2 mk_Grp As fs);
            val rhs = mk_Grp (mk_in As bnf_sets_As CA') (Term.list_comb (bnf_map_AsBs, fs));
            val goal = fold_rev Logic.all (As @ fs) (mk_Trueprop_eq (lhs, rhs));
          in
            Goal.prove_sorry lthy [] [] goal
              (fn {context = ctxt, prems = _} => mk_rel_Grp_tac ctxt rel_OO_Grps (#map_id0 axioms)
                (#map_cong0 axioms) (Lazy.force map_id) (Lazy.force map_comp)
                (map Lazy.force set_map))
            |> Thm.close_derivation \<^here>
          end;

        val rel_Grp = Lazy.lazy mk_rel_Grp;

        fun mk_rel_prems f = map2 (HOLogic.mk_Trueprop oo f) Rs Rs_copy;
        fun mk_rel_concl f = HOLogic.mk_Trueprop
          (f (Term.list_comb (rel, Rs), Term.list_comb (rel, Rs_copy)));

        fun mk_rel_mono () =
          let
            val mono_prems = mk_rel_prems mk_leq;
            val mono_concl = mk_rel_concl (uncurry mk_leq);
          in
            Goal.prove_sorry lthy [] []
              (fold_rev Logic.all (Rs @ Rs_copy) (Logic.list_implies (mono_prems, mono_concl)))
              (fn {context = ctxt, prems = _} =>
                mk_rel_mono_tac ctxt rel_OO_Grps (Lazy.force in_mono))
            |> Thm.close_derivation \<^here>
          end;

        fun mk_rel_cong0 () =
          let
            val cong_prems = mk_rel_prems (curry HOLogic.mk_eq);
            val cong_concl = mk_rel_concl HOLogic.mk_eq;
          in
            Goal.prove_sorry lthy [] []
              (fold_rev Logic.all (Rs @ Rs_copy) (Logic.list_implies (cong_prems, cong_concl)))
              (fn {context = ctxt, prems = _} => (TRY o hyp_subst_tac ctxt THEN' rtac ctxt refl) 1)
            |> Thm.close_derivation \<^here>
          end;

        val rel_mono = Lazy.lazy mk_rel_mono;
        val rel_cong0 = Lazy.lazy mk_rel_cong0;

        fun mk_rel_eq () =
          Goal.prove_sorry lthy [] []
            (mk_Trueprop_eq (Term.list_comb (relAsAs, map HOLogic.eq_const As'),
              HOLogic.eq_const CA'))
            (fn {context = ctxt, prems = _} =>
              mk_rel_eq_tac ctxt live (Lazy.force rel_Grp) (Lazy.force rel_cong0) (#map_id0 axioms))
          |> Thm.close_derivation \<^here>;

        val rel_eq = Lazy.lazy mk_rel_eq;

        fun mk_rel_conversep () =
          let
            val relBsAs = mk_bnf_rel pred2RT's CB' CA';
            val lhs = Term.list_comb (relBsAs, map mk_conversep Rs);
            val rhs = mk_conversep (Term.list_comb (rel, Rs));
            val le_goal = fold_rev Logic.all Rs (HOLogic.mk_Trueprop (mk_leq lhs rhs));
            val le_thm = Goal.prove_sorry lthy [] [] le_goal
              (fn {context = ctxt, prems = _} => mk_rel_conversep_le_tac ctxt rel_OO_Grps
                (Lazy.force rel_eq) (#map_cong0 axioms) (Lazy.force map_comp)
                (map Lazy.force set_map))
              |> Thm.close_derivation \<^here>
            val goal = fold_rev Logic.all Rs (mk_Trueprop_eq (lhs, rhs));
          in
            Goal.prove_sorry lthy [] [] goal
              (fn {context = ctxt, prems = _} =>
                mk_rel_conversep_tac ctxt le_thm (Lazy.force rel_mono))
            |> Thm.close_derivation \<^here>
          end;

        val rel_conversep = Lazy.lazy mk_rel_conversep;

        fun mk_rel_OO () =
          Goal.prove_sorry lthy [] []
            (fold_rev Logic.all (Rs @ Ss) (HOLogic.mk_Trueprop (mk_leq rel_OO_lhs rel_OO_rhs)))
            (fn {context = ctxt, prems = _} => mk_rel_OO_le_tac ctxt rel_OO_Grps (Lazy.force rel_eq)
              (#map_cong0 axioms) (Lazy.force map_comp) (map Lazy.force set_map))
          |> Thm.close_derivation \<^here>
          |> (fn thm => @{thm antisym} OF [thm, #le_rel_OO axioms]);

        val rel_OO = Lazy.lazy mk_rel_OO;

        fun mk_in_rel () = trans OF [rel_OO_Grp, @{thm OO_Grp_alt}] RS @{thm predicate2_eqD};

        val in_rel = Lazy.lazy mk_in_rel;

        fun mk_rel_flip () =
          unfold_thms lthy @{thms conversep_iff}
            (Lazy.force rel_conversep RS @{thm predicate2_eqD});

        val rel_flip = Lazy.lazy mk_rel_flip;

        fun mk_rel_mono_strong0 () =
          let
            fun mk_prem setA setB R S a b =
              HOLogic.mk_Trueprop
                (mk_Ball (setA $ x) (Term.absfree (dest_Free a)
                  (mk_Ball (setB $ y) (Term.absfree (dest_Free b)
                    (HOLogic.mk_imp (R $ a $ b, S $ a $ b))))));
            val prems = HOLogic.mk_Trueprop (Term.list_comb (rel, Rs) $ x $ y) ::
              @{map 6} mk_prem bnf_sets_As bnf_sets_Bs Rs Rs_copy zs ys;
            val concl = HOLogic.mk_Trueprop (Term.list_comb (rel, Rs_copy) $ x $ y);
          in
            Goal.prove_sorry lthy [] []
              (fold_rev Logic.all (x :: y :: Rs @ Rs_copy) (Logic.list_implies (prems, concl)))
              (fn {context = ctxt, prems = _} => mk_rel_mono_strong0_tac ctxt (Lazy.force in_rel)
                (map Lazy.force set_map))
            |> Thm.close_derivation \<^here>
          end;

        val rel_mono_strong0 = Lazy.lazy mk_rel_mono_strong0;

        val rel_mono_strong = Lazy.map (Object_Logic.rulify lthy) rel_mono_strong0;

        fun mk_rel_cong_prem mk_implies x x' z z' set set' R R_copy =
          Logic.all z (Logic.all z'
            (mk_implies (mk_Trueprop_mem (z, set $ x), mk_implies (mk_Trueprop_mem (z', set' $ x'),
              mk_Trueprop_eq (R $ z $ z', R_copy $ z $ z')))));

        fun mk_rel_cong mk_implies () =
          let
            val prem0 = mk_Trueprop_eq (x, x_copy);
            val prem1 = mk_Trueprop_eq (y, y_copy);
            val prems = @{map 6} (mk_rel_cong_prem mk_implies x_copy y_copy)
              zs ys bnf_sets_As bnf_sets_Bs Rs Rs_copy;
            val eq = mk_Trueprop_eq (Term.list_comb (rel, Rs) $ x $ y,
              Term.list_comb (rel, Rs_copy) $ x_copy $ y_copy);
          in
            fold (Variable.add_free_names lthy) (eq :: prem0 :: prem1 :: prems) []
            |> (fn vars => Goal.prove_sorry lthy vars (prem0 :: prem1 :: prems) eq
              (fn {context = ctxt, prems} =>
                mk_rel_cong_tac ctxt (chop 2 prems) (Lazy.force rel_mono_strong)))
            |> Thm.close_derivation \<^here>
          end;

        val rel_cong = Lazy.lazy (mk_rel_cong Logic.mk_implies);
        val rel_cong_simp = Lazy.lazy (mk_rel_cong (fn (a, b) => \<^term>\<open>simp_implies\<close> $ a $ b));

        fun mk_pred_prems f = map2 (HOLogic.mk_Trueprop oo f) Ps Ps_copy;
        fun mk_pred_concl f = HOLogic.mk_Trueprop
          (f (Term.list_comb (pred, Ps), Term.list_comb (pred, Ps_copy)));

        fun mk_pred_cong0 () =
          let
            val cong_prems = mk_pred_prems (curry HOLogic.mk_eq);
            val cong_concl = mk_pred_concl HOLogic.mk_eq;
          in
            Goal.prove_sorry lthy [] []
              (fold_rev Logic.all (Ps @ Ps_copy) (Logic.list_implies (cong_prems, cong_concl)))
              (fn {context = ctxt, prems = _} => (TRY o hyp_subst_tac ctxt THEN' rtac ctxt refl) 1)
            |> Thm.close_derivation \<^here>
          end;

        val pred_cong0 = Lazy.lazy mk_pred_cong0;

        fun mk_rel_eq_onp () =
          let
            val lhs = Term.list_comb (relAsAs, map mk_eq_onp Ps);
            val rhs = mk_eq_onp (Term.list_comb (pred, Ps));
          in
            Goal.prove_sorry lthy (map fst Ps') [] (mk_Trueprop_eq (lhs, rhs))
              (fn {context = ctxt, prems = _} =>
                mk_rel_eq_onp_tac ctxt (#pred_set axioms) (#map_id0 axioms) (Lazy.force rel_Grp))
            |> Thm.close_derivation \<^here>
          end;

        val rel_eq_onp = Lazy.lazy mk_rel_eq_onp;
        val pred_rel = Lazy.map (fn thm => thm RS sym RS @{thm eq_onp_eqD}) rel_eq_onp;

        fun mk_pred_mono_strong0 () =
          let
            fun mk_prem setA P Q a =
              HOLogic.mk_Trueprop
                (mk_Ball (setA $ x) (Term.absfree (dest_Free a) (HOLogic.mk_imp (P $ a, Q $ a))));
            val prems = HOLogic.mk_Trueprop (Term.list_comb (pred, Ps) $ x) ::
              @{map 4} mk_prem bnf_sets_As Ps Ps_copy zs;
            val concl = HOLogic.mk_Trueprop (Term.list_comb (pred, Ps_copy) $ x);
          in
            Goal.prove_sorry lthy [] []
              (fold_rev Logic.all (x :: Ps @ Ps_copy) (Logic.list_implies (prems, concl)))
              (fn {context = ctxt, prems = _} =>
                mk_pred_mono_strong0_tac ctxt (Lazy.force pred_rel) (Lazy.force rel_mono_strong0))
            |> Thm.close_derivation \<^here>
          end;

        val pred_mono_strong0 = Lazy.lazy mk_pred_mono_strong0;

        val pred_mono_strong = Lazy.map (Object_Logic.rulify lthy) pred_mono_strong0;

        fun mk_pred_mono () =
          let
            val mono_prems = mk_pred_prems mk_leq;
            val mono_concl = mk_pred_concl (uncurry mk_leq);
          in
            Goal.prove_sorry lthy [] []
              (fold_rev Logic.all (Ps @ Ps_copy) (Logic.list_implies (mono_prems, mono_concl)))
              (fn {context = ctxt, prems = _} =>
                mk_pred_mono_tac ctxt (Lazy.force rel_eq_onp) (Lazy.force rel_mono))
            |> Thm.close_derivation \<^here>
          end;

        val pred_mono = Lazy.lazy mk_pred_mono;

        fun mk_pred_cong_prem mk_implies x z set P P_copy =
          Logic.all z
            (mk_implies (mk_Trueprop_mem (z, set $ x), mk_Trueprop_eq (P $ z, P_copy $ z)));

        fun mk_pred_cong mk_implies () =
          let
            val prem0 = mk_Trueprop_eq (x, x_copy);
            val prems = @{map 4} (mk_pred_cong_prem mk_implies x_copy) zs bnf_sets_As Ps Ps_copy;
            val eq = mk_Trueprop_eq (Term.list_comb (pred, Ps) $ x,
              Term.list_comb (pred, Ps_copy) $ x_copy);
          in
            fold (Variable.add_free_names lthy) (eq :: prem0 :: prems) []
            |> (fn vars => Goal.prove_sorry lthy vars (prem0 :: prems) eq
              (fn {context = ctxt, prems} =>
                mk_rel_cong_tac ctxt (chop 1 prems) (Lazy.force pred_mono_strong)))
            |> Thm.close_derivation \<^here>
          end;

        val pred_cong = Lazy.lazy (mk_pred_cong Logic.mk_implies);
        val pred_cong_simp = Lazy.lazy (mk_pred_cong (fn (a, b) => \<^term>\<open>simp_implies\<close> $ a $ b));

        fun mk_map_cong_pred () =
          let
            val prem0 = mk_Trueprop_eq (x, x_copy);
            fun mk_eq f g z = Term.absfree (dest_Free z) (HOLogic.mk_eq (f $ z, g $ z));
            val prem = HOLogic.mk_Trueprop
              (Term.list_comb (pred, @{map 3} mk_eq fs fs_copy zs) $ x_copy);
            val eq = mk_Trueprop_eq (Term.list_comb (bnf_map_AsBs, fs) $ x,
              Term.list_comb (bnf_map_AsBs, fs_copy) $ x_copy);
            val goal = fold_rev Logic.all (x :: x_copy :: fs @ fs_copy)
              (Logic.list_implies ([prem0, prem], eq));
          in
            Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} =>
              unfold_thms_tac ctxt [#pred_set axioms] THEN
              HEADGOAL (EVERY' [REPEAT_DETERM o etac ctxt conjE,
                etac ctxt (Lazy.force map_cong) THEN_ALL_NEW
                  (etac ctxt @{thm bspec} THEN' assume_tac ctxt)]))
            |> Thm.close_derivation \<^here>
          end;

        val map_cong_pred = Lazy.lazy mk_map_cong_pred;

        fun mk_rel_map () =
          let
            fun mk_goal lhs rhs =
              fold_rev Logic.all ([x, y] @ S_CsBs @ S_AsCs @ is @ gs) (mk_Trueprop_eq (lhs, rhs));

            val lhss =
              [Term.list_comb (relCsBs, S_CsBs) $ (Term.list_comb (bnf_map_AsCs, is) $ x) $ y,
               Term.list_comb (relAsCs, S_AsCs) $ x $ (Term.list_comb (bnf_map_BsCs, gs) $ y)];
            val rhss =
              [Term.list_comb (rel, @{map 3} (fn f => fn P => fn T =>
                 mk_vimage2p f (HOLogic.id_const T) $ P) is S_CsBs Bs') $ x $ y,
               Term.list_comb (rel, @{map 3} (fn f => fn P => fn T =>
                 mk_vimage2p (HOLogic.id_const T) f $ P) gs S_AsCs As') $ x $ y];
            val goals = map2 mk_goal lhss rhss;
          in
            goals
            |> map (fn goal => Goal.prove_sorry lthy [] [] goal
              (fn {context = ctxt, prems = _} =>
                 mk_rel_map0_tac ctxt live (Lazy.force rel_OO) (Lazy.force rel_conversep)
                  (Lazy.force rel_Grp) (Lazy.force map_id)))
            |> map (unfold_thms lthy @{thms vimage2p_def[of id, simplified id_apply]
                 vimage2p_def[of _ id, simplified id_apply]})
            |> map (Thm.close_derivation \<^here>)
          end;

        val rel_map = Lazy.lazy mk_rel_map;

        fun mk_rel_refl () = @{thm ge_eq_refl[OF ord_eq_le_trans]} OF
          [Lazy.force rel_eq RS sym, Lazy.force rel_mono OF (replicate live @{thm refl_ge_eq})];

        val rel_refl = Lazy.lazy mk_rel_refl;

        fun mk_rel_refl_strong () =
          (rule_by_tactic lthy (ALLGOALS (Object_Logic.full_atomize_tac lthy))
            ((Lazy.force rel_eq RS @{thm predicate2_eqD}) RS @{thm iffD2[OF _ refl]} RS
              Lazy.force rel_mono_strong)) OF
            (replicate live @{thm diag_imp_eq_le})

        val rel_refl_strong = Lazy.lazy mk_rel_refl_strong;

        fun mk_rel_preserves mk_prop prop_conv_thm thm () =
          let
            val Rs = map2 retype_const_or_free self_pred2RTs Rs;
            val prems = map (HOLogic.mk_Trueprop o mk_prop) Rs;
            val goal = HOLogic.mk_Trueprop (mk_prop (Term.list_comb (relAsAs, Rs)));
        val vars = fold (Variable.add_free_names lthy) (goal :: prems) [];
          in
            Goal.prove_sorry lthy vars [] (Logic.list_implies (prems, goal))
              (fn {context = ctxt, prems = _} =>
                unfold_thms_tac ctxt [prop_conv_thm] THEN
                HEADGOAL (rtac ctxt (Lazy.force thm RS sym RS @{thm ord_eq_le_trans})
                  THEN' rtac ctxt (Lazy.force rel_mono) THEN_ALL_NEW assume_tac ctxt))
            |> Thm.close_derivation \<^here>
          end;

        val rel_reflp = Lazy.lazy (mk_rel_preserves mk_reflp @{thm reflp_eq} rel_eq);
        val rel_symp = Lazy.lazy (mk_rel_preserves mk_symp @{thm symp_conversep} rel_conversep);
        val rel_transp = Lazy.lazy (mk_rel_preserves mk_transp @{thm transp_relcompp} rel_OO);

        fun mk_pred_True () =
          let
            val lhs = Term.list_comb (pred, map (fn T => absdummy T \<^term>\<open>True\<close>) As');
            val rhs = absdummy CA' \<^term>\<open>True\<close>;
            val goal = mk_Trueprop_eq (lhs, rhs);
          in
            Goal.prove_sorry lthy [] [] goal
              (fn {context = ctxt, prems = _} =>
                HEADGOAL (EVERY' (map (rtac ctxt) [ext, Lazy.force pred_rel RS trans,
                  Lazy.force rel_cong0 RS fun_cong RS fun_cong RS trans OF
                    replicate live @{thm eq_onp_True},
                  Lazy.force rel_eq RS fun_cong RS fun_cong RS trans, @{thm eqTrueI[OF refl]}])))
            |> Thm.close_derivation \<^here>
          end;

        val pred_True = Lazy.lazy mk_pred_True;

        fun mk_pred_map () =
          let
            val lhs = Term.list_comb (pred', Qs) $ (Term.list_comb (bnf_map_AsBs, fs) $ x);
            val rhs = Term.list_comb (pred, @{map 2} (curry HOLogic.mk_comp) Qs fs) $ x;
            val goal = mk_Trueprop_eq (lhs, rhs);
            val vars = Variable.add_free_names lthy goal [];
            val pred_set = #pred_set axioms RS fun_cong RS sym;
          in
            Goal.prove_sorry lthy vars [] goal
              (fn {context = ctxt, prems = _} =>
                HEADGOAL (rtac ctxt (pred_set RSN (2, pred_set RSN (2, box_equals)))) THEN
                unfold_thms_tac ctxt
                  (@{thms Ball_image_comp ball_empty} @ map Lazy.force set_map) THEN
                HEADGOAL (rtac ctxt refl))
            |> Thm.close_derivation \<^here>
          end;

        val pred_map = Lazy.lazy mk_pred_map;

        fun mk_map_transfer () =
          let
            val rels = map2 mk_rel_fun transfer_domRs transfer_ranRs;
            val rel = mk_rel_fun
              (Term.list_comb (mk_bnf_rel transfer_domRTs CA' CB1, transfer_domRs))
              (Term.list_comb (mk_bnf_rel transfer_ranRTs CB' CB2, transfer_ranRs));
            val concl = HOLogic.mk_Trueprop
              (fold_rev mk_rel_fun rels rel $ bnf_map_AsBs $ mk_bnf_map B1Ts B2Ts);
          in
            Goal.prove_sorry lthy [] []
              (fold_rev Logic.all (transfer_domRs @ transfer_ranRs) concl)
              (fn {context = ctxt, prems = _} => mk_map_transfer_tac ctxt (Lazy.force rel_mono)
                (Lazy.force in_rel) (map Lazy.force set_map) (#map_cong0 axioms)
                (Lazy.force map_comp))
            |> Thm.close_derivation \<^here>
          end;

        val map_transfer = Lazy.lazy mk_map_transfer;

        fun mk_pred_transfer () =
          let
            val iff = HOLogic.eq_const HOLogic.boolT;
            val prem_rels = map (fn T => mk_rel_fun T iff) Rs;
            val prem_elems = mk_rel_fun (Term.list_comb (rel, Rs)) iff;
            val goal = HOLogic.mk_Trueprop
              (fold_rev mk_rel_fun prem_rels prem_elems $ pred $ pred');
            val vars = Variable.add_free_names lthy goal [];
          in
            Goal.prove_sorry lthy vars [] goal (fn {context = ctxt, prems = _} =>
              mk_pred_transfer_tac ctxt live (Lazy.force in_rel) (Lazy.force pred_map)
                (Lazy.force pred_cong))
            |> Thm.close_derivation \<^here>
          end;

        val pred_transfer = Lazy.lazy mk_pred_transfer;

        fun mk_rel_transfer () =
          let
            val iff = HOLogic.eq_const HOLogic.boolT;
            val prem_rels =
              map2 (fn T1 => fn T2 => mk_rel_fun T1 (mk_rel_fun T2 iff)) S_AsCs S_BsEs;
            val prem_elems =
              mk_rel_fun (Term.list_comb (mk_bnf_rel pred2RTsAsCs CA' CC', S_AsCs))
                (mk_rel_fun (Term.list_comb (mk_bnf_rel pred2RTsBsEs CB' CE', S_BsEs)) iff);
            val goal =
              HOLogic.mk_Trueprop (fold_rev mk_rel_fun prem_rels prem_elems $ rel $ relCsEs);
            val vars = Variable.add_free_names lthy goal [];
          in
            Goal.prove_sorry lthy vars [] goal
              (fn {context = ctxt, prems = _} =>
                mk_rel_transfer_tac ctxt (Lazy.force in_rel) (Lazy.force rel_map)
                  (Lazy.force rel_mono_strong))
            |> Thm.close_derivation \<^here>
          end;

        val rel_transfer = Lazy.lazy mk_rel_transfer;

        fun mk_set_transfer () =
          let
            val rel_sets = map2 (fn A => fn B => mk_rel 1 [A] [B] \<^term>\<open>rel_set\<close>) As' Bs';
            val rel_Rs = Term.list_comb (rel, Rs);
            val goals = @{map 4} (fn R => fn rel_set => fn setA => fn setB => HOLogic.mk_Trueprop
              (mk_rel_fun rel_Rs (rel_set $ R) $ setA $ setB)) Rs rel_sets bnf_sets_As bnf_sets_Bs;
          in
            if null goals then []
            else
              let
                val goal = Logic.mk_conjunction_balanced goals;
                val vars = Variable.add_free_names lthy goal [];
              in
                Goal.prove_sorry lthy vars [] goal
                  (fn {context = ctxt, prems = _} =>
                     mk_set_transfer_tac ctxt (Lazy.force in_rel) (map Lazy.force set_map))
                |> Thm.close_derivation \<^here>
                |> Conjunction.elim_balanced (length goals)
              end
          end;

        val set_transfer = Lazy.lazy mk_set_transfer;

        fun mk_inj_map_strong () =
          let
            val assms = @{map 5} (fn setA => fn z => fn f => fn z' => fn f' =>
              fold_rev Logic.all [z, z']
                (Logic.mk_implies (mk_Trueprop_mem (z, setA $ x),
                   Logic.mk_implies (mk_Trueprop_mem (z', setA $ x'),
                     Logic.mk_implies (mk_Trueprop_eq (f $ z, f' $ z'),
                       mk_Trueprop_eq (z, z')))))) bnf_sets_As zs fs zs' fs';
            val concl = Logic.mk_implies
              (mk_Trueprop_eq
                 (Term.list_comb (bnf_map_AsBs, fs) $ x,
                  Term.list_comb (bnf_map_AsBs, fs') $ x'),
               mk_Trueprop_eq (x, x'));
            val goal = fold_rev Logic.all (x :: x' :: fs @ fs')
              (fold_rev (curry Logic.mk_implies) assms concl);
          in
            Goal.prove_sorry lthy [] [] goal (fn {context = ctxt, prems = _} =>
              mk_inj_map_strong_tac ctxt (Lazy.force rel_eq) (Lazy.force rel_map)
                (Lazy.force rel_mono_strong))
            |> Thm.close_derivation \<^here>
          end;

        val inj_map_strong = Lazy.lazy mk_inj_map_strong;

        val defs = mk_defs bnf_map_def bnf_set_defs bnf_rel_def bnf_pred_def;

        val facts = mk_facts bd_Card_order bd_Cinfinite bd_Cnotzero collect_set_map in_bd in_cong
          in_mono in_rel inj_map inj_map_strong map_comp map_cong map_cong_simp map_cong_pred map_id
          map_ident0 map_ident map_transfer rel_eq rel_flip set_map rel_cong0 rel_cong rel_cong_simp
          rel_map rel_mono rel_mono_strong0 rel_mono_strong set_transfer rel_Grp rel_conversep
          rel_OO rel_refl rel_refl_strong rel_reflp rel_symp rel_transp rel_transfer rel_eq_onp
          pred_transfer pred_True pred_map pred_rel pred_mono_strong0 pred_mono_strong pred_mono
          pred_cong0 pred_cong pred_cong_simp;

        val wits = map2 mk_witness bnf_wits wit_thms;

        val bnf_rel =
          Term.subst_atomic_types ((Ds ~~ deads) @ (As' ~~ alphas) @ (Bs' ~~ betas)) rel;

        val bnf_pred = Term.subst_atomic_types ((Ds ~~ deads) @ (As' ~~ alphas)) pred;

        val bnf = mk_bnf bnf_b Calpha live alphas betas dead deads bnf_map bnf_sets bnf_bd axioms
          defs facts wits bnf_rel bnf_pred;
      in
        note_bnf_thms fact_policy qualify bnf_b bnf lthy
      end;

    val one_step_defs =
      no_reflexive (bnf_map_def :: bnf_bd_def :: bnf_set_defs @ bnf_wit_defs @
        [bnf_rel_def, bnf_pred_def]);
  in
    (key, goals, wit_goalss, after_qed, lthy, one_step_defs)
  end;

structure BNF_Plugin = Plugin(type T = bnf);

fun bnf_interpretation name f =
  BNF_Plugin.interpretation name
    (fn bnf => fn lthy => f (transfer_bnf (Proof_Context.theory_of lthy) bnf) lthy);

val interpret_bnf = BNF_Plugin.data;

fun register_bnf_raw key bnf =
  Local_Theory.declaration {syntax = false, pervasive = true}
    (fn phi => Data.map (Symtab.update (key, morph_bnf phi bnf)));

fun register_bnf plugins key bnf =
  register_bnf_raw key bnf #> interpret_bnf plugins bnf;

fun bnf_def const_policy fact_policy internal qualify tacs wit_tac Ds map_b rel_b pred_b set_bs
    raw_csts =
  (fn (_, goals, (triv_tac_opt, wit_goalss), after_qed, lthy, one_step_defs) =>
  let
    fun mk_wits_tac ctxt set_maps =
      TRYALL Goal.conjunction_tac THEN
      (case triv_tac_opt of
        SOME tac => tac ctxt set_maps
      | NONE => unfold_thms_tac ctxt one_step_defs THEN wit_tac ctxt);
    val wit_goals = map Logic.mk_conjunction_balanced wit_goalss;
    fun mk_wit_thms set_maps =
      Goal.prove_sorry lthy [] [] (Logic.mk_conjunction_balanced wit_goals)
        (fn {context = ctxt, prems = _} => mk_wits_tac ctxt set_maps)
        |> Thm.close_derivation \<^here>
        |> Conjunction.elim_balanced (length wit_goals)
        |> map2 (Conjunction.elim_balanced o length) wit_goalss
        |> (map o map) (Thm.forall_elim_vars 0);
  in
    map2 (Thm.close_derivation \<^here> oo Goal.prove_sorry lthy [] [])
      goals (map (fn tac => fn {context = ctxt, prems = _} =>
        unfold_thms_tac ctxt one_step_defs THEN tac ctxt) tacs)
    |> (fn thms => after_qed mk_wit_thms (map single thms) lthy)
  end) o prepare_def const_policy fact_policy internal qualify (K I) (K I) Ds map_b rel_b pred_b
    set_bs raw_csts;

fun bnf_cmd (raw_csts, raw_plugins) =
  (fn (key, goals, (triv_tac_opt, wit_goalss), after_qed, lthy, defs) =>
  let
    val plugins = raw_plugins lthy;
    val wit_goals = map Logic.mk_conjunction_balanced wit_goalss;
    fun mk_triv_wit_thms tac set_maps =
      Goal.prove_sorry lthy [] [] (Logic.mk_conjunction_balanced wit_goals)
        (fn {context = ctxt, prems = _} => TRYALL Goal.conjunction_tac THEN tac ctxt set_maps)
        |> Thm.close_derivation \<^here>
        |> Conjunction.elim_balanced (length wit_goals)
        |> map2 (Conjunction.elim_balanced o length) wit_goalss
        |> (map o map) (Thm.forall_elim_vars 0);
    val (mk_wit_thms, nontriv_wit_goals) =
      (case triv_tac_opt of
        NONE => (fn _ => [], map (map (rpair [])) wit_goalss)
      | SOME tac => (mk_triv_wit_thms tac, []));
  in
    lthy
    |> Proof.theorem NONE (uncurry (register_bnf plugins key) oo after_qed mk_wit_thms)
      (map (single o rpair []) goals @ nontriv_wit_goals)
    |> Proof.unfolding ([[(@{thm OO_Grp_alt} :: @{thm mem_Collect_eq} :: defs, [])]])
    |> Proof.refine_singleton (Method.Basic (fn ctxt =>
      Method.SIMPLE_METHOD (TRYALL (rtac ctxt refl))))
  end) o prepare_def Do_Inline (user_policy Note_Some) false I Syntax.read_typ Syntax.read_term
    NONE Binding.empty Binding.empty Binding.empty [] raw_csts;

fun print_bnfs ctxt =
  let
    fun pretty_set sets i = Pretty.block
      [Pretty.str (mk_setN (i + 1) ^ ":"), Pretty.brk 1,
        Pretty.quote (Syntax.pretty_term ctxt (nth sets i))];

    fun pretty_bnf (key, BNF {T, map, sets, bd, live, lives, dead, deads, ...}) =
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
    Pretty.big_list "Registered bounded natural functors:"
      (map pretty_bnf (sort_by fst (Symtab.dest (Data.get (Context.Proof ctxt)))))
    |> Pretty.writeln
  end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_bnfs\<close>
    "print all bounded natural functors"
    (Scan.succeed (Toplevel.keep (print_bnfs o Toplevel.context_of)));

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>bnf\<close>
    "register a type as a bounded natural functor"
    (parse_opt_binding_colon -- Parse.typ --|
       (Parse.reserved "map" -- \<^keyword>\<open>:\<close>) -- Parse.term --
       Scan.optional ((Parse.reserved "sets" -- \<^keyword>\<open>:\<close>) |--
         Scan.repeat1 (Scan.unless (Parse.reserved "bd") Parse.term)) [] --|
       (Parse.reserved "bd" -- \<^keyword>\<open>:\<close>) -- Parse.term --
       Scan.optional ((Parse.reserved "wits" -- \<^keyword>\<open>:\<close>) |--
         Scan.repeat1 (Scan.unless (Parse.reserved "rel" ||
           Parse.reserved "plugins") Parse.term)) [] --
       Scan.option ((Parse.reserved "rel" -- \<^keyword>\<open>:\<close>) |-- Parse.term) --
       Scan.option ((Parse.reserved "pred" -- \<^keyword>\<open>:\<close>) |-- Parse.term) --
       Scan.optional Plugin_Name.parse_filter (K Plugin_Name.default_filter)
       >> bnf_cmd);

end;
