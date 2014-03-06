(*  Title:      HOL/Tools/BNF/bnf_def.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Definition of bounded natural functors.
*)

signature BNF_DEF =
sig
  type bnf
  type nonemptiness_witness = {I: int list, wit: term, prop: thm list}

  val morph_bnf: morphism -> bnf -> bnf
  val bnf_of: Proof.context -> string -> bnf option
  val register_bnf: string -> (bnf * local_theory) -> (bnf * local_theory)

  val name_of_bnf: bnf -> binding
  val T_of_bnf: bnf -> typ
  val live_of_bnf: bnf -> int
  val lives_of_bnf: bnf -> typ list
  val dead_of_bnf: bnf -> int
  val deads_of_bnf: bnf -> typ list
  val nwits_of_bnf: bnf -> int

  val mapN: string
  val relN: string
  val setN: string
  val mk_setN: int -> string
  val mk_witN: int -> string

  val map_of_bnf: bnf -> term
  val sets_of_bnf: bnf -> term list
  val rel_of_bnf: bnf -> term

  val mk_T_of_bnf: typ list -> typ list -> bnf -> typ
  val mk_bd_of_bnf: typ list -> typ list -> bnf -> term
  val mk_map_of_bnf: typ list -> typ list -> typ list -> bnf -> term
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
  val map_comp0_of_bnf: bnf -> thm
  val map_comp_of_bnf: bnf -> thm
  val map_cong0_of_bnf: bnf -> thm
  val map_cong_of_bnf: bnf -> thm
  val map_def_of_bnf: bnf -> thm
  val map_id0_of_bnf: bnf -> thm
  val map_id_of_bnf: bnf -> thm
  val map_transfer_of_bnf: bnf -> thm
  val le_rel_OO_of_bnf: bnf -> thm
  val rel_def_of_bnf: bnf -> thm
  val rel_Grp_of_bnf: bnf -> thm
  val rel_OO_of_bnf: bnf -> thm
  val rel_OO_Grp_of_bnf: bnf -> thm
  val rel_cong_of_bnf: bnf -> thm
  val rel_conversep_of_bnf: bnf -> thm
  val rel_mono_of_bnf: bnf -> thm
  val rel_mono_strong_of_bnf: bnf -> thm
  val rel_eq_of_bnf: bnf -> thm
  val rel_flip_of_bnf: bnf -> thm
  val set_bd_of_bnf: bnf -> thm list
  val set_defs_of_bnf: bnf -> thm list
  val set_map0_of_bnf: bnf -> thm list
  val set_map_of_bnf: bnf -> thm list
  val wit_thms_of_bnf: bnf -> thm list
  val wit_thmss_of_bnf: bnf -> thm list list

  val mk_map: int -> typ list -> typ list -> term -> term
  val mk_rel: int -> typ list -> typ list -> term -> term
  val build_map: Proof.context -> (typ * typ -> term) -> typ * typ -> term
  val build_rel: Proof.context -> (typ * typ -> term) -> typ * typ -> term
  val flatten_type_args_of_bnf: bnf -> 'a -> 'a list -> 'a list
  val map_flattened_map_args: Proof.context -> string -> (term list -> 'a list) -> term list ->
    'a list

  val mk_witness: int list * term -> thm list -> nonemptiness_witness
  val minimize_wits: (''a list * 'b) list -> (''a list * 'b) list
  val wits_of_bnf: bnf -> nonemptiness_witness list

  val zip_axioms: 'a -> 'a -> 'a -> 'a list -> 'a -> 'a -> 'a list -> 'a -> 'a -> 'a list

  datatype inline_policy = Dont_Inline | Hardly_Inline | Smart_Inline | Do_Inline
  datatype fact_policy = Dont_Note | Note_Some | Note_All

  val bnf_note_all: bool Config.T
  val bnf_timing: bool Config.T
  val user_policy: fact_policy -> Proof.context -> fact_policy
  val note_bnf_thms: fact_policy -> (binding -> binding) -> binding -> bnf -> Proof.context ->
    Proof.context

  val print_bnfs: Proof.context -> unit
  val prepare_def: inline_policy -> (Proof.context -> fact_policy) -> (binding -> binding) ->
    (Proof.context -> 'a -> typ) -> (Proof.context -> 'b -> term) -> typ list option ->
    binding -> binding -> binding list ->
    (((((binding * 'a) * 'b) * 'b list) * 'b) * 'b list) * 'b option -> Proof.context ->
    string * term list *
    ((Proof.context -> thm list -> tactic) option * term list list) *
    ((thm list -> thm list list) -> thm list list -> Proof.context -> bnf * local_theory) *
    local_theory * thm list

  val define_bnf_consts: inline_policy -> fact_policy -> typ list option ->
    binding -> binding -> binding list ->
    (((((binding * typ) * term) * term list) * term) * term list) * term option -> local_theory ->
      ((typ list * typ list * typ list * typ) *
       (term * term list * term * (int list * term) list * term) *
       (thm * thm list * thm * thm list * thm) *
       ((typ list -> typ list -> typ list -> term) *
        (typ list -> typ list -> term -> term) *
        (typ list -> typ list -> typ -> typ) *
        (typ list -> typ list -> typ list -> term) *
        (typ list -> typ list -> typ list -> term))) * local_theory

  val bnf_def: inline_policy -> (Proof.context -> fact_policy) -> (binding -> binding) ->
    (Proof.context -> tactic) list ->
    (Proof.context -> tactic) -> typ list option -> binding ->
    binding -> binding list ->
    (((((binding * typ) * term) * term list) * term) * term list) * term option ->
    local_theory -> bnf * local_theory
end;

structure BNF_Def : BNF_DEF =
struct

open BNF_Util
open BNF_Tactics
open BNF_Def_Tactics

val fundefcong_attrs = @{attributes [fundef_cong]};

type axioms = {
  map_id0: thm,
  map_comp0: thm,
  map_cong0: thm,
  set_map0: thm list,
  bd_card_order: thm,
  bd_cinfinite: thm,
  set_bd: thm list,
  le_rel_OO: thm,
  rel_OO_Grp: thm
};

fun mk_axioms' ((((((((id, comp), cong), map), c_o), cinf), set_bd), le_rel_OO), rel) =
  {map_id0 = id, map_comp0 = comp, map_cong0 = cong, set_map0 = map, bd_card_order = c_o,
   bd_cinfinite = cinf, set_bd = set_bd, le_rel_OO = le_rel_OO, rel_OO_Grp = rel};

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
  ||> the_single
  |> mk_axioms';

fun zip_axioms mid mcomp mcong smap bdco bdinf sbd le_rel_OO rel =
  [mid, mcomp, mcong] @ smap @ [bdco, bdinf] @ sbd @ [le_rel_OO, rel];

fun dest_axioms {map_id0, map_comp0, map_cong0, set_map0, bd_card_order, bd_cinfinite, set_bd,
  le_rel_OO, rel_OO_Grp} =
  zip_axioms map_id0 map_comp0 map_cong0 set_map0 bd_card_order bd_cinfinite set_bd le_rel_OO
    rel_OO_Grp;

fun map_axioms f {map_id0, map_comp0, map_cong0, set_map0, bd_card_order, bd_cinfinite, set_bd,
  le_rel_OO, rel_OO_Grp} =
  {map_id0 = f map_id0,
    map_comp0 = f map_comp0,
    map_cong0 = f map_cong0,
    set_map0 = map f set_map0,
    bd_card_order = f bd_card_order,
    bd_cinfinite = f bd_cinfinite,
    set_bd = map f set_bd,
    le_rel_OO = f le_rel_OO,
    rel_OO_Grp = f rel_OO_Grp};

val morph_axioms = map_axioms o Morphism.thm;

type defs = {
  map_def: thm,
  set_defs: thm list,
  rel_def: thm
}

fun mk_defs map sets rel = {map_def = map, set_defs = sets, rel_def = rel};

fun map_defs f {map_def, set_defs, rel_def} =
  {map_def = f map_def, set_defs = map f set_defs, rel_def = f rel_def};

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
  map_comp: thm lazy,
  map_cong: thm lazy,
  map_id: thm lazy,
  map_transfer: thm lazy,
  rel_eq: thm lazy,
  rel_flip: thm lazy,
  set_map: thm lazy list,
  rel_cong: thm lazy,
  rel_mono: thm lazy,
  rel_mono_strong: thm lazy,
  rel_Grp: thm lazy,
  rel_conversep: thm lazy,
  rel_OO: thm lazy
};

fun mk_facts bd_Card_order bd_Cinfinite bd_Cnotzero collect_set_map in_bd in_cong in_mono in_rel
    map_comp map_cong map_id map_transfer rel_eq rel_flip set_map rel_cong rel_mono
    rel_mono_strong rel_Grp rel_conversep rel_OO = {
  bd_Card_order = bd_Card_order,
  bd_Cinfinite = bd_Cinfinite,
  bd_Cnotzero = bd_Cnotzero,
  collect_set_map = collect_set_map,
  in_bd = in_bd,
  in_cong = in_cong,
  in_mono = in_mono,
  in_rel = in_rel,
  map_comp = map_comp,
  map_cong = map_cong,
  map_id = map_id,
  map_transfer = map_transfer,
  rel_eq = rel_eq,
  rel_flip = rel_flip,
  set_map = set_map,
  rel_cong = rel_cong,
  rel_mono = rel_mono,
  rel_mono_strong = rel_mono_strong,
  rel_Grp = rel_Grp,
  rel_conversep = rel_conversep,
  rel_OO = rel_OO};

fun map_facts f {
  bd_Card_order,
  bd_Cinfinite,
  bd_Cnotzero,
  collect_set_map,
  in_bd,
  in_cong,
  in_mono,
  in_rel,
  map_comp,
  map_cong,
  map_id,
  map_transfer,
  rel_eq,
  rel_flip,
  set_map,
  rel_cong,
  rel_mono,
  rel_mono_strong,
  rel_Grp,
  rel_conversep,
  rel_OO} =
  {bd_Card_order = f bd_Card_order,
    bd_Cinfinite = f bd_Cinfinite,
    bd_Cnotzero = f bd_Cnotzero,
    collect_set_map = Lazy.map f collect_set_map,
    in_bd = Lazy.map f in_bd,
    in_cong = Lazy.map f in_cong,
    in_mono = Lazy.map f in_mono,
    in_rel = Lazy.map f in_rel,
    map_comp = Lazy.map f map_comp,
    map_cong = Lazy.map f map_cong,
    map_id = Lazy.map f map_id,
    map_transfer = Lazy.map f map_transfer,
    rel_eq = Lazy.map f rel_eq,
    rel_flip = Lazy.map f rel_flip,
    set_map = map (Lazy.map f) set_map,
    rel_cong = Lazy.map f rel_cong,
    rel_mono = Lazy.map f rel_mono,
    rel_mono_strong = Lazy.map f rel_mono_strong,
    rel_Grp = Lazy.map f rel_Grp,
    rel_conversep = Lazy.map f rel_conversep,
    rel_OO = Lazy.map f rel_OO};

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

(*thms*)
val bd_card_order_of_bnf = #bd_card_order o #axioms o rep_bnf;
val bd_cinfinite_of_bnf = #bd_cinfinite o #axioms o rep_bnf;
val bd_Card_order_of_bnf = #bd_Card_order o #facts o rep_bnf;
val bd_Cinfinite_of_bnf = #bd_Cinfinite o #facts o rep_bnf;
val bd_Cnotzero_of_bnf = #bd_Cnotzero o #facts o rep_bnf;
val collect_set_map_of_bnf = Lazy.force o #collect_set_map o #facts o rep_bnf;
val in_bd_of_bnf = Lazy.force o #in_bd o #facts o rep_bnf;
val in_cong_of_bnf = Lazy.force o #in_cong o #facts o rep_bnf;
val in_mono_of_bnf = Lazy.force o #in_mono o #facts o rep_bnf;
val in_rel_of_bnf = Lazy.force o #in_rel o #facts o rep_bnf;
val map_def_of_bnf = #map_def o #defs o rep_bnf;
val map_id0_of_bnf = #map_id0 o #axioms o rep_bnf;
val map_id_of_bnf = Lazy.force o #map_id o #facts o rep_bnf;
val map_comp0_of_bnf = #map_comp0 o #axioms o rep_bnf;
val map_comp_of_bnf = Lazy.force o #map_comp o #facts o rep_bnf;
val map_cong0_of_bnf = #map_cong0 o #axioms o rep_bnf;
val map_cong_of_bnf = Lazy.force o #map_cong o #facts o rep_bnf;
val map_transfer_of_bnf = Lazy.force o #map_transfer o #facts o rep_bnf;
val le_rel_OO_of_bnf = #le_rel_OO o #axioms o rep_bnf;
val rel_def_of_bnf = #rel_def o #defs o rep_bnf;
val rel_eq_of_bnf = Lazy.force o #rel_eq o #facts o rep_bnf;
val rel_flip_of_bnf = Lazy.force o #rel_flip o #facts o rep_bnf;
val set_bd_of_bnf = #set_bd o #axioms o rep_bnf;
val set_defs_of_bnf = #set_defs o #defs o rep_bnf;
val set_map0_of_bnf = #set_map0 o #axioms o rep_bnf;
val set_map_of_bnf = map Lazy.force o #set_map o #facts o rep_bnf;
val rel_cong_of_bnf = Lazy.force o #rel_cong o #facts o rep_bnf;
val rel_mono_of_bnf = Lazy.force o #rel_mono o #facts o rep_bnf;
val rel_mono_strong_of_bnf = Lazy.force o #rel_mono_strong o #facts o rep_bnf;
val rel_Grp_of_bnf = Lazy.force o #rel_Grp o #facts o rep_bnf;
val rel_conversep_of_bnf = Lazy.force o #rel_conversep o #facts o rep_bnf;
val rel_OO_of_bnf = Lazy.force o #rel_OO o #facts o rep_bnf;
val rel_OO_Grp_of_bnf = #rel_OO_Grp o #axioms o rep_bnf;
val wit_thms_of_bnf = maps #prop o wits_of_bnf;
val wit_thmss_of_bnf = map #prop o wits_of_bnf;

fun mk_bnf name T live lives lives' dead deads map sets bd axioms defs facts wits rel =
  BNF {name = name, T = T,
       live = live, lives = lives, lives' = lives', dead = dead, deads = deads,
       map = map, sets = sets, bd = bd,
       axioms = axioms, defs = defs, facts = facts,
       nwits = length wits, wits = wits, rel = rel};

fun morph_bnf phi (BNF {name = name, T = T, live = live, lives = lives, lives' = lives',
  dead = dead, deads = deads, map = map, sets = sets, bd = bd,
  axioms = axioms, defs = defs, facts = facts,
  nwits = nwits, wits = wits, rel = rel}) =
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
    rel = Morphism.term phi rel};

structure Data = Generic_Data
(
  type T = bnf Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data : T = Symtab.merge (K true) data;
);

fun bnf_of ctxt =
  Symtab.lookup (Data.get (Context.Proof ctxt))
  #> Option.map (morph_bnf (Morphism.transfer_morphism (Proof_Context.theory_of ctxt)));


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

fun mk_map live Ts Us t =
  let val (Type (_, Ts0), Type (_, Us0)) = strip_typeN (live + 1) (fastype_of t) |>> List.last in
    Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) t
  end;

fun mk_rel live Ts Us t =
  let val [Type (_, Ts0), Type (_, Us0)] = binder_types (snd (strip_typeN live (fastype_of t))) in
    Term.subst_atomic_types (Ts0 @ Us0 ~~ Ts @ Us) t
  end;

fun build_map_or_rel mk const of_bnf dest ctxt build_simple =
  let
    fun build (TU as (T, U)) =
      if T = U then
        const T
      else
        (case TU of
          (Type (s, Ts), Type (s', Us)) =>
          if s = s' then
            let
              val bnf = the (bnf_of ctxt s);
              val live = live_of_bnf bnf;
              val mapx = mk live Ts Us (of_bnf bnf);
              val TUs' = map dest (fst (strip_typeN live (fastype_of mapx)));
            in Term.list_comb (mapx, map build TUs') end
          else
            build_simple TU
        | _ => build_simple TU);
  in build end;

val build_map = build_map_or_rel mk_map HOLogic.id_const map_of_bnf dest_funT;
val build_rel = build_map_or_rel mk_rel HOLogic.eq_const rel_of_bnf dest_pred2T;

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

val bd_card_orderN = "bd_card_order";
val bd_cinfiniteN = "bd_cinfinite";
val bd_Card_orderN = "bd_Card_order";
val bd_CinfiniteN = "bd_Cinfinite";
val bd_CnotzeroN = "bd_Cnotzero";
val collect_set_mapN = "collect_set_map";
val in_bdN = "in_bd";
val in_monoN = "in_mono";
val in_relN = "in_rel";
val map_id0N = "map_id0";
val map_idN = "map_id";
val map_comp0N = "map_comp0";
val map_compN = "map_comp";
val map_cong0N = "map_cong0";
val map_congN = "map_cong";
val map_transferN = "map_transfer";
val rel_eqN = "rel_eq";
val rel_flipN = "rel_flip";
val set_map0N = "set_map0";
val set_mapN = "set_map";
val set_bdN = "set_bd";
val rel_GrpN = "rel_Grp";
val rel_conversepN = "rel_conversep";
val rel_monoN = "rel_mono"
val rel_mono_strongN = "rel_mono_strong"
val rel_comppN = "rel_compp";
val rel_compp_GrpN = "rel_compp_Grp";

datatype inline_policy = Dont_Inline | Hardly_Inline | Smart_Inline | Do_Inline;

datatype fact_policy = Dont_Note | Note_Some | Note_All;

val bnf_note_all = Attrib.setup_config_bool @{binding bnf_note_all} (K false);
val bnf_timing = Attrib.setup_config_bool @{binding bnf_timing} (K false);

fun user_policy policy ctxt = if Config.get ctxt bnf_note_all then Note_All else policy;

val smart_max_inline_term_size = 25; (*FUDGE*)

fun note_bnf_thms fact_policy qualify' bnf_b bnf =
  let
    val axioms = axioms_of_bnf bnf;
    val facts = facts_of_bnf bnf;
    val wits = wits_of_bnf bnf;
    val qualify =
      let val (_, qs, _) = Binding.dest bnf_b;
      in fold_rev (fn (s, mand) => Binding.qualify mand s) qs #> qualify' end;
  in
    (if fact_policy = Note_All then
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
            (in_relN, [Lazy.force (#in_rel facts)]),
            (map_comp0N, [#map_comp0 axioms]),
            (map_id0N, [#map_id0 axioms]),
            (map_transferN, [Lazy.force (#map_transfer facts)]),
            (rel_mono_strongN, [Lazy.force (#rel_mono_strong facts)]),
            (set_map0N, #set_map0 axioms),
            (set_bdN, #set_bd axioms)] @
            (witNs ~~ wit_thmss_of_bnf bnf)
            |> map (fn (thmN, thms) =>
              ((qualify (Binding.qualify true (Binding.name_of bnf_b) (Binding.name thmN)), []),
              [(thms, [])]));
        in
          Local_Theory.notes notes #> snd
        end
      else
        I)
    #> (if fact_policy <> Dont_Note then
        let
          val notes =
            [(map_compN, [Lazy.force (#map_comp facts)], []),
            (map_cong0N, [#map_cong0 axioms], []),
            (map_congN, [Lazy.force (#map_cong facts)], fundefcong_attrs),
            (map_idN, [Lazy.force (#map_id facts)], []),
            (rel_comppN, [Lazy.force (#rel_OO facts)], []),
            (rel_compp_GrpN, no_refl [#rel_OO_Grp axioms], []),
            (rel_conversepN, [Lazy.force (#rel_conversep facts)], []),
            (rel_eqN, [Lazy.force (#rel_eq facts)], []),
            (rel_flipN, [Lazy.force (#rel_flip facts)], []),
            (rel_GrpN, [Lazy.force (#rel_Grp facts)], []),
            (rel_monoN, [Lazy.force (#rel_mono facts)], []),
            (set_mapN, map Lazy.force (#set_map facts), [])]
            |> filter_out (null o #2)
            |> map (fn (thmN, thms, attrs) =>
              ((qualify (Binding.qualify true (Binding.name_of bnf_b) (Binding.name thmN)),
                attrs), [(thms, [])]));
        in
          Local_Theory.notes notes #> snd
        end
      else
        I)
  end;


(* Define new BNFs *)

fun define_bnf_consts const_policy fact_policy Ds_opt map_b rel_b set_bs
  ((((((bnf_b, T_rhs), map_rhs), set_rhss), bd_rhs), wit_rhss), rel_rhs_opt) no_defs_lthy =
  let
    val live = length set_rhss;

    val def_qualify = Binding.conceal o Binding.qualify false (Binding.name_of bnf_b);

    fun mk_prefix_binding pre = Binding.prefix_name (pre ^ "_") bnf_b;

    fun maybe_define user_specified (b, rhs) lthy =
      let
        val inline =
          (user_specified orelse fact_policy = Dont_Note) andalso
          (case const_policy of
            Dont_Inline => false
          | Hardly_Inline => Term.is_Free rhs orelse Term.is_Const rhs
          | Smart_Inline => Term.size_of_term rhs <= smart_max_inline_term_size
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
        |> maybe_define true map_bind_def
        ||>> apfst split_list o fold_map (maybe_define true) set_binds_defs
        ||>> maybe_define true bd_bind_def
        ||> `(maybe_restore no_defs_lthy);

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
    val _ = if null bad_args then () else error ("Locally fixed type arguments " ^
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

    val (((As, Bs), Ds), names_lthy) = lthy
      |> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees (length deads);
    val RTs = map2 (curry HOLogic.mk_prodT) As Bs;
    val pred2RTs = map2 mk_pred2T As Bs;
    val (Rs, Rs') = names_lthy |> mk_Frees' "R" pred2RTs |> fst
    val CA = mk_bnf_T Ds As Calpha;
    val CR = mk_bnf_T Ds RTs Calpha;
    val setRs =
      map3 (fn R => fn T => fn U =>
          HOLogic.Collect_const (HOLogic.mk_prodT (T, U)) $ HOLogic.mk_split R) Rs As Bs;

    (*Grp (in (Collect (split R1) .. Collect (split Rn))) (map fst .. fst)^--1 OO
      Grp (in (Collect (split R1) .. Collect (split Rn))) (map snd .. snd)*)
    val OO_Grp =
      let
        val map1 = Term.list_comb (mk_bnf_map Ds RTs As, map fst_const RTs);
        val map2 = Term.list_comb (mk_bnf_map Ds RTs Bs, map snd_const RTs);
        val bnf_in = mk_in setRs (map (mk_bnf_t Ds RTs) bnf_sets) CR;
      in
        mk_rel_compp (mk_conversep (mk_Grp bnf_in map1), mk_Grp bnf_in map2)
        |> fold_rev Term.absfree Rs'
      end;

    val rel_rhs = the_default OO_Grp rel_rhs_opt;

    val rel_bind_def =
      (fn () => def_qualify (if Binding.is_empty rel_b then mk_prefix_binding relN else rel_b),
         rel_rhs);

    val wit_rhss =
      if null wit_rhss then
        [fold_rev Term.absdummy As (Term.list_comb (mk_bnf_map Ds As As,
          map2 (fn T => fn i => Term.absdummy T (Bound i)) As (live downto 1)) $
          Const (@{const_name undefined}, CA))]
      else wit_rhss;
    val nwits = length wit_rhss;
    val wit_binds_defs =
      let
        val bs = if nwits = 1 then [fn () => def_qualify (mk_prefix_binding witN)]
          else map (fn i => fn () => def_qualify (mk_prefix_binding (mk_witN i))) (1 upto nwits);
      in bs ~~ wit_rhss end;

    val (((bnf_rel_term, raw_rel_def), (bnf_wit_terms, raw_wit_defs)), (lthy, lthy_old)) =
      lthy
      |> maybe_define (is_some rel_rhs_opt) rel_bind_def
      ||>> apfst split_list o fold_map (maybe_define (not (null wit_rhss))) wit_binds_defs
      ||> `(maybe_restore lthy);

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val bnf_rel_def = Morphism.thm phi raw_rel_def;
    val bnf_rel = Morphism.term phi bnf_rel_term;
    fun mk_bnf_rel Ds As' Bs' =
      normalize_rel lthy (map2 mk_pred2T As' Bs') (mk_bnf_T Ds As' Calpha) (mk_bnf_T Ds Bs' Calpha)
        bnf_rel;

    val bnf_wit_defs = map (Morphism.thm phi) raw_wit_defs;
    val bnf_wits =
      map (normalize_wit Calpha_params Calpha alphas o Morphism.term phi) bnf_wit_terms;

    fun mk_OO_Grp Ds' As' Bs' =
      Term.subst_atomic_types ((Ds ~~ Ds') @ (As ~~ As') @ (Bs ~~ Bs')) OO_Grp;
  in
    (((alphas, betas, deads, Calpha),
     (bnf_map, bnf_sets, bnf_bd, bnf_wits, bnf_rel),
     (bnf_map_def, bnf_set_defs, bnf_bd_def, bnf_wit_defs, bnf_rel_def),
     (mk_bnf_map, mk_bnf_t, mk_bnf_T, mk_bnf_rel, mk_OO_Grp)), lthy)
  end;

fun prepare_def const_policy mk_fact_policy qualify prep_typ prep_term Ds_opt map_b rel_b set_bs
  ((((((raw_bnf_b, raw_bnf_T), raw_map), raw_sets), raw_bd), raw_wits), raw_rel_opt)
  no_defs_lthy =
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

    fun err T =
      error ("Trying to register the type " ^ quote (Syntax.string_of_typ no_defs_lthy T) ^
        " as unnamed BNF");

    val (bnf_b, key) =
      if Binding.eq_name (bnf_b, Binding.empty) then
        (case T_rhs of
          Type (C, Ts) => if forall (can dest_TFree) Ts
            then (Binding.qualified_name C, C) else err T_rhs
        | T => err T)
      else (bnf_b, Local_Theory.full_name no_defs_lthy bnf_b);

    val (((alphas, betas, deads, Calpha),
     (bnf_map, bnf_sets, bnf_bd, bnf_wits, bnf_rel),
     (bnf_map_def, bnf_set_defs, bnf_bd_def, bnf_wit_defs, bnf_rel_def),
     (mk_bnf_map_Ds, mk_bnf_t_Ds, mk_bnf_T_Ds, _, mk_OO_Grp)), lthy) =
       define_bnf_consts const_policy fact_policy Ds_opt map_b rel_b set_bs
         ((((((bnf_b, T_rhs), map_rhs), set_rhss), bd_rhs), wit_rhss), rel_rhs_opt) no_defs_lthy;

    val dead = length deads;

    val ((((((As', Bs'), Cs), Ds), B1Ts), B2Ts), (Ts, T)) = lthy
      |> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees live
      ||>> mk_TFrees dead
      ||>> mk_TFrees live
      ||>> mk_TFrees live
      ||> fst o mk_TFrees 1
      ||> the_single
      ||> `(replicate live);

    val mk_bnf_map = mk_bnf_map_Ds Ds;
    val mk_bnf_t = mk_bnf_t_Ds Ds;
    val mk_bnf_T = mk_bnf_T_Ds Ds;

    val pred2RTs = map2 mk_pred2T As' Bs';
    val pred2RTsAsCs = map2 mk_pred2T As' Cs;
    val pred2RTsBsCs = map2 mk_pred2T Bs' Cs;
    val pred2RT's = map2 mk_pred2T Bs' As';
    val self_pred2RTs = map2 mk_pred2T As' As';
    val transfer_domRTs = map2 mk_pred2T As' B1Ts;
    val transfer_ranRTs = map2 mk_pred2T Bs' B2Ts;

    val CA' = mk_bnf_T As' Calpha;
    val CB' = mk_bnf_T Bs' Calpha;
    val CC' = mk_bnf_T Cs Calpha;
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

    val pre_names_lthy = lthy;
    val (((((((((((((((fs, gs), hs), x), y), zs), ys), As),
      As_copy), bs), Rs), Rs_copy), Ss),
      transfer_domRs), transfer_ranRs), names_lthy) = pre_names_lthy
      |> mk_Frees "f" (map2 (curry op -->) As' Bs')
      ||>> mk_Frees "g" (map2 (curry op -->) Bs' Cs)
      ||>> mk_Frees "h" (map2 (curry op -->) As' Ts)
      ||>> yield_singleton (mk_Frees "x") CA'
      ||>> yield_singleton (mk_Frees "y") CB'
      ||>> mk_Frees "z" As'
      ||>> mk_Frees "y" Bs'
      ||>> mk_Frees "A" (map HOLogic.mk_setT As')
      ||>> mk_Frees "A" (map HOLogic.mk_setT As')
      ||>> mk_Frees "b" As'
      ||>> mk_Frees "R" pred2RTs
      ||>> mk_Frees "R" pred2RTs
      ||>> mk_Frees "S" pred2RTsBsCs
      ||>> mk_Frees "R" transfer_domRTs
      ||>> mk_Frees "S" transfer_ranRTs;

    val fs_copy = map2 (retype_free o fastype_of) fs gs;
    val x_copy = retype_free CA' y;

    val rel = mk_bnf_rel pred2RTs CA' CB';
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

    fun mk_map_cong_prem x z set f f_copy =
      Logic.all z (Logic.mk_implies
        (HOLogic.mk_Trueprop (HOLogic.mk_mem (z, set $ x)),
        mk_Trueprop_eq (f $ z, f_copy $ z)));

    val map_cong0_goal =
      let
        val prems = map4 (mk_map_cong_prem x) zs bnf_sets_As fs fs_copy;
        val eq = mk_Trueprop_eq (Term.list_comb (bnf_map_AsBs, fs) $ x,
          Term.list_comb (bnf_map_AsBs, fs_copy) $ x);
      in
        fold_rev Logic.all (x :: fs @ fs_copy) (Logic.list_implies (prems, eq))
      end;

    val set_map0s_goal =
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

    val relAsCs = mk_bnf_rel pred2RTsAsCs CA' CC';
    val relBsCs = mk_bnf_rel pred2RTsBsCs CB' CC';
    val rel_OO_lhs = Term.list_comb (relAsCs, map2 (curry mk_rel_compp) Rs Ss);
    val rel_OO_rhs = mk_rel_compp (Term.list_comb (rel, Rs), Term.list_comb (relBsCs, Ss));
    val le_rel_OO_goal =
      fold_rev Logic.all (Rs @ Ss) (HOLogic.mk_Trueprop (mk_leq rel_OO_rhs rel_OO_lhs));

    val rel_OO_Grp_goal = fold_rev Logic.all Rs (mk_Trueprop_eq (Term.list_comb (rel, Rs),
      Term.list_comb (mk_OO_Grp Ds As' Bs', Rs)));

    val goals = zip_axioms map_id0_goal map_comp0_goal map_cong0_goal set_map0s_goal
      card_order_bd_goal cinfinite_bd_goal set_bds_goal le_rel_OO_goal rel_OO_Grp_goal;

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
            val collect_map = HOLogic.mk_comp
              (mk_collect (map (mk_bnf_t Ts) bnf_sets) defT,
              Term.list_comb (mk_bnf_map As' Ts, hs));
            val image_collect = mk_collect
              (map2 (fn h => fn set => HOLogic.mk_comp (mk_image h, set)) hs bnf_sets_As)
              defT;
            (*collect {set1 ... setm} o map f1 ... fm = collect {f1` o set1 ... fm` o setm}*)
            val goal = fold_rev Logic.all hs (mk_Trueprop_eq (collect_map, image_collect));
          in
            Goal.prove_sorry lthy [] [] goal (K (mk_collect_set_map_tac (#set_map0 axioms)))
            |> Thm.close_derivation
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
            Goal.prove_sorry lthy [] [] in_mono_goal (K (mk_in_mono_tac live))
            |> Thm.close_derivation
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
              (K ((TRY o hyp_subst_tac lthy THEN' rtac refl) 1))
            |> Thm.close_derivation
          end;

        val in_cong = Lazy.lazy mk_in_cong;

        val map_id = Lazy.lazy (fn () => mk_map_id (#map_id0 axioms));
        val map_comp = Lazy.lazy (fn () => mk_map_comp (#map_comp0 axioms));

        fun mk_map_cong () =
          let
            val prem0 = mk_Trueprop_eq (x, x_copy);
            val prems = map4 (mk_map_cong_prem x_copy) zs bnf_sets_As fs fs_copy;
            val eq = mk_Trueprop_eq (Term.list_comb (bnf_map_AsBs, fs) $ x,
              Term.list_comb (bnf_map_AsBs, fs_copy) $ x_copy);
            val goal = fold_rev Logic.all (x :: x_copy :: fs @ fs_copy)
              (Logic.list_implies (prem0 :: prems, eq));
          in
            Goal.prove_sorry lthy [] [] goal (fn _ => mk_map_cong_tac lthy (#map_cong0 axioms))
            |> Thm.close_derivation
          end;

        val map_cong = Lazy.lazy mk_map_cong;

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
                val cTs = map (SOME o certifyT lthy) [ran_bnfT, Library.foldr1 HOLogic.mk_prodT Ts];
                val tinst = fold (fn T => fn t => HOLogic.mk_split (Term.absdummy T t)) (tl revTs)
                  (Term.absdummy (hd revTs) (Term.list_comb (mk_bnf_map bdTs ranTs,
                    map Bound (live - 1 downto 0)) $ Bound live));
                val cts = [NONE, SOME (certify lthy tinst)];
              in
                Drule.instantiate' cTs cts @{thm surj_imp_ordLeq}
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
            |> Thm.close_derivation
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
            |> Thm.close_derivation
          end;

        val rel_Grp = Lazy.lazy mk_rel_Grp;

        fun mk_rel_prems f = map2 (HOLogic.mk_Trueprop oo f) Rs Rs_copy
        fun mk_rel_concl f = HOLogic.mk_Trueprop
          (f (Term.list_comb (rel, Rs), Term.list_comb (rel, Rs_copy)));

        fun mk_rel_mono () =
          let
            val mono_prems = mk_rel_prems mk_leq;
            val mono_concl = mk_rel_concl (uncurry mk_leq);
          in
            Goal.prove_sorry lthy [] []
              (fold_rev Logic.all (Rs @ Rs_copy) (Logic.list_implies (mono_prems, mono_concl)))
              (K (mk_rel_mono_tac rel_OO_Grps (Lazy.force in_mono)))
            |> Thm.close_derivation
          end;

        fun mk_rel_cong () =
          let
            val cong_prems = mk_rel_prems (curry HOLogic.mk_eq);
            val cong_concl = mk_rel_concl HOLogic.mk_eq;
          in
            Goal.prove_sorry lthy [] []
              (fold_rev Logic.all (Rs @ Rs_copy) (Logic.list_implies (cong_prems, cong_concl)))
              (fn _ => (TRY o hyp_subst_tac lthy THEN' rtac refl) 1)
            |> Thm.close_derivation
          end;

        val rel_mono = Lazy.lazy mk_rel_mono;
        val rel_cong = Lazy.lazy mk_rel_cong;

        fun mk_rel_eq () =
          Goal.prove_sorry lthy [] []
            (mk_Trueprop_eq (Term.list_comb (relAsAs, map HOLogic.eq_const As'),
              HOLogic.eq_const CA'))
            (K (mk_rel_eq_tac live (Lazy.force rel_Grp) (Lazy.force rel_cong) (#map_id0 axioms)))
          |> Thm.close_derivation;

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
              |> Thm.close_derivation
            val goal = fold_rev Logic.all Rs (mk_Trueprop_eq (lhs, rhs));
          in
            Goal.prove_sorry lthy [] [] goal
              (K (mk_rel_conversep_tac le_thm (Lazy.force rel_mono)))
            |> Thm.close_derivation
          end;

        val rel_conversep = Lazy.lazy mk_rel_conversep;

        fun mk_rel_OO () =
          Goal.prove_sorry lthy [] []
            (fold_rev Logic.all (Rs @ Ss) (HOLogic.mk_Trueprop (mk_leq rel_OO_lhs rel_OO_rhs)))
            (fn {context = ctxt, prems = _} => mk_rel_OO_le_tac ctxt rel_OO_Grps (Lazy.force rel_eq)
              (#map_cong0 axioms) (Lazy.force map_comp) (map Lazy.force set_map))
          |> Thm.close_derivation
          |> (fn thm => @{thm antisym} OF [thm, #le_rel_OO axioms]);

        val rel_OO = Lazy.lazy mk_rel_OO;

        fun mk_in_rel () = trans OF [rel_OO_Grp, @{thm OO_Grp_alt}] RS @{thm predicate2_eqD};

        val in_rel = Lazy.lazy mk_in_rel;

        fun mk_rel_flip () =
          let
            val rel_conversep_thm = Lazy.force rel_conversep;
            val cts = map (SOME o certify lthy) Rs;
            val rel_conversep_thm' = cterm_instantiate_pos cts rel_conversep_thm;
          in
            unfold_thms lthy @{thms conversep_iff} (rel_conversep_thm' RS @{thm predicate2_eqD})
            |> singleton (Proof_Context.export names_lthy pre_names_lthy)
          end;

        val rel_flip = Lazy.lazy mk_rel_flip;

        fun mk_rel_mono_strong () =
          let
            fun mk_prem setA setB R S a b =
              HOLogic.mk_Trueprop
                (mk_Ball (setA $ x) (Term.absfree (dest_Free a)
                  (mk_Ball (setB $ y) (Term.absfree (dest_Free b)
                    (HOLogic.mk_imp (R $ a $ b, S $ a $ b))))));
            val prems = HOLogic.mk_Trueprop (Term.list_comb (rel, Rs) $ x $ y) :: 
              map6 mk_prem bnf_sets_As bnf_sets_Bs Rs Rs_copy zs ys;
            val concl = HOLogic.mk_Trueprop (Term.list_comb (rel, Rs_copy) $ x $ y);
          in
            Goal.prove_sorry lthy [] []
              (fold_rev Logic.all (x :: y :: Rs @ Rs_copy) (Logic.list_implies (prems, concl)))
              (fn {context = ctxt, prems = _} => mk_rel_mono_strong_tac ctxt (Lazy.force in_rel)
                (map Lazy.force set_map))
            |> Thm.close_derivation
          end;

        val rel_mono_strong = Lazy.lazy mk_rel_mono_strong;

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
            |> Thm.close_derivation
          end;

        val map_transfer = Lazy.lazy mk_map_transfer;

        val defs = mk_defs bnf_map_def bnf_set_defs bnf_rel_def;

        val facts = mk_facts bd_Card_order bd_Cinfinite bd_Cnotzero collect_set_map in_bd in_cong
          in_mono in_rel map_comp map_cong map_id map_transfer rel_eq rel_flip set_map
          rel_cong rel_mono rel_mono_strong rel_Grp rel_conversep rel_OO;

        val wits = map2 mk_witness bnf_wits wit_thms;

        val bnf_rel =
          Term.subst_atomic_types ((Ds ~~ deads) @ (As' ~~ alphas) @ (Bs' ~~ betas)) rel;

        val bnf = mk_bnf bnf_b Calpha live alphas betas dead deads bnf_map bnf_sets bnf_bd axioms
          defs facts wits bnf_rel;
      in
        (bnf, lthy |> note_bnf_thms fact_policy qualify bnf_b bnf)
      end;

    val one_step_defs =
      no_reflexive (bnf_map_def :: bnf_bd_def :: bnf_set_defs @ bnf_wit_defs @ [bnf_rel_def]);
  in
    (key, goals, wit_goalss, after_qed, lthy, one_step_defs)
  end;

fun register_bnf key (bnf, lthy) =
  (bnf, Local_Theory.declaration {syntax = false, pervasive = true}
    (fn phi => Data.map (Symtab.update (key, morph_bnf phi bnf))) lthy);

fun bnf_def const_policy fact_policy qualify tacs wit_tac Ds map_b rel_b set_bs =
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
        |> Conjunction.elim_balanced (length wit_goals)
        |> map2 (Conjunction.elim_balanced o length) wit_goalss
        |> map (map (Thm.close_derivation o Thm.forall_elim_vars 0));
  in
    map2 (Thm.close_derivation oo Goal.prove_sorry lthy [] [])
      goals (map (fn tac => fn {context = ctxt, prems = _} =>
        unfold_thms_tac ctxt one_step_defs THEN tac ctxt) tacs)
    |> (fn thms => after_qed mk_wit_thms (map single thms) lthy)
  end) oo prepare_def const_policy fact_policy qualify (K I) (K I) Ds map_b rel_b set_bs;

val bnf_cmd = (fn (key, goals, (triv_tac_opt, wit_goalss), after_qed, lthy, defs) =>
  let
    val wit_goals = map Logic.mk_conjunction_balanced wit_goalss;
    fun mk_triv_wit_thms tac set_maps =
      Goal.prove_sorry lthy [] [] (Logic.mk_conjunction_balanced wit_goals)
        (fn {context = ctxt, prems = _} => TRYALL Goal.conjunction_tac THEN tac ctxt set_maps)
        |> Conjunction.elim_balanced (length wit_goals)
        |> map2 (Conjunction.elim_balanced o length) wit_goalss
        |> map (map (Thm.close_derivation o Thm.forall_elim_vars 0));
    val (mk_wit_thms, nontriv_wit_goals) = 
      (case triv_tac_opt of
        NONE => (fn _ => [], map (map (rpair [])) wit_goalss)
      | SOME tac => (mk_triv_wit_thms tac, []));
  in
    Proof.unfolding ([[(defs, [])]])
      (Proof.theorem NONE (snd o register_bnf key oo after_qed mk_wit_thms)
        (map (single o rpair []) goals @ nontriv_wit_goals) lthy)
  end) oo prepare_def Do_Inline (user_policy Note_Some) I Syntax.read_typ Syntax.read_term NONE
    Binding.empty Binding.empty [];

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
  Outer_Syntax.improper_command @{command_spec "print_bnfs"}
    "print all bounded natural functors"
    (Scan.succeed (Toplevel.keep (print_bnfs o Toplevel.context_of)));

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "bnf"}
    "register a type as a bounded natural functor"
    (parse_opt_binding_colon -- Parse.typ --|
       (Parse.reserved "map" -- @{keyword ":"}) -- Parse.term --
       (Scan.option ((Parse.reserved "sets" -- @{keyword ":"}) |--
         Scan.repeat1 (Scan.unless (Parse.reserved "bd") Parse.term)) >> the_default []) --|
       (Parse.reserved "bd" -- @{keyword ":"}) -- Parse.term --
       (Scan.option ((Parse.reserved "wits" -- @{keyword ":"}) |--
         Scan.repeat1 (Scan.unless (Parse.reserved "rel") Parse.term)) >> the_default []) --
       Scan.option ((Parse.reserved "rel" -- @{keyword ":"}) |-- Parse.term)
       >> bnf_cmd);

end;
