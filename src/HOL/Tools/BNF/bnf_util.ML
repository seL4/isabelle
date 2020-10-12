(*  Title:      HOL/Tools/BNF/bnf_util.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Library for bounded natural functors.
*)

signature BNF_UTIL =
sig
  include CTR_SUGAR_UTIL
  include BNF_FP_REC_SUGAR_UTIL

  val transfer_plugin: string

  val unflatt: 'a list list list -> 'b list -> 'b list list list
  val unflattt: 'a list list list list -> 'b list -> 'b list list list list

  val mk_TFreess: int list -> Proof.context -> typ list list * Proof.context
  val mk_Freesss: string -> typ list list list -> Proof.context ->
    term list list list * Proof.context
  val mk_Freessss: string -> typ list list list list -> Proof.context ->
    term list list list list * Proof.context
  val nonzero_string_of_int: int -> string

  val binder_fun_types: typ -> typ list
  val body_fun_type: typ -> typ
  val strip_fun_type: typ -> typ list * typ
  val strip_typeN: int -> typ -> typ list * typ

  val mk_pred2T: typ -> typ -> typ
  val mk_relT: typ * typ -> typ
  val dest_relT: typ -> typ * typ
  val dest_pred2T: typ -> typ * typ
  val mk_sumT: typ * typ -> typ

  val ctwo: term
  val fst_const: typ -> term
  val snd_const: typ -> term
  val Id_const: typ -> term

  val enforce_type: Proof.context -> (typ -> typ) -> typ -> term -> term

  val mk_Ball: term -> term -> term
  val mk_Bex: term -> term -> term
  val mk_Card_order: term -> term
  val mk_Field: term -> term
  val mk_Gr: term -> term -> term
  val mk_Grp: term -> term -> term
  val mk_UNION: term -> term -> term
  val mk_Union: typ -> term
  val mk_card_binop: string -> (typ * typ -> typ) -> term -> term -> term
  val mk_card_of: term -> term
  val mk_card_order: term -> term
  val mk_cexp: term -> term -> term
  val mk_cinfinite: term -> term
  val mk_collect: term list -> typ -> term
  val mk_converse: term -> term
  val mk_conversep: term -> term
  val mk_cprod: term -> term -> term
  val mk_csum: term -> term -> term
  val mk_dir_image: term -> term -> term
  val mk_eq_onp: term -> term
  val mk_rel_fun: term -> term -> term
  val mk_image: term -> term
  val mk_in: term list -> term list -> typ -> term
  val mk_inj: term -> term
  val mk_leq: term -> term -> term
  val mk_ordLeq: term -> term -> term
  val mk_rel_comp: term * term -> term
  val mk_rel_compp: term * term -> term
  val mk_vimage2p: term -> term -> term
  val mk_reflp: term -> term
  val mk_symp: term -> term
  val mk_transp: term -> term
  val mk_union: term * term -> term

  (*parameterized terms*)
  val mk_nthN: int -> term -> int -> term

  (*parameterized thms*)
  val prod_injectD: thm
  val prod_injectI: thm
  val ctrans: thm
  val id_apply: thm
  val meta_mp: thm
  val meta_spec: thm
  val o_apply: thm
  val rel_funD: thm
  val rel_funI: thm
  val set_mp: thm
  val set_rev_mp: thm
  val subset_UNIV: thm

  val mk_conjIN: int -> thm
  val mk_nthI: int -> int -> thm
  val mk_nth_conv: int -> int -> thm
  val mk_ordLeq_csum: int -> int -> thm -> thm
  val mk_pointful: Proof.context -> thm -> thm
  val mk_rel_funDN: int -> thm -> thm
  val mk_rel_funDN_rotated: int -> thm -> thm
  val mk_sym: thm -> thm
  val mk_trans: thm -> thm -> thm
  val mk_UnIN: int -> int -> thm
  val mk_Un_upper: int -> int -> thm

  val is_refl_bool: term -> bool
  val is_refl: thm -> bool
  val is_concl_refl: thm -> bool
  val no_refl: thm list -> thm list
  val no_reflexive: thm list -> thm list

  val parse_type_args_named_constrained: (binding option * (string * string option)) list parser
  val parse_map_rel_pred_bindings: (binding * binding * binding) parser

  val typedef: binding * (string * sort) list * mixfix -> term ->
    (binding * binding) option -> (Proof.context -> tactic) ->
    local_theory -> (string * Typedef.info) * local_theory
end;

structure BNF_Util : BNF_UTIL =
struct

open Ctr_Sugar_Util
open BNF_FP_Rec_Sugar_Util

val transfer_plugin = Plugin_Name.declare_setup \<^binding>\<open>transfer\<close>;


(* Library proper *)

fun unfla0 xs = fold_map (fn _ => fn (c :: cs) => (c, cs)) xs;
fun unflat0 xss = fold_map unfla0 xss;
fun unflatt0 xsss = fold_map unflat0 xsss;
fun unflattt0 xssss = fold_map unflatt0 xssss;

fun unflatt xsss = fst o unflatt0 xsss;
fun unflattt xssss = fst o unflattt0 xssss;

val parse_type_arg_constrained =
  Parse.type_ident -- Scan.option (\<^keyword>\<open>::\<close> |-- Parse.!!! Parse.sort);

val parse_type_arg_named_constrained =
   (Parse.reserved "dead" >> K NONE || parse_opt_binding_colon >> SOME) --
   parse_type_arg_constrained;

val parse_type_args_named_constrained =
  parse_type_arg_constrained >> (single o pair (SOME Binding.empty)) ||
  \<^keyword>\<open>(\<close> |-- Parse.!!! (Parse.list1 parse_type_arg_named_constrained --| \<^keyword>\<open>)\<close>) ||
  Scan.succeed [];

val parse_map_rel_pred_binding = Parse.name --| \<^keyword>\<open>:\<close> -- Parse.binding;

val no_map_rel = (Binding.empty, Binding.empty, Binding.empty);

fun extract_map_rel_pred ("map", m) = (fn (_, r, p) => (m, r, p))
  | extract_map_rel_pred ("rel", r) = (fn (m, _, p) => (m, r, p))
  | extract_map_rel_pred ("pred", p) = (fn (m, r, _) => (m, r, p))
  | extract_map_rel_pred (s, _) = error ("Unknown label " ^ quote s ^ " (expected \"map\" or \"rel\")");

val parse_map_rel_pred_bindings =
  \<^keyword>\<open>for\<close> |-- Scan.repeat parse_map_rel_pred_binding
    >> (fn ps => fold extract_map_rel_pred ps no_map_rel)
  || Scan.succeed no_map_rel;

fun typedef (b, Ts, mx) set opt_morphs tac lthy =
  let
    (*Work around loss of qualification in "typedef" axioms by replicating it in the name*)
    val b' = fold_rev Binding.prefix_name (map (suffix "_" o fst) (Binding.path_of b)) b;

    val default_bindings = Typedef.default_bindings (Binding.concealed b');
    val bindings =
      (case opt_morphs of
        NONE => default_bindings
      | SOME (Rep_name, Abs_name) =>
         {Rep_name = Binding.concealed Rep_name,
          Abs_name = Binding.concealed Abs_name,
          type_definition_name = #type_definition_name default_bindings});

    val ((name, info), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> Typedef.add_typedef {overloaded = false} (b', Ts, mx) set (SOME bindings) tac
      ||> `Local_Theory.end_nested;
    val phi = Proof_Context.export_morphism lthy_old lthy;
  in
    ((name, Typedef.transform_info phi info), lthy)
  end;


(* Term construction *)

(** Fresh variables **)

fun nonzero_string_of_int 0 = ""
  | nonzero_string_of_int n = string_of_int n;

val mk_TFreess = fold_map mk_TFrees;

fun mk_Freesss x Tsss = @{fold_map 2} mk_Freess (mk_names (length Tsss) x) Tsss;
fun mk_Freessss x Tssss = @{fold_map 2} mk_Freesss (mk_names (length Tssss) x) Tssss;


(** Types **)

(*maps [T1,...,Tn]--->T to ([T1,T2,...,Tn], T)*)
fun strip_typeN 0 T = ([], T)
  | strip_typeN n (Type (\<^type_name>\<open>fun\<close>, [T, T'])) = strip_typeN (n - 1) T' |>> cons T
  | strip_typeN _ T = raise TYPE ("strip_typeN", [T], []);

(*maps [T1,...,Tn]--->T-->U to ([T1,T2,...,Tn], T-->U), where U is not a function type*)
fun strip_fun_type T = strip_typeN (num_binder_types T - 1) T;

val binder_fun_types = fst o strip_fun_type;
val body_fun_type = snd o strip_fun_type;

fun mk_pred2T T U = mk_predT [T, U];
val mk_relT = HOLogic.mk_setT o HOLogic.mk_prodT;
val dest_relT = HOLogic.dest_prodT o HOLogic.dest_setT;
val dest_pred2T = apsnd Term.domain_type o Term.dest_funT;
fun mk_sumT (LT, RT) = Type (\<^type_name>\<open>Sum_Type.sum\<close>, [LT, RT]);


(** Constants **)

fun fst_const T = Const (\<^const_name>\<open>fst\<close>, T --> fst (HOLogic.dest_prodT T));
fun snd_const T = Const (\<^const_name>\<open>snd\<close>, T --> snd (HOLogic.dest_prodT T));
fun Id_const T = Const (\<^const_name>\<open>Id\<close>, mk_relT (T, T));


(** Operators **)

fun enforce_type ctxt get_T T t =
  Term.subst_TVars (tvar_subst (Proof_Context.theory_of ctxt) [get_T (fastype_of t)] [T]) t;

fun mk_converse R =
  let
    val RT = dest_relT (fastype_of R);
    val RST = mk_relT (snd RT, fst RT);
  in Const (\<^const_name>\<open>converse\<close>, fastype_of R --> RST) $ R end;

fun mk_rel_comp (R, S) =
  let
    val RT = fastype_of R;
    val ST = fastype_of S;
    val RST = mk_relT (fst (dest_relT RT), snd (dest_relT ST));
  in Const (\<^const_name>\<open>relcomp\<close>, RT --> ST --> RST) $ R $ S end;

fun mk_Gr A f =
  let val ((AT, BT), FT) = `dest_funT (fastype_of f);
  in Const (\<^const_name>\<open>Gr\<close>, HOLogic.mk_setT AT --> FT --> mk_relT (AT, BT)) $ A $ f end;

fun mk_conversep R =
  let
    val RT = dest_pred2T (fastype_of R);
    val RST = mk_pred2T (snd RT) (fst RT);
  in Const (\<^const_name>\<open>conversep\<close>, fastype_of R --> RST) $ R end;

fun mk_rel_compp (R, S) =
  let
    val RT = fastype_of R;
    val ST = fastype_of S;
    val RST = mk_pred2T (fst (dest_pred2T RT)) (snd (dest_pred2T ST));
  in Const (\<^const_name>\<open>relcompp\<close>, RT --> ST --> RST) $ R $ S end;

fun mk_Grp A f =
  let val ((AT, BT), FT) = `dest_funT (fastype_of f);
  in Const (\<^const_name>\<open>Grp\<close>, HOLogic.mk_setT AT --> FT --> mk_pred2T AT BT) $ A $ f end;

fun mk_image f =
  let val (T, U) = dest_funT (fastype_of f);
  in Const (\<^const_name>\<open>image\<close>, (T --> U) --> HOLogic.mk_setT T --> HOLogic.mk_setT U) $ f end;

fun mk_Ball X f =
  Const (\<^const_name>\<open>Ball\<close>, fastype_of X --> fastype_of f --> HOLogic.boolT) $ X $ f;

fun mk_Bex X f =
  Const (\<^const_name>\<open>Bex\<close>, fastype_of X --> fastype_of f --> HOLogic.boolT) $ X $ f;

fun mk_UNION X f =
  let
    val (T, U) = dest_funT (fastype_of f);
  in
    Const (\<^const_name>\<open>Sup\<close>, HOLogic.mk_setT U --> U)
      $ (Const (\<^const_name>\<open>image\<close>, (T --> U) --> fastype_of X --> HOLogic.mk_setT U) $ f $ X)
  end;

fun mk_Union T =
  Const (\<^const_name>\<open>Sup\<close>, HOLogic.mk_setT (HOLogic.mk_setT T) --> HOLogic.mk_setT T);

val mk_union = HOLogic.mk_binop \<^const_name>\<open>sup\<close>;

fun mk_Field r =
  let val T = fst (dest_relT (fastype_of r));
  in Const (\<^const_name>\<open>Field\<close>, mk_relT (T, T) --> HOLogic.mk_setT T) $ r end;

fun mk_card_order bd =
  let
    val T = fastype_of bd;
    val AT = fst (dest_relT T);
  in
    Const (\<^const_name>\<open>card_order_on\<close>, HOLogic.mk_setT AT --> T --> HOLogic.boolT) $
      HOLogic.mk_UNIV AT $ bd
  end;

fun mk_Card_order bd =
  let
    val T = fastype_of bd;
    val AT = fst (dest_relT T);
  in
    Const (\<^const_name>\<open>card_order_on\<close>, HOLogic.mk_setT AT --> T --> HOLogic.boolT) $
      mk_Field bd $ bd
  end;

fun mk_cinfinite bd = Const (\<^const_name>\<open>cinfinite\<close>, fastype_of bd --> HOLogic.boolT) $ bd;

fun mk_ordLeq t1 t2 =
  HOLogic.mk_mem (HOLogic.mk_prod (t1, t2),
    Const (\<^const_name>\<open>ordLeq\<close>, mk_relT (fastype_of t1, fastype_of t2)));

fun mk_card_of A =
  let
    val AT = fastype_of A;
    val T = HOLogic.dest_setT AT;
  in
    Const (\<^const_name>\<open>card_of\<close>, AT --> mk_relT (T, T)) $ A
  end;

fun mk_dir_image r f =
  let val (T, U) = dest_funT (fastype_of f);
  in Const (\<^const_name>\<open>dir_image\<close>, mk_relT (T, T) --> (T --> U) --> mk_relT (U, U)) $ r $ f end;

fun mk_rel_fun R S =
  let
    val ((RA, RB), RT) = `dest_pred2T (fastype_of R);
    val ((SA, SB), ST) = `dest_pred2T (fastype_of S);
  in Const (\<^const_name>\<open>rel_fun\<close>, RT --> ST --> mk_pred2T (RA --> SA) (RB --> SB)) $ R $ S end;

(*FIXME: "x"?*)
(*(nth sets i) must be of type "T --> 'ai set"*)
fun mk_in As sets T =
  let
    fun in_single set A =
      let val AT = fastype_of A;
      in Const (\<^const_name>\<open>less_eq\<close>, AT --> AT --> HOLogic.boolT) $ (set $ Free ("x", T)) $ A end;
  in
    if null sets then HOLogic.mk_UNIV T
    else HOLogic.mk_Collect ("x", T, foldr1 (HOLogic.mk_conj) (map2 in_single sets As))
  end;

fun mk_inj t =
  let val T as Type (\<^type_name>\<open>fun\<close>, [domT, _]) = fastype_of t in
    Const (\<^const_name>\<open>inj_on\<close>, T --> HOLogic.mk_setT domT --> HOLogic.boolT) $ t
      $ HOLogic.mk_UNIV domT
  end;

fun mk_leq t1 t2 =
  Const (\<^const_name>\<open>less_eq\<close>, fastype_of t1 --> fastype_of t2 --> HOLogic.boolT) $ t1 $ t2;

fun mk_card_binop binop typop t1 t2 =
  let
    val (T1, relT1) = `(fst o dest_relT) (fastype_of t1);
    val (T2, relT2) = `(fst o dest_relT) (fastype_of t2);
  in Const (binop, relT1 --> relT2 --> mk_relT (typop (T1, T2), typop (T1, T2))) $ t1 $ t2 end;

val mk_csum = mk_card_binop \<^const_name>\<open>csum\<close> mk_sumT;
val mk_cprod = mk_card_binop \<^const_name>\<open>cprod\<close> HOLogic.mk_prodT;
val mk_cexp = mk_card_binop \<^const_name>\<open>cexp\<close> (op --> o swap);
val ctwo = \<^term>\<open>ctwo\<close>;

fun mk_collect xs defT =
  let val T = (case xs of [] => defT | (x::_) => fastype_of x);
  in Const (\<^const_name>\<open>collect\<close>, HOLogic.mk_setT T --> T) $ (HOLogic.mk_set T xs) end;

fun mk_vimage2p f g =
  let
    val (T1, T2) = dest_funT (fastype_of f);
    val (U1, U2) = dest_funT (fastype_of g);
  in
    Const (\<^const_name>\<open>vimage2p\<close>,
      (T1 --> T2) --> (U1 --> U2) --> mk_pred2T T2 U2 --> mk_pred2T T1 U1) $ f $ g
  end;

fun mk_eq_onp P =
  let
    val T = domain_type (fastype_of P);
  in
    Const (\<^const_name>\<open>eq_onp\<close>, (T --> HOLogic.boolT) --> T --> T --> HOLogic.boolT) $ P
  end;

fun mk_pred name R =
  Const (name, uncurry mk_pred2T (fastype_of R |> dest_pred2T) --> HOLogic.boolT) $ R;
val mk_reflp = mk_pred \<^const_name>\<open>reflp\<close>;
val mk_symp = mk_pred \<^const_name>\<open>symp\<close>;
val mk_transp =  mk_pred \<^const_name>\<open>transp\<close>;

fun mk_trans thm1 thm2 = trans OF [thm1, thm2];
fun mk_sym thm = thm RS sym;

val prod_injectD = @{thm iffD1[OF prod.inject]};
val prod_injectI = @{thm iffD2[OF prod.inject]};
val ctrans = @{thm ordLeq_transitive};
val id_apply = @{thm id_apply};
val meta_mp = @{thm meta_mp};
val meta_spec = @{thm meta_spec};
val o_apply = @{thm o_apply};
val rel_funD = @{thm rel_funD};
val rel_funI = @{thm rel_funI};
val set_mp = @{thm set_mp};
val set_rev_mp = @{thm set_rev_mp};
val subset_UNIV = @{thm subset_UNIV};

fun mk_pointful ctxt thm = unfold_thms ctxt [o_apply] (thm RS fun_cong);

fun mk_nthN 1 t 1 = t
  | mk_nthN _ t 1 = HOLogic.mk_fst t
  | mk_nthN 2 t 2 = HOLogic.mk_snd t
  | mk_nthN n t m = mk_nthN (n - 1) (HOLogic.mk_snd t) (m - 1);

fun mk_nth_conv n m =
  let
    fun thm b = if b then @{thm fstI} else @{thm sndI};
    fun mk_nth_conv _ 1 1 = refl
      | mk_nth_conv _ _ 1 = @{thm fst_conv}
      | mk_nth_conv _ 2 2 = @{thm snd_conv}
      | mk_nth_conv b _ 2 = @{thm snd_conv} RS thm b
      | mk_nth_conv b n m = mk_nth_conv false (n - 1) (m - 1) RS thm b;
  in mk_nth_conv (not (m = n)) n m end;

fun mk_nthI 1 1 = @{thm TrueE[OF TrueI]}
  | mk_nthI n m = fold (curry op RS) (replicate (m - 1) @{thm sndI})
    (if m = n then @{thm TrueE[OF TrueI]} else @{thm fstI});

fun mk_conjIN 1 = @{thm TrueE[OF TrueI]}
  | mk_conjIN n = mk_conjIN (n - 1) RSN (2, conjI);

fun mk_ordLeq_csum 1 1 thm = thm
  | mk_ordLeq_csum _ 1 thm = @{thm ordLeq_transitive} OF [thm, @{thm ordLeq_csum1}]
  | mk_ordLeq_csum 2 2 thm = @{thm ordLeq_transitive} OF [thm, @{thm ordLeq_csum2}]
  | mk_ordLeq_csum n m thm = @{thm ordLeq_transitive} OF
    [mk_ordLeq_csum (n - 1) (m - 1) thm, @{thm ordLeq_csum2[OF Card_order_csum]}];

fun mk_rel_funDN n = funpow n (fn thm => thm RS rel_funD);

val mk_rel_funDN_rotated = rotate_prems ~1 oo mk_rel_funDN;

local
  fun mk_Un_upper' 0 = @{thm subset_refl}
    | mk_Un_upper' 1 = @{thm Un_upper1}
    | mk_Un_upper' k = Library.foldr (op RS o swap)
      (replicate (k - 1) @{thm subset_trans[OF Un_upper1]}, @{thm Un_upper1});
in
  fun mk_Un_upper 1 1 = @{thm subset_refl}
    | mk_Un_upper n 1 = mk_Un_upper' (n - 2) RS @{thm subset_trans[OF Un_upper1]}
    | mk_Un_upper n m = mk_Un_upper' (n - m) RS @{thm subset_trans[OF Un_upper2]};
end;

local
  fun mk_UnIN' 0 = @{thm UnI2}
    | mk_UnIN' m = mk_UnIN' (m - 1) RS @{thm UnI1};
in
  fun mk_UnIN 1 1 = @{thm TrueE[OF TrueI]}
    | mk_UnIN n 1 = Library.foldr1 (op RS o swap) (replicate (n - 1) @{thm UnI1})
    | mk_UnIN n m = mk_UnIN' (n - m)
end;

fun is_refl_bool t =
  op aconv (HOLogic.dest_eq t)
  handle TERM _ => false;

fun is_refl_prop t =
  op aconv (HOLogic.dest_eq (HOLogic.dest_Trueprop t))
  handle TERM _ => false;

val is_refl = is_refl_prop o Thm.prop_of;
val is_concl_refl = is_refl_prop o Logic.strip_imp_concl o Thm.prop_of;

val no_refl = filter_out is_refl;
val no_reflexive = filter_out Thm.is_reflexive;

end;
