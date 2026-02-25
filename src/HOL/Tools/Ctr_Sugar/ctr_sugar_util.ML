(*  Title:      HOL/Tools/Ctr_Sugar/ctr_sugar_util.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013

Library for wrapping existing freely generated type's constructors.
*)

signature CTR_SUGAR_UTIL =
sig
  val map_prod: ('a -> 'b) -> ('c -> 'd) -> 'a * 'c -> 'b * 'd

  val seq_conds: (bool -> 'a -> 'b) -> int -> int -> 'a list -> 'b list
  val transpose: 'a list list -> 'a list list
  val pad_list: 'a -> int -> 'a list -> 'a list
  val splice: 'a list -> 'a list -> 'a list
  val permute_like_unique: ('a * 'b -> bool) -> 'a list -> 'b list -> 'c list -> 'c list
  val permute_like: ('a * 'a -> bool) -> 'a list -> 'a list -> 'b list -> 'b list

  val mk_names: int -> string -> string list
  val mk_fresh_names: Proof.context -> int -> string -> string list * Proof.context
  val mk_TFrees': sort list -> Proof.context -> typ list * Proof.context
  val mk_TFrees: int -> Proof.context -> typ list * Proof.context
  val mk_Frees': string -> typ list -> Proof.context ->
    (term list * (string * typ) list) * Proof.context
  val mk_Freess': string -> typ list list -> Proof.context ->
    (term list list * (string * typ) list list) * Proof.context
  val mk_Frees: string -> typ list -> Proof.context -> term list * Proof.context
  val mk_Freess: string -> typ list list -> Proof.context -> term list list * Proof.context
  val dest_TFree_or_TVar: typ -> string * sort
  val resort_tfree_or_tvar: sort -> typ -> typ
  val variant_types: string list -> sort list -> Proof.context ->
    (string * sort) list * Proof.context
  val variant_tfrees: string list -> Proof.context -> typ list * Proof.context

  val base_name_of_typ: typ -> string
  val name_of_const: string -> (typ -> typ) -> term -> string

  val typ_subst_nonatomic: (typ * typ) list -> typ -> typ
  val subst_nonatomic_types: (typ * typ) list -> term -> term

  val lhs_head_of : thm -> term

  val mk_predT: typ list -> typ
  val mk_pred1T: typ -> typ

  val mk_disjIN: int -> int -> thm

  val mk_abs_def: thm -> thm
  val mk_unabs_def: int -> thm -> thm

  val mk_IfN: typ -> term list -> term list -> term
  val mk_Trueprop_eq: term * term -> term
  val mk_Trueprop_mem: term * term -> term

  val rapp: term -> term -> term

  val rtac: Proof.context -> thm -> int -> tactic
  val etac: Proof.context -> thm -> int -> tactic
  val dtac: Proof.context -> thm -> int -> tactic

  val list_all_free: term list -> term -> term
  val list_exists_free: term list -> term -> term

  val fo_match: Proof.context -> term -> term -> Type.tyenv * Envir.tenv

  val unfold_thms: Proof.context -> thm list -> thm -> thm

  val name_noted_thms: string -> string -> (string * thm list) list -> (string * thm list) list
  val substitute_noted_thm: (string * thm list) list -> morphism

  val standard_binding: binding
  val parse_binding_colon: binding parser
  val parse_opt_binding_colon: binding parser

  val ss_only: thm list -> Proof.context -> Proof.context

  (*parameterized thms*)
  val eqTrueI: thm
  val eqFalseI: thm

  val WRAP: ('a -> tactic) -> ('a -> tactic) -> 'a list -> tactic -> tactic
  val WRAP': ('a -> int -> tactic) -> ('a -> int -> tactic) -> 'a list -> (int -> tactic) -> int ->
    tactic
  val CONJ_WRAP_GEN: tactic -> ('a -> tactic) -> 'a list -> tactic
  val CONJ_WRAP_GEN': (int -> tactic) -> ('a -> int -> tactic) -> 'a list -> int -> tactic
  val CONJ_WRAP: ('a -> tactic) -> 'a list -> tactic
  val CONJ_WRAP': ('a -> int -> tactic) -> 'a list -> int -> tactic
end;

structure Ctr_Sugar_Util : CTR_SUGAR_UTIL =
struct

fun map_prod f g (x, y) = (f x, g y);

fun seq_conds f n k xs =
  if k = n then
    map (f false) (take (k - 1) xs)
  else
    let val (negs, pos) = split_last (take k xs) in
      map (f false) negs @ [f true pos]
    end;

fun transpose [] = []
  | transpose ([] :: xss) = transpose xss
  | transpose xss = map hd xss :: transpose (map tl xss);

fun pad_list x n xs = xs @ replicate (n - length xs) x;

fun splice xs ys = flat (map2 (fn x => fn y => [x, y]) xs ys);

fun permute_like_unique eq xs xs' ys =
  map (nth ys o (fn y => find_index (fn x => eq (x, y)) xs)) xs';

fun fresh eq x names =
  (case AList.lookup eq names x of
    NONE => ((x, 0), (x, 0) :: names)
  | SOME n => ((x, n + 1), AList.update eq (x, n + 1) names));

fun deambiguate eq xs = fst (fold_map (fresh eq) xs []);

fun permute_like eq xs xs' =
  permute_like_unique (eq_pair eq (op =)) (deambiguate eq xs) (deambiguate eq xs');

fun mk_names n x = if n = 1 then [x] else map (fn i => x ^ string_of_int i) (1 upto n);
fun mk_fresh_names ctxt = (fn xs => Variable.variant_fixes xs ctxt) oo mk_names;

val mk_TFrees' = apfst (map TFree) oo Variable.invent_types;

fun mk_TFrees n = mk_TFrees' (replicate n \<^sort>\<open>type\<close>);

fun mk_Frees' x Ts ctxt = mk_fresh_names ctxt (length Ts) x |>> (fn xs => `(map Free) (xs ~~ Ts));
fun mk_Freess' x Tss = @{fold_map 2} mk_Frees' (mk_names (length Tss) x) Tss #>> split_list;

fun mk_Frees x Ts ctxt = mk_fresh_names ctxt (length Ts) x |>> (fn xs => map2 (curry Free) xs Ts);
fun mk_Freess x Tss = @{fold_map 2} mk_Frees (mk_names (length Tss) x) Tss;

fun dest_TFree_or_TVar (TFree sS) = sS
  | dest_TFree_or_TVar (TVar ((s, _), S)) = (s, S)
  | dest_TFree_or_TVar _ = error "Invalid type argument";

fun resort_tfree_or_tvar S (TFree (s, _)) = TFree (s, S)
  | resort_tfree_or_tvar S (TVar (x, _)) = TVar (x, S);

fun ensure_prefix pre s = s |> not (String.isPrefix pre s) ? prefix pre;

fun variant_types ss Ss ctxt =
  let
    val (tfrees, _) =
      @{fold_map 2} (fn s => fn S => Name.variant s #> apfst (rpair S))
        ss Ss (Variable.names_of ctxt);
    val ctxt' = fold (Variable.declare_constraints o Logic.mk_type o TFree) tfrees ctxt;
  in (tfrees, ctxt') end;

fun variant_tfrees ss =
  apfst (map TFree) o
    variant_types (map (ensure_prefix "'") ss) (replicate (length ss) \<^sort>\<open>type\<close>);

fun add_components_of_typ (Type (s, Ts)) =
    cons (Long_Name.base_name s) #> fold_rev add_components_of_typ Ts
  | add_components_of_typ _ = I;

fun base_name_of_typ T = space_implode "_" (add_components_of_typ T []);

fun suffix_with_type s (Type (_, Ts)) =
    space_implode "_" (s :: fold_rev add_components_of_typ Ts [])
  | suffix_with_type s _ = s;

fun name_of_const what get_fcT t =
  (case head_of t of
    Const (s, T) => suffix_with_type s (get_fcT T)
  | Free (s, T) => suffix_with_type s (get_fcT T)
  | _ => error ("Cannot extract name of " ^ what));

(*Replace each Ti by Ui (starting from the leaves); inst = [(T1, U1), ..., (Tn, Un)].*)
fun typ_subst_nonatomic [] = I
  | typ_subst_nonatomic inst =
    let
      fun subst (Type (s, Ts)) = perhaps (AList.lookup (op =) inst) (Type (s, map subst Ts))
        | subst T = perhaps (AList.lookup (op =) inst) T;
    in subst end;

fun subst_nonatomic_types [] = I
  | subst_nonatomic_types inst = map_types (typ_subst_nonatomic inst);

fun lhs_head_of thm =
  Term.head_of (fst (HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of thm))));

fun mk_predT Ts = Ts ---> HOLogic.boolT;
fun mk_pred1T T = mk_predT [T];

fun mk_disjIN 1 1 = @{thm TrueE[OF TrueI]}
  | mk_disjIN _ 1 = disjI1
  | mk_disjIN 2 2 = disjI2
  | mk_disjIN n m = (mk_disjIN (n - 1) (m - 1)) RS disjI2;

fun mk_abs_def thm = Drule.abs_def (thm RS eq_reflection handle THM _ => thm);
fun mk_unabs_def n = funpow n (fn thm => thm RS fun_cong);

fun mk_IfN _ _ [t] = t
  | mk_IfN T (c :: cs) (t :: ts) =
    Const (\<^const_name>\<open>If\<close>, HOLogic.boolT --> T --> T --> T) $ c $ t $ mk_IfN T cs ts;

val mk_Trueprop_eq = HOLogic.mk_Trueprop o HOLogic.mk_eq;
val mk_Trueprop_mem = HOLogic.mk_Trueprop o HOLogic.mk_mem;

fun rapp u t = betapply (t, u);

fun list_quant_free quant_const =
  fold_rev (fn Free (xT as (_, T)) => fn P => quant_const T $ Term.absfree xT P);

val list_all_free = list_quant_free HOLogic.all_const;
val list_exists_free = list_quant_free HOLogic.exists_const;

fun fo_match ctxt t pat =
  let val thy = Proof_Context.theory_of ctxt
  in Pattern.first_order_match thy (pat, t) (Vartab.empty, Vartab.empty) end;

val unfold_thms = Local_Defs.unfold0;

fun name_noted_thms _ _ [] = []
  | name_noted_thms qualifier base ((local_name, thms) :: noted) =
    if Long_Name.base_name local_name = base then
      let
        val name = Long_Name.append qualifier base;
        val pos = Position.thread_data ();
        val thms' = Thm_Name.list (name, pos) thms |> map (uncurry Thm.name_derivation);
      in (local_name, thms') :: noted end
    else ((local_name, thms) :: name_noted_thms qualifier base noted);

fun substitute_noted_thm noted =
  let val tab = fold (fold (Termtab.default o `Thm.full_prop_of) o snd) noted Termtab.empty in
    Morphism.thm_morphism "Ctr_Sugar_Util.substitute_noted_thm"
      (perhaps (Termtab.lookup tab o Thm.full_prop_of) o Drule.zero_var_indexes)
  end;

(* The standard binding stands for a name generated following the canonical convention (e.g.,
   "is_Nil" from "Nil"). In contrast, the empty binding is either the standard binding or no
   binding at all, depending on the context. *)
val standard_binding = \<^binding>\<open>_\<close>;

val parse_binding_colon = Parse.binding --| \<^keyword>\<open>:\<close>;
val parse_opt_binding_colon = Scan.optional parse_binding_colon Binding.empty;

fun ss_only thms ctxt = ctxt |> put_simpset HOL_basic_ss |> Simplifier.clear_simpset |> Simplifier.add_simps thms;

val eqTrueI = @{thm iffD2[OF eq_True]};
val eqFalseI =  @{thm iffD2[OF eq_False]};

(*Tactical WRAP surrounds a static given tactic (core) with two deterministic chains of tactics*)
fun WRAP gen_before gen_after xs core_tac =
  fold_rev (fn x => fn tac => gen_before x THEN tac THEN gen_after x) xs core_tac;

fun WRAP' gen_before gen_after xs core_tac =
  fold_rev (fn x => fn tac => gen_before x THEN' tac THEN' gen_after x) xs core_tac;

fun CONJ_WRAP_GEN conj_tac gen_tac xs =
  let val (butlast, last) = split_last xs;
  in WRAP (fn thm => conj_tac THEN gen_tac thm) (K all_tac) butlast (gen_tac last) end;

fun CONJ_WRAP_GEN' conj_tac gen_tac xs =
  let val (butlast, last) = split_last xs;
  in WRAP' (fn thm => conj_tac THEN' gen_tac thm) (K (K all_tac)) butlast (gen_tac last) end;

fun CONJ_WRAP gen_tac = CONJ_WRAP_GEN (resolve0_tac [conjI] 1) gen_tac;
fun CONJ_WRAP' gen_tac = CONJ_WRAP_GEN' (resolve0_tac [conjI]) gen_tac;

fun rtac ctxt thm = resolve_tac ctxt [thm];
fun etac ctxt thm = eresolve_tac ctxt [thm];
fun dtac ctxt thm = dresolve_tac ctxt [thm];

end;
