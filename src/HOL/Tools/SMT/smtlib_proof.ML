(*  Title:      HOL/Tools/SMT/smtlib_proof.ML
    Author:     Sascha Boehme, TU Muenchen
    Author:     Mathias Fleury, ENS Rennes
    Author:     Jasmin Blanchette, TU Muenchen

SMT-LIB-2-style proofs: parsing and abstract syntax tree.
*)

signature SMTLIB_PROOF =
sig
  datatype 'b shared = Tree of SMTLIB.tree | Term of term | Proof of 'b | None
  type ('a, 'b) context

  val mk_context: Proof.context -> int -> 'b shared Symtab.table -> typ Symtab.table ->
    term Symtab.table -> 'a -> ('a, 'b) context
  val empty_context: Proof.context -> typ Symtab.table -> term Symtab.table -> ('a list, 'b) context
  val ctxt_of: ('a, 'b) context -> Proof.context
  val lookup_binding: ('a, 'b) context -> string -> 'b shared
  val update_binding: string * 'b shared -> ('a, 'b) context -> ('a, 'b) context
  val with_bindings: (string * 'b shared) list -> (('a, 'b) context -> 'c * ('d, 'b) context) ->
    ('a, 'b) context -> 'c * ('d, 'b) context
  val next_id: ('a, 'b) context -> int * ('a, 'b) context
  val with_fresh_names: (('a list, 'b) context ->
    term * ((string * (string * typ)) list, 'b) context) -> ('c, 'b) context -> (term * string list)

  (*type and term parsers*)
  type type_parser = SMTLIB.tree * typ list -> typ option
  type term_parser = SMTLIB.tree * term list -> term option
  val add_type_parser: type_parser -> Context.generic -> Context.generic
  val add_term_parser: term_parser -> Context.generic -> Context.generic

  exception SMTLIB_PARSE of string * SMTLIB.tree

  val declare_fun: string -> typ -> ((string * typ) list, 'a) context ->
    ((string * typ) list, 'a) context
  val dest_binding: SMTLIB.tree -> string * 'a shared
  val type_of: ('a, 'b) context -> SMTLIB.tree -> typ
  val term_of: SMTLIB.tree -> ((string * (string * typ)) list, 'a) context ->
    term * ((string * (string * typ)) list, 'a) context

  (*name bindings*)
  type name_bindings
  val empty_name_binding: name_bindings
  val update_name_binding: Symtab.key * SMTLIB.tree -> name_bindings -> name_bindings
  val extract_name_bindings: SMTLIB.tree -> name_bindings -> name_bindings * string list
  val expand_name_bindings: SMTLIB.tree -> name_bindings -> SMTLIB.tree * name_bindings
  val extract_and_update_name_bindings: SMTLIB.tree -> name_bindings ->
     (SMTLIB.tree * name_bindings) * string list
  val remove_name_bindings: SMTLIB.tree -> SMTLIB.tree
end;

structure SMTLIB_Proof: SMTLIB_PROOF =
struct

(* proof parser context *)

datatype 'b shared = Tree of SMTLIB.tree | Term of term | Proof of 'b | None

type ('a, 'b) context = {
  ctxt: Proof.context,
  id: int,
  syms: 'b shared Symtab.table,
  typs: typ Symtab.table,
  funs: term Symtab.table,
  extra: 'a}

fun mk_context ctxt id syms typs funs extra: ('a, 'b) context =
  {ctxt = ctxt, id = id, syms = syms, typs = typs, funs = funs, extra = extra}

fun empty_context ctxt typs funs = mk_context ctxt 1 Symtab.empty typs funs []

fun ctxt_of ({ctxt, ...}: ('a, 'b) context) = ctxt

fun lookup_binding ({syms, ...}: ('a, 'b) context) =
  the_default None o Symtab.lookup syms

fun map_syms f ({ctxt, id, syms, typs, funs, extra}: ('a, 'b) context) =
  mk_context ctxt id (f syms) typs funs extra

fun update_binding b = map_syms (Symtab.update b)

fun with_bindings bs f cx =
  let val bs' = map (lookup_binding cx o fst) bs
  in
    cx
    |> fold update_binding bs
    |> f
    ||> fold2 (fn (name, _) => update_binding o pair name) bs bs'
  end

fun next_id ({ctxt, id, syms, typs, funs, extra}: ('a, 'b) context) =
  (id, mk_context ctxt (id + 1) syms typs funs extra)

fun with_fresh_names f ({ctxt, id, syms, typs, funs, ...}: ('a, 'b) context) =
  let
    fun bind (_, v as (_, T)) t = Logic.all_const T $ Term.absfree v t

    val needs_inferT = equal Term.dummyT orf Term.is_TVar
    val needs_infer = Term.exists_type (Term.exists_subtype needs_inferT)
    fun infer_types ctxt =
      singleton (Type_Infer_Context.infer_types ctxt) #>
      singleton (Proof_Context.standard_term_check_finish ctxt)
    fun infer ctxt t = if needs_infer t then infer_types ctxt t else t

    val (t, {ctxt = ctxt', extra = names, ...}: ((string * (string * typ)) list, 'b) context) =
      f (mk_context ctxt id syms typs funs [])
    val t' = infer ctxt' (fold_rev bind names (HOLogic.mk_Trueprop t))
  in
    (t', map fst names)
  end

fun lookup_typ ({typs, ...}: ('a, 'b) context) = Symtab.lookup typs
fun lookup_fun ({funs, ...}: ('a, 'b) context) = Symtab.lookup funs


(* core type and term parser *)

fun core_type_parser (SMTLIB.Sym "Bool", []) = SOME \<^typ>\<open>HOL.bool\<close>
  | core_type_parser (SMTLIB.Sym "Int", []) = SOME \<^typ>\<open>Int.int\<close>
  | core_type_parser _ = NONE

fun mk_unary n t =
  let val T = fastype_of t
  in Const (n, T --> T) $ t end

fun mk_binary' n T U t1 t2 = Const (n, [T, T] ---> U) $ t1 $ t2

fun mk_binary n t1 t2 =
  let val T = fastype_of t1
  in mk_binary' n T T t1 t2 end

fun mk_rassoc f t ts =
  let val us = rev (t :: ts)
  in fold f (tl us) (hd us) end

fun mk_lassoc f t ts = fold (fn u1 => fn u2 => f u2 u1) ts t

fun mk_lassoc' n = mk_lassoc (mk_binary n)

fun mk_binary_pred n S t1 t2 =
  let
    val T1 = fastype_of t1
    val T2 = fastype_of t2
    val T =
      if T1 <> Term.dummyT then T1
      else if T2 <> Term.dummyT then T2
      else TVar (("?a", serial ()), S)
  in mk_binary' n T \<^typ>\<open>HOL.bool\<close> t1 t2 end

fun mk_less t1 t2 = mk_binary_pred \<^const_name>\<open>ord_class.less\<close> \<^sort>\<open>linorder\<close> t1 t2
fun mk_less_eq t1 t2 = mk_binary_pred \<^const_name>\<open>ord_class.less_eq\<close> \<^sort>\<open>linorder\<close> t1 t2

fun core_term_parser (SMTLIB.Sym "true", _) = SOME \<^Const>\<open>True\<close>
  | core_term_parser (SMTLIB.Sym "false", _) = SOME \<^Const>\<open>False\<close>
  | core_term_parser (SMTLIB.Sym "not", [t]) = SOME (HOLogic.mk_not t)
  | core_term_parser (SMTLIB.Sym "and", t :: ts) = SOME (mk_rassoc (curry HOLogic.mk_conj) t ts)
  | core_term_parser (SMTLIB.Sym "or", t :: ts) = SOME (mk_rassoc (curry HOLogic.mk_disj) t ts)
  | core_term_parser (SMTLIB.Sym "=>", [t1, t2]) = SOME (HOLogic.mk_imp (t1, t2))
  | core_term_parser (SMTLIB.Sym "implies", [t1, t2]) = SOME (HOLogic.mk_imp (t1, t2))
  | core_term_parser (SMTLIB.Sym "=", [t1, t2]) = SOME (HOLogic.mk_eq (t1, t2))
  | core_term_parser (SMTLIB.Sym "~", [t1, t2]) = SOME (HOLogic.mk_eq (t1, t2))
  | core_term_parser (SMTLIB.Sym "ite", [t1, t2, t3]) =
      let
        val T = fastype_of t2
        val c = Const (\<^const_name>\<open>HOL.If\<close>, [\<^typ>\<open>HOL.bool\<close>, T, T] ---> T)
      in SOME (c $ t1 $ t2 $ t3) end
  | core_term_parser (SMTLIB.Num i, []) = SOME (HOLogic.mk_number \<^typ>\<open>Int.int\<close> i)
  | core_term_parser (SMTLIB.Sym "-", [t]) = SOME (mk_unary \<^const_name>\<open>uminus_class.uminus\<close> t)
  | core_term_parser (SMTLIB.Sym "~", [t]) = SOME (mk_unary \<^const_name>\<open>uminus_class.uminus\<close> t)
  | core_term_parser (SMTLIB.Sym "+", t :: ts) =
      SOME (mk_lassoc' \<^const_name>\<open>plus_class.plus\<close> t ts)
  | core_term_parser (SMTLIB.Sym "-", t :: ts) =
      SOME (mk_lassoc' \<^const_name>\<open>minus_class.minus\<close> t ts)
  | core_term_parser (SMTLIB.Sym "*", t :: ts) =
      SOME (mk_lassoc' \<^const_name>\<open>times_class.times\<close> t ts)
  | core_term_parser (SMTLIB.Sym "div", [t1, t2]) = SOME (mk_binary \<^const_name>\<open>z3div\<close> t1 t2)
  | core_term_parser (SMTLIB.Sym "mod", [t1, t2]) = SOME (mk_binary \<^const_name>\<open>z3mod\<close> t1 t2)
  | core_term_parser (SMTLIB.Sym "<", [t1, t2]) = SOME (mk_less t1 t2)
  | core_term_parser (SMTLIB.Sym ">", [t1, t2]) = SOME (mk_less t2 t1)
  | core_term_parser (SMTLIB.Sym "<=", [t1, t2]) = SOME (mk_less_eq t1 t2)
  | core_term_parser (SMTLIB.Sym ">=", [t1, t2]) = SOME (mk_less_eq t2 t1)
  | core_term_parser _ = NONE


(* custom type and term parsers *)

type type_parser = SMTLIB.tree * typ list -> typ option

type term_parser = SMTLIB.tree * term list -> term option

fun id_ord ((id1, _), (id2, _)) = int_ord (id1, id2)

structure Parsers = Generic_Data
(
  type T = (int * type_parser) list * (int * term_parser) list
  val empty : T = ([(serial (), core_type_parser)], [(serial (), core_term_parser)])
  val extend = I
  fun merge ((tys1, ts1), (tys2, ts2)) =
    (Ord_List.merge id_ord (tys1, tys2), Ord_List.merge id_ord (ts1, ts2))
)

fun add_type_parser type_parser =
  Parsers.map (apfst (Ord_List.insert id_ord (serial (), type_parser)))

fun add_term_parser term_parser =
  Parsers.map (apsnd (Ord_List.insert id_ord (serial (), term_parser)))

fun get_type_parsers ctxt = map snd (fst (Parsers.get (Context.Proof ctxt)))
fun get_term_parsers ctxt = map snd (snd (Parsers.get (Context.Proof ctxt)))

fun apply_parsers parsers x =
  let
    fun apply [] = NONE
      | apply (parser :: parsers) =
          (case parser x of
            SOME y => SOME y
          | NONE => apply parsers)
  in apply parsers end


(* type and term parsing *)

exception SMTLIB_PARSE of string * SMTLIB.tree

val desymbolize = Name.desymbolize (SOME false) o perhaps (try (unprefix "?"))

fun fresh_fun add name n T ({ctxt, id, syms, typs, funs, extra}: ('a, 'b) context) =
  let
    val (n', ctxt') = yield_singleton Variable.variant_fixes n ctxt
    val t = Free (n', T)
    val funs' = Symtab.update (name, t) funs
  in (t, mk_context ctxt' id syms typs funs' (add (n', T) extra)) end

fun declare_fun name = snd oo fresh_fun cons name (desymbolize name)
fun declare_free name = fresh_fun (cons o pair name) name (desymbolize name)

fun parse_type cx ty Ts =
  (case apply_parsers (get_type_parsers (ctxt_of cx)) (ty, Ts) of
    SOME T => T
  | NONE =>
      (case ty of
        SMTLIB.Sym name =>
          (case lookup_typ cx name of
            SOME T => T
          | NONE => raise SMTLIB_PARSE ("unknown SMT type", ty))
      | _ => raise SMTLIB_PARSE ("bad SMT type format", ty)))

fun parse_term t ts cx =
  (case apply_parsers (get_term_parsers (ctxt_of cx)) (t, ts) of
    SOME u => (u, cx)
  | NONE =>
      (case t of
        SMTLIB.Sym name =>
          (case lookup_fun cx name of
            SOME u => (Term.list_comb (u, ts), cx)
          | NONE =>
              if null ts then declare_free name Term.dummyT cx
              else raise SMTLIB_PARSE ("bad SMT term", t))
      | _ => raise SMTLIB_PARSE ("bad SMT term format", t)))

fun type_of cx ty =
  (case try (parse_type cx ty) [] of
    SOME T => T
  | NONE =>
      (case ty of
        SMTLIB.S (ty' :: tys) => parse_type cx ty' (map (type_of cx) tys)
      | _ => raise SMTLIB_PARSE ("bad SMT type", ty)))

fun dest_var cx (SMTLIB.S [SMTLIB.Sym name, ty]) = (name, (desymbolize name, type_of cx ty))
  | dest_var _ v = raise SMTLIB_PARSE ("bad SMT quantifier variable format", v)

fun dest_body (SMTLIB.S (SMTLIB.Sym "!" :: body :: _)) = dest_body body
  | dest_body body = body

fun dest_binding (SMTLIB.S [SMTLIB.Sym name, t]) = (name, Tree t)
  | dest_binding b = raise SMTLIB_PARSE ("bad SMT let binding format", b)

fun mk_choice (x, T, P) = HOLogic.choice_const T $ absfree (x, T) P

fun term_of t cx =
  (case t of
    SMTLIB.S [SMTLIB.Sym "forall", SMTLIB.S vars, body] => quant HOLogic.mk_all vars body cx
  | SMTLIB.S [SMTLIB.Sym "exists", SMTLIB.S vars, body] => quant HOLogic.mk_exists vars body cx
  | SMTLIB.S [SMTLIB.Sym "choice", SMTLIB.S vars, body] => quant mk_choice vars body cx
  | SMTLIB.S [SMTLIB.Sym "let", SMTLIB.S bindings, body] =>
      with_bindings (map dest_binding bindings) (term_of body) cx
  | SMTLIB.S (SMTLIB.Sym "!" :: t :: _) => term_of t cx
  | SMTLIB.S (f :: args) =>
      cx
      |> fold_map term_of args
      |-> parse_term f
  | SMTLIB.Sym name =>
      (case lookup_binding cx name of
        Tree u =>
          cx
          |> term_of u
          |-> (fn u' => pair u' o update_binding (name, Term u'))
      | Term u => (u, cx)
      | None => parse_term t [] cx
      | _ => raise SMTLIB_PARSE ("bad SMT term format", t))
  | _ => parse_term t [] cx)

and quant q vars body cx =
  let val vs = map (dest_var cx) vars
  in
    cx
    |> with_bindings (map (apsnd (Term o Free)) vs) (term_of (dest_body body))
    |>> fold_rev (fn (_, (n, T)) => fn t => q (n, T, t)) vs
  end


(* Sharing of terms via "! _ :named name"*)

type name_bindings = SMTLIB.tree Symtab.table * SMTLIB.tree Symtab.table

val empty_name_binding = (Symtab.empty, Symtab.empty)

fun update_name_binding (name, t) (tab, exp_tab) =
  (tab, Symtab.update (name, t) exp_tab)

fun remove_name_bindings (SMTLIB.S (SMTLIB.Sym "!" :: body :: _)) =
      remove_name_bindings body
  | remove_name_bindings (SMTLIB.S body) =
     SMTLIB.S (map remove_name_bindings body)
  | remove_name_bindings t = t

fun extract_name_bindings t (tab, exp_tab) =
  let
    fun extract t (tab, new) =
      (case t of
        SMTLIB.S [SMTLIB.Sym "forall", SMTLIB.S _, body] => extract body (tab, new)
      | SMTLIB.S [SMTLIB.Sym "exists", SMTLIB.S _, body] => extract body (tab, new)
      | SMTLIB.S [SMTLIB.Sym "choice", SMTLIB.S _, body] => extract body (tab, new)
      | SMTLIB.S [SMTLIB.Sym "let", SMTLIB.S bindings, body] =>
          raise (Fail "unsupported let construction in name extraction")
      | SMTLIB.S (SMTLIB.Sym "!" :: t :: [SMTLIB.Key _, SMTLIB.Sym name]) =>
          extract t (tab, new)
          |>> Symtab.update (name, remove_name_bindings t)
          ||> curry (op :: ) name
      | SMTLIB.S args =>
          fold extract args (tab, new)
      | _ => ((tab, new)))
    val (tab, new) = extract t (tab, [])
  in ((tab, exp_tab), new) end

fun expand_name_bindings t (tab, exp_tab) =
  let
    fun expand_update (SMTLIB.Sym sym) exp_tab =
        (case Symtab.lookup exp_tab sym of
          SOME t => (t, exp_tab)
        | NONE =>
           (case (Symtab.lookup tab sym) of
             NONE => (SMTLIB.Sym sym, exp_tab)
           | SOME u =>
              let val (u2, exp_tab) = expand_update u exp_tab
              in (u2, Symtab.update (sym, u2) exp_tab) end
           )
        )
      | expand_update (t as SMTLIB.Key _) exp_tab = (t, exp_tab)
      | expand_update (t as SMTLIB.Num _) exp_tab = (t, exp_tab)
      | expand_update (t as SMTLIB.Dec _) exp_tab = (t, exp_tab)
      | expand_update (t as SMTLIB.Str _) exp_tab = (t, exp_tab)
      | expand_update (SMTLIB.S s) (exp_tab : SMTLIB.tree Symtab.table) =
         fold_map expand_update s exp_tab
         |>> (fn s => SMTLIB.S s)
  in
    expand_update t exp_tab
    |> (fn (t, exp_tab) => (remove_name_bindings t, (tab, exp_tab)))
  end

fun extract_and_update_name_bindings t tab =
  extract_name_bindings t tab
  |>> expand_name_bindings (remove_name_bindings t)

end;
