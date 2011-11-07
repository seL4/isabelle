(*  Title:      Pure/Syntax/syntax_trans.ML
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Syntax translation functions.
*)

signature BASIC_SYNTAX_TRANS =
sig
  val eta_contract: bool Config.T
end

signature SYNTAX_TRANS =
sig
  include BASIC_SYNTAX_TRANS
  val bracketsN: string
  val no_bracketsN: string
  val no_brackets: unit -> bool
  val type_bracketsN: string
  val no_type_bracketsN: string
  val no_type_brackets: unit -> bool
  val abs_tr: term list -> term
  val mk_binder_tr: string * string -> string * (term list -> term)
  val antiquote_tr: string -> term -> term
  val quote_tr: string -> term -> term
  val quote_antiquote_tr: string -> string -> string -> string * (term list -> term)
  val non_typed_tr': (term list -> term) -> typ -> term list -> term
  val non_typed_tr'': ('a -> term list -> term) -> 'a -> typ -> term list -> term
  val tappl_ast_tr': Ast.ast * Ast.ast list -> Ast.ast
  val appl_ast_tr': Ast.ast * Ast.ast list -> Ast.ast
  val applC_ast_tr': Ast.ast * Ast.ast list -> Ast.ast
  val eta_contract_default: bool Unsynchronized.ref
  val eta_contract_raw: Config.raw
  val mark_bound: string -> term
  val mark_boundT: string * typ -> term
  val bound_vars: (string * typ) list -> term -> term
  val abs_tr': Proof.context -> term -> term
  val atomic_abs_tr': string * typ * term -> term * term
  val const_abs_tr': term -> term
  val mk_binder_tr': string * string -> string * (term list -> term)
  val preserve_binder_abs_tr': string -> string -> string * (term list -> term)
  val preserve_binder_abs2_tr': string -> string -> string * (term list -> term)
  val prop_tr': term -> term
  val variant_abs: string * typ * term -> string * term
  val variant_abs': string * typ * term -> string * term
  val dependent_tr': string * string -> term list -> term
  val antiquote_tr': string -> term -> term
  val quote_tr': string -> term -> term
  val quote_antiquote_tr': string -> string -> string -> string * (term list -> term)
  val update_name_tr': term -> term
  val pure_trfuns:
    (string * (Ast.ast list -> Ast.ast)) list *
    (string * (term list -> term)) list *
    (string * (term list -> term)) list *
    (string * (Ast.ast list -> Ast.ast)) list
  val struct_trfuns: string list ->
    (string * (Ast.ast list -> Ast.ast)) list *
    (string * (term list -> term)) list *
    (string * (typ -> term list -> term)) list *
    (string * (Ast.ast list -> Ast.ast)) list
end;

structure Syntax_Trans: SYNTAX_TRANS =
struct

structure Syntax = Lexicon.Syntax;


(* print mode *)

val bracketsN = "brackets";
val no_bracketsN = "no_brackets";

fun no_brackets () =
  find_first (fn mode => mode = bracketsN orelse mode = no_bracketsN)
    (print_mode_value ()) = SOME no_bracketsN;

val type_bracketsN = "type_brackets";
val no_type_bracketsN = "no_type_brackets";

fun no_type_brackets () =
  find_first (fn mode => mode = type_bracketsN orelse mode = no_type_bracketsN)
    (print_mode_value ()) <> SOME type_bracketsN;



(** parse (ast) translations **)

(* strip_positions *)

fun strip_positions_ast_tr [ast] = Ast.strip_positions ast
  | strip_positions_ast_tr asts = raise Ast.AST ("strip_positions_ast_tr", asts);


(* constify *)

fun constify_ast_tr [Ast.Variable c] = Ast.Constant c
  | constify_ast_tr asts = raise Ast.AST ("constify_ast_tr", asts);


(* type syntax *)

fun tapp_ast_tr [ty, c] = Ast.Appl [c, ty]
  | tapp_ast_tr asts = raise Ast.AST ("tapp_ast_tr", asts);

fun tappl_ast_tr [ty, tys, c] = Ast.mk_appl c (ty :: Ast.unfold_ast "_types" tys)
  | tappl_ast_tr asts = raise Ast.AST ("tappl_ast_tr", asts);

fun bracket_ast_tr [dom, cod] = Ast.fold_ast_p "\\<^type>fun" (Ast.unfold_ast "_types" dom, cod)
  | bracket_ast_tr asts = raise Ast.AST ("bracket_ast_tr", asts);


(* application *)

fun appl_ast_tr [f, args] = Ast.Appl (f :: Ast.unfold_ast "_args" args)
  | appl_ast_tr asts = raise Ast.AST ("appl_ast_tr", asts);

fun applC_ast_tr [f, args] = Ast.Appl (f :: Ast.unfold_ast "_cargs" args)
  | applC_ast_tr asts = raise Ast.AST ("applC_ast_tr", asts);


(* abstraction *)

fun idtyp_ast_tr [x, ty] = Ast.Appl [Ast.Constant "_constrain", x, ty]
  | idtyp_ast_tr asts = raise Ast.AST ("idtyp_ast_tr", asts);

fun idtypdummy_ast_tr [ty] = Ast.Appl [Ast.Constant "_constrain", Ast.Constant "_idtdummy", ty]
  | idtypdummy_ast_tr asts = raise Ast.AST ("idtyp_ast_tr", asts);

fun lambda_ast_tr [pats, body] = Ast.fold_ast_p "_abs" (Ast.unfold_ast "_pttrns" pats, body)
  | lambda_ast_tr asts = raise Ast.AST ("lambda_ast_tr", asts);

fun absfree_proper (x, T) t =
  if can Name.dest_internal x
  then error ("Illegal internal variable in abstraction: " ^ quote x)
  else absfree (x, T) t;

fun abs_tr [Free x, t] = absfree_proper x t
  | abs_tr [Const ("_idtdummy", T), t] = absdummy T t
  | abs_tr [Const ("_constrain", _) $ x $ tT, t] =
      Syntax.const "_constrainAbs" $ abs_tr [x, t] $ tT
  | abs_tr ts = raise TERM ("abs_tr", ts);


(* binder *)

fun mk_binder_tr (syn, name) =
  let
    fun err ts = raise TERM ("binder_tr: " ^ syn, ts)
    fun binder_tr [Const ("_idts", _) $ idt $ idts, t] = binder_tr [idt, binder_tr [idts, t]]
      | binder_tr [x, t] =
          let val abs = abs_tr [x, t] handle TERM _ => err [x, t]
          in Syntax.const name $ abs end
      | binder_tr ts = err ts;
  in (syn, binder_tr) end;


(* type propositions *)

fun mk_type ty =
  Syntax.const "_constrain" $
    Syntax.const "\\<^const>TYPE" $ (Syntax.const "\\<^type>itself" $ ty);

fun ofclass_tr [ty, cls] = cls $ mk_type ty
  | ofclass_tr ts = raise TERM ("ofclass_tr", ts);

fun sort_constraint_tr [ty] = Syntax.const "\\<^const>Pure.sort_constraint" $ mk_type ty
  | sort_constraint_tr ts = raise TERM ("sort_constraint_tr", ts);


(* meta propositions *)

fun aprop_tr [t] = Syntax.const "_constrain" $ t $ Syntax.const "\\<^type>prop"
  | aprop_tr ts = raise TERM ("aprop_tr", ts);


(* meta implication *)

fun bigimpl_ast_tr (asts as [asms, concl]) =
      let val prems =
        (case Ast.unfold_ast_p "_asms" asms of
          (asms', Ast.Appl [Ast.Constant "_asm", asm']) => asms' @ [asm']
        | _ => raise Ast.AST ("bigimpl_ast_tr", asts))
      in Ast.fold_ast_p "\\<^const>==>" (prems, concl) end
  | bigimpl_ast_tr asts = raise Ast.AST ("bigimpl_ast_tr", asts);


(* type/term reflection *)

fun type_tr [ty] = mk_type ty
  | type_tr ts = raise TERM ("type_tr", ts);


(* dddot *)

fun dddot_tr ts = Term.list_comb (Syntax.var Syntax_Ext.dddot_indexname, ts);


(* quote / antiquote *)

fun antiquote_tr name =
  let
    fun tr i ((t as Const (c, _)) $ u) =
          if c = name then tr i u $ Bound i
          else tr i t $ tr i u
      | tr i (t $ u) = tr i t $ tr i u
      | tr i (Abs (x, T, t)) = Abs (x, T, tr (i + 1) t)
      | tr _ a = a;
  in tr 0 end;

fun quote_tr name t = Abs ("s", dummyT, antiquote_tr name (Term.incr_boundvars 1 t));

fun quote_antiquote_tr quoteN antiquoteN name =
  let
    fun tr [t] = Syntax.const name $ quote_tr antiquoteN t
      | tr ts = raise TERM ("quote_tr", ts);
  in (quoteN, tr) end;


(* corresponding updates *)

fun update_name_tr (Free (x, T) :: ts) = list_comb (Free (suffix "_update" x, T), ts)
  | update_name_tr (Const (x, T) :: ts) = list_comb (Const (suffix "_update" x, T), ts)
  | update_name_tr (((c as Const ("_constrain", _)) $ t $ ty) :: ts) =
      if Term_Position.is_position ty then list_comb (c $ update_name_tr [t] $ ty, ts)
      else
        list_comb (c $ update_name_tr [t] $
          (Lexicon.fun_type $
            (Lexicon.fun_type $ Lexicon.dummy_type $ ty) $ Lexicon.dummy_type), ts)
  | update_name_tr ts = raise TERM ("update_name_tr", ts);


(* indexed syntax *)

fun indexdefault_ast_tr [] =
      Ast.Appl [Ast.Constant "_index",
        Ast.Appl [Ast.Constant "_struct", Ast.Constant "_indexdefault"]]
  | indexdefault_ast_tr asts = raise Ast.AST ("indexdefault_ast_tr", asts);

fun indexvar_ast_tr [] = Ast.Appl [Ast.Constant "_index", Ast.Variable "some_index"]
  | indexvar_ast_tr asts = raise Ast.AST ("indexvar_ast_tr", asts);

fun struct_ast_tr [Ast.Appl [Ast.Constant "_index", ast]] = ast
  | struct_ast_tr asts = Ast.mk_appl (Ast.Constant "_struct") asts;

fun index_tr [t] = t
  | index_tr ts = raise TERM ("index_tr", ts);

fun the_struct [] = error "Illegal reference to implicit structure"
  | the_struct (x :: _) = x;

fun struct_tr structs [Const ("_indexdefault", _)] = Syntax.free (the_struct structs)
  | struct_tr _ ts = raise TERM ("struct_tr", ts);



(** print (ast) translations **)

(* types *)

fun non_typed_tr' f _ ts = f ts;
fun non_typed_tr'' f x _ ts = f x ts;


(* type syntax *)

fun tappl_ast_tr' (f, []) = raise Ast.AST ("tappl_ast_tr'", [f])
  | tappl_ast_tr' (f, [ty]) = Ast.Appl [Ast.Constant "_tapp", ty, f]
  | tappl_ast_tr' (f, ty :: tys) =
      Ast.Appl [Ast.Constant "_tappl", ty, Ast.fold_ast "_types" tys, f];

fun fun_ast_tr' asts =
  if no_brackets () orelse no_type_brackets () then raise Match
  else
    (case Ast.unfold_ast_p "\\<^type>fun" (Ast.Appl (Ast.Constant "\\<^type>fun" :: asts)) of
      (dom as _ :: _ :: _, cod)
        => Ast.Appl [Ast.Constant "_bracket", Ast.fold_ast "_types" dom, cod]
    | _ => raise Match);


(* application *)

fun appl_ast_tr' (f, []) = raise Ast.AST ("appl_ast_tr'", [f])
  | appl_ast_tr' (f, args) = Ast.Appl [Ast.Constant "_appl", f, Ast.fold_ast "_args" args];

fun applC_ast_tr' (f, []) = raise Ast.AST ("applC_ast_tr'", [f])
  | applC_ast_tr' (f, args) = Ast.Appl [Ast.Constant "_applC", f, Ast.fold_ast "_cargs" args];


(* partial eta-contraction before printing *)

fun eta_abs (Abs (a, T, t)) =
      (case eta_abs t of
        t' as Const ("_aprop", _) $ _ => Abs (a, T, t')
      | t' as f $ u =>
          (case eta_abs u of
            Bound 0 =>
              if Term.is_dependent f then Abs (a, T, t')
              else incr_boundvars ~1 f
          | _ => Abs (a, T, t'))
      | t' => Abs (a, T, t'))
  | eta_abs t = t;

val eta_contract_default = Unsynchronized.ref true;
val eta_contract_raw = Config.declare "eta_contract" (fn _ => Config.Bool (! eta_contract_default));
val eta_contract = Config.bool eta_contract_raw;

fun eta_contr ctxt tm =
  if Config.get ctxt eta_contract then eta_abs tm else tm;


(* abstraction *)

fun mark_boundT (x, T) = Const ("_bound", T --> T) $ Free (x, T);
fun mark_bound x = mark_boundT (x, dummyT);

fun bound_vars vars body =
  subst_bounds (map mark_boundT (Term.rename_wrt_term body vars), body);

fun strip_abss vars_of body_of tm =
  let
    val vars = vars_of tm;
    val body = body_of tm;
    val rev_new_vars = Term.rename_wrt_term body vars;
    fun subst (x, T) b =
      if can Name.dest_internal x andalso not (Term.is_dependent b)
      then (Const ("_idtdummy", T), incr_boundvars ~1 b)
      else (mark_boundT (x, T), Term.subst_bound (mark_bound x, b));
    val (rev_vars', body') = fold_map subst rev_new_vars body;
  in (rev rev_vars', body') end;


fun abs_tr' ctxt tm =
  uncurry (fold_rev (fn x => fn t => Syntax.const "_abs" $ x $ t))
    (strip_abss strip_abs_vars strip_abs_body (eta_contr ctxt tm));

fun atomic_abs_tr' (x, T, t) =
  let val [xT] = Term.rename_wrt_term t [(x, T)]
  in (mark_boundT xT, subst_bound (mark_bound (fst xT), t)) end;

fun abs_ast_tr' asts =
  (case Ast.unfold_ast_p "_abs" (Ast.Appl (Ast.Constant "_abs" :: asts)) of
    ([], _) => raise Ast.AST ("abs_ast_tr'", asts)
  | (xs, body) => Ast.Appl [Ast.Constant "_lambda", Ast.fold_ast "_pttrns" xs, body]);

fun const_abs_tr' t =
  (case eta_abs t of
    Abs (_, _, t') =>
      if Term.is_dependent t' then raise Match
      else incr_boundvars ~1 t'
  | _ => raise Match);


(* binders *)

fun mk_binder_tr' (name, syn) =
  let
    fun mk_idts [] = raise Match    (*abort translation*)
      | mk_idts [idt] = idt
      | mk_idts (idt :: idts) = Syntax.const "_idts" $ idt $ mk_idts idts;

    fun tr' t =
      let
        val (xs, bd) = strip_abss (strip_qnt_vars name) (strip_qnt_body name) t;
      in Syntax.const syn $ mk_idts xs $ bd end;

    fun binder_tr' (t :: ts) = Term.list_comb (tr' (Syntax.const name $ t), ts)
      | binder_tr' [] = raise Match;
  in (name, binder_tr') end;

fun preserve_binder_abs_tr' name syn = (name, fn Abs abs :: ts =>
  let val (x, t) = atomic_abs_tr' abs
  in list_comb (Syntax.const syn $ x $ t, ts) end);

fun preserve_binder_abs2_tr' name syn = (name, fn A :: Abs abs :: ts =>
  let val (x, t) = atomic_abs_tr' abs
  in list_comb (Syntax.const syn $ x $ A $ t, ts) end);


(* idtyp constraints *)

fun idtyp_ast_tr' a [Ast.Appl [Ast.Constant "_constrain", x, ty], xs] =
      Ast.Appl [Ast.Constant a, Ast.Appl [Ast.Constant "_idtyp", x, ty], xs]
  | idtyp_ast_tr' _ _ = raise Match;


(* meta propositions *)

fun prop_tr' tm =
  let
    fun aprop t = Syntax.const "_aprop" $ t;

    fun is_prop Ts t =
      fastype_of1 (Ts, t) = propT handle TERM _ => false;

    fun is_term (Const ("Pure.term", _) $ _) = true
      | is_term _ = false;

    fun tr' _ (t as Const _) = t
      | tr' Ts (t as Const ("_bound", _) $ u) =
          if is_prop Ts u then aprop t else t
      | tr' _ (t as Free (x, T)) =
          if T = propT then aprop (Syntax.free x) else t
      | tr' _ (t as Var (xi, T)) =
          if T = propT then aprop (Syntax.var xi) else t
      | tr' Ts (t as Bound _) =
          if is_prop Ts t then aprop t else t
      | tr' Ts (Abs (x, T, t)) = Abs (x, T, tr' (T :: Ts) t)
      | tr' Ts (t as t1 $ (t2 as Const ("TYPE", Type ("itself", [T])))) =
          if is_prop Ts t andalso not (is_term t) then Const ("_type_prop", T) $ tr' Ts t1
          else tr' Ts t1 $ tr' Ts t2
      | tr' Ts (t as t1 $ t2) =
          (if is_Const (Term.head_of t) orelse not (is_prop Ts t)
            then I else aprop) (tr' Ts t1 $ tr' Ts t2);
  in tr' [] tm end;


(* meta implication *)

fun impl_ast_tr' asts =
  if no_brackets () then raise Match
  else
    (case Ast.unfold_ast_p "\\<^const>==>" (Ast.Appl (Ast.Constant "\\<^const>==>" :: asts)) of
      (prems as _ :: _ :: _, concl) =>
        let
          val (asms, asm) = split_last prems;
          val asms' = Ast.fold_ast_p "_asms" (asms, Ast.Appl [Ast.Constant "_asm", asm]);
        in Ast.Appl [Ast.Constant "_bigimpl", asms', concl] end
    | _ => raise Match);


(* dependent / nondependent quantifiers *)

fun var_abs mark (x, T, b) =
  let val (x', _) = Name.variant x (Term.declare_term_names b Name.context)
  in (x', subst_bound (mark (x', T), b)) end;

val variant_abs = var_abs Free;
val variant_abs' = var_abs mark_boundT;

fun dependent_tr' (q, r) (A :: Abs (x, T, B) :: ts) =
      if Term.is_dependent B then
        let val (x', B') = variant_abs' (x, dummyT, B);
        in Term.list_comb (Syntax.const q $ mark_boundT (x', T) $ A $ B', ts) end
      else Term.list_comb (Syntax.const r $ A $ incr_boundvars ~1 B, ts)
  | dependent_tr' _ _ = raise Match;


(* quote / antiquote *)

fun antiquote_tr' name =
  let
    fun tr' i (t $ u) =
          if u aconv Bound i then Syntax.const name $ tr' i t
          else tr' i t $ tr' i u
      | tr' i (Abs (x, T, t)) = Abs (x, T, tr' (i + 1) t)
      | tr' i a = if a aconv Bound i then raise Match else a;
  in tr' 0 end;

fun quote_tr' name (Abs (_, _, t)) = Term.incr_boundvars ~1 (antiquote_tr' name t)
  | quote_tr' _ _ = raise Match;

fun quote_antiquote_tr' quoteN antiquoteN name =
  let
    fun tr' (t :: ts) = Term.list_comb (Syntax.const quoteN $ quote_tr' antiquoteN t, ts)
      | tr' _ = raise Match;
  in (name, tr') end;


(* corresponding updates *)

local

fun upd_type (Type ("fun", [Type ("fun", [_, T]), _])) = T
  | upd_type _ = dummyT;

fun upd_tr' (x_upd, T) =
  (case try (unsuffix "_update") x_upd of
    SOME x => (x, upd_type T)
  | NONE => raise Match);

in

fun update_name_tr' (Free x) = Free (upd_tr' x)
  | update_name_tr' ((c as Const ("_free", _)) $ Free x) = c $ Free (upd_tr' x)
  | update_name_tr' (Const x) = Const (upd_tr' x)
  | update_name_tr' _ = raise Match;

end;


(* indexed syntax *)

fun index_ast_tr' [Ast.Appl [Ast.Constant "_struct", ast]] = ast
  | index_ast_tr' _ = raise Match;

fun struct_ast_tr' structs [Ast.Constant "_indexdefault"] =
      Ast.Appl [Ast.Constant "_free",
        Ast.Variable (the_struct structs handle ERROR _ => raise Match)]
  | struct_ast_tr' _ _ = raise Match;



(** Pure translations **)

val pure_trfuns =
  ([("_strip_positions", strip_positions_ast_tr),
    ("_constify", constify_ast_tr),
    ("_tapp", tapp_ast_tr),
    ("_tappl", tappl_ast_tr),
    ("_bracket", bracket_ast_tr),
    ("_appl", appl_ast_tr),
    ("_applC", applC_ast_tr),
    ("_lambda", lambda_ast_tr),
    ("_idtyp", idtyp_ast_tr),
    ("_idtypdummy", idtypdummy_ast_tr),
    ("_bigimpl", bigimpl_ast_tr),
    ("_indexdefault", indexdefault_ast_tr),
    ("_indexvar", indexvar_ast_tr),
    ("_struct", struct_ast_tr)],
   [("_abs", abs_tr),
    ("_aprop", aprop_tr),
    ("_ofclass", ofclass_tr),
    ("_sort_constraint", sort_constraint_tr),
    ("_TYPE", type_tr),
    ("_DDDOT", dddot_tr),
    ("_update_name", update_name_tr),
    ("_index", index_tr)],
   ([]: (string * (term list -> term)) list),
   [("\\<^type>fun", fun_ast_tr'),
    ("_abs", abs_ast_tr'),
    ("_idts", idtyp_ast_tr' "_idts"),
    ("_pttrns", idtyp_ast_tr' "_pttrns"),
    ("\\<^const>==>", impl_ast_tr'),
    ("_index", index_ast_tr')]);

fun struct_trfuns structs =
  ([], [("_struct", struct_tr structs)], [], [("_struct", struct_ast_tr' structs)]);

end;

structure Basic_Syntax_Trans: BASIC_SYNTAX_TRANS = Syntax_Trans;
open Basic_Syntax_Trans;
