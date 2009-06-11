(*  Title:      Pure/Syntax/syn_trans.ML
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Syntax translation functions.
*)

signature SYN_TRANS0 =
sig
  val eta_contract: bool ref
  val atomic_abs_tr': string * typ * term -> term * term
  val mk_binder_tr: string * string -> string * (term list -> term)
  val mk_binder_tr': string * string -> string * (term list -> term)
  val dependent_tr': string * string -> term list -> term
  val antiquote_tr: string -> term -> term
  val quote_tr: string -> term -> term
  val quote_antiquote_tr: string -> string -> string -> string * (term list -> term)
  val antiquote_tr': string -> term -> term
  val quote_tr': string -> term -> term
  val quote_antiquote_tr': string -> string -> string -> string * (term list -> term)
  val mark_bound: string -> term
  val mark_boundT: string * typ -> term
  val bound_vars: (string * typ) list -> term -> term
  val variant_abs: string * typ * term -> string * term
  val variant_abs': string * typ * term -> string * term
end;

signature SYN_TRANS1 =
sig
  include SYN_TRANS0
  val non_typed_tr': (term list -> term) -> bool -> typ -> term list -> term
  val non_typed_tr'': ('a -> term list -> term) -> 'a -> bool -> typ -> term list -> term
  val constrainAbsC: string
  val pure_trfuns:
      (string * (Ast.ast list -> Ast.ast)) list *
      (string * (term list -> term)) list *
      (string * (term list -> term)) list *
      (string * (Ast.ast list -> Ast.ast)) list
  val pure_trfunsT: (string * (bool -> typ -> term list -> term)) list
  val struct_trfuns: string list ->
      (string * (Ast.ast list -> Ast.ast)) list *
      (string * (term list -> term)) list *
      (string * (bool -> typ -> term list -> term)) list *
      (string * (Ast.ast list -> Ast.ast)) list
end;

signature SYN_TRANS =
sig
  include SYN_TRANS1
  val abs_tr': term -> term
  val prop_tr': term -> term
  val appl_ast_tr': Ast.ast * Ast.ast list -> Ast.ast
  val applC_ast_tr': Ast.ast * Ast.ast list -> Ast.ast
  val pts_to_asts: Proof.context ->
    (string -> (Proof.context -> Ast.ast list -> Ast.ast) option) ->
    Parser.parsetree list -> Ast.ast list
  val asts_to_terms: Proof.context ->
    (string -> (Proof.context -> term list -> term) option) -> Ast.ast list -> term list
end;

structure SynTrans: SYN_TRANS =
struct


(** parse (ast) translations **)

(* constify *)

fun constify_ast_tr [Ast.Variable c] = Ast.Constant c
  | constify_ast_tr asts = raise Ast.AST ("constify_ast_tr", asts);


(* application *)

fun appl_ast_tr [f, args] = Ast.Appl (f :: Ast.unfold_ast "_args" args)
  | appl_ast_tr asts = raise Ast.AST ("appl_ast_tr", asts);

fun applC_ast_tr [f, args] = Ast.Appl (f :: Ast.unfold_ast "_cargs" args)
  | applC_ast_tr asts = raise Ast.AST ("applC_ast_tr", asts);


(* abstraction *)

fun idtyp_ast_tr (*"_idtyp"*) [x, ty] = Ast.Appl [Ast.Constant "_constrain", x, ty]
  | idtyp_ast_tr (*"_idtyp"*) asts = raise Ast.AST ("idtyp_ast_tr", asts);

fun idtypdummy_ast_tr (*"_idtypdummy"*) [ty] =
      Ast.Appl [Ast.Constant "_constrain", Ast.Constant "_idtdummy", ty]
  | idtypdummy_ast_tr (*"_idtypdummy"*) asts = raise Ast.AST ("idtyp_ast_tr", asts);

fun lambda_ast_tr (*"_lambda"*) [pats, body] =
      Ast.fold_ast_p "_abs" (Ast.unfold_ast "_pttrns" pats, body)
  | lambda_ast_tr (*"_lambda"*) asts = raise Ast.AST ("lambda_ast_tr", asts);

val constrainAbsC = "_constrainAbs";

fun absfree_proper (x, T, t) =
  if can Name.dest_internal x then error ("Illegal internal variable in abstraction: " ^ quote x)
  else Term.absfree (x, T, t);

fun abs_tr (*"_abs"*) [Free (x, T), t] = absfree_proper (x, T, t)
  | abs_tr (*"_abs"*) [Const ("_idtdummy", T), t] = Term.absdummy (T, t)
  | abs_tr (*"_abs"*) [Const ("_constrain", _) $ Free (x, T) $ tT, t] =
      Lexicon.const constrainAbsC $ absfree_proper (x, T, t) $ tT
  | abs_tr (*"_abs"*) [Const ("_constrain", _) $ Const ("_idtdummy", T) $ tT, t] =
      Lexicon.const constrainAbsC $ Term.absdummy (T, t) $ tT
  | abs_tr (*"_abs"*) ts = raise TERM ("abs_tr", ts);


(* binder *)

fun mk_binder_tr (syn, name) =
  let
    fun tr (Free (x, T), t) = Lexicon.const name $ absfree_proper (x, T, t)
      | tr (Const ("_idtdummy", T), t) = Lexicon.const name $ Term.absdummy (T, t)
      | tr (Const ("_constrain", _) $ Free (x, T) $ tT, t) =
          Lexicon.const name $ (Lexicon.const constrainAbsC $ absfree_proper (x, T, t) $ tT)
      | tr (Const ("_constrain", _) $ Const ("_idtdummy", T) $ tT, t) =
          Lexicon.const name $ (Lexicon.const constrainAbsC $ Term.absdummy (T, t) $ tT)
      | tr (Const ("_idts", _) $ idt $ idts, t) = tr (idt, tr (idts, t))
      | tr (t1, t2) = raise TERM ("binder_tr", [t1, t2]);

    fun binder_tr [idts, body] = tr (idts, body)
      | binder_tr ts = raise TERM ("binder_tr", ts);
  in (syn, binder_tr) end;


(* type propositions *)

fun mk_type ty = Lexicon.const "_constrain" $ Lexicon.const "TYPE" $ (Lexicon.const "itself" $ ty);

fun ofclass_tr (*"_ofclass"*) [ty, cls] = cls $ mk_type ty
  | ofclass_tr (*"_ofclass"*) ts = raise TERM ("ofclass_tr", ts);

fun sort_constraint_tr (*"_sort_constraint"*) [ty] =
      Lexicon.const "Pure.sort_constraint" $ mk_type ty
  | sort_constraint_tr (*"_sort_constraint"*) ts = raise TERM ("sort_constraint_tr", ts);


(* meta propositions *)

fun aprop_tr (*"_aprop"*) [t] = Lexicon.const "_constrain" $ t $ Lexicon.const "prop"
  | aprop_tr (*"_aprop"*) ts = raise TERM ("aprop_tr", ts);


(* meta implication *)

fun bigimpl_ast_tr (*"_bigimpl"*) (asts as [asms, concl]) =
      let val prems =
        (case Ast.unfold_ast_p "_asms" asms of
          (asms', Ast.Appl [Ast.Constant "_asm", asm']) => asms' @ [asm']
        | _ => raise Ast.AST ("bigimpl_ast_tr", asts))
      in Ast.fold_ast_p "==>" (prems, concl) end
  | bigimpl_ast_tr (*"_bigimpl"*) asts = raise Ast.AST ("bigimpl_ast_tr", asts);


(* meta conjunction *)

fun conjunction_tr [t, u] = Lexicon.const "Pure.conjunction" $ t $ u
  | conjunction_tr ts = raise TERM ("conjunction_tr", ts);


(* type/term reflection *)

fun type_tr (*"_TYPE"*) [ty] = mk_type ty
  | type_tr (*"_TYPE"*) ts = raise TERM ("type_tr", ts);

fun term_tr [t] = Lexicon.const "Pure.term" $ t
  | term_tr ts = raise TERM ("term_tr", ts);


(* dddot *)

fun dddot_tr (*"_DDDOT"*) ts = Term.list_comb (Lexicon.var SynExt.dddot_indexname, ts);


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
    fun tr [t] = Lexicon.const name $ quote_tr antiquoteN t
      | tr ts = raise TERM ("quote_tr", ts);
  in (quoteN, tr) end;


(* indexed syntax *)

fun struct_ast_tr (*"_struct"*) [Ast.Appl [Ast.Constant "_index", ast]] = ast
  | struct_ast_tr (*"_struct"*) asts = Ast.mk_appl (Ast.Constant "_struct") asts;

fun index_ast_tr ast =
  Ast.mk_appl (Ast.Constant "_index") [Ast.mk_appl (Ast.Constant "_struct") [ast]];

fun indexdefault_ast_tr (*"_indexdefault"*) [] =
      index_ast_tr (Ast.Constant "_indexdefault")
  | indexdefault_ast_tr (*"_indexdefault"*) asts =
      raise Ast.AST ("indexdefault_ast_tr", asts);

fun indexnum_ast_tr (*"_indexnum"*) [ast] =
      index_ast_tr (Ast.mk_appl (Ast.Constant "_indexnum") [ast])
  | indexnum_ast_tr (*"_indexnum"*) asts = raise Ast.AST ("indexnum_ast_tr", asts);

fun indexvar_ast_tr (*"_indexvar"*) [] =
      Ast.mk_appl (Ast.Constant "_index") [Ast.Variable "some_index"]
  | indexvar_ast_tr (*"_indexvar"*) asts = raise Ast.AST ("indexvar_ast_tr", asts);

fun index_tr (*"_index"*) [t] = t
  | index_tr (*"_index"*) ts = raise TERM ("index_tr", ts);


(* implicit structures *)

fun the_struct structs i =
  if 1 <= i andalso i <= length structs then nth structs (i - 1)
  else error ("Illegal reference to implicit structure #" ^ string_of_int i);

fun struct_tr structs (*"_struct"*) [Const ("_indexdefault", _)] =
      Lexicon.free (the_struct structs 1)
  | struct_tr structs (*"_struct"*) [t as (Const ("_indexnum", _) $ Const (s, _))] =
      Lexicon.free (the_struct structs
        (case Lexicon.read_nat s of SOME n => n | NONE => raise TERM ("struct_tr", [t])))
  | struct_tr _ (*"_struct"*) ts = raise TERM ("struct_tr", ts);



(** print (ast) translations **)

(* types *)

fun non_typed_tr' f _ _ ts = f ts;
fun non_typed_tr'' f x _ _ ts = f x ts;


(* application *)

fun appl_ast_tr' (f, []) = raise Ast.AST ("appl_ast_tr'", [f])
  | appl_ast_tr' (f, args) = Ast.Appl [Ast.Constant "_appl", f, Ast.fold_ast "_args" args];

fun applC_ast_tr' (f, []) = raise Ast.AST ("applC_ast_tr'", [f])
  | applC_ast_tr' (f, args) = Ast.Appl [Ast.Constant "_applC", f, Ast.fold_ast "_cargs" args];


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
      if can Name.dest_internal x andalso not (Term.loose_bvar1 (b, 0))
      then (Const ("_idtdummy", T), incr_boundvars ~1 b)
      else (mark_boundT (x, T), Term.subst_bound (mark_bound x, b));
    val (rev_vars', body') = fold_map subst rev_new_vars body;
  in (rev rev_vars', body') end;


(*do (partial) eta-contraction before printing*)

val eta_contract = ref true;

fun eta_contr tm =
  let
    fun is_aprop (Const ("_aprop", _)) = true
      | is_aprop _ = false;

    fun eta_abs (Abs (a, T, t)) =
          (case eta_abs t of
            t' as f $ u =>
              (case eta_abs u of
                Bound 0 =>
                  if Term.loose_bvar1 (f, 0) orelse is_aprop f then Abs (a, T, t')
                  else  incr_boundvars ~1 f
              | _ => Abs (a, T, t'))
          | t' => Abs (a, T, t'))
      | eta_abs t = t;
  in
    if ! eta_contract then eta_abs tm else tm
  end;


fun abs_tr' tm =
  uncurry (fold_rev (fn x => fn t => Lexicon.const "_abs" $ x $ t))
    (strip_abss strip_abs_vars strip_abs_body (eta_contr tm));

fun atomic_abs_tr' (x, T, t) =
  let val [xT] = Term.rename_wrt_term t [(x, T)]
  in (mark_boundT xT, subst_bound (mark_bound (fst xT), t)) end;

fun abs_ast_tr' (*"_abs"*) asts =
  (case Ast.unfold_ast_p "_abs" (Ast.Appl (Ast.Constant "_abs" :: asts)) of
    ([], _) => raise Ast.AST ("abs_ast_tr'", asts)
  | (xs, body) => Ast.Appl [Ast.Constant "_lambda", Ast.fold_ast "_pttrns" xs, body]);


(* binder *)

fun mk_binder_tr' (name, syn) =
  let
    fun mk_idts [] = raise Match    (*abort translation*)
      | mk_idts [idt] = idt
      | mk_idts (idt :: idts) = Lexicon.const "_idts" $ idt $ mk_idts idts;

    fun tr' t =
      let
        val (xs, bd) = strip_abss (strip_qnt_vars name) (strip_qnt_body name) t;
      in Lexicon.const syn $ mk_idts xs $ bd end;

    fun binder_tr' (t :: ts) = Term.list_comb (tr' (Lexicon.const name $ t), ts)
      | binder_tr' [] = raise Match;
  in (name, binder_tr') end;


(* idtyp constraints *)

fun idtyp_ast_tr' a [Ast.Appl [Ast.Constant c, x, ty], xs] =
      if c = "_constrain" then
        Ast.Appl [Ast.Constant a, Ast.Appl [Ast.Constant "_idtyp", x, ty], xs]
      else raise Match
  | idtyp_ast_tr' _ _ = raise Match;


(* type propositions *)

fun type_prop_tr' _ (*"_type_prop"*) T [Const ("Pure.sort_constraint", _)] =
      Lexicon.const "_sort_constraint" $ TypeExt.term_of_typ true T
  | type_prop_tr' show_sorts (*"_type_prop"*) T [t] =
      Lexicon.const "_ofclass" $ TypeExt.term_of_typ show_sorts T $ t
  | type_prop_tr' _ (*"_type_prop"*) T ts = raise TYPE ("type_prop_tr'", [T], ts);


(* meta propositions *)

fun prop_tr' tm =
  let
    fun aprop t = Lexicon.const "_aprop" $ t;

    fun is_prop Ts t =
      fastype_of1 (Ts, t) = propT handle TERM _ => false;

    fun is_term (Const ("Pure.term", _) $ _) = true
      | is_term _ = false;

    fun tr' _ (t as Const _) = t
      | tr' Ts (t as Const ("_bound", _) $ u) =
          if is_prop Ts u then aprop t else t
      | tr' _ (t as Free (x, T)) =
          if T = propT then aprop (Lexicon.free x) else t
      | tr' _ (t as Var (xi, T)) =
          if T = propT then aprop (Lexicon.var xi) else t
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

fun impl_ast_tr' (*"==>"*) asts =
  if TypeExt.no_brackets () then raise Match
  else
    (case Ast.unfold_ast_p "==>" (Ast.Appl (Ast.Constant "==>" :: asts)) of
      (prems as _ :: _ :: _, concl) =>
        let
          val (asms, asm) = split_last prems;
          val asms' = Ast.fold_ast_p "_asms" (asms, Ast.Appl [Ast.Constant "_asm", asm]);
        in Ast.Appl [Ast.Constant "_bigimpl", asms', concl] end
    | _ => raise Match);


(* type reflection *)

fun type_tr' show_sorts (*"TYPE"*) (Type ("itself", [T])) ts =
      Term.list_comb (Lexicon.const "_TYPE" $ TypeExt.term_of_typ show_sorts T, ts)
  | type_tr' _ _ _ = raise Match;


(* type constraints *)

fun type_constraint_tr' show_sorts (*"_type_constraint_"*) (Type ("fun", [T, _])) (t :: ts) =
      Term.list_comb (Lexicon.const SynExt.constrainC $ t $ TypeExt.term_of_typ show_sorts T, ts)
  | type_constraint_tr' _ _ _ = raise Match;


(* dependent / nondependent quantifiers *)

fun var_abs mark (x, T, b) =
  let val ([x'], _) = Name.variants [x] (Term.declare_term_names b Name.context)
  in (x', subst_bound (mark (x', T), b)) end;

val variant_abs = var_abs Free;
val variant_abs' = var_abs mark_boundT;

fun dependent_tr' (q, r) (A :: Abs (x, T, B) :: ts) =
      if Term.loose_bvar1 (B, 0) then
        let val (x', B') = variant_abs' (x, dummyT, B);
        in Term.list_comb (Lexicon.const q $ mark_boundT (x', T) $ A $ B', ts) end
      else Term.list_comb (Lexicon.const r $ A $ B, ts)
  | dependent_tr' _ _ = raise Match;


(* quote / antiquote *)

fun antiquote_tr' name =
  let
    fun tr' i (t $ u) =
      if u aconv Bound i then Lexicon.const name $ tr' i t
      else tr' i t $ tr' i u
      | tr' i (Abs (x, T, t)) = Abs (x, T, tr' (i + 1) t)
      | tr' i a = if a aconv Bound i then raise Match else a;
  in tr' 0 end;

fun quote_tr' name (Abs (_, _, t)) = Term.incr_boundvars ~1 (antiquote_tr' name t)
  | quote_tr' _ _ = raise Match;

fun quote_antiquote_tr' quoteN antiquoteN name =
  let
    fun tr' (t :: ts) = Term.list_comb (Lexicon.const quoteN $ quote_tr' antiquoteN t, ts)
      | tr' _ = raise Match;
  in (name, tr') end;


(* indexed syntax *)

fun index_ast_tr' (*"_index"*) [Ast.Appl [Ast.Constant "_struct", ast]] = ast
  | index_ast_tr' _ = raise Match;


(* implicit structures *)

fun the_struct' structs s =
  [(case Lexicon.read_nat s of
    SOME i => Ast.Variable (the_struct structs i handle ERROR _ => raise Match)
  | NONE => raise Match)] |> Ast.mk_appl (Ast.Constant "_free");

fun struct_ast_tr' structs (*"_struct"*) [Ast.Constant "_indexdefault"] =
      the_struct' structs "1"
  | struct_ast_tr' structs (*"_struct"*) [Ast.Appl [Ast.Constant "_indexnum", Ast.Constant s]] =
      the_struct' structs s
  | struct_ast_tr' _ _ = raise Match;



(** Pure translations **)

val pure_trfuns =
 ([("_constify", constify_ast_tr), ("_appl", appl_ast_tr), ("_applC", applC_ast_tr),
   ("_lambda", lambda_ast_tr), ("_idtyp", idtyp_ast_tr), ("_idtypdummy", idtypdummy_ast_tr),
   ("_bigimpl", bigimpl_ast_tr), ("_indexdefault", indexdefault_ast_tr),
   ("_indexnum", indexnum_ast_tr), ("_indexvar", indexvar_ast_tr), ("_struct", struct_ast_tr)],
  [("_abs", abs_tr), ("_aprop", aprop_tr), ("_ofclass", ofclass_tr),
   ("_sort_constraint", sort_constraint_tr), ("_TYPE", type_tr),
   ("_DDDOT", dddot_tr), ("_index", index_tr)],
  ([]: (string * (term list -> term)) list),
  [("_abs", abs_ast_tr'), ("_idts", idtyp_ast_tr' "_idts"),
   ("_pttrns", idtyp_ast_tr' "_pttrns"), ("==>", impl_ast_tr'),
   ("_index", index_ast_tr')]);

val pure_trfunsT =
  [("_type_prop", type_prop_tr'), ("TYPE", type_tr'), ("_type_constraint_", type_constraint_tr')];

fun struct_trfuns structs =
  ([], [("_struct", struct_tr structs)], [], [("_struct", struct_ast_tr' structs)]);



(** pts_to_asts **)

fun pts_to_asts ctxt trf pts =
  let
    fun trans a args =
      (case trf a of
        NONE => Ast.mk_appl (Ast.Constant a) args
      | SOME f => f ctxt args);

    (*translate pt bottom-up*)
    fun ast_of (Parser.Node (a, pts)) = trans a (map ast_of pts)
      | ast_of (Parser.Tip tok) = Ast.Variable (Lexicon.str_of_token tok);

    val exn_results = map (Exn.capture ast_of) pts;
    val exns = map_filter Exn.get_exn exn_results;
    val results = map_filter Exn.get_result exn_results
  in (case (results, exns) of ([], exn :: _) => reraise exn | _ => results) end;



(** asts_to_terms **)

fun asts_to_terms ctxt trf asts =
  let
    fun trans a args =
      (case trf a of
        NONE => Term.list_comb (Lexicon.const a, args)
      | SOME f => f ctxt args);

    fun term_of (Ast.Constant a) = trans a []
      | term_of (Ast.Variable x) = Lexicon.read_var x
      | term_of (Ast.Appl (Ast.Constant a :: (asts as _ :: _))) =
          trans a (map term_of asts)
      | term_of (Ast.Appl (ast :: (asts as _ :: _))) =
          Term.list_comb (term_of ast, map term_of asts)
      | term_of (ast as Ast.Appl _) = raise Ast.AST ("ast_to_term: malformed ast", [ast]);

    val free_fixed = Term.map_aterms
      (fn t as Const (c, T) =>
          (case try (unprefix Lexicon.fixedN) c of
            NONE => t
          | SOME x => Free (x, T))
        | t => t);

    val exn_results = map (Exn.capture (term_of #> free_fixed)) asts;
    val exns = map_filter Exn.get_exn exn_results;
    val results = map_filter Exn.get_result exn_results
  in (case (results, exns) of ([], exn :: _) => reraise exn | _ => results) end;

end;
