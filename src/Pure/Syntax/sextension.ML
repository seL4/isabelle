(*  Title:      Pure/Syntax/sextension
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Syntax extensions: mixfix declarations, syntax rules, infixes, binders and
the Pure syntax.

Changes:
  SEXTENSION: added Ast, xrule
  changed sext
  added ast_to_term
  ext_of_sext: added xconsts
  SEXTENSION1: added empty_sext, appl_ast_tr'
  SEXTENSION1: removed appl_tr'
TODO:
*)


infix |-> <-| <->;

signature SEXTENSION0 =
sig
  structure Ast: AST
  local open Ast in
    datatype mixfix =
      Mixfix of string * string * string * int list * int |
      Delimfix of string * string * string |
      Infixl of string * string * int |
      Infixr of string * string * int |
      Binder of string * string * string * int * int |
      TInfixl of string * string * int |
      TInfixr of string * string * int
    datatype xrule =
      op |-> of (string * string) * (string * string) |
      op <-| of (string * string) * (string * string) |
      op <-> of (string * string) * (string * string)
    datatype sext =
      Sext of {
        mixfix: mixfix list,
        parse_translation: (string * (term list -> term)) list,
        print_translation: (string * (term list -> term)) list} |
      NewSext of {
        mixfix: mixfix list,
        xrules: xrule list,
        parse_ast_translation: (string * (ast list -> ast)) list,
        parse_preproc: (ast -> ast) option,
        parse_postproc: (ast -> ast) option,
        parse_translation: (string * (term list -> term)) list,
        print_translation: (string * (term list -> term)) list,
        print_preproc: (ast -> ast) option,
        print_postproc: (ast -> ast) option,
        print_ast_translation: (string * (ast list -> ast)) list}
    val eta_contract: bool ref
    val mk_binder_tr: string * string -> string * (term list -> term)
    val mk_binder_tr': string * string -> string * (term list -> term)
    val ndependent_tr: string -> term list -> term
    val dependent_tr': string * string -> term list -> term
    val max_pri: int
  end
end;

signature SEXTENSION1 =
sig
  include SEXTENSION0
  val empty_sext: sext
  val simple_sext: mixfix list -> sext
  val constants: sext -> (string list * string) list
  val pure_sext: sext
  val syntax_types: string list
  val constrainAbsC: string
end;

signature SEXTENSION =
sig
  include SEXTENSION1
  structure Extension: EXTENSION
  sharing Extension.XGram.Ast = Ast
  local open Extension Ast in
    val xrules_of: sext -> xrule list
    val abs_tr': term -> term
    val appl_ast_tr': ast * ast list -> ast
    val ext_of_sext: string list -> string list -> (string -> typ) -> sext -> ext
    val ast_to_term: (string -> (term list -> term) option) -> ast -> term
    val constrainIdtC: string
    val apropC: string
  end
end;

functor SExtensionFun(structure TypeExt: TYPE_EXT and Lexicon: LEXICON)(*: SEXTENSION *) = (* FIXME *)
struct

structure Extension = TypeExt.Extension;
structure Ast = Extension.XGram.Ast;
open Extension Ast;


(** datatype sext **)

datatype mixfix =
  Mixfix of string * string * string * int list * int |
  Delimfix of string * string * string |
  Infixl of string * string * int |
  Infixr of string * string * int |
  Binder of string * string * string * int * int |
  TInfixl of string * string * int |
  TInfixr of string * string * int;

datatype xrule =
  op |-> of (string * string) * (string * string) |
  op <-| of (string * string) * (string * string) |
  op <-> of (string * string) * (string * string);

datatype sext =
  Sext of {
    mixfix: mixfix list,
    parse_translation: (string * (term list -> term)) list,
    print_translation: (string * (term list -> term)) list} |
  NewSext of {
    mixfix: mixfix list,
    xrules: xrule list,
    parse_ast_translation: (string * (ast list -> ast)) list,
    parse_preproc: (ast -> ast) option,
    parse_postproc: (ast -> ast) option,
    parse_translation: (string * (term list -> term)) list,
    print_translation: (string * (term list -> term)) list,
    print_preproc: (ast -> ast) option,
    print_postproc: (ast -> ast) option,
    print_ast_translation: (string * (ast list -> ast)) list};


(* simple_sext *)

fun simple_sext mixfix =
  Sext {mixfix = mixfix, parse_translation = [], print_translation = []};


(* empty_sext *)

val empty_sext = simple_sext [];


(* sext_components *)

fun sext_components (Sext {mixfix, parse_translation, print_translation}) =
      {mixfix = mixfix,
        xrules = [],
        parse_ast_translation = [],
        parse_preproc = None,
        parse_postproc = None,
        parse_translation = parse_translation,
        print_translation = print_translation,
        print_preproc = None,
        print_postproc = None,
        print_ast_translation = []}
  | sext_components (NewSext cmps) = cmps;


(* mixfix_of *)

fun mixfix_of (Sext {mixfix, ...}) = mixfix
  | mixfix_of (NewSext {mixfix, ...}) = mixfix;


(* xrules_of *)

fun xrules_of (Sext _) = []
  | xrules_of (NewSext {xrules, ...}) = xrules;



(** parse translations **)

(* application *)

fun appl_ast_tr (*"_appl"*) [f, args] = Appl (f :: unfold_ast "_args" args)
  | appl_ast_tr (*"_appl"*) asts = raise_ast "appl_ast_tr" asts;


(* abstraction *)

fun idtyp_ast_tr (*"_idtyp"*) [x, ty] = Appl [Constant constrainC, x, ty]
  | idtyp_ast_tr (*"_idtyp"*) asts = raise_ast "idtyp_ast_tr" asts;

fun lambda_ast_tr (*"_lambda"*) [idts, body] =
      fold_ast_p "_%" (unfold_ast "_idts" idts, body)
  | lambda_ast_tr (*"_lambda"*) asts = raise_ast "lambda_ast_tr" asts;

fun abs_tr (*"_%"*) [Free (x, T), body] = absfree (x, T, body)
  | abs_tr (*"_%"*) (ts as [Const (c, _) $ Free (x, T) $ tT, body]) =
      if c = constrainC then
        Const ("_constrainAbs", dummyT) $ absfree (x, T, body) $ tT
      else raise (TERM ("abs_tr", ts))
  | abs_tr (*"_%"*) ts = raise (TERM ("abs_tr", ts));


(* binder *)  (* FIXME check *) (* FIXME check *)

fun mk_binder_tr (sy, name) =
  let
    val const = Const (name, dummyT);

    fun tr (Free (x, T), t) = const $ absfree (x, T, t)
      | tr (Const ("_idts", _) $ idt $ idts, t) = tr (idt, tr (idts, t))
      | tr (t1 as (Const (c, _) $ Free (x, T) $ tT), t) =   (* FIXME *)
          if c = constrainC then
            const $ (Const ("_constrainAbs", dummyT) $ absfree (x, T, t) $ tT)
          else raise (TERM ("binder_tr", [t1, t]))
      | tr (t1, t2) = raise (TERM ("binder_tr", [t1, t2]));

    fun binder_tr (*sy*) [idts, body] = tr (idts, body)
      | binder_tr (*sy*) ts = raise (TERM ("binder_tr", ts));
  in
    (sy, binder_tr)
  end;


(* atomic props *)

fun aprop_ast_tr (*"_aprop"*) [ast] = ast
  | aprop_ast_tr (*"_aprop"*) asts = raise_ast "aprop_ast_tr" asts;


(* meta implication *)

fun bigimpl_ast_tr (*"_bigimpl"*) [asms, concl] =
      fold_ast_p "==>" (unfold_ast "_asms" asms, concl)
  | bigimpl_ast_tr (*"_bigimpl"*) asts = raise_ast "bigimpl_ast_tr" asts;


(* 'dependent' type operators *)

fun ndependent_tr q [A, B] =
      Const (q, dummyT) $ A $ Abs ("x", dummyT, incr_boundvars 1 B)
  | ndependent_tr _ _ = raise Match;



(** print translations **)

(* application *)

fun appl_ast_tr' (f, []) = raise_ast "appl_ast_tr'" [f]
  | appl_ast_tr' (f, args) = Appl [Constant "_appl", f, fold_ast "_args" args];


(* abstraction *)   (* FIXME check *)

fun strip_abss vars_of body_of tm =
  let
    val vars = vars_of tm;
    val body = body_of tm;
    val rev_new_vars = rename_wrt_term body vars;
  in
    (map Free (rev rev_new_vars),
      subst_bounds (map (fn (x, _) => Free (x, dummyT)) rev_new_vars, body))
  end;

(*do (partial) eta-contraction before printing*)

val eta_contract = ref false;

fun eta_contr tm =
  let
    fun eta_abs (Abs (a, T, t)) =
          (case eta_abs t of
            t' as (f $ u) =>
              (case eta_abs u of
                Bound 0 =>
                  if not (0 mem loose_bnos f) then incr_boundvars ~1 f
                  else Abs (a, T, t')
              | _ => Abs (a, T, t'))
          | t' => Abs (a, T, t'))
      | eta_abs t = t;
  in
    if ! eta_contract then eta_abs tm else tm
  end;


fun abs_tr' tm =
  foldr (fn (x, t) => Const ("_%", dummyT) $ x $ t)
    (strip_abss strip_abs_vars strip_abs_body (eta_contr tm));


fun lambda_ast_tr' (*"_%"*) asts =
  (case unfold_ast_p "_%" (Appl (Constant "_%" :: asts)) of
    ([], _) => raise_ast "lambda_ast_tr'" asts
  | (xs, body) => Appl [Constant "_lambda", fold_ast "_idts" xs, body]);


(* binder *) (* FIXME check *)

fun mk_binder_tr' (name, sy) =
  let
    fun mk_idts [] = raise Match    (*abort translation*)
      | mk_idts [idt] = idt
      | mk_idts (idt :: idts) = Const ("_idts", dummyT) $ idt $ mk_idts idts;

    fun tr' t =
      let
        val (xs, bd) = strip_abss (strip_qnt_vars name) (strip_qnt_body name) t;
      in
        Const (sy, dummyT) $ mk_idts xs $ bd
      end;

    fun binder_tr' (*name*) (t :: ts) =
          list_comb (tr' (Const (name, dummyT) $ t), ts)
      | binder_tr' (*name*) [] = raise Match;
  in
    (name, binder_tr')
  end;


(* idts *)

fun idts_ast_tr' (*"_idts"*) [Appl [Constant c, x, ty], xs] =
      if c = constrainC then
        Appl [Constant "_idts", Appl [Constant "_idtyp", x, ty], xs]
      else raise Match
  | idts_ast_tr' (*"_idts"*) _ = raise Match;


(* meta implication *)

fun impl_ast_tr' (*"==>"*) asts =
  (case unfold_ast_p "==>" (Appl (Constant "==>" :: asts)) of
    (asms as (_ :: _ :: _), concl)
      => Appl [Constant "_bigimpl", fold_ast "_asms" asms, concl]
  | _ => raise Match);


(* 'dependent' type operators *)

fun dependent_tr' (q, r) [A, Abs (x, T, B)] =
      if 0 mem (loose_bnos B) then
        let val (x', B') = variant_abs (x, dummyT, B);
        in Const (q, dummyT) $ Free (x', T) $ A $ B' end
      else Const (r, dummyT) $ A $ B
  | dependent_tr' _ _ = raise Match;



(** constants **)

(* FIXME opn, clean: move *)
val clean =
  let
    fun q ("'" :: c :: cs) = c ^ q cs
      | q (c :: cs) = c ^ q cs
      | q ([]) = ""
  in q o explode end;

val opn = "op ";


fun constants sext =
  let
    fun consts (Delimfix (_, ty, c)) = ([c], ty)
      | consts (Mixfix (_, ty, c, _, _)) = ([c], ty)
      | consts (Infixl (c, ty, _)) = ([opn ^ clean c], ty)
      | consts (Infixr (c, ty, _)) = ([opn ^ clean c], ty)
      | consts (Binder (_, ty, c, _, _)) = ([c], ty)
      | consts _ = ([""], "");    (*is filtered out below*)
  in
    distinct (filter_out (fn (l, _) => l = [""]) (map consts (mixfix_of sext)))
  end;



(** ext_of_sext **)   (* FIXME check, clean *)

fun ext_of_sext roots xconsts read_typ sext =
  let
    val
      {mixfix, parse_ast_translation, parse_preproc, parse_postproc,
        parse_translation, print_translation, print_preproc, print_postproc,
        print_ast_translation, ...} = sext_components sext;

    val infixT = [typeT, typeT] ---> typeT;

    fun binder (Binder (sy, _, name, _, _)) = Some (sy, name)
      | binder _ = None;

    fun binder_typ ty =
      (case read_typ ty of
        Type ("fun", [Type ("fun", [_, T2]), T3]) =>
          [Type ("idts", []), T2] ---> T3
      | _ => error (quote ty ^ " is not a valid binder type."));

    fun mfix_of (Mixfix (sy, ty, c, pl, p)) = [Mfix (sy, read_typ ty, c, pl, p)]
      | mfix_of (Delimfix (sy, ty, c)) = [Mfix (sy, read_typ ty, c, [], max_pri)]
      | mfix_of (Infixl (sy, ty, p)) =
          let val T = read_typ ty and c = opn ^ sy and c' = opn ^ clean sy
          in
            [Mfix (c, T, c', [], max_pri),
             Mfix("(_ " ^ sy ^ "/ _)", T, c', [p, p + 1], p)]
          end
      | mfix_of (Infixr (sy, ty, p)) =
          let val T = read_typ ty and c = opn ^ sy and c' = opn ^ clean sy
          in
            [Mfix(c, T, c', [], max_pri),
             Mfix("(_ " ^ sy ^ "/ _)", T, c', [p + 1, p], p)]
          end
      | mfix_of (Binder (sy, ty, _, p, q)) =
          [Mfix ("(3" ^ sy ^ "_./ _)", binder_typ ty, sy, [0, p], q)]
      | mfix_of (TInfixl (s, c, p)) =
          [Mfix ("(_ " ^ s ^ "/ _)", infixT, c, [p, p + 1], p)]
      | mfix_of (TInfixr (s, c, p)) =
          [Mfix ("(_ " ^ s ^ "/ _)", infixT, c, [p + 1, p], p)];

    val mfix = flat (map mfix_of mixfix);
    val mfix_consts = map (fn (Mfix (_, _, c, _, _)) => c) mfix;
    val bs = mapfilter binder mixfix;
    val bparses = map mk_binder_tr bs;
    val bprints = map (mk_binder_tr' o (fn (x, y) => (y, x))) bs;
  in
    Ext {
      roots = roots, mfix = mfix,
      extra_consts = distinct (filter Lexicon.is_identifier (xconsts @ mfix_consts)),
      parse_ast_translation = parse_ast_translation,
      parse_preproc = parse_preproc,
      parse_postproc = parse_postproc,
      parse_translation = bparses @ parse_translation,
      print_translation = bprints @ print_translation,
      print_preproc = print_preproc,
      print_postproc = print_postproc,
      print_ast_translation = print_ast_translation}
  end;



(** ast_to_term **)

fun ast_to_term trf ast =
  let
    fun scan_vname prfx cs =
      (case Lexicon.scan_varname cs of
        ((x, i), []) => Var ((prfx ^ x, i), dummyT)
      | _ => error ("ast_to_term: bad variable name " ^ quote (implode cs)));

    fun vname_to_var v =
      (case explode v of
        "?" :: "'" :: cs => scan_vname "'" cs
      | "?" :: cs => scan_vname "" cs
      | _ => Free (v, dummyT));

    fun trans a args =
      (case trf a of
        None => list_comb (Const (a, dummyT), args)
      | Some f => ((f args)
          handle _ => error ("ast_to_term: error in translation for " ^ quote a)));

    fun trav (Constant a) = trans a []
      | trav (Appl (Constant a :: (asts as _ :: _))) = trans a (map trav asts)
      | trav (Appl (ast :: (asts as _ :: _))) =
          list_comb (trav ast, map trav asts)
      | trav (ast as (Appl _)) = raise_ast "ast_to_term: malformed ast" [ast]
      | trav (Variable x) = vname_to_var x;
  in
    trav ast
  end;



(** the Pure syntax **)

val pure_sext =
  NewSext {
    mixfix = [
      Mixfix   ("(3%_./ _)",  "[idts, 'a] => ('b => 'a)",      "_lambda", [0], 0),
      Delimfix ("_",          "'a => " ^ args,                 ""),
      Delimfix ("_,/ _",      "['a, " ^ args ^ "] => " ^ args, "_args"),
      Delimfix ("_",          "id => idt",                     ""),
      Mixfix   ("_::_",       "[id, type] => idt",             "_idtyp", [0, 0], 0),
      Delimfix ("'(_')",      "idt => idt",                    ""),
      Delimfix ("_",          "idt => idts",                   ""),
      Mixfix   ("_/ _",       "[idt, idts] => idts",           "_idts", [1, 0], 0),
      Delimfix ("_",          "id => aprop",                   ""),
      Delimfix ("_",          "var => aprop",                  ""),
      Mixfix   ("_'(_')",     "[('b => 'a), " ^ args ^ "] => aprop", applC, [max_pri, 0], 0),
      Delimfix ("PROP _",     "aprop => prop",                 "_aprop"),
      Delimfix ("_",          "prop => asms",                  ""),
      Delimfix ("_;/ _",      "[prop, asms] => asms",          "_asms"),
      Mixfix   ("((3[| _ |]) ==>/ _)", "[asms, prop] => prop", "_bigimpl", [0, 1], 1),
      Mixfix   ("(_ ==/ _)",  "['a::{}, 'a] => prop",          "==", [3, 2], 2),
      Mixfix   ("(_ =?=/ _)", "['a::{}, 'a] => prop",          "=?=", [3, 2], 2),
      Mixfix   ("(_ ==>/ _)", "[prop, prop] => prop",          "==>", [2, 1], 1),
      Binder   ("!!",         "('a::logic => prop) => prop",   "all", 0, 0)],
    xrules = [],
    parse_ast_translation =
      [(applC, appl_ast_tr), ("_lambda", lambda_ast_tr), ("_idtyp", idtyp_ast_tr),
        ("_aprop", aprop_ast_tr), ("_bigimpl", bigimpl_ast_tr)],
    parse_preproc = None,
    parse_postproc = None,
    parse_translation = [("_%", abs_tr)],
    print_translation = [],
    print_preproc = None,
    print_postproc = None,
    print_ast_translation = [("_%", lambda_ast_tr'), ("_idts", idts_ast_tr'),
      ("==>", impl_ast_tr')]};

val syntax_types =    (* FIXME clean, check *)
  [logic, "aprop", args, "asms", id, "idt", "idts", tfree, tvar, "type", "types",
    var, "sort", "classes"]

val constrainIdtC = "_idtyp";
val constrainAbsC = "_constrainAbs";
val apropC = "_aprop";


end;

