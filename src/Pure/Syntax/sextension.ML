(*  Title:      Pure/Syntax/sextension.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Syntax extensions (external interface): mixfix declarations, infixes,
binders, translation rules / functions and the Pure syntax.

TODO:
  move ast_to_term, pt_to_ast (?)
*)

infix |-> <-| <->;

signature SEXTENSION0 =
sig
  structure Parser: PARSER
  local open Parser.SynExt.Ast in
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
        parse_translation: (string * (term list -> term)) list,
        print_translation: (string * (term list -> term)) list,
        print_ast_translation: (string * (ast list -> ast)) list}
    val eta_contract: bool ref
    val mk_binder_tr: string * string -> string * (term list -> term)
    val mk_binder_tr': string * string -> string * (term list -> term)
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
  val syntax_consts: (string list * string) list
  val constrainAbsC: string
end;

signature SEXTENSION =
sig
  include SEXTENSION1
  local open Parser Parser.SynExt Parser.SynExt.Ast in
    val xrules_of: sext -> xrule list
    val abs_tr': term -> term
    val appl_ast_tr': ast * ast list -> ast
    val syn_ext_of_sext: string list -> string list -> (string -> typ) -> sext -> syn_ext
    val pt_to_ast: (string -> (ast list -> ast) option) -> parsetree -> ast
    val ast_to_term: (string -> (term list -> term) option) -> ast -> term
    val apropC: string
  end
end;

functor SExtensionFun(Parser: PARSER): SEXTENSION =
struct

structure Parser = Parser;
open Parser.Lexicon Parser.SynExt.Ast Parser.SynExt Parser;


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
    parse_translation: (string * (term list -> term)) list,
    print_translation: (string * (term list -> term)) list,
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
        parse_translation = parse_translation,
        print_translation = print_translation,
        print_ast_translation = []}
  | sext_components (NewSext cmps) = cmps;


(* mixfix_of *)

fun mixfix_of (Sext {mixfix, ...}) = mixfix
  | mixfix_of (NewSext {mixfix, ...}) = mixfix;


(* xrules_of *)

fun xrules_of (Sext _) = []
  | xrules_of (NewSext {xrules, ...}) = xrules;



(** parse (ast) translations **)

(* application *)

fun appl_ast_tr (*"_appl"*) [f, args] = Appl (f :: unfold_ast "_args" args)
  | appl_ast_tr (*"_appl"*) asts = raise_ast "appl_ast_tr" asts;


(* abstraction *)

fun idtyp_ast_tr (*"_idtyp"*) [x, ty] = Appl [Constant constrainC, x, ty]
  | idtyp_ast_tr (*"_idtyp"*) asts = raise_ast "idtyp_ast_tr" asts;

fun lambda_ast_tr (*"_lambda"*) [idts, body] =
      fold_ast_p "_abs" (unfold_ast "_idts" idts, body)
  | lambda_ast_tr (*"_lambda"*) asts = raise_ast "lambda_ast_tr" asts;

fun abs_tr (*"_abs"*) [Free (x, T), body] = absfree (x, T, body)
  | abs_tr (*"_abs"*) (ts as [Const (c, _) $ Free (x, T) $ tT, body]) =
      if c = constrainC then
        Const ("_constrainAbs", dummyT) $ absfree (x, T, body) $ tT
      else raise_term "abs_tr" ts
  | abs_tr (*"_abs"*) ts = raise_term "abs_tr" ts;


(* nondependent abstraction *)

fun k_tr (*"_K"*) [t] = Abs ("uu", dummyT, incr_boundvars 1 t)
  | k_tr (*"_K"*) ts = raise_term "k_tr" ts;


(* binder *)

fun mk_binder_tr (sy, name) =
  let
    val const = Const (name, dummyT);

    fun tr (Free (x, T), t) = const $ absfree (x, T, t)
      | tr (Const ("_idts", _) $ idt $ idts, t) = tr (idt, tr (idts, t))
      | tr (t1 as Const (c, _) $ Free (x, T) $ tT, t) =
          if c = constrainC then
            const $ (Const ("_constrainAbs", dummyT) $ absfree (x, T, t) $ tT)
          else raise_term "binder_tr" [t1, t]
      | tr (t1, t2) = raise_term "binder_tr" [t1, t2];

    fun binder_tr (*sy*) [idts, body] = tr (idts, body)
      | binder_tr (*sy*) ts = raise_term "binder_tr" ts;
  in
    (sy, binder_tr)
  end;


(* atomic props *)

fun aprop_tr (*"_aprop"*) [t] =
      Const (constrainC, dummyT) $ t $ Free ("prop", dummyT)
  | aprop_tr (*"_aprop"*) ts = raise_term "aprop_tr" ts;


(* meta implication *)

fun bigimpl_ast_tr (*"_bigimpl"*) [asms, concl] =
      fold_ast_p "==>" (unfold_ast "_asms" asms, concl)
  | bigimpl_ast_tr (*"_bigimpl"*) asts = raise_ast "bigimpl_ast_tr" asts;


(* explode atoms *)

fun explode_tr (*"_explode"*) (ts as [consC, nilC, bit0, bit1, txt]) =
      let
        fun mk_list [] = nilC
          | mk_list (t :: ts) = consC $ t $ mk_list ts;

        fun encode_bit 0 = bit0
          | encode_bit 1 = bit1
          | encode_bit _ = sys_error "encode_bit";

        fun encode_char c =   (* FIXME leading 0s (?) *)
          mk_list (map encode_bit (radixpand (2, (ord c))));

        val str =
          (case txt of
            Free (s, _) => s
          | Const (s, _) => s
          | _ => raise_term "explode_tr" ts);
      in
        mk_list (map encode_char (explode str))
      end
  | explode_tr (*"_explode"*) ts = raise_term "explode_tr" ts;



(** print (ast) translations **)

(* application *)

fun appl_ast_tr' (f, []) = raise_ast "appl_ast_tr'" [f]
  | appl_ast_tr' (f, args) = Appl [Constant "_appl", f, fold_ast "_args" args];


(* abstraction *)

fun strip_abss vars_of body_of tm =
  let
    fun free (x, _) = Free (x, dummyT);

    val vars = vars_of tm;
    val body = body_of tm;
    val rev_new_vars = rename_wrt_term body vars;
  in
    (map Free (rev rev_new_vars), subst_bounds (map free rev_new_vars, body))
  end;

(*do (partial) eta-contraction before printing*)

val eta_contract = ref false;

fun eta_contr tm =
  let
    fun eta_abs (Abs (a, T, t)) =
          (case eta_abs t of
            t' as f $ u =>
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
  foldr (fn (x, t) => Const ("_abs", dummyT) $ x $ t)
    (strip_abss strip_abs_vars strip_abs_body (eta_contr tm));


fun abs_ast_tr' (*"_abs"*) asts =
  (case unfold_ast_p "_abs" (Appl (Constant "_abs" :: asts)) of
    ([], _) => raise_ast "abs_ast_tr'" asts
  | (xs, body) => Appl [Constant "_lambda", fold_ast "_idts" xs, body]);


(* binder *)

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
    (asms as _ :: _ :: _, concl)
      => Appl [Constant "_bigimpl", fold_ast "_asms" asms, concl]
  | _ => raise Match);


(* dependent / nondependent quantifiers *)

fun dependent_tr' (q, r) (A :: Abs (x, T, B) :: ts) =
      if 0 mem (loose_bnos B) then
        let val (x', B') = variant_abs (x, dummyT, B);
        in list_comb (Const (q, dummyT) $ Free (x', T) $ A $ B', ts) end
      else list_comb (Const (r, dummyT) $ A $ B, ts)
  | dependent_tr' _ _ = raise Match;


(* implode atoms *)

fun implode_ast_tr' (*"_implode"*) (asts as [Constant cons_name, nilC,
    bit0, bit1, bitss]) =
      let
        fun err () = raise_ast "implode_ast_tr'" asts;

        fun strip_list lst =
          let val (xs, y) = unfold_ast_p cons_name lst
          in if y = nilC then xs else err ()
          end;

        fun decode_bit bit =
          if bit = bit0 then "0"
          else if bit = bit1 then "1"
          else err ();

        fun decode_char bits =
          chr (#1 (scan_radixint (2, map decode_bit (strip_list bits))));
      in
        Variable (implode (map decode_char (strip_list bitss)))
      end
  | implode_ast_tr' (*"_implode"*) asts = raise_ast "implode_ast_tr'" asts;



(** syn_ext_of_sext **)

fun strip_esc str =
  let
    fun strip ("'" :: c :: cs) = c :: strip cs
      | strip ["'"] = []
      | strip (c :: cs) = c :: strip cs
      | strip [] = [];
  in
    implode (strip (explode str))
  end;

fun infix_name sy = "op " ^ strip_esc sy;


fun syn_ext_of_sext roots xconsts read_typ sext =
  let
    val {mixfix, parse_ast_translation, parse_translation, print_translation,
      print_ast_translation, ...} = sext_components sext;

    val tinfixT = [typeT, typeT] ---> typeT;

    fun binder (Binder (sy, _, name, _, _)) = Some (sy, name)
      | binder _ = None;

    fun binder_typ ty =
      (case read_typ ty of
        Type ("fun", [Type ("fun", [_, T2]), T3]) =>
          [Type ("idts", []), T2] ---> T3
      | _ => error ("Illegal binder type " ^ quote ty));

    fun mk_infix sy ty c p1 p2 p3 =
      [Mfix ("(_ " ^ sy ^ "/ _)", ty, c, [p1, p2], p3),
       Mfix ("op " ^ sy, ty, c, [], max_pri)];

    fun mfix_of (Mixfix (sy, ty, c, ps, p)) = [Mfix (sy, read_typ ty, c, ps, p)]
      | mfix_of (Delimfix (sy, ty, c)) = [Mfix (sy, read_typ ty, c, [], max_pri)]
      | mfix_of (Infixl (sy, ty, p)) =
          mk_infix sy (read_typ ty) (infix_name sy) p (p + 1) p
      | mfix_of (Infixr (sy, ty, p)) =
          mk_infix sy (read_typ ty) (infix_name sy) (p + 1) p p
      | mfix_of (Binder (sy, ty, _, p, q)) =
          [Mfix ("(3" ^ sy ^ "_./ _)", binder_typ ty, sy, [0, p], q)]
      | mfix_of (TInfixl (s, c, p)) =
          [Mfix ("(_ " ^ s ^ "/ _)", tinfixT, c, [p, p + 1], p)]
      | mfix_of (TInfixr (s, c, p)) =
          [Mfix ("(_ " ^ s ^ "/ _)", tinfixT, c, [p + 1, p], p)];

    val mfix = flat (map mfix_of mixfix);
    val binders = mapfilter binder mixfix;
    val bparses = map mk_binder_tr binders;
    val bprints = map (mk_binder_tr' o swap) binders;
  in
    syn_ext roots mfix (distinct (filter is_xid xconsts))
      (parse_ast_translation,
        bparses @ parse_translation,
        bprints @ print_translation,
        print_ast_translation)
      ([], [])
  end;



(** constants **)

fun constants sext =
  let
    fun consts (Delimfix (_, ty, c)) = ([c], ty)
      | consts (Mixfix (_, ty, c, _, _)) = ([c], ty)
      | consts (Infixl (c, ty, _)) = ([infix_name c], ty)
      | consts (Infixr (c, ty, _)) = ([infix_name c], ty)
      | consts (Binder (_, ty, c, _, _)) = ([c], ty)
      | consts _ = ([""], "");    (*is filtered out below*)
  in
    distinct (filter_out (fn (l, _) => l = [""]) (map consts (mixfix_of sext)))
  end;



(** pt_to_ast **)

fun pt_to_ast trf pt =
  let
    fun trans a args =
      (case trf a of
        None => mk_appl (Constant a) args
      | Some f => f args handle exn
          => (writeln ("Error in parse ast translation for " ^ quote a); raise exn));

    fun ast_of (Node (a, pts)) = trans a (map ast_of pts)
      | ast_of (Tip tok) = Variable (str_of_token tok);
  in
    ast_of pt
  end;



(** ast_to_term **)

fun ast_to_term trf ast =
  let
    fun trans a args =
      (case trf a of
        None => list_comb (Const (a, dummyT), args)
      | Some f => f args handle exn
          => (writeln ("Error in parse translation for " ^ quote a); raise exn));

    fun term_of (Constant a) = trans a []
      | term_of (Variable x) = scan_var x
      | term_of (Appl (Constant a :: (asts as _ :: _))) =
          trans a (map term_of asts)
      | term_of (Appl (ast :: (asts as _ :: _))) =
          list_comb (term_of ast, map term_of asts)
      | term_of (ast as Appl _) = raise_ast "ast_to_term: malformed ast" [ast];
  in
    term_of ast
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
      Mixfix   ("(1_/(1'(_')))", "[('b => 'a), " ^ args ^ "] => aprop", applC, [max_pri, 0], max_pri),
      Delimfix ("PROP _",     "aprop => prop",                 "_aprop"),
      Delimfix ("_",          "prop => asms",                  ""),
      Delimfix ("_;/ _",      "[prop, asms] => asms",          "_asms"),
      Mixfix   ("((3[| _ |]) ==>/ _)", "[asms, prop] => prop", "_bigimpl", [0, 1], 1),
      Mixfix   ("(_ ==/ _)",  "['a::{}, 'a] => prop",          "==", [3, 2], 2),
      Mixfix   ("(_ =?=/ _)", "['a::{}, 'a] => prop",          "=?=", [3, 2], 2),
      Mixfix   ("(_ ==>/ _)", "[prop, prop] => prop",          "==>", [2, 1], 1),
      Binder   ("!!",         "('a::logic => prop) => prop",   "all", 0, 0)],
    xrules = [],
    parse_ast_translation = [(applC, appl_ast_tr), ("_lambda", lambda_ast_tr),
      ("_idtyp", idtyp_ast_tr), ("_bigimpl", bigimpl_ast_tr)],
    parse_translation = [("_abs", abs_tr), ("_aprop", aprop_tr), ("_K", k_tr),
      ("_explode", explode_tr)],
    print_translation = [],
    print_ast_translation = [("_abs", abs_ast_tr'), ("_idts", idts_ast_tr'),
      ("==>", impl_ast_tr'), ("_implode", implode_ast_tr')]};

val syntax_types = terminals @ ["syntax", logic, "type", "types", "sort",
  "classes", args, "idt", "idts", "aprop", "asms"];

val syntax_consts = [(["_K", "_explode", "_implode"], "syntax")];

val constrainAbsC = "_constrainAbs";
val apropC = "_aprop";


end;

