(*  Title:      Pure/sign.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel

The abstract type "sg" of signatures.

TODO:
  a clean modular sequential Sign.extend (using sg_ext list);
*)

signature SIGN =
sig
  structure Symtab: SYMTAB
  structure Syntax: SYNTAX
  structure Type: TYPE
  sharing Symtab = Type.Symtab
  local open Type in
    type sg
    val rep_sg: sg ->
      {tsig: type_sig,
       const_tab: typ Symtab.table,
       syn: Syntax.syntax,
       stamps: string ref list}
    val subsig: sg * sg -> bool
    val eq_sg: sg * sg -> bool
    val print_sg: sg -> unit
    val pprint_sg: sg -> pprint_args -> unit
    val pretty_term: sg -> term -> Syntax.Pretty.T
    val pretty_typ: sg -> typ -> Syntax.Pretty.T
    val string_of_term: sg -> term -> string
    val string_of_typ: sg -> typ -> string
    val pprint_term: sg -> term -> pprint_args -> unit
    val pprint_typ: sg -> typ -> pprint_args -> unit
    val certify_typ: sg -> typ -> typ
    val certify_term: sg -> term -> term * typ * int
    val read_typ: sg * (indexname -> sort option) -> string -> typ
    val extend: sg -> string ->
      (class * class list) list * class list *
      (string list * int) list *
      (string * string list * string) list *
      (string list * (sort list * class)) list *
      (string list * string) list * Syntax.sext option -> sg
    val merge: sg * sg -> sg
    val pure: sg
  end
end;

functor SignFun(structure Syntax: SYNTAX and Type: TYPE): SIGN =
struct

structure Symtab = Type.Symtab;
structure Syntax = Syntax;
structure Pretty = Syntax.Pretty;
structure Type = Type;
open Type;


(** datatype sg **)

(*the "ref" in stamps ensures that no two signatures are identical -- it is
  impossible to forge a signature*)

datatype sg =
  Sg of {
    tsig: type_sig,                 (*order-sorted signature of types*)
    const_tab: typ Symtab.table,    (*types of constants*)
    syn: Syntax.syntax,             (*syntax for parsing and printing*)
    stamps: string ref list};       (*unique theory indentifier*)

fun rep_sg (Sg args) = args;


fun subsig (Sg {stamps = s1, ...}, Sg {stamps = s2, ...}) = s1 subset s2;

fun eq_sg (Sg {stamps = s1, ...}, Sg {stamps = s2, ...}) = eq_set (s1, s2);



(** print signature **)

fun print_sg sg =
  let
    fun prt_typ syn ty = Pretty.quote (Syntax.pretty_typ syn ty);

    fun pretty_sort [cl] = Pretty.str cl
      | pretty_sort cls = Pretty.str_list "{" "}" cls;

    fun pretty_subclass (cl, cls) = Pretty.block
      [Pretty.str (cl ^ " <"), Pretty.brk 1, pretty_sort cls];

    fun pretty_default cls = Pretty.block
      [Pretty.str "default:", Pretty.brk 1, pretty_sort cls];

    fun pretty_arg (ty, n) = Pretty.str (ty ^ " " ^ string_of_int n);

    fun pretty_abbr syn (ty, (vs, rhs)) = Pretty.block
      [prt_typ syn (Type (ty, map (fn v => TVar (v, [])) vs)),
        Pretty.str " =", Pretty.brk 1, prt_typ syn rhs];

    fun pretty_arity ty (cl, []) = Pretty.block
          [Pretty.str (ty ^ " ::"), Pretty.brk 1, Pretty.str cl]
      | pretty_arity ty (cl, srts) = Pretty.block
          [Pretty.str (ty ^ " ::"), Pretty.brk 1,
            Pretty.list "(" ")" (map pretty_sort srts),
            Pretty.brk 1, Pretty.str cl];

    fun pretty_coreg (ty, ars) = map (pretty_arity ty) ars;

    fun pretty_const syn (c, ty) = Pretty.block
      [Pretty.str (quote c ^ " ::"), Pretty.brk 1, prt_typ syn ty];


    val Sg {tsig, const_tab, syn, stamps} = sg;
    val {classes, subclass, default, args, abbrs, coreg} = rep_tsig tsig;
  in
    Pretty.writeln (Pretty.strs ("stamps:" :: map ! stamps));
    Pretty.writeln (Pretty.strs ("classes:" :: classes));
    Pretty.writeln (Pretty.big_list "subclass:" (map pretty_subclass subclass));
    Pretty.writeln (pretty_default default);
    Pretty.writeln (Pretty.big_list "types:" (map pretty_arg args));
    Pretty.writeln (Pretty.big_list "abbrs:" (map (pretty_abbr syn) abbrs));
    Pretty.writeln (Pretty.big_list "coreg:" (flat (map pretty_coreg coreg)));
    Pretty.writeln (Pretty.big_list "consts:"
      (map (pretty_const syn) (Symtab.alist_of const_tab)))
  end;


fun pprint_sg (Sg {stamps, ...}) =
  Pretty.pprint (Pretty.str_list "{" "}" (map ! stamps));



(** pretty printing of terms and types **)

fun pretty_term (Sg {syn, ...}) = Syntax.pretty_term syn;
fun pretty_typ (Sg {syn, ...}) = Syntax.pretty_typ syn;

fun string_of_term (Sg {syn, ...}) = Syntax.string_of_term syn;
fun string_of_typ (Sg {syn, ...}) = Syntax.string_of_typ syn;

fun pprint_term sg = Pretty.pprint o Pretty.quote o (pretty_term sg);
fun pprint_typ sg = Pretty.pprint o Pretty.quote o (pretty_typ sg);



(** certify types and terms **)

(*errors are indicated by exception TYPE*)

fun certify_typ (Sg {tsig, ...}) ty = cert_typ tsig ty;


(* FIXME -> term.ML (?) *)
fun mapfilter_atoms f (Abs (_, _, t)) = mapfilter_atoms f t
  | mapfilter_atoms f (t $ u) = mapfilter_atoms f t @ mapfilter_atoms f u
  | mapfilter_atoms f a = (case f a of Some y => [y] | None => []);

fun certify_term (sg as Sg {tsig, const_tab, ...}) tm =
  let
    fun valid_const a T =
      (case Symtab.lookup (const_tab, a) of
        Some U => typ_instance (tsig, T, U)
      | _ => false);

    fun atom_err (Const (a, T)) =
          if valid_const a T then None
          else Some ("Illegal type for constant " ^ quote a ^ " :: " ^
            quote (string_of_typ sg T))
      | atom_err (Var ((x, i), _)) =
          if i < 0 then Some ("Negative index for Var " ^ quote x) else None
      | atom_err _ = None;


    val norm_tm =
      (case it_term_types (typ_errors tsig) (tm, []) of
        [] => map_term_types (norm_typ tsig) tm
      | errs => raise_type (cat_lines errs) [] [tm]);
  in
    (case mapfilter_atoms atom_err norm_tm of
      [] => (norm_tm, type_of norm_tm, maxidx_of_term norm_tm)
    | errs => raise_type (cat_lines errs) [] [norm_tm])
  end;



(** read types **)

(*read and certify typ wrt a signature; errors are indicated by
  exception ERROR (with messages already printed)*)

fun rd_typ tsig syn sort_of s =
  let
    val def_sort = defaultS tsig;
    val raw_ty =        (*this may raise ERROR, too!*)
      Syntax.read_typ syn (fn x => if_none (sort_of x) def_sort) s;
  in
    cert_typ tsig raw_ty
      handle TYPE (msg, _, _) => error msg
  end
  handle ERROR => error ("The error(s) above occurred in type " ^ quote s);

fun read_typ (Sg {tsig, syn, ...}, sort_of) s = rd_typ tsig syn sort_of s;



(** extend signature **)

(*errors are indicated by exception ERROR (with messages already printed)*)

fun extend sg name (classes, default, types, abbrs, arities, consts, opt_sext) =
  let
    (*reset TVar indices to 0, renaming to preserve distinctness*)
    fun zero_tvar_idxs T =
      let
        val inxSs = typ_tvars T;
        val nms' = variantlist (map (#1 o #1) inxSs, []);
        val tye = map2 (fn ((v, S), a) => (v, TVar ((a, 0), S))) (inxSs, nms');
      in
        typ_subst_TVars tye T
      end;

    (*read and check the type mentioned in a const declaration; zero type var
      indices because type inference requires it*)
    fun read_const tsig syn (c, s) =
      (c, zero_tvar_idxs (varifyT (rd_typ tsig syn (K None) s)))
        handle ERROR => error ("in declaration of constant " ^ quote c);

    fun read_abbr tsig syn (c, vs, rhs_src) =
      (c, (map (rpair 0) vs, varifyT (rd_typ tsig syn (K None) rhs_src)
        handle ERROR => error ("in type abbreviation " ^ quote c)));


    val Sg {tsig, const_tab, syn, stamps} = sg;
    val xconsts = map #1 classes @ flat (map #1 types) @ map #1 abbrs @
      flat (map #1 consts);
    val sext = if_none opt_sext Syntax.empty_sext;

    val tsig' = extend_tsig tsig (classes, default, types, arities);
    val tsig1 = ext_tsig_abbrs tsig' (map (read_abbr tsig' syn) abbrs);

    val syn1 = Syntax.extend syn (rd_typ tsig1 syn (K None))
      (logical_types tsig1, xconsts, sext);

    val all_consts = flat (map (fn (cs, s) => map (rpair s) cs)
      (Syntax.constants sext @ consts));

    val const_tab1 =                              (* FIXME bug: vvvv should be syn *)
      Symtab.extend (K false) (const_tab, map (read_const tsig1 syn1) all_consts)
        handle Symtab.DUPLICATE c
          => error ("Constant " ^ quote c ^ " declared twice");

    val stamps1 =
      if exists (equal name o !) stamps then
        error ("Theory already contains a " ^ quote name ^ " component")
      else stamps @ [ref name];
  in
    Sg {tsig = tsig1, const_tab = const_tab1, syn = syn1, stamps = stamps1}
  end;



(** merge signatures **)

(*errors are indicated by exception TERM*)

fun check_stamps stamps =
  (case duplicates (map ! stamps) of
    [] => stamps
  | dups => raise_term ("Attempt to merge different versions of theories " ^
      commas (map quote dups)) []);

fun merge (sg1, sg2) =
  if subsig (sg2, sg1) then sg1
  else if subsig (sg1, sg2) then sg2
  else
    (*neither is union already; must form union*)
    let
      val Sg {tsig = tsig1, const_tab = const_tab1, syn = syn1,
        stamps = stamps1} = sg1;
      val Sg {tsig = tsig2, const_tab = const_tab2, syn = syn2,
        stamps = stamps2} = sg2;

      val tsig = merge_tsigs (tsig1, tsig2);

      val const_tab = Symtab.merge (op =) (const_tab1, const_tab2)
        handle Symtab.DUPLICATE c =>
          raise_term ("Incompatible types for constant " ^ quote c) [];

      val syn = Syntax.merge (logical_types tsig) syn1 syn2;

      val stamps = check_stamps (merge_lists stamps1 stamps2);
    in
      Sg {tsig = tsig, const_tab = const_tab, syn = syn, stamps = stamps}
    end;



(** the Pure signature **)

val sg0 = Sg {tsig = tsig0, const_tab = Symtab.null,
  syn = Syntax.type_syn, stamps = []};

val pure = extend sg0 "Pure"
  ([("logic", [])],
   ["logic"],
   [(["fun"], 2),
    (["prop"], 0),
    (Syntax.syntax_types, 0)],
   [],
   [(["fun"],  ([["logic"], ["logic"]], "logic")),
    (["prop"], ([], "logic"))],
   ([Syntax.constrainC], "'a::{} => 'a") :: Syntax.syntax_consts,
   Some Syntax.pure_sext);


end;

