(*  Title:      Pure/sign.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Markus Wenzel

The abstract type "sg" of signatures.
*)

signature SIGN =
sig
  structure Symtab: SYMTAB
  structure Syntax: SYNTAX
  structure Type: TYPE
  sharing Symtab = Type.Symtab
  local open Type Syntax in
    type sg
    val rep_sg: sg ->
      {tsig: type_sig,
       const_tab: typ Symtab.table,
       syn: syntax,
       stamps: string ref list}
    val subsig: sg * sg -> bool
    val eq_sg: sg * sg -> bool
    val is_draft: sg -> bool
    val const_type: sg -> string -> typ option
    val classes: sg -> class list
    val subsort: sg -> sort * sort -> bool
    val norm_sort: sg -> sort -> sort
    val nonempty_sort: sg -> sort list -> sort -> bool
    val print_sg: sg -> unit
    val pretty_sg: sg -> Pretty.T
    val pprint_sg: sg -> pprint_args -> unit
    val pretty_term: sg -> term -> Pretty.T
    val pretty_typ: sg -> typ -> Pretty.T
    val pretty_sort: sort -> Pretty.T
    val string_of_term: sg -> term -> string
    val string_of_typ: sg -> typ -> string
    val pprint_term: sg -> term -> pprint_args -> unit
    val pprint_typ: sg -> typ -> pprint_args -> unit
    val certify_typ: sg -> typ -> typ
    val certify_term: sg -> term -> term * typ * int
    val read_typ: sg * (indexname -> sort option) -> string -> typ
    val infer_types: sg -> (indexname -> typ option) ->
      (indexname -> sort option) -> string list -> bool
      -> term list * typ -> int * term * (indexname * typ) list
    val add_classes: (class * class list) list -> sg -> sg
    val add_classrel: (class * class) list -> sg -> sg
    val add_defsort: sort -> sg -> sg
    val add_types: (string * int * mixfix) list -> sg -> sg
    val add_tyabbrs: (string * string list * string * mixfix) list -> sg -> sg
    val add_tyabbrs_i: (string * string list * typ * mixfix) list -> sg -> sg
    val add_arities: (string * sort list * sort) list -> sg -> sg
    val add_consts: (string * string * mixfix) list -> sg -> sg
    val add_consts_i: (string * typ * mixfix) list -> sg -> sg
    val add_syntax: (string * string * mixfix) list -> sg -> sg
    val add_syntax_i: (string * typ * mixfix) list -> sg -> sg
    val add_trfuns:
      (string * (ast list -> ast)) list *
      (string * (term list -> term)) list *
      (string * (term list -> term)) list *
      (string * (ast list -> ast)) list -> sg -> sg
    val add_trrules: (string * string) trrule list -> sg -> sg
    val add_trrules_i: ast trrule list -> sg -> sg
    val add_name: string -> sg -> sg
    val make_draft: sg -> sg
    val merge: sg * sg -> sg
    val proto_pure: sg
    val pure: sg
    val cpure: sg
    val const_of_class: class -> string
    val class_of_const: string -> class
  end
end;

functor SignFun(structure Syntax: SYNTAX and Type: TYPE): SIGN =
struct

structure Symtab = Type.Symtab;
structure Syntax = Syntax;
structure BasicSyntax: BASIC_SYNTAX = Syntax;
structure Pretty = Syntax.Pretty;
structure Type = Type;
open BasicSyntax Type;


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
val tsig_of = #tsig o rep_sg;


(* stamps *)

fun is_draft (Sg {stamps = ref "#" :: _, ...}) = true
  | is_draft _ = false;

fun subsig (Sg {stamps = s1, ...}, Sg {stamps = s2, ...}) = s1 subset s2;

fun eq_sg (Sg {stamps = s1, ...}, Sg {stamps = s2, ...}) = eq_set (s1, s2);


(* consts *)

fun const_type (Sg {const_tab, ...}) c =
  Symtab.lookup (const_tab, c);


(* classes and sorts *)

val classes = #classes o Type.rep_tsig o tsig_of;

val subsort = Type.subsort o tsig_of;
val norm_sort = Type.norm_sort o tsig_of;
val nonempty_sort = Type.nonempty_sort o tsig_of;

fun pretty_sort [c] = Pretty.str c
  | pretty_sort cs = Pretty.str_list "{" "}" cs;



(** print signature **)

val stamp_names = rev o map !;

fun print_sg sg =
  let
    fun prt_typ syn ty = Pretty.quote (Syntax.pretty_typ syn ty);

    fun pretty_subclass (cl, cls) = Pretty.block
      (Pretty.str (cl ^ " <") :: Pretty.brk 1 ::
        Pretty.commas (map Pretty.str cls));

    fun pretty_default cls = Pretty.block
      [Pretty.str "default:", Pretty.brk 1, pretty_sort cls];

    fun pretty_ty (ty, n) = Pretty.str (ty ^ " " ^ string_of_int n);

    fun pretty_abbr syn (ty, (vs, rhs)) = Pretty.block
      [prt_typ syn (Type (ty, map (fn v => TVar ((v, 0), [])) vs)),
        Pretty.str " =", Pretty.brk 1, prt_typ syn rhs];

    fun pretty_arity ty (cl, []) = Pretty.block
          [Pretty.str (ty ^ " ::"), Pretty.brk 1, Pretty.str cl]
      | pretty_arity ty (cl, srts) = Pretty.block
          [Pretty.str (ty ^ " ::"), Pretty.brk 1,
            Pretty.list "(" ")" (map pretty_sort srts),
            Pretty.brk 1, Pretty.str cl];

    fun pretty_arities (ty, ars) = map (pretty_arity ty) ars;

    fun pretty_const syn (c, ty) = Pretty.block
      [Pretty.str (quote c ^ " ::"), Pretty.brk 1, prt_typ syn ty];


    val Sg {tsig, const_tab, syn, stamps} = sg;
    val {classes, subclass, default, tycons, abbrs, arities} = rep_tsig tsig;
  in
    Pretty.writeln (Pretty.strs ("stamps:" :: stamp_names stamps));
    Pretty.writeln (Pretty.strs ("classes:" :: classes));
    Pretty.writeln (Pretty.big_list "subclass:"
                      (map pretty_subclass subclass));
    Pretty.writeln (pretty_default default);
    Pretty.writeln (Pretty.big_list "types:" (map pretty_ty tycons));
    Pretty.writeln (Pretty.big_list "abbrs:" (map (pretty_abbr syn) abbrs));
    Pretty.writeln (Pretty.big_list "arities:"
                      (flat (map pretty_arities arities)));
    Pretty.writeln (Pretty.big_list "consts:"
                      (map (pretty_const syn) (Symtab.dest const_tab)))
  end;


fun pretty_sg (Sg {stamps, ...}) =
  Pretty.str_list "{" "}" (stamp_names stamps);

val pprint_sg = Pretty.pprint o pretty_sg;



(** pretty printing of terms and types **)

fun pretty_term (Sg {syn, stamps, ...}) =
  let val curried = "CPure" mem (map ! stamps);
  in Syntax.pretty_term curried syn end;

fun pretty_typ (Sg {syn, ...}) = Syntax.pretty_typ syn;

fun string_of_term (Sg {syn, stamps, ...}) =
  let val curried = "CPure" mem (map ! stamps);
  in Syntax.string_of_term curried syn end;

fun string_of_typ (Sg {syn, ...}) = Syntax.string_of_typ syn;

fun pprint_term sg = Pretty.pprint o Pretty.quote o (pretty_term sg);
fun pprint_typ sg = Pretty.pprint o Pretty.quote o (pretty_typ sg);



(** read types **)  (*exception ERROR*)

fun err_in_type s =
  error ("The error(s) above occurred in type " ^ quote s);

fun read_raw_typ syn tsig sort_of str =
  Syntax.read_typ syn (fn x => if_none (sort_of x) (defaultS tsig)) str
    handle ERROR => err_in_type str;

(*read and certify typ wrt a signature*)
fun read_typ (Sg {tsig, syn, ...}, sort_of) str =
  cert_typ tsig (read_raw_typ syn tsig sort_of str)
    handle TYPE (msg, _, _) => (writeln msg; err_in_type str);



(** certify types and terms **)   (*exception TYPE*)

fun certify_typ (Sg {tsig, ...}) ty = cert_typ tsig ty;


fun mapfilt_atoms f (Abs (_, _, t)) = mapfilt_atoms f t
  | mapfilt_atoms f (t $ u) = mapfilt_atoms f t @ mapfilt_atoms f u
  | mapfilt_atoms f a = (case f a of Some y => [y] | None => []);

fun certify_term (sg as Sg {tsig, ...}) tm =
  let
    fun valid_const a T =
      (case const_type sg a of
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
    (case mapfilt_atoms atom_err norm_tm of
      [] => (norm_tm, type_of norm_tm, maxidx_of_term norm_tm)
    | errs => raise_type (cat_lines errs) [] [norm_tm])
  end;



(** infer_types **)         (*exception ERROR*)

fun infer_types sg types sorts used freeze (ts, T) =
  let
    val Sg {tsig, ...} = sg;
    val show_typ = string_of_typ sg;
    val show_term = string_of_term sg;

    fun term_err [] = ""
      | term_err [t] = "\nInvolving this term:\n" ^ show_term t
      | term_err ts =
          "\nInvolving these terms:\n" ^ cat_lines (map show_term ts);

    fun exn_type_msg (msg, Ts, ts) =
	"\nType checking error: " ^ msg ^ "\n" ^
	cat_lines (map show_typ Ts) ^ term_err ts ^ "\n";

    val T' = certify_typ sg T
             handle TYPE arg => error (exn_type_msg arg);

    val ct = const_type sg;

    fun warn() =
      if length ts > 1 andalso length ts <= !Syntax.ambiguity_level
      then (*no warning shown yet*)
           writeln "Warning: Currently parsed input \
                   \produces more than one parse tree.\n\
                   \For more information lower Syntax.ambiguity_level."
      else ();

    datatype result = One of int * term * (indexname * typ) list
                    | Errs of (string * typ list * term list)list
                    | Ambigs of term list;

    fun process_term(res,(t,i)) =
       let val (u,tye) = Type.infer_types(tsig,ct,types,sorts,used,freeze,T',t)
       in case res of
            One(_,t0,_) => Ambigs([u,t0])
          | Errs _ => One(i,u,tye)
          | Ambigs(us) => Ambigs(u::us)
       end
       handle TYPE arg => (case res of Errs(errs) => Errs(arg::errs)
                                     | _ => res);

  in case foldl process_term (Errs[], ts ~~ (0 upto (length ts - 1))) of
       One(res) =>
         (if length ts > !Syntax.ambiguity_level
          then writeln "Fortunately, only one parse tree is type correct.\n\
            \It helps (speed!) if you disambiguate your grammar or your input."
          else ();
          res)
     | Errs(errs) => (warn(); error(cat_lines(map exn_type_msg errs)))
     | Ambigs(us) =>
         (warn();
          let val old_show_brackets = !show_brackets
              val dummy = show_brackets := true;
              val errs = cat_lines(map show_term us)
          in show_brackets := old_show_brackets;
             error("Error: More than one term is type correct:\n" ^ errs)
          end)
  end;


(** extend signature **)    (*exception ERROR*)

(** signature extension functions **)  (*exception ERROR*)

fun decls_of name_of mfixs =
  map (fn (x, y, mx) => (name_of x mx, y)) mfixs;


(* add default sort *)

fun ext_defsort (syn, tsig, ctab) defsort =
  (syn, ext_tsig_defsort tsig defsort, ctab);


(* add type constructors *)

fun ext_types (syn, tsig, ctab) types =
  (Syntax.extend_type_gram syn types,
    ext_tsig_types tsig (decls_of Syntax.type_name types),
    ctab);


(* add type abbreviations *)

fun read_abbr syn tsig (t, vs, rhs_src) =
  (t, vs, read_raw_typ syn tsig (K None) rhs_src)
    handle ERROR => error ("in type abbreviation " ^ t);

fun ext_abbrs rd_abbr (syn, tsig, ctab) abbrs =
  let
    fun mfix_of (t, vs, _, mx) = (t, length vs, mx);
    val syn1 = Syntax.extend_type_gram syn (map mfix_of abbrs);

    fun decl_of (t, vs, rhs, mx) =
      rd_abbr syn1 tsig (Syntax.type_name t mx, vs, rhs);
  in
    (syn1, ext_tsig_abbrs tsig (map decl_of abbrs), ctab)
  end;

val ext_tyabbrs_i = ext_abbrs (K (K I));
val ext_tyabbrs = ext_abbrs read_abbr;


(* add type arities *)

fun ext_arities (syn, tsig, ctab) arities =
  let
    val tsig1 = ext_tsig_arities tsig arities;
    val log_types = logical_types tsig1;
  in
    (Syntax.extend_log_types syn log_types, tsig1, ctab)
  end;


(* add term constants and syntax *)

fun err_in_const c =
  error ("in declaration of constant " ^ quote c);

fun err_dup_consts cs =
  error ("Duplicate declaration of constant(s) " ^ commas_quote cs);


fun read_const syn tsig (c, ty_src, mx) =
  (c, read_raw_typ syn tsig (K None) ty_src, mx)
    handle ERROR => err_in_const (Syntax.const_name c mx);

fun ext_cnsts rd_const syn_only (syn, tsig, ctab) raw_consts =
  let
    fun prep_const (c, ty, mx) = (c, varifyT (cert_typ tsig (no_tvars ty)), mx)
      handle TYPE (msg, _, _) => (writeln msg; err_in_const (Syntax.const_name c mx));

    val consts = map (prep_const o rd_const syn tsig) raw_consts;
    val decls =
      if syn_only then []
      else filter_out (equal "" o fst) (decls_of Syntax.const_name consts);
  in
    (Syntax.extend_const_gram syn consts, tsig,
      Symtab.extend_new (ctab, decls)
        handle Symtab.DUPS cs => err_dup_consts cs)
  end;

val ext_consts_i = ext_cnsts (K (K I)) false;
val ext_consts = ext_cnsts read_const false;
val ext_syntax_i = ext_cnsts (K (K I)) true;
val ext_syntax = ext_cnsts read_const true;


(* add type classes *)

fun const_of_class c = c ^ "_class";

fun class_of_const c_class =
  let
    val c = implode (take (size c_class - 6, explode c_class));
  in
    if const_of_class c = c_class then c
    else raise_term ("class_of_const: bad name " ^ quote c_class) []
  end;


fun ext_classes (syn, tsig, ctab) classes =
  let
    val names = map fst classes;
    val consts =
      map (fn c => (const_of_class c, a_itselfT --> propT, NoSyn)) names;
  in
    ext_consts_i
      (Syntax.extend_consts syn names, ext_tsig_classes tsig classes, ctab)
      consts
  end;


(* add to subclass relation *)

fun ext_classrel (syn, tsig, ctab) pairs =
  (syn, ext_tsig_subclass tsig pairs, ctab);


(* add to syntax *)

fun ext_syn extfun (syn, tsig, ctab) args =
  (extfun syn args, tsig, ctab);


(* build signature *)

fun ext_stamps stamps name =
  let
    val stmps = (case stamps of ref "#" :: ss => ss | ss => ss);
  in
    if exists (equal name o !) stmps then
      error ("Theory already contains a " ^ quote name ^ " component")
    else ref name :: stmps
  end;

fun make_sign (syn, tsig, ctab) stamps name =
  Sg {tsig = tsig, const_tab = ctab, syn = syn,
    stamps = ext_stamps stamps name};

fun extend_sign extfun name decls (Sg {tsig, const_tab, syn, stamps}) =
  make_sign (extfun (syn, tsig, const_tab) decls) stamps name;


(* the external interfaces *)

val add_classes   = extend_sign ext_classes "#";
val add_classrel  = extend_sign ext_classrel "#";
val add_defsort   = extend_sign ext_defsort "#";
val add_types     = extend_sign ext_types "#";
val add_tyabbrs   = extend_sign ext_tyabbrs "#";
val add_tyabbrs_i = extend_sign ext_tyabbrs_i "#";
val add_arities   = extend_sign ext_arities "#";
val add_consts    = extend_sign ext_consts "#";
val add_consts_i  = extend_sign ext_consts_i "#";
val add_syntax    = extend_sign ext_syntax "#";
val add_syntax_i  = extend_sign ext_syntax_i "#";
val add_trfuns    = extend_sign (ext_syn Syntax.extend_trfuns) "#";
val add_trrules   = extend_sign (ext_syn Syntax.extend_trrules) "#";
val add_trrules_i = extend_sign (ext_syn Syntax.extend_trrules_i) "#";

fun add_name name sg = extend_sign K name () sg;
val make_draft = add_name "#";



(** merge signatures **)    (*exception TERM*) (*exception ERROR (* FIXME *)*)

fun merge (sg1, sg2) =
  if subsig (sg2, sg1) then sg1
  else if subsig (sg1, sg2) then sg2
  else if is_draft sg1 orelse is_draft sg2 then
    raise_term "Illegal merge of draft signatures" []
  else
    (*neither is union already; must form union*)
    let
      val Sg {tsig = tsig1, const_tab = const_tab1, syn = syn1,
        stamps = stamps1} = sg1;
      val Sg {tsig = tsig2, const_tab = const_tab2, syn = syn2,
        stamps = stamps2} = sg2;


      val stamps = merge_rev_lists stamps1 stamps2;
      val _ =
        (case duplicates (stamp_names stamps) of
          [] => ()
        | dups => raise_term ("Attempt to merge different versions of theories "
            ^ commas_quote dups) []);

      val tsig = merge_tsigs (tsig1, tsig2);

      val const_tab = Symtab.merge (op =) (const_tab1, const_tab2)
        handle Symtab.DUPS cs =>
          raise_term ("Incompatible types for constant(s) " ^ commas_quote cs) [];

      val syn = Syntax.merge_syntaxes syn1 syn2;
    in
      Sg {tsig = tsig, const_tab = const_tab, syn = syn, stamps = stamps}
    end;



(** the Pure signature **)

val proto_pure =
  make_sign (Syntax.pure_syn, tsig0, Symtab.null) [] "#"
  |> add_types
   (("fun", 2, NoSyn) ::
    ("prop", 0, NoSyn) ::
    ("itself", 1, NoSyn) ::
    Syntax.pure_types)
  |> add_classes [(logicC, [])]
  |> add_defsort logicS
  |> add_arities
   [("fun", [logicS, logicS], logicS),
    ("prop", [], logicS),
    ("itself", [logicS], logicS)]
  |> add_syntax Syntax.pure_syntax
  |> add_trfuns Syntax.pure_trfuns
  |> add_consts
   [("==", "['a::{}, 'a] => prop", Mixfix ("(_ ==/ _)", [3, 2], 2)),
    ("=?=", "['a::{}, 'a] => prop", Mixfix ("(_ =?=/ _)", [3, 2], 2)),
    ("==>", "[prop, prop] => prop", Mixfix ("(_ ==>/ _)", [2, 1], 1)),
    ("all", "('a => prop) => prop", Binder ("!!", 0, 0)),
    ("TYPE", "'a itself", NoSyn)]
  |> add_name "ProtoPure";

val pure = proto_pure
  |> add_syntax Syntax.pure_appl_syntax
  |> add_name "Pure";

val cpure = proto_pure
  |> add_syntax Syntax.pure_applC_syntax
  |> add_name "CPure";

end;
