(*  Title:      Pure/sign.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

The abstract types "sg" of signatures
*)

signature SIGN =
sig
  structure Type: TYPE
  structure Symtab: SYMTAB
  structure Syntax: SYNTAX
  sharing Symtab = Type.Symtab
  type sg
  val extend: sg -> string ->
        (class * class list) list * class list *
        (string list * int) list *
        (string * indexname list * string) list *
        (string list * (sort list * class)) list *
        (string list * string)list * Syntax.sext option -> sg
  val merge: sg * sg -> sg
  val pure: sg
  val read_typ: sg * (indexname -> sort option) -> string -> typ
  val rep_sg: sg -> {tsig: Type.type_sig,
                     const_tab: typ Symtab.table,
                     syn: Syntax.syntax,
                     stamps: string ref list}
  val string_of_term: sg -> term -> string
  val string_of_typ: sg -> typ -> string
  val subsig: sg * sg -> bool
  val pprint_term: sg -> term -> pprint_args -> unit
  val pprint_typ: sg -> typ -> pprint_args -> unit
  val pretty_term: sg -> term -> Syntax.Pretty.T
  val term_errors: sg -> term -> string list
end;

functor SignFun(structure Type: TYPE and Syntax: SYNTAX) : SIGN =
struct

structure Type = Type;
structure Symtab = Type.Symtab;
structure Syntax = Syntax;
structure Pretty = Syntax.Pretty


(* Signatures of theories. *)

datatype sg =
  Sg of {
    tsig: Type.type_sig,            (*order-sorted signature of types*)
    const_tab: typ Symtab.table,    (*types of constants*)
    syn: Syntax.syntax,             (*syntax for parsing and printing*)
    stamps: string ref list};       (*unique theory indentifier*)


fun rep_sg (Sg args) = args;

fun subsig(Sg{stamps=s1,...},Sg{stamps=s2,...}) = s1 subset s2;

fun string_of_typ(Sg{tsig,syn,...}) = Syntax.string_of_typ syn;

fun pprint_typ(Sg{syn,...}) = Pretty.pprint o Pretty.quote o (Syntax.pretty_typ syn);

(*Is constant present in table with more generic type?*)
fun valid_const tsig ctab (a,T) = case Symtab.lookup(ctab, a) of
        Some U => Type.typ_instance(tsig,T,U) | _ => false;


(*Check a term for errors.  Are all constants and types valid in signature?
  Does not check that term is well-typed!*)
fun term_errors (sign as Sg{tsig,const_tab,...}) =
  let val showtyp = string_of_typ sign
      fun terrs (Const (a,T), errs) =
	  if valid_const tsig const_tab (a,T)
	  then Type.type_errors tsig (T,errs)
	  else ("Illegal type for constant: " ^ a ^ ": " ^ showtyp T) :: errs
	| terrs (Free (_,T), errs) = Type.type_errors tsig (T,errs)
	| terrs (Var  ((a,i),T), errs) =
	  if  i>=0  then  Type.type_errors tsig (T,errs)
	  else  ("Negative index for Var: " ^ a) :: errs
	| terrs (Bound _, errs) = errs (*loose bvars detected by type_of*)
	| terrs (Abs (_,T,t), errs) =
	      Type.type_errors tsig (T,terrs(t,errs))
	| terrs (f$t, errs) = terrs(f, terrs (t,errs))
  in  fn t => terrs(t,[])  end;



(** The Extend operation **)

(* Extend a signature: may add classes, types and constants. The "ref" in
   stamps ensures that no two signatures are identical -- it is impossible to
   forge a signature. *)

fun extend (Sg {tsig, const_tab, syn, stamps}) name
  (classes, default, types, abbr, arities, const_decs, opt_sext) =
  let
    fun err_in_typ s = error ("The error(s) above occurred in type " ^ quote s);

    fun read_typ tsg sy s =
      Syntax.read_typ sy (K (Type.defaultS tsg)) s handle ERROR => err_in_typ s;

    fun check_typ tsg sy ty =
      (case Type.type_errors tsg (ty, []) of
        [] => ty
      | errs => (prs (cat_lines errs); err_in_typ (Syntax.string_of_typ sy ty)));

    (*reset TVar indices to zero, renaming to preserve distinctness*)
    fun zero_tvar_indices T =
      let
        val inxSs = typ_tvars T;
        val nms' = variantlist (map (#1 o #1) inxSs, []);
        val tye = map (fn ((v, S), a) => (v, TVar ((a, 0), S))) (inxSs ~~ nms');
      in typ_subst_TVars tye T end;

    (*read and check the type mentioned in a const declaration; zero type var
      indices because type inference requires it*)

    fun read_consts tsg sy (cs, s) =
      let val ty = zero_tvar_indices (Type.varifyT (read_typ tsg sy s));
      in
        (case Type.type_errors tsg (ty, []) of
          [] => (cs, ty)
        | errs => error (cat_lines (("Error in type of constants " ^
            space_implode " " (map quote cs)) :: errs)))
      end;

    val tsig' = Type.extend (tsig, classes, default, types, arities);

    fun read_typ_abbr(a,v,s)=
      let val T = Type.varifyT(read_typ tsig' syn s)
      in (a,(v,T)) end handle ERROR => error("This error occured in abbreviation "^ quote a);

    val abbr' = map read_typ_abbr abbr;
    val tsig'' = Type.add_abbrs(tsig',abbr');

    val read_ty =
      (Type.expand_typ tsig'') o (check_typ tsig'' syn) o (read_typ tsig'' syn);
    val log_types = Type.logical_types tsig'';
    val xconsts = map #1 classes @ flat (map #1 types) @ flat (map #1 const_decs);
    val sext = case opt_sext of Some sx => sx | None => Syntax.empty_sext;

    val syn' = Syntax.extend syn read_ty (log_types, xconsts, sext);

    val const_decs' =
      map (read_consts tsig'' syn') (Syntax.constants sext @ const_decs);
  in
    Sg {
      tsig = tsig'',
      const_tab = Symtab.st_of_declist (const_decs', const_tab)
        handle Symtab.DUPLICATE a => error ("Constant " ^ quote a ^ " declared twice"),
      syn = syn',
      stamps = ref name :: stamps}
  end;


(* The empty signature *)

val sg0 = Sg {tsig = Type.tsig0, const_tab = Symtab.null,
  syn = Syntax.type_syn, stamps = []};


(* The pure signature *)

val pure = extend sg0 "Pure"
([("logic", [])],
 ["logic"],
 [(["fun"], 2),
  (["prop"], 0),
  (Syntax.syntax_types, 0)],
 [],
 [(["fun"],  ([["logic"], ["logic"]], "logic")),
  (["prop"], ([], "logic"))],
 [([Syntax.constrainC], "'a::logic => 'a")],
 Some Syntax.pure_sext);



(** The Merge operation **)

(*Update table with (a,x) providing any existing asgt to "a" equals x. *)
fun update_eq ((a,x),tab) =
    case Symtab.lookup(tab,a) of
        None => Symtab.update((a,x), tab)
      | Some y => if x=y then tab
            else  raise TERM ("Incompatible types for constant: "^a, []);

(*Combine tables, updating tab2 by tab1 and checking.*)
fun merge_tabs (tab1,tab2) =
    Symtab.balance (foldr update_eq (Symtab.alist_of tab1, tab2));

(*Combine tables, overwriting tab2 with tab1.*)
fun smash_tabs (tab1,tab2) =
    Symtab.balance (foldr Symtab.update (Symtab.alist_of tab1, tab2));

(*Combine stamps, checking that theory names are disjoint. *)
fun merge_stamps (stamps1,stamps2) =
  let val stamps = stamps1 union stamps2 in
  case findrep (map ! stamps) of
     a::_ => error ("Attempt to merge different versions of theory: " ^ a)
   | [] => stamps
  end;

(*Merge two signatures.  Forms unions of tables.  Prefers sign1. *)
fun merge
  (sign1 as Sg {tsig = tsig1, const_tab = ctab1, stamps = stamps1, syn = syn1},
   sign2 as Sg {tsig = tsig2, const_tab = ctab2, stamps = stamps2, syn = syn2}) =
    if stamps2 subset stamps1 then sign1
    else if stamps1 subset stamps2 then sign2
    else (*neither is union already; must form union*)
      let val tsig = Type.merge (tsig1, tsig2);
      in
        Sg {tsig = tsig, const_tab = merge_tabs (ctab1, ctab2),
          stamps = merge_stamps (stamps1, stamps2),
          syn = Syntax.merge (Type.logical_types tsig) syn1 syn2}
      end;



fun read_typ(Sg{tsig,syn,...}, defS) s =
    let val term = Syntax.read syn Syntax.typeT s;
        val S0 = Type.defaultS tsig;
        fun defS0 s = case defS s of Some S => S | None => S0;
    in Syntax.typ_of_term defS0 term end;

(** pretty printing of terms **)

fun pretty_term (Sg{tsig,syn,...}) = Syntax.pretty_term syn;

fun string_of_term sign t = Pretty.string_of (pretty_term sign t);

fun pprint_term sign = Pretty.pprint o Pretty.quote o (pretty_term sign);

end;

