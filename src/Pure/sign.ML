(*  Title:      Pure/sign.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

The abstract types "sg" (signatures) and "cterm" / "ctyp" (certified terms /
typs under a signature).
*)

signature SIGN =
sig
  structure Type: TYPE
  structure Symtab: SYMTAB
  structure Syntax: SYNTAX
  sharing Symtab = Type.Symtab
  type sg
  type cterm
  type ctyp
  val cfun: (term -> term) -> (cterm -> cterm)
  val cterm_of: sg -> term -> cterm
  val ctyp_of: sg -> typ -> ctyp
  val extend: sg -> string ->
        (class * class list) list * class list *
        (string list * int) list *
        (string list * (sort list * class)) list *
        (string list * string)list * Syntax.sext option -> sg
  val merge: sg * sg -> sg
  val pure: sg
  val read_cterm: sg -> string * typ -> cterm
  val read_ctyp: sg -> string -> ctyp
  val read_insts: sg -> (indexname -> typ option) * (indexname -> sort option)
                  -> (indexname -> typ option) * (indexname -> sort option)
                  -> (string*string)list
                  -> (indexname*ctyp)list * (cterm*cterm)list
  val read_typ: sg * (indexname -> sort option) -> string -> typ
  val rep_cterm: cterm -> {T: typ, t: term, sign: sg, maxidx: int}
  val rep_ctyp: ctyp -> {T: typ, sign: sg}
  val rep_sg: sg -> {tsig: Type.type_sig,
                     const_tab: typ Symtab.table,
                     syn: Syntax.syntax,
                     stamps: string ref list}
  val string_of_cterm: cterm -> string
  val string_of_ctyp: ctyp -> string
  val pprint_cterm: cterm -> pprint_args -> unit
  val pprint_ctyp: ctyp -> pprint_args -> unit
  val string_of_term: sg -> term -> string
  val string_of_typ: sg -> typ -> string
  val pprint_term: sg -> term -> pprint_args -> unit
  val pprint_typ: sg -> typ -> pprint_args -> unit
  val term_of: cterm -> term
  val typ_of: ctyp -> typ
  val pretty_term: sg -> term -> Syntax.Pretty.T
end;

functor SignFun(structure Type: TYPE and Syntax: SYNTAX): SIGN =
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

fun string_of_typ(Sg{tsig,syn,...}) = Syntax.string_of_typ syn;

fun pprint_typ(Sg{syn,...}) = Pretty.pprint o Pretty.quote o (Syntax.pretty_typ syn);

(*Is constant present in table with more generic type?*)
fun valid_const tsig ctab (a,T) = case Symtab.lookup(ctab, a) of
        Some U => Type.typ_instance(tsig,T,U) | _ => false;


(*Check a term for errors.  Are all constants and types valid in signature?
  Does not check that term is well-typed!*)
fun term_errors (sign as Sg{tsig,const_tab,...}) =
let val showtyp = string_of_typ sign;
    fun terrs (Const (a,T), errs) =
        if valid_const tsig const_tab (a,T)
        then Type.type_errors (tsig,showtyp) (T,errs)
        else ("Illegal type for constant: " ^ a ^ ": " ^ showtyp T) :: errs
      | terrs (Free (_,T), errs) = Type.type_errors (tsig,showtyp) (T,errs)
      | terrs (Var  ((a,i),T), errs) =
        if  i>=0  then  Type.type_errors (tsig,showtyp) (T,errs)
        else  ("Negative index for Var: " ^ a) :: errs
      | terrs (Bound _, errs) = errs (*loose bvars detected by type_of*)
      | terrs (Abs (_,T,t), errs) =
            Type.type_errors(tsig,showtyp)(T,terrs(t,errs))
      | terrs (f$t, errs) = terrs(f, terrs (t,errs))
in  terrs  end;



(** The Extend operation **)

(* Extend a signature: may add classes, types and constants. The "ref" in
   stamps ensures that no two signatures are identical -- it is impossible to
   forge a signature. *)

fun extend (Sg {tsig, const_tab, syn, stamps}) name
  (classes, default, types, arities, const_decs, opt_sext) =
  let
    fun err_in_typ s = error ("The error(s) above occurred in type " ^ quote s);

    fun read_typ tsg sy s =
      Syntax.read_typ sy (K (Type.defaultS tsg)) s handle ERROR => err_in_typ s;

    fun check_typ tsg sy ty =
      (case Type.type_errors (tsg, Syntax.string_of_typ sy) (ty, []) of
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
        (case Type.type_errors (tsg, Syntax.string_of_typ sy) (ty, []) of
          [] => (cs, ty)
        | errs => error (cat_lines (("Error in type of constants " ^
            space_implode " " (map quote cs)) :: errs)))
      end;


    (* FIXME abbr *)
    val tsig' = Type.extend (tsig, classes, default, types, arities);

    (* FIXME *)
    fun expand_typ _ ty = ty;

    val read_ty =
      (expand_typ tsig') o (check_typ tsig' syn) o (read_typ tsig' syn);
    val log_types = Type.logical_types tsig';
    val xconsts = map #1 classes @ flat (map #1 types) @ flat (map #1 const_decs);
    val sext = case opt_sext of Some sx => sx | None => Syntax.empty_sext;

    val syn' = Syntax.extend syn read_ty (log_types, xconsts, sext);

    val const_decs' =
      map (read_consts tsig' syn') (Syntax.constants sext @ const_decs);
  in
    Sg {
      tsig = tsig',
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



(**** CERTIFIED TYPES ****)


(*Certified typs under a signature*)
datatype ctyp = Ctyp of {sign: sg,  T: typ};

fun rep_ctyp(Ctyp ctyp) = ctyp;

fun typ_of (Ctyp{sign,T}) = T;

fun ctyp_of (sign as Sg{tsig,...}) T =
        case Type.type_errors (tsig,string_of_typ sign) (T,[]) of
          [] => Ctyp{sign= sign,T= T}
        | errs =>  error (cat_lines ("Error in type:" :: errs));

(*The only use is a horrible hack in the simplifier!*)
fun read_typ(Sg{tsig,syn,...}, defS) s =
    let val term = Syntax.read syn Syntax.typeT s;
        val S0 = Type.defaultS tsig;
        fun defS0 s = case defS s of Some S => S | None => S0;
    in Syntax.typ_of_term defS0 term end;

fun read_ctyp sign = ctyp_of sign o read_typ(sign, K None);

fun string_of_ctyp (Ctyp{sign,T}) = string_of_typ sign T;

fun pprint_ctyp (Ctyp{sign,T}) = pprint_typ sign T;


(**** CERTIFIED TERMS ****)

(*Certified terms under a signature, with checked typ and maxidx of Vars*)
datatype cterm = Cterm of {sign: sg,  t: term,  T: typ,  maxidx: int};

fun rep_cterm (Cterm args) = args;

(*Return the underlying term*)
fun term_of (Cterm{sign,t,T,maxidx}) = t;

(** pretty printing of terms **)

fun pretty_term (Sg{tsig,syn,...}) = Syntax.pretty_term syn;

fun string_of_term sign t = Pretty.string_of (pretty_term sign t);

fun pprint_term sign = Pretty.pprint o Pretty.quote o (pretty_term sign);

fun string_of_cterm (Cterm{sign,t,...}) = string_of_term sign t;

fun pprint_cterm (Cterm{sign,t,...}) = pprint_term sign t;

(*Create a cterm by checking a "raw" term with respect to a signature*)
fun cterm_of sign t =
  case  term_errors sign (t,[])  of
      [] => Cterm{sign=sign, t=t, T= type_of t, maxidx= maxidx_of_term t}
    | errs => raise TERM(cat_lines("Term not in signature"::errs), [t]);

fun cfun f = fn Cterm{sign,t,...} => cterm_of sign (f t);

(*Lexing, parsing, polymorphic typechecking of a term.*)
fun read_def_cterm (sign as Sg{tsig, const_tab, syn,...}, types, sorts)
                   (a,T) =
  let val showtyp = string_of_typ sign
      and showterm = string_of_term sign
      fun termerr [] = ""
        | termerr [t] = "\nInvolving this term:\n" ^ showterm t ^ "\n"
        | termerr ts = "\nInvolving these terms:\n" ^
                       cat_lines (map showterm ts)
      val t = Syntax.read syn T a;
      val (t',tye) = Type.infer_types (tsig, const_tab, types,
                                       sorts, showtyp, T, t)
                  handle TYPE (msg, Ts, ts) =>
          error ("Type checking error: " ^ msg ^ "\n" ^
                  cat_lines (map showtyp Ts) ^ termerr ts)
  in (cterm_of sign t', tye)
  end
  handle TERM (msg, _) => error ("Error: " ^  msg);


fun read_cterm sign = #1 o (read_def_cterm (sign, K None, K None));

(** reading of instantiations **)

fun indexname cs = case Syntax.scan_varname cs of (v,[]) => v
        | _ => error("Lexical error in variable name " ^ quote (implode cs));

fun absent ixn =
  error("No such variable in term: " ^ Syntax.string_of_vname ixn);

fun inst_failure ixn =
  error("Instantiation of " ^ Syntax.string_of_vname ixn ^ " fails");

fun read_insts (sign as Sg{tsig,...}) (rtypes,rsorts) (types,sorts) insts =
let fun split([],tvs,vs) = (tvs,vs)
      | split((sv,st)::l,tvs,vs) = (case explode sv of
                  "'"::cs => split(l,(indexname cs,st)::tvs,vs)
                | cs => split(l,tvs,(indexname cs,st)::vs));
    val (tvs,vs) = split(insts,[],[]);
    fun readT((a,i),st) =
        let val ixn = ("'" ^ a,i);
            val S = case rsorts ixn of Some S => S | None => absent ixn;
            val T = read_typ (sign,sorts) st;
        in if Type.typ_instance(tsig,T,TVar(ixn,S)) then (ixn,T)
           else inst_failure ixn
        end
    val tye = map readT tvs;
    fun add_cterm ((cts,tye), (ixn,st)) =
        let val T = case rtypes ixn of
                      Some T => typ_subst_TVars tye T
                    | None => absent ixn;
            val (ct,tye2) = read_def_cterm (sign,types,sorts) (st,T);
            val cv = cterm_of sign (Var(ixn,typ_subst_TVars tye2 T))
        in ((cv,ct)::cts,tye2 @ tye) end
    val (cterms,tye') = foldl add_cterm (([],tye), vs);
in (map (fn (ixn,T) => (ixn,ctyp_of sign T)) tye', cterms) end;

end;

