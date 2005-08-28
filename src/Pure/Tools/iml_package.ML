signature IML_PACKAGE =
sig
end;

structure ImlPackage : IML_PACKAGE =
struct

type nsidf = string
type idf = string
type qidf = nsidf * idf
type iclass = qidf
type isort = iclass list
type ityco = qidf
type iconst = qidf
type 'a vidf = string * 'a
type tvname = isort vidf

fun qidf_ord ((a, c), (b, d)) =
  (case string_ord (a, b) of EQUAL => string_ord (c, d) | ord => ord);

structure Idfgraph = GraphFun(type key = qidf val ord = qidf_ord);

datatype ityp =
  IType of ityco * ityp list
  | IFree of tvname * isort

type vname = ityp vidf

datatype iexpr =
  IConst of iconst * ityp
  | IVar of vname * ityp
  | IAbs of vname * iexpr
  | IApp of iexpr * iexpr

datatype pat =
  PConst of iconst
  | PVar of vname

type 'a defn = 'a * (pat list * iexpr) list

datatype stmt =
  Def of ityp defn
  | Typdecl of vname list * ityp
  | Datadef of (iconst * vname list) list
  | Classdecl of string list * (string * ityp) list
  | Instdef of iclass * ityco * isort list * (string defn) list

type module = stmt Idfgraph.T

type universe = module Graph.T

fun isort_of_sort nsp sort =
  map (pair nsp) sort

(* fun ityp_of_typ nsp ty =
 *   let
 *     fun ityp_of_typ' (Type (tycon, tys)) = IType ((nsp, tycon), map ityp_of_typ' tys)
 *       | ityp_of_typ' (TFree (varname, sort)) = IFree ((nsp, varname), isort_of_sort nsp sort)
 *   in (ityp_of_typ' o unvarifyT) ty end;
 *)

(* fun iexpr_of_term nsp t =
 *   let
 *     fun iexpr_of_term' (Const (const, ty)) = IConst ((nsp, const), ityp_of_typ nsp ty)
 *       | iexpr_of_term' (Free (varname, ty)) = IVar ((nsp, varname), ityp_of_typ nsp ty)
 *       | iexpr_of_term' (Free (varname, ty)) = IVar ((nsp, varname), ityp_of_typ nsp ty)
 *   in (iexpr_of_term' o map_term_types (unvarifyT)) t
 * 
 *   datatype term =
 *     Const of string * typ |
 *     Free of string * typ |
 *     Var of indexname * typ |
 *     Bound of int |
 *     Abs of string * typ * term |
 *     op $ of term * term
 * 
 * 
 * fun iexpr_of
 *)

val empty_universe = Graph.empty

val empty_module = Idfgraph.empty

datatype deps =
  Check
  | Nocheck
  | Dep of qidf list

fun add_stmt modname idf deps stmt univ =
  let
    fun check_deps Nocheck = I
      | check_deps (Dep idfs) = Graph.add_deps_acyclic (modname, map #2 idfs)
      | check_deps _ = error "'Nocheck' not implemented yet"
  in
    univ
    |> Graph.default_node modname empty_module
    |> Graph.map_node modname (Idfgraph.new_node (idf, stmt))
    |> fold check_deps deps
  end

(* WICHTIG: resolve_qidf, resolve_midf  *)

(* IDEAS: Transaktionspuffer, Errormessage-Stack *)

end;

