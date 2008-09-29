(*  Title:      Pure/ProofGeneral/pgip_types.ML
    ID:         $Id$
    Author:     David Aspinall

PGIP abstraction: types and conversions.
*)

(* TODO: PGML, proverflag *)
signature PGIPTYPES =
sig
    (* Object types: the types of values which can be manipulated externally.
       Ideally a list of other types would be configured as a parameter. *)
    datatype objtype = ObjFile | ObjTheory | ObjTheorem | ObjComment  
                     | ObjTerm | ObjType | ObjOther of string
  
    (* Names for values of objtypes (i.e. prover identifiers). Could be a parameter.
       Names for ObjFiles are URIs. *)
    type objname = string

    type idtable = { context: objname option,    (* container's objname *)
                     objtype: objtype, 
                     ids: objname list }

    (* Types and values (used for preferences and dialogs) *)

    datatype pgiptype = Pgipnull | Pgipbool | Pgipint of int option * int option | Pgipnat
                      | Pgipstring | Pgipconst of string | Pgipchoice of pgipdtype list

    and pgipdtype = Pgipdtype of string option * pgiptype  (* type with opt. description *)

    type pgipval   (* typed value *)

    (* URLs we can cope with *)
    type pgipurl

    (* Representation error in reading/writing PGIP *)
    exception PGIP of string

    (* Interface areas for message output *)
    datatype displayarea = Status | Message | Display | Tracing | Internal | Other of string

    (* Error levels *)
    datatype fatality = Info | Warning | Nonfatal | Fatal | Panic | Log | Debug

    (* File location *)
    type location = { descr: string option,
                      url: pgipurl option,
                      line: int option,
                      column: int option,
                      char: int option,
                      length: int option }

    (* Prover preference *)   
    type preference = { name: string,
                        descr: string option,
                        default: string option,
                        pgiptype: pgiptype }
end

signature PGIPTYPES_OPNS = 
sig
    include PGIPTYPES
 
    (* Object types *)
    val name_of_objtype  : objtype -> string
    val attrs_of_objtype : objtype -> XML.attributes
    val objtype_of_attrs : XML.attributes -> objtype                    (* raises PGIP *)
    val idtable_to_xml   : idtable -> XML.tree

    (* Values as XML strings *)
    val read_pgipint       : (int option * int option) -> string -> int (* raises PGIP *)
    val read_pgipnat       : string -> int                              (* raises PGIP *)
    val read_pgipbool      : string -> bool                             (* raises PGIP *)
    val read_pgipstring    : string -> string                           (* raises PGIP *)
    val int_to_pgstring    : int -> string
    val bool_to_pgstring   : bool -> string
    val string_to_pgstring : string -> string

    (* PGIP datatypes *)
    val pgiptype_to_xml   : pgiptype -> XML.tree
    val read_pgval        : pgiptype -> string -> pgipval              (* raises PGIP *)
    val pgval_to_string   : pgipval -> string

    val attrs_of_displayarea : displayarea -> XML.attributes
    val attrs_of_fatality : fatality -> XML.attributes
    val attrs_of_location : location -> XML.attributes
    val location_of_attrs : XML.attributes -> location (* raises PGIP *)

    val haspref : preference -> XML.tree

    val pgipurl_of_url : Url.T -> pgipurl              (* raises PGIP *)
    val pgipurl_of_string : string -> pgipurl          (* raises PGIP *)
    val pgipurl_of_path : Path.T -> pgipurl
    val path_of_pgipurl : pgipurl -> Path.T
    val string_of_pgipurl : pgipurl -> string
    val attrs_of_pgipurl : pgipurl -> XML.attributes
    val pgipurl_of_attrs : XML.attributes -> pgipurl   (* raises PGIP *)

    (* XML utils, only for PGIP code *)
    val has_attr       : string -> XML.attributes -> bool
    val attr           : string -> string -> XML.attributes
    val opt_attr       : string -> string option -> XML.attributes
    val opt_attr_map   : ('a -> string) -> string -> 'a option -> XML.attributes
    val get_attr       : string -> XML.attributes -> string           (* raises PGIP *)
    val get_attr_opt   : string -> XML.attributes -> string option
    val get_attr_dflt  : string -> string -> XML.attributes -> string
end

structure PgipTypes : PGIPTYPES_OPNS =
struct
exception PGIP of string

(** XML utils **)

fun has_attr attr attrs = Properties.defined attrs attr

fun get_attr_opt attr attrs = Properties.get attrs attr

fun get_attr attr attrs =
    (case get_attr_opt attr attrs of
         SOME value => value
       | NONE => raise PGIP ("Missing attribute: " ^ quote attr))

fun get_attr_dflt attr dflt attrs = the_default dflt (get_attr_opt attr attrs)

fun attr x y = [(x,y)] : XML.attributes

fun opt_attr_map f attr_name opt_val = 
    case opt_val of NONE => [] | SOME v => [(attr_name,f v)]
 (* or, if you've got function-itis: 
    the_default [] (Option.map (single o (pair attr_name) o f) opt_val)
  *)

fun opt_attr attr_name = opt_attr_map I attr_name


(** Objtypes **)

datatype objtype = ObjFile | ObjTheory | ObjTheorem | ObjComment  
                 | ObjTerm | ObjType | ObjOther of string

fun name_of_objtype obj = 
    case obj of 
        ObjFile    => "file"
      | ObjTheory  => "theory"
      | ObjTheorem => "theorem"
      | ObjComment => "comment"
      | ObjTerm    => "term"
      | ObjType    => "type"
      | ObjOther s => s

val attrs_of_objtype = attr "objtype" o name_of_objtype

fun objtype_of_attrs attrs = case get_attr "objtype" attrs of
       "file" => ObjFile
     | "theory" => ObjTheory
     | "theorem" => ObjTheorem
     | "comment" => ObjComment
     | "term" => ObjTerm
     | "type" => ObjType
     | s => ObjOther s    (* where s mem other_objtypes_parameter *)

type objname = string
type idtable = { context: objname option,    (* container's objname *)
                 objtype: objtype, 
                 ids: objname list }

fun idtable_to_xml {context, objtype, ids} = 
    let 
        val objtype_attrs = attrs_of_objtype objtype
        val context_attrs = opt_attr "context" context
        val ids_content = map (fn x => XML.Elem("identifier",[],[XML.Text x])) ids
    in 
        XML.Elem ("idtable",
                  objtype_attrs @ context_attrs,
                  ids_content)
    end


(** Types and values **)

(* readers and writers for values represented in XML strings *)

fun read_pgipbool s =
    (case s of 
         "false" => false 
       | "true" => true 
       | _ => raise PGIP ("Invalid boolean value: " ^ quote s))

local
    fun int_in_range (NONE,NONE) (_: int) = true
      | int_in_range (SOME min,NONE) i = min<= i
      | int_in_range (NONE,SOME max) i = i<=max
      | int_in_range (SOME min,SOME max) i = min<= i andalso i<=max
in
fun read_pgipint range s =
    (case Int.fromString s of 
         SOME i => if int_in_range range i then i
                   else raise PGIP ("Out of range integer value: " ^ quote s)
       | NONE => raise PGIP ("Invalid integer value: " ^ quote s))
end;

fun read_pgipnat s =
    (case Int.fromString s of 
         SOME i => if i >= 0 then i
                   else raise PGIP ("Invalid natural number: " ^ quote s)
       | NONE => raise PGIP ("Invalid natural number: " ^ quote s))

(* NB: we can maybe do without xml decode/encode here. *)
fun read_pgipstring s =  (* non-empty strings, XML escapes decoded *)
    (case XML.parse_string s of
         SOME s => s
       | NONE => raise PGIP ("Expected a non-empty string: " ^ quote s))
    handle _ => raise PGIP ("Invalid XML string syntax: " ^ quote s)  (* FIXME avoid handle _ *)

val int_to_pgstring = signed_string_of_int

fun string_to_pgstring s = XML.text s

fun bool_to_pgstring b = if b then "true" else "false"


(* PGIP datatypes.
   
   This is a reflection of the type structure of PGIP configuration,
   which is meant for setting up user dialogs and preference settings.
   These are configured declaratively in XML, using a syntax for types
   and values which is like a (vastly cut down) form of XML Schema
   Datatypes.

   The prover needs to interpret the strings representing the typed
   values, at least for the types it expects from the dialogs it
   configures.  Here we go further and construct a type-safe
   encapsulation of these values, which would be useful for more
   advanced cases (e.g. generating and processing forms).  
*)


datatype pgiptype = 
         Pgipnull                            (* unit type: unique element is empty string *)
       | Pgipbool                            (* booleans: "true" or "false" *)
       | Pgipint of int option * int option  (* ranged integers, should be XSD canonical *)
       | Pgipnat                             (* naturals: non-negative integers (convenience) *)
       | Pgipstring                          (* non-empty strings *)
       | Pgipconst of string                 (* singleton type *)
       | Pgipchoice of pgipdtype list        (* union type *)

(* Compared with the PGIP schema, we push descriptions of types inside choices. *)

and pgipdtype = Pgipdtype of string option * pgiptype

datatype pgipuval = Pgvalnull | Pgvalbool of bool | Pgvalint of int | Pgvalnat of int 
                  | Pgvalstring of string | Pgvalconst of string

type pgipval = pgiptype * pgipuval      (* type-safe values *)

fun pgipdtype_to_xml (desco,ty) = 
    let
        val desc_attr = opt_attr "descr" desco

        val elt = case ty of
                      Pgipnull => "pgipnull"
                    | Pgipbool => "pgipbool"
                    | Pgipint _ => "pgipint"
                    | Pgipnat => "pgipint"
                    | Pgipstring => "pgipstring"
                    | Pgipconst _ => "pgipconst"
                    | Pgipchoice _ => "pgipchoice"

        fun range_attr r v = attr r (int_to_pgstring v)

        val attrs = case ty of 
                        Pgipint (SOME min,SOME max) => (range_attr "min" min)@(range_attr "max" max)
                      | Pgipint (SOME min,NONE) => (range_attr "min" min)
                      | Pgipint (NONE,SOME max) => (range_attr "max" max)
                      | Pgipnat => (range_attr "min" 0)
                      | Pgipconst nm => attr "name" nm
                      | _ => []

        fun destpgipdtype (Pgipdtype x) = x

        val typargs = case ty of
                          Pgipchoice ds => map destpgipdtype ds
                        | _ => []
    in 
        XML.Elem (elt, (desc_attr @ attrs), (map pgipdtype_to_xml typargs))
    end

val pgiptype_to_xml = pgipdtype_to_xml o pair NONE

fun read_pguval Pgipnull s = 
    if s="" then Pgvalnull
    else raise PGIP ("Expecting empty string for null type, not: " ^ quote s)
  | read_pguval Pgipbool s = Pgvalbool (read_pgipbool s)
  | read_pguval (Pgipint range) s = Pgvalint (read_pgipint range s)
  | read_pguval Pgipnat s = Pgvalnat (read_pgipnat s)
  | read_pguval (Pgipconst c) s = 
    if c=s then Pgvalconst c 
    else raise PGIP ("Given string: "^quote s^" doesn't match expected string: "^quote c)
  | read_pguval Pgipstring s = 
    if s<>"" then Pgvalstring s
    else raise PGIP ("Expecting non-empty string, empty string illegal.")
  | read_pguval (Pgipchoice tydescs) s = 
    let 
        (* Union type: match first in list *)
        fun getty (Pgipdtype(_, ty)) = ty
        val uval = get_first 
                       (fn ty => SOME (read_pguval ty s) handle PGIP _ => NONE)
                       (map getty tydescs)
    in
        case uval of SOME pgv => pgv | NONE => raise PGIP ("Can't match string: "^quote s^
                                                           " against any allowed types.")
    end

fun read_pgval ty s = (ty, read_pguval ty s)
            
fun pgval_to_string (_, Pgvalnull) = ""
  | pgval_to_string (_, Pgvalbool b) = bool_to_pgstring b
  | pgval_to_string (_, Pgvalnat n) = int_to_pgstring n
  | pgval_to_string (_, Pgvalint i) = int_to_pgstring i
  | pgval_to_string (_, Pgvalconst c) = string_to_pgstring c
  | pgval_to_string (_, Pgvalstring s) = string_to_pgstring s


type pgipurl = Path.T    (* URLs: only local files *)

datatype displayarea = Status | Message | Display | Tracing | Internal | Other of string

datatype fatality = Info | Warning | Nonfatal | Fatal | Panic | Log | Debug

type location = { descr: string option,
                  url: pgipurl option,
                  line: int option,
                  column: int option,
                  char: int option,
                  length: int option }



(** Url operations **)


fun pgipurl_of_string url = (* only handle file:/// or file://localhost/ *)
        case Url.explode url of
            (Url.File path) => path
          | _ => raise PGIP ("Cannot access non-local URL " ^ quote url)
                       
fun pgipurl_of_path p = p

fun path_of_pgipurl p = p  (* potentially raises PGIP, but not with this implementation *)

fun string_of_pgipurl p = Path.implode p

fun attrval_of_pgipurl purl = "file:" ^ (XML.text (File.platform_path (File.full_path purl)))
fun attrs_of_pgipurl purl = [("url", attrval_of_pgipurl purl)]

val pgipurl_of_attrs = pgipurl_of_string o get_attr "url"

fun pgipurl_of_url (Url.File p) = p
  | pgipurl_of_url url = 
    raise PGIP ("Cannot access non-local/non-file URL " ^ quote (Url.implode url))


(** Messages and errors **)

local
  fun string_of_area Status = "status"
    | string_of_area Message = "message"
    | string_of_area Display = "display"
    | string_of_area Tracing = "tracing"
    | string_of_area Internal = "internal"
    | string_of_area (Other s) = s

  fun string_of_fatality Info = "info"
    | string_of_fatality Warning = "warning"
    | string_of_fatality Nonfatal = "nonfatal"
    | string_of_fatality Fatal = "fatal"
    | string_of_fatality Panic = "panic"
    | string_of_fatality Log = "log"
    | string_of_fatality Debug = "debug"
in
  fun attrs_of_displayarea area = [("area", string_of_area area)]

  fun attrs_of_fatality fatality = [("fatality", string_of_fatality fatality)]

  fun attrs_of_location ({ descr, url, line, column, char, length }:location) =
      let 
          val descr = opt_attr "location_descr" descr
          val url = opt_attr_map attrval_of_pgipurl "location_url" url
          val line = opt_attr_map int_to_pgstring "locationline" line
          val column = opt_attr_map int_to_pgstring "locationcolumn"  column
          val char = opt_attr_map int_to_pgstring "locationcharacter" char
          val length = opt_attr_map int_to_pgstring "locationlength" length
      in 
          descr @ url @ line @ column @ char @ length
      end

    fun pgipint_of_string err s = 
        case Int.fromString s of 
            SOME i => i
          | NONE => raise PGIP ("Type error in " ^ quote err ^ ": expected integer.")

  fun location_of_attrs attrs = 
      let
          val descr = get_attr_opt "location_descr" attrs
          val url = Option.map  pgipurl_of_string (get_attr_opt "location_url" attrs)
          val line = Option.map (pgipint_of_string "location element line attribute")
                                (get_attr_opt "locationline" attrs)
          val column = Option.map (pgipint_of_string "location element column attribute")
                                  (get_attr_opt "locationcolumn" attrs)
          val char = Option.map (pgipint_of_string "location element char attribute")
                                (get_attr_opt "locationcharacter" attrs)
          val length = Option.map (pgipint_of_string "location element length attribute")
                                  (get_attr_opt "locationlength" attrs)
      in 
          {descr=descr, url=url, line=line, column=column, char=char, length=length}
      end
end

(** Preferences **)

type preference = { name: string,
                    descr: string option,
                    default: string option,
                    pgiptype: pgiptype }

fun haspref ({ name, descr, default, pgiptype}:preference) = 
    XML.Elem ("haspref",
              attr "name" name @
              opt_attr "descr" descr @
              opt_attr "default" default,
              [pgiptype_to_xml pgiptype])

end

