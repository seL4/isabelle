signature XML_CONV =
sig
  type 'a input = XML.tree -> 'a
  type 'a output = 'a -> XML.tree

  exception ParseException of string

  val xml_of_typ: typ output
  val typ_of_xml: typ input

  val xml_of_term: term output
  val term_of_xml : term input

  val xml_of_mixfix: mixfix output
  val mixfix_of_xml: mixfix input
  
  val xml_of_proof: Proofterm.proof output

  val xml_of_bool: bool output
  val bool_of_xml: bool input
		  
  val xml_of_int: int output
  val int_of_xml: int input

  val xml_of_string: string output
  val string_of_xml: string input

  val xml_of_list: 'a output -> 'a list output
  val list_of_xml: 'a input -> 'a list input
  
  val xml_of_tuple : 'a output -> 'a list output
  val tuple_of_xml: 'a input -> int -> 'a list input

  val xml_of_option: 'a output -> 'a option output
  val option_of_xml: 'a input -> 'a option input

  val xml_of_pair: 'a output -> 'b output -> ('a * 'b) output
  val pair_of_xml: 'a input -> 'b input -> ('a * 'b) input

  val xml_of_triple: 'a output -> 'b output -> 'c output -> ('a * 'b * 'c) output
  val triple_of_xml: 'a input -> 'b input -> 'c input -> ('a * 'b * 'c) input
  
  val xml_of_unit: unit output
  val unit_of_xml: unit input

  val xml_of_quadruple: 'a output -> 'b output -> 'c output -> 'd output -> ('a * 'b * 'c * 'd) output
  val quadruple_of_xml: 'a input -> 'b input -> 'c input -> 'd input -> ('a * 'b * 'c * 'd) input

  val xml_of_quintuple: 'a output -> 'b output -> 'c output -> 'd output -> 'e output -> ('a * 'b * 'c * 'd * 'e) output
  val quintuple_of_xml: 'a input -> 'b input -> 'c input -> 'd input -> 'e input -> ('a * 'b * 'c * 'd * 'e) input

  val wrap : string -> 'a output -> 'a output
  val unwrap : ('a -> 'b) -> 'a input -> 'b input
  val wrap_empty : string output
  val unwrap_empty : 'a -> 'a input
  val name_of_wrap : XML.tree -> string

  val write_to_file: 'a output -> string -> 'a -> unit
  val read_from_file: 'a input -> string -> 'a
end;

structure XMLConv : XML_CONV =
struct
  
type 'a input = XML.tree -> 'a
type 'a output = 'a -> XML.tree
exception ParseException of string

fun parse_err s = raise ParseException s

fun xml_of_class name = XML.Elem ("class", [("name", name)], []);

fun class_of_xml (XML.Elem ("class", [("name", name)], [])) = name
  | class_of_xml _ = parse_err "class"
 
fun xml_of_typ (TVar ((s, i), S)) = XML.Elem ("TVar",
      ("name", s) :: (if i=0 then [] else [("index", string_of_int i)]),
      map xml_of_class S)
  | xml_of_typ (TFree (s, S)) =
      XML.Elem ("TFree", [("name", s)], map xml_of_class S)
  | xml_of_typ (Type (s, Ts)) =
      XML.Elem ("Type", [("name", s)], map xml_of_typ Ts);

fun intofstr s i = 
    case Int.fromString i of 
	NONE => parse_err (s^", invalid index: "^i)
      | SOME i => i

fun typ_of_xml (XML.Elem ("TVar", [("name", s)], cs)) = TVar ((s,0), map class_of_xml cs)
  | typ_of_xml (XML.Elem ("TVar", [("name", s), ("index", i)], cs)) = 
    TVar ((s, intofstr "TVar" i), map class_of_xml cs)
  | typ_of_xml (XML.Elem ("TFree", [("name", s)], cs)) = TFree (s, map class_of_xml cs)
  | typ_of_xml (XML.Elem ("Type", [("name", s)], ts)) = Type (s, map typ_of_xml ts)
  | typ_of_xml _ = parse_err "type"

fun xml_of_term (Bound i) =
      XML.Elem ("Bound", [("index", string_of_int i)], [])
  | xml_of_term (Free (s, T)) =
      XML.Elem ("Free", [("name", s)], [xml_of_typ T])
  | xml_of_term (Var ((s, i), T)) = XML.Elem ("Var",
      ("name", s) :: (if i=0 then [] else [("index", string_of_int i)]),
      [xml_of_typ T])
  | xml_of_term (Const (s, T)) =
      XML.Elem ("Const", [("name", s)], [xml_of_typ T])
  | xml_of_term (t $ u) =
      XML.Elem ("App", [], [xml_of_term t, xml_of_term u])
  | xml_of_term (Abs (s, T, t)) =
      XML.Elem ("Abs", [("vname", s)], [xml_of_typ T, xml_of_term t]);

fun term_of_xml (XML.Elem ("Bound", [("index", i)], [])) = Bound (intofstr "Bound" i)
  | term_of_xml (XML.Elem ("Free", [("name", s)], [T])) = Free (s, typ_of_xml T)
  | term_of_xml (XML.Elem ("Var",[("name", s)], [T])) = Var ((s,0), typ_of_xml T)
  | term_of_xml (XML.Elem ("Var",[("name", s), ("index", i)], [T])) = Var ((s,intofstr "Var" i), typ_of_xml T)
  | term_of_xml (XML.Elem ("Const", [("name", s)], [T])) = Const (s, typ_of_xml T)
  | term_of_xml (XML.Elem ("App", [], [t, u])) = (term_of_xml t) $ (term_of_xml u)
  | term_of_xml (XML.Elem ("Abs", [("vname", s)], [T, t])) = Abs (s, typ_of_xml T, term_of_xml t)
  | term_of_xml _ = parse_err "term"

fun xml_of_opttypes NONE = []
  | xml_of_opttypes (SOME Ts) = [XML.Elem ("types", [], map xml_of_typ Ts)];

(* FIXME: the t argument of PThm and PAxm is actually redundant, since *)
(* it can be looked up in the theorem database. Thus, it could be      *)
(* omitted from the xml representation.                                *)

fun xml_of_proof (PBound i) =
      XML.Elem ("PBound", [("index", string_of_int i)], [])
  | xml_of_proof (Abst (s, optT, prf)) =
      XML.Elem ("Abst", [("vname", s)],
        (case optT of NONE => [] | SOME T => [xml_of_typ T]) @
        [xml_of_proof prf])
  | xml_of_proof (AbsP (s, optt, prf)) =
      XML.Elem ("AbsP", [("vname", s)],
        (case optt of NONE => [] | SOME t => [xml_of_term t]) @
        [xml_of_proof prf])
  | xml_of_proof (prf % optt) =
      XML.Elem ("Appt", [],
        xml_of_proof prf ::
        (case optt of NONE => [] | SOME t => [xml_of_term t]))
  | xml_of_proof (prf %% prf') =
      XML.Elem ("AppP", [], [xml_of_proof prf, xml_of_proof prf'])
  | xml_of_proof (Hyp t) = XML.Elem ("Hyp", [], [xml_of_term t])
  | xml_of_proof (PThm ((s, _), _, t, optTs)) =
      XML.Elem ("PThm", [("name", s)], xml_of_term t :: xml_of_opttypes optTs)
  | xml_of_proof (PAxm (s, t, optTs)) =
      XML.Elem ("PAxm", [("name", s)], xml_of_term t :: xml_of_opttypes optTs)
  | xml_of_proof (Oracle (s, t, optTs)) =
      XML.Elem ("Oracle", [("name", s)], xml_of_term t :: xml_of_opttypes optTs)
  | xml_of_proof (MinProof _) = XML.Elem ("MinProof", [], []);

fun xml_of_bool b = XML.Elem ("bool", [("value", if b then "true" else "false")], [])
fun xml_of_int i = XML.Elem ("int", [("value", string_of_int i)], [])
fun xml_of_string s = XML.Elem ("string", [("value", s)], [])
fun xml_of_unit () = XML.Elem ("unit", [], [])
fun xml_of_list output ls = XML.Elem ("list", [], map output ls)
fun xml_of_tuple output ls = XML.Elem ("tuple", [], map output ls)
fun xml_of_option output opt = XML.Elem ("option", [], case opt of NONE => [] | SOME x => [output x])
fun wrap s output x = XML.Elem (s, [], [output x])
fun wrap_empty s = XML.Elem (s, [], [])
fun xml_of_pair output1 output2 (x1, x2) = XML.Elem ("pair", [], [output1 x1, output2 x2])
fun xml_of_triple output1 output2 output3 (x1, x2, x3) = XML.Elem ("triple", [], [output1 x1, output2 x2, output3 x3])
fun xml_of_quadruple output1 output2 output3 output4 (x1, x2, x3, x4) = 
    XML.Elem ("quadruple", [], [output1 x1, output2 x2, output3 x3, output4 x4])
fun xml_of_quintuple output1 output2 output3 output4 output5 (x1, x2, x3, x4, x5) = 
    XML.Elem ("quintuple", [], [output1 x1, output2 x2, output3 x3, output4 x4, output5 x5])
										  
fun bool_of_xml (XML.Elem ("bool", [("value", "true")], [])) = true
  | bool_of_xml (XML.Elem ("bool", [("value", "false")], [])) = false
  | bool_of_xml _ = parse_err "bool"

fun int_of_xml (XML.Elem ("int", [("value", i)], [])) = intofstr "int" i
  | int_of_xml _ = parse_err "int"

fun unit_of_xml (XML.Elem ("unit", [], [])) = ()
  | unit_of_xml _ = parse_err "unit"

fun list_of_xml input (XML.Elem ("list", [], ls)) = map input ls
  | list_of_xml _ _ = parse_err "list"

fun tuple_of_xml input i (XML.Elem ("tuple", [], ls)) = 
    if i = length ls then map input ls else parse_err "tuple"
  | tuple_of_xml _ _ _ = parse_err "tuple"

fun option_of_xml input (XML.Elem ("option", [], [])) = NONE
  | option_of_xml input (XML.Elem ("option", [], [opt])) = SOME (input opt)
  | option_of_xml _ _ = parse_err "option"

fun pair_of_xml input1 input2 (XML.Elem ("pair", [], [x1, x2])) = (input1 x1, input2 x2)
  | pair_of_xml _ _ _ = parse_err "pair"

fun triple_of_xml input1 input2 input3 (XML.Elem ("triple", [], [x1, x2, x3])) = (input1 x1, input2 x2, input3 x3)
  | triple_of_xml _ _ _ _ = parse_err "triple"

fun quadruple_of_xml input1 input2 input3 input4 (XML.Elem ("quadruple", [], [x1, x2, x3, x4])) = 
    (input1 x1, input2 x2, input3 x3, input4 x4)
  | quadruple_of_xml _ _ _ _ _ = parse_err "quadruple"

fun quintuple_of_xml input1 input2 input3 input4 input5 (XML.Elem ("quintuple", [], [x1, x2, x3, x4, x5])) = 
    (input1 x1, input2 x2, input3 x3, input4 x4, input5 x5)
  | quintuple_of_xml _ _ _ _ _ _ = parse_err "quintuple"

fun unwrap f input (XML.Elem (_, [], [x])) = f (input x)
  | unwrap _ _ _  = parse_err "unwrap"

fun unwrap_empty x (XML.Elem (_, [], [])) = x 
  | unwrap_empty _ _ = parse_err "unwrap_unit"

fun name_of_wrap (XML.Elem (name, _, _)) = name
  | name_of_wrap _ = parse_err "name_of_wrap"

fun string_of_xml (XML.Elem ("string", [("value", s)], [])) = s
  | string_of_xml _ = parse_err "string"

fun xml_of_mixfix NoSyn = wrap_empty "nosyn"
  | xml_of_mixfix Structure = wrap_empty "structure"
  | xml_of_mixfix (Mixfix args) = wrap "mixfix" (xml_of_triple xml_of_string (xml_of_list xml_of_int) xml_of_int) args
  | xml_of_mixfix (Delimfix s) = wrap "delimfix" xml_of_string s
  | xml_of_mixfix (InfixName args) = wrap "infixname" (xml_of_pair xml_of_string xml_of_int) args
  | xml_of_mixfix (InfixlName args) = wrap "infixlname" (xml_of_pair xml_of_string xml_of_int) args
  | xml_of_mixfix (InfixrName args) = wrap "infixrname" (xml_of_pair xml_of_string xml_of_int) args
  | xml_of_mixfix (Infix i) = wrap "infix" xml_of_int i
  | xml_of_mixfix (Infixl i) = wrap "infixl" xml_of_int i
  | xml_of_mixfix (Infixr i) = wrap "infixr" xml_of_int i
  | xml_of_mixfix (Binder args) = wrap "binder" (xml_of_triple xml_of_string xml_of_int xml_of_int) args
				  
fun mixfix_of_xml e = 
    (case name_of_wrap e of 
	 "nosyn" => unwrap_empty NoSyn 
       | "structure" => unwrap_empty Structure 
       | "mixfix" => unwrap Mixfix (triple_of_xml string_of_xml (list_of_xml int_of_xml) int_of_xml)
       | "delimfix" => unwrap Delimfix string_of_xml
       | "infixname" => unwrap InfixName (pair_of_xml string_of_xml int_of_xml) 
       | "infixlname" => unwrap InfixlName (pair_of_xml string_of_xml int_of_xml)  
       | "infixrname" => unwrap InfixrName (pair_of_xml string_of_xml int_of_xml)
       | "infix" => unwrap Infix int_of_xml
       | "infixl" => unwrap Infixl int_of_xml 
       | "infixr" => unwrap Infixr int_of_xml
       | "binder" => unwrap Binder (triple_of_xml string_of_xml int_of_xml int_of_xml)
       | _ => parse_err "mixfix"
    ) e


fun write_to_file output fname x = File.write (Path.unpack fname) (XML.string_of_tree (output x))
 
fun read_from_file input fname = 
    let
	val _ = writeln "read_from_file enter"
	val s = File.read (Path.unpack fname)
	val _ = writeln "done: read file"
	val tree = timeit (fn () => XML.tree_of_string s)
	val _ = writeln "done: tree"
	val x = timeit (fn () => input tree)
	val _ = writeln "done: input"
    in
	x
    end

end;

structure XMLConvOutput =
struct
open XMLConv
 
val typ = xml_of_typ
val term = xml_of_term
val mixfix = xml_of_mixfix
val proof = xml_of_proof
val bool = xml_of_bool
val int = xml_of_int
val string = xml_of_string
val unit = xml_of_unit
val list = xml_of_list
val pair = xml_of_pair
val option = xml_of_option
val triple = xml_of_triple
val quadruple = xml_of_quadruple
val quintuple = xml_of_quintuple

end

structure XMLConvInput = 
struct
open XMLConv

val typ = typ_of_xml
val term = term_of_xml
val mixfix = mixfix_of_xml
val bool = bool_of_xml
val int = int_of_xml
val string = string_of_xml
val unit = unit_of_xml
val list = list_of_xml
val pair = pair_of_xml
val option = option_of_xml
val triple = triple_of_xml
val quadruple = quadruple_of_xml
val quintuple = quintuple_of_xml

end

