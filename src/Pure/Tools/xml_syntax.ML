(*  Title:      Pure/Tools/xml_syntax.ML
    Author:     Stefan Berghofer, TU Muenchen

Input and output of types, terms, and proofs in XML format.
See isabelle.xsd for a description of the syntax.
*)

signature XML_SYNTAX =
sig
  val xml_of_type: typ -> XML.tree
  val xml_of_term: term -> XML.tree
  val xml_of_proof: Proofterm.proof -> XML.tree
  val write_to_file: Path.T -> string -> XML.tree -> unit
  exception XML of string * XML.tree
  val type_of_xml: XML.tree -> typ
  val term_of_xml: XML.tree -> term
  val proof_of_xml: XML.tree -> Proofterm.proof
end;

structure XMLSyntax : XML_SYNTAX =
struct

(**** XML output ****)

fun xml_of_class name = XML.Elem ("class", [("name", name)], []);

fun xml_of_type (TVar ((s, i), S)) = XML.Elem ("TVar",
      ("name", s) :: (if i=0 then [] else [("index", string_of_int i)]),
      map xml_of_class S)
  | xml_of_type (TFree (s, S)) =
      XML.Elem ("TFree", [("name", s)], map xml_of_class S)
  | xml_of_type (Type (s, Ts)) =
      XML.Elem ("Type", [("name", s)], map xml_of_type Ts);

fun xml_of_term (Bound i) =
      XML.Elem ("Bound", [("index", string_of_int i)], [])
  | xml_of_term (Free (s, T)) =
      XML.Elem ("Free", [("name", s)], [xml_of_type T])
  | xml_of_term (Var ((s, i), T)) = XML.Elem ("Var",
      ("name", s) :: (if i=0 then [] else [("index", string_of_int i)]),
      [xml_of_type T])
  | xml_of_term (Const (s, T)) =
      XML.Elem ("Const", [("name", s)], [xml_of_type T])
  | xml_of_term (t $ u) =
      XML.Elem ("App", [], [xml_of_term t, xml_of_term u])
  | xml_of_term (Abs (s, T, t)) =
      XML.Elem ("Abs", [("vname", s)], [xml_of_type T, xml_of_term t]);

fun xml_of_opttypes NONE = []
  | xml_of_opttypes (SOME Ts) = [XML.Elem ("types", [], map xml_of_type Ts)];

(* FIXME: the t argument of PThm and PAxm is actually redundant, since *)
(* it can be looked up in the theorem database. Thus, it could be      *)
(* omitted from the xml representation.                                *)

fun xml_of_proof (PBound i) =
      XML.Elem ("PBound", [("index", string_of_int i)], [])
  | xml_of_proof (Abst (s, optT, prf)) =
      XML.Elem ("Abst", [("vname", s)],
        (case optT of NONE => [] | SOME T => [xml_of_type T]) @
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
  | xml_of_proof (PThm (_, ((s, t, optTs), _))) =
      XML.Elem ("PThm", [("name", s)], xml_of_term t :: xml_of_opttypes optTs)
  | xml_of_proof (PAxm (s, t, optTs)) =
      XML.Elem ("PAxm", [("name", s)], xml_of_term t :: xml_of_opttypes optTs)
  | xml_of_proof (Oracle (s, t, optTs)) =
      XML.Elem ("Oracle", [("name", s)], xml_of_term t :: xml_of_opttypes optTs)
  | xml_of_proof MinProof =
      XML.Elem ("MinProof", [], []);

(* useful for checking the output against a schema file *)

fun write_to_file path elname x =
  File.write path
    ("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ^
     XML.string_of (XML.Elem (elname,
       [("xmlns:xsi", "http://www.w3.org/2001/XMLSchema-instance"),
        ("xsi:noNamespaceSchemaLocation", "isabelle.xsd")],
       [x])));


(**** XML input ****)

exception XML of string * XML.tree;

fun class_of_xml (XML.Elem ("class", [("name", name)], [])) = name
  | class_of_xml tree = raise XML ("class_of_xml: bad tree", tree);

fun index_of_string s tree idx = (case Int.fromString idx of
  NONE => raise XML (s ^ ": bad index", tree) | SOME i => i);

fun type_of_xml (tree as XML.Elem ("TVar", atts, classes)) = TVar
      ((case Properties.get atts "name" of
          NONE => raise XML ("type_of_xml: name of TVar missing", tree)
        | SOME name => name,
        the_default 0 (Option.map (index_of_string "type_of_xml" tree)
          (Properties.get atts "index"))),
       map class_of_xml classes)
  | type_of_xml (XML.Elem ("TFree", [("name", s)], classes)) =
      TFree (s, map class_of_xml classes)
  | type_of_xml (XML.Elem ("Type", [("name", s)], types)) =
      Type (s, map type_of_xml types)
  | type_of_xml tree = raise XML ("type_of_xml: bad tree", tree);

fun term_of_xml (tree as XML.Elem ("Bound", [("index", idx)], [])) =
      Bound (index_of_string "bad variable index" tree idx)
  | term_of_xml (XML.Elem ("Free", [("name", s)], [typ])) =
      Free (s, type_of_xml typ)
  | term_of_xml (tree as XML.Elem ("Var", atts, [typ])) = Var
      ((case Properties.get atts "name" of
          NONE => raise XML ("type_of_xml: name of Var missing", tree)
        | SOME name => name,
        the_default 0 (Option.map (index_of_string "term_of_xml" tree)
          (Properties.get atts "index"))),
       type_of_xml typ)
  | term_of_xml (XML.Elem ("Const", [("name", s)], [typ])) =
      Const (s, type_of_xml typ)
  | term_of_xml (XML.Elem ("App", [], [term, term'])) =
      term_of_xml term $ term_of_xml term'
  | term_of_xml (XML.Elem ("Abs", [("vname", s)], [typ, term])) =
      Abs (s, type_of_xml typ, term_of_xml term)
  | term_of_xml tree = raise XML ("term_of_xml: bad tree", tree);

fun opttypes_of_xml [] = NONE
  | opttypes_of_xml [XML.Elem ("types", [], types)] =
      SOME (map type_of_xml types)
  | opttypes_of_xml (tree :: _) = raise XML ("opttypes_of_xml: bad tree", tree);

fun proof_of_xml (tree as XML.Elem ("PBound", [("index", idx)], [])) =
      PBound (index_of_string "proof_of_xml" tree idx)
  | proof_of_xml (XML.Elem ("Abst", [("vname", s)], [proof])) =
      Abst (s, NONE, proof_of_xml proof)
  | proof_of_xml (XML.Elem ("Abst", [("vname", s)], [typ, proof])) =
      Abst (s, SOME (type_of_xml typ), proof_of_xml proof)
  | proof_of_xml (XML.Elem ("AbsP", [("vname", s)], [proof])) =
      AbsP (s, NONE, proof_of_xml proof)
  | proof_of_xml (XML.Elem ("AbsP", [("vname", s)], [term, proof])) =
      AbsP (s, SOME (term_of_xml term), proof_of_xml proof)
  | proof_of_xml (XML.Elem ("Appt", [], [proof])) =
      proof_of_xml proof % NONE
  | proof_of_xml (XML.Elem ("Appt", [], [proof, term])) =
      proof_of_xml proof % SOME (term_of_xml term)
  | proof_of_xml (XML.Elem ("AppP", [], [proof, proof'])) =
      proof_of_xml proof %% proof_of_xml proof'
  | proof_of_xml (XML.Elem ("Hyp", [], [term])) =
      Hyp (term_of_xml term)
  | proof_of_xml (XML.Elem ("PThm", [("name", s)], term :: opttypes)) =
      (* FIXME? *)
      PThm (serial (), ((s, term_of_xml term, opttypes_of_xml opttypes),
        Future.value (Proofterm.approximate_proof_body MinProof)))
  | proof_of_xml (XML.Elem ("PAxm", [("name", s)], term :: opttypes)) =
      PAxm (s, term_of_xml term, opttypes_of_xml opttypes)
  | proof_of_xml (XML.Elem ("Oracle", [("name", s)], term :: opttypes)) =
      Oracle (s, term_of_xml term, opttypes_of_xml opttypes)
  | proof_of_xml (XML.Elem ("MinProof", _, _)) = MinProof
  | proof_of_xml tree = raise XML ("proof_of_xml: bad tree", tree);

end;
