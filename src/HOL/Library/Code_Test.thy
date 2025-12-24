(*  Title:      HOL/Library/Code_Test.thy
    Author:     Andreas Lochbihler, ETH Zürich

Test infrastructure for the code generator.
*)

section \<open>Test infrastructure for the code generator\<close>

theory Code_Test
imports Main
keywords "test_code" :: diag
begin

subsection \<open>YXML encoding for \<^typ>\<open>Code_Evaluation.term\<close>\<close>

datatype (plugins del: code size "quickcheck") yxml_of_term = YXML

lemma yot_anything: "x = (y :: yxml_of_term)"
by(cases x y rule: yxml_of_term.exhaust[case_product yxml_of_term.exhaust])(simp)

definition yot_empty :: yxml_of_term where [code drop]: "yot_empty = YXML"
definition yot_literal :: "String.literal \<Rightarrow> yxml_of_term"
  where [code drop]: "yot_literal _ = YXML"
definition yot_append :: "yxml_of_term \<Rightarrow> yxml_of_term \<Rightarrow> yxml_of_term"
  where [code drop]: "yot_append _ _ = YXML"
definition yot_concat :: "yxml_of_term list \<Rightarrow> yxml_of_term"
  where [code drop]: "yot_concat _ = YXML"

text \<open>Serialise \<^typ>\<open>yxml_of_term\<close> to native string of target language\<close>

code_printing type_constructor yxml_of_term
  \<rightharpoonup>  (SML) "string"
  and (OCaml) "string"
  and (Haskell) "String"
  and (Scala) "String"
| constant yot_empty
  \<rightharpoonup>  (SML) "\"\""
  and (OCaml) "\"\""
  and (Haskell) "\"\""
  and (Scala) "\"\""
| constant yot_literal
  \<rightharpoonup>  (SML) "_"
  and (OCaml) "_"
  and (Haskell) "_"
  and (Scala) "_"
| constant yot_append
  \<rightharpoonup> (SML) "String.concat [(_), (_)]"
  and (OCaml) "String.concat \"\" [(_); (_)]"
  and (Haskell) infixr 5 "++"
  and (Scala) infixl 5 "+"
| constant yot_concat
  \<rightharpoonup> (SML) "String.concat"
  and (OCaml) "String.concat \"\""
  and (Haskell) "Prelude.concat"
  and (Scala) "_.mkString(\"\")"

text \<open>
  Stripped-down implementations of Isabelle's XML tree with YXML encoding as
  defined in \<^file>\<open>~~/src/Pure/PIDE/xml.ML\<close>, \<^file>\<open>~~/src/Pure/PIDE/yxml.ML\<close>
  sufficient to encode \<^typ>\<open>Code_Evaluation.term\<close> as in
  \<^file>\<open>~~/src/Pure/term_xml.ML\<close>.
\<close>

datatype (plugins del: code size "quickcheck") xml_tree = XML_Tree

lemma xml_tree_anything: "x = (y :: xml_tree)"
by(cases x y rule: xml_tree.exhaust[case_product xml_tree.exhaust])(simp)

context begin
local_setup \<open>Local_Theory.map_background_naming (Name_Space.mandatory_path "xml")\<close>

type_synonym attributes = "(String.literal \<times> String.literal) list"
type_synonym body = "xml_tree list"

definition Elem :: "String.literal \<Rightarrow> attributes \<Rightarrow> xml_tree list \<Rightarrow> xml_tree"
where [code drop]: "Elem _ _ _ = XML_Tree"

definition Text :: "String.literal \<Rightarrow> xml_tree"
where [code drop]: "Text _ = XML_Tree"

definition node :: "xml_tree list \<Rightarrow> xml_tree"
where "node ts = Elem (STR '':'') [] ts"

definition tagged :: "String.literal \<Rightarrow> String.literal option \<Rightarrow> xml_tree list \<Rightarrow> xml_tree"
where "tagged tag x ts = Elem tag (case x of None \<Rightarrow> [] | Some x' \<Rightarrow> [(STR ''0'', x')]) ts"

definition list where "list f xs = map (node \<circ> f) xs"

definition X :: yxml_of_term where "X = yot_literal (STR 0x05)"
definition Y :: yxml_of_term where "Y = yot_literal (STR 0x06)"
definition XY :: yxml_of_term where "XY = yot_append X Y"
definition XYX :: yxml_of_term where "XYX = yot_append XY X"

end

code_datatype xml.Elem xml.Text

definition yxml_string_of_xml_tree :: "xml_tree \<Rightarrow> yxml_of_term \<Rightarrow> yxml_of_term"
where "yxml_string_of_xml_tree _ _ = YXML"

lemma yxml_string_of_xml_tree_code [code]:
  "yxml_string_of_xml_tree (xml.Elem name atts ts) rest =
   yot_append xml.XY (
   yot_append (yot_literal name) (
   foldr (\<lambda>(a, x) rest.
     yot_append xml.Y (
     yot_append (yot_literal a) (
     yot_append (yot_literal (STR ''='')) (
     yot_append (yot_literal x) rest)))) atts (
   foldr yxml_string_of_xml_tree ts (
   yot_append xml.XYX rest))))"
  "yxml_string_of_xml_tree (xml.Text s) rest = yot_append (yot_literal s) rest"
by(rule yot_anything)+

definition yxml_string_of_body :: "xml.body \<Rightarrow> yxml_of_term"
where "yxml_string_of_body ts = foldr yxml_string_of_xml_tree ts yot_empty"

text \<open>
  Encoding \<^typ>\<open>Code_Evaluation.term\<close> into XML trees as defined in
  \<^file>\<open>~~/src/Pure/term_xml.ML\<close>.
\<close>

definition xml_of_typ :: "Typerep.typerep \<Rightarrow> xml.body"
where "xml_of_typ _ = [XML_Tree]"

definition xml_of_term :: "Code_Evaluation.term \<Rightarrow> xml.body"
where "xml_of_term _ = [XML_Tree]"

lemma xml_of_typ_code [code]:
  "xml_of_typ (typerep.Typerep t args) = [xml.tagged (STR ''0'') (Some t) (xml.list xml_of_typ args)]"
by(simp add: xml_of_typ_def xml_tree_anything)

lemma xml_of_term_code [code]:
  "xml_of_term (Code_Evaluation.Const x ty) = [xml.tagged (STR ''0'') (Some x) (xml_of_typ ty)]"
  "xml_of_term (Code_Evaluation.App t1 t2)  = [xml.tagged (STR ''5'') None [xml.node (xml_of_term t1), xml.node (xml_of_term t2)]]"
  "xml_of_term (Code_Evaluation.Abs x ty t) = [xml.tagged (STR ''4'') (Some x) [xml.node (xml_of_typ ty), xml.node (xml_of_term t)]]"
  \<comment> \<open>FIXME: \<^const>\<open>Code_Evaluation.Free\<close> is used only in \<^theory>\<open>HOL.Quickcheck_Narrowing\<close> to represent
    uninstantiated parameters in constructors. Here, we always translate them to \<^ML>\<open>Free\<close> variables.\<close>
  "xml_of_term (Code_Evaluation.Free x ty)  = [xml.tagged (STR ''1'') (Some x) (xml_of_typ ty)]"
by(simp_all add: xml_of_term_def xml_tree_anything)

definition yxml_string_of_term :: "Code_Evaluation.term \<Rightarrow> yxml_of_term"
where "yxml_string_of_term = yxml_string_of_body \<circ> xml_of_term"

subsection \<open>Test engine and drivers\<close>

ML_file \<open>code_test.ML\<close>

end
