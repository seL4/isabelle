(*  Title:      HOL/Main.thy
    ID:         $Id$
    Author:     Stefan Berghofer, Tobias Nipkow and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Main HOL *}

theory Main = Map + Hilbert_Choice:

text {*
  Theory @{text Main} includes everything.  Note that theory @{text
  PreList} already includes most HOL theories.
*}

text {* Belongs to theory List. *}
declare lists_mono [mono]
declare map_cong [recdef_cong]
lemmas rev_induct [case_names Nil snoc] = rev_induct
  and rev_cases [case_names Nil snoc] = rev_exhaust


subsection {* Characters and strings *}

datatype nibble =
    Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 | Nibble6 | Nibble7
  | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD | NibbleE | NibbleF

datatype char = Char nibble nibble
  -- "Note: canonical order of character encoding coincides with standard term ordering"

types string = "char list"

syntax
  "_Char" :: "xstr => char"    ("CHR _")
  "_String" :: "xstr => string"    ("_")

parse_ast_translation {*
  let
    val constants = Syntax.Appl o map Syntax.Constant;

    fun mk_nib n = "Nibble" ^ chr (n + (if n <= 9 then ord "0" else ord "A" - 10));
    fun mk_char c =
      if Symbol.is_ascii c andalso Symbol.is_printable c then
        constants ["Char", mk_nib (ord c div 16), mk_nib (ord c mod 16)]
      else error ("Printable ASCII character expected: " ^ quote c);

    fun mk_string [] = Syntax.Constant "Nil"
      | mk_string (c :: cs) = Syntax.Appl [Syntax.Constant "Cons", mk_char c, mk_string cs];

    fun char_ast_tr [Syntax.Variable xstr] =
        (case Syntax.explode_xstr xstr of
          [c] => mk_char c
        | _ => error ("Single character expected: " ^ xstr))
      | char_ast_tr asts = raise AST ("char_ast_tr", asts);

    fun string_ast_tr [Syntax.Variable xstr] =
        (case Syntax.explode_xstr xstr of
          [] => constants [Syntax.constrainC, "Nil", "string"]
        | cs => mk_string cs)
      | string_ast_tr asts = raise AST ("string_tr", asts);
  in [("_Char", char_ast_tr), ("_String", string_ast_tr)] end;
*}

print_ast_translation {*
  let
    fun dest_nib (Syntax.Constant c) =
        (case explode c of
          ["N", "i", "b", "b", "l", "e", h] =>
            if "0" <= h andalso h <= "9" then ord h - ord "0"
            else if "A" <= h andalso h <= "F" then ord h - ord "A" + 10
            else raise Match
        | _ => raise Match)
      | dest_nib _ = raise Match;

    fun dest_chr c1 c2 =
      let val c = chr (dest_nib c1 * 16 + dest_nib c2)
      in if Symbol.is_printable c then c else raise Match end;

    fun dest_char (Syntax.Appl [Syntax.Constant "Char", c1, c2]) = dest_chr c1 c2
      | dest_char _ = raise Match;

    fun xstr cs = Syntax.Appl [Syntax.Constant "_xstr", Syntax.Variable (Syntax.implode_xstr cs)];

    fun char_ast_tr' [c1, c2] = Syntax.Appl [Syntax.Constant "_Char", xstr [dest_chr c1 c2]]
      | char_ast_tr' _ = raise Match;

    fun list_ast_tr' [args] = Syntax.Appl [Syntax.Constant "_String",
            xstr (map dest_char (Syntax.unfold_ast "_args" args))]
      | list_ast_tr' ts = raise Match;
  in [("Char", char_ast_tr'), ("@list", list_ast_tr')] end;
*}


subsection {* Configuration of the code generator *}

types_code
  "bool"  ("bool")
  "*"     ("(_ */ _)")
  "list"  ("_ list")

consts_code
  "op ="    ("(_ =/ _)")

  "True"    ("true")
  "False"   ("false")
  "Not"     ("not")
  "op |"    ("(_ orelse/ _)")
  "op &"    ("(_ andalso/ _)")
  "If"      ("(if _/ then _/ else _)")

  "Pair"    ("(_,/ _)")
  "fst"     ("fst")
  "snd"     ("snd")

  "Nil"     ("[]")
  "Cons"    ("(_ ::/ _)")

  "wfrec"   ("wf'_rec?")

ML {* fun wf_rec f x = f (wf_rec f) x; *}

lemma [code]: "((n::nat) < 0) = False" by simp
declare less_Suc_eq [code]

end
