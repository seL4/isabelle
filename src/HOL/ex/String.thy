(*  Title:      HOL/String.thy
    ID:         $Id$

Hex chars. Strings.
*)

String = List +

datatype
  nibble = H00 | H01 | H02 | H03 | H04 | H05 | H06 | H07
         | H08 | H09 | H0A | H0B | H0C | H0D | H0E | H0F

datatype
  char = Char nibble nibble

types
  string = char list

syntax
  "_Char"       :: xstr => char       ("CHR _")
  "_String"     :: xstr => string     ("_")

end


ML

local
  open Syntax;

  val ssquote = enclose "''" "''";


  (* chars *)

  val zero = ord "0";
  val ten = ord "A" - 10;

  fun mk_nib n =
    const ("H0" ^ chr (n + (if n <= 9 then zero else ten)));

  fun dest_nib (Const (c, _)) =
        (case explode c of
          ["H", "0", h] => ord h - (if h <= "9" then zero else ten)
        | _ => raise Match)
    | dest_nib _ = raise Match;

  fun dest_nibs t1 t2 = chr (dest_nib t1 * 16 + dest_nib t2);


  fun mk_char c =
    const "Char" $ mk_nib (ord c div 16) $ mk_nib (ord c mod 16);

  fun dest_char (Const ("Char", _) $ t1 $ t2) = dest_nibs t1 t2
    | dest_char _ = raise Match;


  fun char_tr (*"_Char"*) [Free (c, _)] =
        if size c = 1 then mk_char c
        else error ("Bad character: " ^ quote c)
    | char_tr (*"_Char"*) ts = raise_term "char_tr" ts;

  fun char_tr' (*"Char"*) [t1, t2] =
        const "_Char" $ free (ssquote (dest_nibs t1 t2))
    | char_tr' (*"Char"*) _ = raise Match;


  (* strings *)

  fun mk_string [] = const constrainC $ const "[]" $ const "string"
    | mk_string (t :: ts) = const "op #" $ t $ mk_string ts;

  fun dest_string (Const ("[]", _)) = []
    | dest_string (Const ("op #", _) $ c $ cs) = dest_char c :: dest_string cs
    | dest_string _ = raise Match;


  fun string_tr (*"_String"*) [Free (txt, _)] =
        mk_string (map mk_char (explode txt))
    | string_tr (*"_String"*) ts = raise_term "string_tr" ts;

  fun cons_tr' (*"op #"*) [c, cs] =
        const "_String" $ free (ssquote (implode (dest_char c :: dest_string cs)))
    | cons_tr' (*"op #"*) ts = raise Match;

in
  val parse_translation = [("_Char", char_tr), ("_String", string_tr)];
  val print_translation = [("Char", char_tr'), ("op #", cons_tr')];
end;

