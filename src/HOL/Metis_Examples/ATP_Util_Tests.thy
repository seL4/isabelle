(*  Title:      HOL/Metis_Examples/ATP_Util_Tests.thy
    Author:     Martin Desharnais-Schäfer, LMU München

Tests for the utility functions used by the ATP module.
*)
theory ATP_Util_Tests
  imports HOL.ATP
begin

ML \<open>
open ATP_Util

(* Whitespace, and the single space kept between two ident characters *)
val () = \<^assert> (strip_spaces_except_between_idents "" = "")
val () = \<^assert> (strip_spaces_except_between_idents " " = "")
val () = \<^assert> (strip_spaces_except_between_idents "a" = "a")
val () = \<^assert> (strip_spaces_except_between_idents " a" = "a")
val () = \<^assert> (strip_spaces_except_between_idents "a " = "a")
val () = \<^assert> (strip_spaces_except_between_idents "cnf( 1 , plain )" = "cnf(1,plain)")
val () = \<^assert> (strip_spaces_except_between_idents "a b" = "a b")
val () = \<^assert> (strip_spaces_except_between_idents "foo  bar" = "foo bar")
val () = \<^assert> (strip_spaces_except_between_idents "a   b" = "a b")
val () = \<^assert> (strip_spaces_except_between_idents "ab  cd  ef" = "ab cd ef")
val () = \<^assert> (strip_spaces_except_between_idents "foo (" = "foo(")
val () = \<^assert> (strip_spaces_except_between_idents "( a" = "(a")
val () = \<^assert> (strip_spaces_except_between_idents "1 2" = "1 2")
val () = \<^assert> (strip_spaces_except_between_idents "_ a" = "_ a")
val () = \<^assert> (strip_spaces_except_between_idents "a\t\nb" = "a b")
val () = \<^assert> (strip_spaces_except_between_idents "a\127b" = "a b")

(* Comments, unterminated ones, and "/" or "*" that start no comment *)
val () = \<^assert> (strip_spaces_except_between_idents "%" = "")
val () = \<^assert> (strip_spaces_except_between_idents "%c\nb" = "b")
val () = \<^assert> (strip_spaces_except_between_idents "a %" = "a")
val () = \<^assert> (strip_spaces_except_between_idents "a %c" = "a")
val () = \<^assert> (strip_spaces_except_between_idents "/*" = "")
val () = \<^assert> (strip_spaces_except_between_idents "/*x*/b" = "b")
val () = \<^assert> (strip_spaces_except_between_idents "a/* x */b" = "a b")
val () = \<^assert> (strip_spaces_except_between_idents "a/*b" = "a")
val () = \<^assert> (strip_spaces_except_between_idents "a/*x*" = "a")
val () = \<^assert> (strip_spaces_except_between_idents "a/*x*//*y*/b" = "a b")
val () = \<^assert> (strip_spaces_except_between_idents "/*a*/ /*b*/c" = "c")
val () = \<^assert> (strip_spaces_except_between_idents "*/" = "*/")
val () = \<^assert> (strip_spaces_except_between_idents "a/" = "a/")
val () = \<^assert> (strip_spaces_except_between_idents "/a" = "/a")
val () = \<^assert> (strip_spaces_except_between_idents "a/b" = "a/b")

(* A comment separates two identifiers just like whitespace, with or without whitespace of its
   own around it *)
val () = \<^assert> (strip_spaces_except_between_idents "foo bar" = "foo bar")
val () = \<^assert> (strip_spaces_except_between_idents "foo %c\nbar" = "foo bar")
val () = \<^assert> (strip_spaces_except_between_idents "foo\n%c\nbar" = "foo bar")
val () = \<^assert> (strip_spaces_except_between_idents "foo %c\n%d\nbar" = "foo bar")
val () = \<^assert> (strip_spaces_except_between_idents "foo /* c */ bar" = "foo bar")
val () = \<^assert> (strip_spaces_except_between_idents "foo/* c */bar" = "foo bar")
val () = \<^assert> (strip_spaces_except_between_idents "a %c\nb" = "a b")

(* no space here: "." is not an ident character *)
val () = \<^assert> (strip_spaces_except_between_idents "cnf(1,a). %c\ncnf(2,b)."
  = "cnf(1,a).cnf(2,b).")

(* With skip_comments = false, "%" and "/*" are ordinary characters *)
val () = \<^assert> (strip_spaces false Char.isAlphaNum "a %c\nb" = "a%c b")
val () = \<^assert> (strip_spaces false (K true) "a %b\nc" = "a %b c")
\<close>

end