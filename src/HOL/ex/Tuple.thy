(*  Title:      HOL/ex/Tuple.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Properly nested products (see also theory Prod).

Unquestionably, this should be used as the standard representation of
tuples in HOL, but it breaks many existing theories!
*)

header {* Properly nested products *}

theory Tuple = HOL:


subsection {* Abstract syntax *}

typedecl unit
typedecl ('a, 'b) prod

consts
  Pair :: "'a => 'b => ('a, 'b) prod"
  fst :: "('a, 'b) prod => 'a"
  snd :: "('a, 'b) prod => 'b"
  split :: "('a => 'b => 'c) => ('a, 'b) prod => 'c"
  Unity :: unit    ("'(')")


subsection {* Concrete syntax *}

subsubsection {* Tuple types *}

nonterminals
  tuple_type_args
syntax
  "_tuple_type_arg"  :: "type => tuple_type_args"                    ("_" [21] 21)
  "_tuple_type_args" :: "type => tuple_type_args => tuple_type_args" ("_ */ _" [21, 20] 20)
  "_tuple_type"      :: "type => tuple_type_args => type"            ("(_ */ _)" [21, 20] 20)

syntax (xsymbols)
  "_tuple_type_args" :: "type => tuple_type_args => tuple_type_args" ("_ \<times>/ _" [21, 20] 20)
  "_tuple_type"      :: "type => tuple_type_args => type"          ("(_ \<times>/ _)" [21, 20] 20)

syntax (HTML output)
  "_tuple_type_args" :: "type => tuple_type_args => tuple_type_args" ("_ \<times>/ _" [21, 20] 20)
  "_tuple_type"      :: "type => tuple_type_args => type"          ("(_ \<times>/ _)" [21, 20] 20)

translations
  (type) "'a * 'b" == (type) "('a, ('b, unit) prod) prod"
  (type) "('a, ('b, 'cs) _tuple_type_args) _tuple_type" ==
    (type) "('a, ('b, 'cs) _tuple_type) prod"


subsubsection {* Tuples *}

nonterminals
  tuple_args
syntax
  "_tuple"      :: "'a => tuple_args => 'b"             ("(1'(_,/ _'))")
  "_tuple_arg"  :: "'a => tuple_args"                   ("_")
  "_tuple_args" :: "'a => tuple_args => tuple_args"     ("_,/ _")
translations
  "(x, y)" == "Pair x (Pair y ())"
  "_tuple x (_tuple_args y zs)" == "Pair x (_tuple y zs)"


subsubsection {* Tuple patterns *}

nonterminals tuple_pat_args
  -- {* extends pre-defined type "pttrn" syntax used in abstractions *}
syntax
  "_tuple_pat_arg"  :: "pttrn => tuple_pat_args"                     ("_")
  "_tuple_pat_args" :: "pttrn => tuple_pat_args => tuple_pat_args"   ("_,/ _")
  "_tuple_pat"      :: "pttrn => tuple_pat_args => pttrn"            ("'(_,/ _')")

translations
  "%(x,y). b" => "split (%x. split (%y. (_K b) :: unit => _))"
  "%(x,y). b" <= "split (%x. split (%y. _K b))"
  "_abs (_tuple_pat x (_tuple_pat_args y zs)) b" == "split (%x. (_abs (_tuple_pat y zs) b))"

(* FIXME test *)
  (*the following rules accommodate tuples in `case C ... (x,y,...) ... => ...' where
     (x,y,...) is parsed as `Pair x (Pair y ...)' because it is logic, not pttrn*)
  "_abs (Pair x (Pair y ())) b" => "%(x,y). b"
  "_abs (Pair x (_abs (_tuple_pat y zs) b))" => "_abs (_tuple_pat x (_tuple_pat_args y zs)) b"

(* FIXME improve handling of nested patterns *)
typed_print_translation {*
  let
    fun split_tr' _ T1
            (Abs (x, xT, Const ("split", T2) $ Abs (y, yT, Abs (_, Type ("unit", []), b))) :: ts) =
          if Term.loose_bvar1 (b, 0) then raise Match
          else Term.list_comb
            (Const ("split", T1) $ Abs (x, xT, Const ("split", T2) $
              Abs (y, yT, Syntax.const "_K" $ Term.incr_boundvars ~1 b)), ts)
      | split_tr' _ _ _ = raise Match;
  in [("split", split_tr')] end
*}

end
