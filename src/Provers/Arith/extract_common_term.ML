(*  Title:      Provers/Arith/extract_common_term.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2000  University of Cambridge

Extract common terms in balanced expressions:

     i + u + j ~~ i' + u + j'  ==  u + (i + j) ~~ u + (i' + j')
     i + u     ~~ u            ==  u + i       ~~ u + 0

where ~~ is an appropriate balancing operation (e.g. =, <=, <, -) and 0 is a
suitable identity for +.

This massaged formula is then simplified in a user-specified way.
*)

signature EXTRACT_COMMON_TERM_DATA =
sig
  (*abstract syntax*)
  val mk_sum: typ -> term list -> term
  val dest_sum: term -> term list
  val mk_bal: term * term -> term
  val dest_bal: term -> term * term
  val find_first: term -> term list -> term list
  (*proof tools*)
  val mk_eq: term * term -> term
  val norm_tac: simpset -> tactic                (*proves the result*)
  val simplify_meta_eq: simpset -> thm -> thm -> thm (*simplifies the result*)
  val simp_conv: simpset -> term -> thm option  (*proves simp thm*)
end;


functor ExtractCommonTermFun(Data: EXTRACT_COMMON_TERM_DATA):
  sig
  val proc: simpset -> term -> thm option
  end
=
struct

(*a left-to-right scan of terms1, seeking a term u that is also in terms2*)
fun find_common (terms1,terms2) =
  let val tab2 = fold (Termtab.update o rpair ()) terms2 Termtab.empty
      fun seek [] = raise TERM("find_common", [])
        | seek (u::terms) =
              if Termtab.defined tab2 u then u
              else seek terms
  in seek terms1 end;

(*the simplification procedure*)
fun proc ss t =
  let
    val ctxt = Simplifier.the_context ss;
    val prems = Simplifier.prems_of ss;
    val ([t'], ctxt') = Variable.import_terms true [t] ctxt
    val export = singleton (Variable.export ctxt' ctxt)

    val (t1,t2) = Data.dest_bal t'
    val terms1 = Data.dest_sum t1
    and terms2 = Data.dest_sum t2

    val u = find_common (terms1,terms2)
    val simp_th =
          case Data.simp_conv ss u of NONE => raise TERM("no simp", [])
          | SOME th => th
    val terms1' = Data.find_first u terms1
    and terms2' = Data.find_first u terms2
    and T = Term.fastype_of u

    val t'' = Data.mk_bal (Data.mk_sum T (u::terms1'), Data.mk_sum T (u::terms2'))
    val reshape =
      Goal.prove ctxt [] [] (Data.mk_eq (t', t'')) (K (Data.norm_tac ss))

  in
    SOME (export (Data.simplify_meta_eq ss simp_th reshape))
  end
  (* FIXME avoid handling of generic exceptions *)
  handle TERM _ => NONE
       | TYPE _ => NONE;   (*Typically (if thy doesn't include Numeral)
                             Undeclared type constructor "Numeral.bin"*)

end;
