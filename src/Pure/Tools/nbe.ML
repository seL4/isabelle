(*  ID:         $Id$
    Author:     Tobias Nipkow, Florian Haftmann, TU Muenchen

Installing "normalization by evaluation"
*)

signature NORMBYEVAL =
sig
  val lookup: string -> NBE_Eval.Univ
  val update: string * NBE_Eval.Univ -> unit
end;

structure NormByEval:NORMBYEVAL =
struct

structure NBE_Data = TheoryDataFun
(struct
  val name = "Pure/NormByEval";
  type T = NBE_Eval.Univ Symtab.table
  val empty = Symtab.empty
  val copy = I;
  val extend = I;
  fun merge _ = Symtab.merge (K true)
  fun print _ _ = ();
end);

val _ = Context.add_setup NBE_Data.init;

fun use_show s = (writeln ("\n---generated code:\n"^ s);
     use_text(writeln o enclose "\n---compiler echo:\n" "\n---\n",
              writeln o enclose "\n--- compiler echo (with error!):\n" 
                                "\n---\n")
      true s);

val tab = ref Symtab.empty
fun lookup s = the(Symtab.lookup (!tab) s)
fun update sx = (tab := Symtab.update sx (!tab))
fun defined s = Symtab.defined (!tab) s;

fun top_nbe st thy =
let val t = Sign.read_term thy st
    val ((t',diff),thy') = CodegenPackage.codegen_incr t thy
    val _ = (tab := NBE_Data.get thy;
             Library.seq (use_show o NBE_Codegen.generate defined) diff)
    val thy'' = NBE_Data.put (!tab) thy'
    val nt' = NBE_Eval.nbe (!tab) t'
    val _ = print nt'
in
  thy''
end

structure P = OuterParse and K = OuterKeyword;

val nbeP =
  OuterSyntax.command "norm_by_eval" "norm by eval" K.thy_decl
    (P.term >> (Toplevel.theory o top_nbe));

val _ = OuterSyntax.add_parsers [nbeP];
(*
ProofGeneral.write_keywords "nbe";
*)
(* isar-keywords-nbe.el -> isabelle/etc/
   Isabelle -k nbe *)

end


(*
fun to_term xs (C s) = Const(s,dummyT)
  | to_term xs (V s) = Free(s,dummyT)
  | to_term xs (B i) = Bound (find_index_eq i xs)
  | to_term xs (A(t1,t2)) = to_term xs t1 $ to_term xs t2
  | to_term xs (AbsN(i,t)) = Abs("u",dummyT,to_term (i::xs) t);
*)
