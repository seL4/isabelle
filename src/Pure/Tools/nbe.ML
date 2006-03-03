(*  ID:         $Id$
    Author:     Tobias Nipkow, Florian Haftmann, TU Muenchen

Toplevel theory interface for "normalization by evaluation"
*)

signature NBE =
sig
  val norm_by_eval_i: term -> theory -> term * theory;
  val lookup: string -> NBE_Eval.Univ;
  val update: string * NBE_Eval.Univ -> unit;
end;

structure NBE: NBE =
struct

structure NBE_Data = TheoryDataFun
(struct
  val name = "Pure/NBE";
  type T = NBE_Eval.Univ Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ = Symtab.merge (K true);
  fun print _ _ = ();
end);

val _ = Context.add_setup NBE_Data.init;

val tab : NBE_Eval.Univ Symtab.table ref = ref Symtab.empty;
fun lookup s = (the o Symtab.lookup (!tab)) s;
fun update sx = (tab := Symtab.update sx (!tab));
fun defined s = Symtab.defined (!tab) s;

fun use_show s = (writeln ("\n---generated code:\n"^ s);
     use_text(writeln o enclose "\n---compiler echo:\n" "\n---\n",
              writeln o enclose "\n--- compiler echo (with error!):\n" 
                                "\n---\n")
      true s);

fun norm_by_eval_i t thy =
  let
    val nbe_tab = NBE_Data.get thy;
    val modl_old = CodegenThingol.partof (Symtab.keys nbe_tab)
      (CodegenPackage.get_root_module thy);
    val (t', thy') = CodegenPackage.codegen_term t thy;
    val modl_new = CodegenPackage.get_root_module thy';
    val diff = CodegenThingol.diff_module (modl_new, modl_old);
    val _ = writeln ("new definitions: " ^ (commas o map fst) diff);
    val _ = (tab := nbe_tab;
             Library.seq (use_show o NBE_Codegen.generate defined) diff);
    val thy'' = NBE_Data.put (!tab) thy';
    val nt' = NBE_Eval.nbe (!tab) t';
    val _ = print nt';
    val t' = NBE_Codegen.nterm_to_term thy'' nt';
(*
    val _ = print t';
    val (t'', _) =
      Sign.infer_types (Sign.pp thy) thy (Sign.consts_of thy) (K NONE) (K NONE)
        [] true ([t'], type_of t);
*)
    val _ = (Pretty.writeln o Sign.pretty_term thy'') t';
  in
    (t', thy'')
  end;

fun norm_by_eval raw_t thy = norm_by_eval_i (Sign.read_term thy raw_t) thy;

structure P = OuterParse and K = OuterKeyword;

val nbeP =
  OuterSyntax.command "norm_by_eval" "normalization by evaluation" K.thy_decl
    (P.term >> (fn t => Toplevel.theory (snd o norm_by_eval t)));

val _ = OuterSyntax.add_parsers [nbeP];

end;
