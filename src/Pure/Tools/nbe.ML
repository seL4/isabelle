(*  ID:         $Id$
    Author:     Tobias Nipkow, Florian Haftmann, TU Muenchen

Toplevel theory interface for "normalization by evaluation"
Preconditions: no Vars
*)

signature NBE =
sig
  val norm_by_eval_i: term -> theory -> term * theory;
  val lookup: string -> NBE_Eval.Univ;
  val update: string * NBE_Eval.Univ -> unit
  val trace_nbe: bool ref
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

val trace_nbe = ref false;

fun nbe_trace fs = if !trace_nbe then tracing(fs()) else ();

val _ = Context.add_setup NBE_Data.init;

val tab : NBE_Eval.Univ Symtab.table ref = ref Symtab.empty;
fun lookup s = (the o Symtab.lookup (!tab)) s;
fun update sx = (tab := Symtab.update sx (!tab));
fun defined s = Symtab.defined (!tab) s;

fun use_show "" = ()
  | use_show s =
 (if !trace_nbe then tracing ("\n---generated code:\n"^ s) else ();
  use_text(tracing o enclose "\n---compiler echo:\n" "\n---\n",
           tracing o enclose "\n--- compiler echo (with error!):\n" "\n---\n")
      (!trace_nbe) s);

(* FIXME move to term.ML *)
fun subst_Frees [] tm = tm
  | subst_Frees inst tm =
      let
        fun subst (t as Free(s, _)) = the_default t (AList.lookup (op =) inst s)
          | subst (Abs (a, T, t)) = Abs (a, T, subst t)
          | subst (t $ u) = subst t $ subst u
          | subst t = t;
      in subst tm end;

fun var_tab t = (Term.add_frees t [], Term.add_vars t []);

fun anno_vars (Ftab,Vtab) =
  subst_Vars  (map (fn (ixn,T) => (ixn, Var(ixn,T))) Vtab) o
  subst_Frees (map (fn (s,T) =>   (s,   Free(s,T)))  Ftab)

(* FIXME try to use isar_cmd/print_term to take care of context *)
fun norm_by_eval_i t thy =
  let
    val nbe_tab = NBE_Data.get thy;
    val modl_old = CodegenThingol.project_module (Symtab.keys nbe_tab)
      (CodegenPackage.get_root_module thy);
    val (t', thy') = CodegenPackage.codegen_term t thy;
    val modl_new = CodegenPackage.get_root_module thy';
    val diff = CodegenThingol.diff_module (modl_new, modl_old);
    val _ = nbe_trace (fn() => "new definitions: " ^ (commas o map fst) diff);
    val _ = (tab := nbe_tab;
             Library.seq (use_show o NBE_Codegen.generate defined) diff);
    val thy'' = NBE_Data.put (!tab) thy';
    val nt' = NBE_Eval.nbe (!tab) t';
    val _ = nbe_trace (fn() => "Input:\n" ^ Display.raw_string_of_term t)
    val _ =  nbe_trace (fn()=> "Normalized:\n" ^ NBE_Eval.string_of_nterm nt');
    val t' = NBE_Codegen.nterm_to_term thy'' nt';
    val _ = nbe_trace (fn()=>"Converted back:\n" ^ Display.raw_string_of_term t');
    val t'' = anno_vars (var_tab t) t';
    val _ = nbe_trace (fn()=>"Vars typed:\n" ^ Display.raw_string_of_term t'');
    val ty = type_of t;
    val (t''', _) =
      Sign.infer_types (Sign.pp thy) thy (Sign.consts_of thy) (K NONE) (K NONE)
        [] false ([t''], ty);
    val s = Pretty.string_of
      (Pretty.block [Pretty.quote (Sign.pretty_term thy'' t'''), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Sign.pretty_typ thy'' ty)])
    val _ = writeln s
  in  (t''', thy'')  end;

fun norm_by_eval raw_t thy = norm_by_eval_i (Sign.read_term thy raw_t) thy;

structure P = OuterParse and K = OuterKeyword;

val nbeP =
  OuterSyntax.command "normal_form" "normalization by evaluation" K.thy_decl
    (P.term >> (fn t => Toplevel.theory (snd o norm_by_eval t)));

val _ = OuterSyntax.add_parsers [nbeP];

end;
