(*  ID:         $Id$
    Author:     Tobias Nipkow, Florian Haftmann, TU Muenchen

Toplevel theory interface for "normalization by evaluation"
Preconditions: no Vars
*)

signature NBE =
sig
  val norm_term: theory -> term -> term
  val lookup: string -> NBE_Eval.Univ
  val update: string * NBE_Eval.Univ -> unit
  val trace_nbe: bool ref
end;

structure NBE: NBE =
struct


(* theory data setup *)

structure NBE_Data = TheoryDataFun
(struct
  val name = "Pure/NBE"
  type T = NBE_Eval.Univ Symtab.table
  val empty = Symtab.empty
  val copy = I
  val extend = I
  fun merge _ = Symtab.merge (K true)
  fun print _ _ = ()
end);

val _ = Context.add_setup NBE_Data.init;


(* sandbox communication *)

val tab : NBE_Eval.Univ Symtab.table ref = ref Symtab.empty;
fun lookup s = (the o Symtab.lookup (!tab)) s;
fun update sx = (tab := Symtab.update sx (!tab));
fun defined s = Symtab.defined (!tab) s;


(* FIXME replace by Term.map_aterms *)
fun subst_Frees [] tm = tm
  | subst_Frees inst tm =
      let
        fun subst (t as Free(s, _)) = the_default t (AList.lookup (op =) inst s)
          | subst (Abs (a, T, t)) = Abs (a, T, subst t)
          | subst (t $ u) = subst t $ subst u
          | subst t = t;
      in subst tm end;

fun var_tab t = (Term.add_frees t [], Term.add_vars t []);

fun anno_vars (Ftab, Vtab) =
  subst_Vars  (map (fn (ixn, T) => (ixn, Var(ixn,T))) Vtab) o
  subst_Frees (map (fn (s, T) =>   (s,   Free(s,T)))  Ftab)


(* debugging *)

val trace_nbe = ref false;

fun trace f = if !trace_nbe then tracing (f ()) else ();

(* FIXME better turn this into a function
    NBE_Eval.Univ Symtab.table -> NBE_Eval.Univ Symtab.table
    with implicit side effect *)
fun use_code "" = ()
  | use_code s =
      (if !trace_nbe then tracing ("\n---generated code:\n"^ s) else ();
       use_text(tracing o enclose "\n---compiler echo:\n" "\n---\n",
            tracing o enclose "\n--- compiler echo (with error!):\n" "\n---\n")
        (!trace_nbe) s);


(* norm by eval *)

(* FIXME try to use isar_cmd/print_term to take care of context *)
fun norm_print t thy =
  let
    val _ = trace (fn () => "Input:\n" ^ Display.raw_string_of_term t);
    fun compile_term t thy =
      let
        val (modl_this, thy') = CodegenPackage.get_root_module thy;
        val nbe_tab = NBE_Data.get thy';
        val modl_old = CodegenThingol.project_module (Symtab.keys nbe_tab) modl_this;
        val (t', thy'') = CodegenPackage.codegen_term t thy';
        val (modl_new, thy''') = CodegenPackage.get_root_module thy'';
        val diff = CodegenThingol.diff_module (modl_new, modl_old);
        val _ = trace (fn () => "new definitions: " ^ (commas o map fst) diff);
        val _ = (tab := nbe_tab;
             Library.seq (use_code o NBE_Codegen.generate defined) diff);
        val thy'''' = NBE_Data.put (!tab) thy''';
        val nt' = NBE_Eval.nbe (!tab) t';
      in (nt', thy'''') end;
    fun eval_term t nt thy =
      let
        val vtab = var_tab t;
        val ty = type_of t;
        fun restrain ty t = Sign.infer_types (Sign.pp thy) thy (Sign.consts_of thy)
            (K NONE) (K NONE)
            [] false ([t], ty) |> fst;
        val _ = trace (fn () => "Normalized:\n" ^ NBE_Eval.string_of_nterm nt);
        val t' = NBE_Codegen.nterm_to_term thy nt;
        val _ = trace (fn () =>"Converted back:\n" ^ Display.raw_string_of_term t');
        val t'' = anno_vars vtab t';
        val _ = trace (fn () =>"Vars typed:\n" ^ Display.raw_string_of_term t'');
        val t''' = restrain ty t''
        val s = Pretty.string_of
            (Pretty.block [Pretty.quote (Sign.pretty_term thy t'''), Pretty.fbrk,
                Pretty.str "::", Pretty.brk 1, Pretty.quote (Sign.pretty_typ thy ty)])
        val _ = writeln s
      in (t''', thy) end;
  in
    thy
    |> compile_term t
    |-> (fn nt => eval_term t nt)
  end;

fun norm_print' s thy = norm_print (Sign.read_term thy s) thy;

fun norm_term thy t = fst (norm_print t (Theory.copy thy));


(* Isar setup *)

local structure P = OuterParse and K = OuterKeyword in

val nbeP =
  OuterSyntax.command "normal_form" "normalization by evaluation" K.thy_decl
    (P.term >> (fn s => Toplevel.theory (snd o norm_print' s)));

end;

val _ = OuterSyntax.add_parsers [nbeP];

end;
