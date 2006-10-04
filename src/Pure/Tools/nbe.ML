(*  Title:      Pure/nbe.ML
    ID:         $Id$
    Author:     Tobias Nipkow, Florian Haftmann, TU Muenchen

Toplevel theory interface for "normalization by evaluation"
*)

signature NBE =
sig
  (*preconditions: no Vars/TVars in term*)
  val norm_term: theory -> term -> term
  val normalization_conv: cterm -> thm
  val lookup: string -> NBE_Eval.Univ
  val update: string * NBE_Eval.Univ -> unit
  val trace: bool ref
end;

structure NBE: NBE =
struct

val trace = ref false;
fun tracing f = if !trace then Output.tracing (f ()) else ();


(* theory data setup *)

structure NBE_Data = CodeDataFun
(struct
  val name = "Pure/NBE"
  type T = NBE_Eval.Univ Symtab.table
  val empty = Symtab.empty
  fun merge _ = Symtab.merge (K true)
  fun purge _ _ = Symtab.empty
end);

val _ = Context.add_setup NBE_Data.init;


(* sandbox communication *)

val tab : NBE_Eval.Univ Symtab.table ref = ref Symtab.empty;
fun lookup s = (the o Symtab.lookup (!tab)) s;
fun update sx = (tab := Symtab.update sx (!tab));


(* norm by eval *)

local

(* FIXME better turn this into a function
    NBE_Eval.Univ Symtab.table -> NBE_Eval.Univ Symtab.table
    with implicit side effect *)
fun use_code NONE = ()
  | use_code (SOME s) =
      (tracing (fn () => "\n---generated code:\n" ^ s);
       use_text (Output.tracing o enclose "\n---compiler echo:\n" "\n---\n",
            Output.tracing o enclose "\n--- compiler echo (with error!):\n" "\n---\n")
        (!trace) s);

fun generate thy funs =
  let
    val _ = tab := NBE_Data.get thy;;
    val _ = Library.seq (use_code o NBE_Codegen.generate thy
      (fn s => Symtab.defined (!tab) s)) funs;
  in NBE_Data.change thy (K (!tab)) end;

fun compile_term thy t =
  let
    (*FIXME: proper interfaces in codegen_*)
    val (consts, cs) = CodegenConsts.consts_of thy t;
    val funcgr = CodegenFuncgr.mk_funcgr thy consts cs;
    (*FIXME: proper interfaces in codegen_*)
    fun const_typ (c, ty) =
      let
        val const = CodegenConsts.norm_of_typ thy (c, ty);
      in case CodegenFuncgr.get_funcs funcgr const
       of (thm :: _) => CodegenData.typ_func thy thm
        | [] => Sign.the_const_type thy c
      end;
    val (_, ct) = CodegenData.preprocess_cterm thy const_typ (Thm.cterm_of thy t)
    val t' = Thm.term_of ct;
    val (consts, cs) = CodegenConsts.consts_of thy t';
    val funcgr = CodegenFuncgr.mk_funcgr thy consts cs;
    val nbe_tab = NBE_Data.get thy;
    val all_consts =
      CodegenFuncgr.all_deps_of funcgr consts
      |> (map o filter_out) (Symtab.defined nbe_tab o CodegenNames.const thy)
      |> filter_out null;
    val funs = (map o map)
      (fn c => (CodegenNames.const thy c, CodegenFuncgr.get_funcs funcgr c)) all_consts;
    val _ = tracing (fn () => "new definitions: " ^ (commas o maps (map fst)) funs);
    val _ = generate thy funs;
    val nt = NBE_Eval.eval thy (!tab) t';
  in nt end;

fun subst_Frees [] = I
  | subst_Frees inst =
      Term.map_aterms (fn (t as Free(s, _)) => the_default t (AList.lookup (op =) inst s)
                  | t => t);

fun var_tab t = (Term.add_frees t [], Term.add_vars t []);

fun anno_vars (Ftab, Vtab) =
  subst_Vars  (map (fn (ixn, T) => (ixn, Var(ixn,T))) Vtab) o
  subst_Frees (map (fn (s, T) =>   (s,   Free(s,T)))  Ftab)

in

fun norm_term thy t =
  let
    val _ = tracing (fn () => "Input:\n" ^ Display.raw_string_of_term t);
    val nt = compile_term thy t;
    val vtab = var_tab t;
    val ty = type_of t;
    fun constrain ty t = Sign.infer_types (Sign.pp thy) thy (Sign.consts_of thy)
        (K NONE) (K NONE) Name.context false ([t], ty) |> fst;
    val _ = tracing (fn () => "Normalized:\n" ^ NBE_Eval.string_of_nterm nt);
    val t' = NBE_Codegen.nterm_to_term thy nt;
    val _ = tracing (fn () =>"Converted back:\n" ^ Display.raw_string_of_term t');
    val t'' = anno_vars vtab t';
    val _ = tracing (fn () =>"Vars typed:\n" ^ Display.raw_string_of_term t'');
    val t''' = constrain ty t'';
    val _ = if null (Term.term_tvars t''') then () else
      error ("Illegal schematic type variables in normalized term: "
        ^ setmp show_types true (Sign.string_of_term thy) t''');
  in t''' end;

fun norm_print_term ctxt modes t =
  let
    val thy = ProofContext.theory_of ctxt;
    val t' = norm_term thy t;
    val ty = Term.type_of t';
    val p = Library.setmp print_mode (modes @ ! print_mode) (fn () =>
      Pretty.block [Pretty.quote (ProofContext.pretty_term ctxt t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (ProofContext.pretty_typ ctxt ty)]) ();
  in Pretty.writeln p end;

fun norm_print_term_e (modes, raw_t) state =
  let
    val ctxt = (Proof.context_of o Toplevel.enter_forward_proof) state;
  in norm_print_term ctxt modes (ProofContext.read_term ctxt raw_t) end;

end; (*local*)


(* normalization oracle *)

exception Normalization of term;

fun normalization_oracle (thy, Normalization t) =
  Logic.mk_equals (t, norm_term thy t);

fun normalization_conv ct =
  let val {sign, t, ...} = rep_cterm ct
  in Thm.invoke_oracle_i sign "Pure.normalization" (sign, Normalization t) end;

val _ = Context.add_setup
  (Theory.add_oracle ("normalization", normalization_oracle));


(* Isar setup *)

local structure P = OuterParse and K = OuterKeyword in

val opt_modes = Scan.optional (P.$$$ "(" |-- P.!!! (Scan.repeat1 P.xname --| P.$$$ ")")) [];

val nbeP =
  OuterSyntax.improper_command "normal_form" "normalize term by evaluation" K.diag
    (opt_modes -- P.typ >> (Toplevel.keep o norm_print_term_e));

end;

val _ = OuterSyntax.add_parsers [nbeP];

end;
