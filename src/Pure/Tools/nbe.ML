(*  Title:      Pure/nbe.ML
    ID:         $Id$
    Author:     Tobias Nipkow, Florian Haftmann, TU Muenchen

Toplevel theory interface for "normalization by evaluation"
*)

signature NBE =
sig
  (*preconditions: no Vars/TVars in term*)
  val normalization_conv: cterm -> thm
  val lookup: string -> NBE_Eval.Univ
  val update: string * NBE_Eval.Univ -> unit
  val trace: bool ref
end;

structure NBE: NBE =
struct

val trace = ref false;
fun tracing f x = if !trace then (Output.tracing (f x); x) else x;


(** data setup **)

(* preproc and postproc attributes *)

structure NBE_Rewrite = TheoryDataFun
(struct
  val name = "Pure/nbe";
  type T = thm list * thm list

  val empty = ([],[])
  val copy = I;
  val extend = I;

  fun merge _ ((pres1,posts1), (pres2,posts2)) =
    (Library.merge Thm.eq_thm (pres1,pres2), Library.merge Thm.eq_thm (posts1,posts2))

  fun print _ _ = ()
end);

val _ =
  let
    fun map_data f = Context.mapping (NBE_Rewrite.map f) I;
    fun attr_pre (thy, thm) =
      ((map_data o apfst) (insert Thm.eq_thm thm) thy, thm)
    fun attr_post (thy, thm) = 
      ((map_data o apsnd) (insert Thm.eq_thm thm) thy, thm)
    val attr = Attrib.syntax (Scan.lift (Args.$$$ "pre" >> K attr_pre
      || Args.$$$ "post" >> K attr_post));
  in
    Context.add_setup (
      NBE_Rewrite.init
      #> Attrib.add_attributes
          [("normal", attr, "declare rewrite theorems for normalization")]
    )
  end;

fun the_pres thy =
  let
    val ctxt = ProofContext.init thy;
    val pres = (map (LocalDefs.meta_rewrite_rule ctxt) o fst) (NBE_Rewrite.get thy)
  in pres end

fun apply_posts thy =
  let
    val ctxt = ProofContext.init thy;
    val posts = (map (LocalDefs.meta_rewrite_rule ctxt) o snd) (NBE_Rewrite.get thy)
  in MetaSimplifier.rewrite false posts end

(* theorem store *)

structure Funcgr = CodegenFuncgrRetrieval (
  val name = "Pure/nbe_thms";
  val rewrites = the_pres;
);

(* code store *)

structure NBE_Data = CodeDataFun
(struct
  val name = "Pure/mbe";
  type T = NBE_Eval.Univ Symtab.table;
  val empty = Symtab.empty;
  fun merge _ = Symtab.merge (K true);
  fun purge _ _ _ = Symtab.empty;
end);

val _ = Context.add_setup (Funcgr.init #> NBE_Data.init);


(** norm by eval **)

(* sandbox communication *)

val tab : NBE_Eval.Univ Symtab.table ref = ref Symtab.empty;
fun lookup s = (the o Symtab.lookup (!tab)) s;
fun update sx = (tab := Symtab.update sx (!tab));

local

(* function generation *)

fun generate thy funs =
  let
    (* FIXME better turn this into a function
        NBE_Eval.Univ Symtab.table -> NBE_Eval.Univ Symtab.table
        with implicit side effect *)
    fun use_code NONE = ()
      | use_code (SOME s) =
          (tracing (fn () => "\n---generated code:\n" ^ s) ();
           use_text "" (Output.tracing o enclose "\n---compiler echo:\n" "\n---\n",
                Output.tracing o enclose "\n--- compiler echo (with error!):\n" "\n---\n")
            (!trace) s);
    val _ = tracing (fn () => "new definitions: " ^ (commas o maps (map fst)) funs) ();
    val _ = tab := NBE_Data.get thy;;
    val _ = Library.seq (use_code o NBE_Codegen.generate thy
      (fn s => Symtab.defined (!tab) s)) funs;
  in NBE_Data.change thy (K (!tab)) end;

fun ensure_funs thy funcgr t =
  let
    fun consts_of thy t =
      fold_aterms (fn Const c => cons (CodegenConsts.const_of_cexpr thy c) | _ => I) t []
    val consts = consts_of thy t;
    val nbe_tab = NBE_Data.get thy;
  in
    CodegenFuncgr.deps funcgr consts
    |> (map o filter_out) (Symtab.defined nbe_tab o CodegenNames.const thy)
    |> filter_out null
    |> (map o map) (fn c => (CodegenNames.const thy c, CodegenFuncgr.funcs funcgr c))
    |> generate thy
  end;

(* term evaluation *)

fun eval_term thy funcgr t =
  let
    fun subst_Frees [] = I
      | subst_Frees inst =
          Term.map_aterms (fn (t as Free(s, _)) => the_default t (AList.lookup (op =) inst s)
                      | t => t);
    val anno_vars =
      subst_Frees (map (fn (s, T) => (s, Free (s, T))) (Term.add_frees t []))
      #> subst_Vars  (map (fn (ixn, T) => (ixn, Var(ixn,T))) (Term.add_vars t []))
    fun check_tvars t = if null (Term.term_tvars t) then t else
      error ("Illegal schematic type variables in normalized term: "
        ^ setmp show_types true (Sign.string_of_term thy) t);
    val ty = type_of t;
    fun constrain t = Sign.infer_types (Sign.pp thy) thy (Sign.consts_of thy)
      (K NONE) (K NONE) Name.context false ([t], ty) |> fst;
    val _ = ensure_funs thy funcgr t;
  in
    t
    |> tracing (fn t => "Input:\n" ^ Display.raw_string_of_term t)
    |> NBE_Eval.eval thy (!tab)
    |> tracing (fn nt => "Normalized:\n" ^ NBE_Eval.string_of_nterm nt)
    |> NBE_Codegen.nterm_to_term thy
    |> tracing (fn t =>"Converted back:\n" ^ Display.raw_string_of_term t)
    |> anno_vars
    |> tracing (fn t =>"Vars typed:\n" ^ Display.raw_string_of_term t)
    |> constrain
    |> check_tvars
  end;

(* evaluation oracle *)

exception Normalization of CodegenFuncgr.T * term;

fun normalization_oracle (thy, Normalization (funcgr, t)) =
  Logic.mk_equals (t, eval_term thy funcgr t);

fun normalization_invoke thy funcgr t =
  Thm.invoke_oracle_i thy "Pure.normalization" (thy, Normalization (funcgr, t));

in

(* interface *)

fun normalization_conv ct =
  let
    val thy = Thm.theory_of_cterm ct;
    fun mk funcgr drop_classes ct thm1 =
      let
        val t = Thm.term_of ct;
        val thm2 = normalization_invoke thy funcgr t;
        val thm3 = apply_posts thy ((snd o Drule.dest_equals o Thm.cprop_of) thm2);
        val thm23 = drop_classes (Thm.transitive thm2 thm3);
      in
        Thm.transitive thm1 thm23 handle THM _ =>
          error ("normalization_conv - could not construct proof:\n"
          ^ (cat_lines o map string_of_thm) [thm1, thm2, thm3])
      end;
  in fst (Funcgr.make_term thy mk ct) end;

fun norm_print_term ctxt modes t =
  let
    val thy = ProofContext.theory_of ctxt;
    val ct = Thm.cterm_of thy t;
    val (_, t') = (Logic.dest_equals o Thm.prop_of o normalization_conv) ct;
    val ty = Term.type_of t';
    val p = Library.setmp print_mode (modes @ ! print_mode) (fn () =>
      Pretty.block [Pretty.quote (ProofContext.pretty_term ctxt t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (ProofContext.pretty_typ ctxt ty)]) ();
  in Pretty.writeln p end;

fun norm_print_term_e (modes, raw_t) state =
  let val ctxt = Toplevel.context_of state
  in norm_print_term ctxt modes (ProofContext.read_term ctxt raw_t) end;

val _ = Context.add_setup
  (Theory.add_oracle ("normalization", normalization_oracle));

end; (*local*)


(* Isar setup *)

local structure P = OuterParse and K = OuterKeyword in

val opt_modes = Scan.optional (P.$$$ "(" |-- P.!!! (Scan.repeat1 P.xname --| P.$$$ ")")) [];

val nbeP =
  OuterSyntax.improper_command "normal_form" "normalize term by evaluation" K.diag
    (opt_modes -- P.typ >> (Toplevel.keep o norm_print_term_e));

end;

val _ = OuterSyntax.add_parsers [nbeP];

end;
