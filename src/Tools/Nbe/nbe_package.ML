(*  Title:      Tools/Nbe/nbe_package.ML
    ID:         $Id$
    Authors:    Klaus Aehlig, LMU Muenchen; Tobias Nipkow, Florian Haftmann, TU Muenchen

Toplevel theory interface for normalization by evaluation.
*)

signature NBE_PACKAGE =
sig
  val normalization_conv: cterm -> thm
  val setup: theory -> theory
  val trace: bool ref
end;

structure Nbe_Package: NBE_PACKAGE =
struct

val trace = ref false;
fun tracing f x = if !trace then (Output.tracing (f x); x) else x;


(** data setup **)

(* preproc and postproc attributes *)

structure Nbe_Rewrite = TheoryDataFun
(
  type T = thm list * thm list
  val empty = ([], []);
  val copy = I;
  val extend = I;
  fun merge _ ((pres1,posts1), (pres2,posts2)) =
    (Library.merge Thm.eq_thm (pres1,pres2), Library.merge Thm.eq_thm (posts1,posts2))
);

val setup_rewrite =
  let
    fun map_data f = Context.mapping (Nbe_Rewrite.map f) I;
    fun attr_pre (thy, thm) =
      ((map_data o apfst) (insert Thm.eq_thm thm) thy, thm)
    fun attr_post (thy, thm) = 
      ((map_data o apsnd) (insert Thm.eq_thm thm) thy, thm)
    val attr = Attrib.syntax (Scan.lift (Args.$$$ "pre" >> K attr_pre
      || Args.$$$ "post" >> K attr_post));
  in
    Attrib.add_attributes
      [("normal", attr, "declare rewrite theorems for normalization")]
  end;

fun the_pres thy =
  let
    val ctxt = ProofContext.init thy;
    val pres = (map (LocalDefs.meta_rewrite_rule ctxt) o fst) (Nbe_Rewrite.get thy)
  in pres end

fun apply_posts thy =
  let
    val ctxt = ProofContext.init thy;
    val posts = (map (LocalDefs.meta_rewrite_rule ctxt) o snd) (Nbe_Rewrite.get thy)
  in MetaSimplifier.rewrite false posts end

(* theorem store *)

structure Funcgr = CodegenFuncgrRetrieval (val rewrites = the_pres);


(** norm by eval **)

local

fun eval_term thy funcgr t =
  let
    fun subst_Frees [] = I
      | subst_Frees inst =
          Term.map_aterms (fn (t as Free (s, _)) => the_default t (AList.lookup (op =) inst s)
                            | t => t);
    val anno_vars =
      subst_Frees (map (fn (s, T) => (s, Free (s, T))) (Term.add_frees t []))
      #> subst_Vars (map (fn (ixn, T) => (ixn, Var (ixn, T))) (Term.add_vars t []))
    fun check_tvars t = if null (Term.term_tvars t) then t else
      error ("Illegal schematic type variables in normalized term: "
        ^ setmp show_types true (Sign.string_of_term thy) t);
    val ty = type_of t;
    fun constrain t =
      singleton (ProofContext.infer_types_pats (ProofContext.init thy)) (TypeInfer.constrain t ty);
  in
    t
    |> tracing (fn t => "Input:\n" ^ Display.raw_string_of_term t)
    |> Nbe_Eval.eval thy
    |> tracing (fn t => "Normalized:\n" ^ setmp show_types true Display.raw_string_of_term t)
    |> tracing (fn _ => "Term type:\n" ^ Display.raw_string_of_typ ty)
    |> anno_vars
    |> tracing (fn t => "Vars typed:\n" ^ setmp show_types true Display.raw_string_of_term t)
    |> tracing (fn t => setmp show_types true (Sign.string_of_term thy) t)
    |> constrain
    |> tracing (fn t => "Types inferred:\n" ^ setmp show_types true Display.raw_string_of_term t)
    |> check_tvars
  end;

(* evaluation oracle *)

exception Normalization of CodegenFuncgr.T * term;

fun normalization_oracle (thy, Normalization (funcgr, t)) =
  Logic.mk_equals (t, eval_term thy funcgr t);

fun normalization_invoke thy funcgr t =
  Thm.invoke_oracle_i thy "Nbe.normalization" (thy, Normalization (funcgr, t));

in

(* interface *)

val setup_oracle = Theory.add_oracle ("normalization", normalization_oracle)

fun normalization_conv ct =
  let
    val thy = Thm.theory_of_cterm ct;
    fun mk funcgr drop_classes ct thm1 =
      let
        val t = Thm.term_of ct;
        val thm2 = normalization_invoke thy funcgr t;
        val thm3 = apply_posts thy (Thm.rhs_of thm2);
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

fun norm_print_term_cmd (modes, raw_t) state =
  let val ctxt = Toplevel.context_of state
  in norm_print_term ctxt modes (ProofContext.read_term ctxt raw_t) end;

end; (*local*)


(* Isar setup *)

local structure P = OuterParse and K = OuterKeyword in

val opt_modes = Scan.optional (P.$$$ "(" |-- P.!!! (Scan.repeat1 P.xname --| P.$$$ ")")) [];

val nbeP =
  OuterSyntax.improper_command "normal_form" "normalize term by evaluation" K.diag
    (opt_modes -- P.typ >> (Toplevel.keep o norm_print_term_cmd));

end;

val setup = setup_rewrite #> setup_oracle;

val _ = OuterSyntax.add_parsers [nbeP];

end;
