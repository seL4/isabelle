(*  Title:      Tools/nbe.ML
    ID:         $Id$
    Authors:    Klaus Aehlig, LMU Muenchen; Tobias Nipkow, Florian Haftmann, TU Muenchen

Normalization by evaluation, based on generic code generator.
*)

signature NBE =
sig
  datatype Univ = 
      Const of string * Univ list            (*named (uninterpreted) constants*)
    | Free of string * Univ list
    | BVar of int * Univ list
    | Abs of (int * (Univ list -> Univ)) * Univ list;
  val free: string -> Univ list -> Univ       (*free (uninterpreted) variables*)
  val abs: int -> (Univ list -> Univ) -> Univ list -> Univ
                                            (*abstractions as functions*)
  val app: Univ -> Univ -> Univ              (*explicit application*)

  val univs_ref: (unit -> Univ list) ref 
  val lookup_fun: string -> Univ

  val norm_conv: cterm -> thm
  val norm_term: theory -> term -> term

  val trace: bool ref
  val setup: theory -> theory
end;

structure Nbe: NBE =
struct

(* generic non-sense *)

val trace = ref false;
fun tracing f x = if !trace then (Output.tracing (f x); x) else x;


(** the semantical universe **)

(*
   Functions are given by their semantical function value. To avoid
   trouble with the ML-type system, these functions have the most
   generic type, that is "Univ list -> Univ". The calling convention is
   that the arguments come as a list, the last argument first. In
   other words, a function call that usually would look like

   f x_1 x_2 ... x_n   or   f(x_1,x_2, ..., x_n)

   would be in our convention called as

              f [x_n,..,x_2,x_1]

   Moreover, to handle functions that are still waiting for some
   arguments we have additionally a list of arguments collected to far
   and the number of arguments we're still waiting for.
*)

datatype Univ = 
    Const of string * Univ list        (*named (uninterpreted) constants*)
  | Free of string * Univ list         (*free variables*)
  | BVar of int * Univ list            (*bound named variables*)
  | Abs of (int * (Univ list -> Univ)) * Univ list
                                      (*abstractions as closures*);

(* constructor functions *)

val free = curry Free;
fun abs n f ts = Abs ((n, f), ts);
fun app (Abs ((1, f), xs)) x = f (x :: xs)
  | app (Abs ((n, f), xs)) x = Abs ((n - 1, f), x :: xs)
  | app (Const (name, args)) x = Const (name, x :: args)
  | app (Free (name, args)) x = Free (name, x :: args)
  | app (BVar (name, args)) x = BVar (name, x :: args);

(* global functions store *)

structure Nbe_Functions = CodeDataFun
(
  type T = Univ Graph.T;
  val empty = Graph.empty;
  fun merge _ = Graph.merge (K true);
  fun purge _ NONE _ = Graph.empty
    | purge NONE _ _ = Graph.empty
    | purge (SOME thy) (SOME cs) gr = Graph.empty
        (*let
          val cs_exisiting =
            map_filter (CodeName.const_rev thy) (Graph.keys gr);
          val dels = (Graph.all_preds gr
              o map (CodeName.const thy)
              o filter (member (op =) cs_exisiting)
            ) cs;
        in Graph.del_nodes dels gr end*);
);

fun defined gr = can (Graph.get_node gr);

(* sandbox communication *)

val univs_ref = ref (fn () => [] : Univ list);

local

val gr_ref = ref NONE : Nbe_Functions.T option ref;

in

fun lookup_fun s = case ! gr_ref
 of NONE => error "compile_univs"
  | SOME gr => Graph.get_node gr s;

fun compile_univs tab ([], _) = []
  | compile_univs tab (cs, raw_s) =
      let
        val _ = univs_ref := (fn () => []);
        val s = "Nbe.univs_ref := " ^ raw_s;
        val _ = tracing (fn () => "\n--- generated code:\n" ^ s) ();
        val _ = gr_ref := SOME tab;
        val _ = use_text "" (Output.tracing o enclose "\n---compiler echo:\n" "\n---\n",
          Output.tracing o enclose "\n--- compiler echo (with error):\n" "\n---\n")
          (!trace) s;
        val _ = gr_ref := NONE;
        val univs = case !univs_ref () of [] => error "compile_univs" | univs => univs;
      in cs ~~ univs end;

end; (*local*)


(** assembling and compiling ML code from terms **)

(* abstract ML syntax *)

infix 9 `$` `$$`;
fun e1 `$` e2 = "(" ^ e1 ^ " " ^ e2 ^ ")";
fun e `$$` es = "(" ^ e ^ " " ^ space_implode " " es ^ ")";
fun ml_abs v e = "(fn " ^ v ^ " => " ^ e ^ ")";

fun ml_Val v s = "val " ^ v ^ " = " ^ s;
fun ml_cases t cs =
  "(case " ^ t ^ " of " ^ space_implode " | " (map (fn (p, t) => p ^ " => " ^ t) cs) ^ ")";
fun ml_Let ds e = "let\n" ^ space_implode "\n" ds ^ " in " ^ e ^ " end";

fun ml_list es = "[" ^ commas es ^ "]";

val ml_delay = ml_abs "()"

fun ml_fundefs ([(name, [([], e)])]) =
      "val " ^ name ^ " = " ^ e ^ "\n"
  | ml_fundefs (eqs :: eqss) =
      let
        fun fundef (name, eqs) =
          let
            fun eqn (es, e) = name ^ " " ^ space_implode " " es ^ " = " ^ e
          in space_implode "\n  | " (map eqn eqs) end;
      in
        (prefix "fun " o fundef) eqs :: map (prefix "and " o fundef) eqss
        |> space_implode "\n"
        |> suffix "\n"
      end;

(* nbe specific syntax *)

local
  val prefix =          "Nbe.";
  val name_const =      prefix ^ "Const";
  val name_free =       prefix ^ "free";
  val name_abs =        prefix ^ "abs";
  val name_app =        prefix ^ "app";
  val name_lookup_fun = prefix ^ "lookup_fun";
in

fun nbe_const c ts = name_const `$` ("(" ^ ML_Syntax.print_string c ^ ", " ^ ml_list ts ^ ")");
fun nbe_fun c = "c_" ^ translate_string (fn "." => "_" | c => c) c;
fun nbe_free v = name_free `$$` [ML_Syntax.print_string v, ml_list []];
fun nbe_bound v = "v_" ^ v;

fun nbe_apps e es =
  Library.foldr (fn (s, e) => name_app `$$` [e, s]) (es, e);

fun nbe_abss 0 f = f `$` ml_list []
  | nbe_abss n f = name_abs `$$` [string_of_int n, f, ml_list []];

fun nbe_lookup c = ml_Val (nbe_fun c) (name_lookup_fun `$` ML_Syntax.print_string c);

val nbe_value = "value";

end;

open BasicCodeThingol;

(* greetings to Tarski *)

fun assemble_iterm thy is_fun num_args =
  let
    fun of_iterm t =
      let
        val (t', ts) = CodeThingol.unfold_app t
      in of_iapp t' (fold (cons o of_iterm) ts []) end
    and of_iconst c ts = case num_args c
     of SOME n => if n <= length ts
          then let val (args2, args1) = chop (length ts - n) ts
          in nbe_apps (nbe_fun c `$` ml_list args1) args2
          end else nbe_const c ts
      | NONE => if is_fun c then nbe_apps (nbe_fun c) ts
          else nbe_const c ts
    and of_iapp (IConst (c, (dss, _))) ts = of_iconst c ts
      | of_iapp (IVar v) ts = nbe_apps (nbe_bound v) ts
      | of_iapp ((v, _) `|-> t) ts =
          nbe_apps (nbe_abss 1 (ml_abs (ml_list [nbe_bound v]) (of_iterm t))) ts
      | of_iapp (ICase (((t, _), cs), t0)) ts =
          nbe_apps (ml_cases (of_iterm t) (map (pairself of_iterm) cs
            @ [("_", of_iterm t0)])) ts
  in of_iterm end;

fun assemble_fun thy is_fun num_args (c, eqns) =
  let
    val assemble_arg = assemble_iterm thy (K false) (K NONE);
    val assemble_rhs = assemble_iterm thy is_fun num_args;
    fun assemble_eqn (args, rhs) =
      ([ml_list (map assemble_arg (rev args))], assemble_rhs rhs);
    val default_params = map nbe_bound
      (Name.invent_list [] "a" ((the o num_args) c));
    val default_eqn = ([ml_list default_params], nbe_const c default_params);
  in map assemble_eqn eqns @ [default_eqn] end;

fun assemble_eqnss thy is_fun ([], deps) = ([], "")
  | assemble_eqnss thy is_fun (eqnss, deps) =
      let
        val cs = map fst eqnss;
        val num_args = cs ~~ map (fn (_, (args, rhs) :: _) => length args) eqnss;
        val funs = fold (fold (CodeThingol.fold_constnames
          (insert (op =))) o map snd o snd) eqnss [];
        val bind_funs = map nbe_lookup (filter is_fun funs);
        val bind_locals = ml_fundefs (map nbe_fun cs ~~ map
          (assemble_fun thy is_fun (AList.lookup (op =) num_args)) eqnss);
        val result = ml_list (map (fn (c, n) => nbe_abss n (nbe_fun c)) num_args)
          |> ml_delay;
      in (cs, ml_Let (bind_funs @ [bind_locals]) result) end;

fun assemble_eval thy is_fun (((vs, ty), t), deps) =
  let
    val funs = CodeThingol.fold_constnames (insert (op =)) t [];
    val frees = CodeThingol.fold_unbound_varnames (insert (op =)) t [];
    val bind_funs = map nbe_lookup (filter is_fun funs);
    val bind_value = ml_fundefs [(nbe_value, [([ml_list (map nbe_bound frees)],
      assemble_iterm thy is_fun (K NONE) t)])];
    val result = ml_list [nbe_value `$` ml_list (map nbe_free frees)]
      |> ml_delay;
  in ([nbe_value], ml_Let (bind_funs @ [bind_value]) result) end;

fun eqns_of_stmt ((_, CodeThingol.Fun (_, [])), _) =
      NONE
  | eqns_of_stmt ((name, CodeThingol.Fun (_, eqns)), deps) =
      SOME ((name, map fst eqns), deps)
  | eqns_of_stmt ((_, CodeThingol.Datatypecons _), _) =
      NONE
  | eqns_of_stmt ((_, CodeThingol.Datatype _), _) =
      NONE
  | eqns_of_stmt ((_, CodeThingol.Class _), _) =
      NONE
  | eqns_of_stmt ((_, CodeThingol.Classrel _), _) =
      NONE
  | eqns_of_stmt ((_, CodeThingol.Classparam _), _) =
      NONE
  | eqns_of_stmt ((_, CodeThingol.Classinst _), _) =
      NONE;

fun compile_stmts thy is_fun =
  map_filter eqns_of_stmt
  #> split_list
  #> assemble_eqnss thy is_fun
  #> compile_univs (Nbe_Functions.get thy);

fun eval_term thy is_fun =
  assemble_eval thy is_fun
  #> compile_univs (Nbe_Functions.get thy)
  #> the_single
  #> snd;


(** compilation and evaluation **)

(* ensure global functions *)

fun ensure_funs thy code =
  let
    fun add_dep (name, dep) gr =
      if can (Graph.get_node gr) name andalso can (Graph.get_node gr) dep
      then Graph.add_edge (name, dep) gr else gr;
    fun compile' stmts gr =
      let
        val compiled = compile_stmts thy (defined gr) stmts;
        val names = map (fst o fst) stmts;
        val deps = maps snd stmts;
      in
        Nbe_Functions.change thy (fold Graph.new_node compiled
          #> fold (fn name => fold (curry add_dep name) deps) names)
      end;
    val nbe_gr = Nbe_Functions.get thy;
    val stmtss = rev (Graph.strong_conn code)
      |> (map o map_filter) (fn name => if defined nbe_gr name
           then NONE
           else SOME ((name, Graph.get_node code name), Graph.imm_succs code name))
      |> filter_out null
  in fold compile' stmtss nbe_gr end;

(* reification *)

fun term_of_univ thy t =
  let
    fun of_apps bounds (t, ts) =
      fold_map (of_univ bounds) ts
      #>> (fn ts' => list_comb (t, rev ts'))
    and of_univ bounds (Const (name, ts)) typidx =
          let
            val SOME c = CodeName.const_rev thy name;
            val T = Code.default_typ thy c;
            val T' = map_type_tvar (fn ((v, i), S) => TypeInfer.param (typidx + i) (v, S)) T;
            val typidx' = typidx + maxidx_of_typ T' + 1;
          in of_apps bounds (Term.Const (c, T'), ts) typidx' end
      | of_univ bounds (Free (name, ts)) typidx =
          of_apps bounds (Term.Free (name, dummyT), ts) typidx
      | of_univ bounds (BVar (name, ts)) typidx =
          of_apps bounds (Bound (bounds - name - 1), ts) typidx
      | of_univ bounds (t as Abs _) typidx =
          typidx
          |> of_univ (bounds + 1) (app t (BVar (bounds, [])))
          |-> (fn t' => pair (Term.Abs ("u", dummyT, t')))
  in of_univ 0 t 0 |> fst end;

(* evaluation with type reconstruction *)

fun eval thy code t vs_ty_t deps =
  let
    val ty = type_of t;
    fun subst_Frees [] = I
      | subst_Frees inst =
          Term.map_aterms (fn (t as Term.Free (s, _)) => the_default t (AList.lookup (op =) inst s)
                            | t => t);
    val anno_vars =
      subst_Frees (map (fn (s, T) => (s, Term.Free (s, T))) (Term.add_frees t []))
      #> subst_Vars (map (fn (ixn, T) => (ixn, Var (ixn, T))) (Term.add_vars t []))
    fun constrain t =
      singleton (Syntax.check_terms (ProofContext.init thy)) (TypeInfer.constrain ty t);
    fun check_tvars t = if null (Term.term_tvars t) then t else
      error ("Illegal schematic type variables in normalized term: "
        ^ setmp show_types true (Sign.string_of_term thy) t);
  in
    (vs_ty_t, deps)
    |> eval_term thy (defined (ensure_funs thy code))
    |> term_of_univ thy
    |> tracing (fn t => "Normalized:\n" ^ setmp show_types true Display.raw_string_of_term t)
    |> anno_vars
    |> tracing (fn t => "Vars typed:\n" ^ setmp show_types true Display.raw_string_of_term t)
    |> constrain
    |> tracing (fn t => "Types inferred:\n" ^ setmp show_types true Display.raw_string_of_term t)
    |> check_tvars
    |> tracing (fn _ => "---\n")
  end;

(* evaluation oracle *)

exception Norm of CodeThingol.code * term
  * (CodeThingol.typscheme * CodeThingol.iterm) * string list;

fun norm_oracle (thy, Norm (code, t, vs_ty_t, deps)) =
  Logic.mk_equals (t, eval thy code t vs_ty_t deps);

fun norm_invoke thy code t vs_ty_t deps =
  Thm.invoke_oracle_i thy "HOL.norm" (thy, Norm (code, t, vs_ty_t, deps));
  (*FIXME get rid of hardwired theory name*)

fun norm_conv ct =
  let
    val thy = Thm.theory_of_cterm ct;
    fun conv code vs_ty_t deps ct =
      let
        val t = Thm.term_of ct;
      in norm_invoke thy code t vs_ty_t deps end;
  in CodePackage.eval_conv thy conv ct end;

fun norm_term thy =
  let
    fun invoke code vs_ty_t deps t =
      eval thy code t vs_ty_t deps;
  in CodePackage.eval_term thy invoke #> Code.postprocess_term thy end;

(* evaluation command *)

fun norm_print_term ctxt modes t =
  let
    val thy = ProofContext.theory_of ctxt;
    val t' = norm_term thy t;
    val ty' = Term.type_of t';
    val p = PrintMode.with_modes modes (fn () =>
      Pretty.block [Pretty.quote (ProofContext.pretty_term ctxt t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (ProofContext.pretty_typ ctxt ty')]) ();
  in Pretty.writeln p end;


(** Isar setup **)

fun norm_print_term_cmd (modes, s) state =
  let val ctxt = Toplevel.context_of state
  in norm_print_term ctxt modes (Syntax.read_term ctxt s) end;

val setup = Theory.add_oracle ("norm", norm_oracle)

local structure P = OuterParse and K = OuterKeyword in

val opt_modes = Scan.optional (P.$$$ "(" |-- P.!!! (Scan.repeat1 P.xname --| P.$$$ ")")) [];

val nbeP =
  OuterSyntax.improper_command "normal_form" "normalize term by evaluation" K.diag
    (opt_modes -- P.typ >> (Toplevel.keep o norm_print_term_cmd));

val _ = OuterSyntax.add_parsers [nbeP];

end;

end;
