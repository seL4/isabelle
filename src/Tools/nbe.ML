(*  Title:      Tools/Nbe/Nbe_Eval.ML
    ID:         $Id$
    Authors:    Klaus Aehlig, LMU Muenchen; Tobias Nipkow, Florian Haftmann, TU Muenchen

Evaluation mechanisms for normalization by evaluation.
*)

(*
FIXME:
- get rid of BVar (?) - it is only used for terms to be evaluated, not for functions
- proper purge operation - preliminary for...
- really incremental code generation
*)

signature NBE =
sig
  datatype Univ = 
      Const of string * Univ list        (*named constructors*)
    | Free of string * Univ list
    | BVar of int * Univ list
    | Abs of (int * (Univ list -> Univ)) * Univ list;
  val free: string -> Univ list -> Univ       (*free (uninterpreted) variables*)
  val abs: int -> (Univ list -> Univ) -> Univ list -> Univ
                                            (*abstractions as functions*)
  val app: Univ -> Univ -> Univ              (*explicit application*)

  val univs_ref: Univ list ref 
  val lookup_fun: CodegenNames.const -> Univ

  val normalization_conv: cterm -> thm

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

   (?) Finally, it might happen, that a function does not get all the
   arguments it needs.  In this case the function must provide means to
   present itself as a string. As this might be a heavy-wight
   operation, we delay it. (?) 
*)

datatype Univ = 
    Const of string * Univ list        (*named constructors*)
  | Free of string * Univ list         (*free variables*)
  | BVar of int * Univ list            (*bound named variables*)
  | Abs of (int * (Univ list -> Univ)) * Univ list
                                      (*functions*);

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
(struct
  type T = Univ Symtab.table;
  val empty = Symtab.empty;
  fun merge _ = Symtab.merge (K true);
  fun purge _ _ _ = Symtab.empty;
end);

(* sandbox communication *)

val univs_ref = ref [] : Univ list ref;

local

val tab_ref = ref NONE : Univ Symtab.table option ref;

in

fun lookup_fun s = case ! tab_ref
 of NONE => error "compile_univs"
  | SOME tab => (the o Symtab.lookup tab) s;

fun compile_univs tab ([], _) = []
  | compile_univs tab (cs, raw_s) =
      let
        val _ = univs_ref := [];
        val s = "Nbe.univs_ref := " ^ raw_s;
        val _ = tracing (fn () => "\n---generated code:\n" ^ s) ();
        val _ = tab_ref := SOME tab;
        val _ = use_text "" (Output.tracing o enclose "\n---compiler echo:\n" "\n---\n",
          Output.tracing o enclose "\n--- compiler echo (with error):\n" "\n---\n")
          (!trace) s;
        val _ = tab_ref := NONE;
        val univs = case !univs_ref of [] => error "compile_univs" | univs => univs;
      in cs ~~ univs end;

end; (*local*)


(** assembling and compiling ML code from terms **)

(* abstract ML syntax *)

infix 9 `$` `$$`;
fun e1 `$` e2 = "(" ^ e1 ^ " " ^ e2 ^ ")";
fun e `$$` es = "(" ^ e ^ " " ^ space_implode " " es ^ ")";
fun ml_abs v e = "(fn" ^ v ^ " => " ^ e ^ ")";

fun ml_Val v s = "val " ^ v ^ " = " ^ s;
fun ml_cases t cs =
  "(case " ^ t ^ " of " ^ space_implode " | " (map (fn (p, t) => p ^ " => " ^ t) cs) ^ ")";
fun ml_Let ds e = "let\n" ^ space_implode "\n" ds ^ " in " ^ e ^ " end";

fun ml_list es = "[" ^ commas es ^ "]";

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

open BasicCodegenThingol;

(* greetings to Tarski *)

fun assemble_iterm thy is_fun num_args =
  let
    fun of_iterm t =
      let
        val (t', ts) = CodegenThingol.unfold_app t
      in of_itermapp t' (fold (cons o of_iterm) ts []) end
    and of_itermapp (IConst (c, (dss, _))) ts =
          (case num_args c
           of SOME n => if n <= length ts
                then let val (args2, args1) = chop (length ts - n) ts
                in nbe_apps (nbe_fun c `$` ml_list args1) args2
                end else nbe_const c ts
            | NONE => if is_fun c then nbe_apps (nbe_fun c) ts
                else nbe_const c ts)
      | of_itermapp (IVar v) ts = nbe_apps (nbe_bound v) ts
      | of_itermapp ((v, _) `|-> t) ts =
          nbe_apps (nbe_abss 1 (ml_abs (ml_list [nbe_bound v]) (of_iterm t))) ts
      | of_itermapp (ICase (((t, _), cs), t0)) ts =
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

fun assemble_eqnss thy is_fun [] = ([], "")
  | assemble_eqnss thy is_fun eqnss =
      let
        val cs = map fst eqnss;
        val num_args = cs ~~ map (fn (_, (args, rhs) :: _) => length args) eqnss;
        val funs = fold (fold (CodegenThingol.fold_constnames
          (insert (op =))) o map snd o snd) eqnss [];
        val bind_funs = map nbe_lookup (filter is_fun funs);
        val bind_locals = ml_fundefs (map nbe_fun cs ~~ map
          (assemble_fun thy is_fun (AList.lookup (op =) num_args)) eqnss);
        val result = ml_list (map (fn (c, n) => nbe_abss n (nbe_fun c)) num_args);
      in (cs, ml_Let (bind_funs @ [bind_locals]) result) end;

fun assemble_eval thy is_fun t =
  let
    val funs = CodegenThingol.fold_constnames (insert (op =)) t [];
    val frees = CodegenThingol.fold_unbound_varnames (insert (op =)) t [];
    val bind_funs = map nbe_lookup (filter is_fun funs);
    val bind_value = ml_fundefs [(nbe_value, [([ml_list (map nbe_bound frees)],
      assemble_iterm thy is_fun (K NONE) t)])];
    val result = ml_list [nbe_value `$` ml_list (map nbe_free frees)];
  in ([nbe_value], ml_Let (bind_funs @ [bind_value]) result) end;

fun eqns_of_stmt (name, CodegenThingol.Fun ([], _)) =
      NONE
  | eqns_of_stmt (name, CodegenThingol.Fun (eqns, _)) =
      SOME (name, eqns)
  | eqns_of_stmt (_, CodegenThingol.Datatypecons _) =
      NONE
  | eqns_of_stmt (_, CodegenThingol.Datatype _) =
      NONE
  | eqns_of_stmt (_, CodegenThingol.Class _) =
      NONE
  | eqns_of_stmt (_, CodegenThingol.Classrel _) =
      NONE
  | eqns_of_stmt (_, CodegenThingol.Classop _) =
      NONE
  | eqns_of_stmt (_, CodegenThingol.Classinst _) =
      NONE;

fun compile_stmts thy is_fun =
  map_filter eqns_of_stmt
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
    fun compile' stmts tab =
      let
        val compiled = compile_stmts thy (Symtab.defined tab) stmts;
      in Nbe_Functions.change thy (fold Symtab.update compiled) end;
    val nbe_tab = Nbe_Functions.get thy;
    val stmtss =
      map (AList.make (Graph.get_node code)) (rev (Graph.strong_conn code))
      |> (map o filter_out) (Symtab.defined nbe_tab o fst)
  in fold compile' stmtss nbe_tab end;

(* re-conversion *)

fun term_of_univ thy t =
  let
    fun of_apps bounds (t, ts) =
      fold_map (of_univ bounds) ts
      #>> (fn ts' => list_comb (t, rev ts'))
    and of_univ bounds (Const (name, ts)) typidx =
          let
            val SOME (const as (c, _)) = CodegenNames.const_rev thy name;
            val T = CodegenData.default_typ thy const;
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

fun eval thy code t t' =
  let
    fun subst_Frees [] = I
      | subst_Frees inst =
          Term.map_aterms (fn (t as Term.Free (s, _)) => the_default t (AList.lookup (op =) inst s)
                            | t => t);
    val anno_vars =
      subst_Frees (map (fn (s, T) => (s, Term.Free (s, T))) (Term.add_frees t []))
      #> subst_Vars (map (fn (ixn, T) => (ixn, Var (ixn, T))) (Term.add_vars t []))
    fun check_tvars t = if null (Term.term_tvars t) then t else
      error ("Illegal schematic type variables in normalized term: "
        ^ setmp show_types true (Sign.string_of_term thy) t);
    val ty = type_of t;
    fun constrain t =
      singleton (ProofContext.infer_types_pats (ProofContext.init thy)) (TypeInfer.constrain t ty);
  in
    t'
    |> eval_term thy (Symtab.defined (ensure_funs thy code))
    |> term_of_univ thy
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

exception Normalization of CodegenThingol.code * term * CodegenThingol.iterm;

fun normalization_oracle (thy, Normalization (code, t, t')) =
  Logic.mk_equals (t, eval thy code t t');

fun normalization_invoke thy code t t' =
  Thm.invoke_oracle_i thy "Nbe.normalization" (thy, Normalization (code, t, t'));

fun normalization_conv ct =
  let
    val thy = Thm.theory_of_cterm ct;
    fun conv code t' ct =
      let
        val t = Thm.term_of ct;
      in normalization_invoke thy code t t' end;
  in CodegenPackage.eval_conv thy conv ct end;

(* evaluation command *)

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


(** Isar setup **)

fun norm_print_term_cmd (modes, raw_t) state =
  let val ctxt = Toplevel.context_of state
  in norm_print_term ctxt modes (ProofContext.read_term ctxt raw_t) end;

val setup = Theory.add_oracle ("normalization", normalization_oracle)

local structure P = OuterParse and K = OuterKeyword in

val opt_modes = Scan.optional (P.$$$ "(" |-- P.!!! (Scan.repeat1 P.xname --| P.$$$ ")")) [];

val nbeP =
  OuterSyntax.improper_command "normal_form" "normalize term by evaluation" K.diag
    (opt_modes -- P.typ >> (Toplevel.keep o norm_print_term_cmd));

val _ = OuterSyntax.add_parsers [nbeP];

end;

end;
