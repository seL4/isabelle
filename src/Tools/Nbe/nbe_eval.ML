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

signature NBE_EVAL =
sig
  datatype Univ = 
      Const of string * Univ list        (*uninterpreted constants*)
    | Free of string * Univ list         (*free (uninterpreted) variables*)
    | BVar of int * Univ list            (*bound named variables*)
    | Abs of (int * (Univ list -> Univ)) * Univ list
                                        (*abstractions as functions*)
  val apply: Univ -> Univ -> Univ

  val univs_ref: Univ list ref 
  val lookup_fun: CodegenNames.const -> Univ

  (*preconditions: no Vars/TVars in term*)
  val eval: theory -> term -> term

  val trace: bool ref
end;

structure Nbe_Eval: NBE_EVAL =
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

fun apply (Abs ((1, f), xs)) x = f (x :: xs)
  | apply (Abs ((n, f), xs)) x = Abs ((n - 1, f), x :: xs)
  | apply (Const (name, args)) x = Const (name, x :: args)
  | apply (Free (name, args)) x = Free (name, x :: args)
  | apply (BVar (name, args)) x = BVar (name, x :: args);


(** global functions **)

structure Nbe_Functions = CodeDataFun
(struct
  type T = Univ Symtab.table;
  val empty = Symtab.empty;
  fun merge _ = Symtab.merge (K true);
  fun purge _ _ _ = Symtab.empty;
end);


(** sandbox communication **)

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
        val s = "Nbe_Eval.univs_ref := " ^ raw_s;
        val _ = tracing (fn () => "\n---generated code:\n" ^ s) ();
        val _ = tab_ref := SOME tab; (*FIXME hide proper*)
        val _ = use_text "" (Output.tracing o enclose "\n---compiler echo:\n" "\n---\n",
          Output.tracing o enclose "\n--- compiler echo (with error):\n" "\n---\n")
          (!trace) s;
        val _ = tab_ref := NONE;
        val univs = case !univs_ref of [] => error "compile_univs" | univs => univs;
      in cs ~~ univs end;

end; (*local*)


(** printing ML syntax **)

fun ml_app e1 e2 = "(" ^ e1 ^ " " ^ e2 ^ ")";
fun ml_apps s ss = Library.foldl (uncurry ml_app) (s, ss);
fun ml_abs v e = "(fn" ^ v ^ " => " ^ e ^ ")";

fun ml_Val v s = "val " ^ v ^ " = " ^ s;
fun ml_Let ds e = "let\n" ^ space_implode "\n" ds ^ " in " ^ e ^ " end";

val ml_string = ML_Syntax.print_string;
fun ml_pair e1 e2 = "(" ^ e1 ^ ", " ^ e2 ^ ")";
fun ml_list es = "[" ^ commas es ^ "]";

fun ml_cases t cs =
  "(case " ^ t ^ " of " ^ space_implode " |" (map (fn (p, t) => p ^ " => " ^ t) cs) ^ ")";

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


(** nbe specific syntax **)

local
  val Eval =            "Nbe_Eval.";
  val Eval_Const =      Eval ^ "Const";
  val Eval_Free =       Eval ^ "Free";
  val Eval_apply =      Eval ^ "apply";
  val Eval_Abs =        Eval ^ "Abs";
  val Eval_lookup_fun = Eval ^ "lookup_fun";
in

fun nbe_const c args = ml_app Eval_Const (ml_pair (ml_string c) (ml_list args));

fun nbe_fun c = "c_" ^ translate_string (fn "." => "_" | c => c) c;

fun nbe_free v = ml_app Eval_Free (ml_pair (ml_string v)  (ml_list []));

fun nbe_bound v = "v_" ^ v;

fun nbe_apps e es =
  Library.foldr (fn (s, e) => ml_app (ml_app Eval_apply e) s) (es, e);

fun nbe_abss 0 f = ml_app f (ml_list [])
  | nbe_abss n f = ml_app Eval_Abs (ml_pair (ml_pair (string_of_int n) f) (ml_list []));

fun nbe_lookup c = ml_Val (nbe_fun c) (ml_app Eval_lookup_fun (ml_string c));

val nbe_value = "value";

end;


(** assembling and compiling of terms etc. **)

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
                in nbe_apps (ml_app (nbe_fun c) (ml_list args1)) args2
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
    val result = ml_list [ml_app nbe_value (ml_list (map nbe_free frees))];
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
          |> of_univ (bounds + 1) (apply t (BVar (bounds, [])))
          |-> (fn t' => pair (Term.Abs ("u", dummyT, t')))
  in of_univ 0 t 0 |> fst end;


(* interface *)

fun eval thy t =
  let
    val (code, t') = CodegenPackage.compile_term thy t;
    val tab = ensure_funs thy code;
    val u = eval_term thy (Symtab.defined tab) t';
  in term_of_univ thy u end;;

end;
