(*  Title:      Tools/Nbe/Nbe_Eval.ML
    ID:         $Id$
    Authors:    Klaus Aehlig, LMU Muenchen; Tobias Nipkow, Florian Haftmann, TU Muenchen

Evaluation mechanisms for normalization by evaluation.
*)

(*
FIXME:
- implement purge operation proper
- get rid of BVar (?) - it is only used tor terms to be evaluated, not for functions
*)

signature NBE_EVAL =
sig
  datatype Univ = 
      Constr of string * Univ list       (*named constructors*)
    | Var of string * Univ list          (*free variables*)
    | BVar of int * Univ list            (*bound named variables*)
    | Fun of (Univ list -> Univ) * Univ list * int
                                        (*functions*)
  val apply: Univ -> Univ -> Univ

  val univs_ref: (CodegenNames.const * Univ) list ref 
  val compile_univs: string -> (CodegenNames.const * Univ) list
  val lookup_fun: CodegenNames.const -> Univ

  (*preconditions: no Vars/TVars in term*)
  val eval: theory -> CodegenFuncgr.T -> term -> term

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
   arguments it needs. In this case the function must provide means to
   present itself as a string. As this might be a heavy-wight
   operation, we delay it. (?) 
*)

datatype Univ = 
    Constr of string * Univ list       (*named constructors*)
  | Var of string * Univ list          (*free variables*)
  | BVar of int * Univ list            (*bound named variables*)
  | Fun of (Univ list -> Univ) * Univ list * int
                                      (*functions*);

fun apply (Fun (f, xs, 1)) x = f (x :: xs)
  | apply (Fun (f, xs, n)) x = Fun (f, x :: xs, n - 1)
  | apply (Constr (name, args)) x = Constr (name, x :: args)
  | apply (Var (name, args)) x = Var (name, x :: args)
  | apply (BVar (name, args)) x = BVar (name, x :: args);


(** global functions **)

structure Nbe_Data = CodeDataFun
(struct
  type T = Univ Symtab.table;
  val empty = Symtab.empty;
  fun merge _ = Symtab.merge (K true);
  fun purge _ _ _ = Symtab.empty;
end);


(** sandbox communication **)

val univs_ref = ref [] : (string * Univ) list ref;

fun compile_univs "" = []
  | compile_univs raw_s =
      let
        val _ = univs_ref := [];
        val s = "Nbe_Eval.univs_ref := " ^ raw_s;
        val _ = tracing (fn () => "\n---generated code:\n" ^ s) ();
        val _ = use_text "" (Output.tracing o enclose "\n---compiler echo:\n" "\n---\n",
          Output.tracing o enclose "\n--- compiler echo (with error!):\n" "\n---\n")
          (!trace) s;
        val univs = case !univs_ref of [] => error "compile_univs" | univs => univs;
      in univs end;

val tab_ref = ref Symtab.empty : Univ Symtab.table ref;
fun lookup_fun s = (the o Symtab.lookup (! tab_ref)) s;


(** printing ML syntax **)

structure S =
struct

(* generic basics *)

fun app e1 e2 = "(" ^ e1 ^ " " ^ e2 ^ ")";
fun apps s ss = Library.foldl (uncurry app) (s, ss);
fun abs v e = "(fn" ^ v ^ " => " ^ e ^ ")";

fun Val v s = "val " ^ v ^ " = " ^ s;
fun Let ds e = "let\n" ^ space_implode "\n" ds ^ " in " ^ e ^ " end";

val string = ML_Syntax.print_string;
fun tup es = "(" ^ commas es ^ ")";
fun list es = "[" ^ commas es ^ "]";

fun fundefs (eqs :: eqss) =
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


(* runtime names *)

local

val Eval =              "Nbe_Eval.";
val Eval_Constr =       Eval ^ "Constr";
val Eval_apply =        Eval ^ "apply";
val Eval_Fun =          Eval ^ "Fun";
val Eval_lookup_fun =   Eval ^ "lookup_fun";

in

(* nbe specific syntax *)

fun nbe_constr c args = app Eval_Constr (tup [string c, list args]);

fun nbe_const c = "c_" ^ translate_string (fn "." => "_" | c => c) c;

fun nbe_free v = "v_" ^ v;

fun nbe_apps e es =
  Library.foldr (fn (s, e) => app (app Eval_apply e) s) (es, e);

fun nbe_abs (v, e) =
  app Eval_Fun (tup [abs (list [nbe_free v]) e, list [], "1"]);

fun nbe_fun (c, 0) = tup [string c, app (nbe_const c) (list [])]
  | nbe_fun (c, n) = tup [string c,
      app Eval_Fun (tup [nbe_const c, list [], string_of_int n])];

fun nbe_lookup c = Val (nbe_const c) (app Eval_lookup_fun (string c));

end;

end;


(** assembling and compiling ML representation of terms **)

fun assemble_term thy is_global local_arity =
  let
    fun of_term t =
      let
        val (t', ts) = strip_comb t
      in of_termapp t' (fold (cons o of_term) ts []) end
    and of_termapp (Const cexpr) ts =
          let
            val c = (CodegenNames.const thy o CodegenConsts.const_of_cexpr thy) cexpr;
          in case local_arity c
           of SOME n => if n <= length ts
                then let val (args2, args1) = chop (length ts - n) ts
                in S.nbe_apps (S.app (S.nbe_const c) (S.list args1)) args2
                end else S.nbe_constr c ts
            | NONE => if is_global c then S.nbe_apps (S.nbe_const c) ts
                else S.nbe_constr c ts
          end
      | of_termapp (Free (v, _)) ts = S.nbe_apps (S.nbe_free v) ts
      | of_termapp (Abs abs) ts =
          let
            val (v', t') = Syntax.variant_abs abs;
          in S.nbe_apps (S.nbe_abs (v', of_term t')) ts end;
  in of_term end;

fun assemble_fun thy is_global local_arity (c, eqns) =
  let
    val assemble_arg = assemble_term thy (K false) (K NONE);
    val assemble_rhs = assemble_term thy is_global local_arity;
    fun assemble_eqn (args, rhs) =
      ([S.list (map assemble_arg (rev args))], assemble_rhs rhs);
    val default_params = map S.nbe_free
      (Name.invent_list [] "a" ((the o local_arity) c));
    val default_eqn = ([S.list default_params], S.nbe_constr c default_params);
  in map assemble_eqn eqns @ [default_eqn] end;

fun compile _ _ [] = []
  | compile _ _ [(_, [])] = []
  | compile thy is_global fundefs =
      let
        val eqnss = (map o apsnd o map) (apfst (snd o strip_comb) o Logic.dest_equals
          o Logic.unvarify o prop_of) fundefs;
        val cs = map fst eqnss;
        val arities = cs ~~ map (fn (_, (args, rhs) :: _) => length args) eqnss;
        val used_cs = fold (fold (fold_aterms (fn Const cexpr =>
          insert (op =) ((CodegenNames.const thy o CodegenConsts.const_of_cexpr thy) cexpr)
            | _ => I)) o map snd o snd) eqnss [];
        val bind_globals = map S.nbe_lookup (filter is_global used_cs);
        val bind_locals = S.fundefs (map S.nbe_const cs ~~ map
          (assemble_fun thy is_global (AList.lookup (op =) arities)) eqnss);
        val result = S.list (map S.nbe_fun arities);
      in compile_univs (S.Let (bind_globals @ [bind_locals]) result) end;


(** evaluation with greetings to Tarski **)

(* conversion and evaluation *)

fun univ_of_term thy lookup_fun =
  let
    fun of_term vars t =
      let
        val (t', ts) = strip_comb t
      in
        Library.foldl (uncurry apply)
          (of_termapp vars  t', map (of_term vars) ts)
      end
    and of_termapp vars (Const cexpr) =
          let
            val s = (CodegenNames.const thy o CodegenConsts.const_of_cexpr thy) cexpr;
          in the_default (Constr (s, [])) (lookup_fun s) end
      | of_termapp vars (Free (v, _)) =
          the_default (Var (v, [])) (AList.lookup (op =) vars v)
      | of_termapp vars (Abs abs) =
          let
            val (v', t') = Syntax.variant_abs abs;
          in Fun (fn [x] => of_term (AList.update (op =) (v', x) vars) t', [], 1) end;
  in of_term [] end;


(* ensure global functions *)

fun ensure_funs thy funcgr t =
  let
    fun consts_of thy t =
      fold_aterms (fn Const c => cons (CodegenConsts.const_of_cexpr thy c) | _ => I) t []
    val consts = consts_of thy t;
    fun compile' eqs tab =
      let
        val _ = tab_ref := tab;
        val compiled = compile thy (Symtab.defined tab) eqs;
      in Nbe_Data.change thy (fold Symtab.update compiled) end;
    val nbe_tab = Nbe_Data.get thy;
  in
    CodegenFuncgr.deps funcgr consts
    |> (map o filter_out) (Symtab.defined nbe_tab o CodegenNames.const thy)
    |> filter_out null
    |> (map o map) (fn c => (CodegenNames.const thy c, CodegenFuncgr.funcs funcgr c))
    |> tracing (fn funs => "new definitions: " ^ (commas o maps (map fst)) funs)
    |> (fn funs => fold compile' funs nbe_tab)
  end;


(* re-conversion *)

fun term_of_univ thy t =
  let
    fun of_apps bounds (t, ts) =
      fold_map (of_univ bounds) ts
      #>> (fn ts' => list_comb (t, rev ts'))
    and of_univ bounds (Constr (name, ts)) typidx =
          let
            val SOME (const as (c, _)) = CodegenNames.const_rev thy name;
            val T = CodegenData.default_typ thy const;
            val T' = map_type_tvar (fn ((v, i), S) => TypeInfer.param (typidx + i) (v, S)) T;
            val typidx' = typidx + maxidx_of_typ T' + 1;
          in of_apps bounds (Const (c, T'), ts) typidx' end
      | of_univ bounds (Var (name, ts)) typidx =
          of_apps bounds (Free (name, dummyT), ts) typidx
      | of_univ bounds (BVar (name, ts)) typidx =
          of_apps bounds (Bound (bounds - name - 1), ts) typidx
      | of_univ bounds (F as Fun _) typidx =
          typidx
          |> of_univ (bounds + 1) (apply F (BVar (bounds, [])))
          |-> (fn t' => pair (Abs ("u", dummyT, t')))
  in of_univ 0 t 0 |> fst end;


(* interface *)

fun eval thy funcgr t =
  let
    val tab = ensure_funs thy funcgr t;
    val u = univ_of_term thy (Symtab.lookup tab) t;
  in term_of_univ thy u end;;

end;
