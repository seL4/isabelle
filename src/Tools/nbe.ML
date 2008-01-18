(*  Title:      Tools/nbe.ML
    ID:         $Id$
    Authors:    Klaus Aehlig, LMU Muenchen; Tobias Nipkow, Florian Haftmann, TU Muenchen

Normalization by evaluation, based on generic code generator.
*)

signature NBE =
sig
  val norm_conv: cterm -> thm
  val norm_term: theory -> term -> term

  datatype Univ =
      Const of string * Univ list            (*named (uninterpreted) constants*)
    | Free of string * Univ list             (*free (uninterpreted) variables*)
    | DFree of string * int                  (*free (uninterpreted) dictionary parameters*)
    | BVar of int * Univ list
    | Abs of (int * (Univ list -> Univ)) * Univ list;
  val apps: Univ -> Univ list -> Univ        (*explicit applications*)
  val abs: int -> (Univ list -> Univ) -> Univ
                                            (*abstractions as closures*)

  val univs_ref: (unit -> Univ list -> Univ list) option ref
  val norm_invoke: theory -> CodeThingol.code -> term
    -> CodeThingol.typscheme * CodeThingol.iterm -> string list -> thm
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
  | DFree of string * int              (*free (uninterpreted) dictionary parameters*)
  | BVar of int * Univ list            (*bound named variables*)
  | Abs of (int * (Univ list -> Univ)) * Univ list
                                      (*abstractions as closures*);

(* constructor functions *)

fun abs n f = Abs ((n, f), []);
fun apps (Abs ((n, f), xs)) ys = let val k = n - length ys in
      if k = 0 then f (ys @ xs)
      else if k < 0 then
        let val (zs, ws) = chop (~ k) ys
        in apps (f (ws @ xs)) zs end
      else Abs ((k, f), ys @ xs) end (*note: reverse convention also for apps!*)
  | apps (Const (name, xs)) ys = Const (name, ys @ xs)
  | apps (Free (name, xs)) ys = Free (name, ys @ xs)
  | apps (BVar (name, xs)) ys = BVar (name, ys @ xs);

(* universe graph *)

type univ_gr = Univ option Graph.T;
val compiled : univ_gr -> string -> bool = can o Graph.get_node;


(** assembling and compiling ML code from terms **)

(* abstract ML syntax *)

infix 9 `$` `$$`;
fun e1 `$` e2 = "(" ^ e1 ^ " " ^ e2 ^ ")";
fun e `$$` [] = e
  | e `$$` es = "(" ^ e ^ " " ^ space_implode " " es ^ ")";
fun ml_abs v e = "(fn " ^ v ^ " => " ^ e ^ ")";

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
  val name_abs =        prefix ^ "abs";
  val name_apps =       prefix ^ "apps";
in

fun nbe_fun' c = "c_" ^ translate_string (fn "." => "_" | c => c) c;
val nbe_fun = nbe_fun'; (*FIXME!*)
fun nbe_dict v n = "d_" ^ v ^ "_" ^ string_of_int n;
fun nbe_bound v = "v_" ^ v;
val nbe_value = "";

(*note: these three are the "turning spots" where proper argument order is established!*)
fun nbe_apps t [] = t
  | nbe_apps t ts = name_apps `$$` [t, ml_list (rev ts)];
fun nbe_apps_local c ts = nbe_fun c `$` ml_list (rev ts);
fun nbe_apps_constr c ts =
  name_const `$` ("(" ^ ML_Syntax.print_string c ^ ", " ^ ml_list (rev ts) ^ ")");


fun nbe_abss 0 f = f `$` ml_list []
  | nbe_abss n f = name_abs `$$` [string_of_int n, f];

end;

open BasicCodeThingol;

(* sandbox communication *)

val univs_ref = ref (NONE : (unit -> Univ list -> Univ list) option);

val compile =
  tracing (fn s => "\n--- code to be evaluated:\n" ^ s)
  #> ML_Context.evaluate
      (Output.tracing o enclose "\n---compiler echo:\n" "\n---\n",
      Output.tracing o enclose "\n--- compiler echo (with error):\n" "\n---\n")
      (!trace) ("Nbe.univs_ref", univs_ref);

(* code generation *)

datatype const_kind = Local of int | Global | Constr;

fun assemble_constapp kind c dss ts = 
      let
        val ts' = (maps o map) (assemble_idict kind) dss @ ts;
      in case kind c
       of Local n => if n <= length ts'
            then let val (ts1, ts2) = chop n ts'
            in nbe_apps (nbe_apps_local c ts1) ts2
            end else nbe_apps (nbe_abss n (nbe_fun c)) ts'
        | Global => nbe_apps (nbe_fun c) ts'
        | Constr => nbe_apps_constr c ts'
      end
and assemble_idict kind (DictConst (inst, dss)) =
      assemble_constapp kind inst dss []
  | assemble_idict kind (DictVar (supers, (v, (n, _)))) =
      fold_rev (fn super => assemble_constapp kind super [] o single) supers (nbe_dict v n);

fun assemble_iterm kind =
  let
    fun of_iterm t =
      let
        val (t', ts) = CodeThingol.unfold_app t
      in of_iapp t' (fold_rev (cons o of_iterm) ts []) end
    and of_iapp (IConst (c, (dss, _))) ts = assemble_constapp kind c dss ts
      | of_iapp (IVar v) ts = nbe_apps (nbe_bound v) ts
      | of_iapp ((v, _) `|-> t) ts =
          nbe_apps (nbe_abss 1 (ml_abs (ml_list [nbe_bound v]) (of_iterm t))) ts
      | of_iapp (ICase (((t, _), cs), t0)) ts =
          nbe_apps (ml_cases (of_iterm t) (map (pairself of_iterm) cs
            @ [("_", of_iterm t0)])) ts
  in of_iterm end;

fun assemble_eqns kind (c, (vs, eqns)) =
  let
    val dict_args = maps (fn (v, sort) => map_index (nbe_dict v o fst) sort) vs;
    val assemble_arg = assemble_iterm (K Constr);
    val assemble_rhs = assemble_iterm kind;
    fun assemble_eqn (args, rhs) =
      ([ml_list (rev (dict_args @ map assemble_arg args))], assemble_rhs rhs);
    val default_args = dict_args @ map nbe_bound (Name.invent_list [] "a" ((length o fst o hd) eqns));
    val default_eqn = ([ml_list (rev default_args)], nbe_apps_constr c default_args);
  in (nbe_fun' c, map assemble_eqn eqns @ [default_eqn]) end;

fun assemble_eqnss gr deps [] = ([], ("", []))
  | assemble_eqnss gr deps eqnss =
      let
        val cs = map fst eqnss;
        val num_args = cs ~~ map (fn (_, (vs, (args, rhs) :: _)) =>
          length (maps snd vs) + length args) eqnss;
        fun kind c = case AList.lookup (op =) num_args c
         of SOME n => Local n
          | NONE => if (is_some o Option.join o try (Graph.get_node gr)) c
              then Global else Constr;
        val deps' = filter (is_some o Option.join o try (Graph.get_node gr)) deps;
        val bind_deps = ml_list (map nbe_fun' deps');
        val bind_locals = ml_fundefs (map (assemble_eqns kind) eqnss);
        val result = ml_list (map (fn (c, n) => nbe_abss n (nbe_fun c)) num_args);
        val arg_deps = map (the o Graph.get_node gr) deps';
      in (cs, (ml_abs bind_deps (ml_Let [bind_locals] result), arg_deps)) end;

fun compile_eqnss gr deps eqnss = case assemble_eqnss gr deps eqnss
 of ([], _) => []
  | (cs, (s, deps)) => cs ~~ compile s deps;

fun eqns_of_stmt (_, CodeThingol.Fun (_, [])) =
      []
  | eqns_of_stmt (const, CodeThingol.Fun ((vs, _), eqns)) =
      [(const, (vs, map fst eqns))]
  | eqns_of_stmt (_, CodeThingol.Datatypecons _) =
      []
  | eqns_of_stmt (_, CodeThingol.Datatype _) =
      []
  | eqns_of_stmt (class, CodeThingol.Class (v, (superclasses, classops))) =
      let
        val names = map snd superclasses @ map fst classops;
        val params = Name.invent_list [] "d" (length names);
        fun mk (k, name) =
          (name, ([(v, [])],
            [([IConst (class, ([], [])) `$$ map IVar params], IVar (nth params k))]));
      in map_index mk names end
  | eqns_of_stmt (_, CodeThingol.Classrel _) =
      []
  | eqns_of_stmt (_, CodeThingol.Classparam _) =
      []
  | eqns_of_stmt (inst, CodeThingol.Classinst ((class, (_, arities)), (superinsts, instops))) =
      [(inst, (arities, [([], IConst (class, ([], [])) `$$
        map (fn (_, (_, (inst, dicts))) => IConst (inst, (dicts, []))) superinsts
        @ map (IConst o snd o fst) instops)]))];

fun compile_stmts stmts_deps =
  let
    val names = map (fst o fst) stmts_deps;
    val names_deps = map (fn ((name, _), deps) => (name, deps)) stmts_deps;
    val eqnss = maps (eqns_of_stmt o fst) stmts_deps;
    val compiled_deps = names_deps
      |> maps snd
      |> distinct (op =)
      |> subtract (op =) names;
    fun compile gr = eqnss
      |> compile_eqnss gr compiled_deps
      |> rpair gr;
  in
    fold (fn name => Graph.new_node (name, NONE)) names
    #> fold (fn (name, deps) => fold (curry Graph.add_edge name) deps) names_deps
    #> compile
    #-> fold (fn (name, univ) => Graph.map_node name (K (SOME univ)))
  end;

fun ensure_stmts code =
  let
    fun add_stmts names gr = if exists (compiled gr) names then gr else gr
      |> compile_stmts (map (fn name => ((name, Graph.get_node code name),
          Graph.imm_succs code name)) names);
  in fold_rev add_stmts (Graph.strong_conn code) end;

fun eval_term gr deps ((vs, ty), t) =
  let 
    val frees = CodeThingol.fold_unbound_varnames (insert (op =)) t []
    val frees' = map (fn v => Free (v, [])) frees;
    val dict_frees = maps (fn (v, sort) => map_index (curry DFree v o fst) sort) vs;
  in
    (nbe_value, (vs, [(map IVar frees, t)]))
    |> singleton (compile_eqnss gr deps)
    |> snd
    |> (fn t => apps t (rev (dict_frees @ frees')))
  end;


(** evaluation **)

(* reification *)

fun term_of_univ thy t =
  let
    fun take_until f [] = []
      | take_until f (x::xs) = if f x then [] else x :: take_until f xs;
    fun is_dict (Const (c, _)) =
          (is_some o CodeName.class_rev thy) c
          orelse (is_some o CodeName.classrel_rev thy) c
          orelse (is_some o CodeName.instance_rev thy) c
      | is_dict (DFree _) = true
      | is_dict _ = false;
    fun of_apps bounds (t, ts) =
      fold_map (of_univ bounds) ts
      #>> (fn ts' => list_comb (t, rev ts'))
    and of_univ bounds (Const (name, ts)) typidx =
          let
            val ts' = take_until is_dict ts;
            val SOME c = CodeName.const_rev thy name;
            val T = Code.default_typ thy c;
            val T' = map_type_tvar (fn ((v, i), S) => TypeInfer.param (typidx + i) (v, S)) T;
            val typidx' = typidx + maxidx_of_typ T' + 1;
          in of_apps bounds (Term.Const (c, T'), ts') typidx' end
      | of_univ bounds (Free (name, ts)) typidx =
          of_apps bounds (Term.Free (name, dummyT), ts) typidx
      | of_univ bounds (BVar (name, ts)) typidx =
          of_apps bounds (Bound (bounds - name - 1), ts) typidx
      | of_univ bounds (t as Abs _) typidx =
          typidx
          |> of_univ (bounds + 1) (apps t [BVar (bounds, [])])
          |-> (fn t' => pair (Term.Abs ("u", dummyT, t')))
  in of_univ 0 t 0 |> fst end;

(* function store *)

structure Nbe_Functions = CodeDataFun
(
  type T = univ_gr;
  val empty = Graph.empty;
  fun merge _ = Graph.merge (K true);
  fun purge _ NONE _ = Graph.empty
    | purge NONE _ _ = Graph.empty
    | purge (SOME thy) (SOME cs) gr =
        let
          val cs_exisiting =
            map_filter (CodeName.const_rev thy) (Graph.keys gr);
          val dels = (Graph.all_preds gr
              o map (CodeName.const thy)
              o filter (member (op =) cs_exisiting)
            ) cs;
        in Graph.del_nodes dels gr end;
);

(* compilation, evaluation and reification *)

fun compile_eval thy code vs_ty_t deps =
  vs_ty_t
  |> eval_term (Nbe_Functions.change thy (ensure_stmts code)) deps
  |> term_of_univ thy;

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
    val string_of_term = setmp show_types true (Sign.string_of_term thy);
  in
    compile_eval thy code vs_ty_t deps
    |> tracing (fn t => "Normalized:\n" ^ string_of_term t)
    |> anno_vars
    |> tracing (fn t => "Vars typed:\n" ^ string_of_term t)
    |> constrain
    |> tracing (fn t => "Types inferred:\n" ^ string_of_term t)
    |> tracing (fn t => "---\n")
    |> check_tvars
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
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt ty')]) ();
  in Pretty.writeln p end;


(** Isar setup **)

fun norm_print_term_cmd (modes, s) state =
  let val ctxt = Toplevel.context_of state
  in norm_print_term ctxt modes (Syntax.read_term ctxt s) end;

val setup = Theory.add_oracle ("norm", norm_oracle)

local structure P = OuterParse and K = OuterKeyword in

val opt_modes = Scan.optional (P.$$$ "(" |-- P.!!! (Scan.repeat1 P.xname --| P.$$$ ")")) [];

val _ =
  OuterSyntax.improper_command "normal_form" "normalize term by evaluation" K.diag
    (opt_modes -- P.typ >> (Toplevel.keep o norm_print_term_cmd));

end;

end;
