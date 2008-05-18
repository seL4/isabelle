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
      Const of int * Univ list               (*named (uninterpreted) constants*)
    | Free of string * Univ list             (*free (uninterpreted) variables*)
    | DFree of string * int                  (*free (uninterpreted) dictionary parameters*)
    | BVar of int * Univ list
    | Abs of (int * (Univ list -> Univ)) * Univ list;
  val apps: Univ -> Univ list -> Univ        (*explicit applications*)
  val abss: int -> (Univ list -> Univ) -> Univ
                                            (*abstractions as closures*)

  val univs_ref: (unit -> Univ list -> Univ list) option ref
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
    Const of int * Univ list           (*named (uninterpreted) constants*)
  | Free of string * Univ list         (*free variables*)
  | DFree of string * int              (*free (uninterpreted) dictionary parameters*)
  | BVar of int * Univ list            (*bound named variables*)
  | Abs of (int * (Univ list -> Univ)) * Univ list
                                      (*abstractions as closures*);

(* constructor functions *)

fun abss n f = Abs ((n, f), []);
fun apps (Abs ((n, f), xs)) ys = let val k = n - length ys in
      if k = 0 then f (ys @ xs)
      else if k < 0 then
        let val (zs, ws) = chop (~ k) ys
        in apps (f (ws @ xs)) zs end
      else Abs ((k, f), ys @ xs) end (*note: reverse convention also for apps!*)
  | apps (Const (name, xs)) ys = Const (name, ys @ xs)
  | apps (Free (name, xs)) ys = Free (name, ys @ xs)
  | apps (BVar (name, xs)) ys = BVar (name, ys @ xs);


(** assembling and compiling ML code from terms **)

(* abstract ML syntax *)

infix 9 `$` `$$`;
fun e1 `$` e2 = "(" ^ e1 ^ " " ^ e2 ^ ")";
fun e `$$` [] = e
  | e `$$` es = "(" ^ e ^ " " ^ space_implode " " es ^ ")";
fun ml_abs v e = "(fn " ^ v ^ " => " ^ e ^ ")";

fun ml_cases t cs =
  "(case " ^ t ^ " of " ^ space_implode " | " (map (fn (p, t) => p ^ " => " ^ t) cs) ^ ")";
fun ml_Let d e = "let\n" ^ d ^ " in " ^ e ^ " end";

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
        |> cat_lines
        |> suffix "\n"
      end;

(* nbe specific syntax and sandbox communication *)

val univs_ref = ref (NONE : (unit -> Univ list -> Univ list) option);

local
  val prefix =          "Nbe.";
  val name_ref =        prefix ^ "univs_ref";
  val name_const =      prefix ^ "Const";
  val name_abss =       prefix ^ "abss";
  val name_apps =       prefix ^ "apps";
in

val univs_cookie = (name_ref, univs_ref);

fun nbe_fun "" = "nbe_value"
  | nbe_fun c = "c_" ^ translate_string (fn "." => "_" | c => c) c;
fun nbe_dict v n = "d_" ^ v ^ "_" ^ string_of_int n;
fun nbe_bound v = "v_" ^ v;

(*note: these three are the "turning spots" where proper argument order is established!*)
fun nbe_apps t [] = t
  | nbe_apps t ts = name_apps `$$` [t, ml_list (rev ts)];
fun nbe_apps_local c ts = nbe_fun c `$` ml_list (rev ts);
fun nbe_apps_constr idx ts =
  name_const `$` ("(" ^ string_of_int idx ^ ", " ^ ml_list (rev ts) ^ ")");

fun nbe_abss 0 f = f `$` ml_list []
  | nbe_abss n f = name_abss `$$` [string_of_int n, f];

end;

open BasicCodeThingol;

(* code generation *)

fun assemble_eqnss idx_of deps eqnss =
  let
    fun prep_eqns (c, (vs, eqns)) =
      let
        val dicts = maps (fn (v, sort) => map_index (nbe_dict v o fst) sort) vs;
        val num_args = length dicts + (length o fst o hd) eqns;
      in (c, (num_args, (dicts, eqns))) end;
    val eqnss' = map prep_eqns eqnss;

    fun assemble_constapp c dss ts = 
      let
        val ts' = (maps o map) assemble_idict dss @ ts;
      in case AList.lookup (op =) eqnss' c
       of SOME (n, _) => if n <= length ts'
            then let val (ts1, ts2) = chop n ts'
            in nbe_apps (nbe_apps_local c ts1) ts2
            end else nbe_apps (nbe_abss n (nbe_fun c)) ts'
        | NONE => if member (op =) deps c
            then nbe_apps (nbe_fun c) ts'
            else nbe_apps_constr (idx_of c) ts'
      end
    and assemble_idict (DictConst (inst, dss)) =
          assemble_constapp inst dss []
      | assemble_idict (DictVar (supers, (v, (n, _)))) =
          fold_rev (fn super => assemble_constapp super [] o single) supers (nbe_dict v n);

    fun assemble_iterm constapp =
      let
        fun of_iterm t =
          let
            val (t', ts) = CodeThingol.unfold_app t
          in of_iapp t' (fold_rev (cons o of_iterm) ts []) end
        and of_iapp (IConst (c, (dss, _))) ts = constapp c dss ts
          | of_iapp (IVar v) ts = nbe_apps (nbe_bound v) ts
          | of_iapp ((v, _) `|-> t) ts =
              nbe_apps (nbe_abss 1 (ml_abs (ml_list [nbe_bound v]) (of_iterm t))) ts
          | of_iapp (ICase (((t, _), cs), t0)) ts =
              nbe_apps (ml_cases (of_iterm t) (map (pairself of_iterm) cs
                @ [("_", of_iterm t0)])) ts
      in of_iterm end;

    fun assemble_eqns (c, (num_args, (dicts, eqns))) =
      let
        val assemble_arg = assemble_iterm
          (fn c => fn _ => fn ts => nbe_apps_constr (idx_of c) ts);
        val assemble_rhs = assemble_iterm assemble_constapp;
        fun assemble_eqn (args, rhs) =
          ([ml_list (rev (dicts @ map assemble_arg args))], assemble_rhs rhs);
        val default_args = map nbe_bound (Name.invent_list [] "a" num_args);
        val default_eqn = if c = "" then NONE
          else SOME ([ml_list (rev default_args)],
            nbe_apps_constr (idx_of c) default_args);
      in
        ((nbe_fun c, map assemble_eqn eqns @ the_list default_eqn),
          nbe_abss num_args (nbe_fun c))
      end;

    val (fun_vars, fun_vals) = map_split assemble_eqns eqnss';
    val deps_vars = ml_list (map nbe_fun deps);
  in ml_abs deps_vars (ml_Let (ml_fundefs fun_vars) (ml_list fun_vals)) end;

(* code compilation *)

fun compile_eqnss gr raw_deps [] = []
  | compile_eqnss gr raw_deps eqnss = 
      let
        val (deps, deps_vals) = split_list (map_filter
          (fn dep => Option.map (fn univ => (dep, univ)) (fst ((Graph.get_node gr dep)))) raw_deps);
        val idx_of = raw_deps
          |> map (fn dep => (dep, snd (Graph.get_node gr dep)))
          |> AList.lookup (op =)
          |> (fn f => the o f);
        val s = assemble_eqnss idx_of deps eqnss;
        val cs = map fst eqnss;
      in
        s
        |> tracing (fn s => "\n--- code to be evaluated:\n" ^ s)
        |> ML_Context.evaluate
            (Output.tracing o enclose "\n---compiler echo:\n" "\n---\n",
            Output.tracing o enclose "\n--- compiler echo (with error):\n" "\n---\n")
            (!trace) univs_cookie
        |> (fn f => f deps_vals)
        |> (fn univs => cs ~~ univs)
      end;

(* preparing function equations *)

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
    val refl_deps = names_deps
      |> maps snd
      |> distinct (op =)
      |> fold (insert (op =)) names;
    fun new_node name (gr, (maxidx, idx_tab)) = if can (Graph.get_node gr) name
      then (gr, (maxidx, idx_tab))
      else (Graph.new_node (name, (NONE, maxidx)) gr,
        (maxidx + 1, Inttab.update_new (maxidx, name) idx_tab));
    fun compile gr = eqnss
      |> compile_eqnss gr refl_deps
      |> rpair gr;
  in
    fold new_node refl_deps
    #> apfst (fold (fn (name, deps) => fold (curry Graph.add_edge name) deps) names_deps
      #> compile
      #-> fold (fn (name, univ) => (Graph.map_node name o apfst) (K (SOME univ))))
  end;

fun ensure_stmts code =
  let
    fun add_stmts names (gr, (maxidx, idx_tab)) = if exists ((can o Graph.get_node) gr) names
      then (gr, (maxidx, idx_tab))
      else (gr, (maxidx, idx_tab))
        |> compile_stmts (map (fn name => ((name, Graph.get_node code name),
          Graph.imm_succs code name)) names);
  in fold_rev add_stmts (Graph.strong_conn code) end;


(** evaluation **)

(* term evaluation *)

fun eval_term gr deps ((vs, ty), t) =
  let 
    val frees = CodeThingol.fold_unbound_varnames (insert (op =)) t []
    val frees' = map (fn v => Free (v, [])) frees;
    val dict_frees = maps (fn (v, sort) => map_index (curry DFree v o fst) sort) vs;
  in
    ("", (vs, [(map IVar frees, t)]))
    |> singleton (compile_eqnss gr deps)
    |> snd
    |> (fn t => apps t (rev (dict_frees @ frees')))
  end;

(* reification *)

fun term_of_univ thy idx_tab t =
  let
    fun take_until f [] = []
      | take_until f (x::xs) = if f x then [] else x :: take_until f xs;
    fun is_dict (Const (idx, _)) =
          let
            val c = the (Inttab.lookup idx_tab idx);
          in
            (is_some o CodeName.class_rev thy) c
            orelse (is_some o CodeName.classrel_rev thy) c
            orelse (is_some o CodeName.instance_rev thy) c
          end
      | is_dict (DFree _) = true
      | is_dict _ = false;
    fun of_apps bounds (t, ts) =
      fold_map (of_univ bounds) ts
      #>> (fn ts' => list_comb (t, rev ts'))
    and of_univ bounds (Const (idx, ts)) typidx =
          let
            val ts' = take_until is_dict ts;
            val c = (the o CodeName.const_rev thy o the o Inttab.lookup idx_tab) idx;
            val T = Code.default_typ thy c;
            val T' = map_type_tvar (fn ((v, i), S) => TypeInfer.param (typidx + i) (v, [])) T;
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
  type T = (Univ option * int) Graph.T * (int * string Inttab.table);
  val empty = (Graph.empty, (0, Inttab.empty));
  fun merge _ ((gr1, (maxidx1, idx_tab1)), (gr2, (maxidx2, idx_tab2))) =
    (Graph.merge (K true) (gr1, gr2), (IntInf.max (maxidx1, maxidx2),
      Inttab.merge (K true) (idx_tab1, idx_tab2)));
  fun purge _ NONE _ = empty
    | purge NONE _ _ = empty
    | purge (SOME thy) (SOME cs) (gr, (maxidx, idx_tab)) =
        let
          val cs_exisiting =
            map_filter (CodeName.const_rev thy) (Graph.keys gr);
          val dels = (Graph.all_preds gr
              o map (CodeName.const thy)
              o filter (member (op =) cs_exisiting)
            ) cs;
        in (Graph.del_nodes dels gr, (maxidx, idx_tab)) end;
);

(* compilation, evaluation and reification *)

fun compile_eval thy code vs_ty_t deps =
  let
    val (gr, (_, idx_tab)) = Nbe_Functions.change thy (ensure_stmts code);
  in
    vs_ty_t
    |> eval_term gr deps
    |> term_of_univ thy idx_tab
  end;

(* evaluation with type reconstruction *)

fun eval thy t code vs_ty_t deps =
  let
    fun subst_const f = map_aterms (fn t as Term.Const (c, ty) => Term.Const (f c, ty)
      | t => t);
    val subst_triv_consts = subst_const (CodeUnit.resubst_alias thy);
    val ty = type_of t;
    val type_free = AList.lookup (op =)
      (map (fn (s, T) => (s, Term.Free (s, T))) (Term.add_frees t []));
    val type_frees = Term.map_aterms
      (fn (t as Term.Free (s, _)) => the_default t (type_free s) | t => t);
    fun type_infer t = [(t, ty)]
      |> TypeInfer.infer_types (Syntax.pp_global thy) (Sign.tsig_of thy) I
           (try (Type.strip_sorts o Sign.the_const_type thy)) (K NONE)
           Name.context 0 NONE
      |> fst |> the_single |> fst;
    fun check_tvars t = if null (Term.term_tvars t) then t else
      error ("Illegal schematic type variables in normalized term: "
        ^ setmp show_types true (Syntax.string_of_term_global thy) t);
    val string_of_term = setmp show_types true (Syntax.string_of_term_global thy);
  in
    compile_eval thy code vs_ty_t deps
    |> tracing (fn t => "Normalized:\n" ^ string_of_term t)
    |> subst_triv_consts
    |> type_frees
    |> tracing (fn t => "Vars typed:\n" ^ string_of_term t)
    |> type_infer
    |> tracing (fn t => "Types inferred:\n" ^ string_of_term t)
    |> check_tvars
    |> tracing (fn t => "---\n")
  end;

(* evaluation oracle *)

exception Norm of term * CodeThingol.code
  * (CodeThingol.typscheme * CodeThingol.iterm) * string list;

fun norm_oracle (thy, Norm (t, code, vs_ty_t, deps)) =
  Logic.mk_equals (t, eval thy t code vs_ty_t deps);

fun norm_invoke thy t code vs_ty_t deps =
  Thm.invoke_oracle_i thy "HOL.norm" (thy, Norm (t, code, vs_ty_t, deps));
  (*FIXME get rid of hardwired theory name*)

fun add_triv_classes thy =
  let
    val inters = curry (Sorts.inter_sort (Sign.classes_of thy))
      (CodeUnit.triv_classes thy);
    fun map_sorts f = (map_types o map_atyps)
      (fn TVar (v, sort) => TVar (v, f sort)
        | TFree (v, sort) => TFree (v, f sort));
  in map_sorts inters end;

fun norm_conv ct =
  let
    val thy = Thm.theory_of_cterm ct;
    fun evaluator' t code vs_ty_t deps = norm_invoke thy t code vs_ty_t deps;
    fun evaluator t = (add_triv_classes thy t, evaluator' t);
  in CodePackage.evaluate_conv thy evaluator ct end;

fun norm_term thy t =
  let
    fun evaluator' t code vs_ty_t deps = eval thy t code vs_ty_t deps;
    fun evaluator t = (add_triv_classes thy t, evaluator' t);
  in (Code.postprocess_term thy o CodePackage.evaluate_term thy evaluator) t end;

(* evaluation command *)

fun norm_print_term ctxt modes t =
  let
    val thy = ProofContext.theory_of ctxt;
    val t' = norm_term thy t;
    val ty' = Term.type_of t';
    val ctxt' = Variable.auto_fixes t ctxt;
    val p = PrintMode.with_modes modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
  in Pretty.writeln p end;


(** Isar setup **)

fun norm_print_term_cmd (modes, s) state =
  let val ctxt = Toplevel.context_of state
  in norm_print_term ctxt modes (Syntax.read_term ctxt s) end;

val setup = Theory.add_oracle ("norm", norm_oracle);

local structure P = OuterParse and K = OuterKeyword in

val opt_modes = Scan.optional (P.$$$ "(" |-- P.!!! (Scan.repeat1 P.xname --| P.$$$ ")")) [];

val _ =
  OuterSyntax.improper_command "normal_form" "normalize term by evaluation" K.diag
    (opt_modes -- P.typ >> (Toplevel.keep o norm_print_term_cmd));

end;

end;
