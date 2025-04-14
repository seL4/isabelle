(*  Title:      Tools/nbe.ML
    Authors:    Klaus Aehlig, LMU Muenchen; Tobias Nipkow, Florian Haftmann, TU Muenchen

Normalization by evaluation, based on generic code generator.
*)

signature NBE =
sig
  val dynamic_conv: Proof.context -> conv
  val dynamic_value: Proof.context -> term -> term
  val static_conv: { ctxt: Proof.context, consts: string list }
    -> Proof.context -> conv
  val static_value: { ctxt: Proof.context, consts: string list }
    -> Proof.context -> term -> term

  datatype Type =
      Type of string * Type list
    | TParam of string
  datatype Univ =
      Const of (int * Type list) * Univ list (*named (uninterpreted) constants*)
    | DFree of string * int                  (*free (uninterpreted) dictionary parameters*)
    | BVar of int * Univ list                (*bound variables, named*)
    | Abs of (int * (Univ list -> Univ)) * Univ list
  val apps: Univ -> Univ list -> Univ        (*explicit applications*)
  val abss: int -> (Univ list -> Univ) -> Univ
                                             (*abstractions as closures*)
  val same: Univ * Univ -> bool

  val put_result: (unit -> (Type list -> Univ) list -> (Type list -> Univ) list)
    -> Proof.context -> Proof.context
  val trace: bool Config.T

  val add_const_alias: thm -> theory -> theory
end;

structure Nbe: NBE =
struct

(* generic non-sense *)

val trace = Attrib.setup_config_bool \<^binding>\<open>nbe_trace\<close> (K false);
fun traced ctxt f x = if Config.get ctxt trace then (tracing (f x); x) else x;


(** certificates and oracle for "trivial type classes" **)

structure Triv_Class_Data = Theory_Data
(
  type T = (class * thm) list;
  val empty = [];
  fun merge data : T = AList.merge (op =) (K true) data;
);

fun add_const_alias thm thy =
  let
    val (ofclass, eqn) = case try Logic.dest_equals (Thm.prop_of thm)
     of SOME ofclass_eq => ofclass_eq
      | _ => error ("Bad certificate: " ^ Thm.string_of_thm_global thy thm);
    val (T, class) = case try Logic.dest_of_class ofclass
     of SOME T_class => T_class
      | _ => error ("Bad certificate: " ^ Thm.string_of_thm_global thy thm);
    val tvar = case try Term.dest_TVar T
     of SOME (tvar as (_, sort)) => if null (filter (can (Axclass.get_info thy)) sort)
          then tvar
          else error ("Bad sort: " ^ Thm.string_of_thm_global thy thm)
      | _ => error ("Bad type: " ^ Thm.string_of_thm_global thy thm);
    val _ = if Term.add_tvars eqn [] = [tvar] then ()
      else error ("Inconsistent type: " ^ Thm.string_of_thm_global thy thm);
    val lhs_rhs = case try Logic.dest_equals eqn
     of SOME lhs_rhs => lhs_rhs
      | _ => error ("Not an equation: " ^ Syntax.string_of_term_global thy eqn);
    val c_c' = case try (apply2 (Axclass.unoverload_const thy o dest_Const)) lhs_rhs
     of SOME c_c' => c_c'
      | _ => error ("Not an equation with two constants: "
          ^ Syntax.string_of_term_global thy eqn);
    val _ = if the_list (Axclass.class_of_param thy (snd c_c')) = [class] then ()
      else error ("Inconsistent class: " ^ Thm.string_of_thm_global thy thm);
  in Triv_Class_Data.map (AList.update (op =) (class, Thm.trim_context thm)) thy end;

local

val get_triv_classes = map fst o Triv_Class_Data.get;

val (_, triv_of_class) =
  Theory.setup_result (Thm.add_oracle (\<^binding>\<open>triv_of_class\<close>,
    fn (thy, T, class) => Thm.global_cterm_of thy (Logic.mk_of_class (T, class))));

in

fun lift_triv_classes_conv orig_ctxt conv ct =
  let
    val thy = Proof_Context.theory_of orig_ctxt;
    val ctxt = Proof_Context.init_global thy;
      (*FIXME quasi-global context*)
    val algebra = Sign.classes_of thy;
    val triv_classes = get_triv_classes thy;
    fun additional_classes sort = filter_out (fn class => Sorts.sort_le algebra (sort, [class])) triv_classes;
    fun mk_entry (v, sort) =
      let
        val T = TFree (v, sort);
        val cT = Thm.ctyp_of ctxt T;
        val triv_sort = additional_classes sort;
      in
        (v, (Sorts.inter_sort algebra (sort, triv_sort),
          (cT, AList.make (fn class => Thm.of_class (cT, class)) sort
            @ AList.make (fn class => triv_of_class (thy, T, class)) triv_sort)))
      end;
    val vs_tab = map mk_entry (Term.add_tfrees (Thm.term_of ct) []);
    fun instantiate thm =
      let
        val tvars =
          Term.add_tvars (#1 (Logic.dest_equals (Logic.strip_imp_concl (Thm.prop_of thm)))) [];
        val instT = map2 (fn v => fn (_, (_, (cT, _))) => (v, cT)) tvars vs_tab;
      in Thm.instantiate (TVars.make instT, Vars.empty) thm end;
    fun of_class (TFree (v, _), class) =
          the (AList.lookup (op =) ((snd o snd o the o AList.lookup (op =) vs_tab) v) class)
      | of_class (T, _) = error ("Bad type " ^ Syntax.string_of_typ ctxt T);
    fun strip_of_class thm =
      let
        val prems_of_class = Thm.prop_of thm
          |> Logic.strip_imp_prems
          |> map (Logic.dest_of_class #> of_class);
      in fold Thm.elim_implies prems_of_class thm end;
  in
    ct
    |> Thm.term_of
    |> (map_types o map_type_tfree)
        (fn (v, _) => TFree (v, (fst o the o AList.lookup (op =) vs_tab) v))
    |> Thm.cterm_of ctxt
    |> conv ctxt
    |> Thm.strip_shyps
    |> Thm.varifyT_global
    |> Thm.unconstrainT
    |> instantiate
    |> strip_of_class
  end;

fun lift_triv_classes_rew ctxt rew t =
  let
    val thy = Proof_Context.theory_of ctxt;
    val algebra = Sign.classes_of thy;
    val triv_classes = get_triv_classes thy;
    val vs = Term.add_tfrees t [];
  in
    t
    |> (map_types o map_type_tfree)
        (fn (v, sort) => TFree (v, Sorts.inter_sort algebra (sort, triv_classes)))
    |> rew
    |> (map_types o map_type_tfree)
        (fn (v, sort) => TFree (v, the_default sort (AList.lookup (op =) vs v)))
  end;

end;


(** the semantic universe **)

(*
   Functions are given by their semantic function value. To avoid
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

datatype Type =
    Type of string * Type list
  | TParam of string

datatype Univ =
    Const of (int * Type list) * Univ list (*named (uninterpreted) constants*)
  | DFree of string * int                  (*free (uninterpreted) dictionary parameters*)
  | BVar of int * Univ list                (*bound variables, named*)
  | Abs of (int * (Univ list -> Univ)) * Univ list
                                           (*abstractions as closures*)

(* constructor functions *)

fun abss n f = Abs ((n, f), []);
fun apps (Abs ((n, f), us)) ws = let val k = n - length ws in
      case int_ord (k, 0)
       of EQUAL => f (ws @ us)
        | LESS => let val (ws1, ws2) = chop (~ k) ws in apps (f (ws2 @ us)) ws1 end
        | GREATER => Abs ((k, f), ws @ us) (*note: reverse convention also for apps!*)
      end
  | apps (Const (name, xs)) ys = Const (name, ys @ xs)
  | apps (BVar (n, xs)) ys = BVar (n, ys @ xs);

fun same_type (Type (tyco1, ty1), Type (tyco2, tys2)) =
      (tyco1 = tyco2) andalso eq_list same_type (ty1, tys2)
  | same_type (TParam v1, TParam v2) = (v1 = v2)
  | same_type _ = false;

fun same (Const ((k1, typargs1), us1), Const ((k2, typargs2), us2)) =
      (k1 = k2) andalso eq_list same_type (typargs1, typargs2) andalso eq_list same (us1, us2)
  | same (DFree (n1, i1), DFree (n2, i2)) = (n1 = n2) andalso (i1 = i2)
  | same (BVar (i1, us1), BVar (i2, us2)) = (i1 = i2) andalso eq_list same (us1, us2)
  | same _ = false;


(** assembling and compiling ML code from terms **)

(* abstract ML syntax *)

infix 9 `$` `$$`;
infix 8 `*`;
fun e1 `$` e2 = enclose "(" ")" (e1 ^ " " ^ e2);
fun e `$$` [] = e
  | e `$$` es = enclose "(" ")" (e ^ " " ^ implode_space es);
fun ml_abs v e = enclose "(" ")" ("fn " ^ v ^ " => " ^ e);

fun ml_cases e cs = enclose "(" ")"
  ("case " ^ e ^ " of " ^ space_implode " | " (map (fn (p, e) => p ^ " => " ^ e) cs));
fun ml_let d e = "\n  let\n" ^ prefix_lines "    " d ^ "\n  in " ^ e ^ " end";

fun ml_and [] = "true"
  | ml_and [e] = e
  | ml_and es = enclose "(" ")" (space_implode " andalso " es);
fun ml_if b e1 e2 = enclose "(" ")" (implode_space ["if", b, "then", e1, "else", e2]);

fun e1 `*` e2 = enclose "(" ")" (e1 ^ ", " ^ e2);
fun ml_list es = enclose "[" "]" (commas es);

fun ml_exc s = enclose "(" ")" ("raise Fail " ^ quote s);

fun ml_fundefs ([(name, [([], e)])]) =
      "val " ^ name ^ " = " ^ e ^ ""
  | ml_fundefs (eqs :: eqss) =
      let
        fun fundef (name, eqs) =
          let
            fun eqn (es, e) = name ^ " " ^ implode_space es ^ " = " ^ e
          in space_implode "\n  | " (map eqn eqs) end;
      in
        (prefix "fun " o fundef) eqs :: map (prefix "and " o fundef) eqss
        |> cat_lines
      end;


(* nbe specific syntax and sandbox communication *)

structure Univs = Proof_Data
(
  type T = unit -> (Type list -> Univ) list -> (Type list -> Univ) list;
  val empty: T = fn () => raise Fail "Univs";
  fun init _ = empty;
);
val get_result = Univs.get;
val put_result = Univs.put;

local
  val prefix = "Nbe.";
  val name_put = prefix ^ "put_result";
  val name_const = prefix ^ "Const";
  val name_type = prefix ^ "Type";
  val name_abss = prefix ^ "abss";
  val name_apps = prefix ^ "apps";
  val name_same = prefix ^ "same";
in

val univs_cookie = (get_result, put_result, name_put);

(*
  Convention: parameters representing ("assembled") string representations of logical entities
  are prefixed with an "a_" -- unless they are an unqualified name ready to become part of
  an ML identifier.
*)

fun nbe_tparam v = "t_" ^ v;
fun nbe_dict v n = "d_" ^ v ^ "_" ^ string_of_int n;
fun nbe_global_param v = "w_" ^ v;
fun nbe_bound v = "v_" ^ v;
fun nbe_bound_optional NONE = "_"
  | nbe_bound_optional (SOME v) = nbe_bound v;
fun nbe_type a_sym a_tys = name_type `$` (quote a_sym `*` ml_list a_tys);
fun nbe_fun a_sym a_typargs = a_sym `$` ml_list a_typargs;

(*note: these are the "turning spots" where proper argument order is established!*)
fun nbe_apps a_u [] = a_u
  | nbe_apps a_u a_us = name_apps `$$` [a_u, ml_list (rev a_us)];
fun nbe_apps_fun a_sym a_typargs a_us = nbe_fun a_sym a_typargs `$` ml_list (rev a_us);
fun nbe_apps_fallback_fun a_sym a_us = a_sym `$$` a_us;
fun nbe_apps_constr a_sym a_typargs a_us = name_const `$` ((a_sym `*` ml_list a_typargs) `*` ml_list (rev a_us));
fun nbe_apps_constmatch a_sym a_us = name_const `$` ((a_sym `*` "_") `*` ml_list (rev a_us));

fun nbe_abss 0 f = f `$` ml_list []
  | nbe_abss n f = name_abss `$$` [string_of_int n, f];

fun nbe_same (v1, v2) = enclose "(" ")" (name_same `$` (nbe_bound v1 `*` nbe_bound v2));

end;

open Basic_Code_Symbol;
open Basic_Code_Thingol;


(* code generation *)

fun subst_nonlin_vars args =
  let
    val vs = (fold o Code_Thingol.fold_varnames)
      (fn v => AList.map_default (op =) (v, 0) (Integer.add 1)) args [];
    val names = Name.make_context (map fst vs);
    val (vs_renames, _) = fold_map (fn (v, k) => if k > 1
      then Name.invent' v (k - 1) #>> (fn vs => (v, vs))
      else pair (v, [])) vs names;
    val samepairs = maps (fn (v, vs) => map (pair v) vs) vs_renames;
    fun subst_vars (t as IConst _) samepairs = (t, samepairs)
      | subst_vars (t as IVar NONE) samepairs = (t, samepairs)
      | subst_vars (t as IVar (SOME v)) samepairs = (case AList.lookup (op =) samepairs v
         of SOME v' => (IVar (SOME v'), AList.delete (op =) v samepairs)
          | NONE => (t, samepairs))
      | subst_vars (t1 `$ t2) samepairs = samepairs
          |> subst_vars t1
          ||>> subst_vars t2
          |>> (op `$)
      | subst_vars (ICase { primitive = t, ... }) samepairs = subst_vars t samepairs;
    val (args', _) = fold_map subst_vars args samepairs;
  in (samepairs, args') end;

fun preprocess_eqns (sym, (vs, eqns)) =
  let
    val a_tparams = map (fn (v, _) => nbe_tparam v) vs;
    val a_dict_params = maps (fn (v, sort) => map_index (nbe_dict v o fst) sort) vs;
    val num_args = length a_dict_params + ((length o fst o hd) eqns);
    val a_global_params = map nbe_global_param (Name.invent_global "a" (num_args - length a_dict_params));
  in (sym, (num_args, (a_tparams, a_dict_params, a_global_params, (map o apfst) subst_nonlin_vars eqns))) end;

fun assemble_type (tyco `%% tys) = nbe_type tyco (map assemble_type tys)
  | assemble_type (ITyVar v) = nbe_tparam v

fun assemble_preprocessed_eqnss ctxt idx_of_sym deps eqnss =
  let
    fun suffixed_fun_ident suffix sym = space_implode "_"
      ["c", if Code_Symbol.is_value sym then "value" else string_of_int (idx_of_sym sym),
      Code_Symbol.default_base sym, suffix];
    val fun_ident = suffixed_fun_ident "nbe";
    fun fallback_fun_ident i = suffixed_fun_ident (string_of_int i);
    fun constr_ident sym =
      if Config.get ctxt trace
      then string_of_int (idx_of_sym sym) ^ " (*" ^ Code_Symbol.default_base sym ^ "*)"
      else string_of_int (idx_of_sym sym);

    fun assemble_fun sym = nbe_fun (fun_ident sym);
    fun assemble_app_fun sym = nbe_apps_fun (fun_ident sym);
    fun assemble_app_fallback_fun i sym = nbe_apps_fallback_fun (fallback_fun_ident i sym);
    fun assemble_app_constr sym = nbe_apps_constr (constr_ident sym);
    fun assemble_app_constmatch sym = nbe_apps_constmatch (constr_ident sym);

    fun assemble_constapp sym typargs dictss a_ts =
      let
        val a_typargs = map (assemble_type) typargs;
        val a_ts' = (maps o map) assemble_dict (map2 (fn ty => map (fn dict => (ty, dict))) typargs dictss) @ a_ts;
      in case AList.lookup (op =) eqnss sym
       of SOME (num_args, _) => if num_args <= length a_ts'
            then let val (a_ts1, a_ts2) = chop num_args a_ts'
            in nbe_apps (assemble_app_fun sym a_typargs a_ts1) a_ts2
            end else nbe_apps (nbe_abss num_args (assemble_fun sym a_typargs)) a_ts'
        | NONE => if member (op =) deps sym
            then nbe_apps (assemble_fun sym a_typargs) a_ts'
            else assemble_app_constr sym a_typargs a_ts'
      end
    and assemble_classrels classrels =
      fold_rev (fn classrel => assemble_constapp (Class_Relation classrel) [] [] o single) classrels
    and assemble_dict (ty, Dict (classrels, dict)) =
          assemble_classrels classrels (assemble_plain_dict ty dict)
    and assemble_plain_dict (_ `%% tys) (Dict_Const (inst, dictss)) =
          assemble_constapp (Class_Instance inst) tys (map snd dictss) []
      | assemble_plain_dict _ (Dict_Var { var, index, ... }) =
          nbe_dict var index

    fun assemble_constmatch sym _ dictss a_ts =
      assemble_app_constmatch sym ((maps o map) (K "_") dictss @ a_ts);

    fun assemble_iterm constapp =
      let
        fun of_iterm match_continuation t =
          let
            val (t', ts) = Code_Thingol.unfold_app t
          in of_iapp match_continuation t' (fold_rev (cons o of_iterm NONE) ts []) end
        and of_iapp match_continuation (IConst { sym, typargs, dictss, ... }) = constapp sym typargs dictss
          | of_iapp match_continuation (IVar v) = nbe_apps (nbe_bound_optional v)
          | of_iapp match_continuation ((v, _) `|=> (t, _)) =
              nbe_apps (nbe_abss 1 (ml_abs (ml_list [nbe_bound_optional v]) (of_iterm NONE t)))
          | of_iapp match_continuation (ICase { term = t, clauses = clauses, primitive = t0, ... }) =
              nbe_apps (ml_cases (of_iterm NONE t)
                (map (fn (p, t) => (assemble_iterm assemble_constmatch NONE p, of_iterm match_continuation t)) clauses
                  @ [("_", case match_continuation of SOME s => s | NONE => of_iterm NONE t0)]))
      in of_iterm end;

    val assemble_args = map (assemble_iterm assemble_constmatch NONE);
    val assemble_rhs = assemble_iterm assemble_constapp;

    fun assemble_fallback_fundef sym a_global_params ((samepairs, args), rhs) a_fallback_rhs =
      let
        val a_rhs_core = assemble_rhs (SOME a_fallback_rhs) rhs;
        val a_rhs = if null samepairs then a_rhs_core
          else ml_if (ml_and (map nbe_same samepairs)) a_rhs_core a_fallback_rhs;
        val a_fallback_eqn = if forall Code_Thingol.is_IVar args then NONE
          else SOME (replicate (length a_global_params) "_", a_fallback_rhs);
      in (assemble_args args, a_rhs) :: the_list a_fallback_eqn end;

    fun assemble_fallback_fundefs sym a_tparams a_dict_params a_global_params [(([], []), rhs)] =
          assemble_rhs NONE rhs
      | assemble_fallback_fundefs sym a_tparams a_dict_params a_global_params eqns =
          let
            val a_fallback_syms = map_range (fn i => fallback_fun_ident i sym) (length eqns);
            val a_fallback_rhss =
              map_range (fn i => assemble_app_fallback_fun (i + 1) sym a_global_params) (length eqns - 1)
              @ [assemble_app_constr sym a_tparams (a_dict_params @ a_global_params)];
          in
            ml_let (ml_fundefs (a_fallback_syms ~~
              map2 (assemble_fallback_fundef sym a_global_params) eqns a_fallback_rhss))
              (assemble_app_fallback_fun 0 sym a_global_params)
          end;

    fun assemble_fundef (sym, (num_args, (a_tparams, a_dict_params, a_global_params, eqns))) =
      let
        val a_lhs = [ml_list a_tparams, ml_list (rev (a_dict_params @ a_global_params))];
        val a_rhs = assemble_fallback_fundefs sym a_tparams a_dict_params a_global_params eqns;
        val a_univ = ml_abs (ml_list a_tparams) (nbe_abss num_args (assemble_fun sym a_tparams));
      in
        ((fun_ident sym, [(a_lhs, a_rhs), (a_lhs, ml_exc (fun_ident sym))]), a_univ)
      end;

    val (a_fun_defs, a_fun_vals) = map_split assemble_fundef eqnss;
    val dep_params = ml_list (map fun_ident deps);
  in ml_abs dep_params (ml_let (ml_fundefs a_fun_defs) (ml_list a_fun_vals)) end;

fun assemble_eqnss ctxt idx_of_sym deps eqnss =
  assemble_preprocessed_eqnss ctxt idx_of_sym deps (map preprocess_eqns eqnss);


(* compilation of equations *)

fun compile_eqnss ctxt nbe_program raw_deps [] = []
  | compile_eqnss ctxt nbe_program raw_deps eqnss =
      let
        val (deps, deps_vals) = split_list (map_filter
          (fn dep => Option.map (fn univ => (dep, univ)) (fst ((Code_Symbol.Graph.get_node nbe_program dep)))) raw_deps);
        val idx_of_sym = raw_deps
          |> map (fn dep => (dep, snd (Code_Symbol.Graph.get_node nbe_program dep)))
          |> AList.lookup (op =)
          |> (fn f => the o f);
        val s = assemble_eqnss ctxt idx_of_sym deps eqnss;
        val syms = map fst eqnss;
      in
        s
        |> traced ctxt (fn s => "\n--- code to be evaluated:\n" ^ s)
        |> pair ""
        |> Code_Runtime.value ctxt univs_cookie
        |> (fn dependent_fs => dependent_fs deps_vals)
        |> (fn fs => syms ~~ fs)
      end;


(* extraction of equations from statements *)

fun dummy_const sym typargs dictss =
  IConst { sym = sym, typargs = typargs, dictss = dictss,
    dom = [], annotation = NONE, range = ITyVar "" };

fun eqns_of_stmt (_, Code_Thingol.NoStmt) =
      []
  | eqns_of_stmt (_, Code_Thingol.Fun ((_, []), _)) =
      []
  | eqns_of_stmt (sym_const, Code_Thingol.Fun (((vs, _), eqns), _)) =
      [(sym_const, (vs, map fst eqns))]
  | eqns_of_stmt (_, Code_Thingol.Datatypecons _) =
      []
  | eqns_of_stmt (_, Code_Thingol.Datatype _) =
      []
  | eqns_of_stmt (sym_class, Code_Thingol.Class (v, (classrels, classparams))) =
      let
        val syms = map (rpair [] o Class_Relation) classrels @ map (rpair [(v, [])] o Constant o fst) classparams;
        val params = Name.invent_global "d" (length syms);
        fun mk (k, (sym, vs)) =
          (sym, (vs,
            [([dummy_const sym_class [] [] `$$ map (IVar o SOME) params],
              IVar (SOME (nth params k)))]));
      in map_index mk syms end
  | eqns_of_stmt (_, Code_Thingol.Classrel _) =
      []
  | eqns_of_stmt (_, Code_Thingol.Classparam _) =
      []
  | eqns_of_stmt (sym_inst, Code_Thingol.Classinst { class, tyco, vs, superinsts, inst_params, ... }) =
      [(sym_inst, (vs, [([], dummy_const (Type_Class class) [] [] `$$
        map (fn (class, dictss) =>
          dummy_const (Class_Instance (tyco, class)) (map (ITyVar o fst) vs) (map snd dictss)) superinsts
          @ map (IConst o fst o snd o fst) inst_params)]))];


(* compilation of whole programs *)

fun ensure_sym_idx sym (nbe_program, (max_idx, sym_tab)) =
  if can (Code_Symbol.Graph.get_node nbe_program) sym
  then (nbe_program, (max_idx, sym_tab))
  else (Code_Symbol.Graph.new_node (sym, (NONE, max_idx)) nbe_program,
    (max_idx + 1, Inttab.update_new (max_idx, sym) sym_tab));

fun compile_stmts ctxt stmts_deps =
  let
    val names = map (fst o fst) stmts_deps;
    val names_deps = map (fn ((name, _), deps) => (name, deps)) stmts_deps;
    val eqnss = maps (eqns_of_stmt o fst) stmts_deps;
    val refl_deps = names_deps
      |> maps snd
      |> distinct (op =)
      |> fold (insert (op =)) names;
    fun compile nbe_program = eqnss
      |> compile_eqnss ctxt nbe_program refl_deps
      |> rpair nbe_program;
  in
    fold ensure_sym_idx refl_deps
    #> apfst (fold (fn (name, deps) => fold (curry Code_Symbol.Graph.add_edge name) deps) names_deps
      #> compile
      #-> fold (fn (sym, univ) => (Code_Symbol.Graph.map_node sym o apfst) (K (SOME univ))))
  end;

fun compile_program { ctxt, program } =
  let
    fun add_stmts names (nbe_program, (max_idx, sym_tab)) =
      if exists ((can o Code_Symbol.Graph.get_node) nbe_program) names
      then (nbe_program, (max_idx, sym_tab))
      else (nbe_program, (max_idx, sym_tab))
        |> compile_stmts ctxt (map (fn sym => ((sym, Code_Symbol.Graph.get_node program sym),
          Code_Symbol.Graph.immediate_succs program sym)) names);
  in
    fold_rev add_stmts (Code_Symbol.Graph.strong_conn program)
  end;


(** normalization **)

(* compilation and reconstruction of terms *)

fun ad_hoc_eqn_of_term ((vs, _) : typscheme, t) =
  (Code_Symbol.value, (vs, [([], t)]));

fun compile_term { ctxt, nbe_program, deps, tfrees, vs_ty_t = vs_ty_t as ((vs, _), _) } =
  let
    val tparams = map (fn (v, _) => TParam v) tfrees;
    val dict_frees = maps (fn (v, sort) => map_index (curry DFree v o fst) sort) vs;
  in
    ad_hoc_eqn_of_term vs_ty_t
    |> singleton (compile_eqnss ctxt nbe_program deps)
    |> snd
    |> (fn f => apps (f tparams) (rev dict_frees))
  end;

fun reconstruct_term ctxt sym_tab tfrees =
  let
    fun take_until f [] = []
      | take_until f (x :: xs) = if f x then [] else x :: take_until f xs;
    fun is_dict (Const ((idx, _), _)) =
          (case Inttab.lookup sym_tab idx of
            SOME (Constant _) => false
          | _ => true)
      | is_dict (DFree _) = true
      | is_dict _ = false;
    fun const_of_idx idx =
      case Inttab.lookup sym_tab idx of SOME (Constant const) => const;
    fun reconstruct_type (Type (tyco, tys)) = Term.Type (tyco, map reconstruct_type tys)
      | reconstruct_type (TParam v) = TFree (v, the (AList.lookup (op =) tfrees v));
    fun of_apps bounds (t, ts) =
      list_comb (t, rev (map (of_univ bounds) ts))
    and of_univ bounds (Const ((idx, tparams), us)) =
          let
            val const = const_of_idx idx;
            val us' = take_until is_dict us;
            val T = Consts.instance (Proof_Context.consts_of ctxt) (const, map reconstruct_type tparams);
          in of_apps bounds (Term.Const (const, T), us') end
      | of_univ bounds (BVar (i, us)) =
          of_apps bounds (Bound (bounds - i - 1), us)
      | of_univ bounds (u as Abs _) =
          Term.Abs ("u", dummyT, of_univ (bounds + 1) (apps u [BVar (bounds, [])]))
  in of_univ 0 end;

fun compile_and_reconstruct_term { ctxt, nbe_program, sym_tab, deps, tfrees, vs_ty_t } =
  compile_term { ctxt = ctxt, nbe_program = nbe_program, deps = deps, tfrees = tfrees, vs_ty_t = vs_ty_t }
  |> reconstruct_term ctxt sym_tab tfrees;

fun retype_term ctxt t T =
  let
    val ctxt' =
      ctxt
      |> Variable.declare_typ T
      |> Config.put Type_Infer.object_logic false
      |> Config.put Type_Infer_Context.const_sorts false
  in
    singleton (Variable.export_terms ctxt' ctxt') (Syntax.check_term ctxt' (Type.constraint T t))
  end;

fun normalize_term (nbe_program, sym_tab) raw_ctxt t_original vs_ty_t deps =
  let
    val T = fastype_of t_original;
    val tfrees = Term.add_tfrees t_original [];
    val ctxt = Syntax.init_pretty_global (Proof_Context.theory_of raw_ctxt);
    val string_of_term =
      Syntax.string_of_term
         (ctxt
           |> Config.put show_types true
           |> Config.put show_sorts true);
    fun retype t' = retype_term ctxt t' T;
    fun check_tvars t' =
      if null (Term.add_tvars t' []) then t'
      else error ("Illegal schematic type variables in normalized term: " ^ string_of_term t');
  in
    Code_Preproc.timed "computing NBE expression" #ctxt compile_and_reconstruct_term
      { ctxt = ctxt, nbe_program = nbe_program, sym_tab = sym_tab, deps = deps,
        tfrees = tfrees, vs_ty_t = vs_ty_t }
    |> traced ctxt (fn t => "Normalized:\n" ^ string_of_term t)
    |> retype
    |> traced ctxt (fn t => "Types inferred:\n" ^ string_of_term t)
    |> check_tvars
    |> traced ctxt (fn _ => "---\n")
  end;


(* function store *)

structure Nbe_Functions = Code_Data
(
  type T = ((Type list -> Univ) option * int) Code_Symbol.Graph.T * (int * Code_Symbol.T Inttab.table);
  val empty = (Code_Symbol.Graph.empty, (0, Inttab.empty));
);

fun compile ignore_cache ctxt program =
  let
    val (nbe_program, (_, sym_tab)) =
      Nbe_Functions.change (if ignore_cache then NONE else SOME (Proof_Context.theory_of ctxt))
        (Code_Preproc.timed "compiling NBE program" #ctxt
          compile_program { ctxt = ctxt, program = program });
  in (nbe_program, sym_tab) end;


(* evaluation oracle *)

fun mk_equals ctxt lhs raw_rhs =
  let
    val ty = Thm.typ_of_cterm lhs;
    val eq = Thm.cterm_of ctxt \<^Const>\<open>Pure.eq ty\<close>;
    val rhs = Thm.cterm_of ctxt raw_rhs;
  in Thm.mk_binop eq lhs rhs end;

val (_, raw_oracle) =
  Theory.setup_result (Thm.add_oracle (\<^binding>\<open>normalization_by_evaluation\<close>,
    fn (nbe_program_sym_tab, ctxt, vs_ty_t, deps, ct) =>
      mk_equals ctxt ct (normalize_term nbe_program_sym_tab ctxt (Thm.term_of ct) vs_ty_t deps)));

fun oracle nbe_program_sym_tab ctxt vs_ty_t deps ct =
  raw_oracle (nbe_program_sym_tab, ctxt, vs_ty_t, deps, ct);

fun dynamic_conv ctxt = lift_triv_classes_conv ctxt
  (fn ctxt' => Code_Thingol.dynamic_conv ctxt' (fn program =>
    oracle (compile false ctxt program) ctxt'));

fun dynamic_value ctxt = lift_triv_classes_rew ctxt
  (Code_Thingol.dynamic_value ctxt I (fn program =>
    normalize_term (compile false ctxt program) ctxt));

fun static_conv (ctxt_consts as { ctxt, ... }) =
  let
    val conv = Code_Thingol.static_conv_thingol ctxt_consts
      (fn { program, deps = _ } => oracle (compile true ctxt program));
  in fn ctxt' => lift_triv_classes_conv ctxt' conv end;

fun static_value { ctxt, consts } =
  let
    val comp = Code_Thingol.static_value { ctxt = ctxt, lift_postproc = I, consts = consts }
      (fn { program, deps = _ } => normalize_term (compile false ctxt program));
  in fn ctxt' => lift_triv_classes_rew ctxt' (comp ctxt') end;

end;
