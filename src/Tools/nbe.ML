(*  Title:      Tools/nbe.ML
    Authors:    Klaus Aehlig, LMU Muenchen; Tobias Nipkow, Florian Haftmann, TU Muenchen

Normalization by evaluation, based on generic code generator.
*)

signature NBE =
sig
  val norm_conv: cterm -> thm
  val norm: theory -> term -> term

  datatype Univ =
      Const of int * Univ list               (*named (uninterpreted) constants*)
    | DFree of string * int                  (*free (uninterpreted) dictionary parameters*)
    | BVar of int * Univ list
    | Abs of (int * (Univ list -> Univ)) * Univ list
  val apps: Univ -> Univ list -> Univ        (*explicit applications*)
  val abss: int -> (Univ list -> Univ) -> Univ
                                             (*abstractions as closures*)
  val same: Univ -> Univ -> bool

  val univs_ref: (unit -> Univ list -> Univ list) option Unsynchronized.ref
  val trace: bool Unsynchronized.ref

  val setup: theory -> theory
  val add_const_alias: thm -> theory -> theory
end;

structure Nbe: NBE =
struct

(* generic non-sense *)

val trace = Unsynchronized.ref false;
fun traced f x = if !trace then (tracing (f x); x) else x;


(** certificates and oracle for "trivial type classes" **)

structure Triv_Class_Data = Theory_Data
(
  type T = (class * thm) list;
  val empty = [];
  val extend = I;
  fun merge data : T = AList.merge (op =) (K true) data;
);

fun add_const_alias thm thy =
  let
    val (ofclass, eqn) = case try Logic.dest_equals (Thm.prop_of thm)
     of SOME ofclass_eq => ofclass_eq
      | _ => error ("Bad certificate: " ^ Display.string_of_thm_global thy thm);
    val (T, class) = case try Logic.dest_of_class ofclass
     of SOME T_class => T_class
      | _ => error ("Bad certificate: " ^ Display.string_of_thm_global thy thm);
    val tvar = case try Term.dest_TVar T
     of SOME (tvar as (_, sort)) => if null (filter (can (AxClass.get_info thy)) sort)
          then tvar
          else error ("Bad sort: " ^ Display.string_of_thm_global thy thm)
      | _ => error ("Bad type: " ^ Display.string_of_thm_global thy thm);
    val _ = if Term.add_tvars eqn [] = [tvar] then ()
      else error ("Inconsistent type: " ^ Display.string_of_thm_global thy thm);
    val lhs_rhs = case try Logic.dest_equals eqn
     of SOME lhs_rhs => lhs_rhs
      | _ => error ("Not an equation: " ^ Syntax.string_of_term_global thy eqn);
    val c_c' = case try (pairself (Code.check_const thy)) lhs_rhs
     of SOME c_c' => c_c'
      | _ => error ("Not an equation with two constants: "
          ^ Syntax.string_of_term_global thy eqn);
    val _ = if the_list (AxClass.class_of_param thy (snd c_c')) = [class] then ()
      else error ("Inconsistent class: " ^ Display.string_of_thm_global thy thm);
  in Triv_Class_Data.map (AList.update (op =) (class, thm)) thy end;

local

val get_triv_classes = map fst o Triv_Class_Data.get;

val (_, triv_of_class) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (Binding.name "triv_of_class", fn (thy, (v, T), class) =>
    Thm.cterm_of thy (Logic.mk_of_class (T, class)))));

in

fun lift_triv_classes_conv thy conv ct =
  let
    val algebra = Sign.classes_of thy;
    val triv_classes = get_triv_classes thy;
    val certT = Thm.ctyp_of thy;
    fun critical_classes sort = filter_out (fn class => Sign.subsort thy (sort, [class])) triv_classes;
    val vs = Term.add_tfrees (Thm.term_of ct) []
      |> map_filter (fn (v, sort) => case critical_classes sort
          of [] => NONE
           | classes => SOME (v, ((sort, classes), Sorts.inter_sort algebra (triv_classes, sort))));
    val of_classes = maps (fn (v, ((sort, classes), _)) => map (fn class =>
      ((v, class), triv_of_class (thy, (v, TVar ((v, 0), sort)), class))) classes
      @ map (fn class => ((v, class), Thm.of_class (certT (TVar ((v, 0), sort)), class)))
        sort) vs;
    fun strip_of_class thm =
      let
        val prem_props = (Logic.strip_imp_prems o Thm.prop_of) thm;
        val prem_thms = map (the o AList.lookup (op =) of_classes
          o apfst (fst o fst o dest_TVar) o Logic.dest_of_class) prem_props;
      in Drule.implies_elim_list thm prem_thms end;
  in ct
    |> Drule.cterm_rule Thm.varifyT
    |> Thm.instantiate_cterm (Thm.certify_inst thy (map (fn (v, ((sort, _), sort')) =>
        (((v, 0), sort), TFree (v, sort'))) vs, []))
    |> Drule.cterm_rule Thm.freezeT
    |> conv
    |> Thm.varifyT
    |> fold (fn (v, (_, sort')) => Thm.unconstrainT (certT (TVar ((v, 0), sort')))) vs
    |> Thm.certify_instantiate (map (fn (v, ((sort, _), _)) =>
        (((v, 0), []), TVar ((v, 0), sort))) vs, [])
    |> strip_of_class
    |> Thm.freezeT
  end;

fun lift_triv_classes_rew thy rew t =
  let
    val algebra = Sign.classes_of thy;
    val triv_classes = get_triv_classes thy;
    val vs = Term.add_tfrees t [];
  in t
    |> (map_types o map_type_tfree)
        (fn (v, sort) => TFree (v, Sorts.inter_sort algebra (sort, triv_classes)))
    |> rew
    |> (map_types o map_type_tfree)
        (fn (v, _) => TFree (v, the (AList.lookup (op =) vs v)))
  end;

end;


(** the semantic universe **)

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
  | DFree of string * int              (*free (uninterpreted) dictionary parameters*)
  | BVar of int * Univ list            (*bound variables, named*)
  | Abs of (int * (Univ list -> Univ)) * Univ list
                                       (*abstractions as closures*);

fun same (Const (k, xs)) (Const (l, ys)) = k = l andalso sames xs ys
  | same (DFree (s, k)) (DFree (t, l)) = s = t andalso k = l
  | same (BVar (k, xs)) (BVar (l, ys)) = k = l andalso sames xs ys
  | same _ _ = false
and sames xs ys = length xs = length ys andalso forall (uncurry same) (xs ~~ ys);

(* constructor functions *)

fun abss n f = Abs ((n, f), []);
fun apps (Abs ((n, f), xs)) ys = let val k = n - length ys in
      case int_ord (k, 0)
       of EQUAL => f (ys @ xs)
        | LESS => let val (zs, ws) = chop (~ k) ys in apps (f (ws @ xs)) zs end
        | GREATER => Abs ((k, f), ys @ xs) (*note: reverse convention also for apps!*)
      end
  | apps (Const (name, xs)) ys = Const (name, ys @ xs)
  | apps (BVar (n, xs)) ys = BVar (n, ys @ xs);


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
fun ml_as v t = "(" ^ v ^ " as " ^ t ^ ")";

fun ml_and [] = "true"
  | ml_and [x] = x
  | ml_and xs = "(" ^ space_implode " andalso " xs ^ ")";
fun ml_if b x y = "(if " ^ b ^ " then " ^ x ^ " else " ^ y ^ ")";

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

val univs_ref = Unsynchronized.ref (NONE : (unit -> Univ list -> Univ list) option);

local
  val prefix =      "Nbe.";
  val name_ref =    prefix ^ "univs_ref";
  val name_const =  prefix ^ "Const";
  val name_abss =   prefix ^ "abss";
  val name_apps =   prefix ^ "apps";
  val name_same =   prefix ^ "same";
in

val univs_cookie = (name_ref, univs_ref);

fun nbe_fun 0 "" = "nbe_value"
  | nbe_fun i c = "c_" ^ translate_string (fn "." => "_" | c => c) c ^ "_" ^ string_of_int i;
fun nbe_dict v n = "d_" ^ v ^ "_" ^ string_of_int n;
fun nbe_bound v = "v_" ^ v;
fun nbe_bound_optional NONE = "_"
  | nbe_bound_optional  (SOME v) = nbe_bound v;
fun nbe_default v = "w_" ^ v;

(*note: these three are the "turning spots" where proper argument order is established!*)
fun nbe_apps t [] = t
  | nbe_apps t ts = name_apps `$$` [t, ml_list (rev ts)];
fun nbe_apps_local i c ts = nbe_fun i c `$` ml_list (rev ts);
fun nbe_apps_constr idx_of c ts =
  let
    val c' = if !trace then string_of_int (idx_of c) ^ " (*" ^ c ^ "*)"
      else string_of_int (idx_of c);
  in name_const `$` ("(" ^ c' ^ ", " ^ ml_list (rev ts) ^ ")") end;

fun nbe_abss 0 f = f `$` ml_list []
  | nbe_abss n f = name_abss `$$` [string_of_int n, f];

fun nbe_same v1 v2 = "(" ^ name_same ^ " " ^ nbe_bound v1 ^ " " ^ nbe_bound v2 ^ ")";

end;

open Basic_Code_Thingol;

(* code generation *)

fun assemble_eqnss idx_of deps eqnss =
  let
    fun prep_eqns (c, (vs, eqns)) =
      let
        val dicts = maps (fn (v, sort) => map_index (nbe_dict v o fst) sort) vs;
        val num_args = length dicts + ((length o fst o hd) eqns);
      in (c, (num_args, (dicts, eqns))) end;
    val eqnss' = map prep_eqns eqnss;

    fun assemble_constapp c dss ts = 
      let
        val ts' = (maps o map) assemble_idict dss @ ts;
      in case AList.lookup (op =) eqnss' c
       of SOME (num_args, _) => if num_args <= length ts'
            then let val (ts1, ts2) = chop num_args ts'
            in nbe_apps (nbe_apps_local 0 c ts1) ts2
            end else nbe_apps (nbe_abss num_args (nbe_fun 0 c)) ts'
        | NONE => if member (op =) deps c
            then nbe_apps (nbe_fun 0 c) ts'
            else nbe_apps_constr idx_of c ts'
      end
    and assemble_idict (DictConst (inst, dss)) =
          assemble_constapp inst dss []
      | assemble_idict (DictVar (supers, (v, (n, _)))) =
          fold_rev (fn super => assemble_constapp super [] o single) supers (nbe_dict v n);

    fun assemble_iterm constapp =
      let
        fun of_iterm match_cont t =
          let
            val (t', ts) = Code_Thingol.unfold_app t
          in of_iapp match_cont t' (fold_rev (cons o of_iterm NONE) ts []) end
        and of_iapp match_cont (IConst (c, ((_, dss), _))) ts = constapp c dss ts
          | of_iapp match_cont (IVar v) ts = nbe_apps (nbe_bound_optional v) ts
          | of_iapp match_cont ((v, _) `|=> t) ts =
              nbe_apps (nbe_abss 1 (ml_abs (ml_list [nbe_bound_optional v]) (of_iterm NONE t))) ts
          | of_iapp match_cont (ICase (((t, _), cs), t0)) ts =
              nbe_apps (ml_cases (of_iterm NONE t)
                (map (fn (p, t) => (of_iterm NONE p, of_iterm match_cont t)) cs
                  @ [("_", case match_cont of SOME s => s | NONE => of_iterm NONE t0)])) ts
      in of_iterm end;

    fun subst_nonlin_vars args =
      let
        val vs = (fold o Code_Thingol.fold_varnames)
          (fn v => AList.map_default (op =) (v, 0) (Integer.add 1)) args [];
        val names = Name.make_context (map fst vs);
        fun declare v k ctxt = let val vs = Name.invents ctxt v k
          in (vs, fold Name.declare vs ctxt) end;
        val (vs_renames, _) = fold_map (fn (v, k) => if k > 1
          then declare v (k - 1) #>> (fn vs => (v, vs))
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
          | subst_vars (ICase (_, t)) samepairs = subst_vars t samepairs;
        val (args', _) = fold_map subst_vars args samepairs;
      in (samepairs, args') end;

    fun assemble_eqn c dicts default_args (i, (args, rhs)) =
      let
        val is_eval = (c = "");
        val default_rhs = nbe_apps_local (i+1) c (dicts @ default_args);
        val match_cont = if is_eval then NONE else SOME default_rhs;
        val assemble_arg = assemble_iterm
          (fn c => fn _ => fn ts => nbe_apps_constr idx_of c ts) NONE;
        val assemble_rhs = assemble_iterm assemble_constapp match_cont ;
        val (samepairs, args') = subst_nonlin_vars args;
        val s_args = map assemble_arg args';
        val s_rhs = if null samepairs then assemble_rhs rhs
          else ml_if (ml_and (map (uncurry nbe_same) samepairs))
            (assemble_rhs rhs) default_rhs;
        val eqns = if is_eval then
            [([ml_list (rev (dicts @ s_args))], s_rhs)]
          else
            [([ml_list (rev (dicts @ map2 ml_as default_args s_args))], s_rhs),
              ([ml_list (rev (dicts @ default_args))], default_rhs)]
      in (nbe_fun i c, eqns) end;

    fun assemble_eqns (c, (num_args, (dicts, eqns))) =
      let
        val default_args = map nbe_default
          (Name.invent_list [] "a" (num_args - length dicts));
        val eqns' = map_index (assemble_eqn c dicts default_args) eqns
          @ (if c = "" then [] else [(nbe_fun (length eqns) c,
            [([ml_list (rev (dicts @ default_args))],
              nbe_apps_constr idx_of c (dicts @ default_args))])]);
      in (eqns', nbe_abss num_args (nbe_fun 0 c)) end;

    val (fun_vars, fun_vals) = map_split assemble_eqns eqnss';
    val deps_vars = ml_list (map (nbe_fun 0) deps);
  in ml_abs deps_vars (ml_Let (ml_fundefs (flat fun_vars)) (ml_list fun_vals)) end;

(* code compilation *)

fun compile_eqnss _ gr raw_deps [] = []
  | compile_eqnss ctxt gr raw_deps eqnss =
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
        |> traced (fn s => "\n--- code to be evaluated:\n" ^ s)
        |> ML_Context.evaluate ctxt (!trace) univs_cookie
        |> (fn f => f deps_vals)
        |> (fn univs => cs ~~ univs)
      end;


(* preparing function equations *)

fun eqns_of_stmt (_, Code_Thingol.Fun (_, (_, []))) =
      []
  | eqns_of_stmt (const, Code_Thingol.Fun (_, ((vs, _), eqns))) =
      [(const, (vs, map fst eqns))]
  | eqns_of_stmt (_, Code_Thingol.Datatypecons _) =
      []
  | eqns_of_stmt (_, Code_Thingol.Datatype _) =
      []
  | eqns_of_stmt (class, Code_Thingol.Class (_, (v, (superclasses, classops)))) =
      let
        val names = map snd superclasses @ map fst classops;
        val params = Name.invent_list [] "d" (length names);
        fun mk (k, name) =
          (name, ([(v, [])],
            [([IConst (class, (([], []), [])) `$$ map (IVar o SOME) params],
              IVar (SOME (nth params k)))]));
      in map_index mk names end
  | eqns_of_stmt (_, Code_Thingol.Classrel _) =
      []
  | eqns_of_stmt (_, Code_Thingol.Classparam _) =
      []
  | eqns_of_stmt (inst, Code_Thingol.Classinst ((class, (_, arities)), (superinsts, instops))) =
      [(inst, (arities, [([], IConst (class, (([], []), [])) `$$
        map (fn (_, (_, (inst, dicts))) => IConst (inst, (([], dicts), []))) superinsts
        @ map (IConst o snd o fst) instops)]))];

fun compile_stmts ctxt stmts_deps =
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
      |> compile_eqnss ctxt gr refl_deps
      |> rpair gr;
  in
    fold new_node refl_deps
    #> apfst (fold (fn (name, deps) => fold (curry Graph.add_edge name) deps) names_deps
      #> compile
      #-> fold (fn (name, univ) => (Graph.map_node name o apfst) (K (SOME univ))))
  end;

fun ensure_stmts ctxt naming program =
  let
    fun add_stmts names (gr, (maxidx, idx_tab)) = if exists ((can o Graph.get_node) gr) names
      then (gr, (maxidx, idx_tab))
      else (gr, (maxidx, idx_tab))
        |> compile_stmts ctxt (map (fn name => ((name, Graph.get_node program name),
          Graph.imm_succs program name)) names);
  in
    fold_rev add_stmts (Graph.strong_conn program)
    #> pair naming
  end;


(** evaluation **)

(* term evaluation *)

fun eval_term ctxt gr deps (vs : (string * sort) list, t) =
  let 
    val dict_frees = maps (fn (v, sort) => map_index (curry DFree v o fst) sort) vs;
  in
    ("", (vs, [([], t)]))
    |> singleton (compile_eqnss ctxt gr deps)
    |> snd
    |> (fn t => apps t (rev dict_frees))
  end;

(* reification *)

fun typ_of_itype program vs (ityco `%% itys) =
      let
        val Code_Thingol.Datatype (tyco, _) = Graph.get_node program ityco;
      in Type (tyco, map (typ_of_itype program vs) itys) end
  | typ_of_itype program vs (ITyVar v) =
      let
        val sort = (the o AList.lookup (op =) vs) v;
      in TFree ("'" ^ v, sort) end;

fun term_of_univ thy program idx_tab t =
  let
    fun take_until f [] = []
      | take_until f (x::xs) = if f x then [] else x :: take_until f xs;
    fun is_dict (Const (idx, _)) = (case (Graph.get_node program o the o Inttab.lookup idx_tab) idx
         of Code_Thingol.Class _ => true
          | Code_Thingol.Classrel _ => true
          | Code_Thingol.Classinst _ => true
          | _ => false)
      | is_dict (DFree _) = true
      | is_dict _ = false;
    fun const_of_idx idx = (case (Graph.get_node program o the o Inttab.lookup idx_tab) idx
         of Code_Thingol.Fun (c, _) => c
          | Code_Thingol.Datatypecons (c, _) => c
          | Code_Thingol.Classparam (c, _) => c);
    fun of_apps bounds (t, ts) =
      fold_map (of_univ bounds) ts
      #>> (fn ts' => list_comb (t, rev ts'))
    and of_univ bounds (Const (idx, ts)) typidx =
          let
            val ts' = take_until is_dict ts;
            val c = const_of_idx idx;
            val T = map_type_tvar (fn ((v, i), _) =>
              TypeInfer.param typidx (v ^ string_of_int i, []))
                (Sign.the_const_type thy c);
            val typidx' = typidx + 1;
          in of_apps bounds (Term.Const (c, T), ts') typidx' end
      | of_univ bounds (BVar (n, ts)) typidx =
          of_apps bounds (Bound (bounds - n - 1), ts) typidx
      | of_univ bounds (t as Abs _) typidx =
          typidx
          |> of_univ (bounds + 1) (apps t [BVar (bounds, [])])
          |-> (fn t' => pair (Term.Abs ("u", dummyT, t')))
  in of_univ 0 t 0 |> fst end;

(* function store *)

structure Nbe_Functions = Code_Data
(
  type T = Code_Thingol.naming * ((Univ option * int) Graph.T * (int * string Inttab.table));
  val empty = (Code_Thingol.empty_naming, (Graph.empty, (0, Inttab.empty)));
);

(* compilation, evaluation and reification *)

fun compile_eval thy naming program vs_t deps =
  let
    val ctxt = ProofContext.init thy;
    val (_, (gr, (_, idx_tab))) =
      Nbe_Functions.change thy (ensure_stmts ctxt naming program o snd);
  in
    vs_t
    |> eval_term ctxt gr deps
    |> term_of_univ thy program idx_tab
  end;

(* evaluation with type reconstruction *)

fun normalize thy naming program ((vs0, (vs, ty)), t) deps =
  let
    val ty' = typ_of_itype program vs0 ty;
    fun type_infer t =
      singleton (TypeInfer.infer_types (Syntax.pp_global thy) (Sign.tsig_of thy) I
        (try (Type.strip_sorts o Sign.the_const_type thy)) (K NONE) Name.context 0)
      (TypeInfer.constrain ty' t);
    fun check_tvars t = if null (Term.add_tvars t []) then t else
      error ("Illegal schematic type variables in normalized term: "
        ^ setmp_CRITICAL show_types true (Syntax.string_of_term_global thy) t);
    val string_of_term = setmp_CRITICAL show_types true (Syntax.string_of_term_global thy);
  in
    compile_eval thy naming program (vs, t) deps
    |> traced (fn t => "Normalized:\n" ^ string_of_term t)
    |> type_infer
    |> traced (fn t => "Types inferred:\n" ^ string_of_term t)
    |> check_tvars
    |> traced (fn t => "---\n")
  end;


(* evaluation oracle *)

fun mk_equals thy lhs raw_rhs =
  let
    val ty = Thm.typ_of (Thm.ctyp_of_term lhs);
    val eq = Thm.cterm_of thy (Term.Const ("==", ty --> ty --> propT));
    val rhs = Thm.cterm_of thy raw_rhs;
  in Thm.mk_binop eq lhs rhs end;

val (_, raw_norm_oracle) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (Binding.name "norm", fn (thy, naming, program, vsp_ty_t, deps, ct) =>
    mk_equals thy ct (normalize thy naming program vsp_ty_t deps))));

fun norm_oracle thy naming program vsp_ty_t deps ct =
  raw_norm_oracle (thy, naming, program, vsp_ty_t, deps, ct);

fun no_frees_conv conv ct =
  let
    val frees = Thm.add_cterm_frees ct [];
    fun apply_beta free thm = Thm.combination thm (Thm.reflexive free)
      |> Conv.fconv_rule (Conv.arg_conv (Conv.try_conv (Thm.beta_conversion false)))
      |> Conv.fconv_rule (Conv.arg1_conv (Thm.beta_conversion false));
  in
    ct
    |> fold_rev Thm.cabs frees
    |> conv
    |> fold apply_beta frees
  end;

fun no_frees_rew rew t =
  let
    val frees = map Free (Term.add_frees t []);
  in
    t
    |> fold_rev lambda frees
    |> rew
    |> (fn t' => Term.betapplys (t', frees))
  end;

val norm_conv = no_frees_conv (fn ct =>
  let
    val thy = Thm.theory_of_cterm ct;
  in lift_triv_classes_conv thy (Code_Thingol.eval_conv thy (norm_oracle thy)) ct end);

fun norm thy = lift_triv_classes_rew thy (no_frees_rew (Code_Thingol.eval thy I (normalize thy)));

(* evaluation command *)

fun norm_print_term ctxt modes t =
  let
    val thy = ProofContext.theory_of ctxt;
    val t' = norm thy t;
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

val setup = Value.add_evaluator ("nbe", norm o ProofContext.theory_of);

local structure P = OuterParse and K = OuterKeyword in

val opt_modes = Scan.optional (P.$$$ "(" |-- P.!!! (Scan.repeat1 P.xname --| P.$$$ ")")) [];

val _ =
  OuterSyntax.improper_command "normal_form" "normalize term by evaluation" K.diag
    (opt_modes -- P.term >> (Toplevel.keep o norm_print_term_cmd));

end;

end;
 