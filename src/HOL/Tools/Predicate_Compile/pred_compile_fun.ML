(* Author: Lukas Bulwahn, TU Muenchen

Preprocessing functions to predicates
*)

signature PREDICATE_COMPILE_FUN =
sig
val define_predicates : (string * thm list) list -> theory -> (string * thm list) list * theory
  val rewrite_intro : theory -> thm -> thm list
  val setup_oracle : theory -> theory
  val pred_of_function : theory -> string -> string option
end;

structure Predicate_Compile_Fun : PREDICATE_COMPILE_FUN =
struct


(* Oracle for preprocessing  *)

val (oracle : (string * (cterm -> thm)) option Unsynchronized.ref) = Unsynchronized.ref NONE;

fun the_oracle () =
  case !oracle of
    NONE => error "Oracle is not setup"
  | SOME (_, oracle) => oracle
             
val setup_oracle = Thm.add_oracle (Binding.name "pred_compile_preprocessing", I) #->
  (fn ora => fn thy => let val _ = (oracle := SOME ora) in thy end)
  
  
fun is_funtype (Type ("fun", [_, _])) = true
  | is_funtype _ = false;

fun is_Type (Type _) = true
  | is_Type _ = false

(* returns true if t is an application of an datatype constructor *)
(* which then consequently would be splitted *)
(* else false *)
(*
fun is_constructor thy t =
  if (is_Type (fastype_of t)) then
    (case DatatypePackage.get_datatype thy ((fst o dest_Type o fastype_of) t) of
      NONE => false
    | SOME info => (let
      val constr_consts = maps (fn (_, (_, _, constrs)) => map fst constrs) (#descr info)
      val (c, _) = strip_comb t
      in (case c of
        Const (name, _) => name mem_string constr_consts
        | _ => false) end))
  else false
*)

(* must be exported in code.ML *)
fun is_constr thy = is_some o Code.get_datatype_of_constr thy;

(* Table from constant name (string) to term of inductive predicate *)
structure Pred_Compile_Preproc = TheoryDataFun
(
  type T = string Symtab.table;
  val empty = Symtab.empty;
  val copy = I;
  val extend = I;
  fun merge _ = Symtab.merge (op =);
)

fun defined thy = Symtab.defined (Pred_Compile_Preproc.get thy) 


fun transform_ho_typ (T as Type ("fun", _)) =
  let
    val (Ts, T') = strip_type T
  in if T' = @{typ "bool"} then T else (Ts @ [T']) ---> HOLogic.boolT end
| transform_ho_typ t = t

fun transform_ho_arg arg = 
  case (fastype_of arg) of
    (T as Type ("fun", _)) =>
      (case arg of
        Free (name, _) => Free (name, transform_ho_typ T)
      | _ => error "I am surprised")
| _ => arg

fun pred_type T =
  let
    val (Ts, T') = strip_type T
    val Ts' = map transform_ho_typ Ts
  in
    (Ts' @ [T']) ---> HOLogic.boolT
  end;

(* FIXME: create new predicate name -- does not avoid nameclashing *)
fun pred_of f =
  let
    val (name, T) = dest_Const f
  in
    if (body_type T = @{typ bool}) then
      (Free (Long_Name.base_name name ^ "P", T))
    else
      (Free (Long_Name.base_name name ^ "P", pred_type T))
  end

fun mk_param lookup_pred (t as Free (v, _)) = lookup_pred t
  | mk_param lookup_pred t =
  let
    val (vs, body) = strip_abs t
    val names = Term.add_free_names body []
    val vs_names = Name.variant_list names (map fst vs)
    val vs' = map2 (curry Free) vs_names (map snd vs)
    val body' = subst_bounds (rev vs', body)
    val (f, args) = strip_comb body'
    val resname = Name.variant (vs_names @ names) "res"
    val resvar = Free (resname, body_type (fastype_of body'))
    val P = lookup_pred f
    val pred_body = list_comb (P, args @ [resvar])
    val param = fold_rev lambda (vs' @ [resvar]) pred_body
  in param end;


(* creates the list of premises for every intro rule *)
(* theory -> term -> (string list, term list list) *)

fun dest_code_eqn eqn = let
  val (lhs, rhs) = Logic.dest_equals (Logic.unvarify (Thm.prop_of eqn))
  val (func, args) = strip_comb lhs
in ((func, args), rhs) end;

fun string_of_typ T = Syntax.string_of_typ_global @{theory} T

fun string_of_term t =
  case t of
    Const (c, T) => "Const (" ^ c ^ ", " ^ string_of_typ T ^ ")"
  | Free (c, T) => "Free (" ^ c ^ ", " ^ string_of_typ T ^ ")"
  | Var ((c, i), T) => "Var ((" ^ c ^ ", " ^ string_of_int i ^ "), " ^ string_of_typ T ^ ")"
  | Bound i => "Bound " ^ string_of_int i
  | Abs (x, T, t) => "Abs (" ^ x ^ ", " ^ string_of_typ T ^ ", " ^ string_of_term t ^ ")"
  | t1 $ t2 => "(" ^ string_of_term t1 ^ ") $ (" ^ string_of_term t2 ^ ")"
  
fun ind_package_get_nparams thy name =
  case try (Inductive.the_inductive (ProofContext.init thy)) name of
    SOME (_, result) => length (Inductive.params_of (#raw_induct result))
  | NONE => error ("No such predicate: " ^ quote name) 

(* TODO: does not work with higher order functions yet *)
fun mk_rewr_eq (func, pred) =
  let
    val (argTs, resT) = (strip_type (fastype_of func))
    val nctxt =
      Name.make_context (Term.fold_aterms (fn Free (x, _) => insert (op =) x | _ => I) (func $ pred) [])
    val (argnames, nctxt') = Name.variants (replicate (length argTs) "a") nctxt
    val ([resname], nctxt'') = Name.variants ["r"] nctxt'
    val args = map Free (argnames ~~ argTs)
    val res = Free (resname, resT)
  in Logic.mk_equals
      (HOLogic.mk_eq (res, list_comb (func, args)), list_comb (pred, args @ [res]))
  end;

fun has_split_rule_cname @{const_name "nat_case"} = true
  | has_split_rule_cname @{const_name "list_case"} = true
  | has_split_rule_cname _ = false
  
fun has_split_rule_term thy (Const (@{const_name "nat_case"}, _)) = true 
  | has_split_rule_term thy (Const (@{const_name "list_case"}, _)) = true 
  | has_split_rule_term thy _ = false

fun has_split_rule_term' thy (Const (@{const_name "If"}, _)) = true
  | has_split_rule_term' thy (Const (@{const_name "Let"}, _)) = true
  | has_split_rule_term' thy c = has_split_rule_term thy c
  
fun prepare_split_thm ctxt split_thm =
    (split_thm RS @{thm iffD2})
    |> LocalDefs.unfold ctxt [@{thm atomize_conjL[symmetric]},
      @{thm atomize_all[symmetric]}, @{thm atomize_imp[symmetric]}]

fun find_split_thm thy (Const (name, typ)) =
  let
    fun split_name str =
      case first_field "." str
        of (SOME (field, rest)) => field :: split_name rest
         | NONE => [str]
    val splitted_name = split_name name
  in
    if length splitted_name > 0 andalso
       String.isSuffix "_case" (List.last splitted_name)
    then
      (List.take (splitted_name, length splitted_name - 1)) @ ["split"]
      |> space_implode "."
      |> PureThy.get_thm thy
      |> SOME
      handle ERROR msg => NONE
    else NONE
  end
  | find_split_thm _ _ = NONE

fun find_split_thm' thy (Const (@{const_name "If"}, _)) = SOME @{thm split_if}
  | find_split_thm' thy (Const (@{const_name "Let"}, _)) = SOME @{thm refl} (* TODO *)
  | find_split_thm' thy c = find_split_thm thy c

fun strip_all t = (Term.strip_all_vars t, Term.strip_all_body t)

fun folds_map f xs y =
  let
    fun folds_map' acc [] y = [(rev acc, y)]
      | folds_map' acc (x :: xs) y =
        maps (fn (x, y) => folds_map' (x :: acc) xs y) (f x y)
    in
      folds_map' [] xs y
    end;

fun mk_prems thy (lookup_pred, get_nparams) t (names, prems) =
  let
    fun mk_prems' (t as Const (name, T)) (names, prems) =
      if is_constr thy name orelse (is_none (try lookup_pred t)) then
        [(t, (names, prems))]
      else [(lookup_pred t, (names, prems))]
    | mk_prems' (t as Free (f, T)) (names, prems) = 
      [(lookup_pred t, (names, prems))]
    | mk_prems' (t as Abs _) (names, prems) =
      if Predicate_Compile_Aux.is_predT (fastype_of t) then
      [(t, (names, prems))] else error "mk_prems': Abs "
      (* mk_param *)
    | mk_prems' t (names, prems) =
      if Predicate_Compile_Aux.is_constrt thy t then
        [(t, (names, prems))]
      else
        if has_split_rule_term' thy (fst (strip_comb t)) then
          let
            val (f, args) = strip_comb t
            val split_thm = prepare_split_thm (ProofContext.init thy) (the (find_split_thm' thy f))
            (* TODO: contextify things - this line is to unvarify the split_thm *)
            (*val ((_, [isplit_thm]), _) = Variable.import true [split_thm] (ProofContext.init thy)*)
            val (assms, concl) = Logic.strip_horn (Thm.prop_of split_thm)
            val (P, [split_t]) = strip_comb (HOLogic.dest_Trueprop concl) 
            val subst = Pattern.match thy (split_t, t) (Vartab.empty, Vartab.empty)
            val (_, split_args) = strip_comb split_t
            val match = split_args ~~ args
            fun mk_prems_of_assm assm =
              let
                val (vTs, assm') = strip_all (Envir.beta_norm (Envir.subst_term subst assm))
                val var_names = Name.variant_list names (map fst vTs)
                val vars = map Free (var_names ~~ (map snd vTs))
                val (prems', pre_res) = Logic.strip_horn (subst_bounds (rev vars, assm'))
                val (_, [inner_t]) = strip_comb (HOLogic.dest_Trueprop pre_res)
              in
                mk_prems' inner_t (var_names @ names, prems' @ prems)
              end
          in
            maps mk_prems_of_assm assms
          end
        else
          let
            val (f, args) = strip_comb t
            (* TODO: special procedure for higher-order functions: split arguments in
              simple types and function types *)
            val resname = Name.variant names "res"
            val resvar = Free (resname, body_type (fastype_of t))
            val names' = resname :: names
            fun mk_prems'' (t as Const (c, _)) =
              if is_constr thy c orelse (is_none (try lookup_pred t)) then
                folds_map mk_prems' args (names', prems) |>
                map
                  (fn (argvs, (names'', prems')) =>
                  let
                    val prem = HOLogic.mk_Trueprop (HOLogic.mk_eq (resvar, list_comb (f, argvs)))
                  in (names'', prem :: prems') end)
              else
                let
                  val pred = lookup_pred t
                  val nparams = get_nparams pred
                  val (params, args) = chop nparams args
                  val params' = map (mk_param thy lookup_pred) params
                in
                  folds_map mk_prems' args (names', prems)
                  |> map (fn (argvs, (names'', prems')) =>
                    let
                      val prem = HOLogic.mk_Trueprop (list_comb (pred, params' @ argvs @ [resvar]))
                    in (names'', prem :: prems') end)
                end
            | mk_prems'' (t as Free (_, _)) =
                let
                  (* higher order argument call *)
                  val pred = lookup_pred t
                in
                  folds_map mk_prems' args (resname :: names, prems)
                  |> map (fn (argvs, (names', prems')) =>
                     let
                       val prem = HOLogic.mk_Trueprop (list_comb (pred, argvs @ [resvar]))
                     in (names', prem :: prems') end)
                end
            | mk_prems'' t =
              error ("Invalid term: " ^ Syntax.string_of_term_global thy t)
          in
            map (pair resvar) (mk_prems'' f)
          end
  in
    mk_prems' t (names, prems)
  end;

(* assumption: mutual recursive predicates all have the same parameters. *)  
fun define_predicates specs thy =
  if forall (fn (const, _) => member (op =) (Symtab.keys (Pred_Compile_Preproc.get thy)) const) specs then
    ([], thy)
  else
  let
    val consts = map fst specs
    val eqns = maps snd specs
    (*val eqns = maps (Predicate_Compile_Preproc_Data.get_specification thy) consts*)
      (* create prednames *)
    val ((funs, argss), rhss) = map_split dest_code_eqn eqns |>> split_list
    val argss' = map (map transform_ho_arg) argss
    val pnames = map dest_Free (distinct (op =) (maps (filter (is_funtype o fastype_of)) argss'))
    val preds = map pred_of funs
    val prednames = map (fst o dest_Free) preds
    val funnames = map (fst o dest_Const) funs
    val fun_pred_names = (funnames ~~ prednames)  
      (* mapping from term (Free or Const) to term *)
    fun lookup_pred (Const (name, T)) =
      (case (Symtab.lookup (Pred_Compile_Preproc.get thy) name) of
          SOME c => Const (c, pred_type T)
        | NONE =>
          (case AList.lookup op = fun_pred_names name of
            SOME f => Free (f, pred_type T)
          | NONE => Const (name, T)))
      | lookup_pred (Free (name, T)) =
        if member op = (map fst pnames) name then
          Free (name, transform_ho_typ T)
        else
          Free (name, T)
      | lookup_pred t =
         error ("lookup function is not defined for " ^ Syntax.string_of_term_global thy t)
     
        (* mapping from term (predicate term, not function term!) to int *)
    fun get_nparams (Const (name, _)) =
      the_default 0 (try (ind_package_get_nparams thy) name)
    | get_nparams (Free (name, _)) =
        (if member op = prednames name then
          length pnames
        else 0)
    | get_nparams t = error ("No parameters for " ^ (Syntax.string_of_term_global thy t))
  
    (* create intro rules *)
  
    fun mk_intros ((func, pred), (args, rhs)) =
      if (body_type (fastype_of func) = @{typ bool}) then
       (*TODO: preprocess predicate definition of rhs *)
        [Logic.list_implies ([HOLogic.mk_Trueprop rhs], HOLogic.mk_Trueprop (list_comb (pred, args)))]
      else
        let
          val names = Term.add_free_names rhs []
        in mk_prems thy (lookup_pred, get_nparams) rhs (names, [])
          |> map (fn (resultt, (names', prems)) =>
            Logic.list_implies (prems, HOLogic.mk_Trueprop (list_comb (pred, args @ [resultt]))))
        end
    fun mk_rewr_thm (func, pred) = @{thm refl}
  in
    case try (maps mk_intros) ((funs ~~ preds) ~~ (argss' ~~ rhss)) of
      NONE => ([], thy) 
    | SOME intr_ts =>
        if is_some (try (map (cterm_of thy)) intr_ts) then
          let
            val (ind_result, thy') =
              Inductive.add_inductive_global (serial_string ())
                {quiet_mode = false, verbose = false, kind = Thm.internalK,
                  alt_name = Binding.empty, coind = false, no_elim = false,
                  no_ind = false, skip_mono = false, fork_mono = false}
                (map (fn (s, T) => ((Binding.name s, T), NoSyn)) (distinct (op =) (map dest_Free preds)))
                pnames
                (map (fn x => (Attrib.empty_binding, x)) intr_ts)
                [] thy
            val prednames = map (fst o dest_Const) (#preds ind_result)
            (* val rewr_thms = map mk_rewr_eq ((distinct (op =) funs) ~~ (#preds ind_result)) *)
            (* add constants to my table *)
            val specs = map (fn predname => (predname, filter (Predicate_Compile_Aux.is_intro predname) (#intrs ind_result))) prednames
            val thy'' = Pred_Compile_Preproc.map (fold Symtab.update_new (consts ~~ prednames)) thy'
          in
            (specs, thy'')
          end
        else
          let
            val _ = tracing "Introduction rules of function_predicate are not welltyped"
          in ([], thy) end
  end

(* preprocessing intro rules - uses oracle *)

(* theory -> thm -> thm *)
fun rewrite_intro thy intro =
  let
    fun lookup_pred (Const (name, T)) =
      (case (Symtab.lookup (Pred_Compile_Preproc.get thy) name) of
        SOME c => Const (c, pred_type T)
      | NONE => error ("Function " ^ name ^ " is not inductified"))
    | lookup_pred (Free (name, T)) = Free (name, T)
    | lookup_pred _ = error "lookup function is not defined!"

    fun get_nparams (Const (name, _)) =
      the_default 0 (try (ind_package_get_nparams thy) name)
    | get_nparams (Free _) = 0
    | get_nparams t = error ("No parameters for " ^ (Syntax.string_of_term_global thy t))
    
    val intro_t = (Logic.unvarify o prop_of) intro
    val (prems, concl) = Logic.strip_horn intro_t
    val frees = map fst (Term.add_frees intro_t [])
    fun rewrite prem names =
      let
        val t = (HOLogic.dest_Trueprop prem)
        val (lit, mk_lit) = case try HOLogic.dest_not t of
            SOME t => (t, HOLogic.mk_not)
          | NONE => (t, I)
        val (P, args) = (strip_comb lit) 
      in
        folds_map (
          fn t => if (is_funtype (fastype_of t)) then (fn x => [(t, x)])
            else mk_prems thy (lookup_pred, get_nparams) t) args (names, [])
        |> map (fn (resargs, (names', prems')) =>
          let
            val prem' = HOLogic.mk_Trueprop (mk_lit (list_comb (P, resargs)))
          in (prem'::prems', names') end)
      end
    val intro_ts' = folds_map rewrite prems frees
      |> maps (fn (prems', frees') =>
        rewrite concl frees'
        |> map (fn (concl'::conclprems, _) =>
          Logic.list_implies ((flat prems') @ conclprems, concl')))
  in
    map (Drule.standard o the_oracle () o cterm_of thy) intro_ts'
  end; 

end;
