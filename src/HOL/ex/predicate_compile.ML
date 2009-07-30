(* Author: Lukas Bulwahn, TU Muenchen

(Prototype of) A compiler from predicates specified by intro/elim rules
to equations.
*)

signature PREDICATE_COMPILE =
sig
  type mode = int list option list * int list
  val add_equations_of: string list -> theory -> theory
  val register_predicate : (thm list * thm * int) -> theory -> theory
  val is_registered : theory -> string -> bool
  val fetch_pred_data : theory -> string -> (thm list * thm * int)  
  val predfun_intro_of: theory -> string -> mode -> thm
  val predfun_elim_of: theory -> string -> mode -> thm
  val strip_intro_concl: int -> term -> term * (term list * term list)
  val predfun_name_of: theory -> string -> mode -> string
  val all_preds_of : theory -> string list
  val modes_of: theory -> string -> mode list
  val intros_of: theory -> string -> thm list
  val nparams_of: theory -> string -> int
  val add_intro: thm -> theory -> theory
  val set_elim: thm -> theory -> theory
  val setup: theory -> theory
  val code_pred: string -> Proof.context -> Proof.state
  val code_pred_cmd: string -> Proof.context -> Proof.state
  val print_stored_rules: theory -> unit
  val do_proofs: bool ref
  val mk_casesrule : Proof.context -> int -> thm list -> term
  val analyze_compr: theory -> term -> term
  val eval_ref: (unit -> term Predicate.pred) option ref
  val add_equations : string -> theory -> theory
  val code_pred_intros_attrib : attribute
end;

structure Predicate_Compile : PREDICATE_COMPILE =
struct

(** auxiliary **)

(* debug stuff *)

fun tracing s = (if ! Toplevel.debug then Output.tracing s else ());

fun print_tac s = (if ! Toplevel.debug then Tactical.print_tac s else Seq.single);
fun new_print_tac s = Tactical.print_tac s
fun debug_tac msg = (fn st => (Output.tracing msg; Seq.single st));

val do_proofs = ref true;

fun mycheat_tac thy i st =
  (Tactic.rtac (SkipProof.make_thm thy (Var (("A", 0), propT))) i) st

fun remove_last_goal thy st =
  (Tactic.rtac (SkipProof.make_thm thy (Var (("A", 0), propT))) (nprems_of st)) st

(* reference to preprocessing of InductiveSet package *)

val ind_set_codegen_preproc = Inductive_Set.codegen_preproc;

(** fundamentals **)

(* syntactic operations *)

fun mk_eq (x, xs) =
  let fun mk_eqs _ [] = []
        | mk_eqs a (b::cs) =
            HOLogic.mk_eq (Free (a, fastype_of b), b) :: mk_eqs a cs
  in mk_eqs x xs end;

fun mk_tupleT [] = HOLogic.unitT
  | mk_tupleT Ts = foldr1 HOLogic.mk_prodT Ts;

fun dest_tupleT (Type (@{type_name Product_Type.unit}, [])) = []
  | dest_tupleT (Type (@{type_name "*"}, [T1, T2])) = T1 :: (dest_tupleT T2)
  | dest_tupleT t = [t]

fun mk_tuple [] = HOLogic.unit
  | mk_tuple ts = foldr1 HOLogic.mk_prod ts;

fun dest_tuple (Const (@{const_name Product_Type.Unity}, _)) = []
  | dest_tuple (Const (@{const_name Pair}, _) $ t1 $ t2) = t1 :: (dest_tuple t2)
  | dest_tuple t = [t]

fun mk_pred_enumT T = Type (@{type_name Predicate.pred}, [T])

fun dest_pred_enumT (Type (@{type_name Predicate.pred}, [T])) = T
  | dest_pred_enumT T = raise TYPE ("dest_pred_enumT", [T], []);

fun mk_Enum f =
  let val T as Type ("fun", [T', _]) = fastype_of f
  in
    Const (@{const_name Predicate.Pred}, T --> mk_pred_enumT T') $ f    
  end;

fun mk_Eval (f, x) =
  let val T = fastype_of x
  in
    Const (@{const_name Predicate.eval}, mk_pred_enumT T --> T --> HOLogic.boolT) $ f $ x
  end;

fun mk_empty T = Const (@{const_name Orderings.bot}, mk_pred_enumT T);

fun mk_single t =
  let val T = fastype_of t
  in Const(@{const_name Predicate.single}, T --> mk_pred_enumT T) $ t end;

fun mk_bind (x, f) =
  let val T as Type ("fun", [_, U]) = fastype_of f
  in
    Const (@{const_name Predicate.bind}, fastype_of x --> T --> U) $ x $ f
  end;

val mk_sup = HOLogic.mk_binop @{const_name sup};

fun mk_if_predenum cond = Const (@{const_name Predicate.if_pred},
  HOLogic.boolT --> mk_pred_enumT HOLogic.unitT) $ cond;

fun mk_not_pred t = let val T = mk_pred_enumT HOLogic.unitT
  in Const (@{const_name Predicate.not_pred}, T --> T) $ t end

fun mk_pred_map T1 T2 tf tp = Const (@{const_name Predicate.map},
  (T1 --> T2) --> mk_pred_enumT T1 --> mk_pred_enumT T2) $ tf $ tp;


(* destruction of intro rules *)

(* FIXME: look for other place where this functionality was used before *)
fun strip_intro_concl nparams intro = let
  val _ $ u = Logic.strip_imp_concl intro
  val (pred, all_args) = strip_comb u
  val (params, args) = chop nparams all_args
in (pred, (params, args)) end

(* data structures *)

type mode = int list option list * int list; (*pmode FIMXE*)

fun string_of_mode (iss, is) = space_implode " -> " (map
  (fn NONE => "X"
    | SOME js => enclose "[" "]" (commas (map string_of_int js)))
       (iss @ [SOME is]));

fun print_modes modes = Output.tracing ("Inferred modes:\n" ^
  cat_lines (map (fn (s, ms) => s ^ ": " ^ commas (map
    string_of_mode ms)) modes));

    
datatype predfun_data = PredfunData of {
  name : string,
  definition : thm,
  intro : thm,
  elim : thm
};

fun rep_predfun_data (PredfunData data) = data;
fun mk_predfun_data (name, definition, intro, elim) =
  PredfunData {name = name, definition = definition, intro = intro, elim = elim}

datatype pred_data = PredData of {
  intros : thm list,
  elim : thm option,
  nparams : int,
  functions : (mode * predfun_data) list
};

fun rep_pred_data (PredData data) = data;
fun mk_pred_data ((intros, elim, nparams), functions) =
  PredData {intros = intros, elim = elim, nparams = nparams, functions = functions}
fun map_pred_data f (PredData {intros, elim, nparams, functions}) =
  mk_pred_data (f ((intros, elim, nparams), functions))
  
fun eq_option eq (NONE, NONE) = true
  | eq_option eq (SOME x, SOME y) = eq (x, y)
  | eq_option eq _ = false
  
fun eq_pred_data (PredData d1, PredData d2) = 
  eq_list (Thm.eq_thm) (#intros d1, #intros d2) andalso
  eq_option (Thm.eq_thm) (#elim d1, #elim d2) andalso
  #nparams d1 = #nparams d2
  
structure PredData = TheoryDataFun
(
  type T = pred_data Graph.T;
  val empty = Graph.empty;
  val copy = I;
  val extend = I;
  fun merge _ = Graph.merge eq_pred_data;
);

(* queries *)

fun lookup_pred_data thy name =
  Option.map rep_pred_data (try (Graph.get_node (PredData.get thy)) name)

fun the_pred_data thy name = case lookup_pred_data thy name
 of NONE => error ("No such predicate " ^ quote name)  
  | SOME data => data;

val is_registered = is_some oo lookup_pred_data 

val all_preds_of = Graph.keys o PredData.get

val intros_of = #intros oo the_pred_data

fun the_elim_of thy name = case #elim (the_pred_data thy name)
 of NONE => error ("No elimination rule for predicate " ^ quote name)
  | SOME thm => thm 
  
val has_elim = is_some o #elim oo the_pred_data;

val nparams_of = #nparams oo the_pred_data

val modes_of = (map fst) o #functions oo the_pred_data

fun all_modes_of thy = map (fn name => (name, modes_of thy name)) (all_preds_of thy) 

val is_compiled = not o null o #functions oo the_pred_data

fun lookup_predfun_data thy name mode =
  Option.map rep_predfun_data (AList.lookup (op =)
  (#functions (the_pred_data thy name)) mode)

fun the_predfun_data thy name mode = case lookup_predfun_data thy name mode
 of NONE => error ("No such mode" ^ string_of_mode mode)
  | SOME data => data;

val predfun_name_of = #name ooo the_predfun_data

val predfun_definition_of = #definition ooo the_predfun_data

val predfun_intro_of = #intro ooo the_predfun_data

val predfun_elim_of = #elim ooo the_predfun_data

fun print_stored_rules thy =
  let
    val preds = (Graph.keys o PredData.get) thy
    fun print pred () = let
      val _ = writeln ("predicate: " ^ pred)
      val _ = writeln ("number of parameters: " ^ string_of_int (nparams_of thy pred))
      val _ = writeln ("introrules: ")
      val _ = fold (fn thm => fn u => writeln (Display.string_of_thm_global thy thm))
        (rev (intros_of thy pred)) ()
    in
      if (has_elim thy pred) then
        writeln ("elimrule: " ^ Display.string_of_thm_global thy (the_elim_of thy pred))
      else
        writeln ("no elimrule defined")
    end
  in
    fold print preds ()
  end;

(** preprocessing rules **)  

fun imp_prems_conv cv ct =
  case Thm.term_of ct of
    Const ("==>", _) $ _ $ _ => Conv.combination_conv (Conv.arg_conv cv) (imp_prems_conv cv) ct
  | _ => Conv.all_conv ct

fun Trueprop_conv cv ct =
  case Thm.term_of ct of
    Const ("Trueprop", _) $ _ => Conv.arg_conv cv ct  
  | _ => error "Trueprop_conv"

fun preprocess_intro thy rule =
  Conv.fconv_rule
    (imp_prems_conv
      (Trueprop_conv (Conv.try_conv (Conv.rewr_conv (Thm.symmetric @{thm Predicate.eq_is_eq})))))
    (Thm.transfer thy rule)

fun preprocess_elim thy nargs elimrule = let
   fun replace_eqs (Const ("Trueprop", _) $ (Const ("op =", T) $ lhs $ rhs)) =
      HOLogic.mk_Trueprop (Const (@{const_name Predicate.eq}, T) $ lhs $ rhs)
    | replace_eqs t = t
   fun preprocess_case t = let
     val params = Logic.strip_params t
     val (assums1, assums2) = chop nargs (Logic.strip_assums_hyp t)
     val assums_hyp' = assums1 @ (map replace_eqs assums2)
     in list_all (params, Logic.list_implies (assums_hyp', Logic.strip_assums_concl t)) end
   val prems = Thm.prems_of elimrule
   val cases' = map preprocess_case (tl prems)
   val elimrule' = Logic.list_implies ((hd prems) :: cases', Thm.concl_of elimrule)
 in
   Thm.equal_elim
     (Thm.symmetric (Conv.implies_concl_conv (MetaSimplifier.rewrite true [@{thm eq_is_eq}])
        (cterm_of thy elimrule')))
     elimrule
 end;

fun fetch_pred_data thy name =
  case try (Inductive.the_inductive (ProofContext.init thy)) name of
    SOME (info as (_, result)) => 
      let
        fun is_intro_of intro =
          let
            val (const, _) = strip_comb (HOLogic.dest_Trueprop (concl_of intro))
          in (fst (dest_Const const) = name) end;
        val intros = map (preprocess_intro thy) (filter is_intro_of (#intrs result)) 
        val elim = nth (#elims result) (find_index (fn s => s = name) (#names (fst info)))
        val nparams = length (Inductive.params_of (#raw_induct result))
      in (intros, elim, nparams) end
  | NONE => error ("No such predicate: " ^ quote name)
  
(* updaters *)

fun add_predfun name mode data = let
    val add = apsnd (cons (mode, mk_predfun_data data))
  in PredData.map (Graph.map_node name (map_pred_data add)) end

fun is_inductive_predicate thy name =
  is_some (try (Inductive.the_inductive (ProofContext.init thy)) name)

fun depending_preds_of thy intros = fold Term.add_consts (map Thm.prop_of intros) [] |> map fst
    |> filter (fn c => is_inductive_predicate thy c orelse is_registered thy c)

(* code dependency graph *)    
fun dependencies_of thy name =
  let
    val (intros, elim, nparams) = fetch_pred_data thy name 
    val data = mk_pred_data ((intros, SOME elim, nparams), [])
    val keys = depending_preds_of thy intros
  in
    (data, keys)
  end;

(* TODO: add_edges - by analysing dependencies *)
fun add_intro thm thy = let
   val (name, _) = dest_Const (fst (strip_intro_concl 0 (prop_of thm)))
   fun cons_intro gr =
     case try (Graph.get_node gr) name of
       SOME pred_data => Graph.map_node name (map_pred_data
         (apfst (fn (intro, elim, nparams) => (thm::intro, elim, nparams)))) gr
     | NONE =>
       let
         val nparams = the_default 0 (try (#3 o fetch_pred_data thy) name)
       in Graph.new_node (name, mk_pred_data (([thm], NONE, nparams), [])) gr end;
  in PredData.map cons_intro thy end

fun set_elim thm = let
    val (name, _) = dest_Const (fst 
      (strip_comb (HOLogic.dest_Trueprop (hd (prems_of thm)))))
    fun set (intros, _, nparams) = (intros, SOME thm, nparams)  
  in PredData.map (Graph.map_node name (map_pred_data (apfst set))) end

fun set_nparams name nparams = let
    fun set (intros, elim, _ ) = (intros, elim, nparams) 
  in PredData.map (Graph.map_node name (map_pred_data (apfst set))) end

fun register_predicate (intros, elim, nparams) thy = let
    val (name, _) = dest_Const (fst (strip_intro_concl nparams (prop_of (hd intros))))
    fun set _ = (intros, SOME elim, nparams)
  in
    PredData.map (Graph.new_node (name, mk_pred_data ((intros, SOME elim, nparams), []))
      #> fold Graph.add_edge (map (pair name) (depending_preds_of thy intros))) thy
  end

  
(* Mode analysis *)

(*** check if a term contains only constructor functions ***)
fun is_constrt thy =
  let
    val cnstrs = flat (maps
      (map (fn (_, (Tname, _, cs)) => map (apsnd (rpair Tname o length)) cs) o #descr o snd)
      (Symtab.dest (Datatype.get_all thy)));
    fun check t = (case strip_comb t of
        (Free _, []) => true
      | (Const (s, T), ts) => (case (AList.lookup (op =) cnstrs s, body_type T) of
            (SOME (i, Tname), Type (Tname', _)) => length ts = i andalso Tname = Tname' andalso forall check ts
          | _ => false)
      | _ => false)
  in check end;

(*** check if a type is an equality type (i.e. doesn't contain fun)
  FIXME this is only an approximation ***)
fun is_eqT (Type (s, Ts)) = s <> "fun" andalso forall is_eqT Ts
  | is_eqT _ = true;

fun term_vs tm = fold_aterms (fn Free (x, T) => cons x | _ => I) tm [];
val terms_vs = distinct (op =) o maps term_vs;

(** collect all Frees in a term (with duplicates!) **)
fun term_vTs tm =
  fold_aterms (fn Free xT => cons xT | _ => I) tm [];

fun get_args is ts = let
  fun get_args' _ _ [] = ([], [])
    | get_args' is i (t::ts) = (if member (op =) is i then apfst else apsnd) (cons t)
        (get_args' is (i+1) ts)
in get_args' is 1 ts end

(*FIXME this function should not be named merge... make it local instead*)
fun merge xs [] = xs
  | merge [] ys = ys
  | merge (x::xs) (y::ys) = if length x >= length y then x::merge xs (y::ys)
      else y::merge (x::xs) ys;

fun subsets i j = if i <= j then
       let val is = subsets (i+1) j
       in merge (map (fn ks => i::ks) is) is end
     else [[]];
     
(* FIXME: should be in library - map_prod *)
fun cprod ([], ys) = []
  | cprod (x :: xs, ys) = map (pair x) ys @ cprod (xs, ys);

fun cprods xss = foldr (map op :: o cprod) [[]] xss;

datatype hmode = Mode of mode * int list * hmode option list; (*FIXME don't understand
  why there is another mode type tmode !?*)

  
(*TODO: cleanup function and put together with modes_of_term *)
fun modes_of_param default modes t = let
    val (vs, t') = strip_abs t
    val b = length vs
    fun mk_modes name args = Option.map (maps (fn (m as (iss, is)) =>
        let
          val (args1, args2) =
            if length args < length iss then
              error ("Too few arguments for inductive predicate " ^ name)
            else chop (length iss) args;
          val k = length args2;
          val perm = map (fn i => (find_index (fn t => t = Bound (b - i)) args2) + 1)
            (1 upto b)
          val partial_mode = (1 upto k) \\ perm
        in
          if not (partial_mode subset is) then [] else
          let
            val is' = 
            (fold_index (fn (i, j) => if j mem is then cons (i + 1) else I) perm [])
            |> fold (fn i => if i > k then cons (i - k + b) else I) is
              
           val res = map (fn x => Mode (m, is', x)) (cprods (map
            (fn (NONE, _) => [NONE]
              | (SOME js, arg) => map SOME (filter
                  (fn Mode (_, js', _) => js=js') (modes_of_term modes arg)))
                    (iss ~~ args1)))
          in res end
        end)) (AList.lookup op = modes name)
  in case strip_comb t' of
    (Const (name, _), args) => the_default default (mk_modes name args)
    | (Var ((name, _), _), args) => the (mk_modes name args)
    | (Free (name, _), args) => the (mk_modes name args)
    | _ => default end
  
and modes_of_term modes t =
  let
    val ks = 1 upto length (binder_types (fastype_of t));
    val default = [Mode (([], ks), ks, [])];
    fun mk_modes name args = Option.map (maps (fn (m as (iss, is)) =>
        let
          val (args1, args2) =
            if length args < length iss then
              error ("Too few arguments for inductive predicate " ^ name)
            else chop (length iss) args;
          val k = length args2;
          val prfx = 1 upto k
        in
          if not (is_prefix op = prfx is) then [] else
          let val is' = map (fn i => i - k) (List.drop (is, k))
          in map (fn x => Mode (m, is', x)) (cprods (map
            (fn (NONE, _) => [NONE]
              | (SOME js, arg) => map SOME (filter
                  (fn Mode (_, js', _) => js=js') (modes_of_term modes arg)))
                    (iss ~~ args1)))
          end
        end)) (AList.lookup op = modes name)

  in (case strip_comb t of
      (Const (name, _), args) => the_default default (mk_modes name args)
    | (Var ((name, _), _), args) => the (mk_modes name args)
    | (Free (name, _), args) => the (mk_modes name args)
    | (Abs _, []) => modes_of_param default modes t 
    | _ => default)
  end

datatype indprem = Prem of term list * term | Negprem of term list * term | Sidecond of term;

fun select_mode_prem thy modes vs ps =
  find_first (is_some o snd) (ps ~~ map
    (fn Prem (us, t) => find_first (fn Mode (_, is, _) =>
          let
            val (in_ts, out_ts) = get_args is us;
            val (out_ts', in_ts') = List.partition (is_constrt thy) out_ts;
            val vTs = maps term_vTs out_ts';
            val dupTs = map snd (duplicates (op =) vTs) @
              List.mapPartial (AList.lookup (op =) vTs) vs;
          in
            terms_vs (in_ts @ in_ts') subset vs andalso
            forall (is_eqT o fastype_of) in_ts' andalso
            term_vs t subset vs andalso
            forall is_eqT dupTs
          end)
            (modes_of_term modes t handle Option =>
               error ("Bad predicate: " ^ Syntax.string_of_term_global thy t))
      | Negprem (us, t) => find_first (fn Mode (_, is, _) =>
            length us = length is andalso
            terms_vs us subset vs andalso
            term_vs t subset vs)
            (modes_of_term modes t handle Option =>
               error ("Bad predicate: " ^ Syntax.string_of_term_global thy t))
      | Sidecond t => if term_vs t subset vs then SOME (Mode (([], []), [], []))
          else NONE
      ) ps);

fun check_mode_clause thy param_vs modes (iss, is) (ts, ps) =
  let
    val modes' = modes @ List.mapPartial
      (fn (_, NONE) => NONE | (v, SOME js) => SOME (v, [([], js)]))
        (param_vs ~~ iss); 
    fun check_mode_prems vs [] = SOME vs
      | check_mode_prems vs ps = (case select_mode_prem thy modes' vs ps of
          NONE => NONE
        | SOME (x, _) => check_mode_prems
            (case x of Prem (us, _) => vs union terms_vs us | _ => vs)
            (filter_out (equal x) ps))
    val (in_ts, in_ts') = List.partition (is_constrt thy) (fst (get_args is ts));
    val in_vs = terms_vs in_ts;
    val concl_vs = terms_vs ts
  in
    forall is_eqT (map snd (duplicates (op =) (maps term_vTs in_ts))) andalso
    forall (is_eqT o fastype_of) in_ts' andalso
    (case check_mode_prems (param_vs union in_vs) ps of
       NONE => false
     | SOME vs => concl_vs subset vs)
  end;

fun check_modes_pred thy param_vs preds modes (p, ms) =
  let val SOME rs = AList.lookup (op =) preds p
  in (p, List.filter (fn m => case find_index
    (not o check_mode_clause thy param_vs modes m) rs of
      ~1 => true
    | i => (tracing ("Clause " ^ string_of_int (i+1) ^ " of " ^
      p ^ " violates mode " ^ string_of_mode m); false)) ms)
  end;

fun fixp f (x : (string * mode list) list) =
  let val y = f x
  in if x = y then x else fixp f y end;

fun infer_modes thy extra_modes arities param_vs preds = fixp (fn modes =>
  map (check_modes_pred thy param_vs preds (modes @ extra_modes)) modes)
    (map (fn (s, (ks, k)) => (s, cprod (cprods (map
      (fn NONE => [NONE]
        | SOME k' => map SOME (subsets 1 k')) ks),
      subsets 1 k))) arities);


(* term construction *)

(* for simple modes (e.g. parameters) only: better call it param_funT *)
(* or even better: remove it and only use funT'_of - some modifications to funT'_of necessary *) 
fun funT_of T NONE = T
  | funT_of T (SOME mode) = let
     val Ts = binder_types T;
     val (Us1, Us2) = get_args mode Ts
   in Us1 ---> (mk_pred_enumT (mk_tupleT Us2)) end;

fun funT'_of (iss, is) T = let
    val Ts = binder_types T
    val (paramTs, argTs) = chop (length iss) Ts
    val paramTs' = map2 (fn SOME is => funT'_of ([], is) | NONE => I) iss paramTs 
    val (inargTs, outargTs) = get_args is argTs
  in
    (paramTs' @ inargTs) ---> (mk_pred_enumT (mk_tupleT outargTs))
  end; 


fun mk_v (names, vs) s T = (case AList.lookup (op =) vs s of
      NONE => (Free (s, T), (names, (s, [])::vs))
    | SOME xs =>
        let
          val s' = Name.variant names s;
          val v = Free (s', T)
        in
          (v, (s'::names, AList.update (op =) (s, v::xs) vs))
        end);

fun distinct_v (Free (s, T)) nvs = mk_v nvs s T
  | distinct_v (t $ u) nvs =
      let
        val (t', nvs') = distinct_v t nvs;
        val (u', nvs'') = distinct_v u nvs';
      in (t' $ u', nvs'') end
  | distinct_v x nvs = (x, nvs);

fun compile_match thy eqs eqs' out_ts success_t =
  let 
    val eqs'' = maps mk_eq eqs @ eqs'
    val names = fold Term.add_free_names (success_t :: eqs'' @ out_ts) [];
    val name = Name.variant names "x";
    val name' = Name.variant (name :: names) "y";
    val T = mk_tupleT (map fastype_of out_ts);
    val U = fastype_of success_t;
    val U' = dest_pred_enumT U;
    val v = Free (name, T);
    val v' = Free (name', T);
  in
    lambda v (fst (Datatype.make_case
      (ProofContext.init thy) false [] v
      [(mk_tuple out_ts,
        if null eqs'' then success_t
        else Const (@{const_name HOL.If}, HOLogic.boolT --> U --> U --> U) $
          foldr1 HOLogic.mk_conj eqs'' $ success_t $
            mk_empty U'),
       (v', mk_empty U')]))
  end;

(*FIXME function can be removed*)
fun mk_funcomp f t =
  let
    val names = Term.add_free_names t [];
    val Ts = binder_types (fastype_of t);
    val vs = map Free
      (Name.variant_list names (replicate (length Ts) "x") ~~ Ts)
  in
    fold_rev lambda vs (f (list_comb (t, vs)))
  end;



fun compile_param_ext thy modes (NONE, t) = t
  | compile_param_ext thy modes (m as SOME (Mode ((iss, is'), is, ms)), t) =
      let
        val (vs, u) = strip_abs t
        val (ivs, ovs) = get_args is vs    
        val (f, args) = strip_comb u
        val (params, args') = chop (length ms) args
        val (inargs, outargs) = get_args is' args'
        val b = length vs
        val perm = map (fn i => find_index (fn t => t = Bound (b - i)) args' + 1) (1 upto b)
        val outp_perm =
          snd (get_args is perm)
          |> map (fn i => i - length (filter (fn x => x < i) is'))
        val names = [] (* TODO *)
        val out_names = Name.variant_list names (replicate (length outargs) "x")
        val f' = case f of
            Const (name, T) =>
              if AList.defined op = modes name then
                Const (predfun_name_of thy name (iss, is'), funT'_of (iss, is') T)
              else error "compile param: Not an inductive predicate with correct mode"
          | Free (name, T) => Free (name, funT_of T (SOME is'))
        val outTs = dest_tupleT (dest_pred_enumT (body_type (fastype_of f')))
        val out_vs = map Free (out_names ~~ outTs)
        val params' = map (compile_param thy modes) (ms ~~ params)
        val f_app = list_comb (f', params' @ inargs)
        val single_t = (mk_single (mk_tuple (map (fn i => nth out_vs (i - 1)) outp_perm)))
        val match_t = compile_match thy [] [] out_vs single_t
      in list_abs (ivs,
        mk_bind (f_app, match_t))
      end
  | compile_param_ext _ _ _ = error "compile params"

and compile_param thy modes (NONE, t) = t
 | compile_param thy modes (m as SOME (Mode ((iss, is'), is, ms)), t) =
   (* (case t of
     Abs _ => error "compile_param: Invalid term" *) (* compile_param_ext thy modes (m, t) *)
   (*  |  _ => let *)
   let  
     val (f, args) = strip_comb (Envir.eta_contract t)
     val (params, args') = chop (length ms) args
     val params' = map (compile_param thy modes) (ms ~~ params)
     val f' = case f of
        Const (name, T) =>
          if AList.defined op = modes name then
             Const (predfun_name_of thy name (iss, is'), funT'_of (iss, is') T)
          else error "compile param: Not an inductive predicate with correct mode"
      | Free (name, T) => Free (name, funT_of T (SOME is'))
   in list_comb (f', params' @ args') end
 | compile_param _ _ _ = error "compile params"
  
  
fun compile_expr thy modes (SOME (Mode (mode, is, ms)), t) =
      (case strip_comb t of
         (Const (name, T), params) =>
           if AList.defined op = modes name then
             let
               val (Ts, Us) = get_args is
                 (curry Library.drop (length ms) (fst (strip_type T)))
               val params' = map (compile_param thy modes) (ms ~~ params)
             in list_comb (Const (predfun_name_of thy name mode, ((map fastype_of params') @ Ts) --->
               mk_pred_enumT (mk_tupleT Us)), params')
             end
           else error "not a valid inductive expression"
       | (Free (name, T), args) =>
         (*if name mem param_vs then *)
         (* Higher order mode call *)
         let val r = Free (name, funT_of T (SOME is))
         in list_comb (r, args) end)
  | compile_expr _ _ _ = error "not a valid inductive expression"


fun compile_clause thy all_vs param_vs modes (iss, is) (ts, ps) inp =
  let
    val modes' = modes @ List.mapPartial
      (fn (_, NONE) => NONE | (v, SOME js) => SOME (v, [([], js)]))
        (param_vs ~~ iss);
    fun check_constrt t (names, eqs) =
      if is_constrt thy t then (t, (names, eqs)) else
        let
          val s = Name.variant names "x";
          val v = Free (s, fastype_of t)
        in (v, (s::names, HOLogic.mk_eq (v, t)::eqs)) end;

    val (in_ts, out_ts) = get_args is ts;
    val (in_ts', (all_vs', eqs)) =
      fold_map check_constrt in_ts (all_vs, []);

    fun compile_prems out_ts' vs names [] =
          let
            val (out_ts'', (names', eqs')) =
              fold_map check_constrt out_ts' (names, []);
            val (out_ts''', (names'', constr_vs)) = fold_map distinct_v
              out_ts'' (names', map (rpair []) vs);
          in
            compile_match thy constr_vs (eqs @ eqs') out_ts'''
              (mk_single (mk_tuple out_ts))
          end
      | compile_prems out_ts vs names ps =
          let
            val vs' = distinct (op =) (flat (vs :: map term_vs out_ts));
            val SOME (p, mode as SOME (Mode (_, js, _))) =
              select_mode_prem thy modes' vs' ps
            val ps' = filter_out (equal p) ps
            val (out_ts', (names', eqs)) =
              fold_map check_constrt out_ts (names, [])
            val (out_ts'', (names'', constr_vs')) = fold_map distinct_v
              out_ts' ((names', map (rpair []) vs))
            val (compiled_clause, rest) = case p of
               Prem (us, t) =>
                 let
                   val (in_ts, out_ts''') = get_args js us;
                   val u = list_comb (compile_expr thy modes (mode, t), in_ts)
                   val rest = compile_prems out_ts''' vs' names'' ps'
                 in
                   (u, rest)
                 end
             | Negprem (us, t) =>
                 let
                   val (in_ts, out_ts''') = get_args js us
                   val u = list_comb (compile_expr thy modes (mode, t), in_ts)
                   val rest = compile_prems out_ts''' vs' names'' ps'
                 in
                   (mk_not_pred u, rest)
                 end
             | Sidecond t =>
                 let
                   val rest = compile_prems [] vs' names'' ps';
                 in
                   (mk_if_predenum t, rest)
                 end
          in
            compile_match thy constr_vs' eqs out_ts'' 
              (mk_bind (compiled_clause, rest))
          end
    val prem_t = compile_prems in_ts' param_vs all_vs' ps;
  in
    mk_bind (mk_single inp, prem_t)
  end

fun compile_pred thy all_vs param_vs modes s T cls mode =
  let
    val Ts = binder_types T;
    val (Ts1, Ts2) = chop (length param_vs) Ts;
    val Ts1' = map2 funT_of Ts1 (fst mode)
    val (Us1, Us2) = get_args (snd mode) Ts2;
    val xnames = Name.variant_list param_vs
      (map (fn i => "x" ^ string_of_int i) (snd mode));
    val xs = map2 (fn s => fn T => Free (s, T)) xnames Us1;
    val cl_ts =
      map (fn cl => compile_clause thy
        all_vs param_vs modes mode cl (mk_tuple xs)) cls;
    val mode_id = predfun_name_of thy s mode
  in
    HOLogic.mk_Trueprop (HOLogic.mk_eq
      (list_comb (Const (mode_id, (Ts1' @ Us1) --->
           mk_pred_enumT (mk_tupleT Us2)),
         map2 (fn s => fn T => Free (s, T)) param_vs Ts1' @ xs),
       foldr1 mk_sup cl_ts))
  end;

fun compile_preds thy all_vs param_vs modes preds =
  map (fn (s, (T, cls)) =>
    map (compile_pred thy all_vs param_vs modes s T cls)
      ((the o AList.lookup (op =) modes) s)) preds;


(* special setup for simpset *)                  
val HOL_basic_ss' = HOL_basic_ss setSolver 
  (mk_solver "all_tac_solver" (fn _ => fn _ => all_tac))


(* Definition of executable functions and their intro and elim rules *)

fun print_arities arities = tracing ("Arities:\n" ^
  cat_lines (map (fn (s, (ks, k)) => s ^ ": " ^
    space_implode " -> " (map
      (fn NONE => "X" | SOME k' => string_of_int k')
        (ks @ [SOME k]))) arities));

fun mk_Eval_of ((x, T), NONE) names = (x, names)
  | mk_Eval_of ((x, T), SOME mode) names = let
  val Ts = binder_types T
  val argnames = Name.variant_list names
        (map (fn i => "x" ^ string_of_int i) (1 upto (length Ts)));
  val args = map Free (argnames ~~ Ts)
  val (inargs, outargs) = get_args mode args
  val r = mk_Eval (list_comb (x, inargs), mk_tuple outargs)
  val t = fold_rev lambda args r 
in
  (t, argnames @ names)
end;

fun create_intro_elim_rule nparams mode defthm mode_id funT pred thy =
let
  val Ts = binder_types (fastype_of pred)
  val funtrm = Const (mode_id, funT)
  val argnames = Name.variant_list []
        (map (fn i => "x" ^ string_of_int i) (1 upto (length Ts)));
  val (Ts1, Ts2) = chop nparams Ts;
  val Ts1' = map2 funT_of Ts1 (fst mode)
  val args = map Free (argnames ~~ (Ts1' @ Ts2))
  val (params, io_args) = chop nparams args
  val (inargs, outargs) = get_args (snd mode) io_args
  val param_names = Name.variant_list argnames
    (map (fn i => "p" ^ string_of_int i) (1 upto nparams))
  val param_vs = map Free (param_names ~~ Ts1)
  val (params', names) = fold_map mk_Eval_of ((params ~~ Ts1) ~~ (fst mode)) []
  val predpropI = HOLogic.mk_Trueprop (list_comb (pred, param_vs @ io_args))
  val predpropE = HOLogic.mk_Trueprop (list_comb (pred, params' @ io_args))
  val param_eqs = map (HOLogic.mk_Trueprop o HOLogic.mk_eq) (param_vs ~~ params')
  val funargs = params @ inargs
  val funpropE = HOLogic.mk_Trueprop (mk_Eval (list_comb (funtrm, funargs),
                  if null outargs then Free("y", HOLogic.unitT) else mk_tuple outargs))
  val funpropI = HOLogic.mk_Trueprop (mk_Eval (list_comb (funtrm, funargs),
                   mk_tuple outargs))
  val introtrm = Logic.list_implies (predpropI :: param_eqs, funpropI)
  val _ = Output.tracing (Syntax.string_of_term_global thy introtrm) 
  val simprules = [defthm, @{thm eval_pred},
                   @{thm "split_beta"}, @{thm "fst_conv"}, @{thm "snd_conv"}]
  val unfolddef_tac = (Simplifier.asm_full_simp_tac (HOL_basic_ss addsimps simprules) 1)
  val introthm = Goal.prove (ProofContext.init thy) (argnames @ param_names @ ["y"]) [] introtrm (fn {...} => unfolddef_tac)
  val P = HOLogic.mk_Trueprop (Free ("P", HOLogic.boolT));
  val elimtrm = Logic.list_implies ([funpropE, Logic.mk_implies (predpropE, P)], P)
  val elimthm = Goal.prove (ProofContext.init thy) (argnames @ param_names @ ["y", "P"]) [] elimtrm (fn {...} => unfolddef_tac)
in 
  (introthm, elimthm)
end;

fun create_definitions preds nparams (name, modes) thy =
  let
    val _ = tracing "create definitions"
    val T = AList.lookup (op =) preds name |> the
    fun create_definition mode thy = let
      fun string_of_mode mode = if null mode then "0"
        else space_implode "_" (map string_of_int mode)
      val HOmode = let
        fun string_of_HOmode m s = case m of NONE => s | SOME mode => s ^ "__" ^ (string_of_mode mode)    
        in (fold string_of_HOmode (fst mode) "") end;
      val mode_id = name ^ (if HOmode = "" then "_" else HOmode ^ "___")
        ^ (string_of_mode (snd mode))
      val Ts = binder_types T;
      val (Ts1, Ts2) = chop nparams Ts;
      val Ts1' = map2 funT_of Ts1 (fst mode)
      val (Us1, Us2) = get_args (snd mode) Ts2;
      val names = Name.variant_list []
        (map (fn i => "x" ^ string_of_int i) (1 upto (length Ts)));
      val xs = map Free (names ~~ (Ts1' @ Ts2));
      val (xparams, xargs) = chop nparams xs;
      val (xparams', names') = fold_map mk_Eval_of ((xparams ~~ Ts1) ~~ (fst mode)) names
      val (xins, xouts) = get_args (snd mode) xargs;
      fun mk_split_lambda [] t = lambda (Free (Name.variant names' "x", HOLogic.unitT)) t
       | mk_split_lambda [x] t = lambda x t
       | mk_split_lambda xs t = let
         fun mk_split_lambda' (x::y::[]) t = HOLogic.mk_split (lambda x (lambda y t))
           | mk_split_lambda' (x::xs) t = HOLogic.mk_split (lambda x (mk_split_lambda' xs t))
         in mk_split_lambda' xs t end;
      val predterm = mk_Enum (mk_split_lambda xouts (list_comb (Const (name, T), xparams' @ xargs)))
      val funT = (Ts1' @ Us1) ---> (mk_pred_enumT (mk_tupleT Us2))
      val mode_id = Sign.full_bname thy (Long_Name.base_name mode_id)
      val lhs = list_comb (Const (mode_id, funT), xparams @ xins)
      val def = Logic.mk_equals (lhs, predterm)
      val ([definition], thy') = thy |>
        Sign.add_consts_i [(Binding.name (Long_Name.base_name mode_id), funT, NoSyn)] |>
        PureThy.add_defs false [((Binding.name (Long_Name.base_name mode_id ^ "_def"), def), [])]
      val (intro, elim) = create_intro_elim_rule nparams mode definition mode_id funT (Const (name, T)) thy'
      in thy' |> add_predfun name mode (mode_id, definition, intro, elim)
        |> PureThy.store_thm (Binding.name (Long_Name.base_name mode_id ^ "I"), intro) |> snd
        |> PureThy.store_thm (Binding.name (Long_Name.base_name mode_id ^ "E"), elim)  |> snd
        |> Theory.checkpoint
      end;
  in
    fold create_definition modes thy
  end;

(**************************************************************************************)
(* Proving equivalence of term *)

fun is_Type (Type _) = true
  | is_Type _ = false

(* returns true if t is an application of an datatype constructor *)
(* which then consequently would be splitted *)
(* else false *)
fun is_constructor thy t =
  if (is_Type (fastype_of t)) then
    (case Datatype.get_info thy ((fst o dest_Type o fastype_of) t) of
      NONE => false
    | SOME info => (let
      val constr_consts = maps (fn (_, (_, _, constrs)) => map fst constrs) (#descr info)
      val (c, _) = strip_comb t
      in (case c of
        Const (name, _) => name mem_string constr_consts
        | _ => false) end))
  else false

(* MAJOR FIXME:  prove_params should be simple
 - different form of introrule for parameters ? *)
fun prove_param thy modes (NONE, t) =
  all_tac 
| prove_param thy modes (m as SOME (Mode (mode, is, ms)), t) =
  REPEAT_DETERM (etac @{thm thin_rl} 1)
  THEN REPEAT_DETERM (rtac @{thm ext} 1)
  THEN (rtac @{thm iffI} 1)
  THEN new_print_tac "prove_param"
  (* proof in one direction *)
  THEN (atac 1)
  (* proof in the other direction *)
  THEN (atac 1)
  THEN new_print_tac "after prove_param"
(*  let
    val  (f, args) = strip_comb t
    val (params, _) = chop (length ms) args
    val f_tac = case f of
        Const (name, T) => simp_tac (HOL_basic_ss addsimps 
           (@{thm eval_pred}::(predfun_definition_of thy name mode)::
           @{thm "Product_Type.split_conv"}::[])) 1
      | Free _ => all_tac
      | Abs _ => error "TODO: implement here"
  in  
    print_tac "before simplification in prove_args:"
    THEN f_tac
    THEN print_tac "after simplification in prove_args"
    THEN (EVERY (map (prove_param thy modes) (ms ~~ params)))
    THEN (REPEAT_DETERM (atac 1))
  end
*)
fun prove_expr thy modes (SOME (Mode (mode, is, ms)), t, us) (premposition : int) =
  (case strip_comb t of
    (Const (name, T), args) =>
      if AList.defined op = modes name then (let
          val introrule = predfun_intro_of thy name mode
          (*val (in_args, out_args) = get_args is us
          val (pred, rargs) = strip_comb (HOLogic.dest_Trueprop
            (hd (Logic.strip_imp_prems (prop_of introrule))))
          val nparams = length ms (* get_nparams thy (fst (dest_Const pred)) *)
          val (_, args) = chop nparams rargs
          val subst = map (pairself (cterm_of thy)) (args ~~ us)
          val inst_introrule = Drule.cterm_instantiate subst introrule*)
         (* the next line is old and probably wrong *)
          val (args1, args2) = chop (length ms) args
        in
        rtac @{thm bindI} 1
        THEN print_tac "before intro rule:"
        (* for the right assumption in first position *)
        THEN rotate_tac premposition 1
        THEN rtac introrule 1
        THEN new_print_tac "after intro rule"
        (* work with parameter arguments *)
        THEN (atac 1)
        THEN (new_print_tac "parameter goal")
        THEN (EVERY (map (prove_param thy modes) (ms ~~ args1)))
        THEN (REPEAT_DETERM (atac 1)) end)
      else error "Prove expr if case not implemented"
    | _ => rtac @{thm bindI} 1
           THEN atac 1)
  | prove_expr _ _ _ _ =  error "Prove expr not implemented"

fun SOLVED tac st = FILTER (fn st' => nprems_of st' = nprems_of st - 1) tac st; 

fun SOLVEDALL tac st = FILTER (fn st' => nprems_of st' = 0) tac st

fun prove_match thy (out_ts : term list) = let
  fun get_case_rewrite t =
    if (is_constructor thy t) then let
      val case_rewrites = (#case_rewrites (Datatype.the_info thy
        ((fst o dest_Type o fastype_of) t)))
      in case_rewrites @ (flat (map get_case_rewrite (snd (strip_comb t)))) end
    else []
  val simprules = @{thm "unit.cases"} :: @{thm "prod.cases"} :: (flat (map get_case_rewrite out_ts))
(* replace TRY by determining if it necessary - are there equations when calling compile match? *)
in
   (* make this simpset better! *)
  asm_simp_tac (HOL_basic_ss' addsimps simprules) 1
  THEN print_tac "after prove_match:"
  THEN (DETERM (TRY (EqSubst.eqsubst_tac (ProofContext.init thy) [0] [@{thm "HOL.if_P"}] 1
         THEN (REPEAT_DETERM (rtac @{thm conjI} 1 THEN (SOLVED (asm_simp_tac HOL_basic_ss 1))))
         THEN (SOLVED (asm_simp_tac HOL_basic_ss 1)))))
  THEN print_tac "after if simplification"
end;

(* corresponds to compile_fun -- maybe call that also compile_sidecond? *)

fun prove_sidecond thy modes t =
  let
    fun preds_of t nameTs = case strip_comb t of 
      (f as Const (name, T), args) =>
        if AList.defined (op =) modes name then (name, T) :: nameTs
          else fold preds_of args nameTs
      | _ => nameTs
    val preds = preds_of t []
    val defs = map
      (fn (pred, T) => predfun_definition_of thy pred ([], (1 upto (length (binder_types T)))))
        preds
  in 
    (* remove not_False_eq_True when simpset in prove_match is better *)
    simp_tac (HOL_basic_ss addsimps @{thm not_False_eq_True} :: @{thm eval_pred} :: defs) 1 
    (* need better control here! *)
  end

fun prove_clause thy nargs all_vs param_vs modes (iss, is) (ts, ps) = let
  val modes' = modes @ List.mapPartial
   (fn (_, NONE) => NONE | (v, SOME js) => SOME (v, [([], js)]))
     (param_vs ~~ iss);
  fun check_constrt ((names, eqs), t) =
      if is_constrt thy t then ((names, eqs), t) else
        let
          val s = Name.variant names "x";
          val v = Free (s, fastype_of t)
        in ((s::names, HOLogic.mk_eq (v, t)::eqs), v) end;
  
  val (in_ts, clause_out_ts) = get_args is ts;
  val ((all_vs', eqs), in_ts') =
      (*FIXME*) Library.foldl_map check_constrt ((all_vs, []), in_ts);
  fun prove_prems out_ts vs [] =
    (prove_match thy out_ts)
    THEN asm_simp_tac HOL_basic_ss' 1
    THEN print_tac "before the last rule of singleI:"
    THEN (rtac (if null clause_out_ts then @{thm singleI_unit} else @{thm singleI}) 1)
  | prove_prems out_ts vs rps =
    let
      val vs' = distinct (op =) (flat (vs :: map term_vs out_ts));
      val SOME (p, mode as SOME (Mode ((iss, js), _, param_modes))) =
        select_mode_prem thy modes' vs' rps;
      val premposition = (find_index (equal p) ps) + nargs
      val rps' = filter_out (equal p) rps;
      val rest_tac = (case p of Prem (us, t) =>
          let
            val (in_ts, out_ts''') = get_args js us
            val rec_tac = prove_prems out_ts''' vs' rps'
          in
            print_tac "before clause:"
            THEN asm_simp_tac HOL_basic_ss 1
            THEN print_tac "before prove_expr:"
            THEN prove_expr thy modes (mode, t, us) premposition
            THEN print_tac "after prove_expr:"
            THEN rec_tac
          end
        | Negprem (us, t) =>
          let
            val (in_ts, out_ts''') = get_args js us
            val rec_tac = prove_prems out_ts''' vs' rps'
            val name = (case strip_comb t of (Const (c, _), _) => SOME c | _ => NONE)
            val (_, params) = strip_comb t
          in
            rtac @{thm bindI} 1
            THEN (if (is_some name) then
                simp_tac (HOL_basic_ss addsimps [predfun_definition_of thy (the name) (iss, js)]) 1
                THEN rtac @{thm not_predI} 1
                (* FIXME: work with parameter arguments *)
                THEN (EVERY (map (prove_param thy modes) (param_modes ~~ params)))
              else
                rtac @{thm not_predI'} 1)
            THEN (REPEAT_DETERM (atac 1))
            THEN rec_tac
          end
        | Sidecond t =>
         rtac @{thm bindI} 1
         THEN rtac @{thm if_predI} 1
         THEN print_tac "before sidecond:"
         THEN prove_sidecond thy modes t
         THEN print_tac "after sidecond:"
         THEN prove_prems [] vs' rps')
    in (prove_match thy out_ts)
        THEN rest_tac
    end;
  val prems_tac = prove_prems in_ts' param_vs ps
in
  rtac @{thm bindI} 1
  THEN rtac @{thm singleI} 1
  THEN prems_tac
end;

fun select_sup 1 1 = []
  | select_sup _ 1 = [rtac @{thm supI1}]
  | select_sup n i = (rtac @{thm supI2})::(select_sup (n - 1) (i - 1));

fun prove_one_direction thy all_vs param_vs modes clauses ((pred, T), mode) = let
(*  val ind_result = Inductive.the_inductive (ProofContext.init thy) pred
  val index = find_index (fn s => s = pred) (#names (fst ind_result))
  val (_, T) = dest_Const (nth (#preds (snd ind_result)) index) *)
  val nargs = length (binder_types T) - nparams_of thy pred
  val pred_case_rule = singleton (ind_set_codegen_preproc thy)
    (preprocess_elim thy nargs (the_elim_of thy pred))
  (* FIXME preprocessor |> Simplifier.full_simplify (HOL_basic_ss addsimps [@{thm Predicate.memb_code}])*)
in
  REPEAT_DETERM (CHANGED (rewtac @{thm "split_paired_all"}))
  THEN etac (predfun_elim_of thy pred mode) 1
  THEN etac pred_case_rule 1
  THEN (EVERY (map
         (fn i => EVERY' (select_sup (length clauses) i) i) 
           (1 upto (length clauses))))
  THEN (EVERY (map (prove_clause thy nargs all_vs param_vs modes mode) clauses))
  THEN new_print_tac "proved one direction"
end;

(*******************************************************************************************************)
(* Proof in the other direction ************************************************************************)
(*******************************************************************************************************)

fun prove_match2 thy out_ts = let
  fun split_term_tac (Free _) = all_tac
    | split_term_tac t =
      if (is_constructor thy t) then let
        val info = Datatype.the_info thy ((fst o dest_Type o fastype_of) t)
        val num_of_constrs = length (#case_rewrites info)
        (* special treatment of pairs -- because of fishing *)
        val split_rules = case (fst o dest_Type o fastype_of) t of
          "*" => [@{thm prod.split_asm}] 
          | _ => PureThy.get_thms thy (((fst o dest_Type o fastype_of) t) ^ ".split_asm")
        val (_, ts) = strip_comb t
      in
        (Splitter.split_asm_tac split_rules 1)
(*        THEN (Simplifier.asm_full_simp_tac HOL_basic_ss 1)
          THEN (DETERM (TRY (etac @{thm Pair_inject} 1))) *)
        THEN (REPEAT_DETERM_N (num_of_constrs - 1) (etac @{thm botE} 1 ORELSE etac @{thm botE} 2))
        THEN (EVERY (map split_term_tac ts))
      end
    else all_tac
  in
    split_term_tac (mk_tuple out_ts)
    THEN (DETERM (TRY ((Splitter.split_asm_tac [@{thm "split_if_asm"}] 1) THEN (etac @{thm botE} 2))))
  end

(* VERY LARGE SIMILIRATIY to function prove_param 
-- join both functions
*)

fun prove_param2 thy modes (NONE, t) = all_tac 
  | prove_param2 thy modes (m as SOME (Mode (mode, is, ms)), t) = let
    val  (f, args) = strip_comb t
    val (params, _) = chop (length ms) args
    val f_tac = case f of
        Const (name, T) => full_simp_tac (HOL_basic_ss addsimps 
           (@{thm eval_pred}::(predfun_definition_of thy name mode)
           :: @{thm "Product_Type.split_conv"}::[])) 1
      | Free _ => all_tac
  in  
    print_tac "before simplification in prove_args:"
    THEN f_tac
    THEN print_tac "after simplification in prove_args"
    THEN (EVERY (map (prove_param2 thy modes) (ms ~~ params)))
  end


fun prove_expr2 thy modes (SOME (Mode (mode, is, ms)), t) = 
  (case strip_comb t of
    (Const (name, T), args) =>
      if AList.defined op = modes name then
        etac @{thm bindE} 1
        THEN (REPEAT_DETERM (CHANGED (rewtac @{thm "split_paired_all"})))
        THEN new_print_tac "prove_expr2-before"
        THEN (debug_tac (Syntax.string_of_term_global thy
          (prop_of (predfun_elim_of thy name mode))))
        THEN (etac (predfun_elim_of thy name mode) 1)
        THEN new_print_tac "prove_expr2"
        (* TODO -- FIXME: replace remove_last_goal*)
        (* THEN (EVERY (replicate (length args) (remove_last_goal thy))) *)
        THEN (EVERY (map (prove_param thy modes) (ms ~~ args)))
        THEN new_print_tac "finished prove_expr2"
      
      else error "Prove expr2 if case not implemented"
    | _ => etac @{thm bindE} 1)
  | prove_expr2 _ _ _ = error "Prove expr2 not implemented"

fun prove_sidecond2 thy modes t = let
  fun preds_of t nameTs = case strip_comb t of 
    (f as Const (name, T), args) =>
      if AList.defined (op =) modes name then (name, T) :: nameTs
        else fold preds_of args nameTs
    | _ => nameTs
  val preds = preds_of t []
  val defs = map
    (fn (pred, T) => predfun_definition_of thy pred ([], (1 upto (length (binder_types T)))))
      preds
  in
   (* only simplify the one assumption *)
   full_simp_tac (HOL_basic_ss' addsimps @{thm eval_pred} :: defs) 1 
   (* need better control here! *)
   THEN print_tac "after sidecond2 simplification"
   end
  
fun prove_clause2 thy all_vs param_vs modes (iss, is) (ts, ps) pred i = let
  val modes' = modes @ List.mapPartial
   (fn (_, NONE) => NONE | (v, SOME js) => SOME (v, [([], js)]))
     (param_vs ~~ iss);
  fun check_constrt ((names, eqs), t) =
      if is_constrt thy t then ((names, eqs), t) else
        let
          val s = Name.variant names "x";
          val v = Free (s, fastype_of t)
        in ((s::names, HOLogic.mk_eq (v, t)::eqs), v) end;
  val pred_intro_rule = nth (intros_of thy pred) (i - 1)
    |> preprocess_intro thy
    |> (fn thm => hd (ind_set_codegen_preproc thy [thm]))
    (* FIXME preprocess |> Simplifier.full_simplify (HOL_basic_ss addsimps [@ {thm Predicate.memb_code}]) *)
  val (in_ts, clause_out_ts) = get_args is ts;
  val ((all_vs', eqs), in_ts') =
      (*FIXME*) Library.foldl_map check_constrt ((all_vs, []), in_ts);
  fun prove_prems2 out_ts vs [] =
    print_tac "before prove_match2 - last call:"
    THEN prove_match2 thy out_ts
    THEN print_tac "after prove_match2 - last call:"
    THEN (etac @{thm singleE} 1)
    THEN (REPEAT_DETERM (etac @{thm Pair_inject} 1))
    THEN (asm_full_simp_tac HOL_basic_ss' 1)
    THEN (REPEAT_DETERM (etac @{thm Pair_inject} 1))
    THEN (asm_full_simp_tac HOL_basic_ss' 1)
    THEN SOLVED (print_tac "state before applying intro rule:"
      THEN (rtac pred_intro_rule 1)
      (* How to handle equality correctly? *)
      THEN (print_tac "state before assumption matching")
      THEN (REPEAT (atac 1 ORELSE 
         (CHANGED (asm_full_simp_tac HOL_basic_ss' 1)
          THEN print_tac "state after simp_tac:"))))
  | prove_prems2 out_ts vs ps = let
      val vs' = distinct (op =) (flat (vs :: map term_vs out_ts));
      val SOME (p, mode as SOME (Mode ((iss, js), _, param_modes))) =
        select_mode_prem thy modes' vs' ps;
      val ps' = filter_out (equal p) ps;
      val rest_tac = (case p of Prem (us, t) =>
          let
            val (in_ts, out_ts''') = get_args js us
            val rec_tac = prove_prems2 out_ts''' vs' ps'
          in
            (prove_expr2 thy modes (mode, t)) THEN rec_tac
          end
        | Negprem (us, t) =>
          let
            val (in_ts, out_ts''') = get_args js us
            val rec_tac = prove_prems2 out_ts''' vs' ps'
            val name = (case strip_comb t of (Const (c, _), _) => SOME c | _ => NONE)
            val (_, params) = strip_comb t
          in
            print_tac "before neg prem 2"
            THEN etac @{thm bindE} 1
            THEN (if is_some name then
                full_simp_tac (HOL_basic_ss addsimps [predfun_definition_of thy (the name) (iss, js)]) 1 
                THEN etac @{thm not_predE} 1
                THEN (EVERY (map (prove_param thy modes) (param_modes ~~ params)))
              else
                etac @{thm not_predE'} 1)
            THEN rec_tac
          end 
        | Sidecond t =>
            etac @{thm bindE} 1
            THEN etac @{thm if_predE} 1
            THEN prove_sidecond2 thy modes t 
            THEN prove_prems2 [] vs' ps')
    in print_tac "before prove_match2:"
       THEN prove_match2 thy out_ts
       THEN print_tac "after prove_match2:"
       THEN rest_tac
    end;
  val prems_tac = prove_prems2 in_ts' param_vs ps 
in
  new_print_tac "starting prove_clause2"
  THEN etac @{thm bindE} 1
  THEN (etac @{thm singleE'} 1)
  THEN (TRY (etac @{thm Pair_inject} 1))
  THEN print_tac "after singleE':"
  THEN prems_tac
end;
 
fun prove_other_direction thy all_vs param_vs modes clauses (pred, mode) = let
  fun prove_clause (clause, i) =
    (if i < length clauses then etac @{thm supE} 1 else all_tac)
    THEN (prove_clause2 thy all_vs param_vs modes mode clause pred i)
in
  (DETERM (TRY (rtac @{thm unit.induct} 1)))
   THEN (REPEAT_DETERM (CHANGED (rewtac @{thm split_paired_all})))
   THEN (rtac (predfun_intro_of thy pred mode) 1)
   THEN (REPEAT_DETERM (rtac @{thm refl} 2))
   THEN (EVERY (map prove_clause (clauses ~~ (1 upto (length clauses)))))
end;

fun prove_pred thy all_vs param_vs modes clauses (((pred, T), mode), t) = let
  val ctxt = ProofContext.init thy
  val clauses' = the (AList.lookup (op =) clauses pred)
in
  Goal.prove ctxt (Term.fold_aterms (fn Free (x, _) => insert (op =) x | _ => I) t []) [] t
    (if !do_proofs then
      (fn _ =>
      rtac @{thm pred_iffI} 1
      THEN prove_one_direction thy all_vs param_vs modes clauses' ((pred, T), mode)
      THEN print_tac "proved one direction"
      THEN prove_other_direction thy all_vs param_vs modes clauses' (pred, mode)
      THEN print_tac "proved other direction")
     else (fn _ => mycheat_tac thy 1))
end;

fun prove_preds thy all_vs param_vs modes clauses pmts =
  map (prove_pred thy all_vs param_vs modes clauses) pmts

(* special case: inductive predicate with no clauses *)
fun noclause (predname, T) thy = let
  val Ts = binder_types T
  val names = Name.variant_list []
        (map (fn i => "x" ^ (string_of_int i)) (1 upto (length Ts)))
  val vs = map2 (curry Free) names Ts
  val clausehd =  HOLogic.mk_Trueprop (list_comb(Const (predname, T), vs))
  val intro_t = Logic.mk_implies (@{prop False}, clausehd)
  val P = HOLogic.mk_Trueprop (Free ("P", HOLogic.boolT))
  val elim_t = Logic.list_implies ([clausehd, Logic.mk_implies (@{prop False}, P)], P)
  val intro = Goal.prove (ProofContext.init thy) names [] intro_t
        (fn {...} => etac @{thm FalseE} 1)
  val elim = Goal.prove (ProofContext.init thy) ("P" :: names) [] elim_t
        (fn {...} => etac (the_elim_of thy predname) 1) 
in
  add_intro intro thy
  |> set_elim elim
end

fun prepare_intrs thy prednames =
  let
    (* FIXME: preprocessing moved to fetch_pred_data *)
    val intrs = map (preprocess_intro thy) (maps (intros_of thy) prednames)
      |> ind_set_codegen_preproc thy (*FIXME preprocessor
      |> map (Simplifier.full_simplify (HOL_basic_ss addsimps [@ {thm Predicate.memb_code}]))*)
      |> map (Logic.unvarify o prop_of)
    val nparams = nparams_of thy (hd prednames)
    val preds = distinct (op =) (map (dest_Const o fst o (strip_intro_concl nparams)) intrs)
    val extra_modes = all_modes_of thy |> filter_out (fn (name, _) => member (op =) prednames name)
    val _ $ u = Logic.strip_imp_concl (hd intrs);
    val params = List.take (snd (strip_comb u), nparams);
    val param_vs = maps term_vs params
    val all_vs = terms_vs intrs
    fun dest_prem t =
      (case strip_comb t of
        (v as Free _, ts) => if v mem params then Prem (ts, v) else Sidecond t
      | (c as Const (@{const_name Not}, _), [t]) => (case dest_prem t of
          Prem (ts, t) => Negprem (ts, t)
        | Negprem _ => error ("Double negation not allowed in premise: " ^ (Syntax.string_of_term_global thy (c $ t))) 
        | Sidecond t => Sidecond (c $ t))
      | (c as Const (s, _), ts) =>
        if is_registered thy s then
          let val (ts1, ts2) = chop (nparams_of thy s) ts
          in Prem (ts2, list_comb (c, ts1)) end
        else Sidecond t
      | _ => Sidecond t)
    fun add_clause intr (clauses, arities) =
    let
      val _ $ t = Logic.strip_imp_concl intr;
      val (Const (name, T), ts) = strip_comb t;
      val (ts1, ts2) = chop nparams ts;
      val prems = map (dest_prem o HOLogic.dest_Trueprop) (Logic.strip_imp_prems intr);
      val (Ts, Us) = chop nparams (binder_types T)
    in
      (AList.update op = (name, these (AList.lookup op = clauses name) @
        [(ts2, prems)]) clauses,
       AList.update op = (name, (map (fn U => (case strip_type U of
                 (Rs as _ :: _, Type ("bool", [])) => SOME (length Rs)
               | _ => NONE)) Ts,
             length Us)) arities)
    end;
    val (clauses, arities) = fold add_clause intrs ([], []);
  in (preds, nparams, all_vs, param_vs, extra_modes, clauses, arities) end;

fun arrange kvs =
  let
    fun add (key, value) table =
      AList.update op = (key, these (AList.lookup op = table key) @ [value]) table
  in fold add kvs [] end;
        
(* main function *)

fun add_equations_of prednames thy =
let
  val _ = tracing ("starting add_equations with " ^ commas prednames ^ "...")
  (* null clause handling *)
  (*
  val thy' = fold (fn pred as (predname, T) => fn thy =>
    if null (intros_of thy predname) then noclause pred thy else thy) preds thy
    *)
  val (preds, nparams, all_vs, param_vs, extra_modes, clauses, arities) =
    prepare_intrs thy prednames
  val _ = tracing "Infering modes..."
  val modes = infer_modes thy extra_modes arities param_vs clauses
  val _ = print_modes modes
  val _ = tracing "Defining executable functions..."
  val thy' = fold (create_definitions preds nparams) modes thy |> Theory.checkpoint
  val clauses' = map (fn (s, cls) => (s, (the (AList.lookup (op =) preds s), cls))) clauses
  val _ = tracing "Compiling equations..."
  val ts = compile_preds thy' all_vs param_vs (extra_modes @ modes) clauses'
  val _ = map (Output.tracing o (Syntax.string_of_term_global thy')) (flat ts)
  val pred_mode =
    maps (fn (s, (T, _)) => map (pair (s, T)) ((the o AList.lookup (op =) modes) s)) clauses' 
  val _ = Output.tracing "Proving equations..."
  val result_thms =
    prove_preds thy' all_vs param_vs (extra_modes @ modes) clauses (pred_mode ~~ (flat ts))
  val thy'' = fold (fn (name, result_thms) => fn thy => snd (PureThy.add_thmss
    [((Binding.qualify true (Long_Name.base_name name) (Binding.name "equation"), result_thms),
      [Attrib.attribute_i thy Code.add_default_eqn_attrib])] thy))
    (arrange ((map (fn ((name, _), _) => name) pred_mode) ~~ result_thms)) thy'
    |> Theory.checkpoint
in
  thy''
end

(* generation of case rules from user-given introduction rules *)

fun mk_casesrule ctxt nparams introrules =
  let
    val intros = map (Logic.unvarify o prop_of) introrules
    val (pred, (params, args)) = strip_intro_concl nparams (hd intros)
    val ([propname], ctxt1) = Variable.variant_fixes ["thesis"] ctxt
    val prop = HOLogic.mk_Trueprop (Free (propname, HOLogic.boolT))
    val (argnames, ctxt2) = Variable.variant_fixes
      (map (fn i => "a" ^ string_of_int i) (1 upto (length args))) ctxt1
    val argvs = map2 (curry Free) argnames (map fastype_of args)
    fun mk_case intro = let
        val (_, (_, args)) = strip_intro_concl nparams intro
        val prems = Logic.strip_imp_prems intro
        val eqprems = map (HOLogic.mk_Trueprop o HOLogic.mk_eq) (argvs ~~ args)
        val frees = (fold o fold_aterms)
          (fn t as Free _ =>
              if member (op aconv) params t then I else insert (op aconv) t
           | _ => I) (args @ prems) []
        in fold Logic.all frees (Logic.list_implies (eqprems @ prems, prop)) end
    val assm = HOLogic.mk_Trueprop (list_comb (pred, params @ argvs))
    val cases = map mk_case intros
  in Logic.list_implies (assm :: cases, prop) end;

fun add_equations name thy =
  let
    val thy' = PredData.map (Graph.extend (dependencies_of thy) name) thy |> Theory.checkpoint;
    (*val preds = Graph.all_preds (PredData.get thy') [name] |> filter_out (has_elim thy') *)
    fun strong_conn_of gr keys =
      Graph.strong_conn (Graph.subgraph (member (op =) (Graph.all_succs gr keys)) gr)
    val scc = strong_conn_of (PredData.get thy') [name]
    val thy'' = fold_rev
      (fn preds => fn thy =>
        if forall (null o modes_of thy) preds then add_equations_of preds thy else thy)
      scc thy' |> Theory.checkpoint
  in thy'' end

  
fun attrib f = Thm.declaration_attribute (fn thm => Context.mapping (f thm) I);

val code_pred_intros_attrib = attrib add_intro;

(** user interface **)

local

(* TODO: make TheoryDataFun to GenericDataFun & remove duplication of local theory and theory *)
(* TODO: must create state to prove multiple cases *)
fun generic_code_pred prep_const raw_const lthy =
  let
  
    val thy = ProofContext.theory_of lthy
    val const = prep_const thy raw_const
    
    val lthy' = LocalTheory.theory (PredData.map (Graph.extend (dependencies_of thy) const)) lthy
      |> LocalTheory.checkpoint
    val thy' = ProofContext.theory_of lthy'
    val preds = Graph.all_preds (PredData.get thy') [const] |> filter_out (has_elim thy')
    
    fun mk_cases const =
      let
        val nparams = nparams_of thy' const
        val intros = intros_of thy' const
      in mk_casesrule lthy' nparams intros end  
    val cases_rules = map mk_cases preds
    val cases =
      map (fn case_rule => RuleCases.Case {fixes = [],
        assumes = [("", Logic.strip_imp_prems case_rule)],
        binds = [], cases = []}) cases_rules
    val case_env = map2 (fn p => fn c => (Long_Name.base_name p, SOME c)) preds cases
    val _ = Output.tracing (commas (map fst case_env))
    val lthy'' = ProofContext.add_cases true case_env lthy'
    
    fun after_qed thms =
      LocalTheory.theory (fold set_elim (map the_single thms) #> add_equations const)
  in
    Proof.theorem_i NONE after_qed (map (single o (rpair [])) cases_rules) lthy''
  end;

structure P = OuterParse

in

val code_pred = generic_code_pred (K I);
val code_pred_cmd = generic_code_pred Code.read_const

val setup = PredData.put (Graph.empty) #>
  Attrib.setup @{binding code_pred_intros} (Scan.succeed (attrib add_intro))
    "adding alternative introduction rules for code generation of inductive predicates"
(*  Attrib.setup @{binding code_ind_cases} (Scan.succeed add_elim_attrib)
    "adding alternative elimination rules for code generation of inductive predicates";
    *)
  (*FIXME name discrepancy in attribs and ML code*)
  (*FIXME intros should be better named intro*)
  (*FIXME why distinguished attribute for cases?*)

val _ = OuterSyntax.local_theory_to_proof "code_pred"
  "prove equations for predicate specified by intro/elim rules"
  OuterKeyword.thy_goal (P.term_group >> code_pred_cmd)

end

(*FIXME
- Naming of auxiliary rules necessary?
- add default code equations P x y z = P_i_i_i x y z
*)

(* transformation for code generation *)

val eval_ref = ref (NONE : (unit -> term Predicate.pred) option);

(*FIXME turn this into an LCF-guarded preprocessor for comprehensions*)
fun analyze_compr thy t_compr =
  let
    val split = case t_compr of (Const (@{const_name Collect}, _) $ t) => t
      | _ => error ("Not a set comprehension: " ^ Syntax.string_of_term_global thy t_compr);
    val (body, Ts, fp) = HOLogic.strip_splits split;
    val (pred as Const (name, T), all_args) = strip_comb body;
    val (params, args) = chop (nparams_of thy name) all_args;
    val user_mode = map_filter I (map_index
      (fn (i, t) => case t of Bound j => if j < length Ts then NONE
        else SOME (i+1) | _ => SOME (i+1)) args); (*FIXME dangling bounds should not occur*)
    val modes = filter (fn Mode (_, is, _) => is = user_mode)
      (modes_of_term (all_modes_of thy) (list_comb (pred, params)));
    val m = case modes
     of [] => error ("No mode possible for comprehension "
                ^ Syntax.string_of_term_global thy t_compr)
      | [m] => m
      | m :: _ :: _ => (warning ("Multiple modes possible for comprehension "
                ^ Syntax.string_of_term_global thy t_compr); m);
    val (inargs, outargs) = get_args user_mode args;
    val t_pred = list_comb (compile_expr thy (all_modes_of thy) (SOME m, list_comb (pred, params)),
      inargs);
    val t_eval = if null outargs then t_pred else let
        val outargs_bounds = map (fn Bound i => i) outargs;
        val outargsTs = map (nth Ts) outargs_bounds;
        val T_pred = mk_tupleT outargsTs;
        val T_compr = HOLogic.mk_tupleT fp Ts;
        val arrange_bounds = map_index I outargs_bounds
          |> sort (prod_ord (K EQUAL) int_ord)
          |> map fst;
        val arrange = funpow (length outargs_bounds - 1) HOLogic.mk_split
          (Term.list_abs (map (pair "") outargsTs,
            HOLogic.mk_tuple fp T_compr (map Bound arrange_bounds)))
      in mk_pred_map T_pred T_compr arrange t_pred end
  in t_eval end;

fun eval thy t_compr =
  let
    val t = analyze_compr thy t_compr;
    val T = dest_pred_enumT (fastype_of t);
    val t' = mk_pred_map T HOLogic.termT (HOLogic.term_of_const T) t;
  in (T, Code_ML.eval NONE ("Predicate_Compile.eval_ref", eval_ref) Predicate.map thy t' []) end;

fun values ctxt k t_compr =
  let
    val thy = ProofContext.theory_of ctxt;
    val (T, t) = eval thy t_compr;
    val setT = HOLogic.mk_setT T;
    val (ts, _) = Predicate.yieldn k t;
    val elemsT = HOLogic.mk_set T ts;
  in if k = ~1 orelse length ts < k then elemsT
    else Const (@{const_name Set.union}, setT --> setT --> setT) $ elemsT $ t_compr
  end;

fun values_cmd modes k raw_t state =
  let
    val ctxt = Toplevel.context_of state;
    val t = Syntax.read_term ctxt raw_t;
    val t' = values ctxt k t;
    val ty' = Term.type_of t';
    val ctxt' = Variable.auto_fixes t' ctxt;
    val p = PrintMode.with_modes modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
  in Pretty.writeln p end;

local structure P = OuterParse in

val opt_modes = Scan.optional (P.$$$ "(" |-- P.!!! (Scan.repeat1 P.xname --| P.$$$ ")")) [];

val _ = OuterSyntax.improper_command "values" "enumerate and print comprehensions" OuterKeyword.diag
  (opt_modes -- Scan.optional P.nat ~1 -- P.term
    >> (fn ((modes, k), t) => Toplevel.no_timing o Toplevel.keep
        (values_cmd modes k t)));

end;

end;

