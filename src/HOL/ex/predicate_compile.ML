(* Author: Lukas Bulwahn, TU Muenchen

(Prototype of) A compiler from predicates specified by intro/elim rules
to equations.
*)

signature PREDICATE_COMPILE =
sig
  type mode = int list option list * int list
  val prove_equation: string -> mode option -> theory -> theory
  val intro_rule: theory -> string -> mode -> thm
  val elim_rule: theory -> string -> mode -> thm
  val strip_intro_concl: term -> int -> term * (term list * term list)
  val modename_of: theory -> string -> mode -> string
  val modes_of: theory -> string -> mode list
  val pred_intros: theory -> string -> thm list
  val get_nparams: theory -> string -> int
  val setup: theory -> theory
  val code_pred: string -> Proof.context -> Proof.state
  val code_pred_cmd: string -> Proof.context -> Proof.state
  val print_alternative_rules: theory -> theory (*FIXME diagnostic command?*)
  val do_proofs: bool ref
  val analyze_compr: theory -> term -> term
  val eval_ref: (unit -> term Predicate.pred) option ref
end;

structure Predicate_Compile : PREDICATE_COMPILE =
struct

(** auxiliary **)

(* debug stuff *)

fun makestring _ = "?";   (* FIXME dummy *)

fun tracing s = (if ! Toplevel.debug then Output.tracing s else ());

fun print_tac s = (if ! Toplevel.debug then Tactical.print_tac s else Seq.single);
fun debug_tac msg = (fn st => (tracing msg; Seq.single st));

val do_proofs = ref true;


(** fundamentals **)

(* syntactic operations *)

fun mk_eq (x, xs) =
  let fun mk_eqs _ [] = []
        | mk_eqs a (b::cs) =
            HOLogic.mk_eq (Free (a, fastype_of b), b) :: mk_eqs a cs
  in mk_eqs x xs end;

fun mk_tupleT [] = HOLogic.unitT
  | mk_tupleT Ts = foldr1 HOLogic.mk_prodT Ts;

fun mk_tuple [] = HOLogic.unit
  | mk_tuple ts = foldr1 HOLogic.mk_prod ts;

fun dest_tuple (Const (@{const_name Product_Type.Unity}, _)) = []
  | dest_tuple (Const (@{const_name Pair}, _) $ t1 $ t2) = t1 :: (dest_tuple t2)
  | dest_tuple t = [t]

fun mk_pred_enumT T = Type ("Predicate.pred", [T])

fun dest_pred_enumT (Type ("Predicate.pred", [T])) = T
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


(* data structures *)

type mode = int list option list * int list;

val mode_ord = prod_ord (list_ord (option_ord (list_ord int_ord))) (list_ord int_ord);

structure PredModetab = TableFun(
  type key = string * mode
  val ord = prod_ord fast_string_ord mode_ord
);


(*FIXME scrap boilerplate*)

structure IndCodegenData = TheoryDataFun
(
  type T = {names : string PredModetab.table,
            modes : mode list Symtab.table,
            function_defs : Thm.thm Symtab.table,
            function_intros : Thm.thm Symtab.table,
            function_elims : Thm.thm Symtab.table,
            intro_rules : Thm.thm list Symtab.table,
            elim_rules : Thm.thm Symtab.table,
            nparams : int Symtab.table
           }; (*FIXME: better group tables according to key*)
      (* names: map from inductive predicate and mode to function name (string).
         modes: map from inductive predicates to modes
         function_defs: map from function name to definition
         function_intros: map from function name to intro rule
         function_elims: map from function name to elim rule
         intro_rules: map from inductive predicate to alternative intro rules
         elim_rules: map from inductive predicate to alternative elimination rule
         nparams: map from const name to number of parameters (* assuming there exist intro and elimination rules *) 
       *)
  val empty = {names = PredModetab.empty,
               modes = Symtab.empty,
               function_defs = Symtab.empty,
               function_intros = Symtab.empty,
               function_elims = Symtab.empty,
               intro_rules = Symtab.empty,
               elim_rules = Symtab.empty,
               nparams = Symtab.empty};
  val copy = I;
  val extend = I;
  fun merge _ (r : T * T) = {names = PredModetab.merge (op =) (pairself #names r),
                   modes = Symtab.merge (op =) (pairself #modes r),
                   function_defs = Symtab.merge Thm.eq_thm (pairself #function_defs r),
                   function_intros = Symtab.merge Thm.eq_thm (pairself #function_intros r),
                   function_elims = Symtab.merge Thm.eq_thm (pairself #function_elims r),
                   intro_rules = Symtab.merge ((forall Thm.eq_thm) o (op ~~)) (pairself #intro_rules r),
                   elim_rules = Symtab.merge Thm.eq_thm (pairself #elim_rules r),
                   nparams = Symtab.merge (op =) (pairself #nparams r)};
);

  fun map_names f thy = IndCodegenData.map
    (fn x => {names = f (#names x), modes = #modes x, function_defs = #function_defs x,
            function_intros = #function_intros x, function_elims = #function_elims x,
            intro_rules = #intro_rules x, elim_rules = #elim_rules x,
            nparams = #nparams x}) thy

  fun map_modes f thy = IndCodegenData.map
    (fn x => {names = #names x, modes = f (#modes x), function_defs = #function_defs x,
            function_intros = #function_intros x, function_elims = #function_elims x,
            intro_rules = #intro_rules x, elim_rules = #elim_rules x,
            nparams = #nparams x}) thy

  fun map_function_defs f thy = IndCodegenData.map
    (fn x => {names = #names x, modes = #modes x, function_defs = f (#function_defs x),
            function_intros = #function_intros x, function_elims = #function_elims x,
            intro_rules = #intro_rules x, elim_rules = #elim_rules x,
            nparams = #nparams x}) thy 
  
  fun map_function_elims f thy = IndCodegenData.map
    (fn x => {names = #names x, modes = #modes x, function_defs = #function_defs x,
            function_intros = #function_intros x, function_elims = f (#function_elims x),
            intro_rules = #intro_rules x, elim_rules = #elim_rules x,
            nparams = #nparams x}) thy

  fun map_function_intros f thy = IndCodegenData.map
    (fn x => {names = #names x, modes = #modes x, function_defs = #function_defs x,
            function_intros = f (#function_intros x), function_elims = #function_elims x,
            intro_rules = #intro_rules x, elim_rules = #elim_rules x,
            nparams = #nparams x}) thy

  fun map_intro_rules f thy = IndCodegenData.map
    (fn x => {names = #names x, modes = #modes x, function_defs = #function_defs x,
            function_intros = #function_intros x, function_elims = #function_elims x,
            intro_rules = f (#intro_rules x), elim_rules = #elim_rules x,
            nparams = #nparams x}) thy 
  
  fun map_elim_rules f thy = IndCodegenData.map
    (fn x => {names = #names x, modes = #modes x, function_defs = #function_defs x,
            function_intros = #function_intros x, function_elims = #function_elims x,
            intro_rules = #intro_rules x, elim_rules = f (#elim_rules x),
            nparams = #nparams x}) thy

  fun map_nparams f thy = IndCodegenData.map
    (fn x => {names = #names x, modes = #modes x, function_defs = #function_defs x,
            function_intros = #function_intros x, function_elims = #function_elims x,
            intro_rules = #intro_rules x, elim_rules = #elim_rules x,
            nparams = f (#nparams x)}) thy

(* removes first subgoal *)
fun mycheat_tac thy i st =
  (Tactic.rtac (SkipProof.make_thm thy (Var (("A", 0), propT))) i) st

(* Lightweight mode analysis **********************************************)

(**************************************************************************)
(* source code from old code generator ************************************)

(**** check if a term contains only constructor functions ****)

fun is_constrt thy =
  let
    val cnstrs = flat (maps
      (map (fn (_, (Tname, _, cs)) => map (apsnd (rpair Tname o length)) cs) o #descr o snd)
      (Symtab.dest (DatatypePackage.get_datatypes thy)));
    fun check t = (case strip_comb t of
        (Free _, []) => true
      | (Const (s, T), ts) => (case (AList.lookup (op =) cnstrs s, body_type T) of
            (SOME (i, Tname), Type (Tname', _)) => length ts = i andalso Tname = Tname' andalso forall check ts
          | _ => false)
      | _ => false)
  in check end;

(**** check if a type is an equality type (i.e. doesn't contain fun)
  FIXME this is only an approximation ****)

fun is_eqT (Type (s, Ts)) = s <> "fun" andalso forall is_eqT Ts
  | is_eqT _ = true;

(**** mode inference ****)

fun string_of_mode (iss, is) = space_implode " -> " (map
  (fn NONE => "X"
    | SOME js => enclose "[" "]" (commas (map string_of_int js)))
       (iss @ [SOME is]));

fun print_modes modes = tracing ("Inferred modes:\n" ^
  cat_lines (map (fn (s, ms) => s ^ ": " ^ commas (map
    string_of_mode ms)) modes));

fun term_vs tm = fold_aterms (fn Free (x, T) => cons x | _ => I) tm [];
val terms_vs = distinct (op =) o maps term_vs;

(** collect all Frees in a term (with duplicates!) **)
fun term_vTs tm =
  fold_aterms (fn Free xT => cons xT | _ => I) tm [];

fun get_args is ts = let
  fun get_args' _ _ [] = ([], [])
    | get_args' is i (t::ts) = (if i mem is then apfst else apsnd) (cons t)
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

fun cprod ([], ys) = []
  | cprod (x :: xs, ys) = map (pair x) ys @ cprod (xs, ys);

fun cprods xss = foldr (map op :: o cprod) [[]] xss;

datatype hmode = Mode of mode * int list * hmode option list; (*FIXME don't understand
  why there is another mode type!?*)

fun modes_of_term modes t =
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


(*****************************************************************************************)
(**** end of old source code *************************************************************)
(*****************************************************************************************)
(**** term construction ****)

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
      NONE => ((names, (s, [])::vs), Free (s, T))
    | SOME xs =>
        let
          val s' = Name.variant names s;
          val v = Free (s', T)
        in
          ((s'::names, AList.update (op =) (s, v::xs) vs), v)
        end);

fun distinct_v (nvs, Free (s, T)) = mk_v nvs s T
  | distinct_v (nvs, t $ u) =
      let
        val (nvs', t') = distinct_v (nvs, t);
        val (nvs'', u') = distinct_v (nvs', u);
      in (nvs'', t' $ u') end
  | distinct_v x = x;

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
    lambda v (fst (DatatypePackage.make_case
      (ProofContext.init thy) false [] v
      [(mk_tuple out_ts,
        if null eqs'' then success_t
        else Const (@{const_name HOL.If}, HOLogic.boolT --> U --> U --> U) $
          foldr1 HOLogic.mk_conj eqs'' $ success_t $
            mk_empty U'),
       (v', mk_empty U')]))
  end;

fun modename_of thy name mode = let
    val v = (PredModetab.lookup (#names (IndCodegenData.get thy)) (name, mode))
  in if (is_some v) then the v (*FIXME use case here*)
     else error ("fun modename_of - definition not found: name: " ^ name ^ " mode: " ^  (makestring mode))
  end

fun modes_of thy =
  these o Symtab.lookup ((#modes o IndCodegenData.get) thy);

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

fun compile_param thy modes (NONE, t) = t
  | compile_param thy modes (m as SOME (Mode ((iss, is'), is, ms)), t) = let
    val (f, args) = strip_comb t
    val (params, args') = chop (length ms) args
    val params' = map (compile_param thy modes) (ms ~~ params)
    val f' = case f of
        Const (name, T) =>
          if AList.defined op = modes name then
            Const (modename_of thy name (iss, is'), funT'_of (iss, is') T)
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
               val mode_id = modename_of thy name mode
             in list_comb (Const (mode_id, ((map fastype_of params') @ Ts) --->
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
    fun check_constrt ((names, eqs), t) =
      if is_constrt thy t then ((names, eqs), t) else
        let
          val s = Name.variant names "x";
          val v = Free (s, fastype_of t)
        in ((s::names, HOLogic.mk_eq (v, t)::eqs), v) end;

    val (in_ts, out_ts) = get_args is ts;
    val ((all_vs', eqs), in_ts') =
      (*FIXME*) Library.foldl_map check_constrt ((all_vs, []), in_ts);

    fun compile_prems out_ts' vs names [] =
          let
            val ((names', eqs'), out_ts'') =
              (*FIXME*) Library.foldl_map check_constrt ((names, []), out_ts');
            val (nvs, out_ts''') = (*FIXME*) Library.foldl_map distinct_v
              ((names', map (rpair []) vs), out_ts'');
          in
            compile_match thy (snd nvs) (eqs @ eqs') out_ts'''
              (mk_single (mk_tuple out_ts))
          end
      | compile_prems out_ts vs names ps =
          let
            val vs' = distinct (op =) (flat (vs :: map term_vs out_ts));
            val SOME (p, mode as SOME (Mode (_, js, _))) =
              select_mode_prem thy modes' vs' ps
            val ps' = filter_out (equal p) ps
            val ((names', eqs), out_ts') =
              (*FIXME*) Library.foldl_map check_constrt ((names, []), out_ts)
            val (nvs, out_ts'') = (*FIXME*) Library.foldl_map distinct_v
              ((names', map (rpair []) vs), out_ts')
            val (compiled_clause, rest) = case p of
               Prem (us, t) =>
                 let
                   val (in_ts, out_ts''') = get_args js us;
                   val u = list_comb (compile_expr thy modes (mode, t), in_ts)
                   val rest = compile_prems out_ts''' vs' (fst nvs) ps'
                 in
                   (u, rest)
                 end
             | Negprem (us, t) =>
                 let
                   val (in_ts, out_ts''') = get_args js us
                   val u = list_comb (compile_expr thy modes (mode, t), in_ts)
                   val rest = compile_prems out_ts''' vs' (fst nvs) ps'
                 in
                   (mk_not_pred u, rest)
                 end
             | Sidecond t =>
                 let
                   val rest = compile_prems [] vs' (fst nvs) ps';
                 in
                   (mk_if_predenum t, rest)
                 end
          in
            compile_match thy (snd nvs) eqs out_ts'' 
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
    val mode_id = modename_of thy s mode
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

(* end of term construction ******************************************************)

(* special setup for simpset *)                  
val HOL_basic_ss' = HOL_basic_ss setSolver 
  (mk_solver "all_tac_solver" (fn _ => fn _ => all_tac))


(* misc: constructing and proving tupleE rules ***********************************)


(* Creating definitions of functional programs 
   and proving intro and elim rules **********************************************) 

fun is_ind_pred thy c = 
  (can (InductivePackage.the_inductive (ProofContext.init thy)) c) orelse
  (c mem_string (Symtab.keys (#intro_rules (IndCodegenData.get thy))))

fun get_name_of_ind_calls_of_clauses thy preds intrs =
    fold Term.add_consts intrs [] |> map fst
    |> filter_out (member (op =) preds) |> filter (is_ind_pred thy)

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

fun create_intro_rule nparams mode defthm mode_id funT pred thy =
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
  val (params', names) = fold_map mk_Eval_of ((params ~~ Ts1) ~~ (fst mode)) []
  val predprop = HOLogic.mk_Trueprop (list_comb (pred, params' @ io_args))
  val funargs = params @ inargs
  val funpropE = HOLogic.mk_Trueprop (mk_Eval (list_comb (funtrm, funargs),
                  if null outargs then Free("y", HOLogic.unitT) else mk_tuple outargs))
  val funpropI = HOLogic.mk_Trueprop (mk_Eval (list_comb (funtrm, funargs),
                   mk_tuple outargs))
  val introtrm = Logic.mk_implies (predprop, funpropI)
  val simprules = [defthm, @{thm eval_pred},
                   @{thm "split_beta"}, @{thm "fst_conv"}, @{thm "snd_conv"}]
  val unfolddef_tac = (Simplifier.asm_full_simp_tac (HOL_basic_ss addsimps simprules) 1)
  val introthm = Goal.prove (ProofContext.init thy) (argnames @ ["y"]) [] introtrm (fn {...} => unfolddef_tac)
  val P = HOLogic.mk_Trueprop (Free ("P", HOLogic.boolT));
  val elimtrm = Logic.list_implies ([funpropE, Logic.mk_implies (predprop, P)], P)
  val elimthm = Goal.prove (ProofContext.init thy) (argnames @ ["y", "P"]) [] elimtrm (fn {...} => unfolddef_tac)
in
  map_function_intros (Symtab.update_new (mode_id, introthm)) thy
  |> map_function_elims (Symtab.update_new (mode_id, elimthm))
  |> PureThy.store_thm (Binding.name (Long_Name.base_name mode_id ^ "I"), introthm) |> snd
  |> PureThy.store_thm (Binding.name (Long_Name.base_name mode_id ^ "E"), elimthm)  |> snd
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
      val ([defthm], thy') = thy |>
        Sign.add_consts_i [(Binding.name (Long_Name.base_name mode_id), funT, NoSyn)] |>
        PureThy.add_defs false [((Binding.name (Long_Name.base_name mode_id ^ "_def"), def), [])]
      in thy' |> map_names (PredModetab.update_new ((name, mode), mode_id))
           |> map_function_defs (Symtab.update_new (mode_id, defthm))
           |> create_intro_rule nparams mode defthm mode_id funT (Const (name, T))
      end;
  in
    fold create_definition modes thy
  end;

(**************************************************************************************)
(* Proving equivalence of term *)


fun intro_rule thy pred mode = modename_of thy pred mode
    |> Symtab.lookup (#function_intros (IndCodegenData.get thy)) |> the

fun elim_rule thy pred mode = modename_of thy pred mode
    |> Symtab.lookup (#function_elims (IndCodegenData.get thy)) |> the

fun pred_intros thy predname = let
    fun is_intro_of pred intro = let
      val const = fst (strip_comb (HOLogic.dest_Trueprop (concl_of intro)))
    in (fst (dest_Const const) = pred) end;
    val d = IndCodegenData.get thy
  in
    if (Symtab.defined (#intro_rules d) predname) then
      rev (Symtab.lookup_list (#intro_rules d) predname)
    else
      InductivePackage.the_inductive (ProofContext.init thy) predname
      |> snd |> #intrs |> filter (is_intro_of predname)
  end

fun function_definition thy pred mode =
  modename_of thy pred mode |> Symtab.lookup (#function_defs (IndCodegenData.get thy)) |> the

fun is_Type (Type _) = true
  | is_Type _ = false

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


(* returns true if t is an application of an datatype constructor *)
(* which then consequently would be splitted *)
(* else false *)
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

(* MAJOR FIXME:  prove_params should be simple
 - different form of introrule for parameters ? *)
fun prove_param thy modes (NONE, t) = all_tac 
  | prove_param thy modes (m as SOME (Mode (mode, is, ms)), t) = let
    val  (f, args) = strip_comb t
    val (params, _) = chop (length ms) args
    val f_tac = case f of
        Const (name, T) => simp_tac (HOL_basic_ss addsimps 
           @{thm eval_pred}::function_definition thy name mode::[]) 1
      | Free _ => all_tac
  in  
    print_tac "before simplification in prove_args:"
    THEN debug_tac ("mode" ^ (makestring mode))
    THEN f_tac
    THEN print_tac "after simplification in prove_args"
    (* work with parameter arguments *)
    THEN (EVERY (map (prove_param thy modes) (ms ~~ params)))
    THEN (REPEAT_DETERM (atac 1))
  end

fun prove_expr thy modes (SOME (Mode (mode, is, ms)), t, us) (premposition : int) =
  (case strip_comb t of
    (Const (name, T), args) =>
      if AList.defined op = modes name then (let
          val introrule = intro_rule thy name mode
          (*val (in_args, out_args) = get_args is us
          val (pred, rargs) = strip_comb (HOLogic.dest_Trueprop
            (hd (Logic.strip_imp_prems (prop_of introrule))))
          val nparams = length ms (* get_nparams thy (fst (dest_Const pred)) *)
          val (_, args) = chop nparams rargs
          val _ = tracing ("args: " ^ (makestring args))
          val subst = map (pairself (cterm_of thy)) (args ~~ us)
          val _ = tracing ("subst: " ^ (makestring subst))
          val inst_introrule = Drule.cterm_instantiate subst introrule*)
         (* the next line is old and probably wrong *)
          val (args1, args2) = chop (length ms) args
          val _ = tracing ("premposition: " ^ (makestring premposition))
        in
        rtac @{thm bindI} 1
        THEN print_tac "before intro rule:"
        THEN debug_tac ("mode" ^ (makestring mode))
        THEN debug_tac (makestring introrule)
        THEN debug_tac ("premposition: " ^ (makestring premposition))
        (* for the right assumption in first position *)
        THEN rotate_tac premposition 1
        THEN rtac introrule 1
        THEN print_tac "after intro rule"
        (* work with parameter arguments *)
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
      val case_rewrites = (#case_rewrites (DatatypePackage.the_datatype thy
        ((fst o dest_Type o fastype_of) t)))
      in case_rewrites @ (flat (map get_case_rewrite (snd (strip_comb t)))) end
    else []
  val simprules = @{thm "unit.cases"} :: @{thm "prod.cases"} :: (flat (map get_case_rewrite out_ts))
(* replace TRY by determining if it necessary - are there equations when calling compile match? *)
in
  print_tac ("before prove_match rewriting: simprules = " ^ (makestring simprules))
   (* make this simpset better! *)
  THEN asm_simp_tac (HOL_basic_ss' addsimps simprules) 1
  THEN print_tac "after prove_match:"
  THEN (DETERM (TRY (EqSubst.eqsubst_tac (ProofContext.init thy) [0] [@{thm "HOL.if_P"}] 1
         THEN (REPEAT_DETERM (rtac @{thm conjI} 1 THEN (SOLVED (asm_simp_tac HOL_basic_ss 1))))
         THEN (SOLVED (asm_simp_tac HOL_basic_ss 1)))))
  THEN print_tac "after if simplification"
end;

(* corresponds to compile_fun -- maybe call that also compile_sidecond? *)

fun prove_sidecond thy modes t = let
  val _ = tracing ("prove_sidecond:" ^ (makestring t))
  fun preds_of t nameTs = case strip_comb t of 
    (f as Const (name, T), args) =>
      if AList.defined (op =) modes name then (name, T) :: nameTs
        else fold preds_of args nameTs
    | _ => nameTs
  val preds = preds_of t []
  
  val _ = tracing ("preds: " ^ (makestring preds))
  val defs = map
    (fn (pred, T) => function_definition thy pred ([], (1 upto (length (binder_types T)))))
      preds
  val _ = tracing ("defs: " ^ (makestring defs))
in 
   (* remove not_False_eq_True when simpset in prove_match is better *)
   simp_tac (HOL_basic_ss addsimps @{thm not_False_eq_True} :: @{thm eval_pred} :: defs) 1 
   (* need better control here! *)
   THEN print_tac "after sidecond simplification"
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
            print_tac "before negated clause:"
            THEN rtac @{thm bindI} 1
            THEN (if (is_some name) then
                simp_tac (HOL_basic_ss addsimps [function_definition thy (the name) (iss, js)]) 1
                THEN rtac @{thm not_predI} 1
                THEN print_tac "after neg. intro rule"
                THEN print_tac ("t = " ^ (makestring t))
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

(* FIXME: This function relies on the derivation of an induction rule *)
fun get_nparams thy s = let
    val _ = tracing ("get_nparams: " ^ s)
  in
  if Symtab.defined (#nparams (IndCodegenData.get thy)) s then
    the (Symtab.lookup (#nparams (IndCodegenData.get thy)) s) 
  else
    case try (InductivePackage.the_inductive (ProofContext.init thy)) s of
      SOME info => info |> snd |> #raw_induct |> Thm.unvarify
        |> InductivePackage.params_of |> length
    | NONE => 0 (* default value *)
  end

val ind_set_codegen_preproc = InductiveSetPackage.codegen_preproc;

fun pred_elim thy predname =
  if (Symtab.defined (#elim_rules (IndCodegenData.get thy)) predname) then
    the (Symtab.lookup (#elim_rules (IndCodegenData.get thy)) predname)
  else
    (let
      val ind_result = InductivePackage.the_inductive (ProofContext.init thy) predname
      val index = find_index (fn s => s = predname) (#names (fst ind_result))
    in nth (#elims (snd ind_result)) index end)

fun prove_one_direction thy all_vs param_vs modes clauses ((pred, T), mode) = let
  val elim_rule = the (Symtab.lookup (#function_elims (IndCodegenData.get thy)) (modename_of thy pred mode))
(*  val ind_result = InductivePackage.the_inductive (ProofContext.init thy) pred
  val index = find_index (fn s => s = pred) (#names (fst ind_result))
  val (_, T) = dest_Const (nth (#preds (snd ind_result)) index) *)
  val nargs = length (binder_types T) - get_nparams thy pred
  val pred_case_rule = singleton (ind_set_codegen_preproc thy)
    (preprocess_elim thy nargs (pred_elim thy pred))
  (* FIXME preprocessor |> Simplifier.full_simplify (HOL_basic_ss addsimps [@ {thm Predicate.memb_code}])*)
  val _ = tracing ("pred_case_rule " ^ (makestring pred_case_rule))
in
  REPEAT_DETERM (CHANGED (rewtac @{thm "split_paired_all"}))
  THEN etac elim_rule 1
  THEN etac pred_case_rule 1
  THEN (EVERY (map
         (fn i => EVERY' (select_sup (length clauses) i) i) 
           (1 upto (length clauses))))
  THEN (EVERY (map (prove_clause thy nargs all_vs param_vs modes mode) clauses))
end;

(*******************************************************************************************************)
(* Proof in the other direction ************************************************************************)
(*******************************************************************************************************)

fun prove_match2 thy out_ts = let
  fun split_term_tac (Free _) = all_tac
    | split_term_tac t =
      if (is_constructor thy t) then let
        val info = DatatypePackage.the_datatype thy ((fst o dest_Type o fastype_of) t)
        val num_of_constrs = length (#case_rewrites info)
        (* special treatment of pairs -- because of fishing *)
        val split_rules = case (fst o dest_Type o fastype_of) t of
          "*" => [@{thm prod.split_asm}] 
          | _ => PureThy.get_thms thy (((fst o dest_Type o fastype_of) t) ^ ".split_asm")
        val (_, ts) = strip_comb t
      in
        print_tac ("splitting with t = " ^ (makestring t))
        THEN (Splitter.split_asm_tac split_rules 1)
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
           @{thm eval_pred}::function_definition thy name mode::[]) 1
      | Free _ => all_tac
  in  
    print_tac "before simplification in prove_args:"
    THEN debug_tac ("function : " ^ (makestring f) ^ " - mode" ^ (makestring mode))
    THEN f_tac
    THEN print_tac "after simplification in prove_args"
    (* work with parameter arguments *)
    THEN (EVERY (map (prove_param2 thy modes) (ms ~~ params)))
  end

fun prove_expr2 thy modes (SOME (Mode (mode, is, ms)), t) = 
  (case strip_comb t of
    (Const (name, T), args) =>
      if AList.defined op = modes name then
        etac @{thm bindE} 1
        THEN (REPEAT_DETERM (CHANGED (rewtac @{thm "split_paired_all"})))
        THEN (etac (elim_rule thy name mode) 1)
        THEN (EVERY (map (prove_param2 thy modes) (ms ~~ args)))
      else error "Prove expr2 if case not implemented"
    | _ => etac @{thm bindE} 1)
  | prove_expr2 _ _ _ = error "Prove expr2 not implemented"

fun prove_sidecond2 thy modes t = let
  val _ = tracing ("prove_sidecond:" ^ (makestring t))
  fun preds_of t nameTs = case strip_comb t of 
    (f as Const (name, T), args) =>
      if AList.defined (op =) modes name then (name, T) :: nameTs
        else fold preds_of args nameTs
    | _ => nameTs
  val preds = preds_of t []
  val _ = tracing ("preds: " ^ (makestring preds))
  val defs = map
    (fn (pred, T) => function_definition thy pred ([], (1 upto (length (binder_types T)))))
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
  val pred_intro_rule = nth (pred_intros thy pred) (i - 1)
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
                full_simp_tac (HOL_basic_ss addsimps [function_definition thy (the name) (iss, js)]) 1 
                THEN etac @{thm not_predE} 1
                THEN (EVERY (map (prove_param2 thy modes) (param_modes ~~ params)))
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
  print_tac "starting prove_clause2"
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
   THEN (rtac (intro_rule thy pred mode) 1)
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

(* look for other place where this functionality was used before *)
fun strip_intro_concl intro nparams = let
  val _ $ u = Logic.strip_imp_concl intro
  val (pred, all_args) = strip_comb u
  val (params, args) = chop nparams all_args
in (pred, (params, args)) end

(* setup for alternative introduction and elimination rules *)

fun add_intro_thm thm thy = let
   val (pred, _) = dest_Const (fst (strip_intro_concl (prop_of thm) 0))
 in map_intro_rules (Symtab.insert_list Thm.eq_thm (pred, thm)) thy end

fun add_elim_thm thm thy = let
    val (pred, _) = dest_Const (fst 
      (strip_comb (HOLogic.dest_Trueprop (hd (prems_of thm)))))
  in map_elim_rules (Symtab.update (pred, thm)) thy end


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
  val intro_thm = Goal.prove (ProofContext.init thy) names [] intro_t
        (fn {...} => etac @{thm FalseE} 1)
  val elim_thm = Goal.prove (ProofContext.init thy) ("P" :: names) [] elim_t
        (fn {...} => etac (pred_elim thy predname) 1) 
in
  add_intro_thm intro_thm thy
  |> add_elim_thm elim_thm
end

(*************************************************************************************)
(* main function *********************************************************************)
(*************************************************************************************)

fun prove_equation ind_name mode thy =
let
  val _ = tracing ("starting prove_equation' with " ^ ind_name)
  val (prednames, preds) = 
    case (try (InductivePackage.the_inductive (ProofContext.init thy)) ind_name) of
      SOME info => let val preds = info |> snd |> #preds
        in (map (fst o dest_Const) preds, map ((apsnd Logic.unvarifyT) o dest_Const) preds) end
    | NONE => let
        val pred = Symtab.lookup (#intro_rules (IndCodegenData.get thy)) ind_name
          |> the |> hd |> prop_of
          |> Logic.strip_imp_concl |> HOLogic.dest_Trueprop |> strip_comb
          |> fst |>  dest_Const |> apsnd Logic.unvarifyT
       in ([ind_name], [pred]) end
  val thy' = fold (fn pred as (predname, T) => fn thy =>
    if null (pred_intros thy predname) then noclause pred thy else thy) preds thy
  val intrs = map (preprocess_intro thy') (maps (pred_intros thy') prednames)
    |> ind_set_codegen_preproc thy' (*FIXME preprocessor
    |> map (Simplifier.full_simplify (HOL_basic_ss addsimps [@ {thm Predicate.memb_code}]))*)
    |> map (Logic.unvarify o prop_of)
  val _ = tracing ("preprocessed intro rules:" ^ (makestring (map (cterm_of thy') intrs)))
  val name_of_calls = get_name_of_ind_calls_of_clauses thy' prednames intrs 
  val _ = tracing ("calling preds: " ^ makestring name_of_calls)
  val _ = tracing "starting recursive compilations"
  fun rec_call name thy = 
    (*FIXME use member instead of infix mem*)
    if not (name mem (Symtab.keys (#modes (IndCodegenData.get thy)))) then
      prove_equation name NONE thy else thy
  val thy'' = fold rec_call name_of_calls thy'
  val _ = tracing "returning from recursive calls"
  val _ = tracing "starting mode inference"
  val extra_modes = Symtab.dest (#modes (IndCodegenData.get thy''))
  val nparams = get_nparams thy'' ind_name
  val _ $ u = Logic.strip_imp_concl (hd intrs);
  val params = List.take (snd (strip_comb u), nparams);
  val param_vs = maps term_vs params
  val all_vs = terms_vs intrs
  fun dest_prem t =
      (case strip_comb t of
        (v as Free _, ts) => if v mem params then Prem (ts, v) else Sidecond t
      | (c as Const (@{const_name Not}, _), [t]) => (case dest_prem t of
          Prem (ts, t) => Negprem (ts, t)
        | Negprem _ => error ("Double negation not allowed in premise: " ^ (makestring (c $ t))) 
        | Sidecond t => Sidecond (c $ t))
      | (c as Const (s, _), ts) =>
        if is_ind_pred thy'' s then
          let val (ts1, ts2) = chop (get_nparams thy'' s) ts
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
  val modes = infer_modes thy'' extra_modes arities param_vs clauses
  val _ = print_arities arities;
  val _ = print_modes modes;
  val modes = if (is_some mode) then AList.update (op =) (ind_name, [the mode]) modes else modes
  val _ = print_modes modes
  val thy''' = fold (create_definitions preds nparams) modes thy''
    |> map_modes (fold Symtab.update_new modes)
  val clauses' = map (fn (s, cls) => (s, (the (AList.lookup (op =) preds s), cls))) clauses
  val _ = tracing "compiling predicates..."
  val ts = compile_preds thy''' all_vs param_vs (extra_modes @ modes) clauses'
  val _ = tracing "returned term from compile_preds"
  val pred_mode = maps (fn (s, (T, _)) => map (pair (s, T)) ((the o AList.lookup (op =) modes) s)) clauses'
  val _ = tracing "starting proof"
  val result_thms = prove_preds thy''' all_vs param_vs (extra_modes @ modes) clauses (pred_mode ~~ (flat ts))
  val (_, thy'''') = yield_singleton PureThy.add_thmss
    ((Binding.qualify true (Long_Name.base_name ind_name) (Binding.name "equation"), result_thms),
      [Attrib.attribute_i thy''' Code.add_default_eqn_attrib]) thy'''
in
  thy''''
end

fun set_nparams (pred, nparams) thy = map_nparams (Symtab.update (pred, nparams)) thy

fun print_alternative_rules thy = let
    val d = IndCodegenData.get thy
    val preds = (Symtab.keys (#intro_rules d)) union (Symtab.keys (#elim_rules d))
    val _ = tracing ("preds: " ^ (makestring preds))
    fun print pred = let
      val _ = tracing ("predicate: " ^ pred)
      val _ = tracing ("introrules: ")
      val _ = fold (fn thm => fn u => tracing (makestring thm))
        (rev (Symtab.lookup_list (#intro_rules d) pred)) ()
      val _ = tracing ("casesrule: ")
      val _ = tracing (makestring (Symtab.lookup (#elim_rules d) pred))
    in () end
    val _ = map print preds
 in thy end; 


(* generation of case rules from user-given introduction rules *)

fun mk_casesrule introrules nparams ctxt =
  let
    val intros = map prop_of introrules
    val (pred, (params, args)) = strip_intro_concl (hd intros) nparams
    val ([propname], ctxt1) = Variable.variant_fixes ["thesis"] ctxt
    val prop = HOLogic.mk_Trueprop (Free (propname, HOLogic.boolT))
    val (argnames, ctxt2) = Variable.variant_fixes
      (map (fn i => "a" ^ string_of_int i) (1 upto (length args))) ctxt1
    val argvs = map Free (argnames ~~ (map fastype_of args))
      (*FIXME map2*)
    fun mk_case intro = let
        val (_, (_, args)) = strip_intro_concl intro nparams
        val prems = Logic.strip_imp_prems intro
        val eqprems = map (HOLogic.mk_Trueprop o HOLogic.mk_eq) (argvs ~~ args)
        val frees = (fold o fold_aterms)
          (fn t as Free _ =>
              if member (op aconv) params t then I else insert (op aconv) t
           | _ => I) (args @ prems) []
        in fold Logic.all frees (Logic.list_implies (eqprems @ prems, prop)) end
    val assm = HOLogic.mk_Trueprop (list_comb (pred, params @ argvs))
    val cases = map mk_case intros
    val (_, ctxt3) = ProofContext.add_assms_i Assumption.assume_export
              [((Binding.name AutoBind.assmsN, []), map (fn t => (t, [])) (assm :: cases))]
              ctxt2
  in (pred, prop, ctxt3) end;


(** user interface **)

local

fun attrib f = Thm.declaration_attribute (fn thm => Context.mapping (f thm) I);

val add_elim_attrib = attrib add_elim_thm;

fun generic_code_pred prep_const raw_const lthy =
  let
    val thy = ProofContext.theory_of lthy
    val const = prep_const thy raw_const
    val nparams = get_nparams thy const
    val intro_rules = pred_intros thy const
    val (((tfrees, frees), fact), lthy') =
      Variable.import_thms true intro_rules lthy;
    val (pred, prop, lthy'') = mk_casesrule fact nparams lthy'
    val (predname, _) = dest_Const pred
    fun after_qed [[th]] lthy'' =
      lthy''
      |> LocalTheory.note Thm.generatedK
           ((Binding.empty, [Attrib.internal (K add_elim_attrib)]), [th])
      |> snd
      |> LocalTheory.theory (prove_equation predname NONE)
  in
    Proof.theorem_i NONE after_qed [[(prop, [])]] lthy''
  end;

structure P = OuterParse

in

val code_pred = generic_code_pred (K I);
val code_pred_cmd = generic_code_pred Code.read_const

val setup =
  Attrib.setup @{binding code_ind_intros} (Scan.succeed (attrib add_intro_thm))
    "adding alternative introduction rules for code generation of inductive predicates" #>
  Attrib.setup @{binding code_ind_cases} (Scan.succeed add_elim_attrib)
    "adding alternative elimination rules for code generation of inductive predicates";
  (*FIXME name discrepancy in attribs and ML code*)
  (*FIXME intros should be better named intro*)
  (*FIXME why distinguished atribute for cases?*)

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

fun analyze_compr thy t_compr =
  let
    val split = case t_compr of (Const (@{const_name Collect}, _) $ t) => t
      | _ => error ("Not a set comprehension: " ^ Syntax.string_of_term_global thy t_compr);
    val (body, Ts, fp) = HOLogic.strip_split split;
      (*FIXME former order of tuple positions must be restored*)
    val (pred as Const (name, T), all_args) = strip_comb body
    val (params, args) = chop (get_nparams thy name) all_args
    val user_mode = map_filter I (map_index
      (fn (i, t) => case t of Bound j => if j < length Ts then NONE
        else SOME (i+1) | _ => SOME (i+1)) args) (*FIXME dangling bounds should not occur*)
    val (inargs, _) = get_args user_mode args;
    val all_modes = Symtab.dest (#modes (IndCodegenData.get thy));
    val modes = filter (fn Mode (_, is, _) => is = user_mode)
      (modes_of_term all_modes (list_comb (pred, params)));
    val m = case modes
     of [] => error ("No mode possible for comprehension "
                ^ Syntax.string_of_term_global thy t_compr)
      | [m] => m
      | m :: _ :: _ => (warning ("Multiple modes possible for comprehension "
                ^ Syntax.string_of_term_global thy t_compr); m);
    val t_eval = list_comb (compile_expr thy all_modes (SOME m, list_comb (pred, params)),
      inargs)
  in t_eval end;

end;

