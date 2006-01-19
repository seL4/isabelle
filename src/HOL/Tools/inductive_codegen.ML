(*  Title:      HOL/inductive_codegen.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen

Code generator for inductive predicates.
*)

signature INDUCTIVE_CODEGEN =
sig
  val add : string option -> theory attribute
  val setup : theory -> theory
end;

structure InductiveCodegen : INDUCTIVE_CODEGEN =
struct

open Codegen;

(**** theory data ****)

structure CodegenData = TheoryDataFun
(struct
  val name = "HOL/inductive_codegen";
  type T =
    {intros : (thm * string) list Symtab.table,
     graph : unit Graph.T,
     eqns : (thm * string) list Symtab.table};
  val empty =
    {intros = Symtab.empty, graph = Graph.empty, eqns = Symtab.empty};
  val copy = I;
  val extend = I;
  fun merge _ ({intros=intros1, graph=graph1, eqns=eqns1},
    {intros=intros2, graph=graph2, eqns=eqns2}) =
    {intros = Symtab.merge_multi (Drule.eq_thm_prop o pairself fst)
       (intros1, intros2),
     graph = Graph.merge (K true) (graph1, graph2),
     eqns = Symtab.merge_multi (Drule.eq_thm_prop o pairself fst)
       (eqns1, eqns2)};
  fun print _ _ = ();
end);


fun warn thm = warning ("InductiveCodegen: Not a proper clause:\n" ^
  string_of_thm thm);

fun add_node (g, x) = Graph.new_node (x, ()) g handle Graph.DUP _ => g;

fun add optmod (p as (thy, thm)) =
  let
    val {intros, graph, eqns} = CodegenData.get thy;
    fun thyname_of s = (case optmod of
      NONE => thyname_of_const s thy | SOME s => s);
  in (case concl_of thm of
      _ $ (Const ("op :", _) $ _ $ t) => (case head_of t of
        Const (s, _) =>
          let val cs = foldr add_term_consts [] (prems_of thm)
          in (CodegenData.put
            {intros = intros |>
             Symtab.update (s, Symtab.lookup_multi intros s @ [(thm, thyname_of s)]),
             graph = foldr (uncurry (Graph.add_edge o pair s))
               (Library.foldl add_node (graph, s :: cs)) cs,
             eqns = eqns} thy, thm)
          end
      | _ => (warn thm; p))
    | _ $ (Const ("op =", _) $ t $ _) => (case head_of t of
        Const (s, _) =>
          (CodegenData.put {intros = intros, graph = graph,
             eqns = eqns |> Symtab.update
               (s, Symtab.lookup_multi eqns s @ [(thm, thyname_of s)])} thy, thm)
      | _ => (warn thm; p))
    | _ => (warn thm; p))
  end;

fun get_clauses thy s =
  let val {intros, graph, ...} = CodegenData.get thy
  in case Symtab.lookup intros s of
      NONE => (case InductivePackage.get_inductive thy s of
        NONE => NONE
      | SOME ({names, ...}, {intrs, ...}) =>
          SOME (names, thyname_of_const s thy,
            preprocess thy intrs))
    | SOME _ =>
        let
          val SOME names = find_first
            (fn xs => s mem xs) (Graph.strong_conn graph);
          val intrs = List.concat (map
            (fn s => the (Symtab.lookup intros s)) names);
          val (_, (_, thyname)) = split_last intrs
        in SOME (names, thyname, preprocess thy (map fst intrs)) end
  end;


(**** improper tuples ****)

fun prod_factors p (Const ("Pair", _) $ t $ u) =
      p :: prod_factors (1::p) t @ prod_factors (2::p) u
  | prod_factors p _ = [];

fun split_prod p ps t = if p mem ps then (case t of
       Const ("Pair", _) $ t $ u =>
         split_prod (1::p) ps t @ split_prod (2::p) ps u
     | _ => error "Inconsistent use of products") else [t];

fun full_split_prod (Const ("Pair", _) $ t $ u) =
      full_split_prod t @ full_split_prod u
  | full_split_prod t = [t];

datatype factors = FVar of int list list | FFix of int list list;

exception Factors;

fun mg_factor (FVar f) (FVar f') = FVar (f inter f')
  | mg_factor (FVar f) (FFix f') =
      if f' subset f then FFix f' else raise Factors
  | mg_factor (FFix f) (FVar f') =
      if f subset f' then FFix f else raise Factors
  | mg_factor (FFix f) (FFix f') =
      if f subset f' andalso f' subset f then FFix f else raise Factors;

fun dest_factors (FVar f) = f
  | dest_factors (FFix f) = f;

fun infer_factors sg extra_fs (fs, (optf, t)) =
  let fun err s = error (s ^ "\n" ^ Sign.string_of_term sg t)
  in (case (optf, strip_comb t) of
      (SOME f, (Const (name, _), args)) =>
        (case AList.lookup (op =) extra_fs name of
           NONE => AList.update (op =) (name, getOpt
             (Option.map (mg_factor f) (AList.lookup (op =) fs name), f)) fs
         | SOME (fs', f') => (mg_factor f (FFix f');
             Library.foldl (infer_factors sg extra_fs)
               (fs, map (Option.map FFix) fs' ~~ args)))
    | (SOME f, (Var ((name, _), _), [])) =>
        AList.update (op =) (name, getOpt
          (Option.map (mg_factor f) (AList.lookup (op =) fs name), f)) fs
    | (NONE, _) => fs
    | _ => err "Illegal term")
      handle Factors => err "Product factor mismatch in"
  end;

fun string_of_factors p ps = if p mem ps then
    "(" ^ string_of_factors (1::p) ps ^ ", " ^ string_of_factors (2::p) ps ^ ")"
  else "_";


(**** check if a term contains only constructor functions ****)

fun is_constrt thy =
  let
    val cnstrs = List.concat (List.concat (map
      (map (fn (_, (_, _, cs)) => map (apsnd length) cs) o #descr o snd)
      (Symtab.dest (DatatypePackage.get_datatypes thy))));
    fun check t = (case strip_comb t of
        (Var _, []) => true
      | (Const (s, _), ts) => (case AList.lookup (op =) cnstrs s of
            NONE => false
          | SOME i => length ts = i andalso forall check ts)
      | _ => false)
  in check end;

(**** check if a type is an equality type (i.e. doesn't contain fun) ****)

fun is_eqT (Type (s, Ts)) = s <> "fun" andalso forall is_eqT Ts
  | is_eqT _ = true;

(**** mode inference ****)

fun string_of_mode (iss, is) = space_implode " -> " (map
  (fn NONE => "X"
    | SOME js => enclose "[" "]" (commas (map string_of_int js)))
       (iss @ [SOME is]));

fun print_modes modes = message ("Inferred modes:\n" ^
  space_implode "\n" (map (fn (s, ms) => s ^ ": " ^ commas (map
    string_of_mode ms)) modes));

val term_vs = map (fst o fst o dest_Var) o term_vars;
val terms_vs = distinct o List.concat o (map term_vs);

(** collect all Vars in a term (with duplicates!) **)
fun term_vTs tm =
  fold_aterms (fn Var ((x, _), T) => cons (x, T) | _ => I) tm [];

fun get_args _ _ [] = ([], [])
  | get_args is i (x::xs) = (if i mem is then apfst else apsnd) (cons x)
      (get_args is (i+1) xs);

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

datatype mode = Mode of (int list option list * int list) * mode option list;

fun modes_of modes t =
  let
    fun mk_modes name args = List.concat
      (map (fn (m as (iss, is)) => map (Mode o pair m) (cprods (map
        (fn (NONE, _) => [NONE]
          | (SOME js, arg) => map SOME
              (List.filter (fn Mode ((_, js'), _) => js=js') (modes_of modes arg)))
                (iss ~~ args)))) ((the o AList.lookup (op =) modes) name))

  in (case strip_comb t of
      (Const ("op =", Type (_, [T, _])), _) =>
        [Mode (([], [1]), []), Mode (([], [2]), [])] @
        (if is_eqT T then [Mode (([], [1, 2]), [])] else [])
    | (Const (name, _), args) => mk_modes name args
    | (Var ((name, _), _), args) => mk_modes name args
    | (Free (name, _), args) => mk_modes name args)
  end;

datatype indprem = Prem of term list * term | Sidecond of term;

fun select_mode_prem thy modes vs ps =
  find_first (isSome o snd) (ps ~~ map
    (fn Prem (us, t) => find_first (fn Mode ((_, is), _) =>
          let
            val (in_ts, out_ts) = get_args is 1 us;
            val (out_ts', in_ts') = List.partition (is_constrt thy) out_ts;
            val vTs = List.concat (map term_vTs out_ts');
            val dupTs = map snd (duplicates vTs) @
              List.mapPartial (AList.lookup (op =) vTs) vs;
          in
            terms_vs (in_ts @ in_ts') subset vs andalso
            forall (is_eqT o fastype_of) in_ts' andalso
            term_vs t subset vs andalso
            forall is_eqT dupTs
          end)
            (modes_of modes t handle Option => [Mode (([], []), [])])
      | Sidecond t => if term_vs t subset vs then SOME (Mode (([], []), []))
          else NONE) ps);

fun check_mode_clause thy arg_vs modes (iss, is) (ts, ps) =
  let
    val modes' = modes @ List.mapPartial
      (fn (_, NONE) => NONE | (v, SOME js) => SOME (v, [([], js)]))
        (arg_vs ~~ iss);
    fun check_mode_prems vs [] = SOME vs
      | check_mode_prems vs ps = (case select_mode_prem thy modes' vs ps of
          NONE => NONE
        | SOME (x, _) => check_mode_prems
            (case x of Prem (us, _) => vs union terms_vs us | _ => vs)
            (filter_out (equal x) ps));
    val (in_ts, in_ts') = List.partition (is_constrt thy) (fst (get_args is 1 ts));
    val in_vs = terms_vs in_ts;
    val concl_vs = terms_vs ts
  in
    forall is_eqT (map snd (duplicates (List.concat (map term_vTs in_ts)))) andalso
    forall (is_eqT o fastype_of) in_ts' andalso
    (case check_mode_prems (arg_vs union in_vs) ps of
       NONE => false
     | SOME vs => concl_vs subset vs)
  end;

fun check_modes_pred thy arg_vs preds modes (p, ms) =
  let val SOME rs = AList.lookup (op =) preds p
  in (p, List.filter (fn m => case find_index
    (not o check_mode_clause thy arg_vs modes m) rs of
      ~1 => true
    | i => (message ("Clause " ^ string_of_int (i+1) ^ " of " ^
      p ^ " violates mode " ^ string_of_mode m); false)) ms)
  end;

fun fixp f x =
  let val y = f x
  in if x = y then x else fixp f y end;

fun infer_modes thy extra_modes factors arg_vs preds = fixp (fn modes =>
  map (check_modes_pred thy arg_vs preds (modes @ extra_modes)) modes)
    (map (fn (s, (fs, f)) => (s, cprod (cprods (map
      (fn NONE => [NONE]
        | SOME f' => map SOME (subsets 1 (length f' + 1))) fs),
      subsets 1 (length f + 1)))) factors);

(**** code generation ****)

fun mk_eq (x::xs) =
  let fun mk_eqs _ [] = []
        | mk_eqs a (b::cs) = Pretty.str (a ^ " = " ^ b) :: mk_eqs b cs
  in mk_eqs x xs end;

fun mk_tuple xs = Pretty.block (Pretty.str "(" ::
  List.concat (separate [Pretty.str ",", Pretty.brk 1] (map single xs)) @
  [Pretty.str ")"]);

(* convert nested pairs to n-tuple *)

fun conv_ntuple [_] t ps = ps
  | conv_ntuple [_, _] t ps = ps
  | conv_ntuple us t ps =
      let
        val xs = map (fn i => Pretty.str ("x" ^ string_of_int i))
          (1 upto length us);
        fun ntuple (ys as (x, T) :: xs) U =
          if T = U then (x, xs)
          else
            let
              val Type ("*", [U1, U2]) = U;
              val (p1, ys1) = ntuple ys U1;
              val (p2, ys2) = ntuple ys1 U2
            in (mk_tuple [p1, p2], ys2) end
      in
        [Pretty.str "Seq.map (fn", Pretty.brk 1,
         fst (ntuple (xs ~~ map fastype_of us) (HOLogic.dest_setT (fastype_of t))),
         Pretty.str " =>", Pretty.brk 1, mk_tuple xs, Pretty.str ")",
         Pretty.brk 1, parens (Pretty.block ps)]
      end;

(* convert n-tuple to nested pairs *)

fun conv_ntuple' fs T ps =
  let
    fun mk_x i = Pretty.str ("x" ^ string_of_int i);
    fun conv i js (Type ("*", [T, U])) =
          if js mem fs then
            let
              val (p, i') = conv i (1::js) T;
              val (q, i'') = conv i' (2::js) U
            in (mk_tuple [p, q], i'') end
          else (mk_x i, i+1)
      | conv i js _ = (mk_x i, i+1)
    val (p, i) = conv 1 [] T
  in
    if i > 3 then
      [Pretty.str "Seq.map (fn", Pretty.brk 1,
       mk_tuple (map mk_x (1 upto i-1)), Pretty.str " =>", Pretty.brk 1,
       p, Pretty.str ")", Pretty.brk 1, parens (Pretty.block ps)]
    else ps
  end;

fun mk_v ((names, vs), s) = (case AList.lookup (op =) vs s of
      NONE => ((names, (s, [s])::vs), s)
    | SOME xs => let val s' = variant names s in
        ((s'::names, AList.update (op =) (s, s'::xs) vs), s') end);

fun distinct_v (nvs, Var ((s, 0), T)) =
      apsnd (Var o rpair T o rpair 0) (mk_v (nvs, s))
  | distinct_v (nvs, t $ u) =
      let
        val (nvs', t') = distinct_v (nvs, t);
        val (nvs'', u') = distinct_v (nvs', u);
      in (nvs'', t' $ u') end
  | distinct_v x = x;

fun is_exhaustive (Var _) = true
  | is_exhaustive (Const ("Pair", _) $ t $ u) =
      is_exhaustive t andalso is_exhaustive u
  | is_exhaustive _ = false;

fun compile_match nvs eq_ps out_ps success_p can_fail =
  let val eqs = List.concat (separate [Pretty.str " andalso", Pretty.brk 1]
    (map single (List.concat (map (mk_eq o snd) nvs) @ eq_ps)));
  in
    Pretty.block
     ([Pretty.str "(fn ", mk_tuple out_ps, Pretty.str " =>", Pretty.brk 1] @
      (Pretty.block ((if eqs=[] then [] else Pretty.str "if " ::
         [Pretty.block eqs, Pretty.brk 1, Pretty.str "then "]) @
         (success_p ::
          (if eqs=[] then [] else [Pretty.brk 1, Pretty.str "else Seq.empty"]))) ::
       (if can_fail then
          [Pretty.brk 1, Pretty.str "| _ => Seq.empty)"]
        else [Pretty.str ")"])))
  end;

fun modename module s (iss, is) gr =
  let val (gr', id) = if s = "op =" then (gr, ("", "equal"))
    else mk_const_id module s gr
  in (gr', space_implode "__"
    (mk_qual_id module id ::
      map (space_implode "_" o map string_of_int) (List.mapPartial I iss @ [is])))
  end;

fun compile_expr thy defs dep module brack (gr, (NONE, t)) =
      apsnd single (invoke_codegen thy defs dep module brack (gr, t))
  | compile_expr _ _ _ _ _ (gr, (SOME _, Var ((name, _), _))) =
      (gr, [Pretty.str name])
  | compile_expr thy defs dep module brack (gr, (SOME (Mode (mode, ms)), t)) =
      let
        val (Const (name, _), args) = strip_comb t;
        val (gr', (ps, mode_id)) = foldl_map
            (compile_expr thy defs dep module true) (gr, ms ~~ args) |>>>
          modename module name mode;
      in (gr', (if brack andalso not (null ps) then
        single o parens o Pretty.block else I)
          (List.concat (separate [Pretty.brk 1]
            ([Pretty.str mode_id] :: ps))))
      end;

fun compile_clause thy defs gr dep module all_vs arg_vs modes (iss, is) (ts, ps) =
  let
    val modes' = modes @ List.mapPartial
      (fn (_, NONE) => NONE | (v, SOME js) => SOME (v, [([], js)]))
        (arg_vs ~~ iss);

    fun check_constrt ((names, eqs), t) =
      if is_constrt thy t then ((names, eqs), t) else
        let val s = variant names "x";
        in ((s::names, (s, t)::eqs), Var ((s, 0), fastype_of t)) end;

    fun compile_eq (gr, (s, t)) =
      apsnd (Pretty.block o cons (Pretty.str (s ^ " = ")) o single)
        (invoke_codegen thy defs dep module false (gr, t));

    val (in_ts, out_ts) = get_args is 1 ts;
    val ((all_vs', eqs), in_ts') =
      foldl_map check_constrt ((all_vs, []), in_ts);

    fun is_ind t = (case head_of t of
          Const (s, _) => s = "op =" orelse AList.defined (op =) modes s
        | Var ((s, _), _) => s mem arg_vs);

    fun compile_prems out_ts' vs names gr [] =
          let
            val (gr2, out_ps) = foldl_map
              (invoke_codegen thy defs dep module false) (gr, out_ts);
            val (gr3, eq_ps) = foldl_map compile_eq (gr2, eqs);
            val ((names', eqs'), out_ts'') =
              foldl_map check_constrt ((names, []), out_ts');
            val (nvs, out_ts''') = foldl_map distinct_v
              ((names', map (fn x => (x, [x])) vs), out_ts'');
            val (gr4, out_ps') = foldl_map
              (invoke_codegen thy defs dep module false) (gr3, out_ts''');
            val (gr5, eq_ps') = foldl_map compile_eq (gr4, eqs')
          in
            (gr5, compile_match (snd nvs) (eq_ps @ eq_ps') out_ps'
              (Pretty.block [Pretty.str "Seq.single", Pretty.brk 1, mk_tuple out_ps])
              (exists (not o is_exhaustive) out_ts'''))
          end
      | compile_prems out_ts vs names gr ps =
          let
            val vs' = distinct (List.concat (vs :: map term_vs out_ts));
            val SOME (p, mode as SOME (Mode ((_, js), _))) =
              select_mode_prem thy modes' vs' ps;
            val ps' = filter_out (equal p) ps;
            val ((names', eqs), out_ts') =
              foldl_map check_constrt ((names, []), out_ts);
            val (nvs, out_ts'') = foldl_map distinct_v
              ((names', map (fn x => (x, [x])) vs), out_ts');
            val (gr0, out_ps) = foldl_map
              (invoke_codegen thy defs dep module false) (gr, out_ts'');
            val (gr1, eq_ps) = foldl_map compile_eq (gr0, eqs)
          in
            (case p of
               Prem (us, t) =>
                 let
                   val (in_ts, out_ts''') = get_args js 1 us;
                   val (gr2, in_ps) = foldl_map
                     (invoke_codegen thy defs dep module false) (gr1, in_ts);
                   val (gr3, ps) = if is_ind t then
                       apsnd (fn ps => ps @ [Pretty.brk 1, mk_tuple in_ps])
                         (compile_expr thy defs dep module false
                           (gr2, (mode, t)))
                     else
                       apsnd (fn p => conv_ntuple us t
                         [Pretty.str "Seq.of_list", Pretty.brk 1, p])
                           (invoke_codegen thy defs dep module true (gr2, t));
                   val (gr4, rest) = compile_prems out_ts''' vs' (fst nvs) gr3 ps';
                 in
                   (gr4, compile_match (snd nvs) eq_ps out_ps
                      (Pretty.block (ps @
                         [Pretty.str " :->", Pretty.brk 1, rest]))
                      (exists (not o is_exhaustive) out_ts''))
                 end
             | Sidecond t =>
                 let
                   val (gr2, side_p) = invoke_codegen thy defs dep module true (gr1, t);
                   val (gr3, rest) = compile_prems [] vs' (fst nvs) gr2 ps';
                 in
                   (gr3, compile_match (snd nvs) eq_ps out_ps
                      (Pretty.block [Pretty.str "?? ", side_p,
                        Pretty.str " :->", Pretty.brk 1, rest])
                      (exists (not o is_exhaustive) out_ts''))
                 end)
          end;

    val (gr', prem_p) = compile_prems in_ts' arg_vs all_vs' gr ps;
  in
    (gr', Pretty.block [Pretty.str "Seq.single inp :->", Pretty.brk 1, prem_p])
  end;

fun compile_pred thy defs gr dep module prfx all_vs arg_vs modes s cls mode =
  let val (gr', (cl_ps, mode_id)) =
    foldl_map (fn (gr, cl) => compile_clause thy defs
      gr dep module all_vs arg_vs modes mode cl) (gr, cls) |>>>
    modename module s mode
  in
    ((gr', "and "), Pretty.block
      ([Pretty.block (separate (Pretty.brk 1)
         (Pretty.str (prfx ^ mode_id) ::
           map Pretty.str arg_vs) @
         [Pretty.str " inp ="]),
        Pretty.brk 1] @
       List.concat (separate [Pretty.str " ++", Pretty.brk 1] (map single cl_ps))))
  end;

fun compile_preds thy defs gr dep module all_vs arg_vs modes preds =
  let val ((gr', _), prs) = foldl_map (fn ((gr, prfx), (s, cls)) =>
    foldl_map (fn ((gr', prfx'), mode) => compile_pred thy defs gr'
      dep module prfx' all_vs arg_vs modes s cls mode)
        ((gr, prfx), ((the o AList.lookup (op =) modes) s))) ((gr, "fun "), preds)
  in
    (gr', space_implode "\n\n" (map Pretty.string_of (List.concat prs)) ^ ";\n\n")
  end;

(**** processing of introduction rules ****)

exception Modes of
  (string * (int list option list * int list) list) list *
  (string * (int list list option list * int list list)) list;

fun lookup_modes gr dep = apfst List.concat (apsnd List.concat (ListPair.unzip
  (map ((fn (SOME (Modes x), _, _) => x | _ => ([], [])) o get_node gr)
    (Graph.all_preds (fst gr) [dep]))));

fun print_factors factors = message ("Factors:\n" ^
  space_implode "\n" (map (fn (s, (fs, f)) => s ^ ": " ^
    space_implode " -> " (map
      (fn NONE => "X" | SOME f' => string_of_factors [] f')
        (fs @ [SOME f]))) factors));

fun prep_intrs intrs = map (rename_term o #prop o rep_thm o standard) intrs;

fun constrain cs [] = []
  | constrain cs ((s, xs) :: ys) = (s, case AList.lookup (op =) cs s of
      NONE => xs
    | SOME xs' => xs inter xs') :: constrain cs ys;

fun mk_extra_defs thy defs gr dep names module ts =
  Library.foldl (fn (gr, name) =>
    if name mem names then gr
    else (case get_clauses thy name of
        NONE => gr
      | SOME (names, thyname, intrs) =>
          mk_ind_def thy defs gr dep names (if_library thyname module)
            [] [] (prep_intrs intrs)))
            (gr, foldr add_term_consts [] ts)

and mk_ind_def thy defs gr dep names module modecs factorcs intrs =
  add_edge (hd names, dep) gr handle Graph.UNDEF _ =>
    let
      val _ $ (_ $ _ $ u) = Logic.strip_imp_concl (hd intrs);
      val (_, args) = strip_comb u;
      val arg_vs = List.concat (map term_vs args);

      fun dest_prem factors (_ $ (p as (Const ("op :", _) $ t $ u))) =
            (case AList.lookup (op =) factors (case head_of u of
                 Const (name, _) => name | Var ((name, _), _) => name) of
               NONE => Prem (full_split_prod t, u)
             | SOME f => Prem (split_prod [] f t, u))
        | dest_prem factors (_ $ ((eq as Const ("op =", _)) $ t $ u)) =
            Prem ([t, u], eq)
        | dest_prem factors (_ $ t) = Sidecond t;

      fun add_clause factors (clauses, intr) =
        let
          val _ $ (_ $ t $ u) = Logic.strip_imp_concl intr;
          val Const (name, _) = head_of u;
          val prems = map (dest_prem factors) (Logic.strip_imp_prems intr);
        in
          AList.update (op =) (name, ((these o AList.lookup (op =) clauses) name) @
             [(split_prod [] ((the o AList.lookup (op =) factors) name) t, prems)]) clauses
        end;

      fun check_set (Const (s, _)) = s mem names orelse isSome (get_clauses thy s)
        | check_set (Var ((s, _), _)) = s mem arg_vs
        | check_set _ = false;

      fun add_prod_factors extra_fs (fs, _ $ (Const ("op :", _) $ t $ u)) =
            if check_set (head_of u)
            then infer_factors (sign_of thy) extra_fs
              (fs, (SOME (FVar (prod_factors [] t)), u))
            else fs
        | add_prod_factors _ (fs, _) = fs;

      val gr' = mk_extra_defs thy defs
        (add_edge (hd names, dep)
          (new_node (hd names, (NONE, "", "")) gr)) (hd names) names module intrs;
      val (extra_modes, extra_factors) = lookup_modes gr' (hd names);
      val fs = constrain factorcs (map (apsnd dest_factors)
        (Library.foldl (add_prod_factors extra_factors) ([], List.concat (map (fn t =>
          Logic.strip_imp_concl t :: Logic.strip_imp_prems t) intrs))));
      val factors = List.mapPartial (fn (name, f) =>
        if name mem arg_vs then NONE
        else SOME (name, (map (AList.lookup (op =) fs) arg_vs, f))) fs;
      val clauses =
        Library.foldl (add_clause (fs @ map (apsnd snd) extra_factors)) ([], intrs);
      val modes = constrain modecs
        (infer_modes thy extra_modes factors arg_vs clauses);
      val _ = print_factors factors;
      val _ = print_modes modes;
      val (gr'', s) = compile_preds thy defs gr' (hd names) module (terms_vs intrs)
        arg_vs (modes @ extra_modes) clauses;
    in
      (map_node (hd names)
        (K (SOME (Modes (modes, factors)), module, s)) gr'')
    end;

fun find_mode gr dep s u modes is = (case find_first (fn Mode ((_, js), _) => is=js)
  (modes_of modes u handle Option => []) of
     NONE => codegen_error gr dep
       ("No such mode for " ^ s ^ ": " ^ string_of_mode ([], is))
   | mode => mode);

fun mk_ind_call thy defs gr dep module t u is_query = (case head_of u of
  Const (s, T) => (case (get_clauses thy s, get_assoc_code thy s T) of
       (NONE, _) => NONE
     | (SOME (names, thyname, intrs), NONE) =>
         let
          fun mk_mode (((ts, mode), i), Const ("dummy_pattern", _)) =
                ((ts, mode), i+1)
            | mk_mode (((ts, mode), i), t) = ((ts @ [t], mode @ [i]), i+1);

           val module' = if_library thyname module;
           val gr1 = mk_extra_defs thy defs
             (mk_ind_def thy defs gr dep names module'
             [] [] (prep_intrs intrs)) dep names module' [u];
           val (modes, factors) = lookup_modes gr1 dep;
           val ts = split_prod [] ((snd o the o AList.lookup (op =) factors) s) t;
           val (ts', is) = if is_query then
               fst (Library.foldl mk_mode ((([], []), 1), ts))
             else (ts, 1 upto length ts);
           val mode = find_mode gr1 dep s u modes is;
           val (gr2, in_ps) = foldl_map
             (invoke_codegen thy defs dep module false) (gr1, ts');
           val (gr3, ps) =
             compile_expr thy defs dep module false (gr2, (mode, u))
         in
           SOME (gr3, Pretty.block
             (ps @ [Pretty.brk 1, mk_tuple in_ps]))
         end
     | _ => NONE)
  | _ => NONE);

fun list_of_indset thy defs gr dep module brack u = (case head_of u of
  Const (s, T) => (case (get_clauses thy s, get_assoc_code thy s T) of
       (NONE, _) => NONE
     | (SOME (names, thyname, intrs), NONE) =>
         let
           val module' = if_library thyname module;
           val gr1 = mk_extra_defs thy defs
             (mk_ind_def thy defs gr dep names module'
             [] [] (prep_intrs intrs)) dep names module' [u];
           val (modes, factors) = lookup_modes gr1 dep;
           val mode = find_mode gr1 dep s u modes [];
           val (gr2, ps) =
             compile_expr thy defs dep module false (gr1, (mode, u));
           val (gr3, _) =
             invoke_tycodegen thy defs dep module false (gr2, body_type T)
         in
           SOME (gr3, (if brack then parens else I)
             (Pretty.block ([Pretty.str "Seq.list_of", Pretty.brk 1,
               Pretty.str "("] @
                conv_ntuple' (snd (valOf (AList.lookup (op =) factors s)))
                 (HOLogic.dest_setT (fastype_of u))
                 (ps @ [Pretty.brk 1, Pretty.str "()"]) @
               [Pretty.str ")"])))
         end
     | _ => NONE)
  | _ => NONE);

fun clause_of_eqn eqn =
  let
    val (t, u) = HOLogic.dest_eq (HOLogic.dest_Trueprop (concl_of eqn));
    val (Const (s, T), ts) = strip_comb t;
    val (Ts, U) = strip_type T
  in
    rename_term
      (Logic.list_implies (prems_of eqn, HOLogic.mk_Trueprop (HOLogic.mk_mem
        (foldr1 HOLogic.mk_prod (ts @ [u]), Const (s ^ "_aux",
          HOLogic.mk_setT (foldr1 HOLogic.mk_prodT (Ts @ [U])))))))
  end;

fun mk_fun thy defs name eqns dep module module' gr =
  case try (get_node gr) name of
    NONE =>
    let
      val clauses = map clause_of_eqn eqns;
      val pname = name ^ "_aux";
      val arity = length (snd (strip_comb (fst (HOLogic.dest_eq
        (HOLogic.dest_Trueprop (concl_of (hd eqns)))))));
      val mode = 1 upto arity;
      val (gr', (fun_id, mode_id)) = gr |>
        mk_const_id module' name |>>>
        modename module' pname ([], mode);
      val vars = map (fn i => Pretty.str ("x" ^ string_of_int i)) mode;
      val s = Pretty.string_of (Pretty.block
        [mk_app false (Pretty.str ("fun " ^ snd fun_id)) vars, Pretty.str " =",
         Pretty.brk 1, Pretty.str "Seq.hd", Pretty.brk 1,
         parens (Pretty.block [Pretty.str mode_id,
           Pretty.brk 1, mk_tuple vars])]) ^ ";\n\n";
      val gr'' = mk_ind_def thy defs (add_edge (name, dep)
        (new_node (name, (NONE, module', s)) gr')) name [pname] module'
        [(pname, [([], mode)])]
        [(pname, map (fn i => replicate i 2) (0 upto arity-1))]
        clauses;
      val (modes, _) = lookup_modes gr'' dep;
      val _ = find_mode gr'' dep pname (snd (HOLogic.dest_mem (HOLogic.dest_Trueprop
        (Logic.strip_imp_concl (hd clauses))))) modes mode
    in (gr'', mk_qual_id module fun_id) end
  | SOME _ =>
      (add_edge (name, dep) gr, mk_qual_id module (get_const_id name gr));

fun inductive_codegen thy defs gr dep module brack (Const ("op :", _) $ t $ u) =
      ((case mk_ind_call thy defs gr dep module (Term.no_dummy_patterns t) u false of
         NONE => NONE
       | SOME (gr', call_p) => SOME (gr', (if brack then parens else I)
           (Pretty.block [Pretty.str "?! (", call_p, Pretty.str ")"])))
        handle TERM _ => mk_ind_call thy defs gr dep module t u true)
  | inductive_codegen thy defs gr dep module brack t = (case strip_comb t of
      (Const (s, _), ts) => (case Symtab.lookup (#eqns (CodegenData.get thy)) s of
        NONE => list_of_indset thy defs gr dep module brack t
      | SOME eqns =>
          let
            val (_, (_, thyname)) = split_last eqns;
            val (gr', id) = mk_fun thy defs s (preprocess thy (map fst eqns))
              dep module (if_library thyname module) gr;
            val (gr'', ps) = foldl_map
              (invoke_codegen thy defs dep module true) (gr', ts);
          in SOME (gr'', mk_app brack (Pretty.str id) ps)
          end)
    | _ => NONE);

val setup =
  add_codegen "inductive" inductive_codegen #>
  CodegenData.init #>
  add_attribute "ind" (Scan.option (Args.$$$ "target" |-- Args.colon |-- Args.name) >> add);

end;


(**** combinators for code generated from inductive predicates ****)

infix 5 :->;
infix 3 ++;

fun s :-> f = Seq.flat (Seq.map f s);

fun s1 ++ s2 = Seq.append (s1, s2);

fun ?? b = if b then Seq.single () else Seq.empty;

fun ?! s = isSome (Seq.pull s);    

fun equal__1 x = Seq.single x;

val equal__2 = equal__1;

fun equal__1_2 (x, y) = ?? (x = y);
