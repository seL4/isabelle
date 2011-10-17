(*  Title:      HOL/Tools/inductive_codegen.ML
    Author:     Stefan Berghofer, TU Muenchen

Code generator for inductive predicates.
*)

signature INDUCTIVE_CODEGEN =
sig
  val add: string option -> int option -> attribute
  val poke_test_fn: (int * int * int -> term list option) -> unit
  val test_term: Proof.context -> (term * term list) list -> int list ->
    term list option * Quickcheck.report option
  val active : bool Config.T
  val setup: theory -> theory
end;

structure Inductive_Codegen : INDUCTIVE_CODEGEN =
struct

(**** theory data ****)

fun merge_rules tabs =
  Symtab.join (fn _ => AList.merge (Thm.eq_thm_prop) (K true)) tabs;

structure CodegenData = Theory_Data
(
  type T =
    {intros : (thm * (string * int)) list Symtab.table,
     graph : unit Graph.T,
     eqns : (thm * string) list Symtab.table};
  val empty =
    {intros = Symtab.empty, graph = Graph.empty, eqns = Symtab.empty};
  val extend = I;
  fun merge
    ({intros = intros1, graph = graph1, eqns = eqns1},
      {intros = intros2, graph = graph2, eqns = eqns2}) : T =
    {intros = merge_rules (intros1, intros2),
     graph = Graph.merge (K true) (graph1, graph2),
     eqns = merge_rules (eqns1, eqns2)};
);


fun warn thy thm =
  warning ("Inductive_Codegen: Not a proper clause:\n" ^
    Display.string_of_thm_global thy thm);

fun add_node x g = Graph.new_node (x, ()) g handle Graph.DUP _ => g;

fun add optmod optnparms = Thm.declaration_attribute (fn thm => Context.mapping (fn thy =>
  let
    val {intros, graph, eqns} = CodegenData.get thy;
    fun thyname_of s = (case optmod of
      NONE => Codegen.thyname_of_const thy s | SOME s => s);
  in
    (case Option.map strip_comb (try HOLogic.dest_Trueprop (concl_of thm)) of
      SOME (Const (@{const_name HOL.eq}, _), [t, _]) =>
        (case head_of t of
          Const (s, _) =>
            CodegenData.put {intros = intros, graph = graph,
               eqns = eqns |> Symtab.map_default (s, [])
                 (AList.update Thm.eq_thm_prop (thm, thyname_of s))} thy
        | _ => (warn thy thm; thy))
    | SOME (Const (s, _), _) =>
        let
          val cs = fold Term.add_const_names (Thm.prems_of thm) [];
          val rules = Symtab.lookup_list intros s;
          val nparms =
            (case optnparms of
              SOME k => k
            | NONE =>
                (case rules of
                  [] =>
                    (case try (Inductive.the_inductive (Proof_Context.init_global thy)) s of
                      SOME (_, {raw_induct, ...}) =>
                        length (Inductive.params_of raw_induct)
                    | NONE => 0)
                | xs => snd (snd (List.last xs))))
        in CodegenData.put
          {intros = intros |>
           Symtab.update (s, (AList.update Thm.eq_thm_prop
             (thm, (thyname_of s, nparms)) rules)),
           graph = fold_rev (Graph.add_edge o pair s) cs (fold add_node (s :: cs) graph),
           eqns = eqns} thy
        end
    | _ => (warn thy thm; thy))
  end) I);

fun get_clauses thy s =
  let val {intros, graph, ...} = CodegenData.get thy in
    (case Symtab.lookup intros s of
      NONE =>
        (case try (Inductive.the_inductive (Proof_Context.init_global thy)) s of
          NONE => NONE
        | SOME ({names, ...}, {intrs, raw_induct, ...}) =>
            SOME (names, Codegen.thyname_of_const thy s,
              length (Inductive.params_of raw_induct),
              Codegen.preprocess thy intrs))
    | SOME _ =>
        let
          val SOME names = find_first
            (fn xs => member (op =) xs s) (Graph.strong_conn graph);
          val intrs as (_, (thyname, nparms)) :: _ =
            maps (the o Symtab.lookup intros) names;
        in SOME (names, thyname, nparms, Codegen.preprocess thy (map fst (rev intrs))) end)
  end;


(**** check if a term contains only constructor functions ****)

fun is_constrt thy =
  let
    val cnstrs = flat (maps
      (map (fn (_, (_, _, cs)) => map (apsnd length) cs) o #descr o snd)
      (Symtab.dest (Datatype_Data.get_all thy)));
    fun check t =
      (case strip_comb t of
        (Var _, []) => true
      | (Const (s, _), ts) =>
          (case AList.lookup (op =) cnstrs s of
            NONE => false
          | SOME i => length ts = i andalso forall check ts)
      | _ => false);
  in check end;


(**** check if a type is an equality type (i.e. doesn't contain fun) ****)

fun is_eqT (Type (s, Ts)) = s <> "fun" andalso forall is_eqT Ts
  | is_eqT _ = true;


(**** mode inference ****)

fun string_of_mode (iss, is) = space_implode " -> " (map
  (fn NONE => "X"
    | SOME js => enclose "[" "]" (commas (map string_of_int js)))
       (iss @ [SOME is]));

fun print_modes modes = Codegen.message ("Inferred modes:\n" ^
  cat_lines (map (fn (s, ms) => s ^ ": " ^ commas (map
    (fn (m, rnd) => string_of_mode m ^
       (if rnd then " (random)" else "")) ms)) modes));

val term_vs = map (fst o fst o dest_Var) o Misc_Legacy.term_vars;
val terms_vs = distinct (op =) o maps term_vs;

(** collect all Vars in a term (with duplicates!) **)
fun term_vTs tm =
  fold_aterms (fn Var ((x, _), T) => cons (x, T) | _ => I) tm [];

fun get_args _ _ [] = ([], [])
  | get_args is i (x::xs) = (if member (op =) is i then apfst else apsnd) (cons x)
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

fun cprods xss = List.foldr (map op :: o cprod) [[]] xss;

datatype mode = Mode of ((int list option list * int list) * bool) * int list * mode option list;

fun needs_random (Mode ((_, b), _, ms)) =
  b orelse exists (fn NONE => false | SOME m => needs_random m) ms;

fun modes_of modes t =
  let
    val ks = 1 upto length (binder_types (fastype_of t));
    val default = [Mode ((([], ks), false), ks, [])];
    fun mk_modes name args = Option.map
     (maps (fn (m as ((iss, is), _)) =>
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
                  (fn Mode (_, js', _) => js=js') (modes_of modes arg)))
                    (iss ~~ args1)))
          end
        end)) (AList.lookup op = modes name)

  in
    (case strip_comb t of
      (Const (@{const_name HOL.eq}, Type (_, [T, _])), _) =>
        [Mode ((([], [1]), false), [1], []), Mode ((([], [2]), false), [2], [])] @
        (if is_eqT T then [Mode ((([], [1, 2]), false), [1, 2], [])] else [])
    | (Const (name, _), args) => the_default default (mk_modes name args)
    | (Var ((name, _), _), args) => the (mk_modes name args)
    | (Free (name, _), args) => the (mk_modes name args)
    | _ => default)
  end;

datatype indprem = Prem of term list * term * bool | Sidecond of term;

fun missing_vars vs ts = subtract (fn (x, ((y, _), _)) => x = y) vs
  (fold Term.add_vars ts []);

fun monomorphic_vars vs = null (fold (Term.add_tvarsT o snd) vs []);

fun mode_ord p = int_ord (pairself (fn (Mode ((_, rnd), _, _), vs) =>
  length vs + (if null vs then 0 else 1) + (if rnd then 1 else 0)) p);

fun select_mode_prem thy modes vs ps =
  sort (mode_ord o pairself (hd o snd))
    (filter_out (null o snd) (ps ~~ map
      (fn Prem (us, t, is_set) => sort mode_ord
          (map_filter (fn m as Mode (_, is, _) =>
            let
              val (in_ts, out_ts) = get_args is 1 us;
              val (out_ts', in_ts') = List.partition (is_constrt thy) out_ts;
              val vTs = maps term_vTs out_ts';
              val dupTs = map snd (duplicates (op =) vTs) @
                map_filter (AList.lookup (op =) vTs) vs;
              val missing_vs = missing_vars vs (t :: in_ts @ in_ts')
            in
              if forall (is_eqT o fastype_of) in_ts' andalso forall is_eqT dupTs
                andalso monomorphic_vars missing_vs
              then SOME (m, missing_vs)
              else NONE
            end)
              (if is_set then [Mode ((([], []), false), [], [])]
               else modes_of modes t handle Option =>
                 error ("Bad predicate: " ^ Syntax.string_of_term_global thy t)))
        | Sidecond t =>
            let val missing_vs = missing_vars vs [t]
            in
              if monomorphic_vars missing_vs
              then [(Mode ((([], []), false), [], []), missing_vs)]
              else []
            end)
              ps));

fun use_random codegen_mode = member (op =) codegen_mode "random_ind";

fun check_mode_clause thy codegen_mode arg_vs modes ((iss, is), rnd) (ts, ps) =
  let
    val modes' = modes @ map_filter
      (fn (_, NONE) => NONE | (v, SOME js) => SOME (v, [(([], js), false)]))
        (arg_vs ~~ iss);
    fun check_mode_prems vs rnd [] = SOME (vs, rnd)
      | check_mode_prems vs rnd ps =
          (case select_mode_prem thy modes' vs ps of
            (x, (m, []) :: _) :: _ =>
              check_mode_prems
                (case x of Prem (us, _, _) => union (op =) vs (terms_vs us) | _ => vs)
                (rnd orelse needs_random m)
                (filter_out (equal x) ps)
          | (_, (_, vs') :: _) :: _ =>
              if use_random codegen_mode then
                check_mode_prems (union (op =) vs (map (fst o fst) vs')) true ps
              else NONE
          | _ => NONE);
    val (in_ts, in_ts') = List.partition (is_constrt thy) (fst (get_args is 1 ts));
    val in_vs = terms_vs in_ts;
  in
    if forall is_eqT (map snd (duplicates (op =) (maps term_vTs in_ts))) andalso
      forall (is_eqT o fastype_of) in_ts'
    then
      (case check_mode_prems (union (op =) arg_vs in_vs) rnd ps of
        NONE => NONE
      | SOME (vs, rnd') =>
          let val missing_vs = missing_vars vs ts
          in
            if null missing_vs orelse
              use_random codegen_mode andalso monomorphic_vars missing_vs
            then SOME (rnd' orelse not (null missing_vs))
            else NONE
          end)
    else NONE
  end;

fun check_modes_pred thy codegen_mode arg_vs preds modes (p, ms) =
  let val SOME rs = AList.lookup (op =) preds p in
    (p, map_filter (fn m as (m', _) =>
      let val xs = map (check_mode_clause thy codegen_mode arg_vs modes m) rs in
        (case find_index is_none xs of
          ~1 => SOME (m', exists (fn SOME b => b) xs)
        | i => (Codegen.message ("Clause " ^ string_of_int (i+1) ^ " of " ^
          p ^ " violates mode " ^ string_of_mode m'); NONE))
      end) ms)
  end;

fun fixp f (x : (string * ((int list option list * int list) * bool) list) list) =
  let val y = f x
  in if x = y then x else fixp f y end;

fun infer_modes thy codegen_mode extra_modes arities arg_vs preds = fixp (fn modes =>
  map (check_modes_pred thy codegen_mode arg_vs preds (modes @ extra_modes)) modes)
    (map (fn (s, (ks, k)) => (s, map (rpair false) (cprod (cprods (map
      (fn NONE => [NONE]
        | SOME k' => map SOME (subsets 1 k')) ks),
      subsets 1 k)))) arities);


(**** code generation ****)

fun mk_eq (x::xs) =
  let
    fun mk_eqs _ [] = []
      | mk_eqs a (b :: cs) = Codegen.str (a ^ " = " ^ b) :: mk_eqs b cs;
  in mk_eqs x xs end;

fun mk_tuple xs =
  Pretty.block (Codegen.str "(" ::
    flat (separate [Codegen.str ",", Pretty.brk 1] (map single xs)) @
    [Codegen.str ")"]);

fun mk_v s (names, vs) =
  (case AList.lookup (op =) vs s of
    NONE => (s, (names, (s, [s])::vs))
  | SOME xs =>
      let val s' = singleton (Name.variant_list names) s
      in (s', (s'::names, AList.update (op =) (s, s'::xs) vs)) end);

fun distinct_v (Var ((s, 0), T)) nvs =
      let val (s', nvs') = mk_v s nvs
      in (Var ((s', 0), T), nvs') end
  | distinct_v (t $ u) nvs =
      let
        val (t', nvs') = distinct_v t nvs;
        val (u', nvs'') = distinct_v u nvs';
      in (t' $ u', nvs'') end
  | distinct_v t nvs = (t, nvs);

fun is_exhaustive (Var _) = true
  | is_exhaustive (Const (@{const_name Pair}, _) $ t $ u) =
      is_exhaustive t andalso is_exhaustive u
  | is_exhaustive _ = false;

fun compile_match nvs eq_ps out_ps success_p can_fail =
  let val eqs = flat (separate [Codegen.str " andalso", Pretty.brk 1]
    (map single (maps (mk_eq o snd) nvs @ eq_ps)));
  in
    Pretty.block
     ([Codegen.str "(fn ", mk_tuple out_ps, Codegen.str " =>", Pretty.brk 1] @
      (Pretty.block ((if null eqs then [] else Codegen.str "if " ::
         [Pretty.block eqs, Pretty.brk 1, Codegen.str "then "]) @
         (success_p ::
          (if null eqs then [] else [Pretty.brk 1, Codegen.str "else DSeq.empty"]))) ::
       (if can_fail then
          [Pretty.brk 1, Codegen.str "| _ => DSeq.empty)"]
        else [Codegen.str ")"])))
  end;

fun modename module s (iss, is) gr =
  let val (id, gr') = if s = @{const_name HOL.eq} then (("", "equal"), gr)
    else Codegen.mk_const_id module s gr
  in (space_implode "__"
    (Codegen.mk_qual_id module id ::
      map (space_implode "_" o map string_of_int) (map_filter I iss @ [is])), gr')
  end;

fun mk_funcomp brack s k p = (if brack then Codegen.parens else I)
  (Pretty.block [Pretty.block ((if k = 0 then [] else [Codegen.str "("]) @
    separate (Pretty.brk 1) (Codegen.str s :: replicate k (Codegen.str "|> ???")) @
    (if k = 0 then [] else [Codegen.str ")"])), Pretty.brk 1, p]);

fun compile_expr thy codegen_mode defs dep module brack modes (NONE, t) gr =
      apfst single (Codegen.invoke_codegen thy codegen_mode defs dep module brack t gr)
  | compile_expr _ _ _ _ _ _ _ (SOME _, Var ((name, _), _)) gr =
      ([Codegen.str name], gr)
  | compile_expr thy codegen_mode
        defs dep module brack modes (SOME (Mode ((mode, _), _, ms)), t) gr =
      (case strip_comb t of
        (Const (name, _), args) =>
          if name = @{const_name HOL.eq} orelse AList.defined op = modes name then
            let
              val (args1, args2) = chop (length ms) args;
              val ((ps, mode_id), gr') =
                gr |> fold_map
                  (compile_expr thy codegen_mode defs dep module true modes) (ms ~~ args1)
                ||>> modename module name mode;
               val (ps', gr'') =
                (case mode of
                   ([], []) => ([Codegen.str "()"], gr')
                 | _ => fold_map
                     (Codegen.invoke_codegen thy codegen_mode defs dep module true) args2 gr');
             in
              ((if brack andalso not (null ps andalso null ps') then
                single o Codegen.parens o Pretty.block else I)
                  (flat (separate [Pretty.brk 1]
                    ([Codegen.str mode_id] :: ps @ map single ps'))), gr')
             end
          else
            apfst (single o mk_funcomp brack "??" (length (binder_types (fastype_of t))))
              (Codegen.invoke_codegen thy codegen_mode defs dep module true t gr)
      | _ =>
        apfst (single o mk_funcomp brack "??" (length (binder_types (fastype_of t))))
          (Codegen.invoke_codegen thy codegen_mode defs dep module true t gr));

fun compile_clause thy codegen_mode defs dep module all_vs arg_vs modes (iss, is) (ts, ps) inp gr =
  let
    val modes' = modes @ map_filter
      (fn (_, NONE) => NONE | (v, SOME js) => SOME (v, [(([], js), false)]))
        (arg_vs ~~ iss);

    fun check_constrt t (names, eqs) =
      if is_constrt thy t then (t, (names, eqs))
      else
        let val s = singleton (Name.variant_list names) "x";
        in (Var ((s, 0), fastype_of t), (s::names, (s, t)::eqs)) end;

    fun compile_eq (s, t) gr =
      apfst (Pretty.block o cons (Codegen.str (s ^ " = ")) o single)
        (Codegen.invoke_codegen thy codegen_mode defs dep module false t gr);

    val (in_ts, out_ts) = get_args is 1 ts;
    val (in_ts', (all_vs', eqs)) = fold_map check_constrt in_ts (all_vs, []);

    fun compile_prems out_ts' vs names [] gr =
          let
            val (out_ps, gr2) =
              fold_map (Codegen.invoke_codegen thy codegen_mode defs dep module false)
                out_ts gr;
            val (eq_ps, gr3) = fold_map compile_eq eqs gr2;
            val (out_ts'', (names', eqs')) = fold_map check_constrt out_ts' (names, []);
            val (out_ts''', nvs) =
              fold_map distinct_v out_ts'' (names', map (fn x => (x, [x])) vs);
            val (out_ps', gr4) =
              fold_map (Codegen.invoke_codegen thy codegen_mode defs dep module false)
                out_ts''' gr3;
            val (eq_ps', gr5) = fold_map compile_eq eqs' gr4;
            val vs' = distinct (op =) (flat (vs :: map term_vs out_ts'));
            val missing_vs = missing_vars vs' out_ts;
            val final_p = Pretty.block
              [Codegen.str "DSeq.single", Pretty.brk 1, mk_tuple out_ps]
          in
            if null missing_vs then
              (compile_match (snd nvs) (eq_ps @ eq_ps') out_ps'
                 final_p (exists (not o is_exhaustive) out_ts'''), gr5)
            else
              let
                val (pat_p, gr6) =
                  Codegen.invoke_codegen thy codegen_mode defs dep module true
                    (HOLogic.mk_tuple (map Var missing_vs)) gr5;
                val gen_p =
                  Codegen.mk_gen gr6 module true [] ""
                    (HOLogic.mk_tupleT (map snd missing_vs));
              in
                (compile_match (snd nvs) eq_ps' out_ps'
                  (Pretty.block [Codegen.str "DSeq.generator ", gen_p,
                    Codegen.str " :->", Pretty.brk 1,
                    compile_match [] eq_ps [pat_p] final_p false])
                  (exists (not o is_exhaustive) out_ts'''),
                 gr6)
              end
          end
      | compile_prems out_ts vs names ps gr =
          let
            val vs' = distinct (op =) (flat (vs :: map term_vs out_ts));
            val (out_ts', (names', eqs)) = fold_map check_constrt out_ts (names, []);
            val (out_ts'', nvs) =
              fold_map distinct_v out_ts' (names', map (fn x => (x, [x])) vs);
            val (out_ps, gr0) =
              fold_map (Codegen.invoke_codegen thy codegen_mode defs dep module false)
                out_ts'' gr;
            val (eq_ps, gr1) = fold_map compile_eq eqs gr0;
          in
            (case hd (select_mode_prem thy modes' vs' ps) of
              (p as Prem (us, t, is_set), (mode as Mode (_, js, _), []) :: _) =>
                let
                  val ps' = filter_out (equal p) ps;
                  val (in_ts, out_ts''') = get_args js 1 us;
                  val (in_ps, gr2) =
                    fold_map (Codegen.invoke_codegen thy codegen_mode defs dep module true)
                      in_ts gr1;
                  val (ps, gr3) =
                    if not is_set then
                      apfst (fn ps => ps @
                          (if null in_ps then [] else [Pretty.brk 1]) @
                          separate (Pretty.brk 1) in_ps)
                        (compile_expr thy codegen_mode defs dep module false modes
                          (SOME mode, t) gr2)
                    else
                      apfst (fn p =>
                        Pretty.breaks [Codegen.str "DSeq.of_list", Codegen.str "(case", p,
                        Codegen.str "of", Codegen.str "Set", Codegen.str "xs", Codegen.str "=>",
                        Codegen.str "xs)"])
                        (*this is a very strong assumption about the generated code!*)
                        (Codegen.invoke_codegen thy codegen_mode defs dep module true t gr2);
                   val (rest, gr4) = compile_prems out_ts''' vs' (fst nvs) ps' gr3;
                 in
                   (compile_match (snd nvs) eq_ps out_ps
                     (Pretty.block (ps @
                       [Codegen.str " :->", Pretty.brk 1, rest]))
                       (exists (not o is_exhaustive) out_ts''), gr4)
                 end
            | (p as Sidecond t, [(_, [])]) =>
                let
                  val ps' = filter_out (equal p) ps;
                  val (side_p, gr2) =
                    Codegen.invoke_codegen thy codegen_mode defs dep module true t gr1;
                  val (rest, gr3) = compile_prems [] vs' (fst nvs) ps' gr2;
                in
                  (compile_match (snd nvs) eq_ps out_ps
                    (Pretty.block [Codegen.str "?? ", side_p,
                      Codegen.str " :->", Pretty.brk 1, rest])
                    (exists (not o is_exhaustive) out_ts''), gr3)
                end
            | (_, (_, missing_vs) :: _) =>
                let
                  val T = HOLogic.mk_tupleT (map snd missing_vs);
                  val (_, gr2) =
                    Codegen.invoke_tycodegen thy codegen_mode defs dep module false T gr1;
                  val gen_p = Codegen.mk_gen gr2 module true [] "" T;
                  val (rest, gr3) = compile_prems
                    [HOLogic.mk_tuple (map Var missing_vs)] vs' (fst nvs) ps gr2;
                in
                  (compile_match (snd nvs) eq_ps out_ps
                    (Pretty.block [Codegen.str "DSeq.generator", Pretty.brk 1,
                      gen_p, Codegen.str " :->", Pretty.brk 1, rest])
                    (exists (not o is_exhaustive) out_ts''), gr3)
                end)
          end;

    val (prem_p, gr') = compile_prems in_ts' arg_vs all_vs' ps gr ;
  in
    (Pretty.block [Codegen.str "DSeq.single", Pretty.brk 1, inp,
       Codegen.str " :->", Pretty.brk 1, prem_p], gr')
  end;

fun compile_pred thy codegen_mode defs dep module prfx all_vs arg_vs modes s cls mode gr =
  let
    val xs = map Codegen.str (Name.variant_list arg_vs
      (map (fn i => "x" ^ string_of_int i) (snd mode)));
    val ((cl_ps, mode_id), gr') = gr |>
      fold_map (fn cl => compile_clause thy codegen_mode defs
        dep module all_vs arg_vs modes mode cl (mk_tuple xs)) cls ||>>
      modename module s mode
  in
    (Pretty.block
      ([Pretty.block (separate (Pretty.brk 1)
         (Codegen.str (prfx ^ mode_id) ::
           map Codegen.str arg_vs @
           (case mode of ([], []) => [Codegen.str "()"] | _ => xs)) @
         [Codegen.str " ="]),
        Pretty.brk 1] @
       flat (separate [Codegen.str " ++", Pretty.brk 1] (map single cl_ps))), (gr', "and "))
  end;

fun compile_preds thy codegen_mode defs dep module all_vs arg_vs modes preds gr =
  let val (prs, (gr', _)) = fold_map (fn (s, cls) =>
    fold_map (fn (mode, _) => fn (gr', prfx') => compile_pred thy codegen_mode defs
      dep module prfx' all_vs arg_vs modes s cls mode gr')
        (((the o AList.lookup (op =) modes) s))) preds (gr, "fun ")
  in
    (space_implode "\n\n" (map Codegen.string_of (flat prs)) ^ ";\n\n", gr')
  end;

(**** processing of introduction rules ****)

exception Modes of
  (string * ((int list option list * int list) * bool) list) list *
  (string * (int option list * int)) list;

fun lookup_modes gr dep = apfst flat (apsnd flat (ListPair.unzip
  (map ((fn (SOME (Modes x), _, _) => x | _ => ([], [])) o Codegen.get_node gr)
    (Graph.all_preds (fst gr) [dep]))));

fun print_arities arities = Codegen.message ("Arities:\n" ^
  cat_lines (map (fn (s, (ks, k)) => s ^ ": " ^
    space_implode " -> " (map
      (fn NONE => "X" | SOME k' => string_of_int k')
        (ks @ [SOME k]))) arities));

fun prep_intrs intrs =
  map (Codegen.rename_term o Thm.prop_of o Drule.export_without_context) intrs;

fun constrain cs [] = []
  | constrain cs ((s, xs) :: ys) =
      (s,
        (case AList.lookup (op =) cs (s : string) of
          NONE => xs
        | SOME xs' => inter (op = o apfst fst) xs' xs)) :: constrain cs ys;

fun mk_extra_defs thy codegen_mode defs gr dep names module ts =
  fold (fn name => fn gr =>
    if member (op =) names name then gr
    else
      (case get_clauses thy name of
        NONE => gr
      | SOME (names, thyname, nparms, intrs) =>
          mk_ind_def thy codegen_mode defs gr dep names
            (Codegen.if_library codegen_mode thyname module)
            [] (prep_intrs intrs) nparms))
    (fold Term.add_const_names ts []) gr

and mk_ind_def thy codegen_mode defs gr dep names module modecs intrs nparms =
  Codegen.add_edge_acyclic (hd names, dep) gr handle
    Graph.CYCLES (xs :: _) =>
      error ("Inductive_Codegen: illegal cyclic dependencies:\n" ^ commas xs)
  | Graph.UNDEF _ =>
    let
      val _ $ u = Logic.strip_imp_concl (hd intrs);
      val args = List.take (snd (strip_comb u), nparms);
      val arg_vs = maps term_vs args;

      fun get_nparms s = if member (op =) names s then SOME nparms else
        Option.map #3 (get_clauses thy s);

      fun dest_prem (_ $ (Const (@{const_name Set.member}, _) $ t $ u)) =
            Prem ([t], Envir.beta_eta_contract u, true)
        | dest_prem (_ $ ((eq as Const (@{const_name HOL.eq}, _)) $ t $ u)) =
            Prem ([t, u], eq, false)
        | dest_prem (_ $ t) =
            (case strip_comb t of
              (v as Var _, ts) =>
                if member (op =) args v then Prem (ts, v, false) else Sidecond t
            | (c as Const (s, _), ts) =>
                (case get_nparms s of
                  NONE => Sidecond t
                | SOME k =>
                    let val (ts1, ts2) = chop k ts
                    in Prem (ts2, list_comb (c, ts1), false) end)
            | _ => Sidecond t);

      fun add_clause intr (clauses, arities) =
        let
          val _ $ t = Logic.strip_imp_concl intr;
          val (Const (name, T), ts) = strip_comb t;
          val (ts1, ts2) = chop nparms ts;
          val prems = map dest_prem (Logic.strip_imp_prems intr);
          val (Ts, Us) = chop nparms (binder_types T)
        in
          (AList.update op = (name, these (AList.lookup op = clauses name) @
             [(ts2, prems)]) clauses,
           AList.update op = (name, (map (fn U =>
              (case strip_type U of
                (Rs as _ :: _, @{typ bool}) => SOME (length Rs)
              | _ => NONE)) Ts,
             length Us)) arities)
        end;

      val gr' = mk_extra_defs thy codegen_mode defs
        (Codegen.add_edge (hd names, dep)
          (Codegen.new_node (hd names, (NONE, "", "")) gr)) (hd names) names module intrs;
      val (extra_modes, extra_arities) = lookup_modes gr' (hd names);
      val (clauses, arities) = fold add_clause intrs ([], []);
      val modes = constrain modecs
        (infer_modes thy codegen_mode extra_modes arities arg_vs clauses);
      val _ = print_arities arities;
      val _ = print_modes modes;
      val (s, gr'') =
        compile_preds thy codegen_mode defs (hd names) module (terms_vs intrs)
          arg_vs (modes @ extra_modes) clauses gr';
    in
      (Codegen.map_node (hd names)
        (K (SOME (Modes (modes, arities)), module, s)) gr'')
    end;

fun find_mode gr dep s u modes is =
  (case find_first (fn Mode (_, js, _) => is = js) (modes_of modes u handle Option => []) of
    NONE =>
      Codegen.codegen_error gr dep
        ("No such mode for " ^ s ^ ": " ^ string_of_mode ([], is))
  | mode => mode);

fun mk_ind_call thy codegen_mode defs dep module is_query s T ts names thyname k intrs gr =
  let
    val (ts1, ts2) = chop k ts;
    val u = list_comb (Const (s, T), ts1);

    fun mk_mode (Const (@{const_name dummy_pattern}, _)) ((ts, mode), i) =
          ((ts, mode), i + 1)
      | mk_mode t ((ts, mode), i) = ((ts @ [t], mode @ [i]), i + 1);

    val module' = Codegen.if_library codegen_mode thyname module;
    val gr1 =
      mk_extra_defs thy codegen_mode defs
        (mk_ind_def thy codegen_mode defs gr dep names module'
        [] (prep_intrs intrs) k) dep names module' [u];
    val (modes, _) = lookup_modes gr1 dep;
    val (ts', is) =
      if is_query then fst (fold mk_mode ts2 (([], []), 1))
      else (ts2, 1 upto length (binder_types T) - k);
    val mode = find_mode gr1 dep s u modes is;
    val _ = if is_query orelse not (needs_random (the mode)) then ()
      else warning ("Illegal use of random data generators in " ^ s);
    val (in_ps, gr2) =
      fold_map (Codegen.invoke_codegen thy codegen_mode defs dep module true)
        ts' gr1;
    val (ps, gr3) =
      compile_expr thy codegen_mode defs dep module false modes (mode, u) gr2;
  in
    (Pretty.block (ps @ (if null in_ps then [] else [Pretty.brk 1]) @
       separate (Pretty.brk 1) in_ps), gr3)
  end;

fun clause_of_eqn eqn =
  let
    val (t, u) = HOLogic.dest_eq (HOLogic.dest_Trueprop (concl_of eqn));
    val (Const (s, T), ts) = strip_comb t;
    val (Ts, U) = strip_type T
  in
    Codegen.rename_term (Logic.list_implies (prems_of eqn, HOLogic.mk_Trueprop
      (list_comb (Const (s ^ "_aux", Ts @ [U] ---> HOLogic.boolT), ts @ [u]))))
  end;

fun mk_fun thy codegen_mode defs name eqns dep module module' gr =
  (case try (Codegen.get_node gr) name of
    NONE =>
      let
        val clauses = map clause_of_eqn eqns;
        val pname = name ^ "_aux";
        val arity =
          length (snd (strip_comb (fst (HOLogic.dest_eq
            (HOLogic.dest_Trueprop (concl_of (hd eqns)))))));
        val mode = 1 upto arity;
        val ((fun_id, mode_id), gr') = gr |>
          Codegen.mk_const_id module' name ||>>
          modename module' pname ([], mode);
        val vars = map (fn i => Codegen.str ("x" ^ string_of_int i)) mode;
        val s = Codegen.string_of (Pretty.block
          [Codegen.mk_app false (Codegen.str ("fun " ^ snd fun_id)) vars, Codegen.str " =",
           Pretty.brk 1, Codegen.str "DSeq.hd", Pretty.brk 1,
           Codegen.parens (Pretty.block (separate (Pretty.brk 1) (Codegen.str mode_id ::
             vars)))]) ^ ";\n\n";
        val gr'' = mk_ind_def thy codegen_mode defs (Codegen.add_edge (name, dep)
          (Codegen.new_node (name, (NONE, module', s)) gr')) name [pname] module'
          [(pname, [([], mode)])] clauses 0;
        val (modes, _) = lookup_modes gr'' dep;
        val _ = find_mode gr'' dep pname (head_of (HOLogic.dest_Trueprop
          (Logic.strip_imp_concl (hd clauses)))) modes mode
      in (Codegen.mk_qual_id module fun_id, gr'') end
  | SOME _ =>
      (Codegen.mk_qual_id module (Codegen.get_const_id gr name),
        Codegen.add_edge (name, dep) gr));

(* convert n-tuple to nested pairs *)

fun conv_ntuple fs ts p =
  let
    val k = length fs;
    val xs = map_range (fn i => Codegen.str ("x" ^ string_of_int i)) (k + 1);
    val xs' = map (fn Bound i => nth xs (k - i)) ts;
    fun conv xs js =
      if member (op =) fs js then
        let
          val (p, xs') = conv xs (1::js);
          val (q, xs'') = conv xs' (2::js)
        in (mk_tuple [p, q], xs'') end
      else (hd xs, tl xs)
  in
    if k > 0 then
      Pretty.block
        [Codegen.str "DSeq.map (fn", Pretty.brk 1,
         mk_tuple xs', Codegen.str " =>", Pretty.brk 1, fst (conv xs []),
         Codegen.str ")", Pretty.brk 1, Codegen.parens p]
    else p
  end;

fun inductive_codegen thy codegen_mode defs dep module brack t gr =
  (case strip_comb t of
    (Const (@{const_name Collect}, _), [u]) =>
      let val (r, Ts, fs) = HOLogic.strip_psplits u in
        (case strip_comb r of
          (Const (s, T), ts) =>
            (case (get_clauses thy s, Codegen.get_assoc_code thy (s, T)) of
              (SOME (names, thyname, k, intrs), NONE) =>
                let
                  val (ts1, ts2) = chop k ts;
                  val ts2' = map
                    (fn Bound i => Term.dummy_pattern (nth Ts (length Ts - i - 1)) | t => t) ts2;
                  val (ots, its) = List.partition is_Bound ts2;
                  val closed = forall (not o Term.is_open);
                in
                  if null (duplicates op = ots) andalso
                    closed ts1 andalso closed its
                  then
                    let
                      val (call_p, gr') =
                        mk_ind_call thy codegen_mode defs dep module true
                          s T (ts1 @ ts2') names thyname k intrs gr;
                    in
                      SOME ((if brack then Codegen.parens else I) (Pretty.block
                        [Codegen.str "Set", Pretty.brk 1, Codegen.str "(DSeq.list_of", Pretty.brk 1,
                         Codegen.str "(", conv_ntuple fs ots call_p, Codegen.str "))"]),
                         (*this is a very strong assumption about the generated code!*)
                         gr')
                    end
                  else NONE
                end
            | _ => NONE)
        | _ => NONE)
      end
  | (Const (s, T), ts) =>
      (case Symtab.lookup (#eqns (CodegenData.get thy)) s of
        NONE =>
          (case (get_clauses thy s, Codegen.get_assoc_code thy (s, T)) of
            (SOME (names, thyname, k, intrs), NONE) =>
              if length ts < k then NONE else
                SOME
                  (let
                    val (call_p, gr') = mk_ind_call thy codegen_mode defs dep module false
                      s T (map Term.no_dummy_patterns ts) names thyname k intrs gr
                   in
                    (mk_funcomp brack "?!"
                      (length (binder_types T) - length ts) (Codegen.parens call_p), gr')
                   end
                   handle TERM _ =>
                    mk_ind_call thy codegen_mode defs dep module true
                      s T ts names thyname k intrs gr)
          | _ => NONE)
      | SOME eqns =>
          let
            val (_, thyname) :: _ = eqns;
            val (id, gr') =
              mk_fun thy codegen_mode defs s (Codegen.preprocess thy (map fst (rev eqns)))
                dep module (Codegen.if_library codegen_mode thyname module) gr;
            val (ps, gr'') =
              fold_map (Codegen.invoke_codegen thy codegen_mode defs dep module true)
                ts gr';
          in SOME (Codegen.mk_app brack (Codegen.str id) ps, gr'') end)
  | _ => NONE);

val setup =
  Codegen.add_codegen "inductive" inductive_codegen #>
  Attrib.setup @{binding code_ind}
    (Scan.lift (Scan.option (Args.$$$ "target" |-- Args.colon |-- Args.name) --
      Scan.option (Args.$$$ "params" |-- Args.colon |-- Parse.nat) >> uncurry add))
    "introduction rules for executable predicates";


(**** Quickcheck involving inductive predicates ****)

structure Result = Proof_Data
(
  type T = int * int * int -> term list option;
  fun init _ = (fn _ => NONE);
);

val get_test_fn = Result.get;
fun poke_test_fn f = Context.>> (Context.map_proof (Result.put f));


fun strip_imp p =
  let val (q, r) = HOLogic.dest_imp p
  in strip_imp r |>> cons q end
  handle TERM _ => ([], p);

fun deepen bound f i =
  if i > bound then NONE
  else
    (case f i of
      NONE => deepen bound f (i + 1)
    | SOME x => SOME x);

val active = Attrib.setup_config_bool @{binding quickcheck_SML_inductive_active} (K false);
    
val depth_bound = Attrib.setup_config_int @{binding quickcheck_ind_depth} (K 10);
val depth_start = Attrib.setup_config_int @{binding quickcheck_ind_depth_start} (K 1);
val random_values = Attrib.setup_config_int @{binding quickcheck_ind_random} (K 5);
val size_offset = Attrib.setup_config_int @{binding quickcheck_ind_size_offset} (K 0);

fun test_term ctxt [(t, [])] =
      let
        val t' = fold_rev absfree (Term.add_frees t []) t;
        val thy = Proof_Context.theory_of ctxt;
        val (xs, p) = strip_abs t';
        val args' = map_index (fn (i, (_, T)) => ("arg" ^ string_of_int i, T)) xs;
        val args = map Free args';
        val (ps, q) = strip_imp p;
        val Ts = map snd xs;
        val T = Ts ---> HOLogic.boolT;
        val rl = Logic.list_implies
          (map (HOLogic.mk_Trueprop o curry subst_bounds (rev args)) ps @
           [HOLogic.mk_Trueprop (HOLogic.mk_not (subst_bounds (rev args, q)))],
           HOLogic.mk_Trueprop (list_comb (Free ("quickcheckp", T), args)));
        val (_, thy') = Inductive.add_inductive_global
          {quiet_mode=true, verbose=false, alt_name=Binding.empty, coind=false,
           no_elim=true, no_ind=false, skip_mono=false, fork_mono=false}
          [((@{binding quickcheckp}, T), NoSyn)] []
          [(Attrib.empty_binding, rl)] [] (Theory.copy thy);
        val pred = HOLogic.mk_Trueprop (list_comb
          (Const (Sign.intern_const thy' "quickcheckp", T),
           map Term.dummy_pattern Ts));
        val (code, gr) =
          Codegen.generate_code_i thy' ["term_of", "test", "random_ind"] [] "Generated"
            [("testf", pred)];
        val s = "structure Test_Term =\nstruct\n\n" ^
          cat_lines (map snd code) ^
          "\nopen Generated;\n\n" ^ Codegen.string_of
            (Pretty.block [Codegen.str "val () = Inductive_Codegen.poke_test_fn",
              Pretty.brk 1, Codegen.str "(fn p =>", Pretty.brk 1,
              Codegen.str "case Seq.pull (testf p) of", Pretty.brk 1,
              Codegen.str "SOME ",
              mk_tuple [mk_tuple (map (Codegen.str o fst) args'), Codegen.str "_"],
              Codegen.str " =>", Pretty.brk 1, Codegen.str "SOME ",
              Pretty.enum "," "[" "]"
                (map (fn (s, T) => Pretty.block
                  [Codegen.mk_term_of gr "Generated" false T, Pretty.brk 1, Codegen.str s]) args'),
              Pretty.brk 1,
              Codegen.str "| NONE => NONE);"]) ^
          "\n\nend;\n";
        val test_fn =
          ctxt
          |> Context.proof_map
              (ML_Context.exec (fn () => ML_Context.eval_text false Position.none s))
          |> get_test_fn;
        val values = Config.get ctxt random_values;
        val bound = Config.get ctxt depth_bound;
        val start = Config.get ctxt depth_start;
        val offset = Config.get ctxt size_offset;
        fun test [k] = (deepen bound (fn i =>
          (Output.urgent_message ("Search depth: " ^ string_of_int i);
           test_fn (i, values, k+offset))) start, NONE);
      in test end
  | test_term ctxt [_] = error "Option eval is not supported by tester SML_inductive"
  | test_term ctxt _ =
      error "Compilation of multiple instances is not supported by tester SML_inductive";

end;
