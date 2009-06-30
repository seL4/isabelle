(*  Title:      HOL/Tools/inductive_codegen.ML
    Author:     Stefan Berghofer, TU Muenchen

Code generator for inductive predicates.
*)

signature INDUCTIVE_CODEGEN =
sig
  val add : string option -> int option -> attribute
  val setup : theory -> theory
end;

structure InductiveCodegen : INDUCTIVE_CODEGEN =
struct

open Codegen;

(**** theory data ****)

fun merge_rules tabs =
  Symtab.join (fn _ => AList.merge (Thm.eq_thm_prop) (K true)) tabs;

structure CodegenData = TheoryDataFun
(
  type T =
    {intros : (thm * (string * int)) list Symtab.table,
     graph : unit Graph.T,
     eqns : (thm * string) list Symtab.table};
  val empty =
    {intros = Symtab.empty, graph = Graph.empty, eqns = Symtab.empty};
  val copy = I;
  val extend = I;
  fun merge _ ({intros=intros1, graph=graph1, eqns=eqns1},
    {intros=intros2, graph=graph2, eqns=eqns2}) =
    {intros = merge_rules (intros1, intros2),
     graph = Graph.merge (K true) (graph1, graph2),
     eqns = merge_rules (eqns1, eqns2)};
);


fun warn thm = warning ("InductiveCodegen: Not a proper clause:\n" ^
  Display.string_of_thm thm);

fun add_node (g, x) = Graph.new_node (x, ()) g handle Graph.DUP _ => g;

fun add optmod optnparms = Thm.declaration_attribute (fn thm => Context.mapping (fn thy =>
  let
    val {intros, graph, eqns} = CodegenData.get thy;
    fun thyname_of s = (case optmod of
      NONE => Codegen.thyname_of_const thy s | SOME s => s);
  in (case Option.map strip_comb (try HOLogic.dest_Trueprop (concl_of thm)) of
      SOME (Const ("op =", _), [t, _]) => (case head_of t of
        Const (s, _) =>
          CodegenData.put {intros = intros, graph = graph,
             eqns = eqns |> Symtab.map_default (s, [])
               (AList.update Thm.eq_thm_prop (thm, thyname_of s))} thy
      | _ => (warn thm; thy))
    | SOME (Const (s, _), _) =>
        let
          val cs = fold Term.add_const_names (Thm.prems_of thm) [];
          val rules = Symtab.lookup_list intros s;
          val nparms = (case optnparms of
            SOME k => k
          | NONE => (case rules of
             [] => (case try (Inductive.the_inductive (ProofContext.init thy)) s of
                 SOME (_, {raw_induct, ...}) =>
                   length (Inductive.params_of raw_induct)
               | NONE => 0)
            | xs => snd (snd (snd (split_last xs)))))
        in CodegenData.put
          {intros = intros |>
           Symtab.update (s, (AList.update Thm.eq_thm_prop
             (thm, (thyname_of s, nparms)) rules)),
           graph = List.foldr (uncurry (Graph.add_edge o pair s))
             (Library.foldl add_node (graph, s :: cs)) cs,
           eqns = eqns} thy
        end
    | _ => (warn thm; thy))
  end) I);

fun get_clauses thy s =
  let val {intros, graph, ...} = CodegenData.get thy
  in case Symtab.lookup intros s of
      NONE => (case try (Inductive.the_inductive (ProofContext.init thy)) s of
        NONE => NONE
      | SOME ({names, ...}, {intrs, raw_induct, ...}) =>
          SOME (names, Codegen.thyname_of_const thy s,
            length (Inductive.params_of raw_induct),
            preprocess thy intrs))
    | SOME _ =>
        let
          val SOME names = find_first
            (fn xs => member (op =) xs s) (Graph.strong_conn graph);
          val intrs as (_, (thyname, nparms)) :: _ =
            maps (the o Symtab.lookup intros) names;
        in SOME (names, thyname, nparms, preprocess thy (map fst (rev intrs))) end
  end;


(**** check if a term contains only constructor functions ****)

fun is_constrt thy =
  let
    val cnstrs = flat (maps
      (map (fn (_, (_, _, cs)) => map (apsnd length) cs) o #descr o snd)
      (Symtab.dest (Datatype.get_all thy)));
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
  cat_lines (map (fn (s, ms) => s ^ ": " ^ commas (map
    string_of_mode ms)) modes));

val term_vs = map (fst o fst o dest_Var) o OldTerm.term_vars;
val terms_vs = distinct (op =) o List.concat o (map term_vs);

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

fun cprods xss = List.foldr (map op :: o cprod) [[]] xss;

datatype mode = Mode of (int list option list * int list) * int list * mode option list;

fun modes_of modes t =
  let
    val ks = 1 upto length (binder_types (fastype_of t));
    val default = [Mode (([], ks), ks, [])];
    fun mk_modes name args = Option.map (List.concat o
      map (fn (m as (iss, is)) =>
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
              | (SOME js, arg) => map SOME (List.filter
                  (fn Mode (_, js', _) => js=js') (modes_of modes arg)))
                    (iss ~~ args1)))
          end
        end)) (AList.lookup op = modes name)

  in (case strip_comb t of
      (Const ("op =", Type (_, [T, _])), _) =>
        [Mode (([], [1]), [1], []), Mode (([], [2]), [2], [])] @
        (if is_eqT T then [Mode (([], [1, 2]), [1, 2], [])] else [])
    | (Const (name, _), args) => the_default default (mk_modes name args)
    | (Var ((name, _), _), args) => the (mk_modes name args)
    | (Free (name, _), args) => the (mk_modes name args)
    | _ => default)
  end;

datatype indprem = Prem of term list * term * bool | Sidecond of term;

fun select_mode_prem thy modes vs ps =
  find_first (is_some o snd) (ps ~~ map
    (fn Prem (us, t, is_set) => find_first (fn Mode (_, is, _) =>
          let
            val (in_ts, out_ts) = get_args is 1 us;
            val (out_ts', in_ts') = List.partition (is_constrt thy) out_ts;
            val vTs = List.concat (map term_vTs out_ts');
            val dupTs = map snd (duplicates (op =) vTs) @
              List.mapPartial (AList.lookup (op =) vTs) vs;
          in
            terms_vs (in_ts @ in_ts') subset vs andalso
            forall (is_eqT o fastype_of) in_ts' andalso
            term_vs t subset vs andalso
            forall is_eqT dupTs
          end)
            (if is_set then [Mode (([], []), [], [])]
             else modes_of modes t handle Option =>
               error ("Bad predicate: " ^ Syntax.string_of_term_global thy t))
      | Sidecond t => if term_vs t subset vs then SOME (Mode (([], []), [], []))
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
            (case x of Prem (us, _, _) => vs union terms_vs us | _ => vs)
            (filter_out (equal x) ps));
    val (in_ts, in_ts') = List.partition (is_constrt thy) (fst (get_args is 1 ts));
    val in_vs = terms_vs in_ts;
    val concl_vs = terms_vs ts
  in
    forall is_eqT (map snd (duplicates (op =) (List.concat (map term_vTs in_ts)))) andalso
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

fun fixp f (x : (string * (int list option list * int list) list) list) =
  let val y = f x
  in if x = y then x else fixp f y end;

fun infer_modes thy extra_modes arities arg_vs preds = fixp (fn modes =>
  map (check_modes_pred thy arg_vs preds (modes @ extra_modes)) modes)
    (map (fn (s, (ks, k)) => (s, cprod (cprods (map
      (fn NONE => [NONE]
        | SOME k' => map SOME (subsets 1 k')) ks),
      subsets 1 k))) arities);

(**** code generation ****)

fun mk_eq (x::xs) =
  let fun mk_eqs _ [] = []
        | mk_eqs a (b::cs) = str (a ^ " = " ^ b) :: mk_eqs b cs
  in mk_eqs x xs end;

fun mk_tuple xs = Pretty.block (str "(" ::
  List.concat (separate [str ",", Pretty.brk 1] (map single xs)) @
  [str ")"]);

fun mk_v ((names, vs), s) = (case AList.lookup (op =) vs s of
      NONE => ((names, (s, [s])::vs), s)
    | SOME xs => let val s' = Name.variant names s in
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
  let val eqs = List.concat (separate [str " andalso", Pretty.brk 1]
    (map single (List.concat (map (mk_eq o snd) nvs) @ eq_ps)));
  in
    Pretty.block
     ([str "(fn ", mk_tuple out_ps, str " =>", Pretty.brk 1] @
      (Pretty.block ((if eqs=[] then [] else str "if " ::
         [Pretty.block eqs, Pretty.brk 1, str "then "]) @
         (success_p ::
          (if eqs=[] then [] else [Pretty.brk 1, str "else DSeq.empty"]))) ::
       (if can_fail then
          [Pretty.brk 1, str "| _ => DSeq.empty)"]
        else [str ")"])))
  end;

fun modename module s (iss, is) gr =
  let val (id, gr') = if s = @{const_name "op ="} then (("", "equal"), gr)
    else mk_const_id module s gr
  in (space_implode "__"
    (mk_qual_id module id ::
      map (space_implode "_" o map string_of_int) (List.mapPartial I iss @ [is])), gr')
  end;

fun mk_funcomp brack s k p = (if brack then parens else I)
  (Pretty.block [Pretty.block ((if k = 0 then [] else [str "("]) @
    separate (Pretty.brk 1) (str s :: replicate k (str "|> ???")) @
    (if k = 0 then [] else [str ")"])), Pretty.brk 1, p]);

fun compile_expr thy defs dep module brack modes (NONE, t) gr =
      apfst single (invoke_codegen thy defs dep module brack t gr)
  | compile_expr _ _ _ _ _ _ (SOME _, Var ((name, _), _)) gr =
      ([str name], gr)
  | compile_expr thy defs dep module brack modes (SOME (Mode (mode, _, ms)), t) gr =
      (case strip_comb t of
         (Const (name, _), args) =>
           if name = @{const_name "op ="} orelse AList.defined op = modes name then
             let
               val (args1, args2) = chop (length ms) args;
               val ((ps, mode_id), gr') = gr |> fold_map
                   (compile_expr thy defs dep module true modes) (ms ~~ args1)
                   ||>> modename module name mode;
               val (ps', gr'') = (case mode of
                   ([], []) => ([str "()"], gr')
                 | _ => fold_map
                     (invoke_codegen thy defs dep module true) args2 gr')
             in ((if brack andalso not (null ps andalso null ps') then
               single o parens o Pretty.block else I)
                 (List.concat (separate [Pretty.brk 1]
                   ([str mode_id] :: ps @ map single ps'))), gr')
             end
           else apfst (single o mk_funcomp brack "??" (length (binder_types (fastype_of t))))
             (invoke_codegen thy defs dep module true t gr)
       | _ => apfst (single o mk_funcomp brack "??" (length (binder_types (fastype_of t))))
           (invoke_codegen thy defs dep module true t gr));

fun compile_clause thy defs dep module all_vs arg_vs modes (iss, is) (ts, ps) inp gr =
  let
    val modes' = modes @ List.mapPartial
      (fn (_, NONE) => NONE | (v, SOME js) => SOME (v, [([], js)]))
        (arg_vs ~~ iss);

    fun check_constrt ((names, eqs), t) =
      if is_constrt thy t then ((names, eqs), t) else
        let val s = Name.variant names "x";
        in ((s::names, (s, t)::eqs), Var ((s, 0), fastype_of t)) end;

    fun compile_eq (s, t) gr =
      apfst (Pretty.block o cons (str (s ^ " = ")) o single)
        (invoke_codegen thy defs dep module false t gr);

    val (in_ts, out_ts) = get_args is 1 ts;
    val ((all_vs', eqs), in_ts') =
      Library.foldl_map check_constrt ((all_vs, []), in_ts);

    fun compile_prems out_ts' vs names [] gr =
          let
            val (out_ps, gr2) = fold_map
              (invoke_codegen thy defs dep module false) out_ts gr;
            val (eq_ps, gr3) = fold_map compile_eq eqs gr2;
            val ((names', eqs'), out_ts'') =
              Library.foldl_map check_constrt ((names, []), out_ts');
            val (nvs, out_ts''') = Library.foldl_map distinct_v
              ((names', map (fn x => (x, [x])) vs), out_ts'');
            val (out_ps', gr4) = fold_map
              (invoke_codegen thy defs dep module false) (out_ts''') gr3;
            val (eq_ps', gr5) = fold_map compile_eq eqs' gr4;
          in
            (compile_match (snd nvs) (eq_ps @ eq_ps') out_ps'
              (Pretty.block [str "DSeq.single", Pretty.brk 1, mk_tuple out_ps])
              (exists (not o is_exhaustive) out_ts'''), gr5)
          end
      | compile_prems out_ts vs names ps gr =
          let
            val vs' = distinct (op =) (flat (vs :: map term_vs out_ts));
            val SOME (p, mode as SOME (Mode (_, js, _))) =
              select_mode_prem thy modes' vs' ps;
            val ps' = filter_out (equal p) ps;
            val ((names', eqs), out_ts') =
              Library.foldl_map check_constrt ((names, []), out_ts);
            val (nvs, out_ts'') = Library.foldl_map distinct_v
              ((names', map (fn x => (x, [x])) vs), out_ts');
            val (out_ps, gr0) = fold_map
              (invoke_codegen thy defs dep module false) out_ts'' gr;
            val (eq_ps, gr1) = fold_map compile_eq eqs gr0;
          in
            (case p of
               Prem (us, t, is_set) =>
                 let
                   val (in_ts, out_ts''') = get_args js 1 us;
                   val (in_ps, gr2) = fold_map
                     (invoke_codegen thy defs dep module true) in_ts gr1;
                   val (ps, gr3) =
                     if not is_set then
                       apfst (fn ps => ps @
                           (if null in_ps then [] else [Pretty.brk 1]) @
                           separate (Pretty.brk 1) in_ps)
                         (compile_expr thy defs dep module false modes
                           (mode, t) gr2)
                     else
                       apfst (fn p => Pretty.breaks [str "DSeq.of_list", str "(case", p,
                         str "of", str "Set", str "xs", str "=>", str "xs)"])
                         (*this is a very strong assumption about the generated code!*)
                           (invoke_codegen thy defs dep module true t gr2);
                   val (rest, gr4) = compile_prems out_ts''' vs' (fst nvs) ps' gr3;
                 in
                   (compile_match (snd nvs) eq_ps out_ps
                      (Pretty.block (ps @
                         [str " :->", Pretty.brk 1, rest]))
                      (exists (not o is_exhaustive) out_ts''), gr4)
                 end
             | Sidecond t =>
                 let
                   val (side_p, gr2) = invoke_codegen thy defs dep module true t gr1;
                   val (rest, gr3) = compile_prems [] vs' (fst nvs) ps' gr2;
                 in
                   (compile_match (snd nvs) eq_ps out_ps
                      (Pretty.block [str "?? ", side_p,
                        str " :->", Pretty.brk 1, rest])
                      (exists (not o is_exhaustive) out_ts''), gr3)
                 end)
          end;

    val (prem_p, gr') = compile_prems in_ts' arg_vs all_vs' ps gr ;
  in
    (Pretty.block [str "DSeq.single", Pretty.brk 1, inp,
       str " :->", Pretty.brk 1, prem_p], gr')
  end;

fun compile_pred thy defs dep module prfx all_vs arg_vs modes s cls mode gr =
  let
    val xs = map str (Name.variant_list arg_vs
      (map (fn i => "x" ^ string_of_int i) (snd mode)));
    val ((cl_ps, mode_id), gr') = gr |>
      fold_map (fn cl => compile_clause thy defs
        dep module all_vs arg_vs modes mode cl (mk_tuple xs)) cls ||>>
      modename module s mode
  in
    (Pretty.block
      ([Pretty.block (separate (Pretty.brk 1)
         (str (prfx ^ mode_id) ::
           map str arg_vs @
           (case mode of ([], []) => [str "()"] | _ => xs)) @
         [str " ="]),
        Pretty.brk 1] @
       List.concat (separate [str " ++", Pretty.brk 1] (map single cl_ps))), (gr', "and "))
  end;

fun compile_preds thy defs dep module all_vs arg_vs modes preds gr =
  let val (prs, (gr', _)) = fold_map (fn (s, cls) =>
    fold_map (fn mode => fn (gr', prfx') => compile_pred thy defs
      dep module prfx' all_vs arg_vs modes s cls mode gr')
        (((the o AList.lookup (op =) modes) s))) preds (gr, "fun ")
  in
    (space_implode "\n\n" (map string_of (List.concat prs)) ^ ";\n\n", gr')
  end;

(**** processing of introduction rules ****)

exception Modes of
  (string * (int list option list * int list) list) list *
  (string * (int option list * int)) list;

fun lookup_modes gr dep = apfst List.concat (apsnd List.concat (ListPair.unzip
  (map ((fn (SOME (Modes x), _, _) => x | _ => ([], [])) o get_node gr)
    (Graph.all_preds (fst gr) [dep]))));

fun print_arities arities = message ("Arities:\n" ^
  cat_lines (map (fn (s, (ks, k)) => s ^ ": " ^
    space_implode " -> " (map
      (fn NONE => "X" | SOME k' => string_of_int k')
        (ks @ [SOME k]))) arities));

fun prep_intrs intrs = map (rename_term o #prop o rep_thm o standard) intrs;

fun constrain cs [] = []
  | constrain cs ((s, xs) :: ys) = (s, case AList.lookup (op =) cs (s : string) of
      NONE => xs
    | SOME xs' => xs inter xs') :: constrain cs ys;

fun mk_extra_defs thy defs gr dep names module ts =
  Library.foldl (fn (gr, name) =>
    if name mem names then gr
    else (case get_clauses thy name of
        NONE => gr
      | SOME (names, thyname, nparms, intrs) =>
          mk_ind_def thy defs gr dep names (if_library thyname module)
            [] (prep_intrs intrs) nparms))
            (gr, fold Term.add_const_names ts [])

and mk_ind_def thy defs gr dep names module modecs intrs nparms =
  add_edge_acyclic (hd names, dep) gr handle
    Graph.CYCLES (xs :: _) =>
      error ("InductiveCodegen: illegal cyclic dependencies:\n" ^ commas xs)
  | Graph.UNDEF _ =>
    let
      val _ $ u = Logic.strip_imp_concl (hd intrs);
      val args = List.take (snd (strip_comb u), nparms);
      val arg_vs = List.concat (map term_vs args);

      fun get_nparms s = if s mem names then SOME nparms else
        Option.map #3 (get_clauses thy s);

      fun dest_prem (_ $ (Const ("op :", _) $ t $ u)) = Prem ([t], Envir.beta_eta_contract u, true)
        | dest_prem (_ $ ((eq as Const ("op =", _)) $ t $ u)) = Prem ([t, u], eq, false)
        | dest_prem (_ $ t) =
            (case strip_comb t of
               (v as Var _, ts) => if v mem args then Prem (ts, v, false) else Sidecond t
             | (c as Const (s, _), ts) => (case get_nparms s of
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
           AList.update op = (name, (map (fn U => (case strip_type U of
                 (Rs as _ :: _, Type ("bool", [])) => SOME (length Rs)
               | _ => NONE)) Ts,
             length Us)) arities)
        end;

      val gr' = mk_extra_defs thy defs
        (add_edge (hd names, dep)
          (new_node (hd names, (NONE, "", "")) gr)) (hd names) names module intrs;
      val (extra_modes, extra_arities) = lookup_modes gr' (hd names);
      val (clauses, arities) = fold add_clause intrs ([], []);
      val modes = constrain modecs
        (infer_modes thy extra_modes arities arg_vs clauses);
      val _ = print_arities arities;
      val _ = print_modes modes;
      val (s, gr'') = compile_preds thy defs (hd names) module (terms_vs intrs)
        arg_vs (modes @ extra_modes) clauses gr';
    in
      (map_node (hd names)
        (K (SOME (Modes (modes, arities)), module, s)) gr'')
    end;

fun find_mode gr dep s u modes is = (case find_first (fn Mode (_, js, _) => is=js)
  (modes_of modes u handle Option => []) of
     NONE => codegen_error gr dep
       ("No such mode for " ^ s ^ ": " ^ string_of_mode ([], is))
   | mode => mode);

fun mk_ind_call thy defs dep module is_query s T ts names thyname k intrs gr =
  let
    val (ts1, ts2) = chop k ts;
    val u = list_comb (Const (s, T), ts1);

    fun mk_mode (((ts, mode), i), Const ("dummy_pattern", _)) =
          ((ts, mode), i+1)
      | mk_mode (((ts, mode), i), t) = ((ts @ [t], mode @ [i]), i+1);

    val module' = if_library thyname module;
    val gr1 = mk_extra_defs thy defs
      (mk_ind_def thy defs gr dep names module'
      [] (prep_intrs intrs) k) dep names module' [u];
    val (modes, _) = lookup_modes gr1 dep;
    val (ts', is) = if is_query then
        fst (Library.foldl mk_mode ((([], []), 1), ts2))
      else (ts2, 1 upto length (binder_types T) - k);
    val mode = find_mode gr1 dep s u modes is;
    val (in_ps, gr2) = fold_map (invoke_codegen thy defs dep module true) ts' gr1;
    val (ps, gr3) = compile_expr thy defs dep module false modes (mode, u) gr2;
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
    rename_term (Logic.list_implies (prems_of eqn, HOLogic.mk_Trueprop
      (list_comb (Const (s ^ "_aux", Ts @ [U] ---> HOLogic.boolT), ts @ [u]))))
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
      val ((fun_id, mode_id), gr') = gr |>
        mk_const_id module' name ||>>
        modename module' pname ([], mode);
      val vars = map (fn i => str ("x" ^ string_of_int i)) mode;
      val s = string_of (Pretty.block
        [mk_app false (str ("fun " ^ snd fun_id)) vars, str " =",
         Pretty.brk 1, str "DSeq.hd", Pretty.brk 1,
         parens (Pretty.block (separate (Pretty.brk 1) (str mode_id ::
           vars)))]) ^ ";\n\n";
      val gr'' = mk_ind_def thy defs (add_edge (name, dep)
        (new_node (name, (NONE, module', s)) gr')) name [pname] module'
        [(pname, [([], mode)])] clauses 0;
      val (modes, _) = lookup_modes gr'' dep;
      val _ = find_mode gr'' dep pname (head_of (HOLogic.dest_Trueprop
        (Logic.strip_imp_concl (hd clauses)))) modes mode
    in (mk_qual_id module fun_id, gr'') end
  | SOME _ =>
      (mk_qual_id module (get_const_id gr name), add_edge (name, dep) gr);

(* convert n-tuple to nested pairs *)

fun conv_ntuple fs ts p =
  let
    val k = length fs;
    val xs = map (fn i => str ("x" ^ string_of_int i)) (0 upto k);
    val xs' = map (fn Bound i => nth xs (k - i)) ts;
    fun conv xs js =
      if js mem fs then
        let
          val (p, xs') = conv xs (1::js);
          val (q, xs'') = conv xs' (2::js)
        in (mk_tuple [p, q], xs'') end
      else (hd xs, tl xs)
  in
    if k > 0 then
      Pretty.block
        [str "DSeq.map (fn", Pretty.brk 1,
         mk_tuple xs', str " =>", Pretty.brk 1, fst (conv xs []),
         str ")", Pretty.brk 1, parens p]
    else p
  end;

fun inductive_codegen thy defs dep module brack t gr  = (case strip_comb t of
    (Const ("Collect", _), [u]) =>
      let val (r, Ts, fs) = HOLogic.strip_split u
      in case strip_comb r of
          (Const (s, T), ts) =>
            (case (get_clauses thy s, get_assoc_code thy (s, T)) of
              (SOME (names, thyname, k, intrs), NONE) =>
                let
                  val (ts1, ts2) = chop k ts;
                  val ts2' = map
                    (fn Bound i => Term.dummy_pattern (nth Ts i) | t => t) ts2;
                  val (ots, its) = List.partition is_Bound ts2;
                  val no_loose = forall (fn t => not (loose_bvar (t, 0)))
                in
                  if null (duplicates op = ots) andalso
                    no_loose ts1 andalso no_loose its
                  then
                    let val (call_p, gr') = mk_ind_call thy defs dep module true
                      s T (ts1 @ ts2') names thyname k intrs gr 
                    in SOME ((if brack then parens else I) (Pretty.block
                      [str "Set", Pretty.brk 1, str "(DSeq.list_of", Pretty.brk 1, str "(",
                       conv_ntuple fs ots call_p, str "))"]),
                       (*this is a very strong assumption about the generated code!*)
                       gr')
                    end
                  else NONE
                end
            | _ => NONE)
        | _ => NONE
      end
  | (Const (s, T), ts) => (case Symtab.lookup (#eqns (CodegenData.get thy)) s of
      NONE => (case (get_clauses thy s, get_assoc_code thy (s, T)) of
        (SOME (names, thyname, k, intrs), NONE) =>
          if length ts < k then NONE else SOME
            (let val (call_p, gr') = mk_ind_call thy defs dep module false
               s T (map Term.no_dummy_patterns ts) names thyname k intrs gr
             in (mk_funcomp brack "?!"
               (length (binder_types T) - length ts) (parens call_p), gr')
             end handle TERM _ => mk_ind_call thy defs dep module true
               s T ts names thyname k intrs gr )
      | _ => NONE)
    | SOME eqns =>
        let
          val (_, thyname) :: _ = eqns;
          val (id, gr') = mk_fun thy defs s (preprocess thy (map fst (rev eqns)))
            dep module (if_library thyname module) gr;
          val (ps, gr'') = fold_map
            (invoke_codegen thy defs dep module true) ts gr';
        in SOME (mk_app brack (str id) ps, gr'')
        end)
  | _ => NONE);

val setup =
  add_codegen "inductive" inductive_codegen #>
  Code.add_attribute ("ind", Scan.option (Args.$$$ "target" |-- Args.colon |-- Args.name) --
    Scan.option (Args.$$$ "params" |-- Args.colon |-- OuterParse.nat) >> uncurry add);

end;
