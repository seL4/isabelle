(*  Title:      HOL/inductive_codegen.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Code generator for inductive predicates.
*)

signature INDUCTIVE_CODEGEN =
sig
  val add : theory attribute
  val setup : (theory -> theory) list
end;

structure InductiveCodegen : INDUCTIVE_CODEGEN =
struct

open Codegen;

(**** theory data ****)

structure CodegenArgs =
struct
  val name = "HOL/inductive_codegen";
  type T = thm list Symtab.table * unit Graph.T;
  val empty = (Symtab.empty, Graph.empty);
  val copy = I;
  val prep_ext = I;
  fun merge ((tab1, graph1), (tab2, graph2)) =
    (Symtab.merge_multi Drule.eq_thm_prop (tab1, tab2),
     Graph.merge (K true) (graph1, graph2));
  fun print _ _ = ();
end;

structure CodegenData = TheoryDataFun(CodegenArgs);

fun warn thm = warning ("InductiveCodegen: Not a proper clause:\n" ^
  string_of_thm thm);

fun add_node (g, x) = Graph.new_node (x, ()) g handle Graph.DUP _ => g;

fun add (p as (thy, thm)) =
  let val (tab, graph) = CodegenData.get thy;
  in (case concl_of thm of
      _ $ (Const ("op :", _) $ _ $ t) => (case head_of t of
        Const (s, _) =>
          let val cs = foldr add_term_consts (prems_of thm, [])
          in (CodegenData.put
            (Symtab.update ((s,
               if_none (Symtab.lookup (tab, s)) [] @ [thm]), tab),
             foldr (uncurry (Graph.add_edge o pair s))
               (cs, foldl add_node (graph, s :: cs))) thy, thm)
          end
      | _ => (warn thm; p))
    | _ => (warn thm; p))
  end;

fun get_clauses thy s =
  let val (tab, graph) = CodegenData.get thy
  in case Symtab.lookup (tab, s) of
      None => (case InductivePackage.get_inductive thy s of
        None => None
      | Some ({names, ...}, {intrs, ...}) => Some (names, intrs))
    | Some _ =>
        let val Some names = find_first
          (fn xs => s mem xs) (Graph.strong_conn graph)
        in Some (names,
          flat (map (fn s => the (Symtab.lookup (tab, s))) names))
        end
  end;


(**** improper tuples ****)

fun prod_factors p (Const ("Pair", _) $ t $ u) =
      p :: prod_factors (1::p) t @ prod_factors (2::p) u
  | prod_factors p _ = [];

fun split_prod p ps t = if p mem ps then (case t of
       Const ("Pair", _) $ t $ u =>
         split_prod (1::p) ps t @ split_prod (2::p) ps u
     | _ => error "Inconsistent use of products") else [t];

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
      (Some f, (Const (name, _), args)) =>
        (case assoc (extra_fs, name) of
           None => overwrite (fs, (name, if_none
             (apsome (mg_factor f) (assoc (fs, name))) f))
         | Some (fs', f') => (mg_factor f (FFix f');
             foldl (infer_factors sg extra_fs)
               (fs, map (apsome FFix) fs' ~~ args)))
    | (Some f, (Var ((name, _), _), [])) =>
        overwrite (fs, (name, if_none
          (apsome (mg_factor f) (assoc (fs, name))) f))
    | (None, _) => fs
    | _ => err "Illegal term")
      handle Factors => err "Product factor mismatch in"
  end;

fun string_of_factors p ps = if p mem ps then
    "(" ^ string_of_factors (1::p) ps ^ ", " ^ string_of_factors (2::p) ps ^ ")"
  else "_";


(**** check if a term contains only constructor functions ****)

fun is_constrt thy =
  let
    val cnstrs = flat (flat (map
      (map (fn (_, (_, _, cs)) => map (apsnd length) cs) o #descr o snd)
      (Symtab.dest (DatatypePackage.get_datatypes thy))));
    fun check t = (case strip_comb t of
        (Var _, []) => true
      | (Const (s, _), ts) => (case assoc (cnstrs, s) of
            None => false
          | Some i => length ts = i andalso forall check ts)
      | _ => false)
  in check end;

(**** check if a type is an equality type (i.e. doesn't contain fun) ****)

fun is_eqT (Type (s, Ts)) = s <> "fun" andalso forall is_eqT Ts
  | is_eqT _ = true;

(**** mode inference ****)

val term_vs = map (fst o fst o dest_Var) o term_vars;
val terms_vs = distinct o flat o (map term_vs);

fun assoc' s tab key = (case assoc (tab, key) of
      None => error ("Unable to determine " ^ s ^ " of " ^ quote key)
    | Some x => x);

(** collect all Vars in a term (with duplicates!) **)
fun term_vTs t = map (apfst fst o dest_Var)
  (filter is_Var (foldl_aterms (op :: o Library.swap) ([], t)));

fun known_args _ _ [] = []
  | known_args vs i (t::ts) = if term_vs t subset vs then i::known_args vs (i+1) ts
      else known_args vs (i+1) ts;

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

fun cprods xss = foldr (map op :: o cprod) (xss, [[]]);

datatype mode = Mode of (int list option list * int list) * mode option list;

fun modes_of modes t =
  let
    fun mk_modes name args = flat
      (map (fn (m as (iss, is)) => map (Mode o pair m) (cprods (map
        (fn (None, _) => [None]
          | (Some js, arg) => map Some
              (filter (fn Mode ((_, js'), _) => js=js') (modes_of modes arg)))
                (iss ~~ args)))) (assoc' "modes" modes name))

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
  find_first (is_some o snd) (ps ~~ map
    (fn Prem (us, t) => find_first (fn Mode ((_, is), _) =>
          let
            val (_, out_ts) = get_args is 1 us;
            val vTs = flat (map term_vTs out_ts);
            val dupTs = map snd (duplicates vTs) @
              mapfilter (curry assoc vTs) vs;
          in
            is subset known_args vs 1 us andalso
            forall (is_constrt thy) (snd (get_args is 1 us)) andalso
            term_vs t subset vs andalso
            forall is_eqT dupTs
          end)
            (modes_of modes t)
      | Sidecond t => if term_vs t subset vs then Some (Mode (([], []), []))
          else None) ps);

fun check_mode_clause thy arg_vs modes (iss, is) (ts, ps) =
  let
    val modes' = modes @ mapfilter
      (fn (_, None) => None | (v, Some js) => Some (v, [([], js)]))
        (arg_vs ~~ iss);
    fun check_mode_prems vs [] = Some vs
      | check_mode_prems vs ps = (case select_mode_prem thy modes' vs ps of
          None => None
        | Some (x, _) => check_mode_prems
            (case x of Prem (us, _) => vs union terms_vs us | _ => vs)
            (filter_out (equal x) ps));
    val (in_ts', _) = get_args is 1 ts;
    val in_ts = filter (is_constrt thy) in_ts';
    val in_vs = terms_vs in_ts;
    val concl_vs = terms_vs ts
  in
    forall is_eqT (map snd (duplicates (flat (map term_vTs in_ts)))) andalso
    (case check_mode_prems (arg_vs union in_vs) ps of
       None => false
     | Some vs => concl_vs subset vs)
  end;

fun check_modes_pred thy arg_vs preds modes (p, ms) =
  let val Some rs = assoc (preds, p)
  in (p, filter (fn m => forall (check_mode_clause thy arg_vs modes m) rs) ms) end

fun fixp f x =
  let val y = f x
  in if x = y then x else fixp f y end;

fun infer_modes thy extra_modes factors arg_vs preds = fixp (fn modes =>
  map (check_modes_pred thy arg_vs preds (modes @ extra_modes)) modes)
    (map (fn (s, (fs, f)) => (s, cprod (cprods (map
      (fn None => [None]
        | Some f' => map Some (subsets 1 (length f' + 1))) fs),
      subsets 1 (length f + 1)))) factors);

(**** code generation ****)

fun mk_eq (x::xs) =
  let fun mk_eqs _ [] = []
        | mk_eqs a (b::cs) = Pretty.str (a ^ " = " ^ b) :: mk_eqs b cs
  in mk_eqs x xs end;

fun mk_tuple xs = Pretty.block (Pretty.str "(" ::
  flat (separate [Pretty.str ",", Pretty.brk 1] (map single xs)) @
  [Pretty.str ")"]);

fun mk_v ((names, vs), s) = (case assoc (vs, s) of
      None => ((names, (s, [s])::vs), s)
    | Some xs => let val s' = variant names s in
        ((s'::names, overwrite (vs, (s, s'::xs))), s') end);

fun distinct_v (nvs, Var ((s, 0), T)) =
      apsnd (Var o rpair T o rpair 0) (mk_v (nvs, s))
  | distinct_v (nvs, t $ u) =
      let
        val (nvs', t') = distinct_v (nvs, t);
        val (nvs'', u') = distinct_v (nvs', u);
      in (nvs'', t' $ u') end
  | distinct_v x = x;

fun compile_match nvs eq_ps out_ps success_p fail_p =
  let val eqs = flat (separate [Pretty.str " andalso", Pretty.brk 1]
    (map single (flat (map (mk_eq o snd) nvs) @ eq_ps)));
  in
    Pretty.block
     ([Pretty.str "(fn ", mk_tuple out_ps, Pretty.str " =>", Pretty.brk 1] @
      (Pretty.block ((if eqs=[] then [] else Pretty.str "if " ::
         [Pretty.block eqs, Pretty.brk 1, Pretty.str "then "]) @
         (success_p ::
          (if eqs=[] then [] else [Pretty.brk 1, Pretty.str "else ", fail_p]))) ::
       [Pretty.brk 1, Pretty.str "| _ => ", fail_p, Pretty.str ")"]))
  end;

fun modename thy s (iss, is) = space_implode "__"
  (mk_const_id (sign_of thy) s ::
    map (space_implode "_" o map string_of_int) (mapfilter I iss @ [is]));

fun compile_expr thy dep brack (gr, (None, t)) =
      apsnd single (invoke_codegen thy dep brack (gr, t))
  | compile_expr _ _ _ (gr, (Some _, Var ((name, _), _))) =
      (gr, [Pretty.str name])
  | compile_expr thy dep brack (gr, (Some (Mode (mode, ms)), t)) =
      let
        val (Const (name, _), args) = strip_comb t;
        val (gr', ps) = foldl_map
          (compile_expr thy dep true) (gr, ms ~~ args);
      in (gr', (if brack andalso not (null ps) then
        single o parens o Pretty.block else I)
          (flat (separate [Pretty.brk 1]
            ([Pretty.str (modename thy name mode)] :: ps))))
      end;

fun compile_clause thy gr dep all_vs arg_vs modes (iss, is) (ts, ps) =
  let
    val modes' = modes @ mapfilter
      (fn (_, None) => None | (v, Some js) => Some (v, [([], js)]))
        (arg_vs ~~ iss);

    fun check_constrt ((names, eqs), t) =
      if is_constrt thy t then ((names, eqs), t) else
        let val s = variant names "x";
        in ((s::names, (s, t)::eqs), Var ((s, 0), fastype_of t)) end;

    val (in_ts, out_ts) = get_args is 1 ts;
    val ((all_vs', eqs), in_ts') =
      foldl_map check_constrt ((all_vs, []), in_ts);

    fun compile_prems out_ts' vs names gr [] =
          let
            val (gr2, out_ps) = foldl_map
              (invoke_codegen thy dep false) (gr, out_ts);
            val (gr3, eq_ps) = foldl_map (fn (gr, (s, t)) =>
              apsnd (Pretty.block o cons (Pretty.str (s ^ " = ")) o single)
                (invoke_codegen thy dep false (gr, t))) (gr2, eqs);
            val (nvs, out_ts'') = foldl_map distinct_v
              ((names, map (fn x => (x, [x])) vs), out_ts');
            val (gr4, out_ps') = foldl_map
              (invoke_codegen thy dep false) (gr3, out_ts'');
          in
            (gr4, compile_match (snd nvs) eq_ps out_ps'
              (Pretty.block [Pretty.str "Seq.single", Pretty.brk 1, mk_tuple out_ps])
              (Pretty.str "Seq.empty"))
          end
      | compile_prems out_ts vs names gr ps =
          let
            val vs' = distinct (flat (vs :: map term_vs out_ts));
            val Some (p, mode as Some (Mode ((_, js), _))) =
              select_mode_prem thy modes' (arg_vs union vs') ps;
            val ps' = filter_out (equal p) ps;
          in
            (case p of
               Prem (us, t) =>
                 let
                   val (in_ts, out_ts') = get_args js 1 us;
                   val (gr1, in_ps) = foldl_map
                     (invoke_codegen thy dep false) (gr, in_ts);
                   val (nvs, out_ts'') = foldl_map distinct_v
                     ((names, map (fn x => (x, [x])) vs), out_ts);
                   val (gr2, out_ps) = foldl_map
                     (invoke_codegen thy dep false) (gr1, out_ts'');
                   val (gr3, ps) = compile_expr thy dep false (gr2, (mode, t));
                   val (gr4, rest) = compile_prems out_ts' vs' (fst nvs) gr3 ps';
                 in
                   (gr4, compile_match (snd nvs) [] out_ps
                      (Pretty.block (ps @
                         [Pretty.brk 1, mk_tuple in_ps,
                          Pretty.str " :->", Pretty.brk 1, rest]))
                      (Pretty.str "Seq.empty"))
                 end
             | Sidecond t =>
                 let
                   val (gr1, side_p) = invoke_codegen thy dep true (gr, t);
                   val (nvs, out_ts') = foldl_map distinct_v
                     ((names, map (fn x => (x, [x])) vs), out_ts);
                   val (gr2, out_ps) = foldl_map
                     (invoke_codegen thy dep false) (gr1, out_ts')
                   val (gr3, rest) = compile_prems [] vs' (fst nvs) gr2 ps';
                 in
                   (gr3, compile_match (snd nvs) [] out_ps
                      (Pretty.block [Pretty.str "?? ", side_p,
                        Pretty.str " :->", Pretty.brk 1, rest])
                      (Pretty.str "Seq.empty"))
                 end)
          end;

    val (gr', prem_p) = compile_prems in_ts' [] all_vs' gr ps;
  in
    (gr', Pretty.block [Pretty.str "Seq.single inp :->", Pretty.brk 1, prem_p])
  end;

fun compile_pred thy gr dep prfx all_vs arg_vs modes s cls mode =
  let val (gr', cl_ps) = foldl_map (fn (gr, cl) =>
    compile_clause thy gr dep all_vs arg_vs modes mode cl) (gr, cls)
  in
    ((gr', "and "), Pretty.block
      ([Pretty.block (separate (Pretty.brk 1)
         (Pretty.str (prfx ^ modename thy s mode) :: map Pretty.str arg_vs) @
         [Pretty.str " inp ="]),
        Pretty.brk 1] @
       flat (separate [Pretty.str " ++", Pretty.brk 1] (map single cl_ps))))
  end;

fun compile_preds thy gr dep all_vs arg_vs modes preds =
  let val ((gr', _), prs) = foldl_map (fn ((gr, prfx), (s, cls)) =>
    foldl_map (fn ((gr', prfx'), mode) =>
      compile_pred thy gr' dep prfx' all_vs arg_vs modes s cls mode)
        ((gr, prfx), the (assoc (modes, s)))) ((gr, "fun "), preds)
  in
    (gr', space_implode "\n\n" (map Pretty.string_of (flat prs)) ^ ";\n\n")
  end;

(**** processing of introduction rules ****)

exception Modes of
  (string * (int list option list * int list) list) list *
  (string * (int list list option list * int list list)) list;

fun lookup_modes gr dep = apfst flat (apsnd flat (ListPair.unzip
  (map ((fn (Some (Modes x), _) => x | _ => ([], [])) o Graph.get_node gr)
    (Graph.all_preds gr [dep]))));

fun string_of_mode (iss, is) = space_implode " -> " (map
  (fn None => "X"
    | Some js => enclose "[" "]" (commas (map string_of_int js)))
       (iss @ [Some is]));

fun print_modes modes = message ("Inferred modes:\n" ^
  space_implode "\n" (map (fn (s, ms) => s ^ ": " ^ commas (map
    string_of_mode ms)) modes));

fun print_factors factors = message ("Factors:\n" ^
  space_implode "\n" (map (fn (s, (fs, f)) => s ^ ": " ^
    space_implode " -> " (map
      (fn None => "X" | Some f' => string_of_factors [] f')
        (fs @ [Some f]))) factors));

fun mk_extra_defs thy gr dep names ts =
  foldl (fn (gr, name) =>
    if name mem names then gr
    else (case get_clauses thy name of
        None => gr
      | Some (names, intrs) =>
          mk_ind_def thy gr dep names intrs))
            (gr, foldr add_term_consts (ts, []))

and mk_ind_def thy gr dep names intrs =
  let val ids = map (mk_const_id (sign_of thy)) names
  in Graph.add_edge (hd ids, dep) gr handle Graph.UNDEF _ =>
    let
      fun dest_prem factors (_ $ (p as (Const ("op :", _) $ t $ u))) =
            (case head_of u of
               Const (name, _) => (case assoc (factors, name) of
                   None => Sidecond p
                 | Some f => Prem (split_prod [] f t, u))
             | Var ((name, _), _) => Prem (split_prod []
                 (the (assoc (factors, name))) t, u))
        | dest_prem factors (_ $ ((eq as Const ("op =", _)) $ t $ u)) =
            Prem ([t, u], eq)
        | dest_prem factors (_ $ t) = Sidecond t;

      fun add_clause factors (clauses, intr) =
        let
          val _ $ (_ $ t $ u) = Logic.strip_imp_concl intr;
          val Const (name, _) = head_of u;
          val prems = map (dest_prem factors) (Logic.strip_imp_prems intr);
        in
          (overwrite (clauses, (name, if_none (assoc (clauses, name)) [] @
             [(split_prod [] (the (assoc (factors, name))) t, prems)])))
        end;

      fun add_prod_factors extra_fs (fs, _ $ (Const ("op :", _) $ t $ u)) =
          (case apsome (get_clauses thy o fst) (try dest_Const (head_of u)) of
             Some None => fs
           | _ => infer_factors (sign_of thy) extra_fs
              (fs, (Some (FVar (prod_factors [] t)), u)))
        | add_prod_factors _ (fs, _) = fs;

      val intrs' = map (rename_term o #prop o rep_thm o standard) intrs;
      val _ $ (_ $ _ $ u) = Logic.strip_imp_concl (hd intrs');
      val (_, args) = strip_comb u;
      val arg_vs = flat (map term_vs args);
      val gr' = mk_extra_defs thy
        (Graph.add_edge (hd ids, dep)
          (Graph.new_node (hd ids, (None, "")) gr)) (hd ids) names intrs';
      val (extra_modes, extra_factors) = lookup_modes gr' (hd ids);
      val fs = map (apsnd dest_factors)
        (foldl (add_prod_factors extra_factors) ([], flat (map (fn t =>
          Logic.strip_imp_concl t :: Logic.strip_imp_prems t) intrs')));
      val _ = (case map fst fs \\ names \\ arg_vs of
          [] => ()
        | xs => error ("Non-inductive sets: " ^ commas_quote xs));
      val factors = mapfilter (fn (name, f) =>
        if name mem arg_vs then None
        else Some (name, (map (curry assoc fs) arg_vs, f))) fs;
      val clauses =
        foldl (add_clause (fs @ map (apsnd snd) extra_factors)) ([], intrs');
      val modes = infer_modes thy extra_modes factors arg_vs clauses;
      val _ = print_factors factors;
      val _ = print_modes modes;
      val (gr'', s) = compile_preds thy gr' (hd ids) (terms_vs intrs') arg_vs
        (modes @ extra_modes) clauses;
    in
      (Graph.map_node (hd ids) (K (Some (Modes (modes, factors)), s)) gr'')
    end      
  end;

fun mk_ind_call thy gr dep t u is_query = (case head_of u of
  Const (s, T) => (case (get_clauses thy s, get_assoc_code thy s T) of
       (None, _) => None
     | (Some (names, intrs), None) =>
         let
          fun mk_mode (((ts, mode), i), Const ("dummy_pattern", _)) =
                ((ts, mode), i+1)
            | mk_mode (((ts, mode), i), t) = ((ts @ [t], mode @ [i]), i+1);

           val gr1 = mk_extra_defs thy
             (mk_ind_def thy gr dep names intrs) dep names [u];
           val (modes, factors) = lookup_modes gr1 dep;
           val ts = split_prod [] (snd (the (assoc (factors, s)))) t;
           val (ts', is) = if is_query then
               fst (foldl mk_mode ((([], []), 1), ts))
             else (ts, 1 upto length ts);
           val mode = (case find_first (fn Mode ((_, js), _) => is=js)
                  (modes_of modes u) of
                None => error ("No such mode for " ^ s ^ ": " ^
                  string_of_mode ([], is))
              | mode => mode);
           val (gr2, in_ps) = foldl_map
             (invoke_codegen thy dep false) (gr1, ts');
           val (gr3, ps) = compile_expr thy dep false (gr2, (mode, u))
         in
           Some (gr3, Pretty.block
             (ps @ [Pretty.brk 1, mk_tuple in_ps]))
         end
     | _ => None)
  | _ => None);

fun inductive_codegen thy gr dep brack (Const ("op :", _) $ t $ u) =
      ((case mk_ind_call thy gr dep (Term.no_dummy_patterns t) u false of
         None => None
       | Some (gr', call_p) => Some (gr', (if brack then parens else I)
           (Pretty.block [Pretty.str "?! (", call_p, Pretty.str ")"])))
        handle TERM _ => mk_ind_call thy gr dep t u true)
  | inductive_codegen thy gr dep brack _ = None;

val setup =
  [add_codegen "inductive" inductive_codegen,
   CodegenData.init,
   add_attribute "ind" (Scan.succeed add)];

end;


(**** combinators for code generated from inductive predicates ****)

infix 5 :->;
infix 3 ++;

fun s :-> f = Seq.flat (Seq.map f s);

fun s1 ++ s2 = Seq.append (s1, s2);

fun ?? b = if b then Seq.single () else Seq.empty;

fun ?! s = is_some (Seq.pull s);    

fun op_61__1 x = Seq.single x;

val op_61__2 = op_61__1;

fun op_61__1_2 (x, y) = ?? (x = y);
