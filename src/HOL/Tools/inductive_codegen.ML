(*  Title:      HOL/inductive_codegen.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Code generator for inductive predicates.
*)

signature INDUCTIVE_CODEGEN =
sig
  val setup : (theory -> theory) list
end;

structure InductiveCodegen : INDUCTIVE_CODEGEN =
struct

open Codegen;

exception Modes of (string * int list list) list * (string * int list list) list;

datatype indprem = Prem of string * term list * term list
                 | Sidecond of term;

fun prod_factors p (Const ("Pair", _) $ t $ u) =
      p :: prod_factors (1::p) t @ prod_factors (2::p) u
  | prod_factors p _ = [];

fun split_prod p ps t = if p mem ps then (case t of
       Const ("Pair", _) $ t $ u =>
         split_prod (1::p) ps t @ split_prod (2::p) ps u
     | _ => error "Inconsistent use of products") else [t];

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

fun select_mode_prem thy modes vs ps =
  find_first (is_some o snd) (ps ~~ map
    (fn Prem (s, us, args) => find_first (fn is =>
          let
            val (_, out_ts) = get_args is 1 us;
            val vTs = flat (map term_vTs out_ts);
            val dupTs = map snd (duplicates vTs) @
              mapfilter (curry assoc vTs) vs;
          in
            is subset known_args vs 1 us andalso
            forall (is_constrt thy) (snd (get_args is 1 us)) andalso
            terms_vs args subset vs andalso
            forall is_eqT dupTs
          end)
            (the (assoc (modes, s)))
      | Sidecond t => if term_vs t subset vs then Some [] else None) ps);

fun check_mode_clause thy arg_vs modes mode (ts, ps) =
  let
    fun check_mode_prems vs [] = Some vs
      | check_mode_prems vs ps = (case select_mode_prem thy modes vs ps of
          None => None
        | Some (x, _) => check_mode_prems
            (case x of Prem (_, us, _) => vs union terms_vs us | _ => vs)
            (filter_out (equal x) ps));
    val (in_ts', _) = get_args mode 1 ts;
    val in_ts = filter (is_constrt thy) in_ts';
    val in_vs = terms_vs in_ts;
    val concl_vs = terms_vs ts
  in
    forall is_eqT (map snd (duplicates (flat (map term_vTs in_ts')))) andalso
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

fun infer_modes thy extra_modes arg_vs preds = fixp (fn modes =>
  map (check_modes_pred thy arg_vs preds (modes @ extra_modes)) modes)
    (map (fn (s, (ts, _)::_) => (s, subsets 1 (length ts))) preds);

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

fun modename thy s mode = space_implode "_"
  (mk_const_id (sign_of thy) s :: map string_of_int mode);

fun compile_clause thy gr dep all_vs arg_vs modes mode (ts, ps) =
  let
    fun check_constrt ((names, eqs), t) =
      if is_constrt thy t then ((names, eqs), t) else
        let val s = variant names "x";
        in ((s::names, (s, t)::eqs), Var ((s, 0), fastype_of t)) end;

    val (in_ts, out_ts) = get_args mode 1 ts;
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
            val Some (p, Some mode') =
              select_mode_prem thy modes (arg_vs union vs') ps;
            val ps' = filter_out (equal p) ps;
          in
            (case p of
               Prem (s, us, args) =>
                 let
                   val (in_ts, out_ts') = get_args mode' 1 us;
                   val (gr1, in_ps) = foldl_map
                     (invoke_codegen thy dep false) (gr, in_ts);
                   val (gr2, arg_ps) = foldl_map
                     (invoke_codegen thy dep true) (gr1, args);
                   val (nvs, out_ts'') = foldl_map distinct_v
                     ((names, map (fn x => (x, [x])) vs), out_ts);
                   val (gr3, out_ps) = foldl_map
                     (invoke_codegen thy dep false) (gr2, out_ts'')
                   val (gr4, rest) = compile_prems out_ts' vs' (fst nvs) gr3 ps';
                 in
                   (gr4, compile_match (snd nvs) [] out_ps
                      (Pretty.block (separate (Pretty.brk 1)
                        (Pretty.str (modename thy s mode') :: arg_ps) @
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

val string_of_mode = enclose "[" "]" o commas o map string_of_int;

fun print_modes modes = message ("Inferred modes:\n" ^
  space_implode "\n" (map (fn (s, ms) => s ^ ": " ^ commas (map
    string_of_mode ms)) modes));

fun print_factors factors = message ("Factors:\n" ^
  space_implode "\n" (map (fn (s, fs) => s ^ ": " ^ string_of_factors [] fs) factors));
  
fun get_modes (Some (Modes x), _) = x
  | get_modes _ = ([], []);

fun mk_ind_def thy gr dep names intrs =
  let val ids = map (mk_const_id (sign_of thy)) names
  in Graph.add_edge (hd ids, dep) gr handle Graph.UNDEF _ =>
    let
      fun process_prem factors (gr, t' as _ $ (Const ("op :", _) $ t $ u)) =
            (case strip_comb u of
               (Const (name, _), args) =>
                  (case InductivePackage.get_inductive thy name of
                     None => (gr, Sidecond t')
                   | Some ({names=names', ...}, {intrs=intrs', ...}) =>
                       (if names = names' then gr
                          else mk_ind_def thy gr (hd ids) names' intrs',
                        Prem (name, split_prod []
                          (the (assoc (factors, name))) t, args)))
             | _ => (gr, Sidecond t'))
        | process_prem factors (gr, _ $ (Const ("op =", _) $ t $ u)) =
            (gr, Prem ("eq", [t, u], []))
        | process_prem factors (gr, _ $ t) = (gr, Sidecond t);

      fun add_clause factors ((clauses, gr), intr) =
        let
          val _ $ (_ $ t $ u) = Logic.strip_imp_concl intr;
          val (Const (name, _), args) = strip_comb u;
          val (gr', prems) = foldl_map (process_prem factors)
            (gr, Logic.strip_imp_prems intr);
        in
          (overwrite (clauses, (name, if_none (assoc (clauses, name)) [] @
             [(split_prod [] (the (assoc (factors, name))) t, prems)])), gr')
        end;

      fun add_prod_factors (fs, x as _ $ (Const ("op :", _) $ t $ u)) =
            (case strip_comb u of
               (Const (name, _), _) =>
                 let val f = prod_factors [] t
                 in overwrite (fs, (name, f inter if_none (assoc (fs, name)) f)) end
             | _ => fs)
        | add_prod_factors (fs, _) = fs;

      val intrs' = map (rename_term o #prop o rep_thm o standard) intrs;
      val factors = foldl add_prod_factors ([], flat (map (fn t =>
        Logic.strip_imp_concl t :: Logic.strip_imp_prems t) intrs'));
      val (clauses, gr') = foldl (add_clause factors) (([], Graph.add_edge (hd ids, dep)
        (Graph.new_node (hd ids, (None, "")) gr)), intrs');
      val _ $ (_ $ _ $ u) = Logic.strip_imp_concl (hd intrs');
      val (_, args) = strip_comb u;
      val arg_vs = flat (map term_vs args);
      val extra_modes = ("eq", [[1], [2], [1,2]]) :: (flat (map
        (fst o get_modes o Graph.get_node gr') (Graph.all_preds gr' [hd ids])));
      val modes = infer_modes thy extra_modes arg_vs clauses;
      val _ = print_modes modes;
      val _ = print_factors factors;
      val (gr'', s) = compile_preds thy gr' (hd ids) (terms_vs intrs') arg_vs
        (modes @ extra_modes) clauses;
    in
      (Graph.map_node (hd ids) (K (Some (Modes (modes, factors)), s)) gr'')
    end      
  end;

fun mk_ind_call thy gr dep t u is_query = (case strip_comb u of
  (Const (s, _), args) => (case InductivePackage.get_inductive thy s of
       None => None
     | Some ({names, ...}, {intrs, ...}) =>
         let
          fun mk_mode (((ts, mode), i), Var _) = ((ts, mode), i+1)
            | mk_mode (((ts, mode), i), Free _) = ((ts, mode), i+1)
            | mk_mode (((ts, mode), i), t) = ((ts @ [t], mode @ [i]), i+1);

           val gr1 = mk_ind_def thy gr dep names intrs;
           val (modes, factors) = pairself flat (ListPair.unzip
             (map (get_modes o Graph.get_node gr1) (Graph.all_preds gr1 [dep])));
           val ts = split_prod [] (the (assoc (factors, s))) t;
           val (ts', mode) = if is_query then
               fst (foldl mk_mode ((([], []), 1), ts))
             else (ts, 1 upto length ts);
           val _ = if mode mem the (assoc (modes, s)) then () else
             error ("No such mode for " ^ s ^ ": " ^ string_of_mode mode);
           val (gr2, in_ps) = foldl_map
             (invoke_codegen thy dep false) (gr1, ts');
           val (gr3, arg_ps) = foldl_map
             (invoke_codegen thy dep true) (gr2, args);
         in
           Some (gr3, Pretty.block (separate (Pretty.brk 1)
             (Pretty.str (modename thy s mode) :: arg_ps @ [mk_tuple in_ps])))
         end)
  | _ => None);

fun inductive_codegen thy gr dep brack (Const ("op :", _) $ t $ u) =
      (case mk_ind_call thy gr dep t u false of
         None => None
       | Some (gr', call_p) => Some (gr', (if brack then parens else I)
           (Pretty.block [Pretty.str "?! (", call_p, Pretty.str ")"])))
  | inductive_codegen thy gr dep brack (Free ("query", _) $ (Const ("op :", _) $ t $ u)) =
      mk_ind_call thy gr dep t u true
  | inductive_codegen thy gr dep brack _ = None;

val setup = [add_codegen "inductive" inductive_codegen];

end;


(**** combinators for code generated from inductive predicates ****)

infix 5 :->;
infix 3 ++;

fun s :-> f = Seq.flat (Seq.map f s);

fun s1 ++ s2 = Seq.append (s1, s2);

fun ?? b = if b then Seq.single () else Seq.empty;

fun ?! s = is_some (Seq.pull s);    

fun eq_1 x = Seq.single x;

val eq_2 = eq_1;
