(*  Title:      HOL/datatype_codegen.ML
    ID:         $Id$
    Author:     Stefan Berghofer & Florian Haftmann, TU Muenchen

Code generator for inductive datatypes.
*)

signature DATATYPE_CODEGEN =
sig
  val get_datatype_spec_thms: theory -> string
    -> (((string * sort) list * (string * typ list) list) * tactic) option
  val get_all_datatype_cons: theory -> (string * string) list
  val dest_case_expr: theory -> term
    -> ((string * typ) list * ((term * typ) * (term * term) list)) option
  val add_datatype_case_const: string -> theory -> theory
  val add_datatype_case_defs: string -> theory -> theory
  val datatypes_dependency: theory -> string list list
  val get_datatype_mut_specs: theory -> string list
    -> ((string * sort) list * (string * (string * typ list) list) list)
  val get_datatype_arities: theory -> string list -> sort
    -> (string * (((string * sort list) * sort) * term list)) list option
  val prove_arities: (thm list -> tactic) -> string list -> sort
    -> (((string * sort list) * sort) list -> (string * term list) list
    -> ((bstring * attribute list) * term) list) -> theory -> theory
  val setup: theory -> theory
end;

structure DatatypeCodegen : DATATYPE_CODEGEN =
struct

open Codegen;

fun mk_tuple [p] = p
  | mk_tuple ps = Pretty.block (Pretty.str "(" ::
      List.concat (separate [Pretty.str ",", Pretty.brk 1] (map single ps)) @
        [Pretty.str ")"]);

(**** datatype definition ****)

(* find shortest path to constructor with no recursive arguments *)

fun find_nonempty (descr: DatatypeAux.descr) is i =
  let
    val (_, _, constrs) = valOf (AList.lookup (op =) descr i);
    fun arg_nonempty (_, DatatypeAux.DtRec i) = if i mem is then NONE
          else Option.map (curry op + 1 o snd) (find_nonempty descr (i::is) i)
      | arg_nonempty _ = SOME 0;
    fun max xs = Library.foldl
      (fn (NONE, _) => NONE
        | (SOME i, SOME j) => SOME (Int.max (i, j))
        | (_, NONE) => NONE) (SOME 0, xs);
    val xs = sort (int_ord o pairself snd)
      (List.mapPartial (fn (s, dts) => Option.map (pair s)
        (max (map (arg_nonempty o DatatypeAux.strip_dtyp) dts))) constrs)
  in case xs of [] => NONE | x :: _ => SOME x end;

fun add_dt_defs thy defs dep module gr (descr: DatatypeAux.descr) =
  let
    val sg = sign_of thy;
    val tab = DatatypePackage.get_datatypes thy;

    val descr' = List.filter (can (map DatatypeAux.dest_DtTFree o #2 o snd)) descr;
    val rtnames = map (#1 o snd) (List.filter (fn (_, (_, _, cs)) =>
      exists (exists DatatypeAux.is_rec_type o snd) cs) descr');

    val (_, (tname, _, _)) :: _ = descr';
    val node_id = tname ^ " (type)";
    val module' = if_library (thyname_of_type tname thy) module;

    fun mk_dtdef gr prfx [] = (gr, [])
      | mk_dtdef gr prfx ((_, (tname, dts, cs))::xs) =
          let
            val tvs = map DatatypeAux.dest_DtTFree dts;
            val sorts = map (rpair []) tvs;
            val cs' = map (apsnd (map (DatatypeAux.typ_of_dtyp descr sorts))) cs;
            val (gr', (_, type_id)) = mk_type_id module' tname gr;
            val (gr'', ps) =
              foldl_map (fn (gr, (cname, cargs)) =>
                foldl_map (invoke_tycodegen thy defs node_id module' false)
                  (gr, cargs) |>>>
                mk_const_id module' cname) (gr', cs');
            val (gr''', rest) = mk_dtdef gr'' "and " xs
          in
            (gr''',
             Pretty.block (Pretty.str prfx ::
               (if null tvs then [] else
                  [mk_tuple (map Pretty.str tvs), Pretty.str " "]) @
               [Pretty.str (type_id ^ " ="), Pretty.brk 1] @
               List.concat (separate [Pretty.brk 1, Pretty.str "| "]
                 (map (fn (ps', (_, cname)) => [Pretty.block
                   (Pretty.str cname ::
                    (if null ps' then [] else
                     List.concat ([Pretty.str " of", Pretty.brk 1] ::
                       separate [Pretty.str " *", Pretty.brk 1]
                         (map single ps'))))]) ps))) :: rest)
          end;

    fun mk_term_of_def gr prfx [] = []
      | mk_term_of_def gr prfx ((_, (tname, dts, cs)) :: xs) =
          let
            val tvs = map DatatypeAux.dest_DtTFree dts;
            val sorts = map (rpair []) tvs;
            val cs' = map (apsnd (map (DatatypeAux.typ_of_dtyp descr sorts))) cs;
            val dts' = map (DatatypeAux.typ_of_dtyp descr sorts) dts;
            val T = Type (tname, dts');
            val rest = mk_term_of_def gr "and " xs;
            val (_, eqs) = foldl_map (fn (prfx, (cname, Ts)) =>
              let val args = map (fn i =>
                Pretty.str ("x" ^ string_of_int i)) (1 upto length Ts)
              in ("  | ", Pretty.blk (4,
                [Pretty.str prfx, mk_term_of gr module' false T, Pretty.brk 1,
                 if null Ts then Pretty.str (snd (get_const_id cname gr))
                 else parens (Pretty.block
                   [Pretty.str (snd (get_const_id cname gr)),
                    Pretty.brk 1, mk_tuple args]),
                 Pretty.str " =", Pretty.brk 1] @
                 List.concat (separate [Pretty.str " $", Pretty.brk 1]
                   ([Pretty.str ("Const (\"" ^ cname ^ "\","), Pretty.brk 1,
                     mk_type false (Ts ---> T), Pretty.str ")"] ::
                    map (fn (x, U) => [Pretty.block [mk_term_of gr module' false U,
                      Pretty.brk 1, x]]) (args ~~ Ts)))))
              end) (prfx, cs')
          in eqs @ rest end;

    fun mk_gen_of_def gr prfx [] = []
      | mk_gen_of_def gr prfx ((i, (tname, dts, cs)) :: xs) =
          let
            val tvs = map DatatypeAux.dest_DtTFree dts;
            val sorts = map (rpair []) tvs;
            val (cs1, cs2) =
              List.partition (exists DatatypeAux.is_rec_type o snd) cs;
            val SOME (cname, _) = find_nonempty descr [i] i;

            fun mk_delay p = Pretty.block
              [Pretty.str "fn () =>", Pretty.brk 1, p];

            fun mk_constr s b (cname, dts) =
              let
                val gs = map (fn dt => mk_app false (mk_gen gr module' false rtnames s
                    (DatatypeAux.typ_of_dtyp descr sorts dt))
                  [Pretty.str (if b andalso DatatypeAux.is_rec_type dt then "0"
                     else "j")]) dts;
                val (_, id) = get_const_id cname gr
              in case gs of
                  _ :: _ :: _ => Pretty.block
                    [Pretty.str id, Pretty.brk 1, mk_tuple gs]
                | _ => mk_app false (Pretty.str id) (map parens gs)
              end;

            fun mk_choice [c] = mk_constr "(i-1)" false c
              | mk_choice cs = Pretty.block [Pretty.str "one_of",
                  Pretty.brk 1, Pretty.blk (1, Pretty.str "[" ::
                  List.concat (separate [Pretty.str ",", Pretty.fbrk]
                    (map (single o mk_delay o mk_constr "(i-1)" false) cs)) @
                  [Pretty.str "]"]), Pretty.brk 1, Pretty.str "()"];

            val gs = map (Pretty.str o suffix "G" o strip_tname) tvs;
            val gen_name = "gen_" ^ snd (get_type_id tname gr)

          in
            Pretty.blk (4, separate (Pretty.brk 1) 
                (Pretty.str (prfx ^ gen_name ^
                   (if null cs1 then "" else "'")) :: gs @
                 (if null cs1 then [] else [Pretty.str "i"]) @
                 [Pretty.str "j"]) @
              [Pretty.str " =", Pretty.brk 1] @
              (if not (null cs1) andalso not (null cs2)
               then [Pretty.str "frequency", Pretty.brk 1,
                 Pretty.blk (1, [Pretty.str "[",
                   mk_tuple [Pretty.str "i", mk_delay (mk_choice cs1)],
                   Pretty.str ",", Pretty.fbrk,
                   mk_tuple [Pretty.str "1", mk_delay (mk_choice cs2)],
                   Pretty.str "]"]), Pretty.brk 1, Pretty.str "()"]
               else if null cs2 then
                 [Pretty.block [Pretty.str "(case", Pretty.brk 1,
                   Pretty.str "i", Pretty.brk 1, Pretty.str "of",
                   Pretty.brk 1, Pretty.str "0 =>", Pretty.brk 1,
                   mk_constr "0" true (cname, valOf (AList.lookup (op =) cs cname)),
                   Pretty.brk 1, Pretty.str "| _ =>", Pretty.brk 1,
                   mk_choice cs1, Pretty.str ")"]]
               else [mk_choice cs2])) ::
            (if null cs1 then []
             else [Pretty.blk (4, separate (Pretty.brk 1) 
                 (Pretty.str ("and " ^ gen_name) :: gs @ [Pretty.str "i"]) @
               [Pretty.str " =", Pretty.brk 1] @
               separate (Pretty.brk 1) (Pretty.str (gen_name ^ "'") :: gs @
                 [Pretty.str "i", Pretty.str "i"]))]) @
            mk_gen_of_def gr "and " xs
          end

  in
    (add_edge_acyclic (node_id, dep) gr
        handle Graph.CYCLES _ => gr) handle Graph.UNDEF _ =>
         let
           val gr1 = add_edge (node_id, dep)
             (new_node (node_id, (NONE, "", "")) gr);
           val (gr2, dtdef) = mk_dtdef gr1 "datatype " descr';
         in
           map_node node_id (K (NONE, module',
             Pretty.string_of (Pretty.blk (0, separate Pretty.fbrk dtdef @
               [Pretty.str ";"])) ^ "\n\n" ^
             (if "term_of" mem !mode then
                Pretty.string_of (Pretty.blk (0, separate Pretty.fbrk
                  (mk_term_of_def gr2 "fun " descr') @ [Pretty.str ";"])) ^ "\n\n"
              else "") ^
             (if "test" mem !mode then
                Pretty.string_of (Pretty.blk (0, separate Pretty.fbrk
                  (mk_gen_of_def gr2 "fun " descr') @ [Pretty.str ";"])) ^ "\n\n"
              else ""))) gr2
         end
  end;


(**** case expressions ****)

fun pretty_case thy defs gr dep module brack constrs (c as Const (_, T)) ts =
  let val i = length constrs
  in if length ts <= i then
       invoke_codegen thy defs dep module brack (gr, eta_expand c ts (i+1))
    else
      let
        val ts1 = Library.take (i, ts);
        val t :: ts2 = Library.drop (i, ts);
        val names = foldr add_term_names
          (map (fst o fst o dest_Var) (foldr add_term_vars [] ts1)) ts1;
        val (Ts, dT) = split_last (Library.take (i+1, fst (strip_type T)));

        fun pcase gr [] [] [] = ([], gr)
          | pcase gr ((cname, cargs)::cs) (t::ts) (U::Us) =
              let
                val j = length cargs;
                val xs = Name.variant_list names (replicate j "x");
                val Us' = Library.take (j, fst (strip_type U));
                val frees = map Free (xs ~~ Us');
                val (gr0, cp) = invoke_codegen thy defs dep module false
                  (gr, list_comb (Const (cname, Us' ---> dT), frees));
                val t' = Envir.beta_norm (list_comb (t, frees));
                val (gr1, p) = invoke_codegen thy defs dep module false (gr0, t');
                val (ps, gr2) = pcase gr1 cs ts Us;
              in
                ([Pretty.block [cp, Pretty.str " =>", Pretty.brk 1, p]] :: ps, gr2)
              end;

        val (ps1, gr1) = pcase gr constrs ts1 Ts;
        val ps = List.concat (separate [Pretty.brk 1, Pretty.str "| "] ps1);
        val (gr2, p) = invoke_codegen thy defs dep module false (gr1, t);
        val (gr3, ps2) = foldl_map (invoke_codegen thy defs dep module true) (gr2, ts2)
      in (gr3, (if not (null ts2) andalso brack then parens else I)
        (Pretty.block (separate (Pretty.brk 1)
          (Pretty.block ([Pretty.str "(case ", p, Pretty.str " of",
             Pretty.brk 1] @ ps @ [Pretty.str ")"]) :: ps2))))
      end
  end;


(**** constructors ****)

fun pretty_constr thy defs gr dep module brack args (c as Const (s, T)) ts =
  let val i = length args
  in if i > 1 andalso length ts < i then
      invoke_codegen thy defs dep module brack (gr, eta_expand c ts i)
     else
       let
         val id = mk_qual_id module (get_const_id s gr);
         val (gr', ps) = foldl_map
           (invoke_codegen thy defs dep module (i = 1)) (gr, ts);
       in (case args of
          _ :: _ :: _ => (gr', (if brack then parens else I)
            (Pretty.block [Pretty.str id, Pretty.brk 1, mk_tuple ps]))
        | _ => (gr', mk_app brack (Pretty.str id) ps))
       end
  end;


(**** code generators for terms and types ****)

fun datatype_codegen thy defs gr dep module brack t = (case strip_comb t of
   (c as Const (s, T), ts) =>
       (case Library.find_first (fn (_, {index, descr, case_name, ...}) =>
         s = case_name orelse
           AList.defined (op =) ((#3 o the o AList.lookup (op =) descr) index) s)
             (Symtab.dest (DatatypePackage.get_datatypes thy)) of
          NONE => NONE
        | SOME (tname, {index, descr, ...}) =>
           if is_some (get_assoc_code thy s T) then NONE else
           let val SOME (_, _, constrs) = AList.lookup (op =) descr index
           in (case (AList.lookup (op =) constrs s, strip_type T) of
               (NONE, _) => SOME (pretty_case thy defs gr dep module brack
                 ((#3 o the o AList.lookup (op =) descr) index) c ts)
             | (SOME args, (_, Type _)) => SOME (pretty_constr thy defs
                 (fst (invoke_tycodegen thy defs dep module false
                    (gr, snd (strip_type T))))
                 dep module brack args c ts)
             | _ => NONE)
           end)
 |  _ => NONE);

fun datatype_tycodegen thy defs gr dep module brack (Type (s, Ts)) =
      (case Symtab.lookup (DatatypePackage.get_datatypes thy) s of
         NONE => NONE
       | SOME {descr, ...} =>
           if isSome (get_assoc_type thy s) then NONE else
           let
             val (gr', ps) = foldl_map
               (invoke_tycodegen thy defs dep module false) (gr, Ts);
             val gr'' = add_dt_defs thy defs dep module gr' descr
           in SOME (gr'',
             Pretty.block ((if null Ts then [] else
               [mk_tuple ps, Pretty.str " "]) @
               [Pretty.str (mk_qual_id module (get_type_id s gr''))]))
           end)
  | datatype_tycodegen _ _ _ _ _ _ _ = NONE;


(** code 2nd generation **)

fun datatypes_dependency thy =
  let
    val dtnames = DatatypePackage.get_datatypes thy;
    fun add_node (dtname, _) =
      let
        fun add_tycos (Type (tyco, tys)) = insert (op =) tyco #> fold add_tycos tys
          | add_tycos _ = I;
        val deps = (filter (Symtab.defined dtnames) o maps (fn ty =>
          add_tycos ty [])
            o maps snd o snd o the o DatatypePackage.get_datatype_spec thy) dtname
      in
        Graph.default_node (dtname, ())
        #> fold (fn dtname' =>
             Graph.default_node (dtname', ())
             #> Graph.add_edge (dtname', dtname)
           ) deps
      end
  in
    Graph.empty
    |> Symtab.fold add_node dtnames
    |> Graph.strong_conn
  end;

fun get_datatype_mut_specs thy (tycos as tyco :: _) =
  let
    val tycos' = (map (#1 o snd) o #descr o DatatypePackage.the_datatype thy) tyco;
    val _ = if gen_subset (op =) (tycos, tycos') then () else
      error ("datatype constructors are not mutually recursive: " ^ (commas o map quote) tycos);
    val (vs::_, css) = split_list (map (the o DatatypePackage.get_datatype_spec thy) tycos);
  in (vs, tycos ~~ css) end;

fun get_datatype_arities thy tycos sort =
  let
    val algebra = Sign.classes_of thy;
    val (vs_proto, css_proto) = get_datatype_mut_specs thy tycos;
    val vs = map (fn (v, vsort) => (v, Sorts.inter_sort algebra (vsort, sort))) vs_proto;
    fun inst_type tyco (c, tys) =
      let
        val tys' = (map o map_atyps)
          (fn TFree (v, _) => TFree (v, the (AList.lookup (op =) vs v))) tys
      in (c, tys') end;
    val css = map (fn (tyco, cs) => (tyco, (map (inst_type tyco) cs))) css_proto;
    fun mk_arity tyco =
      ((tyco, map snd vs), sort);
    fun typ_of_sort ty =
      let
        val arities = map (fn (tyco, _) => ((tyco, map snd vs), sort)) css;
      in ClassPackage.assume_arities_of_sort thy arities (ty, sort) end;
    fun mk_cons tyco (c, tys) =
      let
        val ts = Name.names Name.context "a" tys;
        val ty = tys ---> Type (tyco, map TFree vs);
      in list_comb (Const (c, ty), map Free ts) end;
  in if forall (fn (_, cs) => forall (fn (_, tys) => forall typ_of_sort tys) cs) css
    then SOME (
      map (fn (tyco, cs) => (tyco, (mk_arity tyco, map (mk_cons tyco) cs))) css
    ) else NONE
  end;

fun prove_arities tac tycos sort f thy =
  case get_datatype_arities thy tycos sort
   of NONE => thy
    | SOME insts => let
        fun proven ((tyco, asorts), sort) =
          Sorts.of_sort (Sign.classes_of thy)
            (Type (tyco, map TFree (Name.names Name.context "'a" asorts)), sort);
        val (arities, css) = (split_list o map_filter
          (fn (tyco, (arity, cs)) => if proven arity
            then NONE else SOME (arity, (tyco, cs)))) insts;
      in
        thy
        |> K ((not o null) arities) ? ClassPackage.prove_instance_arity tac
             arities ("", []) (f arities css)
      end;

fun dtyp_of_case_const thy c =
  get_first (fn (dtco, { case_name, ... }) => if case_name = c then SOME dtco else NONE)
    ((Symtab.dest o DatatypePackage.get_datatypes) thy);

fun dest_case_app cs ts tys =
  let
    val abs = Name.names Name.context "a" (Library.drop (length ts, tys));
    val (ts', t) = split_last (ts @ map Free abs);
    val (tys', sty) = split_last tys;
    fun freenames_of t = fold_aterms
      (fn Free (v, _) => insert (op =) v | _ => I) t [];
    fun dest_case ((c, tys_decl), ty) t =
      let
        val (vs, t') = Term.strip_abs_eta (length tys_decl) t;
        val c' = list_comb (Const (c, map snd vs ---> sty), map Free vs);
      in (c', t') end;
  in (abs, ((t, sty), map2 dest_case (cs ~~ tys') ts')) end;

fun dest_case_expr thy t =
  case strip_comb t
   of (Const (c, ty), ts) =>
        (case dtyp_of_case_const thy c
         of SOME dtco =>
              let val (vs, cs) = (the o DatatypePackage.get_datatype_spec thy) dtco;
              in SOME (dest_case_app cs ts (Library.take (length cs + 1, (fst o strip_type) ty))) end
          | _ => NONE)
    | _ => NONE;

fun datatype_tac thy dtco =
  let
    val ctxt = Context.init_proof thy;
    val inject = (#inject o DatatypePackage.the_datatype thy) dtco;
    val simpset = Simplifier.context ctxt
      (MetaSimplifier.empty_ss addsimprocs [distinct_simproc]);
  in
    (TRY o ALLGOALS o match_tac) [HOL.eq_reflection]
    THEN (
      (ALLGOALS o match_tac) (eqTrueI :: inject)
      ORELSE (ALLGOALS o simp_tac) simpset
    )
    THEN (ALLGOALS o match_tac) [HOL.refl, Drule.reflexive_thm]
  end;

fun get_datatype_spec_thms thy dtco =
  case DatatypePackage.get_datatype_spec thy dtco
   of SOME vs_cos =>
        SOME (vs_cos, datatype_tac thy dtco)
    | NONE => NONE;

fun get_all_datatype_cons thy =
  Symtab.fold (fn (dtco, _) => fold
    (fn (co, _) => cons (co, dtco))
      ((snd o the oo DatatypePackage.get_datatype_spec) thy dtco))
        (DatatypePackage.get_datatypes thy) [];

fun add_datatype_case_const dtco thy =
  let
    val {case_name, index, descr, ...} = DatatypePackage.the_datatype thy dtco;
  in
    CodegenPackage.add_appconst_i (case_name, CodegenPackage.appgen_case dest_case_expr) thy
  end;

fun add_datatype_case_defs dtco thy =
  let
    val {case_rewrites, ...} = DatatypePackage.the_datatype thy dtco
  in
    fold CodegenTheorems.add_fun case_rewrites thy
  end;

val setup = 
  add_codegen "datatype" datatype_codegen #>
  add_tycodegen "datatype" datatype_tycodegen #>
  CodegenTheorems.add_datatype_extr
    get_datatype_spec_thms #>
  CodegenPackage.set_get_all_datatype_cons
    get_all_datatype_cons #>
  DatatypeHooks.add (fold add_datatype_case_const) #>
  DatatypeHooks.add (fold add_datatype_case_defs)

end;
