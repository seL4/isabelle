(*  Title:      HOL/Tools/datatype_codegen.ML
    ID:         $Id$
    Author:     Stefan Berghofer & Florian Haftmann, TU Muenchen

Code generator for inductive datatypes.
*)

signature DATATYPE_CODEGEN =
sig
  val get_eq: theory -> string -> thm list
  val get_eq_datatype: theory -> string -> thm list
  val dest_case_expr: theory -> term
    -> ((string * typ) list * ((term * typ) * (term * term) list)) option
  val get_case_cert: theory -> string -> thm

  type hook = (string * (bool * ((string * sort) list * (string * typ list) list))) list
    -> theory -> theory
  val codetype_hook: hook
  val eq_hook: hook
  val codetypes_dependency: theory -> (string * bool) list list
  val add_codetypes_hook_bootstrap: hook -> theory -> theory
  val the_codetypes_mut_specs: theory -> (string * bool) list
    -> ((string * sort) list * (string * (bool * (string * typ list) list)) list)
  val get_codetypes_arities: theory -> (string * bool) list -> sort
    -> (string * (arity * term list)) list option
  val prove_codetypes_arities: tactic -> (string * bool) list -> sort
    -> (arity list -> (string * term list) list -> theory
      -> ((bstring * Attrib.src list) * term) list * theory)
    -> (arity list -> (string * term list) list -> thm list -> theory -> theory)
    -> theory -> theory

  val setup: theory -> theory
  val setup_hooks: theory -> theory
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
    ((add_edge_acyclic (node_id, dep) gr
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
         end,
     module')
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
     (case DatatypePackage.datatype_of_case thy s of
        SOME {index, descr, ...} =>
          if is_some (get_assoc_code thy (s, T)) then NONE else
          SOME (pretty_case thy defs gr dep module brack
            (#3 (the (AList.lookup op = descr index))) c ts)
      | NONE => case (DatatypePackage.datatype_of_constr thy s, strip_type T) of
        (SOME {index, descr, ...}, (_, U as Type _)) =>
          if is_some (get_assoc_code thy (s, T)) then NONE else
          let val SOME args = AList.lookup op =
            (#3 (the (AList.lookup op = descr index))) s
          in
            SOME (pretty_constr thy defs
              (fst (invoke_tycodegen thy defs dep module false (gr, U)))
              dep module brack args c ts)
          end
      | _ => NONE)
 | _ => NONE);

fun datatype_tycodegen thy defs gr dep module brack (Type (s, Ts)) =
      (case DatatypePackage.get_datatype thy s of
         NONE => NONE
       | SOME {descr, ...} =>
           if is_some (get_assoc_type thy s) then NONE else
           let
             val (gr', ps) = foldl_map
               (invoke_tycodegen thy defs dep module false) (gr, Ts);
             val (gr'', module') = add_dt_defs thy defs dep module gr' descr;
             val (gr''', tyid) = mk_type_id module' s gr''
           in SOME (gr''',
             Pretty.block ((if null Ts then [] else
               [mk_tuple ps, Pretty.str " "]) @
               [Pretty.str (mk_qual_id module tyid)]))
           end)
  | datatype_tycodegen _ _ _ _ _ _ _ = NONE;


(** datatypes for code 2nd generation **)

fun dtyp_of_case_const thy c =
  Option.map (fn {descr, index, ...} => #1 (the (AList.lookup op = descr index)))
    (DatatypePackage.datatype_of_case thy c);

fun dest_case_app cs ts tys =
  let
    val names = (Name.make_context o map fst) (fold Term.add_tfrees ts []);
    val abs = Name.names names "a" (Library.drop (length ts, tys));
    val (ts', t) = split_last (ts @ map Free abs);
    val (tys', sty) = split_last tys;
    fun dest_case ((c, tys_decl), ty) t =
      let
        val (vs, t') = Term.strip_abs_eta (length tys_decl) t;
        val c' = list_comb (Const (c, map snd vs ---> sty), map Free vs);
      in case t'
       of Const ("HOL.undefined", _) => NONE
        | _ => SOME (c', t')
      end;
  in (abs, ((t, sty), map2 dest_case (cs ~~ tys') ts' |> map_filter I)) end;

fun dest_case_expr thy t =
  case strip_comb t
   of (Const (c, ty), ts) =>
        (case dtyp_of_case_const thy c
         of SOME dtco =>
              let val (vs, cs) = (the o DatatypePackage.get_datatype_spec thy) dtco;
              in SOME (dest_case_app cs ts (Library.take (length cs + 1, (fst o strip_type) ty))) end
          | _ => NONE)
    | _ => NONE;

fun mk_distinct cos =
  let
    fun sym_product [] = []
      | sym_product (x::xs) = map (pair x) xs @ sym_product xs;
    fun mk_co_args (co, tys) ctxt =
      let
        val names = Name.invents ctxt "a" (length tys);
        val ctxt' = fold Name.declare names ctxt;
        val vs = map2 (curry Free) names tys;
      in (vs, ctxt') end;
    fun mk_dist ((co1, tys1), (co2, tys2)) =
      let
        val ((xs1, xs2), _) = Name.context
          |> mk_co_args (co1, tys1)
          ||>> mk_co_args (co2, tys2);
        val prem = HOLogic.mk_eq
          (list_comb (co1, xs1), list_comb (co2, xs2));
        val t = HOLogic.mk_not prem;
      in HOLogic.mk_Trueprop t end;
  in map mk_dist (sym_product cos) end;

local
  val not_sym = thm "HOL.not_sym";
  val not_false_true = iffD2 OF [nth (thms "HOL.simp_thms") 7, TrueI];
  val refl = thm "refl";
  val eqTrueI = thm "eqTrueI";
in

fun get_eq_datatype thy dtco =
  let
    val SOME (vs, cs) = DatatypePackage.get_datatype_spec thy dtco;
    fun mk_triv_inject co =
      let
        val ct' = Thm.cterm_of thy
          (Const (co, Type (dtco, map (fn (v, sort) => TVar ((v, 0), sort)) vs)))
        val cty' = Thm.ctyp_of_term ct';
        val SOME (ct, cty) = fold_aterms (fn Var (v, ty) =>
          (K o SOME) (Thm.cterm_of thy (Var (v, Thm.typ_of cty')), Thm.ctyp_of thy ty) | _ => I)
          (Thm.prop_of refl) NONE;
      in eqTrueI OF [Thm.instantiate ([(cty, cty')], [(ct, ct')]) refl] end;
    val inject1 = map_filter (fn (co, []) => SOME (mk_triv_inject co) | _ => NONE) cs
    val inject2 = (#inject o DatatypePackage.the_datatype thy) dtco;
    val ctxt = ProofContext.init thy;
    val simpset = Simplifier.context ctxt
      (MetaSimplifier.empty_ss addsimprocs [distinct_simproc]);
    val cos = map (fn (co, tys) =>
        (Const (co, tys ---> Type (dtco, map TFree vs)), tys)) cs;
    val tac = ALLGOALS (simp_tac simpset)
      THEN ALLGOALS (ProofContext.fact_tac [not_false_true, TrueI]);
    val distinct =
      mk_distinct cos
      |> map (fn t => Goal.prove_global thy [] [] t (K tac))
      |> (fn thms => thms @ map (fn thm => not_sym OF [thm]) thms)
  in inject1 @ inject2 @ distinct end;

end;

fun get_case_cert thy tyco =
  let
    val raw_thms =
      (#case_rewrites o DatatypePackage.the_datatype thy) tyco;
    val thms as hd_thm :: _ = raw_thms
      |> Conjunction.intr_balanced
      |> Drule.unvarify
      |> Conjunction.elim_balanced (length raw_thms)
      |> map Simpdata.mk_meta_eq
      |> map Drule.zero_var_indexes
    val params = fold_aterms (fn (Free (v, _)) => insert (op =) v
      | _ => I) (Thm.prop_of hd_thm) [];
    val rhs = hd_thm
      |> Thm.prop_of
      |> Logic.dest_equals
      |> fst
      |> Term.strip_comb
      |> apsnd (fst o split_last)
      |> list_comb;
    val lhs = Free (Name.variant params "case", Term.fastype_of rhs);
    val asm = (Thm.cterm_of thy o Logic.mk_equals) (lhs, rhs);
  in
    thms
    |> Conjunction.intr_balanced
    |> MetaSimplifier.rewrite_rule [(Thm.symmetric o Thm.assume) asm]
    |> Thm.implies_intr asm
    |> Thm.generalize ([], params) 0
    |> Thm.varifyT
  end;



(** codetypes for code 2nd generation **)

(* abstraction over datatypes vs. type copies *)

fun codetypes_dependency thy =
  let
    val names =
      map (rpair true) (Symtab.keys (DatatypePackage.get_datatypes thy))
        @ map (rpair false) (TypecopyPackage.get_typecopies thy);
    fun add_node (name, is_dt) =
      let
        fun add_tycos (Type (tyco, tys)) = insert (op =) tyco #> fold add_tycos tys
          | add_tycos _ = I;
        val tys = if is_dt then
            (maps snd o snd o the o DatatypePackage.get_datatype_spec thy) name
          else
            [(#typ o the o TypecopyPackage.get_typecopy_info thy) name]
        val deps = (filter (AList.defined (op =) names) o maps (fn ty =>
          add_tycos ty [])) tys;
      in
        Graph.default_node (name, ())
        #> fold (fn name' =>
             Graph.default_node (name', ())
             #> Graph.add_edge (name', name)
           ) deps
      end
  in
    Graph.empty
    |> fold add_node names
    |> Graph.strong_conn
    |> map (AList.make (the o AList.lookup (op =) names))
  end;

fun get_spec thy (dtco, true) =
      (the o DatatypePackage.get_datatype_spec thy) dtco
  | get_spec thy (tyco, false) =
      TypecopyPackage.get_spec thy tyco;

local
  fun get_eq_thms thy tyco = case DatatypePackage.get_datatype thy tyco
   of SOME _ => get_eq_datatype thy tyco
    | NONE => [TypecopyPackage.get_eq thy tyco];
  fun constrain_op_eq_thms thy thms =
    let
      fun add_eq (Const ("op =", ty)) =
            fold (insert (eq_fst (op =))) (Term.add_tvarsT ty [])
        | add_eq _ =
            I
      val eqs = fold (fold_aterms add_eq o Thm.prop_of) thms [];
      val instT = map (fn (v_i, sort) =>
        (Thm.ctyp_of thy (TVar (v_i, sort)),
           Thm.ctyp_of thy (TVar (v_i, Sorts.inter_sort (Sign.classes_of thy)
             (sort, [HOLogic.class_eq]))))) eqs;
    in
      thms
      |> map (Thm.instantiate (instT, []))
    end;
in
  fun get_eq thy tyco =
    get_eq_thms thy tyco
    |> maps ((#mk o #mk_rews o snd o MetaSimplifier.rep_ss o Simplifier.simpset_of) thy)
    |> constrain_op_eq_thms thy
end;

type hook = (string * (bool * ((string * sort) list * (string * typ list) list))) list
  -> theory -> theory;

fun add_codetypes_hook_bootstrap hook thy =
  let
    fun add_spec thy (tyco, is_dt) =
      (tyco, (is_dt, get_spec thy (tyco, is_dt)));
    fun datatype_hook dtcos thy =
      hook (map (add_spec thy) (map (rpair true) dtcos)) thy;
    fun typecopy_hook ((tyco, _)) thy =
      hook ([(tyco, (false, TypecopyPackage.get_spec thy tyco))]) thy;
  in
    thy
    |> fold hook ((map o map) (add_spec thy) (codetypes_dependency thy))
    |> DatatypeHooks.add datatype_hook
    |> TypecopyPackage.add_hook typecopy_hook
  end;

fun the_codetypes_mut_specs thy ([(tyco, is_dt)]) =
      let
        val (vs, cs) = get_spec thy (tyco, is_dt)
      in (vs, [(tyco, (is_dt, cs))]) end
  | the_codetypes_mut_specs thy (tycos' as (tyco, true) :: _) =
      let
        val tycos = map fst tycos';
        val tycos'' = (map (#1 o snd) o #descr o DatatypePackage.the_datatype thy) tyco;
        val _ = if gen_subset (op =) (tycos, tycos'') then () else
          error ("type constructors are not mutually recursive: " ^ (commas o map quote) tycos);
        val (vs::_, css) = split_list (map (the o DatatypePackage.get_datatype_spec thy) tycos);
      in (vs, map2 (fn (tyco, is_dt) => fn cs => (tyco, (is_dt, cs))) tycos' css) end;


(* registering code types in code generator *)

fun add_datatype_spec (tyco, (vs, cos)) thy =
  let
    val cs = map (fn (c, tys) => (c, tys ---> Type (tyco, map TFree vs))) cos;
  in try (Code.add_datatype cs) thy |> the_default thy end;

val codetype_hook =
  fold (fn (dtco, (_ : bool, spec)) => add_datatype_spec (dtco, spec));


(* instrumentalizing the sort algebra *)

fun get_codetypes_arities thy tycos sort =
  let
    val pp = Sign.pp thy;
    val algebra = Sign.classes_of thy;
    val (vs_proto, css_proto) = the_codetypes_mut_specs thy tycos;
    val vs = map (fn (v, vsort) => (v, Sorts.inter_sort algebra (vsort, sort))) vs_proto;
    val css = map (fn (tyco, (_, cs)) => (tyco, cs)) css_proto;
    val algebra' = algebra
      |> fold (fn (tyco, _) =>
           Sorts.add_arities pp (tyco, map (fn class => (class, map snd vs)) sort)) css;
    fun typ_sort_inst ty = CodeUnit.typ_sort_inst algebra' (Logic.varifyT ty, sort);
    val venv = Vartab.empty
      |> fold (fn (v, sort) => Vartab.update_new ((v, 0), sort)) vs
      |> fold (fn (_, cs) => fold (fn (_, tys) => fold typ_sort_inst tys) cs) css;
    fun inst (v, _) = (v, (the o Vartab.lookup venv) (v, 0));
    val vs' = map inst vs;
    fun mk_arity tyco = (tyco, map snd vs', sort);
    fun mk_cons tyco (c, tys) =
      let
        val tys' = (map o Term.map_type_tfree) (TFree o inst) tys;
        val ts = Name.names Name.context "a" tys';
        val ty = (tys' ---> Type (tyco, map TFree vs'));
      in list_comb (Const (c, ty), map Free ts) end;
  in
    map (fn (tyco, cs) => (tyco, (mk_arity tyco, map (mk_cons tyco) cs))) css |> SOME
  end handle Class_Error => NONE;

fun prove_codetypes_arities tac tycos sort f after_qed thy =
  case get_codetypes_arities thy tycos sort
   of NONE => thy
    | SOME insts => let
        fun proven (tyco, asorts, sort) =
          Sorts.of_sort (Sign.classes_of thy)
            (Type (tyco, map TFree (Name.names Name.context "'a" asorts)), sort);
        val (arities, css) = (split_list o map_filter
          (fn (tyco, (arity, cs)) => if proven arity
            then NONE else SOME (arity, (tyco, cs)))) insts;
      in
        thy
        |> not (null arities) ? (
            f arities css
            #-> (fn defs =>
              Class.prove_instance tac arities defs
            #-> (fn defs =>
              after_qed arities css defs)))
      end;


(* operational equality *)

fun eq_hook specs =
  let
    fun add_eq_thms (dtco, (_, (vs, cs))) thy =
      let
        val thy_ref = Theory.check_thy thy;
        val const = Class.inst_const thy ("op =", dtco);
        val get_thms = (fn () => get_eq (Theory.deref thy_ref) dtco |> rev);
      in
        Code.add_funcl (const, Susp.delay get_thms) thy
      end;
  in
    prove_codetypes_arities (Class.intro_classes_tac [])
      (map (fn (tyco, (is_dt, _)) => (tyco, is_dt)) specs)
      [HOLogic.class_eq] ((K o K o pair) []) ((K o K o K) (fold add_eq_thms specs))
  end;



(** theory setup **)

fun add_datatype_case_const dtco thy =
  let
    val {case_name, index, descr, ...} = DatatypePackage.the_datatype thy dtco;
  in
    CodePackage.add_appconst (case_name, CodePackage.appgen_case dest_case_expr) thy
  end;

fun add_datatype_case_defs dtco thy =
  let
    val {case_rewrites, ...} = DatatypePackage.the_datatype thy dtco
  in
    fold_rev (Code.add_func true) case_rewrites thy
  end;

val setup = 
  add_codegen "datatype" datatype_codegen
  #> add_tycodegen "datatype" datatype_tycodegen 
  #> DatatypeHooks.add (fold add_datatype_case_const)
  #> DatatypeHooks.add (fold add_datatype_case_defs)

val setup_hooks =
  add_codetypes_hook_bootstrap codetype_hook
  #> add_codetypes_hook_bootstrap eq_hook


end;
