(*  Title:      HOL/Tools/datatype_codegen.ML
    Author:     Stefan Berghofer and Florian Haftmann, TU Muenchen

Code generator facilities for inductive datatypes.
*)

signature DATATYPE_CODEGEN =
sig
  val mk_eq: theory -> string -> thm list
  val mk_case_cert: theory -> string -> thm
  val setup: theory -> theory
end;

structure DatatypeCodegen : DATATYPE_CODEGEN =
struct

(** SML code generator **)

open Codegen;

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

fun add_dt_defs thy defs dep module (descr: DatatypeAux.descr) sorts gr =
  let
    val descr' = List.filter (can (map DatatypeAux.dest_DtTFree o #2 o snd)) descr;
    val rtnames = map (#1 o snd) (List.filter (fn (_, (_, _, cs)) =>
      exists (exists DatatypeAux.is_rec_type o snd) cs) descr');

    val (_, (tname, _, _)) :: _ = descr';
    val node_id = tname ^ " (type)";
    val module' = if_library (thyname_of_type thy tname) module;

    fun mk_dtdef prfx [] gr = ([], gr)
      | mk_dtdef prfx ((_, (tname, dts, cs))::xs) gr =
          let
            val tvs = map DatatypeAux.dest_DtTFree dts;
            val cs' = map (apsnd (map (DatatypeAux.typ_of_dtyp descr sorts))) cs;
            val ((_, type_id), gr') = mk_type_id module' tname gr;
            val (ps, gr'') = gr' |>
              fold_map (fn (cname, cargs) =>
                fold_map (invoke_tycodegen thy defs node_id module' false)
                  cargs ##>>
                mk_const_id module' cname) cs';
            val (rest, gr''') = mk_dtdef "and " xs gr''
          in
            (Pretty.block (str prfx ::
               (if null tvs then [] else
                  [mk_tuple (map str tvs), str " "]) @
               [str (type_id ^ " ="), Pretty.brk 1] @
               List.concat (separate [Pretty.brk 1, str "| "]
                 (map (fn (ps', (_, cname)) => [Pretty.block
                   (str cname ::
                    (if null ps' then [] else
                     List.concat ([str " of", Pretty.brk 1] ::
                       separate [str " *", Pretty.brk 1]
                         (map single ps'))))]) ps))) :: rest, gr''')
          end;

    fun mk_constr_term cname Ts T ps =
      List.concat (separate [str " $", Pretty.brk 1]
        ([str ("Const (\"" ^ cname ^ "\","), Pretty.brk 1,
          mk_type false (Ts ---> T), str ")"] :: ps));

    fun mk_term_of_def gr prfx [] = []
      | mk_term_of_def gr prfx ((_, (tname, dts, cs)) :: xs) =
          let
            val cs' = map (apsnd (map (DatatypeAux.typ_of_dtyp descr sorts))) cs;
            val dts' = map (DatatypeAux.typ_of_dtyp descr sorts) dts;
            val T = Type (tname, dts');
            val rest = mk_term_of_def gr "and " xs;
            val (_, eqs) = foldl_map (fn (prfx, (cname, Ts)) =>
              let val args = map (fn i =>
                str ("x" ^ string_of_int i)) (1 upto length Ts)
              in ("  | ", Pretty.blk (4,
                [str prfx, mk_term_of gr module' false T, Pretty.brk 1,
                 if null Ts then str (snd (get_const_id gr cname))
                 else parens (Pretty.block
                   [str (snd (get_const_id gr cname)),
                    Pretty.brk 1, mk_tuple args]),
                 str " =", Pretty.brk 1] @
                 mk_constr_term cname Ts T
                   (map (fn (x, U) => [Pretty.block [mk_term_of gr module' false U,
                      Pretty.brk 1, x]]) (args ~~ Ts))))
              end) (prfx, cs')
          in eqs @ rest end;

    fun mk_gen_of_def gr prfx [] = []
      | mk_gen_of_def gr prfx ((i, (tname, dts, cs)) :: xs) =
          let
            val tvs = map DatatypeAux.dest_DtTFree dts;
            val Us = map (DatatypeAux.typ_of_dtyp descr sorts) dts;
            val T = Type (tname, Us);
            val (cs1, cs2) =
              List.partition (exists DatatypeAux.is_rec_type o snd) cs;
            val SOME (cname, _) = find_nonempty descr [i] i;

            fun mk_delay p = Pretty.block
              [str "fn () =>", Pretty.brk 1, p];

            fun mk_force p = Pretty.block [p, Pretty.brk 1, str "()"];

            fun mk_constr s b (cname, dts) =
              let
                val gs = map (fn dt => mk_app false (mk_gen gr module' false rtnames s
                    (DatatypeAux.typ_of_dtyp descr sorts dt))
                  [str (if b andalso DatatypeAux.is_rec_type dt then "0"
                     else "j")]) dts;
                val Ts = map (DatatypeAux.typ_of_dtyp descr sorts) dts;
                val xs = map str
                  (DatatypeProp.indexify_names (replicate (length dts) "x"));
                val ts = map str
                  (DatatypeProp.indexify_names (replicate (length dts) "t"));
                val (_, id) = get_const_id gr cname
              in
                mk_let
                  (map2 (fn p => fn q => mk_tuple [p, q]) xs ts ~~ gs)
                  (mk_tuple
                    [case xs of
                       _ :: _ :: _ => Pretty.block
                         [str id, Pretty.brk 1, mk_tuple xs]
                     | _ => mk_app false (str id) xs,
                     mk_delay (Pretty.block (mk_constr_term cname Ts T
                       (map (single o mk_force) ts)))])
              end;

            fun mk_choice [c] = mk_constr "(i-1)" false c
              | mk_choice cs = Pretty.block [str "one_of",
                  Pretty.brk 1, Pretty.blk (1, str "[" ::
                  List.concat (separate [str ",", Pretty.fbrk]
                    (map (single o mk_delay o mk_constr "(i-1)" false) cs)) @
                  [str "]"]), Pretty.brk 1, str "()"];

            val gs = maps (fn s =>
              let val s' = strip_tname s
              in [str (s' ^ "G"), str (s' ^ "T")] end) tvs;
            val gen_name = "gen_" ^ snd (get_type_id gr tname)

          in
            Pretty.blk (4, separate (Pretty.brk 1) 
                (str (prfx ^ gen_name ^
                   (if null cs1 then "" else "'")) :: gs @
                 (if null cs1 then [] else [str "i"]) @
                 [str "j"]) @
              [str " =", Pretty.brk 1] @
              (if not (null cs1) andalso not (null cs2)
               then [str "frequency", Pretty.brk 1,
                 Pretty.blk (1, [str "[",
                   mk_tuple [str "i", mk_delay (mk_choice cs1)],
                   str ",", Pretty.fbrk,
                   mk_tuple [str "1", mk_delay (mk_choice cs2)],
                   str "]"]), Pretty.brk 1, str "()"]
               else if null cs2 then
                 [Pretty.block [str "(case", Pretty.brk 1,
                   str "i", Pretty.brk 1, str "of",
                   Pretty.brk 1, str "0 =>", Pretty.brk 1,
                   mk_constr "0" true (cname, valOf (AList.lookup (op =) cs cname)),
                   Pretty.brk 1, str "| _ =>", Pretty.brk 1,
                   mk_choice cs1, str ")"]]
               else [mk_choice cs2])) ::
            (if null cs1 then []
             else [Pretty.blk (4, separate (Pretty.brk 1) 
                 (str ("and " ^ gen_name) :: gs @ [str "i"]) @
               [str " =", Pretty.brk 1] @
               separate (Pretty.brk 1) (str (gen_name ^ "'") :: gs @
                 [str "i", str "i"]))]) @
            mk_gen_of_def gr "and " xs
          end

  in
    (module', (add_edge_acyclic (node_id, dep) gr
        handle Graph.CYCLES _ => gr) handle Graph.UNDEF _ =>
         let
           val gr1 = add_edge (node_id, dep)
             (new_node (node_id, (NONE, "", "")) gr);
           val (dtdef, gr2) = mk_dtdef "datatype " descr' gr1 ;
         in
           map_node node_id (K (NONE, module',
             string_of (Pretty.blk (0, separate Pretty.fbrk dtdef @
               [str ";"])) ^ "\n\n" ^
             (if "term_of" mem !mode then
                string_of (Pretty.blk (0, separate Pretty.fbrk
                  (mk_term_of_def gr2 "fun " descr') @ [str ";"])) ^ "\n\n"
              else "") ^
             (if "test" mem !mode then
                string_of (Pretty.blk (0, separate Pretty.fbrk
                  (mk_gen_of_def gr2 "fun " descr') @ [str ";"])) ^ "\n\n"
              else ""))) gr2
         end)
  end;


(**** case expressions ****)

fun pretty_case thy defs dep module brack constrs (c as Const (_, T)) ts gr =
  let val i = length constrs
  in if length ts <= i then
       invoke_codegen thy defs dep module brack (eta_expand c ts (i+1)) gr
    else
      let
        val ts1 = Library.take (i, ts);
        val t :: ts2 = Library.drop (i, ts);
        val names = foldr OldTerm.add_term_names
          (map (fst o fst o dest_Var) (foldr OldTerm.add_term_vars [] ts1)) ts1;
        val (Ts, dT) = split_last (Library.take (i+1, fst (strip_type T)));

        fun pcase [] [] [] gr = ([], gr)
          | pcase ((cname, cargs)::cs) (t::ts) (U::Us) gr =
              let
                val j = length cargs;
                val xs = Name.variant_list names (replicate j "x");
                val Us' = Library.take (j, fst (strip_type U));
                val frees = map Free (xs ~~ Us');
                val (cp, gr0) = invoke_codegen thy defs dep module false
                  (list_comb (Const (cname, Us' ---> dT), frees)) gr;
                val t' = Envir.beta_norm (list_comb (t, frees));
                val (p, gr1) = invoke_codegen thy defs dep module false t' gr0;
                val (ps, gr2) = pcase cs ts Us gr1;
              in
                ([Pretty.block [cp, str " =>", Pretty.brk 1, p]] :: ps, gr2)
              end;

        val (ps1, gr1) = pcase constrs ts1 Ts gr ;
        val ps = List.concat (separate [Pretty.brk 1, str "| "] ps1);
        val (p, gr2) = invoke_codegen thy defs dep module false t gr1;
        val (ps2, gr3) = fold_map (invoke_codegen thy defs dep module true) ts2 gr2;
      in ((if not (null ts2) andalso brack then parens else I)
        (Pretty.block (separate (Pretty.brk 1)
          (Pretty.block ([str "(case ", p, str " of",
             Pretty.brk 1] @ ps @ [str ")"]) :: ps2))), gr3)
      end
  end;


(**** constructors ****)

fun pretty_constr thy defs dep module brack args (c as Const (s, T)) ts gr =
  let val i = length args
  in if i > 1 andalso length ts < i then
      invoke_codegen thy defs dep module brack (eta_expand c ts i) gr
     else
       let
         val id = mk_qual_id module (get_const_id gr s);
         val (ps, gr') = fold_map
           (invoke_codegen thy defs dep module (i = 1)) ts gr;
       in (case args of
          _ :: _ :: _ => (if brack then parens else I)
            (Pretty.block [str id, Pretty.brk 1, mk_tuple ps])
        | _ => (mk_app brack (str id) ps), gr')
       end
  end;


(**** code generators for terms and types ****)

fun datatype_codegen thy defs dep module brack t gr = (case strip_comb t of
   (c as Const (s, T), ts) =>
     (case DatatypePackage.datatype_of_case thy s of
        SOME {index, descr, ...} =>
          if is_some (get_assoc_code thy (s, T)) then NONE else
          SOME (pretty_case thy defs dep module brack
            (#3 (the (AList.lookup op = descr index))) c ts gr )
      | NONE => case (DatatypePackage.datatype_of_constr thy s, strip_type T) of
        (SOME {index, descr, ...}, (_, U as Type (tyname, _))) =>
          if is_some (get_assoc_code thy (s, T)) then NONE else
          let
            val SOME (tyname', _, constrs) = AList.lookup op = descr index;
            val SOME args = AList.lookup op = constrs s
          in
            if tyname <> tyname' then NONE
            else SOME (pretty_constr thy defs
              dep module brack args c ts (snd (invoke_tycodegen thy defs dep module false U gr)))
          end
      | _ => NONE)
 | _ => NONE);

fun datatype_tycodegen thy defs dep module brack (Type (s, Ts)) gr =
      (case DatatypePackage.get_datatype thy s of
         NONE => NONE
       | SOME {descr, sorts, ...} =>
           if is_some (get_assoc_type thy s) then NONE else
           let
             val (ps, gr') = fold_map
               (invoke_tycodegen thy defs dep module false) Ts gr;
             val (module', gr'') = add_dt_defs thy defs dep module descr sorts gr' ;
             val (tyid, gr''') = mk_type_id module' s gr''
           in SOME (Pretty.block ((if null Ts then [] else
               [mk_tuple ps, str " "]) @
               [str (mk_qual_id module tyid)]), gr''')
           end)
  | datatype_tycodegen _ _ _ _ _ _ _ = NONE;


(** generic code generator **)

(* specification *)

fun add_datatype_spec vs dtco cos thy =
  let
    val cs = map (fn (c, tys) => (c, tys ---> Type (dtco, map TFree vs))) cos;
  in
    thy
    |> try (Code.add_datatype cs)
    |> the_default thy
  end;


(* case certificates *)

fun mk_case_cert thy tyco =
  let
    val raw_thms =
      (#case_rewrites o DatatypePackage.the_datatype thy) tyco;
    val thms as hd_thm :: _ = raw_thms
      |> Conjunction.intr_balanced
      |> Thm.unvarify
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
    |> AxClass.unoverload thy
    |> Thm.varifyT
  end;

fun add_datatype_cases dtco thy =
  let
    val {case_rewrites, ...} = DatatypePackage.the_datatype thy dtco;
    val cert = mk_case_cert thy dtco;
    fun add_case_liberal thy = thy
      |> try (Code.add_case cert)
      |> the_default thy;
  in
    thy
    |> add_case_liberal
    |> fold_rev Code.add_default_eqn case_rewrites
  end;


(* equality *)

local

val not_sym = @{thm HOL.not_sym};
val not_false_true = iffD2 OF [nth @{thms HOL.simp_thms} 7, TrueI];
val refl = @{thm refl};
val eqTrueI = @{thm eqTrueI};

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

in

fun mk_eq thy dtco =
  let
    val (vs, cs) = DatatypePackage.the_datatype_spec thy dtco;
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
      (Simplifier.empty_ss addsimprocs [DatatypePackage.distinct_simproc]);
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

fun add_datatypes_equality vs dtcos thy =
  let
    val vs' = (map o apsnd)
      (curry (Sorts.inter_sort (Sign.classes_of thy)) [HOLogic.class_eq]) vs;
    fun add_def dtco lthy =
      let
        val ty = Type (dtco, map TFree vs');
        fun mk_side const_name = Const (const_name, ty --> ty --> HOLogic.boolT)
          $ Free ("x", ty) $ Free ("y", ty);
        val def = HOLogic.mk_Trueprop (HOLogic.mk_eq
          (mk_side @{const_name eq_class.eq}, mk_side @{const_name "op ="}));
        val def' = Syntax.check_term lthy def;
        val ((_, (_, thm)), lthy') = Specification.definition
          (NONE, (Attrib.empty_binding, def')) lthy;
        val ctxt_thy = ProofContext.init (ProofContext.theory_of lthy);
        val thm' = singleton (ProofContext.export lthy' ctxt_thy) thm;
      in (thm', lthy') end;
    fun tac thms = Class.intro_classes_tac []
      THEN ALLGOALS (ProofContext.fact_tac thms);
    fun mk_eq' thy dtco = mk_eq thy dtco
      |> map (Code_Unit.constrain_thm thy [HOLogic.class_eq])
      |> map Simpdata.mk_eq
      |> map (MetaSimplifier.rewrite_rule [Thm.transfer thy @{thm equals_eq}])
      |> map (AxClass.unoverload thy);
    fun add_eq_thms dtco thy =
      let
        val ty = Type (dtco, map TFree vs');
        val thy_ref = Theory.check_thy thy;
        val const = AxClass.param_of_inst thy (@{const_name eq_class.eq}, dtco);
        val eq_refl = @{thm HOL.eq_refl}
          |> Thm.instantiate
              ([pairself (Thm.ctyp_of thy) (TVar (("'a", 0), @{sort eq}), Logic.varifyT ty)], [])
          |> Simpdata.mk_eq
          |> AxClass.unoverload thy;
        fun mk_thms () = (eq_refl, false)
          :: rev (map (rpair true) (mk_eq' (Theory.deref thy_ref) dtco));
      in
        Code.add_eqnl (const, Lazy.lazy mk_thms) thy
      end;
  in
    thy
    |> TheoryTarget.instantiation (dtcos, vs', [HOLogic.class_eq])
    |> fold_map add_def dtcos
    |-> (fn thms => Class.prove_instantiation_instance (K (tac thms))
    #> LocalTheory.exit_global
    #> fold Code.del_eqn thms
    #> fold add_eq_thms dtcos)
  end;


(** theory setup **)

fun add_datatype_code dtcos thy =
  let
    val (vs :: _, coss) = (split_list o map (DatatypePackage.the_datatype_spec thy)) dtcos;
  in
    thy
    |> fold2 (add_datatype_spec vs) dtcos coss
    |> fold add_datatype_cases dtcos
    |> add_datatypes_equality vs dtcos
  end;

val setup = 
  add_codegen "datatype" datatype_codegen
  #> add_tycodegen "datatype" datatype_tycodegen
  #> DatatypePackage.interpretation add_datatype_code

end;
