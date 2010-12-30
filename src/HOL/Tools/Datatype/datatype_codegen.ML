(*  Title:      HOL/Tools/Datatype/datatype_codegen.ML
    Author:     Stefan Berghofer and Florian Haftmann, TU Muenchen

Code generator facilities for inductive datatypes.
*)

signature DATATYPE_CODEGEN =
sig
  val setup: theory -> theory
end;

structure Datatype_Codegen : DATATYPE_CODEGEN =
struct

(** generic code generator **)

(* liberal addition of code data for datatypes *)

fun mk_constr_consts thy vs tyco cos =
  let
    val cs = map (fn (c, tys) => (c, tys ---> Type (tyco, map TFree vs))) cos;
    val cs' = map (fn c_ty as (_, ty) => (AxClass.unoverload_const thy c_ty, ty)) cs;
  in if is_some (try (Code.constrset_of_consts thy) cs')
    then SOME cs
    else NONE
  end;


(* case certificates *)

fun mk_case_cert thy tyco =
  let
    val raw_thms =
      (#case_rewrites o Datatype_Data.the_info thy) tyco;
    val thms as hd_thm :: _ = raw_thms
      |> Conjunction.intr_balanced
      |> Thm.unvarify_global
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
    |> Raw_Simplifier.rewrite_rule [(Thm.symmetric o Thm.assume) asm]
    |> Thm.implies_intr asm
    |> Thm.generalize ([], params) 0
    |> AxClass.unoverload thy
    |> Thm.varifyT_global
  end;


(* equality *)

fun mk_eq_eqns thy tyco =
  let
    val (vs, cos) = Datatype_Data.the_spec thy tyco;
    val { descr, index, inject = inject_thms, distinct = distinct_thms, ... } =
      Datatype_Data.the_info thy tyco;
    val ty = Type (tyco, map TFree vs);
    fun mk_eq (t1, t2) = Const (@{const_name HOL.equal}, ty --> ty --> HOLogic.boolT)
      $ t1 $ t2;
    fun true_eq t12 = HOLogic.mk_eq (mk_eq t12, HOLogic.true_const);
    fun false_eq t12 = HOLogic.mk_eq (mk_eq t12, HOLogic.false_const);
    val triv_injects = map_filter
     (fn (c, []) => SOME (HOLogic.mk_Trueprop (true_eq (Const (c, ty), Const (c, ty))))
       | _ => NONE) cos;
    fun prep_inject (trueprop $ (equiv $ (_ $ t1 $ t2) $ rhs)) =
      trueprop $ (equiv $ mk_eq (t1, t2) $ rhs);
    val injects = map prep_inject (nth (Datatype_Prop.make_injs [descr] vs) index);
    fun prep_distinct (trueprop $ (not $ (_ $ t1 $ t2))) =
      [trueprop $ false_eq (t1, t2), trueprop $ false_eq (t2, t1)];
    val distincts = maps prep_distinct (snd (nth (Datatype_Prop.make_distincts [descr] vs) index));
    val refl = HOLogic.mk_Trueprop (true_eq (Free ("x", ty), Free ("x", ty)));
    val simpset = Simplifier.global_context thy (HOL_basic_ss addsimps 
      (map Simpdata.mk_eq (@{thm equal} :: @{thm eq_True} :: inject_thms @ distinct_thms)));
    fun prove prop = Skip_Proof.prove_global thy [] [] prop (K (ALLGOALS (simp_tac simpset)))
      |> Simpdata.mk_eq;
  in (map prove (triv_injects @ injects @ distincts), prove refl) end;

fun add_equality vs tycos thy =
  let
    fun add_def tyco lthy =
      let
        val ty = Type (tyco, map TFree vs);
        fun mk_side const_name = Const (const_name, ty --> ty --> HOLogic.boolT)
          $ Free ("x", ty) $ Free ("y", ty);
        val def = HOLogic.mk_Trueprop (HOLogic.mk_eq
          (mk_side @{const_name HOL.equal}, mk_side @{const_name HOL.eq}));
        val def' = Syntax.check_term lthy def;
        val ((_, (_, thm)), lthy') = Specification.definition
          (NONE, (Attrib.empty_binding, def')) lthy;
        val ctxt_thy = ProofContext.init_global (ProofContext.theory_of lthy);
        val thm' = singleton (ProofContext.export lthy' ctxt_thy) thm;
      in (thm', lthy') end;
    fun tac thms = Class.intro_classes_tac []
      THEN ALLGOALS (ProofContext.fact_tac thms);
    fun prefix tyco = Binding.qualify true (Long_Name.base_name tyco) o Binding.qualify true "eq" o Binding.name;
    fun add_eq_thms tyco =
      Theory.checkpoint
      #> `(fn thy => mk_eq_eqns thy tyco)
      #-> (fn (thms, thm) => Global_Theory.note_thmss Thm.lemmaK
          [((prefix tyco "refl", [Code.add_nbe_default_eqn_attribute]), [([thm], [])]),
            ((prefix tyco "simps", [Code.add_default_eqn_attribute]), [(rev thms, [])])])
      #> snd
  in
    thy
    |> Class.instantiation (tycos, vs, [HOLogic.class_equal])
    |> fold_map add_def tycos
    |-> (fn def_thms => Class.prove_instantiation_exit_result (map o Morphism.thm)
         (fn _ => fn def_thms => tac def_thms) def_thms)
    |-> (fn def_thms => fold Code.del_eqn def_thms)
    |> fold add_eq_thms tycos
  end;


(* register a datatype etc. *)

fun add_all_code config tycos thy =
  let
    val (vs :: _, coss) = (split_list o map (Datatype_Data.the_spec thy)) tycos;
    val any_css = map2 (mk_constr_consts thy vs) tycos coss;
    val css = if exists is_none any_css then []
      else map_filter I any_css;
    val case_rewrites = maps (#case_rewrites o Datatype_Data.the_info thy) tycos;
    val certs = map (mk_case_cert thy) tycos;
    val tycos_eq = filter_out
      (fn tyco => can (Sorts.mg_domain (Sign.classes_of thy) tyco) [HOLogic.class_equal]) tycos;
  in
    if null css then thy
    else thy
      |> tap (fn _ => Datatype_Aux.message config "Registering datatype for code generator ...")
      |> fold Code.add_datatype css
      |> fold_rev Code.add_default_eqn case_rewrites
      |> fold Code.add_case certs
      |> not (null tycos_eq) ? add_equality vs tycos_eq
   end;


(** SML code generator **)

(* datatype definition *)

fun add_dt_defs thy defs dep module descr sorts gr =
  let
    val descr' = filter (can (map Datatype_Aux.dest_DtTFree o #2 o snd)) descr;
    val rtnames = map (#1 o snd) (filter (fn (_, (_, _, cs)) =>
      exists (exists Datatype_Aux.is_rec_type o snd) cs) descr');

    val (_, (tname, _, _)) :: _ = descr';
    val node_id = tname ^ " (type)";
    val module' = Codegen.if_library (Codegen.thyname_of_type thy tname) module;

    fun mk_dtdef prfx [] gr = ([], gr)
      | mk_dtdef prfx ((_, (tname, dts, cs))::xs) gr =
          let
            val tvs = map Datatype_Aux.dest_DtTFree dts;
            val cs' = map (apsnd (map (Datatype_Aux.typ_of_dtyp descr sorts))) cs;
            val ((_, type_id), gr') = Codegen.mk_type_id module' tname gr;
            val (ps, gr'') = gr' |>
              fold_map (fn (cname, cargs) =>
                fold_map (Codegen.invoke_tycodegen thy defs node_id module' false)
                  cargs ##>>
                Codegen.mk_const_id module' cname) cs';
            val (rest, gr''') = mk_dtdef "and " xs gr''
          in
            (Pretty.block (Codegen.str prfx ::
               (if null tvs then [] else
                  [Codegen.mk_tuple (map Codegen.str tvs), Codegen.str " "]) @
               [Codegen.str (type_id ^ " ="), Pretty.brk 1] @
               flat (separate [Pretty.brk 1, Codegen.str "| "]
                 (map (fn (ps', (_, cname)) => [Pretty.block
                   (Codegen.str cname ::
                    (if null ps' then [] else
                     flat ([Codegen.str " of", Pretty.brk 1] ::
                       separate [Codegen.str " *", Pretty.brk 1]
                         (map single ps'))))]) ps))) :: rest, gr''')
          end;

    fun mk_constr_term cname Ts T ps =
      flat (separate [Codegen.str " $", Pretty.brk 1]
        ([Codegen.str ("Const (\"" ^ cname ^ "\","), Pretty.brk 1,
          Codegen.mk_type false (Ts ---> T), Codegen.str ")"] :: ps));

    fun mk_term_of_def gr prfx [] = []
      | mk_term_of_def gr prfx ((_, (tname, dts, cs)) :: xs) =
          let
            val cs' = map (apsnd (map (Datatype_Aux.typ_of_dtyp descr sorts))) cs;
            val dts' = map (Datatype_Aux.typ_of_dtyp descr sorts) dts;
            val T = Type (tname, dts');
            val rest = mk_term_of_def gr "and " xs;
            val (eqs, _) = fold_map (fn (cname, Ts) => fn prfx =>
              let val args = map (fn i =>
                Codegen.str ("x" ^ string_of_int i)) (1 upto length Ts)
              in (Pretty.blk (4,
                [Codegen.str prfx, Codegen.mk_term_of gr module' false T, Pretty.brk 1,
                 if null Ts then Codegen.str (snd (Codegen.get_const_id gr cname))
                 else Codegen.parens (Pretty.block
                   [Codegen.str (snd (Codegen.get_const_id gr cname)),
                    Pretty.brk 1, Codegen.mk_tuple args]),
                 Codegen.str " =", Pretty.brk 1] @
                 mk_constr_term cname Ts T
                   (map2 (fn x => fn U => [Pretty.block [Codegen.mk_term_of gr module' false U,
                      Pretty.brk 1, x]]) args Ts)), "  | ")
              end) cs' prfx
          in eqs @ rest end;

    fun mk_gen_of_def gr prfx [] = []
      | mk_gen_of_def gr prfx ((i, (tname, dts, cs)) :: xs) =
          let
            val tvs = map Datatype_Aux.dest_DtTFree dts;
            val Us = map (Datatype_Aux.typ_of_dtyp descr sorts) dts;
            val T = Type (tname, Us);
            val (cs1, cs2) =
              List.partition (exists Datatype_Aux.is_rec_type o snd) cs;
            val SOME (cname, _) = Datatype_Aux.find_shortest_path descr i;

            fun mk_delay p = Pretty.block
              [Codegen.str "fn () =>", Pretty.brk 1, p];

            fun mk_force p = Pretty.block [p, Pretty.brk 1, Codegen.str "()"];

            fun mk_constr s b (cname, dts) =
              let
                val gs = map (fn dt => Codegen.mk_app false
                    (Codegen.mk_gen gr module' false rtnames s
                      (Datatype_Aux.typ_of_dtyp descr sorts dt))
                  [Codegen.str (if b andalso Datatype_Aux.is_rec_type dt then "0"
                     else "j")]) dts;
                val Ts = map (Datatype_Aux.typ_of_dtyp descr sorts) dts;
                val xs = map Codegen.str
                  (Datatype_Prop.indexify_names (replicate (length dts) "x"));
                val ts = map Codegen.str
                  (Datatype_Prop.indexify_names (replicate (length dts) "t"));
                val (_, id) = Codegen.get_const_id gr cname;
              in
                Codegen.mk_let
                  (map2 (fn p => fn q => Codegen.mk_tuple [p, q]) xs ts ~~ gs)
                  (Codegen.mk_tuple
                    [case xs of
                       _ :: _ :: _ => Pretty.block
                         [Codegen.str id, Pretty.brk 1, Codegen.mk_tuple xs]
                     | _ => Codegen.mk_app false (Codegen.str id) xs,
                     mk_delay (Pretty.block (mk_constr_term cname Ts T
                       (map (single o mk_force) ts)))])
              end;

            fun mk_choice [c] = mk_constr "(i-1)" false c
              | mk_choice cs = Pretty.block [Codegen.str "one_of",
                  Pretty.brk 1, Pretty.blk (1, Codegen.str "[" ::
                  flat (separate [Codegen.str ",", Pretty.fbrk]
                    (map (single o mk_delay o mk_constr "(i-1)" false) cs)) @
                  [Codegen.str "]"]), Pretty.brk 1, Codegen.str "()"];

            val gs = maps (fn s =>
              let val s' = Codegen.strip_tname s
              in [Codegen.str (s' ^ "G"), Codegen.str (s' ^ "T")] end) tvs;
            val gen_name = "gen_" ^ snd (Codegen.get_type_id gr tname)

          in
            Pretty.blk (4, separate (Pretty.brk 1) 
                (Codegen.str (prfx ^ gen_name ^
                   (if null cs1 then "" else "'")) :: gs @
                 (if null cs1 then [] else [Codegen.str "i"]) @
                 [Codegen.str "j"]) @
              [Codegen.str " =", Pretty.brk 1] @
              (if not (null cs1) andalso not (null cs2)
               then [Codegen.str "frequency", Pretty.brk 1,
                 Pretty.blk (1, [Codegen.str "[",
                   Codegen.mk_tuple [Codegen.str "i", mk_delay (mk_choice cs1)],
                   Codegen.str ",", Pretty.fbrk,
                   Codegen.mk_tuple [Codegen.str "1", mk_delay (mk_choice cs2)],
                   Codegen.str "]"]), Pretty.brk 1, Codegen.str "()"]
               else if null cs2 then
                 [Pretty.block [Codegen.str "(case", Pretty.brk 1,
                   Codegen.str "i", Pretty.brk 1, Codegen.str "of",
                   Pretty.brk 1, Codegen.str "0 =>", Pretty.brk 1,
                   mk_constr "0" true (cname, the (AList.lookup (op =) cs cname)),
                   Pretty.brk 1, Codegen.str "| _ =>", Pretty.brk 1,
                   mk_choice cs1, Codegen.str ")"]]
               else [mk_choice cs2])) ::
            (if null cs1 then []
             else [Pretty.blk (4, separate (Pretty.brk 1) 
                 (Codegen.str ("and " ^ gen_name) :: gs @ [Codegen.str "i"]) @
               [Codegen.str " =", Pretty.brk 1] @
               separate (Pretty.brk 1) (Codegen.str (gen_name ^ "'") :: gs @
                 [Codegen.str "i", Codegen.str "i"]))]) @
            mk_gen_of_def gr "and " xs
          end

  in
    (module', (Codegen.add_edge_acyclic (node_id, dep) gr
        handle Graph.CYCLES _ => gr) handle Graph.UNDEF _ =>
         let
           val gr1 = Codegen.add_edge (node_id, dep)
             (Codegen.new_node (node_id, (NONE, "", "")) gr);
           val (dtdef, gr2) = mk_dtdef "datatype " descr' gr1 ;
         in
           Codegen.map_node node_id (K (NONE, module',
             Codegen.string_of (Pretty.blk (0, separate Pretty.fbrk dtdef @
               [Codegen.str ";"])) ^ "\n\n" ^
             (if member (op =) (! Codegen.mode) "term_of" then
                Codegen.string_of (Pretty.blk (0, separate Pretty.fbrk
                  (mk_term_of_def gr2 "fun " descr') @ [Codegen.str ";"])) ^ "\n\n"
              else "") ^
             (if member (op =) (! Codegen.mode) "test" then
                Codegen.string_of (Pretty.blk (0, separate Pretty.fbrk
                  (mk_gen_of_def gr2 "fun " descr') @ [Codegen.str ";"])) ^ "\n\n"
              else ""))) gr2
         end)
  end;


(* case expressions *)

fun pretty_case thy defs dep module brack constrs (c as Const (_, T)) ts gr =
  let val i = length constrs
  in if length ts <= i then
       Codegen.invoke_codegen thy defs dep module brack (Codegen.eta_expand c ts (i+1)) gr
    else
      let
        val ts1 = take i ts;
        val t :: ts2 = drop i ts;
        val names = List.foldr OldTerm.add_term_names
          (map (fst o fst o dest_Var) (List.foldr OldTerm.add_term_vars [] ts1)) ts1;
        val (Ts, dT) = split_last (take (i+1) (binder_types T));

        fun pcase [] [] [] gr = ([], gr)
          | pcase ((cname, cargs)::cs) (t::ts) (U::Us) gr =
              let
                val j = length cargs;
                val xs = Name.variant_list names (replicate j "x");
                val Us' = take j (binder_types U);
                val frees = map2 (curry Free) xs Us';
                val (cp, gr0) = Codegen.invoke_codegen thy defs dep module false
                  (list_comb (Const (cname, Us' ---> dT), frees)) gr;
                val t' = Envir.beta_norm (list_comb (t, frees));
                val (p, gr1) = Codegen.invoke_codegen thy defs dep module false t' gr0;
                val (ps, gr2) = pcase cs ts Us gr1;
              in
                ([Pretty.block [cp, Codegen.str " =>", Pretty.brk 1, p]] :: ps, gr2)
              end;

        val (ps1, gr1) = pcase constrs ts1 Ts gr ;
        val ps = flat (separate [Pretty.brk 1, Codegen.str "| "] ps1);
        val (p, gr2) = Codegen.invoke_codegen thy defs dep module false t gr1;
        val (ps2, gr3) = fold_map (Codegen.invoke_codegen thy defs dep module true) ts2 gr2;
      in ((if not (null ts2) andalso brack then Codegen.parens else I)
        (Pretty.block (separate (Pretty.brk 1)
          (Pretty.block ([Codegen.str "(case ", p, Codegen.str " of",
             Pretty.brk 1] @ ps @ [Codegen.str ")"]) :: ps2))), gr3)
      end
  end;


(* constructors *)

fun pretty_constr thy defs dep module brack args (c as Const (s, T)) ts gr =
  let val i = length args
  in if i > 1 andalso length ts < i then
      Codegen.invoke_codegen thy defs dep module brack (Codegen.eta_expand c ts i) gr
     else
       let
         val id = Codegen.mk_qual_id module (Codegen.get_const_id gr s);
         val (ps, gr') = fold_map
           (Codegen.invoke_codegen thy defs dep module (i = 1)) ts gr;
       in
        (case args of
          _ :: _ :: _ => (if brack then Codegen.parens else I)
            (Pretty.block [Codegen.str id, Pretty.brk 1, Codegen.mk_tuple ps])
        | _ => (Codegen.mk_app brack (Codegen.str id) ps), gr')
       end
  end;


(* code generators for terms and types *)

fun datatype_codegen thy defs dep module brack t gr =
  (case strip_comb t of
    (c as Const (s, T), ts) =>
      (case Datatype_Data.info_of_case thy s of
        SOME {index, descr, ...} =>
          if is_some (Codegen.get_assoc_code thy (s, T)) then NONE
          else
            SOME (pretty_case thy defs dep module brack
              (#3 (the (AList.lookup op = descr index))) c ts gr)
      | NONE =>
          (case (Datatype_Data.info_of_constr thy (s, T), body_type T) of
            (SOME {index, descr, ...}, U as Type (tyname, _)) =>
              if is_some (Codegen.get_assoc_code thy (s, T)) then NONE
              else
                let
                  val SOME (tyname', _, constrs) = AList.lookup op = descr index;
                  val SOME args = AList.lookup op = constrs s;
                in
                  if tyname <> tyname' then NONE
                  else
                    SOME
                      (pretty_constr thy defs
                        dep module brack args c ts
                        (snd (Codegen.invoke_tycodegen thy defs dep module false U gr)))
                end
          | _ => NONE))
  | _ => NONE);

fun datatype_tycodegen thy defs dep module brack (Type (s, Ts)) gr =
      (case Datatype_Data.get_info thy s of
         NONE => NONE
       | SOME {descr, sorts, ...} =>
           if is_some (Codegen.get_assoc_type thy s) then NONE else
           let
             val (ps, gr') = fold_map
               (Codegen.invoke_tycodegen thy defs dep module false) Ts gr;
             val (module', gr'') = add_dt_defs thy defs dep module descr sorts gr' ;
             val (tyid, gr''') = Codegen.mk_type_id module' s gr''
           in SOME (Pretty.block ((if null Ts then [] else
               [Codegen.mk_tuple ps, Codegen.str " "]) @
               [Codegen.str (Codegen.mk_qual_id module tyid)]), gr''')
           end)
  | datatype_tycodegen _ _ _ _ _ _ _ = NONE;


(** theory setup **)

val setup = 
  Datatype_Data.interpretation add_all_code
  #> Codegen.add_codegen "datatype" datatype_codegen
  #> Codegen.add_tycodegen "datatype" datatype_tycodegen;

end;
