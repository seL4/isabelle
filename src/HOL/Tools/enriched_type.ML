(*  Title:      HOL/Tools/enriched_type.ML
    Author:     Florian Haftmann, TU Muenchen

Functorial structure of types.
*)

signature ENRICHED_TYPE =
sig
  val find_atomic: Proof.context -> typ -> (typ * (bool * bool)) list
  val construct_mapper: Proof.context -> (string * bool -> term)
    -> bool -> typ -> typ -> term
  val enriched_type: string option -> term -> local_theory -> Proof.state
  type entry
  val entries: Proof.context -> entry list Symtab.table
end;

structure Enriched_Type : ENRICHED_TYPE =
struct

(* bookkeeping *)

val compN = "comp";
val idN = "id";
val compositionalityN = "compositionality";
val identityN = "identity";

type entry = { mapper: term, variances: (sort * (bool * bool)) list,
  comp: thm, id: thm };

structure Data = Generic_Data
(
  type T = entry list Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
);

val entries = Data.get o Context.Proof;


(* type analysis *)

fun term_with_typ ctxt T t = Envir.subst_term_types
  (Type.typ_match (Proof_Context.tsig_of ctxt) (fastype_of t, T) Vartab.empty) t;

fun find_atomic ctxt T =
  let
    val variances_of = Option.map #variances o try hd o Symtab.lookup_list (entries ctxt);
    fun add_variance is_contra T =
      AList.map_default (op =) (T, (false, false))
        ((if is_contra then apsnd else apfst) (K true));
    fun analyze' is_contra (_, (co, contra)) T =
      (if co then analyze is_contra T else I)
      #> (if contra then analyze (not is_contra) T else I)
    and analyze is_contra (T as Type (tyco, Ts)) = (case variances_of tyco
          of NONE => add_variance is_contra T
           | SOME variances => fold2 (analyze' is_contra) variances Ts)
      | analyze is_contra T = add_variance is_contra T;
  in analyze false T [] end;

fun construct_mapper ctxt atomic =
  let
    val lookup = hd o Symtab.lookup_list (entries ctxt);
    fun constructs is_contra (_, (co, contra)) T T' =
      (if co then [construct is_contra T T'] else [])
      @ (if contra then [construct (not is_contra) T T'] else [])
    and construct is_contra (T as Type (tyco, Ts)) (T' as Type (_, Ts')) =
          let
            val { mapper = raw_mapper, variances, ... } = lookup tyco;
            val args = maps (fn (arg_pattern, (T, T')) =>
              constructs is_contra arg_pattern T T')
                (variances ~~ (Ts ~~ Ts'));
            val (U, U') = if is_contra then (T', T) else (T, T');
            val mapper = term_with_typ ctxt (map fastype_of args ---> U --> U') raw_mapper;
          in list_comb (mapper, args) end
      | construct is_contra (TFree (v, _)) (TFree _) = atomic (v, is_contra);
  in construct end;


(* mapper properties *)

val compositionality_ss = Simplifier.add_simp (Simpdata.mk_eq @{thm comp_def}) HOL_basic_ss;

fun make_comp_prop ctxt variances (tyco, mapper) =
  let
    val sorts = map fst variances
    val (((vs3, vs2), vs1), _) = ctxt
      |> Variable.invent_types sorts
      ||>> Variable.invent_types sorts
      ||>> Variable.invent_types sorts
    val (Ts1, Ts2, Ts3) = (map TFree vs1, map TFree vs2, map TFree vs3);
    fun mk_argT ((T, T'), (_, (co, contra))) =
      (if co then [(T --> T')] else [])
      @ (if contra then [(T' --> T)] else []);
    val contras = maps (fn (_, (co, contra)) =>
      (if co then [false] else []) @ (if contra then [true] else [])) variances;
    val Ts21 = maps mk_argT ((Ts2 ~~ Ts1) ~~ variances);
    val Ts32 = maps mk_argT ((Ts3 ~~ Ts2) ~~ variances);
    fun invents n k nctxt =
      let
        val names = Name.invent nctxt n k;
      in (names, fold Name.declare names nctxt) end;
    val ((names21, names32), nctxt) = Variable.names_of ctxt
      |> invents "f" (length Ts21)
      ||>> invents "f" (length Ts32);
    val T1 = Type (tyco, Ts1);
    val T2 = Type (tyco, Ts2);
    val T3 = Type (tyco, Ts3);
    val (args21, args32) = (names21 ~~ Ts21, names32 ~~ Ts32);
    val args31 = map2 (fn is_contra => fn ((f21, T21), (f32, T32)) =>
      if not is_contra then
        HOLogic.mk_comp (Free (f21, T21), Free (f32, T32))
      else
        HOLogic.mk_comp (Free (f32, T32), Free (f21, T21))
      ) contras (args21 ~~ args32)
    fun mk_mapper T T' args = list_comb
      (term_with_typ ctxt (map fastype_of args ---> T --> T') mapper, args);
    val mapper21 = mk_mapper T2 T1 (map Free args21);
    val mapper32 = mk_mapper T3 T2 (map Free args32);
    val mapper31 = mk_mapper T3 T1 args31;
    val eq1 = (HOLogic.mk_Trueprop o HOLogic.mk_eq)
      (HOLogic.mk_comp (mapper21, mapper32), mapper31);
    val x = Free (the_single (Name.invent nctxt (Long_Name.base_name tyco) 1), T3)
    val eq2 = (HOLogic.mk_Trueprop o HOLogic.mk_eq)
      (mapper21 $ (mapper32 $ x), mapper31 $ x);
    val comp_prop = fold_rev Logic.all (map Free (args21 @ args32)) eq1;
    val compositionality_prop = fold_rev Logic.all (map Free (args21 @ args32) @ [x]) eq2;
    fun prove_compositionality ctxt comp_thm = Skip_Proof.prove ctxt [] [] compositionality_prop
      (K (ALLGOALS (Method.insert_tac [@{thm fun_cong} OF [comp_thm]]
        THEN' Simplifier.asm_lr_simp_tac compositionality_ss
        THEN_ALL_NEW (Goal.assume_rule_tac ctxt))));
  in (comp_prop, prove_compositionality) end;

val identity_ss = Simplifier.add_simp (Simpdata.mk_eq @{thm id_def}) HOL_basic_ss;

fun make_id_prop ctxt variances (tyco, mapper) =
  let
    val (vs, _) = Variable.invent_types (map fst variances) ctxt;
    val Ts = map TFree vs;
    fun bool_num b = if b then 1 else 0;
    fun mk_argT (T, (_, (co, contra))) =
      replicate (bool_num co + bool_num contra) T
    val arg_Ts = maps mk_argT (Ts ~~ variances)
    val T = Type (tyco, Ts);
    val head = term_with_typ ctxt (map (fn T => T --> T) arg_Ts ---> T --> T) mapper;
    val lhs1 = list_comb (head, map (HOLogic.id_const) arg_Ts);
    val lhs2 = list_comb (head, map (fn arg_T => Abs ("x", arg_T, Bound 0)) arg_Ts);
    val rhs = HOLogic.id_const T;
    val (id_prop, identity_prop) = pairself
      (HOLogic.mk_Trueprop o HOLogic.mk_eq o rpair rhs) (lhs1, lhs2);
    fun prove_identity ctxt id_thm = Skip_Proof.prove ctxt [] [] identity_prop
      (K (ALLGOALS (Method.insert_tac [id_thm] THEN' Simplifier.asm_lr_simp_tac identity_ss)));
  in (id_prop, prove_identity) end;


(* analyzing and registering mappers *)

fun consume eq x [] = (false, [])
  | consume eq x (ys as z :: zs) = if eq (x, z) then (true, zs) else (false, ys);

fun split_mapper_typ "fun" T =
      let
        val (Ts', T') = strip_type T;
        val (Ts'', T'') = split_last Ts';
        val (Ts''', T''') = split_last Ts'';
      in (Ts''', T''', T'' --> T') end
  | split_mapper_typ _ T =
      let
        val (Ts', T') = strip_type T;
        val (Ts'', T'') = split_last Ts';
      in (Ts'', T'', T') end;

fun analyze_mapper ctxt input_mapper =
  let
    val T = fastype_of input_mapper;
    val _ = Type.no_tvars T;
    val _ =
      if null (subtract (op =) (Term.add_tfreesT T []) (Term.add_tfrees input_mapper []))
      then ()
      else error ("Illegal additional type variable(s) in term: " ^ Syntax.string_of_term ctxt input_mapper);
    val _ =
      if null (Term.add_vars (singleton
        (Variable.export_terms (Variable.auto_fixes input_mapper ctxt) ctxt) input_mapper) [])
      then ()
      else error ("Illegal locally free variable(s) in term: "
        ^ Syntax.string_of_term ctxt input_mapper);;
    val mapper = singleton (Variable.polymorphic ctxt) input_mapper;
    val _ =
      if null (Term.add_tfreesT (fastype_of mapper) []) then ()
      else error ("Illegal locally fixed type variable(s) in type: " ^ Syntax.string_of_typ ctxt T);
    fun add_tycos (Type (tyco, Ts)) = insert (op =) tyco #> fold add_tycos Ts
      | add_tycos _ = I;
    val tycos = add_tycos T [];
    val tyco = if tycos = ["fun"] then "fun"
      else case remove (op =) "fun" tycos
       of [tyco] => tyco
        | _ => error ("Bad number of type constructors: " ^ Syntax.string_of_typ ctxt T);
  in (mapper, T, tyco) end;

fun analyze_variances ctxt tyco T =
  let
    fun bad_typ () = error ("Bad mapper type: " ^ Syntax.string_of_typ ctxt T);
    val (Ts, T1, T2) = split_mapper_typ tyco T
      handle List.Empty => bad_typ ();
    val _ = pairself
      ((fn tyco' => if tyco' = tyco then () else bad_typ ()) o fst o dest_Type) (T1, T2)
      handle TYPE _ => bad_typ ();
    val (vs1, vs2) = pairself (map dest_TFree o snd o dest_Type) (T1, T2)
      handle TYPE _ => bad_typ ();
    val _ = if has_duplicates (eq_fst (op =)) (vs1 @ vs2)
      then bad_typ () else ();
    fun check_variance_pair (var1 as (_, sort1), var2 as (_, sort2)) =
      let
        val coT = TFree var1 --> TFree var2;
        val contraT = TFree var2 --> TFree var1;
        val sort = Sign.inter_sort (Proof_Context.theory_of ctxt) (sort1, sort2);
      in
        consume (op =) coT
        ##>> consume (op =) contraT
        #>> pair sort
      end;
    val (variances, left_variances) = fold_map check_variance_pair (vs1 ~~ vs2) Ts;
    val _ = if null left_variances then () else bad_typ ();
  in variances end;

fun gen_enriched_type prep_term some_prfx raw_mapper lthy =
  let
    val (mapper, T, tyco) = analyze_mapper lthy (prep_term lthy raw_mapper);
    val prfx = the_default (Long_Name.base_name tyco) some_prfx;
    val variances = analyze_variances lthy tyco T;
    val (comp_prop, prove_compositionality) = make_comp_prop lthy variances (tyco, mapper);
    val (id_prop, prove_identity) = make_id_prop lthy variances (tyco, mapper);
    val qualify = Binding.qualify true prfx o Binding.name;
    fun mapper_declaration comp_thm id_thm phi context =
      let
        val typ_instance = Sign.typ_instance (Context.theory_of context);
        val mapper' = Morphism.term phi mapper;
        val T_T' = pairself fastype_of (mapper, mapper');
        val vars = Term.add_vars mapper' [];
      in
        if null vars andalso typ_instance T_T' andalso typ_instance (swap T_T')
        then (Data.map o Symtab.cons_list) (tyco,
          { mapper = mapper', variances = variances,
            comp = Morphism.thm phi comp_thm, id = Morphism.thm phi id_thm }) context
        else context
      end;
    fun after_qed [single_comp_thm, single_id_thm] lthy =
      lthy
      |> Local_Theory.note ((qualify compN, []), single_comp_thm)
      ||>> Local_Theory.note ((qualify idN, []), single_id_thm)
      |-> (fn ((_, [comp_thm]), (_, [id_thm])) => fn lthy =>
        lthy
        |> Local_Theory.note ((qualify compositionalityN, []),
            [prove_compositionality lthy comp_thm])
        |> snd
        |> Local_Theory.note ((qualify identityN, []),
            [prove_identity lthy id_thm])
        |> snd
        |> Local_Theory.declaration {syntax = false, pervasive = false}
          (mapper_declaration comp_thm id_thm))
  in
    lthy
    |> Proof.theorem NONE after_qed (map (fn t => [(t, [])]) [comp_prop, id_prop])
  end

val enriched_type = gen_enriched_type Syntax.check_term;
val enriched_type_cmd = gen_enriched_type Syntax.read_term;

val _ = Outer_Syntax.local_theory_to_proof "enriched_type"
  "register operations managing the functorial structure of a type"
  Keyword.thy_goal (Scan.option (Parse.name --| @{keyword ":"}) -- Parse.term
    >> (fn (prfx, t) => enriched_type_cmd prfx t));

end;
