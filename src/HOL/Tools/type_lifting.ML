(*  Title:      HOL/Tools/type_lifting.ML
    Author:     Florian Haftmann, TU Muenchen

Functorial structure of types.
*)

signature TYPE_LIFTING =
sig
  val find_atomic: theory -> typ -> (typ * (bool * bool)) list
  val construct_mapper: theory -> (string * bool -> term)
    -> bool -> typ -> typ -> term
  val type_lifting: string option -> term -> theory -> Proof.state
  type entry
  val entries: theory -> entry Symtab.table
end;

structure Type_Lifting : TYPE_LIFTING =
struct

val compN = "comp";
val idN = "id";
val compositionalityN = "compositionality";
val identityN = "identity";

(** functorial mappers and their properties **)

(* bookkeeping *)

type entry = { mapper: string, variances: (sort * (bool * bool)) list,
  comp: thm, id: thm };

structure Data = Theory_Data(
  type T = entry Symtab.table
  val empty = Symtab.empty
  fun merge (xy : T * T) = Symtab.merge (K true) xy
  val extend = I
);

val entries = Data.get;


(* type analysis *)

fun find_atomic thy T =
  let
    val variances_of = Option.map #variances o Symtab.lookup (Data.get thy);
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

fun construct_mapper thy atomic =
  let
    val lookup = the o Symtab.lookup (Data.get thy);
    fun constructs is_contra (_, (co, contra)) T T' =
      (if co then [construct is_contra T T'] else [])
      @ (if contra then [construct (not is_contra) T T'] else [])
    and construct is_contra (T as Type (tyco, Ts)) (T' as Type (_, Ts')) =
          let
            val { mapper, variances, ... } = lookup tyco;
            val args = maps (fn (arg_pattern, (T, T')) =>
              constructs is_contra arg_pattern T T')
                (variances ~~ (Ts ~~ Ts'));
            val (U, U') = if is_contra then (T', T) else (T, T');
          in list_comb (Const (mapper, map fastype_of args ---> U --> U'), args) end
      | construct is_contra (TFree (v, _)) (TFree _) = atomic (v, is_contra);
  in construct end;


(* mapper properties *)

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
        val names = Name.invents nctxt n k;
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
    fun mk_mapper T T' args = list_comb (Const (mapper,
      map fastype_of args ---> T --> T'), args);
    val lhs = HOLogic.mk_comp (mk_mapper T2 T1 (map Free args21), mk_mapper T3 T2 (map Free args32));
    val rhs = mk_mapper T3 T1 args31;
  in fold_rev Logic.all (map Free (args21 @ args32)) ((HOLogic.mk_Trueprop o HOLogic.mk_eq) (lhs, rhs)) end;

fun make_id_prop ctxt variances (tyco, mapper) =
  let
    val (vs, ctxt') = Variable.invent_types (map fst variances) ctxt;
    val Ts = map TFree vs;
    fun bool_num b = if b then 1 else 0;
    fun mk_argT (T, (_, (co, contra))) =
      replicate (bool_num co + bool_num contra) (T --> T)
    val Ts' = maps mk_argT (Ts ~~ variances)
    val T = Type (tyco, Ts);
    val lhs = list_comb (Const (mapper, Ts' ---> T --> T),
      map (HOLogic.id_const o domain_type) Ts');
  in (HOLogic.mk_Trueprop o HOLogic.mk_eq) (lhs, HOLogic.id_const T) end;

val comp_apply = Simpdata.mk_eq @{thm o_apply};
val id_def = Simpdata.mk_eq @{thm id_def};

fun make_compositionality ctxt thm =
  let
    val ((_, [thm']), ctxt') = Variable.import false [thm] ctxt;
    val thm'' = @{thm fun_cong} OF [thm'];
    val thm''' =
      (Conv.fconv_rule o Conv.arg_conv o Conv.arg1_conv o Conv.rewr_conv) comp_apply thm'';
  in singleton (Variable.export ctxt' ctxt) thm''' end;

fun args_conv k conv =
  if k <= 0 then Conv.all_conv
  else Conv.combination_conv (args_conv (k - 1) conv) conv;

fun make_identity ctxt variances thm =
  let
    val ((_, [thm']), ctxt') = Variable.import false [thm] ctxt;
    fun bool_num b = if b then 1 else 0;
    val num_args = Integer.sum
      (map (fn (_, (co, contra)) => bool_num co + bool_num contra) variances);
    val thm'' =
      (Conv.fconv_rule o Conv.arg_conv o Conv.arg1_conv o args_conv num_args o Conv.rewr_conv) id_def thm';
  in singleton (Variable.export ctxt' ctxt) thm'' end;


(* analyzing and registering mappers *)

fun consume eq x [] = (false, [])
  | consume eq x (ys as z :: zs) = if eq (x, z) then (true, zs) else (false, ys);

fun split_mapper_typ "fun" T =
      let
        val (Ts', T') = strip_type T;
        val (Ts'', T'') = split_last Ts';
        val (Ts''', T''') = split_last Ts'';
      in (Ts''', T''', T'' --> T') end
  | split_mapper_typ tyco T =
      let
        val (Ts', T') = strip_type T;
        val (Ts'', T'') = split_last Ts';
      in (Ts'', T'', T') end;

fun analyze_variances thy tyco T =
  let
    fun bad_typ () = error ("Bad mapper type: " ^ Syntax.string_of_typ_global thy T);
    val (Ts, T1, T2) = split_mapper_typ tyco T
      handle List.Empty => bad_typ ();
    val _ = pairself
      ((fn tyco' => if tyco' = tyco then () else bad_typ ()) o fst o dest_Type) (T1, T2)
    val (vs1, vs2) = pairself (map dest_TFree o snd o dest_Type) (T1, T2)
      handle TYPE _ => bad_typ ();
    val _ = if has_duplicates (eq_fst (op =)) (vs1 @ vs2)
      then bad_typ () else ();
    fun check_variance_pair (var1 as (v1, sort1), var2 as (v2, sort2)) =
      let
        val coT = TFree var1 --> TFree var2;
        val contraT = TFree var2 --> TFree var1;
        val sort = Sign.inter_sort thy (sort1, sort2);
      in
        consume (op =) coT
        ##>> consume (op =) contraT
        #>> pair sort
      end;
    val (variances, left_variances) = fold_map check_variance_pair (vs1 ~~ vs2) Ts;
    val _ = if null left_variances then () else bad_typ ();
  in variances end;

fun gen_type_lifting prep_term some_prfx raw_t thy =
  let
    val (mapper, T) = case prep_term thy raw_t
     of Const cT => cT
      | t => error ("No constant: " ^ Syntax.string_of_term_global thy t);
    val _ = Type.no_tvars T;
    fun add_tycos (Type (tyco, Ts)) = insert (op =) tyco #> fold add_tycos Ts
      | add_tycos _ = I;
    val tycos = add_tycos T [];
    val tyco = if tycos = ["fun"] then "fun"
      else case remove (op =) "fun" tycos
       of [tyco] => tyco
        | _ => error ("Bad number of type constructors: " ^ Syntax.string_of_typ_global thy T);
    val prfx = the_default (Long_Name.base_name tyco) some_prfx;
    val variances = analyze_variances thy tyco T;
    val ctxt = ProofContext.init_global thy;
    val comp_prop = make_comp_prop ctxt variances (tyco, mapper);
    val id_prop = make_id_prop ctxt variances (tyco, mapper);
    val qualify = Binding.qualify true prfx o Binding.name;
    fun after_qed [single_comp, single_id] lthy =
      lthy
      |> Local_Theory.note ((qualify compN, []), single_comp)
      ||>> Local_Theory.note ((qualify idN, []), single_id)
      |-> (fn ((_, [comp]), (_, [id])) => fn lthy =>
        lthy
        |> Local_Theory.note ((qualify compositionalityN, []), [make_compositionality lthy comp])
        |> snd
        |> Local_Theory.note ((qualify identityN, []), [make_identity lthy variances id])
        |> snd
        |> (Local_Theory.background_theory o Data.map)
            (Symtab.update (tyco, { mapper = mapper, variances = variances,
              comp = comp, id = id })));
  in
    thy
    |> Named_Target.theory_init
    |> Proof.theorem NONE after_qed (map (fn t => [(t, [])]) [comp_prop, id_prop])
  end

val type_lifting = gen_type_lifting Sign.cert_term;
val type_lifting_cmd = gen_type_lifting Syntax.read_term_global;

val _ =
  Outer_Syntax.command "type_lifting" "register operations managing the functorial structure of a type" Keyword.thy_goal
    (Scan.option (Parse.name --| Parse.$$$ ":") -- Parse.term
      >> (fn (prfx, t) => Toplevel.print o (Toplevel.theory_to_proof (type_lifting_cmd prfx t))));

end;
