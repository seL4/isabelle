(*  Title:      HOL/Tools/functorial_mappers.ML
    Author:     Florian Haftmann, TU Muenchen

Functorial mappers on types.
*)

signature FUNCTORIAL_MAPPERS =
sig
  val find_atomic: theory -> typ -> (typ * (bool * bool)) list
  val construct_mapper: theory -> (string * bool -> term)
    -> bool -> typ -> typ -> term
  val register: string -> string -> (sort * (bool * bool)) list -> thm -> thm
    -> theory -> theory
  val type_mapper: term -> theory -> Proof.state
  type entry
  val entries: theory -> entry Symtab.table
end;

structure Functorial_Mappers : FUNCTORIAL_MAPPERS =
struct

(** functorial mappers and their properties **)

(* bookkeeping *)

type entry = { mapper: string, variances: (sort * (bool * bool)) list,
  concatenate: thm, identity: thm };

structure Data = Theory_Data(
  type T = entry Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
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

fun make_concatenate_prop variances (tyco, mapper) =
  let
    fun invents n k nctxt =
      let
        val names = Name.invents nctxt n k;
      in (names, fold Name.declare names nctxt) end;
    val (((vs1, vs2), vs3), _) = Name.context
      |> invents Name.aT (length variances)
      ||>> invents Name.aT (length variances)
      ||>> invents Name.aT (length variances);
    fun mk_Ts vs = map2 (fn v => fn (sort, _) => TFree (v, sort))
      vs variances;
    val (Ts1, Ts2, Ts3) = (mk_Ts vs1, mk_Ts vs2, mk_Ts vs3);
    fun mk_argT ((T, T'), (_, (co, contra))) =
      (if co then [(T --> T')] else [])
      @ (if contra then [(T' --> T)] else []);
    val contras = maps (fn (_, (co, contra)) =>
      (if co then [false] else []) @ (if contra then [true] else [])) variances;
    val Ts21 = maps mk_argT ((Ts2 ~~ Ts1) ~~ variances);
    val Ts32 = maps mk_argT ((Ts3 ~~ Ts2) ~~ variances);
    val ((names21, names32), nctxt) = Name.context
      |> invents "f" (length Ts21)
      ||>> invents "f" (length Ts32);
    val T1 = Type (tyco, Ts1);
    val T2 = Type (tyco, Ts2);
    val T3 = Type (tyco, Ts3);
    val x = Free (the_single (Name.invents nctxt "a" 1), T3);
    val (args21, args32) = (names21 ~~ Ts21, names32 ~~ Ts32);
    val args31 = map2 (fn is_contra => fn ((f21, T21), (f32, T32)) =>
      if not is_contra then
        Abs ("x", domain_type T32, Free (f21, T21) $ (Free (f32, T32) $ Bound 0))
      else
        Abs ("x", domain_type T21, Free (f32, T32) $ (Free (f21, T21) $ Bound 0))
      ) contras (args21 ~~ args32)
    fun mk_mapper T T' args = list_comb (Const (mapper,
      map fastype_of args ---> T --> T'), args);
    val lhs = mk_mapper T2 T1 (map Free args21) $
      (mk_mapper T3 T2 (map Free args32) $ x);
    val rhs = mk_mapper T3 T1 args31 $ x;
  in (x, (HOLogic.mk_Trueprop o HOLogic.mk_eq) (lhs, rhs)) end;

fun make_identity_prop variances (tyco, mapper) =
  let
    val vs = Name.invents Name.context Name.aT (length variances);
    val Ts = map2 (fn v => fn (sort, _) => TFree (v, sort)) vs variances;
    fun bool_num b = if b then 1 else 0;
    fun mk_argT (T, (_, (co, contra))) =
      replicate (bool_num co + bool_num contra) (T --> T)
    val Ts' = maps mk_argT (Ts ~~ variances)
    val T = Type (tyco, Ts);
    val x = Free ("a", T);
    val lhs = list_comb (Const (mapper, Ts' ---> T --> T),
      map (fn T => Abs ("x", domain_type T, Bound 0)) Ts') $ x;
  in (x, (HOLogic.mk_Trueprop o HOLogic.mk_eq) (lhs, x)) end;


(* registering primitive mappers *)

fun register tyco mapper variances raw_concatenate raw_identity thy =
  let
    val (_, concatenate_prop) = make_concatenate_prop variances (tyco, mapper);
    val (_, identity_prop) = make_identity_prop variances (tyco, mapper);
    val concatenate = Goal.prove_global thy
      (Term.add_free_names concatenate_prop []) [] concatenate_prop
      (K (ALLGOALS (ProofContext.fact_tac [raw_concatenate])));
    val identity = Goal.prove_global thy
      (Term.add_free_names identity_prop []) [] identity_prop
      (K (ALLGOALS (ProofContext.fact_tac [raw_identity])));
  in
    thy
    |> Data.map (Symtab.update (tyco, { mapper = mapper,
        variances = variances,
        concatenate = concatenate, identity = identity }))
  end;

fun gen_type_mapper prep_term raw_t thy =
  let
    val t = prep_term thy raw_t;
    val after_qed = K I;
  in
    thy
    |> Named_Target.theory_init
    |> Proof.theorem NONE after_qed []
  end

val type_mapper = gen_type_mapper Sign.cert_term;
val type_mapper_cmd = gen_type_mapper Syntax.read_term_global;

val _ =
  Outer_Syntax.command "type_mapper" "register functorial mapper for type with its properties" Keyword.thy_goal
    (Parse.term >> (fn t => Toplevel.print o (Toplevel.theory_to_proof (type_mapper_cmd t))));

end;
