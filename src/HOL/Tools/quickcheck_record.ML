(*  Title:      HOL/Tools/quickcheck_record.ML
    Author:     Florian Haftmann, TU Muenchen

Quickcheck generators for records.
*)

signature QUICKCHECK_RECORD =
sig
  val ensure_random_typecopy: string -> theory -> theory
end;

structure Quickcheck_Record : QUICKCHECK_RECORD =
struct

fun termifyT T = HOLogic.mk_prodT (T, @{typ "unit => term"})
val size = @{term "i::code_numeral"};

fun mk_random_typecopy tyco vs constr T' thy =
  let
    val mk_const = curry (Sign.mk_const thy);
    val Ts = map TFree vs;  
    val T = Type (tyco, Ts);
    val Tm = termifyT T;
    val Tm' = termifyT T';
    val v = "x";
    val t_v = Free (v, Tm');
    val t_constr = Const (constr, T' --> T);
    val lhs = HOLogic.mk_random T size;
    val rhs = HOLogic.mk_ST [((HOLogic.mk_random T' size, @{typ Random.seed}), SOME (v, Tm'))]
      (HOLogic.mk_return Tm @{typ Random.seed}
      (mk_const "Code_Evaluation.valapp" [T', T]
        $ HOLogic.mk_prod (t_constr, Abs ("u", @{typ unit}, HOLogic.reflect_term t_constr)) $ t_v))
      @{typ Random.seed} (SOME Tm, @{typ Random.seed});
    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs));
  in   
    thy
    |> Class.instantiation ([tyco], vs, @{sort random})
    |> `(fn lthy => Syntax.check_term lthy eq)
    |-> (fn eq => Specification.definition (NONE, (apfst Binding.conceal Attrib.empty_binding, eq)))
    |> snd
    |> Class.prove_instantiation_exit (K (Class.intro_classes_tac []))
  end;

fun ensure_random_typecopy tyco thy =
  let
    val SOME { vs = raw_vs, constr, typ = raw_T, ... } =
      Typecopy.get_info thy tyco;
    val constrain = curry (Sorts.inter_sort (Sign.classes_of thy));
    val T = map_atyps (fn TFree (v, sort) =>
      TFree (v, constrain sort @{sort random})) raw_T;
    val vs' = Term.add_tfreesT T [];
    val vs = map (fn (v, sort) =>
      (v, the_default (constrain sort @{sort typerep}) (AList.lookup (op =) vs' v))) raw_vs;
    val can_inst = Sign.of_sort thy (T, @{sort random});
  in if can_inst then mk_random_typecopy tyco vs constr T thy else thy end;

val setup = Typecopy.interpretation ensure_random_typecopy;

end;
