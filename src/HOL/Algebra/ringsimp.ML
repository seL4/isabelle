(*
  Id:        $Id$
  Author:    Clemens Ballarin

Normalisation method for locales ring and cring.
*)

signature ALGEBRA =
sig
  val print_structures: Proof.context -> unit
  val setup: theory -> theory
end;

structure Algebra: ALGEBRA =
struct


(** Theory and context data **)

fun struct_eq ((s1: string, ts1), (s2, ts2)) =
  (s1 = s2) andalso eq_list (op aconv) (ts1, ts2);

structure AlgebraData = GenericDataFun
(struct
  val name = "Algebra/algebra";
  type T = ((string * term list) * thm list) list;
    (* Algebraic structures:
       identifier of the structure, list of operations and simp rules,
       identifier and operations identify the structure uniquely. *)
  val empty = [];
  val extend = I;
  fun merge _ = AList.join struct_eq (K (Library.merge Thm.eq_thm_prop));
  fun print generic structs =
    let
      val ctxt = Context.proof_of generic;
      val pretty_term = Pretty.quote o ProofContext.pretty_term ctxt;
      fun pretty_struct ((s, ts), _) = Pretty.block
        [Pretty.str s, Pretty.str ":", Pretty.brk 1,
         Pretty.enclose "(" ")" (Pretty.breaks (map pretty_term ts))];
    in
      Pretty.big_list "Algebraic structures:" (map pretty_struct structs) |>
        Pretty.writeln
    end
end);

val print_structures = AlgebraData.print o Context.Proof;


(** Method **)

fun struct_tac ((s, ts), simps) =
  let
    val ops = map (fst o Term.strip_comb) ts;
    fun ord (Const (a, _)) = find_index (fn (Const (b, _)) => a=b | _ => false) ops
      | ord (Free (a, _)) = find_index (fn (Free (b, _)) => a=b | _ => false) ops;
    fun less (a, b) = (Term.term_lpo ord (a, b) = LESS);
  in asm_full_simp_tac (HOL_ss settermless less addsimps simps) end;

fun algebra_tac ctxt =
  EVERY' (map (fn s => TRY o struct_tac s) (AlgebraData.get (Context.Proof ctxt)));


(** Attribute **)

fun add_struct_thm s =
  Thm.declaration_attribute
    (fn thm => AlgebraData.map (AList.map_default struct_eq (s, []) (insert Thm.eq_thm_prop thm)));
fun del_struct s =
  Thm.declaration_attribute
    (fn _ => AlgebraData.map (AList.delete struct_eq s));

val attribute = Attrib.syntax
     (Scan.lift ((Args.add >> K true || Args.del >> K false) --| Args.colon ||
        Scan.succeed true) -- Scan.lift Args.name --
      Scan.repeat Args.term
      >> (fn ((b, n), ts) => if b then add_struct_thm (n, ts) else del_struct (n, ts)));


(** Setup **)

val setup =
  AlgebraData.init #>
  Method.add_methods [("algebra", Method.ctxt_args (Method.SIMPLE_METHOD' o algebra_tac),
    "normalisation of algebraic structure")] #>
  Attrib.add_attributes [("algebra", attribute, "theorems controlling algebra method")];

end;
