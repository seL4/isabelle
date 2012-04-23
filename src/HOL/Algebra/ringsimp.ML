(*  Author:     Clemens Ballarin

Normalisation method for locales ring and cring.
*)

signature ALGEBRA =
sig
  val print_structures: Proof.context -> unit
  val attrib_setup: theory -> theory
  val algebra_tac: Proof.context -> int -> tactic
end;

structure Algebra: ALGEBRA =
struct


(** Theory and context data **)

fun struct_eq ((s1: string, ts1), (s2, ts2)) =
  (s1 = s2) andalso eq_list (op aconv) (ts1, ts2);

structure Data = Generic_Data
(
  type T = ((string * term list) * thm list) list;
    (* Algebraic structures:
       identifier of the structure, list of operations and simp rules,
       identifier and operations identify the structure uniquely. *)
  val empty = [];
  val extend = I;
  val merge = AList.join struct_eq (K Thm.merge_thms);
);

fun print_structures ctxt =
  let
    val structs = Data.get (Context.Proof ctxt);
    val pretty_term = Pretty.quote o Syntax.pretty_term ctxt;
    fun pretty_struct ((s, ts), _) = Pretty.block
      [Pretty.str s, Pretty.str ":", Pretty.brk 1,
       Pretty.enclose "(" ")" (Pretty.breaks (map pretty_term ts))];
  in Pretty.writeln (Pretty.big_list "Algebraic structures:" (map pretty_struct structs)) end;


(** Method **)

fun struct_tac ((s, ts), simps) =
  let
    val ops = map (fst o Term.strip_comb) ts;
    fun ord (Const (a, _)) = find_index (fn (Const (b, _)) => a=b | _ => false) ops
      | ord (Free (a, _)) = find_index (fn (Free (b, _)) => a=b | _ => false) ops;
    fun less (a, b) = (Term_Ord.term_lpo ord (a, b) = LESS);
  in asm_full_simp_tac (HOL_ss addsimps simps |> Simplifier.set_termless less) end;

fun algebra_tac ctxt =
  EVERY' (map (fn s => TRY o struct_tac s) (Data.get (Context.Proof ctxt)));


(** Attribute **)

fun add_struct_thm s =
  Thm.declaration_attribute
    (fn thm => Data.map (AList.map_default struct_eq (s, []) (insert Thm.eq_thm_prop thm)));

fun del_struct s =
  Thm.declaration_attribute
    (fn _ => Data.map (AList.delete struct_eq s));

val attrib_setup =
  Attrib.setup @{binding algebra}
    (Scan.lift ((Args.add >> K true || Args.del >> K false) --| Args.colon || Scan.succeed true)
      -- Scan.lift Args.name -- Scan.repeat Args.term
      >> (fn ((b, n), ts) => if b then add_struct_thm (n, ts) else del_struct (n, ts)))
    "theorems controlling algebra method";

end;
