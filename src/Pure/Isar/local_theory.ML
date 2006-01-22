(*  Title:      Pure/Isar/local_theory.ML
    ID:         $Id$
    Author:     Makarius

Local theory operations, with optional target locale.
*)

signature LOCAL_THEORY =
sig
  val map_theory: (theory -> theory) -> Proof.context -> Proof.context
  val map_theory_result: (theory -> 'a * theory) -> Proof.context -> 'a * Proof.context
  val init: string option -> theory -> Proof.context
  val exit: Proof.context -> theory
  val params_of: Proof.context -> (string * typ) list
  val consts: (string * typ * mixfix) list -> Proof.context ->
    ((string * typ) list * term list) * Proof.context
end;

structure LocalTheory: LOCAL_THEORY =
struct

(* local context data *)

structure Data = ProofDataFun
(
  val name = "Isar/local_theory";
  type T =
   {locale: string option,
    params: (string * typ) list,
    hyps: term list,
    exit: theory -> theory};
  fun init _ = {locale = NONE, params = [], hyps = [], exit = I};
  fun print _ _ = ();
);

val _ = Context.add_setup Data.init;


(* theory *)

fun map_theory f ctxt =
  ProofContext.transfer (f (ProofContext.theory_of ctxt)) ctxt;

fun map_theory_result f ctxt =
  let val (res, thy') = f (ProofContext.theory_of ctxt)
  in (res, ProofContext.transfer thy' ctxt) end;

fun init NONE thy = ProofContext.init thy
  | init (SOME loc) thy =
      thy
      |> Locale.init loc
      |> (fn ctxt => Data.put
          {locale = SOME loc,
           params = Locale.the_params thy loc,
           hyps = ProofContext.assms_of ctxt,   (* FIXME query locale!! *)
           exit = Sign.restore_naming thy} ctxt)
      |> map_theory (Sign.add_path loc #> Sign.no_base_names);

fun exit ctxt = #exit (Data.get ctxt) (ProofContext.theory_of ctxt);


(* local theory *)

val params_of = #params o Data.get;

fun consts decls ctxt =
  let
    val thy = ProofContext.theory_of ctxt;
    val params = params_of ctxt;
    val ps = map Free params;
    val Us = map snd params;

    val xs = decls |> map (fn (c, _, mx) => Syntax.const_name c mx);
    val Ts = map #2 decls;
    fun const x T = Term.list_comb (Const (Sign.full_name thy x, Us ---> T), ps);
  in
    ctxt
    |> map_theory (Sign.add_consts_i (decls |> map (fn (c, T, mx) => (c, Us ---> T, mx))))
    |> ProofContext.add_fixes_i (decls |> map (fn (c, T, mx) => (c, SOME T, mx)))
    |-> (fn xs' => pair ((xs' ~~ Ts), map2 const xs Ts))
  end;

end;
