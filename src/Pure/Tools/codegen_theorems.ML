(*  Title:      Pure/Tools/CODEGEN_THEOREMS.ML
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen

Theorems used for code generation.
*)

signature CODEGEN_THEOREMS =
sig
  val add_notify: (string option -> theory -> theory) -> theory -> theory;
  val add_preproc: (theory -> thm list -> thm list) -> theory -> theory;
  val add_funn: thm -> theory -> theory;
  val add_pred: thm -> theory -> theory;
  val add_unfold: thm -> theory -> theory;
  val preprocess: theory -> thm list -> thm list;
  val preprocess_term: theory -> term -> term;
end;

structure CodegenTheorems: CODEGEN_THEOREMS =
struct

(** auxiliary **)

fun dest_funn thm =
  case try (fst o dest_Const o fst o strip_comb o fst o Logic.dest_equals o prop_of) thm
   of SOME c => SOME (c, thm)
    | NONE => NONE;

fun dest_pred thm =
  case try (fst o dest_Const o fst o strip_comb o snd o Logic.dest_implies o prop_of) thm
   of SOME c => SOME (c, thm)
    | NONE => NONE;


(** theory data **)

datatype procs = Procs of {
  preprocs: (serial * (theory -> thm list -> thm list)) list,
  notify: (serial * (string option -> theory -> theory)) list
};

fun mk_procs (preprocs, notify) = Procs { preprocs = preprocs, notify = notify };
fun map_procs f (Procs { preprocs, notify }) = mk_procs (f (preprocs, notify));
fun merge_procs _ (Procs { preprocs = preprocs1, notify = notify1 },
  Procs { preprocs = preprocs2, notify = notify2 }) =
    mk_procs (AList.merge (op =) (K true) (preprocs1, preprocs2),
      AList.merge (op =) (K true) (notify1, notify2));

datatype codethms = Codethms of {
  funns: thm list Symtab.table,
  preds: thm list Symtab.table,
  unfolds: thm list
};

fun mk_codethms ((funns, preds), unfolds) =
  Codethms { funns = funns, preds = preds, unfolds = unfolds };
fun map_codethms f (Codethms { funns, preds, unfolds }) =
  mk_codethms (f ((funns, preds), unfolds));
fun merge_codethms _ (Codethms { funns = funns1, preds = preds1, unfolds = unfolds1 },
  Codethms { funns = funns2, preds = preds2, unfolds = unfolds2 }) =
    mk_codethms ((Symtab.join (K (uncurry (fold (insert eq_thm)))) (funns1, funns2),
        Symtab.join (K (uncurry (fold (insert eq_thm)))) (preds1, preds2)),
          fold (insert eq_thm) unfolds1 unfolds2);

datatype T = T of {
  procs: procs,
  codethms: codethms
};

fun mk_T (procs, codethms) = T { procs = procs, codethms = codethms };
fun map_T f (T { procs, codethms }) = mk_T (f (procs, codethms));
fun merge_T pp (T { procs = procs1, codethms = codethms1 },
  T { procs = procs2, codethms = codethms2 }) =
    mk_T (merge_procs pp (procs1, procs2), merge_codethms pp (codethms1, codethms2));

structure CodegenTheorems = TheoryDataFun
(struct
  val name = "Pure/CodegenTheorems";
  type T = T;
  val empty = mk_T (mk_procs ([], []),
    mk_codethms ((Symtab.empty, Symtab.empty), []));
  val copy = I;
  val extend = I;
  val merge = merge_T;
  fun print _ _ = ();
end);

val _ = Context.add_setup CodegenTheorems.init;


(** notifiers and preprocessors **)

fun add_notify f =
  CodegenTheorems.map (map_T (fn (procs, codethms) =>
    (procs |> map_procs (fn (preprocs, notify) =>
      (preprocs, (serial (), f) :: notify)), codethms)));

fun notify_all c thy =
  fold (fn f => f c) (((fn Procs { notify, ... } => map snd notify)
    o (fn T { procs, ... } => procs) o CodegenTheorems.get) thy) thy;

fun add_preproc f =
  CodegenTheorems.map (map_T (fn (procs, codethms) =>
    (procs |> map_procs (fn (preprocs, notify) =>
      ((serial (), f) :: preprocs, notify)), codethms)))
  #> notify_all NONE;

fun preprocess thy =
  fold (fn f => f thy) (((fn Procs { preprocs, ... } => map snd preprocs)
    o (fn T { procs, ... } => procs) o CodegenTheorems.get) thy);

fun preprocess_term thy t =
  let
    val x = Free (variant (add_term_names (t, [])) "x", fastype_of t);
    (* fake definition *)
    val eq = setmp quick_and_dirty true (SkipProof.make_thm thy)
      (Logic.mk_equals (x, t));
    fun err () = error "preprocess_term: bad preprocessor"
  in case map prop_of (preprocess thy [eq]) of
      [Const ("==", _) $ x' $ t'] => if x = x' then t' else err ()
    | _ => err ()
  end;

fun add_unfold thm =
  CodegenTheorems.map (map_T (fn (procs, codethms) =>
    (procs, codethms |> map_codethms (fn (defs, unfolds) =>
      (defs, thm :: unfolds)))))

fun add_funn thm =
  case dest_funn thm
   of SOME (c, thm) =>
    CodegenTheorems.map (map_T (fn (procs, codethms) =>
      (procs, codethms |> map_codethms (fn ((funns, preds), unfolds) =>
        ((funns |> Symtab.default (c, []) |> Symtab.map (fn thms => thms @ [thm]), preds), unfolds)))))
    | NONE => error ("not a function equation: " ^ string_of_thm thm);

fun add_pred thm =
  case dest_pred thm
   of SOME (c, thm) =>
    CodegenTheorems.map (map_T (fn (procs, codethms) =>
      (procs, codethms |> map_codethms (fn ((funns, preds), unfolds) =>
        ((funns, preds |> Symtab.default (c, []) |> Symtab.map (fn thms => thms @ [thm])), unfolds)))))
    | NONE => error ("not a predicate clause: " ^ string_of_thm thm);


(** isar **)

end; (* struct *)
