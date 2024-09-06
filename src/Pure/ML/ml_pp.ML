(*  Title:      Pure/ML/ml_pp.ML
    Author:     Makarius

ML toplevel pretty-printing for logical entities.
*)

signature ML_PP =
sig
  val toplevel_context: unit -> Proof.context
  val pp_context: Proof.context -> Pretty.T
  val pp_typ: Proof.context -> typ -> Pretty.T
  val pp_term: Proof.context -> term -> Pretty.T
  val pp_thm: Proof.context -> thm -> Pretty.T
end;

structure ML_PP: sig end =
struct

(* logical context *)

(*ML compiler toplevel context: fallback on theory Pure for regular runtime*)
fun toplevel_context () =
  let
    fun global_context () =
      Theory.get_pure ()
      |> Config.put_global Name_Space.names_long true
      |> Syntax.init_pretty_global;
  in
    (case Context.get_generic_context () of
      SOME (Context.Proof ctxt) => ctxt
    | SOME (Context.Theory thy) =>
        (case try Syntax.init_pretty_global thy of
          SOME ctxt => ctxt
        | NONE => global_context ())
    | NONE => global_context ())
  end;

fun pp_context ctxt =
 (if Config.get ctxt Proof_Context.debug then
    Pretty.quote (Pretty.big_list "proof context:" (Proof_Context.pretty_context ctxt))
  else Pretty.str "<context>");


(* logical entities (with syntax) *)

fun pp_typ ctxt T = Pretty.quote (Syntax.pretty_typ ctxt T);
fun pp_term ctxt t = Pretty.quote (Syntax.pretty_term ctxt t);
fun pp_thm ctxt th = Thm.pretty_thm_raw ctxt {quote = true, show_hyps = false} th;

val _ =
  ML_system_pp (fn _ => fn _ => Pretty.to_ML o pp_context);

val _ =
  ML_system_pp (fn depth => fn _ => fn th =>
    ML_Pretty.prune depth (Pretty.to_ML (pp_thm (toplevel_context ()) th)));

val _ =
  ML_system_pp (fn depth => fn _ => fn ct =>
    ML_Pretty.prune depth (Pretty.to_ML (pp_term (toplevel_context ()) (Thm.term_of ct))));

val _ =
  ML_system_pp (fn depth => fn _ => fn cT =>
    ML_Pretty.prune depth (Pretty.to_ML (pp_typ (toplevel_context ()) (Thm.typ_of cT))));

val _ =
  ML_system_pp (fn depth => fn _ => fn T =>
    ML_Pretty.prune depth (Pretty.to_ML (pp_typ (toplevel_context ()) T)));

val _ =
  ML_system_pp (fn depth => fn _ => fn T =>
    ML_Pretty.prune depth (Pretty.to_ML (pp_typ (toplevel_context ()) (ZTerm.typ_of T))));


(* ML term and proofterm *)

local

fun prt_app name prt = Pretty.block [Pretty.str (name ^ " "), prt];
fun prt_apps name = Pretty.enum "," (name ^ " (") ")";

fun prt_term parens (dp: FixedInt.int) t =
  if dp <= 0 then Pretty.dots
  else
    (case t of
      _ $ _ =>
        op :: (strip_comb t)
        |> map_index (fn (i, u) => prt_term true (dp - FixedInt.fromInt i - 1) u)
        |> Pretty.separate " $"
        |> (if parens then Pretty.enclose "(" ")" else Pretty.block)
    | Abs (a, T, b) =>
        prt_apps "Abs"
         [Pretty.from_ML (ML_system_pretty (a, dp - 1)),
          Pretty.from_ML (ML_system_pretty (T, dp - 2)),
          prt_term false (dp - 3) b]
    | Const a => prt_app "Const" (Pretty.from_ML (ML_system_pretty (a, dp - 1)))
    | Free a => prt_app "Free" (Pretty.from_ML (ML_system_pretty (a, dp - 1)))
    | Var a => prt_app "Var" (Pretty.from_ML (ML_system_pretty (a, dp - 1)))
    | Bound a => prt_app "Bound" (Pretty.from_ML (ML_system_pretty (a, dp - 1))));

fun prt_proof parens dp prf =
  if dp <= 0 then Pretty.dots
  else
    (case prf of
      _ % _ => prt_proofs parens dp prf
    | _ %% _ => prt_proofs parens dp prf
    | Abst (a, T, b) =>
        prt_apps "Abst"
         [Pretty.from_ML (ML_system_pretty (a, dp - 1)),
          Pretty.from_ML (ML_system_pretty (T, dp - 2)),
          prt_proof false (dp - 3) b]
    | AbsP (a, t, b) =>
        prt_apps "AbsP"
         [Pretty.from_ML (ML_system_pretty (a, dp - 1)),
          Pretty.from_ML (ML_system_pretty (t, dp - 2)),
          prt_proof false (dp - 3) b]
    | Hyp t => prt_app "Hyp" (prt_term true (dp - 1) t)
    | MinProof => Pretty.str "MinProof"
    | PBound a => prt_app "PBound" (Pretty.from_ML (ML_system_pretty (a, dp - 1)))
    | PAxm a => prt_app "PAxm" (Pretty.from_ML (ML_system_pretty (a, dp - 1)))
    | PClass a => prt_app "PClass" (Pretty.from_ML (ML_system_pretty (a, dp - 1)))
    | Oracle a => prt_app "Oracle" (Pretty.from_ML (ML_system_pretty (a, dp - 1)))
    | PThm a => prt_app "PThm" (Pretty.from_ML (ML_system_pretty (a, dp - 1))))

and prt_proofs parens dp prf =
  let
    val (head, args) = strip_proof prf [];
    val prts =
      head (dp - 1) :: flat (map_index (fn (i, prt) => prt (dp - FixedInt.fromInt i - 2)) args);
  in if parens then Pretty.enclose "(" ")" prts else Pretty.block prts end

and strip_proof (p % t) res =
      strip_proof p
        ((fn d =>
          [Pretty.str " %", Pretty.brk 1,
            Pretty.from_ML (ML_system_pretty (t, d))]) :: res)
  | strip_proof (p %% q) res =
      strip_proof p ((fn d => [Pretty.str " %%", Pretty.brk 1, prt_proof true d q]) :: res)
  | strip_proof p res = (fn d => prt_proof true d p, res);

in

val _ = ML_system_pp (fn depth => fn _ => Pretty.to_ML o prt_term false depth);
val _ = ML_system_pp (fn depth => fn _ => fn prf => Pretty.to_ML (prt_proof false depth prf));

end;

end;
