(*  Title:      Pure/Syntax/syn_trans.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Syntax translation functions.
*)

signature SYN_TRANS0 =
sig
  val eta_contract: bool ref
  val mk_binder_tr: string * string -> string * (term list -> term)
  val mk_binder_tr': string * string -> string * (term list -> term)
  val dependent_tr': string * string -> term list -> term
  val mark_bound: string -> term
  val mark_boundT: string * typ -> term
  val variant_abs': string * typ * term -> string * term
end;

signature SYN_TRANS1 =
sig
  include SYN_TRANS0
  val constrainAbsC: string
  val pure_trfuns:
      (string * (Ast.ast list -> Ast.ast)) list *
      (string * (term list -> term)) list *
      (string * (term list -> term)) list *
      (string * (Ast.ast list -> Ast.ast)) list
  val pure_trfunsT: (string * (typ -> term list -> term)) list
end;

signature SYN_TRANS =
sig
  include SYN_TRANS1
  val abs_tr': term -> term
  val prop_tr': bool -> term -> term
  val appl_ast_tr': Ast.ast * Ast.ast list -> Ast.ast
  val applC_ast_tr': Ast.ast * Ast.ast list -> Ast.ast
  val pt_to_ast: (string -> (Ast.ast list -> Ast.ast) option) -> Parser.parsetree -> Ast.ast
  val ast_to_term: (string -> (term list -> term) option) -> Ast.ast -> term
end;

structure SynTrans: SYN_TRANS =
struct

open TypeExt Lexicon Ast SynExt Parser;


(** parse (ast) translations **)

(* application *)

fun appl_ast_tr [f, args] = Appl (f :: unfold_ast "_args" args)
  | appl_ast_tr asts = raise_ast "appl_ast_tr" asts;

fun applC_ast_tr [f, args] = Appl (f :: unfold_ast "_cargs" args)
  | applC_ast_tr asts = raise_ast "applC_ast_tr" asts;


(* abstraction *)

fun idtyp_ast_tr (*"_idtyp"*) [x, ty] = Appl [Constant constrainC, x, ty]
  | idtyp_ast_tr (*"_idtyp"*) asts = raise_ast "idtyp_ast_tr" asts;

fun lambda_ast_tr (*"_lambda"*) [idts, body] =
      fold_ast_p "_abs" (unfold_ast "_idts" idts, body)
  | lambda_ast_tr (*"_lambda"*) asts = raise_ast "lambda_ast_tr" asts;

val constrainAbsC = "_constrainAbs";

fun abs_tr (*"_abs"*) [Free (x, T), body] = absfree (x, T, body)
  | abs_tr (*"_abs"*) (ts as [Const (c, _) $ Free (x, T) $ tT, body]) =
      if c = constrainC
        then const constrainAbsC $ absfree (x, T, body) $ tT
      else raise_term "abs_tr" ts
  | abs_tr (*"_abs"*) ts = raise_term "abs_tr" ts;


(* nondependent abstraction *)

fun k_tr (*"_K"*) [t] = Abs ("uu", dummyT, incr_boundvars 1 t)
  | k_tr (*"_K"*) ts = raise_term "k_tr" ts;


(* binder *)

fun mk_binder_tr (sy, name) =
  let
    fun tr (Free (x, T), t) = const name $ absfree (x, T, t)
      | tr (Const ("_idts", _) $ idt $ idts, t) = tr (idt, tr (idts, t))
      | tr (t1 as Const (c, _) $ Free (x, T) $ tT, t) =
          if c = constrainC then
            const name $ (const constrainAbsC $ absfree (x, T, t) $ tT)
          else raise_term "binder_tr" [t1, t]
      | tr (t1, t2) = raise_term "binder_tr" [t1, t2];

    fun binder_tr (*sy*) [idts, body] = tr (idts, body)
      | binder_tr (*sy*) ts = raise_term "binder_tr" ts;
  in
    (sy, binder_tr)
  end;


(* meta propositions *)

fun aprop_tr (*"_aprop"*) [t] = const constrainC $ t $ const "prop"
  | aprop_tr (*"_aprop"*) ts = raise_term "aprop_tr" ts;

fun ofclass_tr (*"_ofclass"*) [ty, cls] =
      cls $ (const constrainC $ const "TYPE" $ (const "itself" $ ty))
  | ofclass_tr (*"_ofclass"*) ts = raise_term "ofclass_tr" ts;


(* meta implication *)

fun bigimpl_ast_tr (*"_bigimpl"*) [asms, concl] =
      fold_ast_p "==>" (unfold_ast "_asms" asms, concl)
  | bigimpl_ast_tr (*"_bigimpl"*) asts = raise_ast "bigimpl_ast_tr" asts;



(** print (ast) translations **)

(* application *)

fun appl_ast_tr' (f, []) = raise_ast "appl_ast_tr'" [f]
  | appl_ast_tr' (f, args) = Appl [Constant "_appl", f, fold_ast "_args" args];

fun applC_ast_tr' (f, []) = raise_ast "applC_ast_tr'" [f]
  | applC_ast_tr' (f, args) =
      Appl [Constant "_applC", f, fold_ast "_cargs" args];


(* abstraction *)

fun mark_boundT x_T = const "_bound" $ Free x_T;
fun mark_bound x = mark_boundT (x, dummyT);

fun strip_abss vars_of body_of tm =
  let
    val vars = vars_of tm;
    val body = body_of tm;
    val rev_new_vars = rename_wrt_term body vars;
  in
    (map mark_boundT (rev rev_new_vars),
      subst_bounds (map (mark_bound o #1) rev_new_vars, body))
  end;

(*do (partial) eta-contraction before printing*)

val eta_contract = ref true;

fun eta_contr tm =
  let
    fun eta_abs (Abs (a, T, t)) =
          (case eta_abs t of
            t' as f $ u =>
              (case eta_abs u of
                Bound 0 =>
                  if not (0 mem loose_bnos f) then incr_boundvars ~1 f
                  else Abs (a, T, t')
              | _ => Abs (a, T, t'))
          | t' => Abs (a, T, t'))
      | eta_abs t = t;
  in
    if ! eta_contract then eta_abs tm else tm
  end;


fun abs_tr' tm =
  foldr (fn (x, t) => const "_abs" $ x $ t)
    (strip_abss strip_abs_vars strip_abs_body (eta_contr tm));


fun abs_ast_tr' (*"_abs"*) asts =
  (case unfold_ast_p "_abs" (Appl (Constant "_abs" :: asts)) of
    ([], _) => raise_ast "abs_ast_tr'" asts
  | (xs, body) => Appl [Constant "_lambda", fold_ast "_idts" xs, body]);


(* binder *)

fun mk_binder_tr' (name, sy) =
  let
    fun mk_idts [] = raise Match    (*abort translation*)
      | mk_idts [idt] = idt
      | mk_idts (idt :: idts) = const "_idts" $ idt $ mk_idts idts;

    fun tr' t =
      let
        val (xs, bd) = strip_abss (strip_qnt_vars name) (strip_qnt_body name) t;
      in
        const sy $ mk_idts xs $ bd
      end;

    fun binder_tr' (*name*) (t :: ts) =
          list_comb (tr' (const name $ t), ts)
      | binder_tr' (*name*) [] = raise Match;
  in
    (name, binder_tr')
  end;


(* idts *)

fun idts_ast_tr' (*"_idts"*) [Appl [Constant c, x, ty], xs] =
      if c = constrainC then
        Appl [Constant "_idts", Appl [Constant "_idtyp", x, ty], xs]
      else raise Match
  | idts_ast_tr' (*"_idts"*) _ = raise Match;


(* meta propositions *)

fun prop_tr' show_sorts tm =
  let
    fun aprop t = const "_aprop" $ t;
    val mk_ofclass = if show_sorts then "_mk_ofclassS" else "_mk_ofclass";

    fun is_prop Ts t =
      fastype_of1 (Ts, t) = propT handle TERM _ => false;

    fun tr' _ (t as Const _) = t
      | tr' _ (t as Free (x, T)) =
          if T = propT then aprop (free x) else t
      | tr' _ (t as Var (xi, T)) =
          if T = propT then aprop (var xi) else t
      | tr' Ts (t as Bound _) =
          if is_prop Ts t then aprop t else t
      | tr' Ts (Abs (x, T, t)) = Abs (x, T, tr' (T :: Ts) t)
      | tr' Ts (t as t1 $ (t2 as Const ("TYPE", Type ("itself", [T])))) =
          if is_prop Ts t then Const (mk_ofclass, T) $ tr' Ts t1
          else tr' Ts t1 $ tr' Ts t2
      | tr' Ts (t as t1 $ t2) =
          (if is_Const (head_of t) orelse not (is_prop Ts t)
            then I else aprop) (tr' Ts t1 $ tr' Ts t2);
  in
    tr' [] tm
  end;


fun mk_ofclass_tr' (*"_mk_ofclass"*) T [t] =
      const "_ofclass" $ term_of_typ false T $ t
  | mk_ofclass_tr' (*"_mk_ofclass"*) T ts = raise_type "mk_ofclass_tr'" [T] ts;

fun mk_ofclassS_tr' (*"_mk_ofclassS"*) T [t] =
      const "_ofclass" $ term_of_typ true T $ t
  | mk_ofclassS_tr' (*"_mk_ofclassS"*) T ts = raise_type "mk_ofclassS_tr'" [T] ts;


(* meta implication *)

fun impl_ast_tr' (*"==>"*) asts =
  (case unfold_ast_p "==>" (Appl (Constant "==>" :: asts)) of
    (asms as _ :: _ :: _, concl)
      => Appl [Constant "_bigimpl", fold_ast "_asms" asms, concl]
  | _ => raise Match);


(* dependent / nondependent quantifiers *)

fun variant_abs' (x, T, B) =
  let val x' = variant (add_term_names (B, [])) x in
    (x', subst_bound (mark_boundT (x', T), B))
  end;

fun dependent_tr' (q, r) (A :: Abs (x, T, B) :: ts) =
      if 0 mem (loose_bnos B) then
        let val (x', B') = variant_abs' (x, dummyT, B);
        in list_comb (const q $ mark_boundT (x', T) $ A $ B', ts) end
      else list_comb (const r $ A $ B, ts)
  | dependent_tr' _ _ = raise Match;



(** pure_trfuns **)

val pure_trfuns =
 ([("_appl", appl_ast_tr), ("_applC", applC_ast_tr),
   ("_lambda", lambda_ast_tr), ("_idtyp", idtyp_ast_tr),
   ("_bigimpl", bigimpl_ast_tr)],
  [("_abs", abs_tr), ("_aprop", aprop_tr), ("_ofclass", ofclass_tr),
   ("_K", k_tr)],
  [],
  [("_abs", abs_ast_tr'), ("_idts", idts_ast_tr'), ("==>", impl_ast_tr')]);

val pure_trfunsT =
  [("_mk_ofclass", mk_ofclass_tr'), ("_mk_ofclassS", mk_ofclassS_tr')];



(** pt_to_ast **)

fun pt_to_ast trf pt =
  let
    fun trans a args =
      (case trf a of
        None => mk_appl (Constant a) args
      | Some f => f args handle exn
          => (writeln ("Error in parse ast translation for " ^ quote a);
              raise exn));

    (*translate pt bottom-up*)
    fun ast_of (Node (a, pts)) = trans a (map ast_of pts)
      | ast_of (Tip tok) = Variable (str_of_token tok);
  in
    ast_of pt
  end;



(** ast_to_term **)

fun ast_to_term trf ast =
  let
    fun trans a args =
      (case trf a of
        None => list_comb (const a, args)
      | Some f => f args handle exn
          => (writeln ("Error in parse translation for " ^ quote a);
              raise exn));

    fun term_of (Constant a) = trans a []
      | term_of (Variable x) = scan_var x
      | term_of (Appl (Constant a :: (asts as _ :: _))) =
          trans a (map term_of asts)
      | term_of (Appl (ast :: (asts as _ :: _))) =
          list_comb (term_of ast, map term_of asts)
      | term_of (ast as Appl _) = raise_ast "ast_to_term: malformed ast" [ast];
  in
    term_of ast
  end;

end;
