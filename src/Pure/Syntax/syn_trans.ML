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
end;

signature SYN_TRANS1 =
sig
  include SYN_TRANS0
  structure Parser: PARSER
  local open Parser.SynExt.Ast in
    val constrainAbsC: string
    val pure_trfuns:
      (string * (ast list -> ast)) list *
      (string * (term list -> term)) list *
      (string * (term list -> term)) list *
      (string * (ast list -> ast)) list
  end
end;

signature SYN_TRANS =
sig
  include SYN_TRANS1
  local open Parser Parser.SynExt Parser.SynExt.Ast in
    val abs_tr': term -> term
    val prop_tr': bool -> term -> term
    val appl_ast_tr': ast * ast list -> ast
    val pt_to_ast: (string -> (ast list -> ast) option) -> parsetree -> ast
    val ast_to_term: (string -> (term list -> term) option) -> ast -> term
  end
end;

functor SynTransFun(structure TypeExt: TYPE_EXT and Parser: PARSER
  sharing TypeExt.SynExt = Parser.SynExt): SYN_TRANS =
struct

structure Parser = Parser;
open TypeExt Parser.Lexicon Parser.SynExt.Ast Parser.SynExt Parser;


(** parse (ast) translations **)

(* application *)

fun appl_ast_tr (*"_appl"*) [f, args] = Appl (f :: unfold_ast "_args" args)
  | appl_ast_tr (*"_appl"*) asts = raise_ast "appl_ast_tr" asts;


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


(* abstraction *)

fun strip_abss vars_of body_of tm =
  let
    val vars = vars_of tm;
    val body = body_of tm;
    val rev_new_vars = rename_wrt_term body vars;
  in
    (map Free (rev rev_new_vars),
      subst_bounds (map (free o #1) rev_new_vars, body))
  end;

(*do (partial) eta-contraction before printing*)

val eta_contract = ref false;

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

    fun is_prop tys t =
      fastype_of1 (tys, t) = propT handle TERM _ => false;

    fun tr' _ (t as Const _) = t
      | tr' _ (t as Free (x, ty)) =
          if ty = propT then aprop (free x) else t
      | tr' _ (t as Var (xi, ty)) =
          if ty = propT then aprop (var xi) else t
      | tr' tys (t as Bound _) =
          if is_prop tys t then aprop t else t
      | tr' tys (Abs (x, ty, t)) = Abs (x, ty, tr' (ty :: tys) t)
      | tr' tys (t as t1 $ (t2 as Const ("TYPE", Type ("itself", [ty])))) =
          if is_prop tys t then
            const "_ofclass" $ term_of_typ show_sorts ty $ tr' tys t1
          else tr' tys t1 $ tr' tys t2
      | tr' tys (t as t1 $ t2) =
          (if is_Const (head_of t) orelse not (is_prop tys t)
            then I else aprop) (tr' tys t1 $ tr' tys t2);
  in
    tr' [] tm
  end;


(* meta implication *)

fun impl_ast_tr' (*"==>"*) asts =
  (case unfold_ast_p "==>" (Appl (Constant "==>" :: asts)) of
    (asms as _ :: _ :: _, concl)
      => Appl [Constant "_bigimpl", fold_ast "_asms" asms, concl]
  | _ => raise Match);


(* dependent / nondependent quantifiers *)

fun dependent_tr' (q, r) (A :: Abs (x, T, B) :: ts) =
      if 0 mem (loose_bnos B) then
        let val (x', B') = variant_abs (x, dummyT, B);
        in list_comb (const q $ Free (x', T) $ A $ B', ts) end
      else list_comb (const r $ A $ B, ts)
  | dependent_tr' _ _ = raise Match;



(** pure_trfuns **)

val pure_trfuns =
 ([(applC, appl_ast_tr), ("_lambda", lambda_ast_tr), ("_idtyp", idtyp_ast_tr),
    ("_bigimpl", bigimpl_ast_tr)],
  [("_abs", abs_tr), ("_aprop", aprop_tr), ("_ofclass", ofclass_tr), ("_K", k_tr)],
  [],
  [("_abs", abs_ast_tr'), ("_idts", idts_ast_tr'), ("==>", impl_ast_tr')]);



(** pt_to_ast **)

fun pt_to_ast trf pt =
  let
    fun trans a args =
      (case trf a of
        None => mk_appl (Constant a) args
      | Some f => f args handle exn
          => (writeln ("Error in parse ast translation for " ^ quote a); raise exn));

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
          => (writeln ("Error in parse translation for " ^ quote a); raise exn));

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

