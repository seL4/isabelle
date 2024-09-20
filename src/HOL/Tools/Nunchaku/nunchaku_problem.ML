(*  Title:      HOL/Tools/Nunchaku/nunchaku_problem.ML
    Author:     Jasmin Blanchette, VU Amsterdam
    Copyright   2015, 2016, 2017

Abstract syntax tree for Nunchaku problems.
*)

signature NUNCHAKU_PROBLEM =
sig
  eqtype ident

  datatype ty =
    NType of ident * ty list

  datatype tm =
    NAtom of int * ty
  | NConst of ident * ty list * ty
  | NAbs of tm * tm
  | NMatch of tm * (ident * tm list * tm) list
  | NApp of tm * tm

  type nun_copy_spec =
    {abs_ty: ty,
     rep_ty: ty,
     subset: tm option,
     quotient: tm option,
     abs: tm,
     rep: tm}

  type nun_ctr_spec =
    {ctr: tm,
     arg_tys: ty list}

  type nun_co_data_spec =
    {ty: ty,
     ctrs: nun_ctr_spec list}

  type nun_const_spec =
    {const: tm,
     props: tm list}

  type nun_consts_spec =
    {consts: tm list,
     props: tm list}

  datatype nun_command =
    NTVal of ty * (int option * int option)
  | NCopy of nun_copy_spec
  | NData of nun_co_data_spec list
  | NCodata of nun_co_data_spec list
  | NVal of tm * ty
  | NPred of bool * nun_const_spec list
  | NCopred of nun_const_spec list
  | NRec of nun_const_spec list
  | NSpec of nun_consts_spec
  | NAxiom of tm
  | NGoal of tm
  | NEval of tm

  type nun_problem =
    {commandss: nun_command list list,
     sound: bool,
     complete: bool}

  type name_pool =
    {nice_of_ugly: string Symtab.table,
     ugly_of_nice: string Symtab.table}

  val nun_abstract: string
  val nun_and: string
  val nun_arrow: string
  val nun_asserting: string
  val nun_assign: string
  val nun_at: string
  val nun_axiom: string
  val nun_bar: string
  val nun_choice: string
  val nun_codata: string
  val nun_colon: string
  val nun_comma: string
  val nun_concrete: string
  val nun_conj: string
  val nun_copred: string
  val nun_copy: string
  val nun_data: string
  val nun_disj: string
  val nun_dollar: string
  val nun_dollar_anon_fun_prefix: string
  val nun_dot: string
  val nun_dummy: string
  val nun_else: string
  val nun_end: string
  val nun_equals: string
  val nun_eval: string
  val nun_exists: string
  val nun_false: string
  val nun_forall: string
  val nun_goal: string
  val nun_hash: string
  val nun_if: string
  val nun_implies: string
  val nun_irrelevant: string
  val nun_lambda: string
  val nun_lbrace: string
  val nun_lbracket: string
  val nun_lparen: string
  val nun_match: string
  val nun_mu: string
  val nun_not: string
  val nun_partial_quotient: string
  val nun_pred: string
  val nun_prop: string
  val nun_quotient: string
  val nun_rbrace: string
  val nun_rbracket: string
  val nun_rec: string
  val nun_rparen: string
  val nun_semicolon: string
  val nun_spec: string
  val nun_subset: string
  val nun_then: string
  val nun_true: string
  val nun_type: string
  val nun_unparsable: string
  val nun_unique: string
  val nun_unique_unsafe: string
  val nun_val: string
  val nun_wf: string
  val nun_with: string
  val nun__witness_of: string

  val ident_of_str: string -> ident
  val str_of_ident: ident -> string
  val encode_args: string list -> string
  val nun_const_of_str: string list -> string -> ident
  val nun_tconst_of_str: string list -> string -> ident
  val nun_free_of_str: string -> ident
  val nun_tfree_of_str: string -> ident
  val nun_var_of_str: string -> ident
  val str_of_nun_const: ident -> string list * string
  val str_of_nun_tconst: ident -> string list * string
  val str_of_nun_free: ident -> string
  val str_of_nun_tfree: ident -> string
  val str_of_nun_var: ident -> string

  val dummy_ty: ty
  val prop_ty: ty
  val mk_arrow_ty: ty * ty -> ty
  val mk_arrows_ty: ty list * ty -> ty
  val nabss: tm list * tm -> tm
  val napps: tm * tm list -> tm

  val ty_of: tm -> ty
  val safe_ty_of: tm -> ty

  val fold_map_ty_idents: (string -> 'a -> string * 'a) -> ty -> 'a -> ty * 'a
  val fold_map_tm_idents: (string -> 'a -> string * 'a) -> tm -> 'a -> tm * 'a
  val fold_map_nun_command_idents: (string -> 'a -> string * 'a) -> nun_command -> 'a ->
    nun_command * 'a
  val fold_map_nun_problem_idents: (string -> 'a -> string * 'a) -> nun_problem -> 'a ->
    nun_problem * 'a

  val allocate_nice: name_pool -> string * string -> string * name_pool

  val rcomb_tms: tm list -> tm -> tm
  val abs_tms: tm list -> tm -> tm
  val eta_expandN_tm: int -> tm -> tm
  val eta_expand_builtin_tm: tm -> tm

  val str_of_ty: ty -> string
  val str_of_tm: tm -> string
  val str_of_tmty: tm -> string

  val nice_nun_problem: nun_problem -> nun_problem * name_pool
  val str_of_nun_problem: nun_problem -> string
end;

structure Nunchaku_Problem : NUNCHAKU_PROBLEM =
struct

open Nunchaku_Util;

type ident = string;

datatype ty =
  NType of ident * ty list;

datatype tm =
  NAtom of int * ty
| NConst of ident * ty list * ty
| NAbs of tm * tm
| NMatch of tm * (ident * tm list * tm) list
| NApp of tm * tm;

type nun_copy_spec =
  {abs_ty: ty,
   rep_ty: ty,
   subset: tm option,
   quotient: tm option,
   abs: tm,
   rep: tm};

type nun_ctr_spec =
  {ctr: tm,
   arg_tys: ty list};

type nun_co_data_spec =
  {ty: ty,
   ctrs: nun_ctr_spec list};

type nun_const_spec =
  {const: tm,
   props: tm list};

type nun_consts_spec =
  {consts: tm list,
   props: tm list};

datatype nun_command =
  NTVal of ty * (int option * int option)
| NCopy of nun_copy_spec
| NData of nun_co_data_spec list
| NCodata of nun_co_data_spec list
| NVal of tm * ty
| NPred of bool * nun_const_spec list
| NCopred of nun_const_spec list
| NRec of nun_const_spec list
| NSpec of nun_consts_spec
| NAxiom of tm
| NGoal of tm
| NEval of tm;

type nun_problem =
  {commandss: nun_command list list,
   sound: bool,
   complete: bool};

type name_pool =
  {nice_of_ugly: string Symtab.table,
   ugly_of_nice: string Symtab.table};

val nun_abstract = "abstract";
val nun_and = "and";
val nun_arrow = "->";
val nun_asserting = "asserting";
val nun_assign = ":=";
val nun_at = "@";
val nun_axiom = "axiom";
val nun_bar = "|";
val nun_choice = "choice";
val nun_codata = "codata";
val nun_colon = ":";
val nun_comma = ",";
val nun_concrete = "concrete";
val nun_conj = "&&";
val nun_copred = "copred";
val nun_copy = "copy";
val nun_data = "data";
val nun_disj = "||";
val nun_dollar = "$";
val nun_dollar_anon_fun_prefix = "$anon_fun_";
val nun_dot = ".";
val nun_dummy = "_";
val nun_else = "else";
val nun_end = "end";
val nun_equals = "=";
val nun_eval = "eval";
val nun_exists = "exists";
val nun_false = "false";
val nun_forall = "forall";
val nun_goal = "goal";
val nun_hash = "#";
val nun_if = "if";
val nun_implies = "=>";
val nun_irrelevant = "?__";
val nun_lambda = "fun";
val nun_lbrace = "{";
val nun_lbracket = "[";
val nun_lparen = "(";
val nun_match = "match";
val nun_mu = "mu";
val nun_not = "~";
val nun_partial_quotient = "partial_quotient";
val nun_pred = "pred";
val nun_prop = "prop";
val nun_quotient = "quotient";
val nun_rbrace = "}";
val nun_rbracket = "]";
val nun_rec = "rec";
val nun_rparen = ")";
val nun_semicolon = ";";
val nun_spec = "spec";
val nun_subset = "subset";
val nun_then = "then";
val nun_true = "true";
val nun_type = "type";
val nun_unique = "unique";
val nun_unique_unsafe = "unique_unsafe";
val nun_unparsable = "?__unparsable";
val nun_val = "val";
val nun_wf = "wf";
val nun_with = "with";
val nun__witness_of = "_witness_of";

val nun_parens = enclose nun_lparen nun_rparen;

fun nun_parens_if_space s = s |> String.isSubstring " " s ? nun_parens;

fun str_of_nun_arg_list str_of_arg =
  map (prefix " " o nun_parens_if_space o str_of_arg) #> space_implode "";

fun str_of_nun_and_list str_of_elem =
  map str_of_elem #> space_implode ("\n" ^ nun_and ^ " ");

val is_nun_const_quantifier = member (op =) [nun_forall, nun_exists];
val is_nun_const_connective = member (op =) [nun_conj, nun_disj, nun_implies];

val nun_builtin_arity =
  [(nun_asserting, 2),
   (nun_conj, 2),
   (nun_disj, 2),
   (nun_equals, 2),
   (nun_exists, 1),
   (nun_false, 0),
   (nun_forall, 1),
   (nun_if, 3),
   (nun_implies, 2),
   (nun_not, 1),
   (nun_true, 0)];

val arity_of_nun_builtin = AList.lookup (op =) nun_builtin_arity #> the_default 0;

val nun_const_prefix = "c.";
val nun_free_prefix = "f.";
val nun_var_prefix = "v.";
val nun_tconst_prefix = "C.";
val nun_tfree_prefix = "F.";
val nun_custom_id_suffix = "_";

val ident_of_str = I : string -> ident;
val str_of_ident = I : ident -> string;

val encode_args = enclose "(" ")" o commas;

fun decode_args s =
  let
    fun delta #"(" = 1
      | delta #")" = ~1
      | delta _ = 0;

    fun dec 0 (#"(" :: #")" :: cs) _ = ([], String.implode cs)
      | dec 0 (#"(" :: cs) [] = dec 1 cs [[]]
      | dec 0 cs _ = ([], String.implode cs)
      | dec _ [] _ = raise Fail ("ill-formed arguments in " ^ quote s)
      | dec 1 (#")" :: cs) args = (rev (map (String.implode o rev) args), String.implode cs)
      | dec 1 (#"," :: cs) args = dec 1 cs ([] :: args)
      | dec n (c :: cs) (arg :: args) = dec (n + delta c) cs ((c :: arg) :: args);
  in
    dec 0 (String.explode s) []
  end;

fun nun_const_of_str args =
  suffix nun_custom_id_suffix #> prefix nun_const_prefix #> prefix (encode_args args);
fun nun_tconst_of_str args =
  suffix nun_custom_id_suffix #> prefix nun_tconst_prefix #> prefix (encode_args args);

val nun_free_of_str = suffix nun_custom_id_suffix #> prefix nun_free_prefix;
val nun_tfree_of_str = suffix nun_custom_id_suffix #> prefix nun_tfree_prefix;
val nun_var_of_str = suffix nun_custom_id_suffix #> prefix nun_var_prefix;
val str_of_nun_const = decode_args ##> unprefix nun_const_prefix ##> unsuffix nun_custom_id_suffix;
val str_of_nun_tconst = decode_args ##> unprefix nun_tconst_prefix ##> unsuffix nun_custom_id_suffix;
val str_of_nun_free = unprefix nun_free_prefix #> unsuffix nun_custom_id_suffix;
val str_of_nun_tfree = unprefix nun_tfree_prefix #> unsuffix nun_custom_id_suffix;
val str_of_nun_var = unprefix nun_var_prefix #> unsuffix nun_custom_id_suffix;

fun index_name s 0 = s
  | index_name s j =
    let
      val n = size s;
      val m = n - 1;
    in
      String.substring (s, 0, m) ^ string_of_int j ^ String.substring (s, m, n - m)
    end;

val dummy_ty = NType (nun_dummy, []);
val prop_ty = NType (nun_prop, []);

fun mk_arrow_ty (dom, ran) = NType (nun_arrow, [dom, ran]);
val mk_arrows_ty = Library.foldr mk_arrow_ty;

val nabss = Library.foldr NAbs;
val napps = Library.foldl NApp;

fun domain_ty (NType (_, [ty, _])) = ty
  | domain_ty ty = ty;

fun range_ty (NType (_, [_, ty])) = ty
  | range_ty ty = ty;

fun domain_tys 0 _ = []
  | domain_tys n ty = domain_ty ty :: domain_tys (n - 1) (range_ty ty);

fun ty_of (NAtom (_, ty)) = ty
  | ty_of (NConst (_, _, ty)) = ty
  | ty_of (NAbs (var, body)) = mk_arrow_ty (ty_of var, ty_of body)
  | ty_of (NMatch (_, (_, _, body1) :: _)) = ty_of body1
  | ty_of (NApp (const, _)) = range_ty (ty_of const);

val safe_ty_of = try ty_of #> the_default dummy_ty;

fun strip_nun_binders binder (app as NApp (NConst (id, _, _), NAbs (var, body))) =
    if id = binder then
      strip_nun_binders binder body
      |>> cons var
    else
      ([], app)
  | strip_nun_binders _ tm = ([], tm);

fun fold_map_option _ NONE = pair NONE
  | fold_map_option f (SOME x) = f x #>> SOME;

fun fold_map_ty_idents f (NType (id, tys)) =
    f id
    ##>> fold_map (fold_map_ty_idents f) tys
    #>> NType;

fun fold_map_match_branch_idents f (id, vars, body) =
    f id
    ##>> fold_map (fold_map_tm_idents f) vars
    ##>> fold_map_tm_idents f body
    #>> Scan.triple1
and fold_map_tm_idents f (NAtom (j, ty)) =
    fold_map_ty_idents f ty
    #>> curry NAtom j
  | fold_map_tm_idents f (NConst (id, tys, ty)) =
    f id
    ##>> fold_map (fold_map_ty_idents f) tys
    ##>> fold_map_ty_idents f ty
    #>> (Scan.triple1 #> NConst)
  | fold_map_tm_idents f (NAbs (var, body)) =
    fold_map_tm_idents f var
    ##>> fold_map_tm_idents f body
    #>> NAbs
  | fold_map_tm_idents f (NMatch (obj, branches)) =
    fold_map_tm_idents f obj
    ##>> fold_map (fold_map_match_branch_idents f) branches
    #>> NMatch
  | fold_map_tm_idents f (NApp (const, arg)) =
    fold_map_tm_idents f const
    ##>> fold_map_tm_idents f arg
    #>> NApp;

fun fold_map_nun_copy_spec_idents f {abs_ty, rep_ty, subset, quotient, abs, rep} =
  fold_map_ty_idents f abs_ty
  ##>> fold_map_ty_idents f rep_ty
  ##>> fold_map_option (fold_map_tm_idents f) subset
  ##>> fold_map_option (fold_map_tm_idents f) quotient
  ##>> fold_map_tm_idents f abs
  ##>> fold_map_tm_idents f rep
  #>> (fn (((((abs_ty, rep_ty), subset), quotient), abs), rep) =>
    {abs_ty = abs_ty, rep_ty = rep_ty, subset = subset, quotient = quotient, abs = abs, rep = rep});

fun fold_map_nun_ctr_spec_idents f {ctr, arg_tys} =
  fold_map_tm_idents f ctr
  ##>> fold_map (fold_map_ty_idents f) arg_tys
  #>> (fn (ctr, arg_tys) => {ctr = ctr, arg_tys = arg_tys});

fun fold_map_nun_co_data_spec_idents f {ty, ctrs} =
  fold_map_ty_idents f ty
  ##>> fold_map (fold_map_nun_ctr_spec_idents f) ctrs
  #>> (fn (ty, ctrs) => {ty = ty, ctrs = ctrs});

fun fold_map_nun_const_spec_idents f {const, props} =
  fold_map_tm_idents f const
  ##>> fold_map (fold_map_tm_idents f) props
  #>> (fn (const, props) => {const = const, props = props});

fun fold_map_nun_consts_spec_idents f {consts, props} =
  fold_map (fold_map_tm_idents f) consts
  ##>> fold_map (fold_map_tm_idents f) props
  #>> (fn (consts, props) => {consts = consts, props = props});

fun fold_map_nun_command_idents f (NTVal (ty, cards)) =
    fold_map_ty_idents f ty
    #>> (rpair cards #> NTVal)
  | fold_map_nun_command_idents f (NCopy spec) =
    fold_map_nun_copy_spec_idents f spec
    #>> NCopy
  | fold_map_nun_command_idents f (NData specs) =
    fold_map (fold_map_nun_co_data_spec_idents f) specs
    #>> NData
  | fold_map_nun_command_idents f (NCodata specs) =
    fold_map (fold_map_nun_co_data_spec_idents f) specs
    #>> NCodata
  | fold_map_nun_command_idents f (NVal (tm, ty)) =
    fold_map_tm_idents f tm
    ##>> fold_map_ty_idents f ty
    #>> NVal
  | fold_map_nun_command_idents f (NPred (wf, specs)) =
    fold_map (fold_map_nun_const_spec_idents f) specs
    #>> curry NPred wf
  | fold_map_nun_command_idents f (NCopred specs) =
    fold_map (fold_map_nun_const_spec_idents f) specs
    #>> NCopred
  | fold_map_nun_command_idents f (NRec specs) =
    fold_map (fold_map_nun_const_spec_idents f) specs
    #>> NRec
  | fold_map_nun_command_idents f (NSpec spec) =
    fold_map_nun_consts_spec_idents f spec
    #>> NSpec
  | fold_map_nun_command_idents f (NAxiom tm) =
    fold_map_tm_idents f tm
    #>> NAxiom
  | fold_map_nun_command_idents f (NGoal tm) =
    fold_map_tm_idents f tm
    #>> NGoal
  | fold_map_nun_command_idents f (NEval tm) =
    fold_map_tm_idents f tm
    #>> NEval;

fun fold_map_nun_problem_idents f ({commandss, sound, complete} : nun_problem) =
  fold_map (fold_map (fold_map_nun_command_idents f)) commandss
  #>> (fn commandss' => {commandss = commandss', sound = sound, complete = complete});

fun dest_rassoc_args oper arg0 rest =
  (case rest of
    NApp (NApp (oper', arg1), rest') =>
    if oper' = oper then arg0 :: dest_rassoc_args oper arg1 rest' else [arg0, rest]
  | _ => [arg0, rest]);

val rcomb_tms = fold (fn arg => fn func => NApp (func, arg));
val abs_tms = fold_rev (curry NAbs);

fun fresh_var_names_wrt_tm n tm =
  let
    fun max_var_br (_, vars, body) = fold max_var (body :: vars)
    and max_var (NAtom _) = I
      | max_var (NConst (id, _, _)) =
        (fn max => if String.isPrefix nun_var_prefix id andalso size id > size max then id else max)
      | max_var (NApp (func, arg)) = fold max_var [func, arg]
      | max_var (NAbs (var, body)) = fold max_var [var, body]
      | max_var (NMatch (obj, branches)) = max_var obj #> fold max_var_br branches;

    val dummy_name = nun_var_of_str Name.uu;
    val max_name = max_var tm dummy_name;
  in
    map (index_name max_name) (1 upto n)
  end;

fun eta_expandN_tm 0 tm = tm
  | eta_expandN_tm n tm =
    let
      val var_names = fresh_var_names_wrt_tm n tm;
      val arg_tys = domain_tys n (ty_of tm);
      val vars = map2 (fn id => fn ty => NConst (id, [], ty)) var_names arg_tys;
    in
      abs_tms vars (rcomb_tms vars tm)
    end;

val eta_expand_builtin_tm =
  let
    fun expand_quant_arg (NAbs (var, body)) = NAbs (var, expand_quant_arg body)
      | expand_quant_arg (NMatch (obj, branches)) =
        NMatch (obj, map (@{apply 3(3)} expand_quant_arg) branches)
      | expand_quant_arg (tm as NApp (_, NAbs _)) = tm
      | expand_quant_arg (NApp (quant, arg)) = NApp (quant, eta_expandN_tm 1 arg)
      | expand_quant_arg tm = tm;

    fun expand args (NApp (func, arg)) = expand (expand [] arg :: args) func
      | expand args (func as NConst (id, _, _)) =
        let val missing = Int.max (0, arity_of_nun_builtin id - length args) in
          rcomb_tms args func
          |> eta_expandN_tm missing
          |> is_nun_const_quantifier id ? expand_quant_arg
        end
      | expand args (func as NAtom _) = rcomb_tms args func
      | expand args (NAbs (var, body)) = rcomb_tms args (NAbs (var, expand [] body))
      | expand args (NMatch (obj, branches)) =
        rcomb_tms args (NMatch (obj, map (@{apply 3(3)} (expand [])) branches));
  in
    expand []
  end;

val str_of_ty =
  let
    fun str_of maybe_parens (NType (id, tys)) =
      if id = nun_arrow then
        (case tys of
          [ty, ty'] => maybe_parens (str_of nun_parens ty ^ " " ^ nun_arrow ^ " " ^ str_of I ty'))
      else
        id ^ str_of_nun_arg_list (str_of I) tys
  in
    str_of I
  end;

val (str_of_tmty, str_of_tm) =
  let
    fun is_triv_head (NConst (id, _, _)) = (arity_of_nun_builtin id = 0)
      | is_triv_head (NAtom _) = true
      | is_triv_head (NApp (const, _)) = is_triv_head const
      | is_triv_head (NAbs _) = false
      | is_triv_head (NMatch _) = false;

    fun str_of_at_const id tys =
      nun_at ^ str_of_ident id ^ str_of_nun_arg_list str_of_ty tys;

    fun str_of_app ty_opt const arg =
      let
        val ty_opt' =
          try (Option.map (fn ty => mk_arrow_ty (ty_of arg, ty))) ty_opt
          |> the_default NONE;
      in
        (str_of ty_opt' const |> (case const of NAbs _ => nun_parens | _ => I)) ^
        str_of_nun_arg_list (str_of NONE) [arg]
      end
    and str_of_br ty_opt (id, vars, body) =
      " " ^ nun_bar ^ " " ^ id ^ space_implode "" (map (prefix " " o str_of NONE) vars) ^ " " ^
      nun_arrow ^ " " ^ str_of ty_opt body
    and str_of_tmty tm =
      let val ty = ty_of tm in
        str_of (SOME ty) tm ^ " " ^ nun_colon ^ " " ^ str_of_ty ty
      end
    and str_of _ (NAtom (j, _)) = nun_dollar ^ string_of_int j
      | str_of _ (NConst (id, [], _)) = str_of_ident id
      | str_of (SOME ty0) (NConst (id, tys, ty)) =
        if ty = ty0 then str_of_ident id else str_of_at_const id tys
      | str_of _ (NConst (id, tys, _)) = str_of_at_const id tys
      | str_of ty_opt (NAbs (var, body)) =
        nun_lambda ^ " " ^
        (case ty_opt of
          SOME ty => str_of (SOME (domain_ty ty))
        | NONE => nun_parens o str_of_tmty) var ^
        nun_dot ^ " " ^ str_of (Option.map range_ty ty_opt) body
      | str_of ty_opt (NMatch (obj, branches)) =
        nun_match ^ " " ^ str_of NONE obj ^ " " ^ nun_with ^
        space_implode "" (map (str_of_br ty_opt) branches) ^ " " ^ nun_end
      | str_of ty_opt (app as NApp (func, argN)) =
        (case (func, argN) of
          (NApp (oper as NConst (id, _, _), arg1), arg2) =>
          if id = nun_asserting then
            str_of ty_opt arg1 ^ " " ^ nun_asserting ^ " " ^ str_of (SOME prop_ty) arg2
            |> nun_parens
          else if id = nun_equals then
            (str_of NONE arg1 |> not (is_triv_head arg1) ? nun_parens) ^ " " ^ id ^ " " ^
            (str_of (try ty_of arg2) arg2 |> not (is_triv_head arg2) ? nun_parens)
          else if is_nun_const_connective id then
            let val args = dest_rassoc_args oper arg1 arg2 in
              space_implode (" " ^ id ^ " ")
                (map (fn arg => str_of NONE arg |> not (is_triv_head arg) ? nun_parens) args)
            end
          else
            str_of_app ty_opt func argN
        | (NApp (NApp (NConst (id, _, _), arg1), arg2), arg3) =>
          if id = nun_if then
            nun_if ^ " " ^ str_of NONE arg1 ^ " " ^ nun_then ^ " " ^ str_of NONE arg2 ^ " " ^
            nun_else ^ " " ^ str_of NONE arg3
            |> nun_parens
          else
            str_of_app ty_opt func argN
        | (NConst (id, _, _), NAbs _) =>
          if is_nun_const_quantifier id then
            let val (vars, body) = strip_nun_binders id app in
              id ^ " " ^ implode_space (map (nun_parens o str_of_tmty) vars) ^ nun_dot ^ " " ^
              str_of NONE body
            end
          else
            str_of_app ty_opt func argN
        | _ => str_of_app ty_opt func argN);
  in
    (str_of_tmty, str_of NONE)
  end;

val empty_name_pool = {nice_of_ugly = Symtab.empty, ugly_of_nice = Symtab.empty};

val nice_of_ugly_suggestion =
  unascii_of #> Long_Name.base_name #> ascii_of #> unsuffix nun_custom_id_suffix
  #> (fn s => if s = "" orelse not (Char.isAlpha (String.sub (s, 0))) then "x" ^ s else s);

fun allocate_nice ({nice_of_ugly, ugly_of_nice} : name_pool) (ugly, nice_sugg0) =
  let
    fun alloc j =
      let val nice_sugg = index_name nice_sugg0 j in
        (case Symtab.lookup ugly_of_nice nice_sugg of
          NONE =>
          (nice_sugg,
           {nice_of_ugly = Symtab.update_new (ugly, nice_sugg) nice_of_ugly,
            ugly_of_nice = Symtab.update_new (nice_sugg, ugly) ugly_of_nice})
        | SOME _ => alloc (j + 1))
      end;
  in
    alloc 0
  end;

fun nice_ident ugly (pool as {nice_of_ugly, ...}) =
  if String.isSuffix nun_custom_id_suffix ugly then
    (case Symtab.lookup nice_of_ugly ugly of
      NONE => allocate_nice pool (ugly, nice_of_ugly_suggestion ugly)
    | SOME nice => (nice, pool))
  else
    (ugly, pool);

fun nice_nun_problem problem =
  fold_map_nun_problem_idents nice_ident problem empty_name_pool;

fun str_of_tval (NType (id, tys)) =
  str_of_ident id ^ " " ^ nun_colon ^ " " ^
  fold (K (prefix (nun_type ^ " " ^ nun_arrow ^ " "))) tys nun_type;

fun is_triv_subset (NAbs (_, body)) = is_triv_subset body
  | is_triv_subset (NConst (id, _, _)) = (id = nun_true)
  | is_triv_subset _ = false;

fun str_of_nun_copy_spec {abs_ty, rep_ty, subset, quotient, abs, rep} =
  str_of_ty abs_ty ^ " " ^ nun_assign ^ " " ^ str_of_ty rep_ty ^
  (case subset of
    NONE => ""
  | SOME s =>
    if is_triv_subset s then ""
    else "\n  " ^ nun_subset ^ " " ^ nun_parens_if_space (str_of_tm s)) ^
  (* TODO: use nun_quotient when possible *)
  (case quotient of
    NONE => ""
  | SOME q => "\n  " ^ nun_partial_quotient ^ " " ^ str_of_tm q) ^
  "\n  " ^ nun_abstract ^ " " ^ str_of_tm abs ^ "\n  " ^ nun_concrete ^ " " ^ str_of_tm rep;

fun str_of_nun_ctr_spec {ctr, arg_tys} =
  str_of_tm ctr ^ str_of_nun_arg_list str_of_ty arg_tys;

fun str_of_nun_co_data_spec {ty, ctrs} =
  str_of_ty ty ^ " " ^ nun_assign ^ "\n  " ^
  space_implode ("\n" ^ nun_bar ^ " ") (map str_of_nun_ctr_spec ctrs);

fun str_of_nun_const_spec {const, props} =
  str_of_tmty const ^ " " ^ nun_assign ^ "\n  " ^
  space_implode (nun_semicolon ^ "\n  ") (map str_of_tm props);

fun str_of_nun_consts_spec {consts, props} =
  space_implode (" " ^ nun_and ^ "\n     ") (map str_of_tmty consts) ^ " " ^ nun_assign ^ "\n  " ^
  space_implode (nun_semicolon ^ "\n  ") (map str_of_tm props);

fun str_of_nun_cards_suffix (NONE, NONE) = ""
  | str_of_nun_cards_suffix (c1, c2) =
    let
      val s1 = Option.map (prefix "min_card " o signed_string_of_int) c1;
      val s2 = Option.map (prefix "max_card " o signed_string_of_int) c2;
    in
      enclose " [" "]" (space_implode "; " (map_filter I [s1, s2]))
    end;

fun str_of_nun_command (NTVal (ty, cards)) =
    nun_val ^ " " ^ str_of_tval ty ^ str_of_nun_cards_suffix cards
  | str_of_nun_command (NCopy spec) = nun_copy ^ " " ^ str_of_nun_copy_spec spec
  | str_of_nun_command (NData specs) =
    nun_data ^ " " ^ str_of_nun_and_list str_of_nun_co_data_spec specs
  | str_of_nun_command (NCodata specs) =
    nun_codata ^ " " ^ str_of_nun_and_list str_of_nun_co_data_spec specs
  | str_of_nun_command (NVal (tm, ty)) =
    nun_val ^ " " ^ str_of_tm tm ^ " " ^ nun_colon ^ " " ^ str_of_ty ty
  | str_of_nun_command (NPred (wf, specs)) =
    nun_pred ^ " " ^ (if wf then nun_lbracket ^ nun_wf ^ nun_rbracket ^ " " else "") ^
    str_of_nun_and_list str_of_nun_const_spec specs
  | str_of_nun_command (NCopred specs) =
    nun_copred ^ " " ^ str_of_nun_and_list str_of_nun_const_spec specs
  | str_of_nun_command (NRec specs) =
    nun_rec ^ " " ^ str_of_nun_and_list str_of_nun_const_spec specs
  | str_of_nun_command (NSpec spec) = nun_spec ^ " " ^ str_of_nun_consts_spec spec
  | str_of_nun_command (NAxiom tm) = nun_axiom ^ " " ^ str_of_tm tm
  | str_of_nun_command (NGoal tm) = nun_goal ^ " " ^ str_of_tm tm
  | str_of_nun_command (NEval tm) = nun_hash ^ " " ^ nun_eval ^ " " ^ str_of_tm tm;

fun str_of_nun_problem {commandss, sound, complete} =
  map (cat_lines o map (suffix nun_dot o str_of_nun_command)) commandss
  |> space_implode "\n\n" |> suffix "\n"
  |> prefix (nun_hash ^ " " ^ (if sound then "sound" else "unsound") ^ "\n")
  |> prefix (nun_hash ^ " " ^ (if complete then "complete" else "incomplete") ^ "\n");

end;
