(*  Title:      HOL/Nunchaku/Tools/nunchaku_model.ML
    Author:     Jasmin Blanchette, VU Amsterdam
    Copyright   2015, 2016, 2017

Abstract syntax tree for Nunchaku models.
*)

signature NUNCHAKU_MODEL =
sig
  type ident = Nunchaku_Problem.ident
  type ty = Nunchaku_Problem.ty
  type tm = Nunchaku_Problem.tm
  type name_pool = Nunchaku_Problem.name_pool

  type ty_entry = ty * tm list
  type tm_entry = tm * tm

  type nun_model =
    {type_model: ty_entry list,
     const_model: tm_entry list,
     skolem_model: tm_entry list,
     auxiliary_model: tm_entry list}

  val str_of_nun_model: nun_model -> string

  val allocate_ugly: name_pool -> string * string -> string * name_pool

  val ugly_nun_model: name_pool -> nun_model -> nun_model

  datatype token =
    Ident of ident
  | Symbol of ident
  | Atom of ident * int
  | End_of_Stream

  val parse_tok: ''a -> ''a list -> ''a * ''a list
  val parse_ident: token list -> ident * token list
  val parse_id: ident -> token list -> token * token list
  val parse_sym: ident -> token list -> token * token list
  val parse_atom: token list -> (ident * int) * token list
  val nun_model_of_str: string -> nun_model
end;

structure Nunchaku_Model : NUNCHAKU_MODEL =
struct

open Nunchaku_Problem;

type ty_entry = ty * tm list;
type tm_entry = tm * tm;

type nun_model =
  {type_model: ty_entry list,
   const_model: tm_entry list,
   skolem_model: tm_entry list,
   auxiliary_model: tm_entry list};

fun base_of_id id = hd (space_explode "/" id);

val nun_SAT = str_of_ident "SAT";

fun str_of_ty_entry (ty, tms) =
  "type " ^ str_of_ty ty ^ " := {" ^ commas (map str_of_tm tms) ^ "}.";

fun str_of_tm_entry (tm, value) =
  "val " ^ str_of_tm tm ^ " := " ^ str_of_tm value ^ ".";

fun str_of_nun_model {type_model, const_model, skolem_model, auxiliary_model} =
  map str_of_ty_entry type_model @ "" :: map str_of_tm_entry const_model @ "" ::
  map str_of_tm_entry skolem_model @ "" :: map str_of_tm_entry auxiliary_model
  |> cat_lines;

fun fold_map_ty_entry_idents f (ty, atoms) =
  fold_map_ty_idents f ty
  ##>> fold_map (fold_map_tm_idents f) atoms;

fun fold_map_tm_entry_idents f (tm, value) =
  fold_map_tm_idents f tm
  ##>> fold_map_tm_idents f value;

fun fold_map_nun_model_idents f {type_model, const_model, skolem_model, auxiliary_model} =
  fold_map (fold_map_ty_entry_idents f) type_model
  ##>> fold_map (fold_map_tm_entry_idents f) const_model
  ##>> fold_map (fold_map_tm_entry_idents f) skolem_model
  ##>> fold_map (fold_map_tm_entry_idents f) auxiliary_model
  #>> (fn (((type_model, const_model), skolem_model), auxiliary_model) =>
    {type_model = type_model, const_model = const_model, skolem_model = skolem_model,
     auxiliary_model = auxiliary_model});

fun swap_name_pool ({nice_of_ugly, ugly_of_nice} : name_pool) =
  {nice_of_ugly = ugly_of_nice, ugly_of_nice = nice_of_ugly};

fun allocate_ugly pool (nice, ugly_sugg) =
  allocate_nice (swap_name_pool pool) (nice, ugly_sugg) ||> swap_name_pool;

fun ugly_ident nice (pool as {ugly_of_nice, ...}) =
  (case Symtab.lookup ugly_of_nice nice of
    NONE => allocate_ugly pool (nice, nice)
  | SOME ugly => (ugly, pool));

fun ugly_nun_model pool model =
  fst (fold_map_nun_model_idents ugly_ident model pool);

datatype token =
  Ident of ident
| Symbol of ident
| Atom of ident * int
| End_of_Stream;

val rev_str = String.implode o rev o String.explode;

fun atom_of_str s =
  (case first_field "_" (rev_str s) of
    SOME (rev_suf, rev_pre) =>
    let
      val pre = rev_str rev_pre;
      val suf = rev_str rev_suf;
    in
      (case Int.fromString suf of
        SOME j => Atom (ident_of_str pre, j)
      | NONE => raise Fail ("ill-formed atom: " ^ s))
    end
  | NONE => raise Fail ("ill-formed atom: " ^ s));

fun is_alnum_etc_char c = Char.isAlphaNum c orelse c = #"_" orelse c = #"/";

fun is_dollar_alnum_etc_char c = c = #"$" orelse is_alnum_etc_char c;

val multi_ids =
  [nun_arrow, nun_assign, nun_conj, nun_disj, nun_implies, nun_unparsable, nun_irrelevant];

val nun_dollar_anon_fun_prefix_exploded = String.explode nun_dollar_anon_fun_prefix;
val [nun_dollar_char] = String.explode nun_dollar;

fun next_token [] = (End_of_Stream, [])
  | next_token (c :: cs) =
    if Char.isSpace c then
      next_token cs
    else if c = nun_dollar_char then
      let val n = find_index (not o is_dollar_alnum_etc_char) cs in
        (if n = ~1 then (cs, []) else chop n cs)
        |>> (String.implode
          #> (if is_prefix (op =) nun_dollar_anon_fun_prefix_exploded cs then ident_of_str #> Ident
            else atom_of_str))
      end
    else if is_alnum_etc_char c then
      let val n = find_index (not o is_alnum_etc_char) cs in
        (if n = ~1 then (cs, []) else chop n cs)
        |>> (cons c #> String.implode #> ident_of_str #> Ident)
      end
    else
      let
        fun next_multi id =
          let
            val s = str_of_ident id;
            val n = String.size s - 1;
          in
            if c = String.sub (s, 0) andalso
               is_prefix (op =) (String.explode (String.substring (s, 1, n))) cs then
              SOME (Symbol id, drop n cs)
            else
              NONE
          end;
      in
        (case get_first next_multi multi_ids of
          SOME res => res
        | NONE => (Symbol (ident_of_str (String.str c)), cs))
      end;

val tokenize =
  let
    fun toks cs =
      (case next_token cs of
        (End_of_Stream, []) => []
      | (tok, cs') => tok :: toks cs');
  in
    toks o String.explode
  end;

fun parse_enum sep scan =
  Scan.optional (scan ::: Scan.repeat (sep |-- scan)) [];

fun parse_tok tok =
  Scan.one (curry (op =) tok);

val parse_ident = Scan.some (try (fn Ident id => id));
val parse_id = parse_tok o Ident;
val parse_sym = parse_tok o Symbol;
val parse_atom = Scan.some (try (fn Atom id_j => id_j));

val confusing_ids = [nun_else, nun_then, nun_with];

val parse_confusing_id = Scan.one (fn Ident id => member (op =) confusing_ids id | _ => false);

fun parse_ty toks =
  (parse_ty_arg -- Scan.option (parse_sym nun_arrow -- parse_ty)
   >> (fn (ty, NONE) => ty
     | (lhs, SOME (Symbol id, rhs)) => NType (id, [lhs, rhs]))) toks
and parse_ty_arg toks =
  (parse_ident >> (rpair [] #> NType)
   || parse_sym nun_lparen |-- parse_ty --| parse_sym nun_rparen) toks;

val parse_choice_or_unique =
  (parse_tok (Ident nun_choice) || parse_tok (Ident nun_unique)
   || parse_tok (Ident nun_unique_unsafe))
  -- parse_ty_arg
  >> (fn (Ident id, ty) => NConst (id, [ty], mk_arrows_ty ([ty, prop_ty], ty)));

fun parse_tm toks =
  (parse_id nun_lambda |-- Scan.repeat parse_arg --| parse_sym nun_dot -- parse_tm >> nabss
  || parse_id nun_mu |-- parse_arg --| parse_sym nun_dot -- parse_tm
     >> (fn (var, body) =>
       let val ty = safe_ty_of body in
         NApp (NConst (nun_mu, [ty], mk_arrow_ty (mk_arrow_ty (ty, ty), ty)), NAbs (var, body))
       end)
   || parse_id nun_if |-- parse_tm --| parse_id nun_then -- parse_tm --| parse_id nun_else
       -- parse_tm
     >> (fn ((cond, th), el) =>
       let val ty = safe_ty_of th in
         napps (NConst (nun_if, [ty], mk_arrows_ty ([prop_ty, ty, ty], ty)), [cond, th, el])
       end)
   || parse_implies) toks
and parse_implies toks =
  (parse_disj -- Scan.option (parse_sym nun_implies -- parse_implies)
   >> (fn (tm, NONE) => tm
     | (lhs, SOME (Symbol id, rhs)) => napps (NConst (id, [], dummy_ty), [lhs, rhs]))) toks
and parse_disj toks =
  (parse_conj -- Scan.option (parse_sym nun_disj -- parse_disj)
   >> (fn (tm, NONE) => tm
     | (lhs, SOME (Symbol id, rhs)) => napps (NConst (id, [], dummy_ty), [lhs, rhs]))) toks
and parse_conj toks =
  (parse_not -- Scan.option (parse_sym nun_conj -- parse_conj)
   >> (fn (tm, NONE) => tm
     | (lhs, SOME (Symbol id, rhs)) => napps (NConst (id, [], dummy_ty), [lhs, rhs]))) toks
and parse_not toks =
  (Scan.option (parse_sym nun_not) -- parse_equals
   >> (fn (NONE, tm) => tm
     | (SOME _, tm) => napps (NConst (nun_not, [], dummy_ty), [tm]))) toks
and parse_equals toks =
  (parse_comb -- Scan.option (parse_sym nun_equals -- parse_comb)
   >> (fn (tm, NONE) => tm
     | (lhs, SOME (Symbol id, rhs)) => napps (NConst (id, [], dummy_ty), [lhs, rhs]))) toks
and parse_comb toks =
  (parse_arg -- Scan.repeat (Scan.unless parse_confusing_id parse_arg) >> napps) toks
and parse_arg toks =
  (parse_choice_or_unique
   || parse_ident >> (fn id => NConst (id, [], dummy_ty))
   || parse_sym nun_irrelevant |-- parse_ident
     >> (fn num => NConst (nun_irrelevant ^ num, [], dummy_ty))
   || parse_sym nun_unparsable |-- parse_ty >> (fn ty => NConst (nun_unparsable, [], ty))
   || parse_sym nun_lparen |-- parse_tm -- Scan.option (parse_sym nun_colon |-- parse_ty)
      --| parse_sym nun_rparen
     >> (fn (NConst (id, [], _), SOME ty) => NConst (id, [], ty)
       | (tm, _) => tm)
   || parse_atom >> (fn (id, j) => NAtom (j, NType (id, [])))) toks;

val parse_witness_name =
  parse_ident >> (fn id => NConst (base_of_id id, [], dummy_ty));

val parse_witness =
  parse_id nun__witness_of |-- parse_sym nun_lparen |-- (parse_id nun_forall || parse_id nun_exists)
  |-- Scan.option (parse_sym nun_lparen) |-- parse_witness_name
  --| Scan.repeat (Scan.one (curry (op <>) (Symbol nun_assign)));

val parse_anon_fun_name =
  Scan.one (fn Ident id => String.isPrefix nun_dollar_anon_fun_prefix id | _ => false);

val parse_anon_fun =
  parse_anon_fun_name >> (fn Ident id => NConst (id, [], dummy_ty));

datatype entry =
  Type_Entry of ty_entry
| Const_Entry of tm_entry
| Skolem_Entry of tm_entry
| Auxiliary_Entry of tm_entry;

val parse_entry =
  (parse_id nun_type |-- parse_ty --| parse_sym nun_assign --| parse_sym nun_lbrace --
       parse_enum (parse_sym nun_comma) parse_tm --| parse_sym nun_rbrace
     >> Type_Entry
   || parse_id nun_val |-- parse_anon_fun --| parse_sym nun_assign -- parse_tm >> Auxiliary_Entry
   || parse_id nun_val |-- parse_witness --| parse_sym nun_assign -- parse_tm >> Skolem_Entry
   || parse_id nun_val |-- parse_tm --| parse_sym nun_assign -- parse_tm >> Const_Entry)
  --| parse_sym nun_dot;

val parse_model =
  parse_id nun_SAT |-- parse_sym nun_colon |-- parse_sym nun_lbrace |-- Scan.repeat parse_entry
  --| parse_sym nun_rbrace;

fun add_entry entry ({type_model, const_model, skolem_model, auxiliary_model} : nun_model) =
  (case entry of
    Type_Entry e =>
    {type_model = e :: type_model, const_model = const_model, skolem_model = skolem_model,
     auxiliary_model = auxiliary_model}
  | Const_Entry e =>
    {type_model = type_model, const_model = e :: const_model, skolem_model = skolem_model,
     auxiliary_model = auxiliary_model}
  | Skolem_Entry e =>
    {type_model = type_model, const_model = const_model, skolem_model = e :: skolem_model,
     auxiliary_model = auxiliary_model}
  | Auxiliary_Entry e =>
    {type_model = type_model, const_model = const_model, skolem_model = skolem_model,
     auxiliary_model = e :: auxiliary_model});

fun nun_model_of_str str =
  let val (entries, _) = parse_model (tokenize str) in
    {type_model = [], const_model = [], skolem_model = [], auxiliary_model = []}
    |> fold_rev add_entry entries
  end;

end;
