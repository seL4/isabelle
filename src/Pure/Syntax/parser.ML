(*  Title:      Pure/Syntax/parser.ML
    ID:         $Id$
    Author:     Sonia Mahjoub and Markus Wenzel, TU Muenchen

Isabelle's main parser (used for terms and typs).

TODO:
  fix ambiguous grammar problem
  ~1 --> chain_pri
  improve syntax error
  extend_gram: remove 'roots' arg
*)

signature PARSER =
sig
  structure Lexicon: LEXICON
  structure SynExt: SYN_EXT
  local open Lexicon SynExt SynExt.Ast in
    type gram
    val empty_gram: gram
    val extend_gram: gram -> string list -> xprod list -> gram
    val merge_grams: gram -> gram -> gram
    val pretty_gram: gram -> Pretty.T list
    datatype parsetree =
      Node of string * parsetree list |
      Tip of token
    val parse: gram -> string -> token list -> parsetree
  end
end;

functor ParserFun(structure Symtab: SYMTAB and Lexicon: LEXICON
  and SynExt: SYN_EXT)(*: PARSER *) =  (* FIXME *)
struct

structure Pretty = SynExt.Ast.Pretty;
structure Lexicon = Lexicon;
structure SynExt = SynExt;
open Lexicon SynExt;


(** datatype gram **)

datatype symb =
  Terminal of token |
  Nonterminal of string * int;

datatype gram =
  Gram of (string * (symb list * string * int)) list
    * (symb list * string * int) list Symtab.table;

fun mk_gram prods = Gram (prods, Symtab.make_multi prods);


(* empty, extend, merge grams *)

val empty_gram = mk_gram [];

fun extend_gram (gram1 as Gram (prods1, _)) _ xprods2 =
  let
    fun symb_of (Delim s) = Some (Terminal (Token s))
      | symb_of (Argument (s, p)) =
          (case predef_term s of
            None => Some (Nonterminal (s, p))
          | Some tk => Some (Terminal tk))
      | symb_of _ = None;

    fun prod_of (XProd (lhs, xsymbs, const, pri)) =
      (lhs, (mapfilter symb_of xsymbs, const, pri));

    val prods2 = distinct (map prod_of xprods2);
  in
    if prods2 subset prods1 then gram1
    else mk_gram (extend_list prods1 prods2)
  end;

fun merge_grams (gram1 as Gram (prods1, _)) (gram2 as Gram (prods2, _)) =
  if prods2 subset prods1 then gram1
  else if prods1 subset prods2 then gram2
  else mk_gram (merge_lists prods1 prods2);


(* pretty_gram *)

fun pretty_gram (Gram (prods, _)) =
  let
    fun pretty_name name = [Pretty.str (name ^ " =")];

    fun pretty_symb (Terminal (Token s)) = Pretty.str (quote s)
      | pretty_symb (Terminal tok) = Pretty.str (str_of_token tok)
      | pretty_symb (Nonterminal (s, p)) =
          Pretty.str (s ^ "[" ^ string_of_int p ^ "]");

    fun pretty_const "" = []
      | pretty_const c = [Pretty.str ("=> " ^ quote c)];

    fun pretty_pri p = [Pretty.str ("(" ^ string_of_int p ^ ")")];

    fun pretty_prod (name, (symbs, const, pri)) =
      Pretty.block (Pretty.breaks (pretty_name name @
        map pretty_symb symbs @ pretty_const const @ pretty_pri pri));
  in
    map pretty_prod prods
  end;



(** parse **)

datatype parsetree =
  Node of string * parsetree list |
  Tip of token;

type state =
  string * int
    * parsetree list    (*before point*)
    * symb list         (*after point*)
    * string * int;

type earleystate = state list Array.array;



fun get_prods tab lhs pred =
  filter pred (Symtab.lookup_multi (tab, lhs));

fun getProductions tab A i =
  get_prods tab A (fn (_, _, j) => j >= i orelse j = ~1);

fun getProductions' tab A i k =
  get_prods tab A (fn (_, _, j) => (j >= i andalso j < k) orelse j = ~1);



fun mkState i jj A ([Nonterminal (B, ~1)], id, ~1) =
      (A, max_pri, [], [Nonterminal (B, jj)], id, i)
  | mkState i jj A (ss, id, j) = (A, j, [], ss, id, i);



fun conc (t, k:int) [] = (None, [(t, k)])
  | conc (t, k) ((t', k') :: ts) =
      if t = t' then
        (Some k', if k' >= k then (t', k') :: ts else (t, k) :: ts)
      else
        let val (n, ts') = conc (t, k) ts
        in (n, (t', k') :: ts') end;


fun update_tree ((B, (i, ts)) :: used) (A, t) =
  if A = B then
    let val (n, ts') = conc t ts
    in ((A, (i, ts')) :: used, n) end
  else
    let val (used', n) = update_tree used (A, t)
    in ((B, (i, ts)) :: used', n) end;


fun update_index ((B, (i, ts)) :: used) (A, j) =
  if A = B then (A, (j, ts)) :: used
  else (B, (i, ts)) :: (update_index used (A, j));



fun getS A i Si =
  filter
    (fn (_, _, _, Nonterminal (B, j) :: _, _, _) => A = B andalso j <= i
      | _ => false) Si;

fun getS' A k n Si =
  filter
    (fn (_, _, _, Nonterminal (B, j) :: _, _, _) => A = B andalso j <= k andalso j > n
      | _ => false) Si;

fun getStates Estate i ii A k =
  filter
    (fn (_, _, _, Nonterminal (B, j) :: _, _, _) => A = B andalso j <= k
      | _ => false)
    (Array.sub (Estate, ii));


(* MMW *)(* FIXME *)
fun movedot_term (A, j, ts, Terminal a :: sa, id, i) c =
  if valued_token c then
    (A, j, (ts @ [Tip c]), sa, id, i)
  else (A, j, ts, sa, id, i);

fun movedot_nonterm ts (A, j, tss, Nonterminal (B, k) :: sa, id, i) =
  (A, j, tss @ ts, sa, id, i);

fun movedot_lambda _ [] = []
  | movedot_lambda (B, j, tss, Nonterminal (A, k) :: sa, id, i) ((t, ki) :: ts) =
      if k <= ki then
        (B, j, tss @ t, sa, id, i) ::
          movedot_lambda (B, j, tss, Nonterminal (A, k) :: sa, id, i) ts
      else movedot_lambda (B, j, tss, Nonterminal (A, k) :: sa, id, i) ts;



fun PROCESSS Estate grammar i c states =
let
fun processS used [] (Si, Sii) = (Si, Sii)
  | processS used (S :: States) (Si, Sii) =
      (case S of
        (_, _, _, Nonterminal (A, j) :: _, _, _) =>
          let
            val (used_neu, States_neu) =
              (case assoc (used, A) of
                Some (k, l) =>      (*A gehoert zu used*)
                  if k <= j         (*Prioritaet wurde behandelt*)
                  then (used, movedot_lambda S l)
                  else              (*Prioritaet wurde noch nicht behandelt*)
                    let
                      val L = getProductions' grammar A j k;
                      val States' = map (mkState i j A) L;
                    in
                      (update_index used (A, j), States' @ movedot_lambda S l)
                    end

              | None =>             (*A gehoert nicht zu used*)
                  let
                    val L = getProductions grammar A j;
                    val States' = map (mkState i j A) L;
                  in
                    ((A, (j, [])) :: used, States')
                  end)
          in
            processS used_neu (States @ States_neu) (S :: Si, Sii)
          end
      | (_, _, _, Terminal a :: _, _, _) =>
          processS used States
            (S :: Si,
              if matching_tokens (a, c) then movedot_term S c :: Sii else Sii)
                                          (* MMW *)(* FIXME *)

      | (A, k, ts, [], id, j) =>
          let
            val tt = if id = "" then ts else [Node (id, ts)]
          in
            if j = i then
              let
                val (used', O) = update_tree used (A, (tt, k));
              in
                (case O of
                  None =>
                    let
                      val Slist = getS A k Si;
                      val States' = map (movedot_nonterm tt) Slist;
                    in
                      processS used' (States @ States') (S :: Si, Sii)
                    end
                | Some n =>
                    if n >= k then
                      processS used' States (S :: Si, Sii)
                    else
                      let
                        val Slist = getS' A k n Si;
                        val States' = map (movedot_nonterm tt) Slist;
                      in
                        processS used' (States @ States') (S :: Si, Sii)
                      end)
              end
            else
              processS used
                (States @ map (movedot_nonterm tt) (getStates Estate i j A k))
                (S :: Si, Sii)
          end)
in
  processS [] states ([], [])
end;



fun syntax_error toks =
  error ("Syntax error at: " ^ space_implode " " (map str_of_token toks));

fun produce grammar stateset i indata =
  (case Array.sub (stateset, i) of
    [] => syntax_error indata (* MMW *)(* FIXME *)
  | s =>
    (case indata of
      [] => Array.sub (stateset, i)
    | c :: cs =>
      let
        val (si, sii) = PROCESSS stateset grammar i c s;
      in
        Array.update (stateset, i, si);
        Array.update (stateset, i + 1, sii);
        produce grammar stateset (i + 1) cs
      end));


(*(* FIXME new *)
val get_trees = mapfilter (fn (_, _, [pt], _, _, _) => Some pt | _ => None);
*)

fun get_trees [] = []
  | get_trees ((_, _, pt_lst, _, _, _) :: stateset) =
      let val l = get_trees stateset
      in case pt_lst of
           [ptree] => ptree :: l
         |   _     => l
      end;

fun earley grammar startsymbol indata =
  let
    val S0 = [("S'", 0, [], [Nonterminal (startsymbol, 0), Terminal EndToken], "", 0)];
    val s = length indata + 1;     (* MMW *)(* FIXME was .. + 2 *)
    val Estate = Array.array (s, []);
  in
    Array.update (Estate, 0, S0);
    let
      val l = produce grammar Estate 0 indata;    (* MMW *)(* FIXME was .. @ [EndToken] *)
      val p_trees = get_trees l;
    in p_trees end
  end;


(* FIXME demo *)
fun parse (Gram (_, prod_tab)) start toks =
  (case earley prod_tab start toks of
    [] => sys_error "parse: no parse trees"
  | pt :: _ => pt);


end;

