(*  Title:      Pure/Syntax/parser.ML
    ID:         $Id$
    Author:     Sonia Mahjoub, Markus Wenzel and Carsten Clasohm, TU Muenchen

Isabelle's main parser (used for terms and typs).

TODO:
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
    val parse: gram -> string -> token list -> parsetree list
  end
end;

functor ParserFun(structure Symtab: SYMTAB and Lexicon: LEXICON
  and SynExt: SYN_EXT) =
struct

structure Pretty = SynExt.Ast.Pretty;
structure Lexicon = Lexicon;
structure SynExt = SynExt;
open Lexicon SynExt;


(** datatype gram **)

datatype symb =
  Terminal of token |
  Nonterminal of string * int;

datatype refsymb = Term of token | Nonterm of rhss_ref * int
                                (*reference to production list instead of name*)
and gram = Gram of (string * (symb list * string * int)) list *
                   (string * rhss_ref) list
withtype rhss_ref = (token option * (refsymb list * string * int) list) list ref
                                      (*lookahead table: token and productions*)

(* convert productions to reference grammar with lookaheads and eliminate
   chain productions *)
fun mk_gram prods = 
  let (*get reference on list of all possible rhss for nonterminal lhs
        (if it doesn't exist a new one is created and added to the nonterminal
         list)*)
      fun get_rhss ref_prods lhs =
        case assoc (ref_prods, lhs) of
            None =>
              let val l = ref [(None, [])]
              in (l, (lhs, l) :: ref_prods) end
          | Some l => (l, ref_prods);

      (*convert symb list to refsymb list*)
      fun mk_refsymbs ref_prods [] rs = (rs, ref_prods)
        | mk_refsymbs ref_prods (Terminal tk :: symbs) rs =
            mk_refsymbs ref_prods symbs (rs @ [Term tk])
        | mk_refsymbs ref_prods (Nonterminal (name, prec) :: symbs) rs =
            let val (rhss, ref_prods') = get_rhss ref_prods name
            in mk_refsymbs ref_prods' symbs (rs @ [Nonterm (rhss, prec)])
            end;

      (*convert prod list to (string * rhss_ref) list
        without computing lookaheads*)
      fun mk_ref_gram [] ref_prods = ref_prods
        | mk_ref_gram ((lhs, (rhs, name, prec)) :: ps) ref_prods =
            let val (rhs', ref_prods') = get_rhss ref_prods lhs;
                val (dummy, rhss) = hd (!rhs');
                val (ref_symbs, ref_prods'') = mk_refsymbs ref_prods' rhs [];
            in rhs' := [(dummy, (ref_symbs, name, prec) :: rhss)];
               mk_ref_gram ps ref_prods''
            end;

      (*eliminate chain productions*)
      fun elim_chain ref_gram =
        let (*make a list of pairs representing chain productions and delete
              these productions*)
            fun list_chain [] = []
              | list_chain ((_, rhss_ref) :: ps) =
                  let fun lists [] new_rhss chains = (new_rhss, chains)
                        | lists (([Nonterm (id2, ~1)], _, ~1) :: rs) 
                                new_rhss chains =
                            lists rs new_rhss ((rhss_ref, id2) :: chains)
                        | lists (rhs :: rs) new_rhss chains = 
                            lists rs (rhs :: new_rhss) chains;

                      val (dummy, rhss) = hd (!rhss_ref);

                      val (new_rhss, chains) = lists rhss [] [];
                  in rhss_ref := [(dummy, new_rhss)];
                     chains @ (list_chain ps)
                  end;

            (*convert a list of pairs to an association list
              by using the first element as the key*)
            fun mk_assoc pairs =
              let fun doit [] result = result
                    | doit ((id1, id2) :: ps) result =
                        doit ps 
                        (overwrite (result, (id1, id2 :: (assocs result id1))));
              in doit pairs [] end;

            (*replace reference by list of rhss in chain pairs*)
            fun deref (id1, ids) =
              let fun deref1 [] = []
                    | deref1 (id :: ids) =
                        let val (_, rhss) = hd (!id);
                        in rhss @ (deref1 ids) end;
              in (id1, deref1 ids) end;

            val chain_pairs = 
               map deref (transitive_closure (mk_assoc (list_chain ref_gram)));

            (*add new rhss to productions*)
            fun elim (rhss_ref, rhss) =
              let val (dummy, old_rhss) = hd (!rhss_ref);
              in rhss_ref := [(dummy, old_rhss @ rhss)] end;
        in map elim chain_pairs;
           ref_gram
        end;

      val ref_gram = elim_chain (mk_ref_gram prods []);

      (*make a list of all lambda NTs 
        (i.e. nonterminals that can produce lambda*)
      val lambdas =
        let fun lambda [] result = result
              | lambda ((_, rhss_ref) :: nts) result =
                  if rhss_ref mem result then
                    lambda nts result
                  else
                    let (*list all NTs that can be produced by a rhs
                          containing only lambda NTs*)
                        fun only_lambdas [] result = result
                          | only_lambdas ((_, rhss_ref) :: ps) result =
                              let fun only (symbs, _, _) =
                                   forall (fn (Nonterm (id, _)) => id mem result
                                            | (Term _)          => false) symbs;
                          
                                  val (_, rhss) = hd (!rhss_ref);
                              in if not (rhss_ref mem result) andalso
                                    exists only rhss then
                                   only_lambdas ref_gram (rhss_ref :: result)
                                 else
                                   only_lambdas ps result
                              end;

                        val (_, rhss) = hd (!rhss_ref);
                    in if exists (fn (symbs, _, _) => null symbs) rhss
                       then lambda nts
                              (only_lambdas ref_gram (rhss_ref :: result))
                       else lambda nts result
                    end;
         in lambda ref_gram [] end;

      (*list all nonterminals on which the lookahead depends (due to lambda 
        NTs this can be more than one)
        and report if there is a terminal at the 'start'*)
      fun rhss_start [] skipped = (None, skipped)
        | rhss_start (Term tk :: _) skipped = (Some tk, skipped)
        | rhss_start (Nonterm (rhss_ref, _) :: rest) skipped =
            if rhss_ref mem lambdas then 
              rhss_start rest (rhss_ref ins skipped)
            else
              (None, rhss_ref ins skipped);

      (*list all terminals that can start the given rhss*)
      fun look_rhss starts rhss_ref =
        let fun look [] _ = []
              | look ((symbs, _, _) :: todos) done =
                  let val (start_token, skipped) = rhss_start symbs [];

                      (*process all nonterminals on which the lookahead
                        depends and build the new todo and done lists for
                        the look function*)
                      fun look2 [] todos = look todos (done union skipped)
                        | look2 (rhss_ref :: ls) todos =
                            if rhss_ref mem done then look2 ls todos
                            else case assoc (starts, rhss_ref) of
                                Some tks => tks union (look2 ls todos)
                              | None => let val (_, rhss) = hd (!rhss_ref);
                                        in look2 ls (rhss union todos) end;
                  in case start_token of
                         Some tk => start_token ins (look2 skipped todos)
                       | None => look2 skipped todos
                  end;
 
            val (_, rhss) = hd (!rhss_ref);
        in look rhss [rhss_ref] end;                       

      (*make a table that contains all possible starting terminals
        for each nonterminal*)
      fun mk_starts [] starts = starts
        | mk_starts ((_, rhss_ref) :: ps) starts =
            mk_starts ps ((rhss_ref, look_rhss starts rhss_ref) :: starts);

      val starts = mk_starts ref_gram [];

      (*add list of allowed starting tokens to productions*)
      fun mk_lookahead (_, rhss_ref) =
        let (*add item to lookahead list (a list containing pairs of token and 
              rhss that can be started with it*)
            fun add_start new_rhs tokens table =
                  let fun add [] [] = []
                        | add (tk :: tks) [] =
                            (tk, [new_rhs]) :: (add tks [])
                        | add tokens ((tk, rhss) :: ss) =
                            if tk mem tokens then 
                              (tk, new_rhs :: rhss) :: (add (tokens \ tk) ss)
                            else
                              (tk, rhss) :: (add tokens ss);
                  in add tokens table end;

            (*combine all lookaheads of a list of nonterminals*)
            fun combine_starts rhss_refs =
              foldr (op union) 
              ((map (fn rhss_ref => let val Some tks = assoc (starts, rhss_ref)
                                    in tks end) rhss_refs), []);

            (*get lookahead for a rhs and update lhs' lookahead list*)
            fun look_rhss [] table = table
              | look_rhss ((rhs as (symbs, id, prec)) :: rs) table =
                  let val (start_token, skipped) = rhss_start symbs [];
                      val starts = case start_token of
                                     Some tk => Some tk 
                                                ins (combine_starts skipped)
                                   | None => if skipped subset lambdas then
                                               [None]
                                             else
                                               combine_starts skipped;
                  in look_rhss rs (add_start rhs starts table) end;

             val (_, rhss) = hd (!rhss_ref);
        in rhss_ref := look_rhss rhss [] end;

  in map mk_lookahead ref_gram;
     Gram (prods, ref_gram)
  end;


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
  rhss_ref * int      (*lhs: identification and production precedence*)
  * parsetree list    (*already parsed nonterminals on rhs*)
  * refsymb list      (*rest of rhs*)
  * string            (*name of production*)
  * int;              (*index for previous state list*)

type earleystate = state list Array.array;


(*Get all rhss with precedence >= minPrec*)
fun getRHS minPrec = filter (fn (_, _, prec:int) => prec >= minPrec);

(*Get all rhss with precedence >= minPrec and < maxPrec*)
fun getRHS' minPrec maxPrec =
  filter (fn (_, _, prec:int) => prec >= minPrec andalso prec < maxPrec);

(*Make states using a list of rhss*)
fun mkStates i minPrec lhsID rhss =
  let fun mkState (rhs, id, prodPrec) = (lhsID, prodPrec, [], rhs, id, i);
  in map mkState rhss end;
	
(*Add parse tree to list and eliminate duplicates 
  saving the maximum precedence*)
fun conc (t, prec:int) [] = (None, [(t, prec)])
  | conc (t, prec) ((t', prec') :: ts) =
      if t = t' then
        (Some prec', if prec' >= prec then (t', prec') :: ts 
                     else (t, prec) :: ts)
      else
        let val (n, ts') = conc (t, prec) ts
        in (n, (t', prec') :: ts') end;

(*Update entry in used*)
fun update_tree ((B, (i, ts)) :: used) (A, t) =
  if A = B then
    let val (n, ts') = conc t ts
    in ((A, (i, ts')) :: used, n) end
  else
    let val (used', n) = update_tree used (A, t)
    in ((B, (i, ts)) :: used', n) end;

(*Replace entry in used*)
fun update_index (A, prec) used =
  let fun update((hd as (B, (_, ts))) :: used, used') =
        if A = B
        then used' @ ((A, (prec, ts)) :: used)
        else update (used, hd :: used')
  in update (used, []) end;

fun getS A maxPrec Si =
  filter
    (fn (_, _, _, Nonterm (B, prec) :: _, _, _)
          => A = B andalso prec <= maxPrec
      | _ => false) Si;

fun getS' A maxPrec minPrec Si =
  filter
    (fn (_, _, _, Nonterm (B, prec) :: _, _, _)
          => A = B andalso prec > minPrec andalso prec <= maxPrec
      | _ => false) Si;

fun getStates Estate i ii A maxPrec =
  filter
    (fn (_, _, _, Nonterm (B, prec) :: _, _, _)
          => A = B andalso prec <= maxPrec
      | _ => false)
    (Array.sub (Estate, ii));


fun movedot_term (A, j, ts, Term a :: sa, id, i) c =
  if valued_token c then
    (A, j, (ts @ [Tip c]), sa, id, i)
  else (A, j, ts, sa, id, i);

fun movedot_nonterm ts (A, j, tss, Nonterm _ :: sa, id, i) =
  (A, j, tss @ ts, sa, id, i);

fun movedot_lambda _ [] = []
  | movedot_lambda (B, j, tss, Nonterm (A, k) :: sa, id, i) ((t, ki) :: ts) =
      if k <= ki then
        (B, j, tss @ t, sa, id, i) ::
          movedot_lambda (B, j, tss, Nonterm (A, k) :: sa, id, i) ts
      else movedot_lambda (B, j, tss, Nonterm (A, k) :: sa, id, i) ts;



fun PROCESSS Estate i c states =
let
fun get_lookahead rhss_ref = token_assoc (!rhss_ref, c);

fun processS used [] (Si, Sii) = (Si, Sii)
  | processS used (S :: States) (Si, Sii) =
      (case S of
        (_, _, _, Nonterm (rhss_ref, minPrec) :: _, _, _) =>
          let                                       (*predictor operation*)
            val (used_new, States_new) =
              (case assoc (used, rhss_ref) of
                Some (usedPrec, l) =>       (*nonterminal has been processed*)
                  if usedPrec <= minPrec then
                                      (*wanted precedence has been processed*)
                    (used, movedot_lambda S l)
                  else            (*wanted precedence hasn't been parsed yet*)
                    let val rhss = get_lookahead rhss_ref;
                      val States' = mkStates i minPrec rhss_ref
                                      (getRHS' minPrec usedPrec rhss);
                    in (update_index (rhss_ref, minPrec) used, 
                        movedot_lambda S l @ States')
                    end

              | None =>           (*nonterminal is parsed for the first time*)
                  let val rhss = get_lookahead rhss_ref;
                      val States' = mkStates i minPrec rhss_ref
                                      (getRHS minPrec rhss);
                  in ((rhss_ref, (minPrec, [])) :: used, States') end)
          in
            processS used_new (States_new @ States) (S :: Si, Sii)
          end
      | (_, _, _, Term a :: _, _, _) =>               (*scanner operation*)
          processS used States
            (S :: Si,
              if matching_tokens (a, c) then movedot_term S c :: Sii else Sii)

      | (A, prec, ts, [], id, j) =>                   (*completer operation*)
          let
            val tt = if id = "" then ts else [Node (id, ts)]
          in
            if j = i then                             (*lambda production?*)
              let
                val (used', O) = update_tree used (A, (tt, prec));
              in
                (case O of
                  None =>
                    let
                      val Slist = getS A prec Si;
                      val States' = map (movedot_nonterm tt) Slist;
                    in
                      processS used' (States' @ States) (S :: Si, Sii)
                    end
                | Some n =>
                    if n >= prec then
                      processS used' States (S :: Si, Sii)
                    else
                      let
                        val Slist = getS' A prec n Si;
                        val States' = map (movedot_nonterm tt) Slist;
                      in
                        processS used' (States' @ States) (S :: Si, Sii)
                      end)
              end 
            else
              processS used
                (map (movedot_nonterm tt) (getStates Estate i j A prec) @ States)
                (S :: Si, Sii)
          end)
in
  processS [] states ([], [])
end;



fun syntax_error toks allowed =
  error 
  ((if toks = [] then
      "error: unexpected end of input\n"
    else
      "Syntax error at: " ^ quote (space_implode " " (map str_of_token toks))
      ^ "\n")
   ^ "Expected tokens: " 
   ^ space_implode ", " (map (quote o str_of_token) allowed));

fun produce stateset i indata prev_token =
                     (*the argument prev_token is only used for error messages*)
  (case Array.sub (stateset, i) of
    [] => let (*compute a list of allowed starting tokens 
                for a list of nonterminals*)
              fun get_starts [] = []
                | get_starts (rhss_ref :: refs) =
                    let fun get [] = []
                          | get ((Some tok, _) :: rhss) =
                              tok :: (get rhss)
                          | get ((None, _) :: rhss) =
                              get rhss;
                    in (get (!rhss_ref)) union (get_starts refs) end;

              val NTs = map (fn (_, _, _, Nonterm (a, _) :: _, _, _) => a)
                            (filter (fn (_, _, _, Nonterm _ :: _, _, _) => true
                                     | _ => false) (Array.sub (stateset, i-1)));
              val allowed = get_starts NTs union
                            (map (fn (_, _, _, Term a :: _, _, _) => a)
                            (filter (fn (_, _, _, Term _ :: _, _, _) => true
                                    | _ => false) (Array.sub (stateset, i-1))));
                                             (*terminals have to be searched for
                                               because of lambda productions*)
          in syntax_error (if prev_token = EndToken then indata
                           else prev_token :: indata) allowed
          end
  | s =>
    (case indata of
      [] => Array.sub (stateset, i)
    | c :: cs =>
      let
        val (si, sii) = PROCESSS stateset i c s;
      in
        Array.update (stateset, i, si);
        Array.update (stateset, i + 1, sii);
        produce stateset (i + 1) cs c
      end));


val get_trees = mapfilter (fn (_, _, [pt], _, _, _) => Some pt | _ => None);


fun earley grammar startsymbol indata =
  let
    val rhss_ref = case assoc (grammar, startsymbol) of
                       Some r => r
                     | None => error ("parse: Unknown startsymbol " ^ 
                                      quote startsymbol);
    val S0 = [(ref [], 0, [], [Nonterm (rhss_ref, 0), Term EndToken], "", 0)];
    val s = length indata + 1;
    val Estate = Array.array (s, []);
  in
    Array.update (Estate, 0, S0);
    let
      val l = produce Estate 0 indata EndToken(*dummy*);
      val p_trees = get_trees l;
    in p_trees end
  end;


fun parse (Gram (_, prod_tab)) start toks =
  (case earley prod_tab start toks of
    [] => sys_error "parse: no parse trees"
  | pts => pts);

end;

