(*  Title:      Pure/Syntax/parser.ML
    ID:         $Id$
    Author:     Sonia Mahjoub, Markus Wenzel and Carsten Clasohm, TU Muenchen

Isabelle's main parser (used for terms and types).
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
  val branching_level: int ref;
end;

functor ParserFun(structure Symtab: SYMTAB and Lexicon: LEXICON
  and SynExt: SYN_EXT): PARSER =
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
        let fun look [] _ result = result
              | look ((symbs, _, _) :: todos) done result =
                  let val (start_token, skipped) = rhss_start symbs [];

                      (*process all nonterminals on which the lookahead
                        depends and build the new todo and done lists for
                        the look function*)
                      fun look2 [] todos result = 
                            look todos (done union skipped) result
                        | look2 (rhss_ref :: ls) todos result =
                            if rhss_ref mem done then look2 ls todos result
                            else case assoc (starts, rhss_ref) of
                                Some tks => look2 ls todos (tks union result)
                              | None => 
                                  let val (_, rhss) = hd (!rhss_ref);
                                  in look2 ls (rhss @ todos) result end;
                  in case start_token of
                         Some tk => look2 skipped todos (start_token ins result)
                       | None => look2 skipped todos result
                  end;
 
            val (_, rhss) = hd (!rhss_ref);
        in look rhss [rhss_ref] [] end;                       

      (*make a table that contains all possible starting terminals
        for each nonterminal*)
      fun mk_starts [] starts = starts
        | mk_starts ((_, rhss_ref) :: ps) starts =
            mk_starts ps ((rhss_ref, look_rhss starts rhss_ref) :: starts);

      val starts = mk_starts ref_gram [];

      (*add list of allowed starting tokens to productions*)
      fun mk_lookahead (_, rhss_ref) =
        let (*compares two values of type token option 
              (used for speed reasons)*)
            fun matching_opt_tks (Some tk1, Some tk2) =
                  matching_tokens (tk1, tk2)
              | matching_opt_tks _ = false;

            (*add item to lookahead list (a list containing pairs of token and 
              rhss that can be started with it)*)
            fun add_start new_rhs tokens table =
                  let fun add [] [] = []
                        | add (tk :: tks) [] =
                            (tk, [new_rhs]) :: (add tks [])
                        | add tokens ((tk, rhss) :: ss) =
                            if gen_mem matching_opt_tks (tk, tokens) then 
                              (tk, new_rhs :: rhss) :: (add (tokens \ tk) ss)
                            else
                              (tk, rhss) :: (add tokens ss);
                  in add tokens table end;

            (*combine all lookaheads of a list of nonterminals*)
            fun combine_starts rhss_refs =
              foldr (gen_union matching_opt_tks)
              ((map (fn rhss_ref => let val Some tks = assoc (starts, rhss_ref)
                                    in tks end) rhss_refs), []);

            (*get lookahead for a rhs and update lhs' lookahead list*)
            fun look_rhss [] table = table
              | look_rhss ((rhs as (symbs, id, prec)) :: rs) table =
                  let val (start_token, skipped) = rhss_start symbs [];
                      val starts = case start_token of
                                     Some tk => gen_ins matching_opt_tks 
                                             (Some tk, combine_starts skipped)
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

fun extend_gram (gram1 as Gram (prods1, _)) roots xprods2 =
  let
    fun simplify preserve s = 
      if preserve then 
        (if s mem (roots \\ ["type", "prop", "any"]) then "logic" else s)
      else (if s = "prop" then "@prop_H" else
              (if s mem (roots \\ ["type", "prop", "any"]) then 
                 "@logic_H" 
               else s));

    fun not_delim (Delim _) = false
      | not_delim _ = true

    fun symb_of _ (Delim s) = Some (Terminal (Token s))
      | symb_of preserve (Argument (s, p)) =
          (case predef_term s of
            None => Some (Nonterminal (simplify preserve s, p))
          | Some tk => Some (Terminal tk))
      | symb_of _ _ = None;

    fun prod_of (XProd (lhs, xsymbs, const, pri)) =
      let val copy_prod = (lhs = "prop" andalso forall not_delim xsymbs andalso
                           const <> "");

          val preserve = copy_prod 
                         orelse pri = chain_pri andalso lhs = "logic"
                         orelse lhs mem ["@prop_H", "@logic_H", "any"];

          val lhs' = if copy_prod then "@prop_H" else
                     if lhs = "logic" andalso pri = chain_pri
                        then "@logic_H"
                     else if lhs mem ("logic1" :: (roots \\ ["type", "prop"])) 
                        then "logic"
                     else lhs;
      in (lhs', (mapfilter (symb_of preserve) xsymbs, const, pri))
      end;

    val prods2 = distinct (map prod_of xprods2);
  in
    if prods2 subset prods1 then gram1
    else (writeln "Building new grammar...";
          mk_gram (extend_list prods1 prods2))
  end;

fun merge_grams (gram1 as Gram (prods1, _)) (gram2 as Gram (prods2, _)) =
  if prods2 subset prods1 then gram1
  else if prods1 subset prods2 then gram2
  else (writeln "Building new grammar...";
        mk_gram (merge_lists prods1 prods2));


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


val warned = ref false;  (*flag for warning message*)
val branching_level = ref 100;  (*trigger value for warnings*)

fun PROCESSS Estate i c states =
let
fun get_lookahead rhss_ref = token_assoc (!rhss_ref, c);

fun processS used [] (Si, Sii) = (Si, Sii)
  | processS used (S :: States) (Si, Sii) =
      (case S of
        (_, _, _, Nonterm (rhss_ref, minPrec) :: _, _, _) =>
          let                                       (*predictor operation*)
            val (used_new, new_states) =
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
            processS used_new (new_states @ States) (S :: Si, Sii)
          end
      | (_, _, _, Term a :: _, _, _) =>               (*scanner operation*)
          processS used States
            (S :: Si,
              if matching_tokens (a, c) then movedot_term S c :: Sii else Sii)
      | (A, prec, ts, [], id, j) =>                   (*completer operation*)
          let
            fun check_branching len =
              if not (!warned) andalso len > (!branching_level) then
                (writeln "Warning: Currently parsed expression could be \
                         \extremely ambiguous.";
                 warned := true)
              else ();

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
                      val _ = check_branching (length Slist);
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
                        val _ = check_branching (length Slist);
                        val States' = map (movedot_nonterm tt) Slist;
                      in
                       processS used' (States' @ States) (S :: Si, Sii)
                      end)
              end 
            else
              let val Slist = getStates Estate i j A prec;
                  val _ = check_branching (length Slist);
              in processS used (map (movedot_nonterm tt) Slist @ States)
                   (S :: Si, Sii)
              end
          end)
in processS [] states ([], []) end;


fun syntax_error toks allowed =
  error 
  ((if toks = [] then
      "error: unexpected end of input\n"
    else
      "Syntax error at: " ^ quote (space_implode " " (map str_of_token 
        ((rev o tl o rev) toks)))
      ^ "\n")
   ^ "Expected tokens: " 
   ^ space_implode ", " (map (quote o str_of_token) allowed));

fun produce stateset i indata prev_token =
                     (*the argument prev_token is only used for error messages*)
  (case Array.sub (stateset, i) of
    [] => let (*similar to token_assoc but does not automatically 
                include 'None' key*)
              fun token_assoc2 (list, key) =
                let fun assoc [] = []
                      | assoc ((keyi, xi) :: pairs) =
                          if is_some keyi andalso
                             matching_tokens (the keyi, key) then 
                            (assoc pairs) @ xi
                          else assoc pairs;
                          in assoc list end;

              (*test if tk is a lookahead for a given minimum precedence*)
              fun reduction minPrec tk _ (Term _ :: _, _, prec:int) =
                    if prec >= minPrec then true
                    else false
                | reduction minPrec tk checked 
                            (Nonterm (rhss_ref, NTprec)::_,_, prec) =
                    if prec >= minPrec andalso not (rhss_ref mem checked) then
                      exists (reduction NTprec tk (rhss_ref :: checked)) 
                             (token_assoc2 (!rhss_ref, tk))
                    else false;

              (*compute a list of allowed starting tokens 
                for a list of nonterminals considering precedence*)
              fun get_starts [] = []
                | get_starts ((rhss_ref, minPrec:int) :: refs) =
                    let fun get [] = []
                          | get ((Some tk, prods) :: rhss) =
                              if exists (reduction minPrec tk [rhss_ref]) prods
                              then tk :: (get rhss)
                              else get rhss
                          | get ((None, _) :: rhss) =
                              get rhss;
                    in (get (!rhss_ref)) union (get_starts refs) end;

              val NTs = map (fn (_, _, _, Nonterm (a, prec) :: _, _, _) => 
                              (a, prec))
                            (filter (fn (_, _, _, Nonterm _ :: _, _, _) => true
                                     | _ => false) (Array.sub (stateset, i-1)));
              val allowed = distinct (get_starts NTs @
                            (map (fn (_, _, _, Term a :: _, _, _) => a)
                            (filter (fn (_, _, _, Term _ :: _, _, _) => true
                                   | _ => false) (Array.sub (stateset, i-1)))));
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
    val startsymbol' = case startsymbol of
                           "logic" => "@logic_H"
                         | "prop"  => "@prop_H"
                         | other   => other;
    val rhss_ref = case assoc (grammar, startsymbol) of
                       Some r => r
                     | None   => error ("parse: Unknown startsymbol " ^ 
                                        quote startsymbol);
    val S0 = [(ref [], 0, [], [Nonterm (rhss_ref, 0), Term EndToken], "", 0)];
    val s = length indata + 1;
    val Estate = Array.array (s, []);
  in
    Array.update (Estate, 0, S0);
    let
      val l = (warned := false; produce Estate 0 indata EndToken(*dummy*));

      val p_trees = get_trees l;
    in p_trees end
  end;


fun parse (Gram (_, prod_tab)) start toks =
let val r =
  (case earley prod_tab start toks of
    [] => sys_error "parse: no parse trees"
  | pts => pts);
in r end

end;
