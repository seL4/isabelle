(*  Title:      Pure/Syntax/parser.ML
    ID:         $Id$
    Author:     Sonia Mahjoub, Markus Wenzel, and Carsten Clasohm, TU Muenchen

Isabelle's main parser (used for terms and types).
*)

signature PARSER =
sig
  structure Lexicon: LEXICON
  structure SynExt: SYN_EXT
  local open Lexicon SynExt SynExt.Ast in
    type gram
    val empty_gram: gram
    val extend_gram: gram -> xprod list -> gram
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

type nt_tag = int;              (*production for the NTs are stored in an array
                                  so we can identify NTs by their index*)

datatype symb = Terminal of token
              | Nonterminal of nt_tag * int;              (*(tag, precedence)*)

type nt_gram = ((nt_tag list * token list) *
                (token option * (symb list * string * int) list) list);
                                     (*(([dependent_nts], [start_tokens]),
                                        [(start_token, [(rhs, name, prio)])])*)
                              (*depent_nts is a list of all NTs whose lookahead
                                depends on this NT's lookahead*)

datatype gram =
  Gram of {nt_count: int, prod_count: int,
           tags: nt_tag Symtab.table,
           chains: (nt_tag * nt_tag list) list,              (*[(to, [from])]*)
           lambdas: nt_tag list,
           prods: nt_gram Array.array};
                       (*"tags" is used to map NT names (i.e. strings) to tags;
                         chain productions are not stored as normal productions
                         but instead as an entry in "chains";
                         lambda productions are stored as normal productions
                         and also as an entry in "lambdas"*)

val UnknownStart = EndToken;       (*productions for which no starting token is
                                     known yet are associated with this token*)

(* get all NTs that are connected with a list of NTs 
   (used for expanding chain list)*)
fun connected_with _ [] relatives = relatives
  | connected_with chains (root :: roots) relatives =
    let val branches = (assocs chains root) \\ relatives;
    in connected_with chains (branches @ roots) (branches @ relatives) end;

(* convert productions to grammar;
   N.B. that the chains parameter has the form [(from, [to])];
   prod_count is of type "int option" and is only updated if it is <> None*)
fun add_prods _ chains lambdas prod_count [] = (chains, lambdas, prod_count)
  | add_prods prods chains lambdas prod_count
              ((lhs, new_prod as (rhs, name, pri)) :: ps) =
    let
      (*test if new_prod is a chain production*)
      val (new_chain, chains') =
        let (*store chain if it does not already exist*)
            fun store_chain from =
              let val old_tos = assocs chains from;
              in if lhs mem old_tos then (None, chains)
                 else (Some from, overwrite (chains, (from, lhs ins old_tos)))
              end;
        in if pri = ~1 then
             case rhs of [Nonterminal (id, ~1)] => store_chain id
                       | _ => (None, chains)
           else (None, chains)
        end;

      (*propagate new chain in lookahead and lambda lists;
        added_starts is used later to associate existing
        productions with new starting tokens*)
      val (added_starts, lambdas') =
        if is_none new_chain then ([], lambdas) else
        let (*lookahead of chain's source*)
            val ((from_nts, from_tks), _) = Array.sub (prods, the new_chain);

            (*copy from's lookahead to chain's destinations*)
            fun copy_lookahead [] added = added
              | copy_lookahead (to :: tos) added =
                let
                  val ((to_nts, to_tks), ps) = Array.sub (prods, to);

                  val new_tks = from_tks \\ to_tks;  (*added lookahead tokens*)
                in Array.update (prods, to, ((to_nts, to_tks @ new_tks), ps));
                   copy_lookahead tos (if null new_tks then added
                                       else (to, new_tks) :: added)
                end;

            val tos = connected_with chains' [lhs] [lhs];
        in (copy_lookahead tos [],
            (if lhs mem lambdas then tos else []) union lambdas)
        end;

      (*test if new production can produce lambda
        (rhs must either be empty or only consist of lambda NTs)*)
      val (new_lambda, lambdas') =
        if forall (fn (Nonterminal (id, _)) => id mem lambdas'
                    | (Terminal _) => false) rhs then
          (true, lambdas' union (connected_with chains' [lhs] [lhs]))
        else
          (false, lambdas');

      (*list optional terminal and all nonterminals on which the lookahead
        of a production depends*)
      fun lookahead_dependency _ [] nts = (None, nts)
        | lookahead_dependency _ ((Terminal tk) :: _) nts = (Some tk, nts)
        | lookahead_dependency lambdas ((Nonterminal (nt, _)) :: symbs) nts =
            if nt mem lambdas then
              lookahead_dependency lambdas symbs (nt :: nts)
            else (None, nt :: nts);

      (*get all known starting tokens for a nonterminal*)
      fun starts_for_nt nt = snd (fst (Array.sub (prods, nt)));

      val token_union = gen_union matching_tokens;

      (*update prods, lookaheads, and lambdas according to new lambda NTs*)
      val (added_starts', lambdas') =
        let
          (*propagate added lambda NT*)
          fun propagate_lambda [] added_starts lambdas= (added_starts, lambdas)
            | propagate_lambda (l :: ls) added_starts lambdas =
              let
                (*get lookahead for lambda NT*)
                val ((dependent, l_starts), _) = Array.sub (prods, l);

                (*check productions whose lookahead may depend on lamdba NT*)
                fun examine_prods [] add_lambda nt_dependencies added_tks
                                  nt_prods =
                      (add_lambda, nt_dependencies, added_tks, nt_prods)
                  | examine_prods ((p as (rhs, _, _)) :: ps) add_lambda
                      nt_dependencies added_tks nt_prods =
                    let val (tk, nts) = lookahead_dependency lambdas rhs [];
                    in
                      if l mem nts then       (*update production's lookahead*)
                      let
                        val new_lambda = is_none tk andalso nts subset lambdas;

                        val new_tks = (if is_some tk then [the tk] else []) @
                          foldl token_union ([], map starts_for_nt nts) \\
                          l_starts;
  
                        val added_tks' = token_union (new_tks, added_tks);

                        val nt_dependencies' = nts union nt_dependencies;

                        (*associate production with new starting tokens*)
                        fun copy [] nt_prods = nt_prods
                          | copy (tk :: tks) nt_prods =
                            let val old_prods = assocs nt_prods tk;

                                val prods' = p :: old_prods;
                            in copy tks (overwrite (nt_prods, (tk, prods')))
                            end;
  
                        val nt_prods' =
                          let val new_opt_tks = map Some new_tks;
                          in copy ((if new_lambda then [None] else []) @
                                   new_opt_tks) nt_prods
                          end;
                      in examine_prods ps (add_lambda orelse new_lambda)
                           nt_dependencies' added_tks' nt_prods'
                      end
                      else                                  (*skip production*)
                        examine_prods ps add_lambda nt_dependencies
                                      added_tks nt_prods
                    end;

                (*check each NT whose lookahead depends on new lambda NT*)
                fun process_nts [] added_lambdas added_starts =
                      (added_lambdas, added_starts)
                  | process_nts (nt :: nts) added_lambdas added_starts =
                    let
                      val (lookahead as (old_nts, old_tks), nt_prods) =
                        Array.sub (prods, nt);

                      (*existing productions whose lookahead may depend on l*)
                      val tk_prods =
                        assocs nt_prods
                               (Some (hd l_starts  handle Hd => UnknownStart));

                      (*add_lambda is true if an existing production of the nt
                        produces lambda due to the new lambda NT l*)
                      val (add_lambda, nt_dependencies, added_tks, nt_prods') =
                        examine_prods tk_prods false [] [] nt_prods;

                      val added_nts = nt_dependencies \\ old_nts;

                      val added_lambdas' =
                        if add_lambda then nt :: added_lambdas
                        else added_lambdas;
                    in Array.update (prods, nt,
                                   ((added_nts @ old_nts, old_tks @ added_tks),
                                    nt_prods'));
                                          (*N.B. that because the tks component
                                            is used to access existing
                                            productions we have to add new
                                            tokens at the _end_ of the list*)

                       if null added_tks then
                         process_nts nts added_lambdas' added_starts
                       else
                         process_nts nts added_lambdas'
                                      ((nt, added_tks) :: added_starts)
                    end;

                val (added_lambdas, added_starts') =
                  process_nts dependent [] added_starts;

                val added_lambdas' = added_lambdas \\ lambdas;
              in propagate_lambda (ls @ added_lambdas') added_starts'
                                  (added_lambdas' @ lambdas)
              end;
        in propagate_lambda (lambdas' \\ lambdas) added_starts lambdas' end;

      (*insert production into grammar*)
      val (added_starts', prod_count') =
        if is_some new_chain then (added_starts', prod_count)
                                               (*don't store chain production*)
        else let
          (*lookahead tokens of new production and on which
            NTs lookahead depends*)
          val (start_tk, start_nts) = lookahead_dependency lambdas' rhs [];

          val start_tks = foldl token_union
                          (if is_some start_tk then [the start_tk] else [],
                           map starts_for_nt start_nts);

          val opt_starts = (if new_lambda then [None]
                            else if null start_tks then [Some UnknownStart]
                            else []) @ (map Some start_tks);

          (*add lhs NT to list of dependent NTs in lookahead*)
          fun add_nts [] = ()
            | add_nts (nt :: nts) =
              let val ((old_nts, old_tks), ps) = Array.sub (prods, nt);
              in if lhs mem old_nts then ()
                 else Array.update (prods, nt, ((lhs :: old_nts, old_tks), ps))
              end;

          (*add new start tokens to chained NTs' lookahead list;
            also store new production for lhs NT*)
          fun add_tks [] added prod_count = (added, prod_count)
            | add_tks (nt :: nts) added prod_count =
              let
                val ((old_nts, old_tks), nt_prods) = Array.sub (prods, nt);

                val new_tks = gen_rems matching_tokens (start_tks, old_tks);

                (*store new production*)
                fun store [] prods is_new =
                      (prods, if is_some prod_count andalso is_new then
                                apsome (fn x => x+1) prod_count
                              else prod_count, is_new)
                  | store (tk :: tks) prods is_new =
                    let val tk_prods = assocs prods tk;

                        (*if prod_count = None then we can assume that
                          grammar does not contain new production already*)
                        val (tk_prods', is_new') =
                          if is_some prod_count then
                            if new_prod mem tk_prods then (tk_prods, false)
                            else (new_prod :: tk_prods, true)
                          else (new_prod :: tk_prods, true);

                        val prods' = if is_new' then
                                       overwrite (prods, (tk, tk_prods'))
                                     else prods;
                    in store tks prods' (is_new orelse is_new') end;

                val (nt_prods', prod_count', changed) =
                  if nt = lhs then store opt_starts nt_prods false
                              else (nt_prods, prod_count, false);
              in if not changed andalso null new_tks then ()
                 else Array.update (prods, nt, ((old_nts, old_tks @ new_tks),
                                                nt_prods'));
                 add_tks nts (if null new_tks then added
                              else (nt, new_tks) :: added) prod_count'
              end;
        in add_nts start_nts;
           add_tks (connected_with chains' [lhs] [lhs]) [] prod_count
        end;

      (*associate productions with new lookaheads*)
      val dummy =
        let
          (*propagate added start tokens*)
          fun add_starts [] = ()
            | add_starts ((changed_nt, new_tks) :: starts) =
              let
                (*token under which old productions which
                  depend on changed_nt could be stored*)
                val key =
                 case find_first (fn t => not (t mem new_tks))
                                 (starts_for_nt changed_nt) of
                      None => Some UnknownStart
                    | t => t;

                (*copy productions whose lookahead depends on changed_nt;
                  if key = Some UnknownToken then tk_prods is used to hold
                  the productions not copied*)
                fun update_prods [] result = result
                  | update_prods ((p as (rhs, _, _)) :: ps)
                      (tk_prods, nt_prods) =
                    let
                      (*lookahead dependency for production*)
                      val (tk, depends) = lookahead_dependency lambdas' rhs [];

                      (*test if this production has to be copied*)
                      val update = changed_nt mem depends;

                      (*test if production could already be associated with
                        a member of new_tks*)
                      val lambda = length depends > 1 orelse
                                   not (null depends) andalso is_some tk
                                   andalso the tk mem new_tks;

                      (*associate production with new starting tokens*)
                      fun copy [] nt_prods = nt_prods
                        | copy (tk :: tks) nt_prods =
                          let
                            val tk_prods = assocs nt_prods (Some tk);

                            val tk_prods' =
                              if not lambda then p :: tk_prods
                              else p ins tk_prods;
                                      (*if production depends on lambda NT we
                                        have to look for duplicates*)
                         in copy tks
                                 (overwrite (nt_prods, (Some tk, tk_prods')))
                         end;
                      val result =
                        if update then
                          (tk_prods, copy new_tks nt_prods)
                        else if key = Some UnknownStart then
                          (p :: tk_prods, nt_prods)
                        else (tk_prods, nt_prods);
                    in update_prods ps result end;

                (*copy existing productions for new starting tokens*)
                fun process_nts [] added = added
                  | process_nts (nt :: nts) added =
                    let
                      val (lookahead as (old_nts, old_tks), nt_prods) =
                        Array.sub (prods, nt);

                      val tk_prods = assocs nt_prods key;

                      (*associate productions with new lookahead tokens*)
                      val (tk_prods', nt_prods') =
                        update_prods tk_prods ([], nt_prods);

                      val nt_prods' =
                        if key = Some UnknownStart then
                          overwrite (nt_prods', (key, tk_prods'))
                        else nt_prods';

                      val added_tks =
                        gen_rems matching_tokens (new_tks, old_tks);
                    in if null added_tks then
                         (Array.update (prods, nt, (lookahead, nt_prods'));
                          process_nts nts added)
                       else
                         (Array.update (prods, nt,
                            ((old_nts, added_tks @ old_tks), nt_prods'));
                          process_nts nts ((nt, added_tks) :: added))
                    end;

                val ((dependent, _), _) = Array.sub (prods, changed_nt);
              in add_starts (starts @ (process_nts dependent [])) end;
        in add_starts added_starts' end;
  in add_prods prods chains' lambdas' prod_count ps end;


(* pretty_gram *)

fun pretty_gram (Gram {tags, prods, chains, ...}) =
  let
    fun pretty_name name = [Pretty.str (name ^ " =")];

    val taglist = Symtab.dest tags;

    fun pretty_symb (Terminal (Token s)) = Pretty.str (quote s)
      | pretty_symb (Terminal tok) = Pretty.str (str_of_token tok)
      | pretty_symb (Nonterminal (tag, p)) =
        let val name = fst (the (find_first (fn (n, t) => t = tag) taglist));
        in Pretty.str (name ^ "[" ^ string_of_int p ^ "]") end;

    fun pretty_const "" = []
      | pretty_const c = [Pretty.str ("=> " ^ quote c)];

    fun pretty_pri p = [Pretty.str ("(" ^ string_of_int p ^ ")")];

    fun pretty_prod name (symbs, const, pri) =
      Pretty.block (Pretty.breaks (pretty_name name @
        map pretty_symb symbs @ pretty_const const @ pretty_pri pri));

    fun pretty_nt (name, tag) =
      let
        fun prod_of_chain from = ([Nonterminal (from, ~1)], "", ~1);

        val nt_prods =
          foldl (op union) ([], map snd (snd (Array.sub (prods, tag)))) @
          map prod_of_chain (assocs chains tag);
      in map (pretty_prod name) nt_prods end;
        
  in flat (map pretty_nt taglist) end;


(* empty, extend, merge grams *)

val empty_gram = Gram {nt_count = 0, prod_count = 0,
                       tags = Symtab.null, chains = [], lambdas = [],
                       prods = Array.array (0, (([], []), []))};

fun inverse_chains [] result = result
  | inverse_chains ((root, branches) :: cs) result =
    let fun add [] result = result
          | add (id :: ids) result =
            let val old = assocs result id;
            in add ids (overwrite (result, (id, root :: old))) end;
    in inverse_chains cs (add branches result) end;

fun extend_gram gram [] = gram
  | extend_gram (Gram {nt_count, prod_count, tags, chains, lambdas, prods})
                xprods =
  let
    fun get_tag nt_count tags nt =
      case Symtab.lookup (tags, nt) of
        Some tag => (nt_count, tags, tag)
      | None => (nt_count+1, Symtab.update_new ((nt, nt_count), tags),
                 nt_count);
  
    fun symb_of [] nt_count tags result = (nt_count, tags, rev result)
      | symb_of ((Delim s) :: ss) nt_count tags result =
          symb_of ss nt_count tags ((Terminal (Token s)) :: result)
      | symb_of ((Argument (s, p)) :: ss) nt_count tags result =
          let
            val (nt_count', tags', new_symb) =
              case predef_term s of
                None =>
                  let val (nt_count', tags', s_tag) = get_tag nt_count tags s;
                  in (nt_count', tags', Nonterminal (s_tag, p)) end
              | Some tk => (nt_count, tags, Terminal tk);
          in symb_of ss nt_count' tags' (new_symb :: result) end
      | symb_of (_ :: ss) nt_count tags result =
          symb_of ss nt_count tags result;

    fun prod_of [] nt_count prod_count tags result =
          (nt_count, prod_count, tags, result)
      | prod_of ((XProd (lhs, xsymbs, const, pri)) :: ps)
                nt_count prod_count tags result =
        let val (nt_count', tags', lhs_tag) = get_tag nt_count tags lhs;

            val (nt_count'', tags'', prods) =
              symb_of xsymbs nt_count' tags' [];
        in prod_of ps nt_count'' (prod_count+1) tags''
                   ((lhs_tag, (prods, const, pri)) :: result)
        end;

    val (nt_count', prod_count', tags', prods2) =
      prod_of xprods nt_count prod_count tags [];

    val dummy = writeln "Building new grammar...";

    val prods' =
      let fun get_prod i = if i < nt_count then Array.sub (prods, i)
                           else (([], []), []);
      in Array.tabulate (nt_count', get_prod) end;

    val fromto_chains = inverse_chains chains [];

    val (fromto_chains', lambdas', _) =
      add_prods prods' fromto_chains lambdas None prods2;

    val chains' = inverse_chains fromto_chains' [];
  in Gram {nt_count = nt_count', prod_count = prod_count', tags = tags',
           chains = chains', lambdas = lambdas', prods = prods'}
  end;


fun merge_grams gram_a gram_b =
  let
    val dummy = writeln "Building new grammar...";

    (*find out which grammar is bigger*)
    val (Gram {nt_count = nt_count1, prod_count = prod_count1, tags = tags1,
               chains = chains1, lambdas = lambdas1, prods = prods1},
         Gram {nt_count = nt_count2, prod_count = prod_count2, tags = tags2,
               chains = chains2, lambdas = lambdas2, prods = prods2}) =
      let val Gram {prod_count = count_a, ...} = gram_a;
          val Gram {prod_count = count_b, ...} = gram_b;
      in if count_a > count_b then (gram_a, gram_b)
                              else (gram_b, gram_a)
      end;

    (*get existing tag from grammar1 or create a new one*)
    fun get_tag nt_count tags nt =
      case Symtab.lookup (tags, nt) of
        Some tag => (nt_count, tags, tag)
      | None => (nt_count+1, Symtab.update_new ((nt, nt_count), tags),
                nt_count)

    val ((nt_count1', tags1'), tag_table) =
      let val tag_list = Symtab.dest tags2;

          val table = Array.array (nt_count2, ~1);

          fun store_tag nt_count tags ~1 = (nt_count, tags)
            | store_tag nt_count tags tag =
              let val (nt_count', tags', tag') =
                   get_tag nt_count tags
                     (fst (the (find_first (fn (n, t) => t = tag) tag_list)));
              in Array.update (table, tag, tag');
                 store_tag nt_count' tags' (tag-1)
              end;
      in (store_tag nt_count1 tags1 (nt_count2-1), table) end;
    
    (*convert grammar2 tag to grammar1 tag*)
    fun convert_tag tag = Array.sub (tag_table, tag);

    (*convert chain list to raw productions*)
    fun mk_chain_prods [] result = result
      | mk_chain_prods ((to, froms) :: cs) result =
        let
          val to_tag = convert_tag to;

          fun make [] result = result
            | make (from :: froms) result = make froms ((to_tag,
                ([Nonterminal (convert_tag from, ~1)], "", ~1)) :: result);
        in mk_chain_prods cs (make froms [] @ result) end;
        
    val chain_prods = mk_chain_prods chains2 [];

    (*convert prods2 array to productions*)
    fun process_nt ~1 result = result
      | process_nt nt result =
        let
          val nt_prods = foldl (op union)
                             ([], map snd (snd (Array.sub (prods2, nt))));
          val lhs_tag = convert_tag nt;

          (*convert tags in rhs*)
          fun process_rhs [] result = result
            | process_rhs (Terminal tk :: rhs) result =
                process_rhs rhs (result @ [Terminal tk])
            | process_rhs (Nonterminal (nt, prec) :: rhs) result =
                process_rhs rhs
                            (result @ [Nonterminal (convert_tag nt, prec)]);

          (*convert tags in productions*)
          fun process_prods [] result = result
            | process_prods ((rhs, id, prec) :: ps) result =
                process_prods ps ((lhs_tag, (process_rhs rhs [], id, prec))
                                  :: result);
        in process_nt (nt-1) (process_prods nt_prods [] @ result) end;

    val raw_prods = chain_prods @ process_nt (nt_count2-1) [];

    val prods1' =
      let fun get_prod i = if i < nt_count1 then Array.sub (prods1, i)
                           else (([], []), []);
      in Array.tabulate (nt_count1', get_prod) end;

    val fromto_chains = inverse_chains chains1 [];

    val (fromto_chains', lambdas', Some prod_count1') =
      add_prods prods1' fromto_chains lambdas1 (Some prod_count1) raw_prods;

    val chains' = inverse_chains fromto_chains' [];
  in Gram {nt_count = nt_count1', prod_count = prod_count1',
           tags = tags1', chains = chains', lambdas = lambdas',
           prods = prods1'}
  end;


(** parse **)

datatype parsetree =
  Node of string * parsetree list |
  Tip of token;

type state =
  nt_tag * int *                (*identification and production precedence*)
  parsetree list *              (*already parsed nonterminals on rhs*)
  symb list *                   (*rest of rhs*)
  string *                      (*name of production*)
  int;                          (*index for previous state list*)


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
fun update_trees ((B, (i, ts)) :: used) (A, t) =
  if A = B then
    let val (n, ts') = conc t ts
    in ((A, (i, ts')) :: used, n) end
  else
    let val (used', n) = update_trees used (A, t)
    in ((B, (i, ts)) :: used', n) end;

(*Replace entry in used*)
fun update_prec (A, prec) used =
  let fun update ((hd as (B, (_, ts))) :: used, used') =
        if A = B
        then used' @ ((A, (prec, ts)) :: used)
        else update (used, hd :: used')
  in update (used, []) end;

fun getS A maxPrec Si =
  filter
    (fn (_, _, _, Nonterminal (B, prec) :: _, _, _)
          => A = B andalso prec <= maxPrec
      | _ => false) Si;

fun getS' A maxPrec minPrec Si =
  filter
    (fn (_, _, _, Nonterminal (B, prec) :: _, _, _)
          => A = B andalso prec > minPrec andalso prec <= maxPrec
      | _ => false) Si;

fun getStates Estate i ii A maxPrec =
  filter
    (fn (_, _, _, Nonterminal (B, prec) :: _, _, _)
          => A = B andalso prec <= maxPrec
      | _ => false)
    (Array.sub (Estate, ii));


fun movedot_term (A, j, ts, Terminal a :: sa, id, i) c =
  if valued_token c then
    (A, j, ts @ [Tip c], sa, id, i)
  else (A, j, ts, sa, id, i);

fun movedot_nonterm ts (A, j, tss, Nonterminal _ :: sa, id, i) =
  (A, j, tss @ ts, sa, id, i);

fun movedot_lambda _ [] = []
  | movedot_lambda (B, j, tss, Nonterminal (A, k) :: sa, id, i) ((t, ki) :: ts) =
      if k <= ki then
        (B, j, tss @ t, sa, id, i) ::
          movedot_lambda (B, j, tss, Nonterminal (A, k) :: sa, id, i) ts
      else movedot_lambda (B, j, tss, Nonterminal (A, k) :: sa, id, i) ts;


val warned = ref false;                            (*flag for warning message*)
val branching_level = ref 200;                   (*trigger value for warnings*)

(*get all productions of a NT and NTs chained to it which can
  be started by specified token*)
fun prods_for prods chains include_none tk nts =
let (*similar to token_assoc but does not automatically include 'None' key*)
    fun token_assoc2 (list, key) =
      let fun assoc [] result = result
            | assoc ((keyi, pi) :: pairs) result =
                if is_some keyi andalso matching_tokens (the keyi, key)
                   orelse include_none andalso is_none keyi then 
                  assoc pairs (pi @ result)
                else assoc pairs result;
      in assoc list [] end;

    fun get_prods [] result = result
      | get_prods (nt :: nts) result =
        let val nt_prods = snd (Array.sub (prods, nt));
        in get_prods nts ((token_assoc2 (nt_prods, tk)) @ result) end;
in get_prods (connected_with chains nts nts) [] end;


fun PROCESSS prods chains Estate i c states =
let
fun all_prods_for nt = prods_for prods chains true c [nt];

fun processS used [] (Si, Sii) = (Si, Sii)
  | processS used (S :: States) (Si, Sii) =
      (case S of
        (_, _, _, Nonterminal (nt, minPrec) :: _, _, _) =>
          let                                       (*predictor operation*)
            val (used', new_states) =
              (case assoc (used, nt) of
                Some (usedPrec, l) =>       (*nonterminal has been processed*)
                  if usedPrec <= minPrec then
                                      (*wanted precedence has been processed*)
                    (used, movedot_lambda S l)
                  else            (*wanted precedence hasn't been parsed yet*)
                    let
                      val tk_prods = all_prods_for nt;
                      
                      val States' = mkStates i minPrec nt
                                      (getRHS' minPrec usedPrec tk_prods);
                    in (update_prec (nt, minPrec) used, 
                        movedot_lambda S l @ States')
                    end

              | None =>           (*nonterminal is parsed for the first time*)
                  let val tk_prods = all_prods_for nt;
                      val States' = mkStates i minPrec nt
                                      (getRHS minPrec tk_prods);
                  in ((nt, (minPrec, [])) :: used, States') end);

            val dummy =
              if not (!warned) andalso
                 length (new_states @ States) > (!branching_level) then
                (writeln "Warning: Currently parsed expression could be \
                         \extremely ambiguous.";
                 warned := true)
              else ();
          in
            processS used' (new_states @ States) (S :: Si, Sii)
          end
      | (_, _, _, Terminal a :: _, _, _) =>               (*scanner operation*)
          processS used States
            (S :: Si,
              if matching_tokens (a, c) then movedot_term S c :: Sii else Sii)
      | (A, prec, ts, [], id, j) =>                   (*completer operation*)
          let val tt = if id = "" then ts else [Node (id, ts)] in
            if j = i then                             (*lambda production?*)
              let
                val (used', O) = update_trees used (A, (tt, prec));
              in
                case O of
                  None =>
                    let val Slist = getS A prec Si;
                        val States' = map (movedot_nonterm tt) Slist;
                    in processS used' (States' @ States) (S :: Si, Sii) end
                | Some n =>
                    if n >= prec then processS used' States (S :: Si, Sii)
                    else
                      let val Slist = getS' A prec n Si;
                          val States' = map (movedot_nonterm tt) Slist;
                      in processS used' (States' @ States) (S :: Si, Sii) end
              end 
            else
              let val Slist = getStates Estate i j A prec
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

fun produce prods chains stateset i indata prev_token =
                                      (*prev_token is used for error messages*)
  (case Array.sub (stateset, i) of
    [] => let fun some_prods_for tk nt = prods_for prods chains false tk [nt];

              (*test if tk is a lookahead for a given minimum precedence*)
              fun reduction _ minPrec _ (Terminal _ :: _, _, prec:int) =
                    if prec >= minPrec then true
                    else false
                | reduction tk minPrec checked 
                            (Nonterminal (nt, nt_prec) :: _, _, prec) =
                  if prec >= minPrec andalso not (nt mem checked) then
                    let val chained = connected_with chains [nt] [nt];
                    in exists
                         (reduction tk nt_prec (chained @ checked))
                         (some_prods_for tk nt)
                    end
                  else false;

              (*compute a list of allowed starting tokens 
                for a list of nonterminals considering precedence*)
              fun get_starts [] result = result
                | get_starts ((nt, minPrec:int) :: nts) result =
                  let fun get [] result = result
                        | get ((Some tk, prods) :: ps) result =
                            if not (null prods) andalso
                               exists (reduction tk minPrec [nt]) prods
                            then get ps (tk :: result)
                            else get ps result
                        | get ((None, _) :: ps) result = get ps result;

                      val (_, nt_prods) = Array.sub (prods, nt);

                      val chained = map (fn nt => (nt, minPrec))
                                        (assocs chains nt);
                  in get_starts (chained @ nts)
                                ((get nt_prods []) union result)
                  end;

              val nts =
                mapfilter (fn (_, _, _, Nonterminal (a, prec) :: _, _, _) => 
                           Some (a, prec) | _ => None)
                          (Array.sub (stateset, i-1));
              val allowed =
                distinct (get_starts nts [] @
                  (mapfilter (fn (_, _, _, Terminal a :: _, _, _) => Some a
                               | _ => None)
                             (Array.sub (stateset, i-1))));
          in syntax_error (if prev_token = EndToken then indata
                           else prev_token :: indata) allowed
          end
  | s =>
    (case indata of
       [] => Array.sub (stateset, i)
     | c :: cs =>
       let val (si, sii) = PROCESSS prods chains stateset i c s;
       in Array.update (stateset, i, si);
          Array.update (stateset, i + 1, sii);
          produce prods chains stateset (i + 1) cs c
       end));


val get_trees = mapfilter (fn (_, _, [pt], _, _, _) => Some pt | _ => None);


fun earley prods tags chains startsymbol indata =
  let
    val start_tag = case Symtab.lookup (tags, startsymbol) of
                       Some tag => tag
                     | None   => error ("parse: Unknown startsymbol " ^ 
                                        quote startsymbol);
    val S0 = [(~1, 0, [], [Nonterminal (start_tag, 0), Terminal EndToken],
               "", 0)];
    val s = length indata + 1;
    val Estate = Array.array (s, []);
  in
    Array.update (Estate, 0, S0);
    warned := false;
    get_trees (produce prods chains Estate 0 indata EndToken)
  end;


fun parse (Gram {tags, prods, chains, ...}) start toks =
let val r =
  (case earley prods tags chains start toks of
    [] => sys_error "parse: no parse trees"
  | pts => pts);
in r end

end;
