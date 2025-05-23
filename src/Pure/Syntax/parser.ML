(*  Title:      Pure/Syntax/parser.ML
    Author:     Carsten Clasohm, Sonia Mahjoub
    Author:     Makarius

General context-free parser for the inner syntax of terms and types.
*)

signature PARSER =
sig
  type gram
  val empty_gram: gram
  val make_gram: Syntax_Ext.xprod list -> Syntax_Ext.xprod list -> gram option -> gram
  val pretty_gram: gram -> Pretty.T list
  datatype tree =
    Markup of {markup: Markup.T list, range: Position.range} * tree list |
    Node of {nonterm: string, const: string, range: Position.range} * tree list |
    Tip of Lexicon.token
  val pretty_tree: tree -> Pretty.T list
  val parse: gram -> string -> Lexicon.token list -> tree list
end;

structure Parser: PARSER =
struct

(** datatype gram **)

(* nonterminals *)

(*production for the NTs are stored in a vector, indexed by the NT tag*)
type nt = int;

type tags = nt Symtab.table;
val tags_empty: tags = Symtab.empty;
fun tags_size (tags: tags) = Symtab.size tags;
fun tags_content (tags: tags) = sort_by #1 (Symtab.dest tags);
fun tags_lookup (tags: tags) = Symtab.lookup tags;
fun tags_insert tag (tags: tags) = Symtab.update_new tag tags;

type names = string Inttab.table;
val names_empty: names = Inttab.empty;
fun make_names (tags: tags): names = Inttab.build (Symtab.fold (Inttab.update_new o swap) tags);
fun the_name (names: names) = the o Inttab.lookup names;

type nts = Bitset.T;
val nts_empty: nts = Bitset.empty;
val nts_merge: nts * nts -> nts = Bitset.merge;
fun nts_insert nt : nts -> nts = Bitset.insert nt;
fun nts_member (nts: nts) = Bitset.member nts;
fun nts_fold f (nts: nts) = Bitset.fold f nts;
fun nts_subset (nts1: nts, nts2: nts) = Bitset.forall (nts_member nts2) nts1;
fun nts_is_empty (nts: nts) = Bitset.is_empty nts;
fun nts_is_unique (nts: nts) = Bitset.is_unique nts;


(* tokens *)

structure Tokens = Set(type key = Lexicon.token val ord = Lexicon.token_type_ord);

fun tokens_find P tokens = Tokens.get_first (fn tok => if P tok then SOME tok else NONE) tokens;
fun tokens_add (nt: nt, tokens) = if Tokens.is_empty tokens then I else cons (nt, tokens);


(* productions *)

datatype symb =
  Terminal of Lexicon.token |
  Nonterminal of nt * int |  (*(tag, precedence)*)
  Bg of Markup.T list | En;  (*markup block*)

type prod = symb list * string * int;  (*rhs, name, precedence*)

fun make_chain_prod from : prod = ([Nonterminal (from, ~1)], "", ~1);

fun dest_chain_prod (([Nonterminal (from, ~1)], _, ~1): prod) = SOME from
  | dest_chain_prod _ = NONE;

val no_prec = ~1;

fun upto_prec min max p =
  (min = no_prec orelse p >= min) andalso (max = no_prec orelse p <= max);

fun until_prec min max p =
  (min = no_prec orelse p >= min) andalso (max = no_prec orelse p < max);


structure Prods = Table(Tokens.Key);
type prods = prod list Prods.table;

val prods_empty: prods = Prods.empty;
fun prods_lookup (prods: prods) = Prods.lookup_list prods;
fun prods_update entry : prods -> prods = Prods.update entry;
fun prods_content (prods: prods) = distinct (op =) (maps #2 (Prods.dest prods));

type nt_gram = (nts * Tokens.T) * prods; (*dependent_nts, start_tokens, prods*)
  (*depent_nts is a set of all NTs whose lookahead depends on this NT's lookahead*)

val nt_gram_empty: nt_gram = ((nts_empty, Tokens.empty), prods_empty);

type chains = unit Int_Graph.T;
fun chains_preds (chains: chains) = Int_Graph.immediate_preds chains;
fun chains_all_preds (chains: chains) = Int_Graph.all_preds chains;
fun chains_all_succs (chains: chains) = Int_Graph.all_succs chains;
val chains_empty: chains = Int_Graph.empty;
fun chains_member (chains: chains) = Int_Graph.is_edge chains;
fun chains_declare nt : chains -> chains = Int_Graph.default_node (nt, ());

fun chains_declares (Nonterminal (nt, _)) = chains_declare nt
  | chains_declares _ = I;

fun chains_insert (from, to) =
  chains_declare from #> chains_declare to #> Int_Graph.add_edge (from, to);

datatype gram =
  Gram of
   {tags: tags,
    names: names,
    chains: chains,
    lambdas: nts,
    prods: nt_gram Vector.vector};
    (*"tags" is used to map NT names (i.e. strings) to tags;
     chain productions are not stored as normal productions
     but instead as an entry in "chains": from -> to;
     lambda productions are stored as normal productions
     and also as an entry in "lambdas"*)

(*productions for which no starting token is
  known yet are associated with this token*)
val unknown_start = Lexicon.eof;

fun get_start tks =
  (case Tokens.min tks of
    SOME tk => tk
  | NONE => unknown_start);

fun add_production array_prods (lhs, new_prod as (rhs, _, _) : prod) (chains, lambdas) =
  let
    val chain = dest_chain_prod new_prod;
    val (new_chain, chains') =
      (case chain of
        SOME from =>
          if chains_member chains (from, lhs)
          then (false, chains)
          else (true, chains_insert (from, lhs) chains)
      | NONE => (false, chains |> chains_declare lhs |> fold chains_declares rhs));

    (*propagate new chain in lookahead and lambdas;
      added_starts is used later to associate existing
      productions with new starting tokens*)
    val (added_starts, lambdas') =
      if not new_chain then ([], lambdas)
      else
        let (*lookahead of chain's source*)
          val ((_, from_tks), _) = Array.nth array_prods (the chain);

          (*copy from's lookahead to chain's destinations*)
          fun copy_lookahead to =
            let
              val ((to_nts, to_tks), ps) = Array.nth array_prods to;

              val new_tks = Tokens.subtract to_tks from_tks;  (*added lookahead tokens*)
              val to_tks' = Tokens.merge (to_tks, new_tks);
              val _ = Array.upd array_prods to ((to_nts, to_tks'), ps);
            in tokens_add (to, new_tks) end;

          val tos = chains_all_succs chains' [lhs];
        in
          (fold copy_lookahead tos [],
            lambdas |> nts_member lambdas lhs ? fold nts_insert tos)
        end;

    (*test if new production can produce lambda
      (rhs must either be empty or only consist of lambda NTs)*)
    fun lambda_symb (Nonterminal (id, _)) = nts_member lambdas' id
      | lambda_symb (Terminal _) = false
      | lambda_symb _ = true;
    val new_lambdas =
      if forall lambda_symb rhs
      then SOME (filter_out (nts_member lambdas') (chains_all_succs chains' [lhs]))
      else NONE;
    val lambdas'' = fold nts_insert (these new_lambdas) lambdas';

    (*list optional terminal and all nonterminals on which the lookahead
      of a production depends*)
    fun lookahead_dependency _ [] nts = (NONE, nts)
      | lookahead_dependency _ (Terminal tk :: _) nts = (SOME tk, nts)
      | lookahead_dependency lambdas (Nonterminal (nt, _) :: symbs) nts =
          if nts_member lambdas nt then
            lookahead_dependency lambdas symbs (nts_insert nt nts)
          else (NONE, nts_insert nt nts)
      | lookahead_dependency lambdas (_ :: symbs) nts = lookahead_dependency lambdas symbs nts;

    (*get all known starting tokens for a nonterminal*)
    fun starts_for_nt nt = snd (fst (Array.nth array_prods nt));

    (*update prods, lookaheads, and lambdas according to new lambda NTs*)
    val (added_starts', lambdas') =
      let
        (*propagate added lambda NT*)
        fun propagate_lambda [] added_starts lambdas = (added_starts, lambdas)
          | propagate_lambda (l :: ls) added_starts lambdas =
              let
                (*get lookahead for lambda NT*)
                val ((dependent, l_starts), _) = Array.nth array_prods l;

                (*check productions whose lookahead may depend on lambda NT*)
                fun examine_prods [] add_lambda nt_dependencies added_tks nt_prods =
                      (add_lambda, nt_dependencies, added_tks, nt_prods)
                  | examine_prods ((p as (rhs, _, _)) :: ps) add_lambda
                        nt_dependencies added_tks nt_prods =
                      let val (tk, nts) = lookahead_dependency lambdas rhs nts_empty in
                        if nts_member nts l then       (*update production's lookahead*)
                          let
                            val new_lambda =
                              is_none tk andalso nts_subset (nts, lambdas);

                            val new_tks =
                              Tokens.empty
                              |> fold Tokens.insert (the_list tk)
                              |> nts_fold (curry Tokens.merge o starts_for_nt) nts
                              |> Tokens.subtract l_starts;

                            val added_tks' = Tokens.merge (added_tks, new_tks);

                            val nt_dependencies' = nts_merge (nt_dependencies, nts);

                            (*associate production with new starting tokens*)
                            fun copy tk nt_prods =
                              prods_update (tk, p :: prods_lookup nt_prods tk) nt_prods;

                            val nt_prods' = nt_prods
                              |> Tokens.fold copy new_tks
                              |> new_lambda ? copy Lexicon.dummy;
                          in
                            examine_prods ps (add_lambda orelse new_lambda)
                              nt_dependencies' added_tks' nt_prods'
                          end
                        else (*skip production*)
                          examine_prods ps add_lambda nt_dependencies added_tks nt_prods
                      end;

                (*check each NT whose lookahead depends on new lambda NT*)
                fun process_nts nt (added_lambdas, added_starts) =
                  let
                    val ((old_nts, old_tks), nt_prods) = Array.nth array_prods nt;

                    (*existing productions whose lookahead may depend on l*)
                    val tk_prods = prods_lookup nt_prods (get_start l_starts);

                    (*add_lambda is true if an existing production of the nt
                      produces lambda due to the new lambda NT l*)
                    val (add_lambda, nt_dependencies, added_tks, nt_prods') =
                      examine_prods tk_prods false nts_empty Tokens.empty nt_prods;

                    val new_nts = nts_merge (old_nts, nt_dependencies);
                    val new_tks = Tokens.merge (old_tks, added_tks);

                    val added_lambdas' = added_lambdas |> add_lambda ? cons nt;
                    val _ = Array.upd array_prods nt ((new_nts, new_tks), nt_prods');
                      (*N.B. that because the tks component
                        is used to access existing
                        productions we have to add new
                        tokens at the _end_ of the list*)
                    val added_starts' = tokens_add (nt, added_tks) added_starts;
                  in (added_lambdas', added_starts') end;

                val (added_lambdas, added_starts') =
                  nts_fold process_nts dependent ([], added_starts);
                val added_lambdas' = filter_out (nts_member lambdas) added_lambdas;
              in
                propagate_lambda (ls @ added_lambdas') added_starts'
                  (fold nts_insert added_lambdas' lambdas)
              end;
      in
        propagate_lambda
          (nts_fold (fn l => not (nts_member lambdas l) ? cons l) lambdas'' [])
          added_starts lambdas''
      end;

    (*insert production into grammar*)
    val added_starts' =
      if is_some chain then added_starts'  (*don't store chain production*)
      else
        let
          (*lookahead tokens of new production and on which
            NTs lookahead depends*)
          val (start_tk, start_nts) = lookahead_dependency lambdas' rhs nts_empty;

          val start_tks =
            Tokens.empty
            |> fold Tokens.insert (the_list start_tk)
            |> nts_fold (curry Tokens.merge o starts_for_nt) start_nts;

          val start_tks' =
            start_tks
            |> (if is_some new_lambdas then Tokens.insert Lexicon.dummy
                else if Tokens.is_empty start_tks then Tokens.insert unknown_start
                else I);

          (*add lhs NT to list of dependent NTs in lookahead*)
          fun add_nts nt initial =
            (if initial then
              let val ((old_nts, old_tks), ps) = Array.nth array_prods nt in
                if nts_member old_nts lhs then ()
                else Array.upd array_prods nt ((nts_insert lhs old_nts, old_tks), ps)
              end
             else (); false);

          (*add new start tokens to chained NTs' lookahead list;
            also store new production for lhs NT*)
          fun add_tks [] added = added
            | add_tks (nt :: nts) added =
                let
                  val ((old_nts, old_tks), nt_prods) = Array.nth array_prods nt;

                  val new_tks = Tokens.subtract old_tks start_tks;

                  (*store new production*)
                  fun store tk (prods, _) =
                    let
                      val tk_prods = prods_lookup prods tk;
                      val tk_prods' = new_prod :: tk_prods;
                      val prods' = prods_update (tk, tk_prods') prods;
                    in (prods', true) end;

                  val (nt_prods', changed) = (nt_prods, false)
                    |> nt = lhs ? Tokens.fold store start_tks';
                  val _ =
                    if not changed andalso Tokens.is_empty new_tks then ()
                    else Array.upd array_prods nt ((old_nts, Tokens.merge (old_tks, new_tks)), nt_prods');
                in add_tks nts (tokens_add (nt, new_tks) added) end;
          val _ = nts_fold add_nts start_nts true;
        in add_tks (chains_all_succs chains' [lhs]) [] end;

    (*associate productions with new lookaheads*)
    val _ =
      let
        (*propagate added start tokens*)
        fun add_starts [] = ()
          | add_starts ((changed_nt, new_tks) :: starts) =
              let
                (*token under which old productions which
                  depend on changed_nt could be stored*)
                val key =
                  tokens_find (not o Tokens.member new_tks) (starts_for_nt changed_nt)
                  |> the_default unknown_start;

                (*copy productions whose lookahead depends on changed_nt;
                  if key = SOME unknown_start then tk_prods is used to hold
                  the productions not copied*)
                fun update_prods [] result = result
                  | update_prods ((p as (rhs, _: string, _: nt)) :: ps)
                        (tk_prods, nt_prods) =
                      let
                        (*lookahead dependency for production*)
                        val (tk, depends) = lookahead_dependency lambdas' rhs nts_empty;

                        (*test if this production has to be copied*)
                        val update = nts_member depends changed_nt;

                        (*test if production could already be associated with
                          a member of new_tks*)
                        val lambda =
                          not (nts_is_unique depends) orelse
                          not (nts_is_empty depends) andalso is_some tk
                          andalso Tokens.member new_tks (the tk);

                        (*associate production with new starting tokens*)
                        fun copy tk nt_prods =
                          let
                            val tk_prods = prods_lookup nt_prods tk;
                            val tk_prods' =
                              if not lambda then p :: tk_prods
                              else insert (op =) p tk_prods;
                               (*if production depends on lambda NT we
                                 have to look for duplicates*)
                          in prods_update (tk, tk_prods') nt_prods end;
                        val result =
                          if update then (tk_prods, Tokens.fold copy new_tks nt_prods)
                          else if key = unknown_start then (p :: tk_prods, nt_prods)
                          else (tk_prods, nt_prods);
                      in update_prods ps result end;

                (*copy existing productions for new starting tokens*)
                fun process_nts nt =
                  let
                    val ((nts, tks), nt_prods) = Array.nth array_prods nt;

                    val tk_prods = prods_lookup nt_prods key;

                    (*associate productions with new lookahead tokens*)
                    val (tk_prods', nt_prods') = update_prods tk_prods ([], nt_prods);

                    val nt_prods'' =
                      if key = unknown_start then
                        prods_update (key, tk_prods') nt_prods'
                      else nt_prods';

                    val added_tks = Tokens.subtract tks new_tks;
                    val tks' = Tokens.merge (tks, added_tks);
                    val _ = Array.upd array_prods nt ((nts, tks'), nt_prods'');
                  in tokens_add (nt, added_tks) end;

                val ((dependent, _), _) = Array.nth array_prods changed_nt;
              in add_starts (starts @ nts_fold process_nts dependent []) end;
      in add_starts added_starts' end;
  in (chains', lambdas') end;


(* pretty_gram *)

fun pretty_gram (Gram {tags, names, prods, chains, ...}) =
  let
    val print_nt = the_name names;
    fun print_pri p = if p < 0 then "" else Symbol.make_sup ("(" ^ string_of_int p ^ ")");

    fun pretty_symb (Terminal tok) =
          if Lexicon.is_literal tok
          then [Pretty.quote (Pretty.keyword1 (Lexicon.str_of_token tok))]
          else [Pretty.str (Lexicon.str_of_token tok)]
      | pretty_symb (Nonterminal (tag, p)) = [Pretty.str (print_nt tag ^ print_pri p)]
      | pretty_symb _ = [];

    fun pretty_const "" = []
      | pretty_const c = [Pretty.str ("\<^bold>\<Rightarrow> " ^ quote c)];

    fun pretty_prod (name, tag) =
      (prods_content (#2 (Vector.nth prods tag)) @ map make_chain_prod (chains_preds chains tag))
      |> map (fn (symbs, const, p) =>
          Pretty.block (Pretty.breaks
            (Pretty.str (name ^ print_pri p ^ " =") :: maps pretty_symb symbs @ pretty_const const)));
  in maps pretty_prod (tags_content tags) end;



(** operations on grammars **)

val empty_gram =
  Gram
   {tags = tags_empty,
    names = names_empty,
    chains = chains_empty,
    lambdas = nts_empty,
    prods = Vector.fromList [nt_gram_empty]};

local

fun make_tag s tags =
  (case tags_lookup tags s of
    SOME tag => (tag, tags)
  | NONE =>
      let val tag = tags_size tags
      in (tag, tags_insert (s, tag) tags) end);

fun make_arg (s, p) tags =
  (case Lexicon.get_terminal s of
    NONE =>
      let val (tag, tags') = make_tag s tags;
      in (Nonterminal (tag, p), tags') end
  | SOME tok => (Terminal tok, tags));

fun extend_gram xprods gram =
  let
    fun make_symb (Syntax_Ext.Delim s) (syms, tags) =
          (Terminal (Lexicon.literal s) :: syms, tags)
      | make_symb (Syntax_Ext.Argument a) (syms, tags) =
          let val (arg, tags') = make_arg a tags
          in (arg :: syms, tags') end
      | make_symb (Syntax_Ext.Bg {markup, ...}) (syms, tags) = (Bg markup :: syms, tags)
      | make_symb (Syntax_Ext.En) (syms, tags) = (En :: syms, tags)
      | make_symb _ res = res;

    fun make_prod (Syntax_Ext.XProd (lhs, xsymbs, const, pri)) (result, tags) =
      let
        val (tag, tags') = make_tag lhs tags;
        val (rev_symbs, tags'') = fold make_symb xsymbs ([], tags');
      in ((tag, (rev rev_symbs, const, pri)) :: result, tags'') end;


    val Gram {tags, names = _, chains, lambdas, prods} = gram;

    val (new_prods, tags') = fold make_prod xprods ([], tags);

    val array_prods' =
      Array.tabulate (tags_size tags', fn i =>
        if i < Vector.length prods then Vector.nth prods i
        else nt_gram_empty);

    val (chains', lambdas') =
      (chains, lambdas) |> fold (add_production array_prods') new_prods;
  in
    Gram
     {tags = tags',
      names = make_names tags',
      chains = chains',
      lambdas = lambdas',
      prods = Array.vector array_prods'}
  end;

in

fun make_gram [] _ (SOME gram) = gram
  | make_gram new_xprods _ (SOME gram) = extend_gram new_xprods gram
  | make_gram [] [] NONE = empty_gram
  | make_gram new_xprods old_xprods NONE = extend_gram (new_xprods @ old_xprods) empty_gram;

end;



(** parser **)

(* parse tree *)

datatype tree =
  Markup of {markup: Markup.T list, range: Position.range} * tree list |
  Node of {nonterm: string, const: string, range: Position.range} * tree list |
  Tip of Lexicon.token;

fun tree_range (Markup ({range, ...}, _)) = range
  | tree_range (Node ({range, ...}, _)) = range
  | tree_range (Tip tok) = Lexicon.range_of_token tok;

fun trees_range trees =
  let
    fun first_pos [] = NONE
      | first_pos (t :: rest) =
          let val pos = #1 (tree_range t)
          in if pos = Position.none then first_pos rest else SOME pos end;

    fun last_pos [] res = res
      | last_pos (t :: rest) res =
          let
            val end_pos = #2 (tree_range t);
            val res' = if end_pos = Position.none then res else SOME end_pos;
          in last_pos rest res' end;
  in
    (case first_pos trees of
      NONE => Position.no_range
    | SOME pos =>
        (case last_pos trees NONE of
          NONE => Position.no_range
        | SOME end_pos => Position.range (pos, end_pos)))
  end;

fun pretty_tree (Markup (_, ts)) = maps pretty_tree ts
  | pretty_tree (Node ({nonterm = nt, const = c, ...}, ts)) =
      let
        fun mark_const body =
          if c = "" then body
          else [Pretty.enclose "(" ")" (Pretty.breaks (Pretty.quote (Pretty.str c) :: body))];
        fun mark_nonterm body =
          if nt = "" then body
          else [Pretty.markup_open (Markup.name nt Markup_Kind.markup_syntax) body];
      in mark_nonterm (mark_const (maps pretty_tree ts))  end
  | pretty_tree (Tip tok) =
      if Lexicon.valued_token tok then [Pretty.str (Lexicon.str_of_token tok)] else [];


(* tree_op: bottom-up construction of markup *)

datatype tree_op =
  Markup_Push |
  Markup_Pop of Markup.T list |
  Node_Op of {nonterm: int, const: string} * tree_op list |
  Tip_Op of Lexicon.token;

local
  fun drop_markup (Markup_Push :: ts) = drop_markup ts
    | drop_markup (Markup_Pop _ :: ts) = drop_markup ts
    | drop_markup ts = ts;
in
  fun tree_ops_ord arg =
    if pointer_eq arg then EQUAL
    else
      (case apply2 drop_markup arg of
        (Node_Op ({nonterm = nt, ...}, ts) :: rest, Node_Op ({nonterm = nt', ...}, ts') :: rest') =>
          (case int_ord (nt, nt') of
            EQUAL =>
              (case tree_ops_ord (ts, ts') of
                EQUAL => tree_ops_ord (rest, rest')
              | ord => ord)
          | ord => ord)
      | (Tip_Op t :: rest, Tip_Op t' :: rest') =>
          (case Lexicon.token_content_ord (t, t') of
            EQUAL => tree_ops_ord (rest, rest')
          | ord => ord)
      | (Node_Op _ :: _, Tip_Op _ :: _) => LESS
      | (Tip_Op _ :: _, Node_Op _ :: _) => GREATER
      | ([], []) => EQUAL
      | ([], _ :: _) => LESS
      | (_ :: _, []) => GREATER
      | _ => raise Match);
end;

fun make_tree names root tree_ops =
  let
    fun top [] = []
      | top (xs :: _) = xs;

    fun pop [] = []
      | pop (_ :: xs) = xs;

    fun make_markup markup ts =
      Markup ({markup = markup, range = trees_range ts}, ts);

    fun make_node {nonterm = nt, const} ts =
      Node ({nonterm = the_name names nt, const = const, range = trees_range ts}, ts);

    fun make body stack ops =
      (case ops of
        Markup_Push :: rest => make [] (body :: stack) rest
      | Markup_Pop markup :: rest => make (make_markup markup body :: top stack) (pop stack) rest
      | Node_Op (name, ts) :: rest => make (make_node name (make [] [] ts) :: body) stack rest
      | Tip_Op tok :: rest => make (Tip tok :: body) stack rest
      | [] => if null stack then body else raise Fail "Pending markup blocks");
  in make_node {nonterm = root, const = ""} (make [] [] tree_ops) end;


(* output *)

abstype output = Output of int * tree_op list
with

val empty_output = Output (0, []);

fun token_output tok (Output (n, ts)) = Output (n + 1, Tip_Op tok :: ts);
fun node_output id (Output (n, ts)) = Output (n, [Node_Op (id, ts)]);

fun push_output (Output (n, ts)) = Output (n, Markup_Push :: ts);
fun pop_output markup (Output (n, ts)) = Output (n, Markup_Pop markup :: ts);

fun append_output (Output (m, ss)) (Output (n, ts)) = Output (m + n, ss @ ts);

val output_ord =
  pointer_eq_ord (fn (Output (m, ss), Output (n, tt)) =>
    (case int_ord (m, n) of EQUAL => tree_ops_ord (ss, tt) | ord => ord));

fun output_tree names root (Output (_, ts)) = make_tree names root ts;

end;

structure Output = Table(type key = output val ord = output_ord);


(* parse *)

type state =
  (nt * int *       (*identification and production precedence*)
   string *         (*name of production*)
   int) *           (*index for previous state list*)
  symb list *       (*remaining input -- after "dot"*)
  output;           (*accepted output -- before "dot"*)

local

fun update_output (A, (out, p)) used =
  let
    val (i: int, output) = the (Inttab.lookup used A);
    fun update output' = Inttab.update (A, (i, output'));
  in
    (case Output.lookup output out of
      NONE => (no_prec, update (Output.make [(out, p)]) used)
    | SOME q => (q, if p > q then update (Output.update (out, p) output) used else used))
  end;

val init_prec = (no_prec, Output.empty);

fun update_prec (A, p) used =
  Inttab.map_default (A, init_prec) (fn (_, output) => (p, output)) used;

fun movedot_states out' A min max = build o fold
  (fn ((info, Nonterminal (B, p) :: sa, out): state) =>
      if A = B andalso upto_prec min max p then cons (info, sa, append_output out' out)
      else I
    | _ => I);

fun process_states (Gram {prods = gram_prods, chains = gram_chains, ...}) stateset i c states0 =
  let
    val get = Array.nth stateset;
    val set = Array.upd stateset;

    fun add_prods nt min max : state list -> state list =
      let
        fun add (rhs, id, prod_prec) =
          if until_prec min max prod_prec
          then cons ((nt, prod_prec, id, i), rhs, empty_output)
          else I;
        fun token_prods prods =
          fold add (prods_lookup prods c) #>
          fold add (prods_lookup prods Lexicon.dummy);
        val nt_prods = #2 o Vector.nth gram_prods;
      in fold (token_prods o nt_prods) (chains_all_preds gram_chains [nt]) end;

    fun process _ [] (Si, Sii) = (Si, Sii)
      | process used ((S as (info, symbs, out)) :: states) (Si, Sii) =
          (case symbs of
            Nonterminal (nt, min_prec) :: sa =>
              let (*predictor operation*)
                fun movedot_lambda (out', k) =
                  if min_prec <= k then cons (info, sa, append_output out' out) else I;
                val (used', states', used_trees) =
                  (case Inttab.lookup used nt of
                    SOME (used_prec, used_trees) =>
                      if used_prec <= min_prec then (used, states, used_trees)
                      else
                        let
                          val used' = update_prec (nt, min_prec) used;
                          val states' = states |> add_prods nt min_prec used_prec;
                        in (used', states', used_trees) end
                  | NONE =>
                      let
                        val used' = update_prec (nt, min_prec) used;
                        val states' = states |> add_prods nt min_prec no_prec;
                      in (used', states', Output.empty) end);
                val states'' = states' |> Output.fold movedot_lambda used_trees;
              in process used' states'' (S :: Si, Sii) end
          | Terminal a :: sa => (*scanner operation*)
              let
                val Sii' =
                  if is_equal (Lexicon.token_type_ord (a, c))
                  then (*move dot*) (info, sa, token_output c out) :: Sii else Sii;
              in process used states (S :: Si, Sii') end
          | Bg markup :: sa => process used ((info, sa, pop_output markup out) :: states) (Si, Sii)
          | En :: sa => process used ((info, sa, push_output out) :: states) (Si, Sii)
          | [] => (*completer operation*)
              let
                val (A, p, id, j) = info;
                val out' = node_output {nonterm = A, const = id} out;
                val (used', states') =
                  if j = i then (*lambda production?*)
                    let val (q, used') = update_output (A, (out', p)) used
                    in (used', movedot_states out' A q p Si) end
                  else (used, movedot_states out' A no_prec p (get j));
              in process used' (states' @ states) (S :: Si, Sii) end)

    val (Si, Sii) = process Inttab.empty states0 ([], []);
  in set i Si; set (i + 1) Sii end;

fun produce gram stateset i prev rest =
  (case Array.nth stateset i of
    [] =>
      let
        val inp = if Lexicon.is_dummy prev then rest else prev :: rest;
        val pos = Position.here (Lexicon.pos_of_token prev);
      in
        if null inp then
          error ("Inner syntax error: unexpected end of input" ^ pos)
        else
          error ("Inner syntax error" ^ pos ^
            Markup.markup Markup.no_report
              ("\n" ^ Pretty.string_of
                (Pretty.block [
                  Pretty.str "at", Pretty.brk 1,
                  Pretty.block
                   (Pretty.str "\"" ::
                    Pretty.breaks (map (Pretty.str o Lexicon.str_of_token) (#1 (split_last inp))) @
                    [Pretty.str "\""])])))
      end
  | states =>
      (case rest of
        [] => states
      | c :: cs => (process_states gram stateset i c states; produce gram stateset (i + 1) c cs)));

in

fun parse (gram as Gram {tags, names, ...}) root_name toks =
  let
    val root =
      (case tags_lookup tags root_name of
        SOME tag => tag
      | NONE => error ("Inner syntax: bad grammar root symbol " ^ quote root_name));

    val end_pos =
      (case try List.last toks of
        NONE => Position.none
      | SOME tok => Lexicon.end_pos_of_token tok);
    val input = toks @ [Lexicon.mk_eof end_pos];

    val S0: state = ((~1, 0, "", 0), [Nonterminal (root, 0), Terminal Lexicon.eof], empty_output);
    val stateset = Array.array (length input + 1, []);
    val _ = Array.upd stateset 0 [S0];

    val result =
      produce gram stateset 0 Lexicon.dummy input
      |> map (output_tree names root o #3);
  in if null result then raise Fail "Inner syntax: no parse trees" else result end;

end;

end;
