(*  Title:      Pure/Syntax/parser.ML
    ID:         $Id$
    Author:     Sonia Mahjoub and Markus Wenzel, TU Muenchen

Isabelle's main parser (used for terms and typs).

TODO:
  ~1 --> chain_pri
  rename T, NT
  improve syntax error
  fix ambiguous grammar problem
*)

signature PARSER =
sig
  structure XGram: XGRAM
  structure ParseTree: PARSE_TREE
  local open XGram ParseTree ParseTree.Lexicon in
    type gram
    val empty_gram: gram
    val extend_gram: gram -> string list -> string prod list -> gram
    val mk_gram: string list -> string prod list -> gram
    val parse: gram -> string -> token list -> parsetree
  end
end;

functor ParserFun(structure Symtab: SYMTAB and XGram: XGRAM
  and ParseTree: PARSE_TREE)(*: PARSER *) =  (* FIXME *)
struct

structure XGram = XGram;
structure ParseTree = ParseTree;
structure Lexicon = ParseTree.Lexicon;
open XGram ParseTree Lexicon;


(** datatype gram **)

datatype symb = T of token | NT of string * int;

datatype gram =
  Gram of string list * (symb list * string * int) list Symtab.table;


(* empty_gram *)

val empty_gram = Gram ([], Symtab.null);


(* extend_gram *)

(*prods are stored in reverse order*)

fun extend_gram (Gram (roots, tab)) new_roots xprods =
  let
    fun symb_of (Terminal s) = Some (T (Token s))
      | symb_of (Nonterminal (s, p)) =
          (case predef_term s of
            EndToken => Some (NT (s, p))
          | tk => Some (T tk))
      | symb_of _ = None;

    fun prod_of (Prod (s, xsyms, c, p)) = (s, mapfilter symb_of xsyms, c, p);

    fun add_prod (tab, (s, syms, c, p)) =
      (case Symtab.lookup (tab, s) of
        None => Symtab.update ((s, [(syms, c, p)]), tab)
      | Some prods => Symtab.update ((s, (syms, c, p) :: prods), tab));
  in
    Gram (new_roots union roots,
      Symtab.balance (foldl add_prod (tab, map prod_of xprods)))
  end;


(* mk_gram *)

val mk_gram = extend_gram empty_gram;


(* get_prods *)

fun get_prods tab s pred =
  let
    fun rfilter [] ys = ys
      | rfilter (x :: xs) ys = rfilter xs (if pred x then x :: ys else ys);
  in
    (case Symtab.lookup (tab, s) of
      Some prods => rfilter prods []
    | None => [])
  end;



(** parse **)

type state =
  string * int
    * parsetree list    (*before point*)
    * symb list         (*after point*)
    * string * int;

type earleystate = state list Array.array;



fun getProductions tab A i =
  get_prods tab A (fn (_, _, j) => j >= i orelse j = ~1);

fun getProductions' tab A i k =
  get_prods tab A (fn (_, _, j) => (j >= i andalso j < k) orelse j = ~1);



fun mkState i jj A ([NT(B,~1)],id,~1) =
                     (A,max_pri,[],[NT (B,jj)],id,i)
  | mkState i jj A (ss,id,j) = (A,j,[],ss,id,i) ;



fun conc (t,(k:int)) [] = (None, [(t,k)])
  | conc (t,k) ((t',k')::ts) =
      if (t = t')
      then (Some k', ( if k' >= k
                       then (t',k')::ts
                       else (t,k)::ts )
           )
      else let val (n, ts') = conc (t,k) ts
           in (n, (t',k')::ts')
           end;


fun update_tree ((B,(i,ts))::used) (A,t) =
      if   (A = B)
      then
          let val (n,ts') = conc t ts
          in  ((A,(i,ts'))::used, n)
          end
      else
          let val (used', n) = update_tree used (A,t)
          in  ((B,(i,ts)) :: used', n)
          end;



fun update_index ((B,(i,ts))::used) (A,j) =
      if   (A = B)
      then (A,(j,ts)) :: used
      else (B,(i,ts)) :: (update_index used (A,j));



fun getS A i Si =
       filter (fn (_,_,_,(NT(B,j))::_,_,_)
                                    => (A=B andalso j<=i)
               |      _             => false
              ) Si;



fun getS' A k n Si =
       filter (fn (_,_,_,(NT(B,j))::_,_,_) => (A=B andalso
                                               j<=k andalso
                                               j>n )
               |      _                    => false
              ) Si;



fun getStates Estate i ii A k =
       filter (fn (_,_,_,(NT(B,j))::_,_,_)
                                    => (A=B andalso j<=k)
               |      _             => false
              )
              (Array.sub (Estate, ii))
;



(* MMW *)(* FIXME *)
fun movedot_term (A,j,ts,T a::sa,id,i) c =
                   if (valued_token c)
                   then (A,j,(ts@[Tip c]),sa,id,i)
                   else (A,j,ts,sa,id,i) ;



fun movedot_nonterm ts  (A,j,tss,NT(B,k) ::sa,id,i) =
                         (A,j,tss@ts,sa,id,i) ;



fun movedot_lambda  _  [] = []
  | movedot_lambda (B,j,tss,(NT(A,k))::sa,id,i) ((t,ki)::ts) =
    if k <= ki
    then (B,j,tss@t,sa,id,i) ::
         (movedot_lambda (B,j,tss,(NT(A,k))::sa,id,i) ts)
    else movedot_lambda (B,j,tss,(NT(A,k))::sa,id,i) ts
  ;




fun PROCESSS Estate grammar i c states =

let
fun processS used [] (Si,Sii) = (Si,Sii)
 |  processS used (S::States) (Si,Sii) =
     ( case S of

        (_,_,_,(NT (A,j))::_,_,_)  =>
          let
            val (used_neu, States_neu) =
              ( case assoc (used, A) of
                 Some (k,l) =>         (* A gehoert zu used *)

                   if (k <= j)          (* Prioritaet wurde
                                           behandelt  *)
                   then
                        (used, movedot_lambda S l)

                   else         (* Prioritaet wurde noch nicht
                                        behandelt  *)
                        let val L =
                                getProductions' grammar A j k
                            val States' = map (mkState i j A) L
                        in
                            (update_index used (A,j),
                             States'@ movedot_lambda S l
                            )
                        end

                | None =>       (* A gehoert nicht zu used *)
                      let val L = getProductions grammar A j
                          val States' = map (mkState i j A) L
                      in
                          ((A,(j,[]))::used, States')
                      end
              )
          in
             processS used_neu (States @ States_neu) (S::Si,Sii)
          end

     |  (_,_,_,(T a)::_,_,_)  =>
                processS used States
                    (S::Si, if (matching_tokens (a, c))
                            then  (movedot_term S c)::Sii   (* MMW *)(* FIXME *)
                            else Sii
                    )


     |  (A,k,ts,[],id,j) =>
          let val tt = if id = ""
                       then ts
                       else [Node(id,ts)]
          in
             if (j = i)
             then
                let val (used',O) = update_tree used (A,(tt,k))
                in ( case O of
                      None =>
                         let val Slist = getS A k Si
                             val States' =
                              map (movedot_nonterm tt ) Slist
                         in  processS used'
                             (States @ States') (S::Si,Sii)
                         end
                   |  Some n =>
                         if (n >= k)
                         then
                            processS used' States (S::Si,Sii)
                         else
                            let val Slist = getS' A k n Si
                                val States' =
                              map (movedot_nonterm tt ) Slist
                            in
                              processS used'
                              (States @ States') (S::Si,Sii)
                            end
                   )
                end

              else
                processS used (States @
                               map (movedot_nonterm tt)
                               (getStates Estate i j A k))
                (S::Si,Sii)
           end
     )
in
   processS [] states ([],[])
end;



fun syntax_error toks =
  error ("Syntax error at: " ^ space_implode " " (map str_of_token toks));

fun Produce grammar stateset i indata =
      case (Array.sub (stateset,i)) of
         [] => syntax_error indata (* MMW *)(* FIXME *)
      |  s  =>
           (case indata of
                []  => Array.sub (stateset,i)
             |  (c::cs) =>
                       let val (si,sii) =
                           PROCESSS stateset grammar i c s
                       in
                           Array.update (stateset,i,si);
                           Array.update (stateset,i+1,sii);
                           Produce grammar stateset (i+1) cs
                       end
           );


fun get_trees [] = []
  | get_trees ((_,_,pt_lst,_,_,_) :: stateset) =
       let val l = get_trees stateset
       in case pt_lst of
            [ptree] => ptree :: l
          |   _     => l
       end;



fun earley grammar startsymbol indata =
   let  val S0 =
       [("S'",0,[],[NT (startsymbol,0), T EndToken],"",0)]
        val s = length indata + 1     (* MMW *)(* FIXME was .. + 2 *)
        val Estate = Array.array (s, [])
   in   Array.update (Estate,0,S0);
        let val l = Produce grammar Estate 0 indata    (* MMW *)(* FIXME was .. @ [EndToken] *)
            val p_trees = get_trees l
        in p_trees
        end
   end;


(* FIXME demo *)
fun parse (Gram (roots, prod_tab)) root toks =
  if root mem roots then
    (case earley prod_tab root toks of
      [] => error "parse: no parse trees"
    | pt :: _ => pt)
  else error ("Unparsable category: " ^ root);


end;

