(*  Title:      Pure/Syntax/earley0A.ML
    ID:         $Id$
    Author:     Tobias Nipkow

WARNING: This file is about to disappear.
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

functor EarleyFun(structure Symtab: SYMTAB and Lexicon: LEXICON
  and SynExt: SYN_EXT)(*: PARSER *) =  (* FIXME *)
struct

structure Pretty = SynExt.Ast.Pretty;
structure Lexicon = Lexicon;
structure SynExt = SynExt;
open Lexicon;


(** datatype parsetree **)

datatype parsetree =
  Node of string * parsetree list |
  Tip of token;

fun mk_pt ("", [pt]) = pt
  | mk_pt ("", _) = sys_error "mk_pt: funny copy op in parse tree"
  | mk_pt (s, ptl) = Node (s, ptl);



(** token maps (from lexicon.ML) **)

type 'b TokenMap = (token * 'b list) list * 'b list;
val first_token = 0;

fun int_of_token(Token(tk)) = first_token |
    int_of_token(IdentSy _) = first_token - 1 |
    int_of_token(VarSy _) = first_token - 2 |
    int_of_token(TFreeSy _) = first_token - 3 |
    int_of_token(TVarSy _) = first_token - 4 |
    int_of_token(EndToken) = first_token - 5;

fun lesstk(s, t) = int_of_token(s) < int_of_token(t) orelse
                  (case (s, t) of (Token(a), Token(b)) => a<b | _ => false);

fun mkTokenMap(atll) =
    let val aill = atll;
        val dom = sort lesstk (distinct(flat(map snd aill)));
        val mt = map fst (filter (null o snd) atll);
        fun mktm(i) =
            let fun add(l, (a, il)) = if i mem il then a::l else l
            in (i, foldl add ([], aill)) end;
    in (map mktm dom, mt) end;

fun find_al (i) =
    let fun find((j, al)::l) = if lesstk(i, j) then [] else
                              if matching_tokens(i, j) then al else find l |
            find [] = [];
    in find end;
fun applyTokenMap((l, mt), tk:token) = mt@(find_al tk l);



(* Linked lists: *)
infix 5 &;
datatype 'a LList = nilL | op & of 'a * ('a LListR)
withtype 'a LListR = 'a LList ref;

(* Apply proc to all elements in a linked list *)
fun seqll (proc: '_a -> unit) : ('_a LListR -> unit) =
    let fun seq (ref nilL) = () |
            seq (ref((a:'_a)&l)) = (proc a; seq l)
    in seq end;

fun llist_to_list (ref nilL) = [] |
    llist_to_list (ref(a&ll)) = a::(llist_to_list ll);

val len = length;

local open Array SynExt in
nonfix sub;

fun forA(p: int -> unit, a: 'a array) : unit =
    let val ub = length a
        fun step(i) = if i=ub then () else (p(i); step(i+1));
    in step 0 end;

fun itA(a0:'a, b: 'b array)(f:'a * 'b -> 'a) : 'a =
    let val ub = length b
        fun acc(a,i) = if i=ub then a else acc(f(a,sub(b,i)),i+1)
    in acc(a0,0) end;



(** grammars **)

datatype 'a symb =
  Dlm of 'a |
  Arg of string * int;

datatype 'a prod = Prod of string * 'a symb list * string * int;


datatype Symbol = T of token | NT of int * int
     and Op = Op of OpSyn * string * int
withtype OpSyn = Symbol array
     and OpListA = Op array * int TokenMap
     and FastAcc = int TokenMap;

(*gram_tabs: name of nt -> number, nt number -> productions array,
  nt number -> list of nt's reachable via copy ops*)

type gram_tabs = int Symtab.table * OpListA array * int list array;

type gram = string list * string prod list * gram_tabs;


fun non_term (Arg (s, _)) = if is_terminal s then None else Some s
  | non_term _ = None;

fun non_terms (Prod (_, symbs, _, _)) = mapfilter non_term symbs;


(* mk_pre_grammar *)
(* converts a list of productions in external format into an
   internal gram object. *)

val dummyTM:FastAcc = mkTokenMap[];

fun mk_pre_grammar prods : gram_tabs =
  let
    fun same_res (Prod(t1, _, _, _), Prod(t2, _, _, _)) = t1=t2;
    val partitioned0 = partition_eq same_res prods;
    val nts0 = map (fn Prod(ty, _, _, _)::_ => ty) partitioned0;
    val nts' = distinct(flat(map non_terms prods)) \\ nts0;
    val nts = nts' @ nts0;
    val partitioned = (replicate (len nts') []) @ partitioned0;
    val ntis = nts ~~ (0 upto (len(nts)-1));
    val tab = foldr Symtab.update (ntis, Symtab.null);

    fun nt_or_vt (s, p) =
      (case predef_term s of
        None => NT (the (Symtab.lookup (tab, s)), p)
      | Some tk => T tk);

    fun mksyn(Dlm(t)) = T(t)
      | mksyn(Arg(t)) = nt_or_vt t;

    fun prod2op(Prod(nt, sy, opn, p)) =
        let val syA = arrayoflist(map mksyn sy) in Op(syA, opn, p) end;

    fun mkops prods = (arrayoflist(map prod2op prods), dummyTM);

    val opLA = arrayoflist(map mkops partitioned);

    val subs = array(length opLA, []) : int list array;
    fun newcp v (a, Op(syA, _, p)) =
        if p=chain_pri
        then let val NT(k, _) = sub(syA, 0)
             in if k mem v then a else k ins a end
        else a;
    fun reach v i =
        let val new = itA ([], #1(sub(opLA, i))) (newcp v)
            val v' = new union v
        in flat(map (reach v') new) union v' end;
    fun rch(i) = update(subs, i, reach[i]i);

  in
    forA(rch, subs); (tab, opLA, subs)
  end;


val RootPref = "__";

(* Lookahead tables for speeding up parsing. Lkhd is a mapping from
nonterminals (in the form of OpList) to sets (lists) of token strings *)

type Lkhd = token list list list;

(* subst_syn(s, k) syn = [ pref k ts | ts is a token string derivable from sy
                                      under substitution s ] *)
(* This is the general version.
fun cross l1 l2 = flat(map (fn e2 => (map (fn e1 => e1@e2) l1)) l2);

(* pref k [x1,...,xn] is [x1,...,xk] if 0<=k<=n and [x1,...,xn] otherwise *)
fun pref 0 l = []
  | pref _ [] = []
  | pref k (e::l) = e::(pref (k-1) l);

fun subst_syn(s:Lkhd,k) =
    let fun subst(ref(symb & syn)):token list list =
              let val l1 = case symb of T t => [[t]] |
                         NT(oplr,_) => let val Some l = assoc(s,!oplr) in l end
              in distinct(map (pref k) (cross l1 (subst syn))) end |
            subst _ = [[]]
    in subst end;
*)
(* This one is specialized to lookahead 1 and a bit too generous *)
fun subst_syn(s:Lkhd,1) syA =
    let fun subst i = if i = length(syA) then [[]] else
              case sub(syA,i) of
                NT(j,_) => let val pre = nth_elem(j,s)
                         in if [] mem pre then (pre \ []) union subst(i+1)
                            else pre end |
               T(tk) => [[tk]];
    in subst 0 end;

(* mk_lkhd(G,k) returns a table which associates with every nonterminal N in
G the list of pref k s for all token strings s with N -G->* s *)

fun mk_lkhd(opLA:OpListA array,k:int):Lkhd =
    let fun step(s:Lkhd):Lkhd =
            let fun subst_op(l,Op(sy,_,_)) = subst_syn(s,k)sy union l;
                fun step2(l,(opA,_)) = l@[itA([],opA)subst_op];
            in writeln"."; itA([],opLA)step2 end;
        fun iterate(s:Lkhd):Lkhd = let val s' = step s
              in if map len s = map len s' then s
                 else iterate s' end
    in writeln"Computing lookahead tables ...";
       iterate (replicate (length opLA) []) end;


(* mk_earley_gram *)       (* create look ahead tables *)

fun mk_earley_gram (g as (tab, opLA, _):gram_tabs):gram_tabs =
    let val lkhd = mk_lkhd(opLA, 1);
        fun mk_fa(i):FastAcc =
            let val opA = #1(sub(opLA, i));
                fun start(j) = let val Op(sy, _, _) = sub(opA, j);
                                   val pre = subst_syn(lkhd, 1) sy
                        in (j, if [] mem pre then [] else map hd pre) end;
            in mkTokenMap(map start (0 upto(length(opA)-1))) end;
        fun updt(i) = update(opLA, i, (#1(sub(opLA, i)), mk_fa(i)));

    in forA(updt, opLA); g end;


(* compile_xgram *)

fun compile_xgram (roots, prods) =
  let
    fun mk_root nt =
      Prod (RootPref ^ nt, [Arg (nt, 0), Dlm EndToken], "", 0);

    val prods' = (map mk_root roots) @ prods;
  in
    mk_earley_gram (mk_pre_grammar prods')
  end;


(* translate (from xgram.ML) *)

fun translate trfn =
  map (fn Dlm t => Dlm (trfn t) | Arg s => Arg s);


(* mk_gram_tabs *)

fun str_to_tok (opl: string prod list): token prod list =
  map
    (fn Prod (t, syn, s, pa) => Prod (t, translate Token syn, s, pa))
    opl;

fun mk_gram_tabs roots prods = compile_xgram (roots, str_to_tok prods);



(** build gram **)

fun mk_gram roots prods = (roots, prods, mk_gram_tabs roots prods);

fun sub_gram (roots1, prods1, _) (roots2, prods2, _) =
  roots1 subset roots2 andalso prods1 subset prods2;


(* empty, extend, merge grams *)

val empty_gram = mk_gram [] [];

fun extend_gram (gram1 as (roots1, prods1, _)) roots2 xprods2 =
  let
    fun symb_of (Delim s) = Some (Dlm s)
      | symb_of (Argument s_p) = Some (Arg s_p)
      | symb_of _ = None;

    fun prod_of (XProd (lhs, xsymbs, const, pri)) =
      Prod (lhs, mapfilter symb_of xsymbs, const, pri);

    val prods2 = distinct (map prod_of xprods2);
  in
    if roots2 subset roots1 andalso prods2 subset prods1 then gram1
    else mk_gram (extend_list roots1 roots2) (extend_list prods1 prods2)
  end;

fun merge_grams (gram1 as (roots1, prods1, _)) (gram2 as (roots2, prods2, _)) =
  if sub_gram gram2 gram1 then gram1
  else if sub_gram gram1 gram2 then gram2
  else mk_gram (merge_lists roots1 roots2) (merge_lists prods1 prods2);


(* pretty_gram *)

fun pretty_gram (_, prods, _) =
  let
    fun pretty_name name = [Pretty.str (name ^ " =")];

    fun pretty_symb (Dlm s) = Pretty.str (quote s)
      | pretty_symb (Arg (s, p)) =
          if is_terminal s then Pretty.str s
          else Pretty.str (s ^ "[" ^ string_of_int p ^ "]");

    fun pretty_const "" = []
      | pretty_const c = [Pretty.str ("=> " ^ quote c)];

    fun pretty_pri p = [Pretty.str ("(" ^ string_of_int p ^ ")")];

    fun pretty_prod (Prod (name, symbs, const, pri)) =
      Pretty.block (Pretty.breaks (pretty_name name @
        map pretty_symb symbs @ pretty_const const @ pretty_pri pri));
  in
    map pretty_prod prods
  end;



(* State: nonterminal#, production#, index in production,
          index of originating state set,
          parse trees generated so far,
*)

datatype State = St of int * int * int * int * parsetree list
withtype StateSet  = State LListR * (State -> unit) LListR;
type Compl = State -> unit;
type StateSetList = StateSet array;
(* Debugging:
val print_SL = seqll(fn St(nti,pi,ip,fs,ptl)=>
(print_int nti; prs" "; print_int pi; prs" "; print_int ip; prs" ";
print_int fs; prs" "; print_int(len ptl); prs"\n"));

fun print_SS(s1,delr) = (writeln"================="; print_SL s1);

fun count_ss(ref nilL) = 0
  | count_ss(ref(_ & ss)) = count_ss(ss)+1;

fun print_stat(state_sets) =
    let fun pr i = let val(s1,_)=sub(state_sets,i)
                in prs" "; print_int(count_ss s1) end;
    in prs"["; forA(pr,state_sets); prs"]\n" end;
*)
fun mt_stateS():StateSet = (ref nilL, ref nilL);

fun mt_states(n):StateSetList = array(n,mt_stateS());

fun ismt_stateS((ref nilL,_):StateSet) = true | ismt_stateS _ = false;

fun fst_state((ref(st & _),_): StateSet) = st;

fun apply_all_states(f,(slr,_):StateSet) = seqll f slr;

fun add_state(nti,pi,ip,from,ptl,(sllr,delr):StateSet) =
      let fun add(ref(St(nti',pi',ip',from',_) & rest)) =
                if nti=nti' andalso pi=pi' andalso ip=ip' andalso from=from'
                then ()
                else add rest |
              add(last as ref nilL) =
                let val newst = St(nti,pi,ip,from,ptl)
                in last := newst & ref nilL;
                   seqll (fn compl => compl newst) delr
                end;
      in add sllr end;

fun complete(nti,syA,opn,p,ptl,ss,si as (_,delr):StateSet,opLA,rchA) =
      let val pt = mk_pt(opn,ptl)
          fun compl(St(ntj,pj,jp,from,ptl)) =
                let val Op(syj,_,_) = sub(fst(sub(opLA,ntj)),pj) in
                if jp=length(syj) then () else
                case sub(syj,jp) of
                  NT(nt,p') => if p >= p' andalso nti mem sub(rchA,nt)
                        then add_state(ntj,pj,jp+1,from,ptl@[pt], si)
                        else ()
                | _ => ()
                end
      in apply_all_states(compl,ss);
         if length(syA)=0 (* delayed completion in case of empty production: *)
         then delr := compl & ref(!delr) else ()
      end;

fun predict(tk,isi,si,p',opLA) = fn nti =>
    let val (opA,tm) = sub(opLA,nti);
        fun add(pi) = let val opr as Op(syA,_,p) = sub(opA,pi)
                in if p < p' then () else add_state(nti,pi,0,isi,[],si) end
    in seq add (applyTokenMap(tm,tk)) end;



fun unknown c = error ("Unparsable category: " ^ c);

fun syn_err toks =
  error ("Syntax error at: " ^ quote (space_implode " " (map str_of_token toks)));

fun parse ((_, _, (tab, opLA, rchA)):gram) (root:string) (tl: token list): parsetree =
  let
    val tl' = tl;
    val state_sets = mt_states(len tl' + 1);
    val s0 = mt_stateS();
    val rooti = case Symtab.lookup(tab, RootPref^root) of
            Some(ri) => ri | None => unknown root;

    fun lr (tl, isi, si, t) =
        if ismt_stateS(si) then syn_err (t::tl) else
        case tl of
          [] => () |
          t::tl =>
            let val si1 = mt_stateS();
                fun process(St(nti,pi,ip,from,ptl)) =
                      let val opA = #1(sub(opLA,nti))
                          val Op(syA,opn,p) = sub(opA,pi) in
                    if ip = length(syA)
                    then complete(nti,syA,opn,p,ptl,
                                    sub(state_sets,from),si,opLA,rchA)
                    else case sub(syA,ip) of
                      NT(ntj,p) =>
                            seq (predict(t,isi,si,p,opLA)) (sub(rchA,ntj))
                    | T(t') =>
                        if matching_tokens(t,t')
                        then add_state(nti,pi,ip+1,from,
                                       if valued_token(t)
                                       then ptl@[Tip(t)] else ptl,
                                       si1)
                        else () end;

        in apply_all_states(process,si);
           update(state_sets,isi+1,si1);
           lr(tl,isi+1,si1,t) end

  in
    update (state_sets, 0, s0);
    add_state (rooti, 0, 0, 0, [], s0);
    lr (tl', 0, s0, EndToken(*dummy*));
    (*print_stat state_sets;*)
    let val St(_, _, _, _, [pt]) = fst_state(sub(state_sets, len tl'))
    in pt end
  end;

end;


end;

