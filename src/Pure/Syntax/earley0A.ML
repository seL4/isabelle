(*  Title:      Pure/Syntax/earley0A.ML
    ID:         $Id$
    Author:     Tobias Nipkow

WARNING: This file is about to disappear.
*)

signature PARSER =
sig
  structure XGram: XGRAM
  structure ParseTree: PARSE_TREE
  local open XGram ParseTree ParseTree.Lexicon in
    type gram
    val mk_gram: string list -> string prod list -> gram
    val parse: gram -> string -> token list -> parsetree
  end

(*  exception SYNTAX_ERROR of token list *)
(*  val compile_xgram: string list * token prod list -> Gram *)
(*  val parsable: Gram * string -> bool *)
(*  val print_gram: Gram * lexicon -> unit *)
end;

functor EarleyFun(structure Symtab: SYMTAB and XGram: XGRAM
  and ParseTree: PARSE_TREE): PARSER =
struct

structure ParseTree = ParseTree;
structure Lexicon = ParseTree.Lexicon;
structure XGram = XGram;
open ParseTree Lexicon;


(** mk_pt (from parse_tree.ML) **)

fun mk_pt ("", [pt]) = pt
  | mk_pt ("", _) = error "mk_pt: funny copy op in parse tree"
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

local open Array XGram ParseTree ParseTree.Lexicon in
nonfix sub;

fun forA(p: int -> unit, a: 'a array) : unit =
    let val ub = length a
        fun step(i) = if i=ub then () else (p(i); step(i+1));
    in step 0 end;

fun itA(a0:'a, b: 'b array)(f:'a * 'b -> 'a) : 'a =
    let val ub = length b
        fun acc(a,i) = if i=ub then a else acc(f(a,sub(b,i)),i+1)
    in acc(a0,0) end;

(*
gram: name of nt -> number, nt number -> productions array,
      nt number -> list of nt's reachable via copy ops
*)

datatype Symbol = T of token | NT of int * int
     and Op = Op of OpSyn * string * int
withtype OpSyn = Symbol array
     and OpListA = Op array * int TokenMap
     and FastAcc = int TokenMap;

type gram = int Symtab.table * OpListA array * int list array;

fun non_term(Nonterminal(s,_)) = if predef_term(s)=EndToken then [s] else []
  | non_term(_) = [];

fun non_terms(Prod(_,symbs,_,_)) = flat(map non_term symbs);

(* mk_pre_grammar converts a list of productions in external format into an
internal gram object. *)
val dummyTM:FastAcc = mkTokenMap[];

fun mk_pre_grammar(prods): gram =
let fun same_res(Prod(t1,_,_,_), Prod(t2,_,_,_)) = t1=t2;
    val partitioned0 = partition_eq same_res prods;
    val nts0 = map (fn Prod(ty,_,_,_)::_ => ty) partitioned0;
    val nts' = distinct(flat(map non_terms prods)) \\ nts0;
    val nts = nts' @ nts0;
    val partitioned = (replicate (len nts') []) @ partitioned0;
    val ntis = nts ~~ (0 upto (len(nts)-1));
    val tab = foldr Symtab.update (ntis,Symtab.null);

    fun nt_or_vt(s,p) =
        (case predef_term(s) of
           EndToken => let val Some(i) = Symtab.lookup(tab,s) in NT(i,p) end
         | tk => T(tk));

    fun mksyn(Terminal(t)) = [T(t)]
      | mksyn(Nonterminal(t)) = [nt_or_vt t]
      | mksyn(_) = [];

    fun prod2op(Prod(nt,sy,opn,p)) =
        let val syA = arrayoflist(flat(map mksyn sy)) in Op(syA,opn,p) end;

    fun mkops prods = (arrayoflist(map prod2op prods),dummyTM);

    val opLA = arrayoflist(map mkops partitioned);

    val subs = array(length opLA,[]) : int list array;
    fun newcp v (a,Op(syA,_,p)) =
        if p=chain_pri
        then let val NT(k,_) = sub(syA,0)
             in if k mem v then a else k ins a end
        else a;
    fun reach v i =
        let val new = itA ([],#1(sub(opLA,i))) (newcp v)
            val v' = new union v
        in flat(map (reach v') new) union v' end;
    fun rch(i) = update(subs,i,reach[i]i);

in forA(rch,subs); (tab,opLA,subs) end;

val RootPref = "__";

(* Lookahead tables for speeding up parsing. Lkhd is a mapping from
nonterminals (in the form of OpList) to sets (lists) of token strings *)

type Lkhd = token list list list;

(* subst_syn(s,k) syn = [ pref k ts | ts is a token string derivable from sy
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

(* create look ahead tables *)
fun mk_earley_gram(g as (tab,opLA,_):gram):gram =
    let val lkhd = mk_lkhd(opLA,1);
        fun mk_fa(i):FastAcc =
            let val opA = #1(sub(opLA,i));
                fun start(j) = let val Op(sy,_,_) = sub(opA,j);
                                   val pre = subst_syn(lkhd,1) sy
                        in (j,if [] mem pre then [] else map hd pre) end;
            in mkTokenMap(map start (0 upto(length(opA)-1))) end;
        fun updt(i) = update(opLA,i,(#1(sub(opLA,i)),mk_fa(i)));

    in forA(updt,opLA); g end;

fun compile_xgram(roots,prods) =
      let fun mk_root nt = Prod(RootPref^nt,
                [Nonterminal(nt,0),Terminal(EndToken)],"",0);
          val prods' = (map mk_root roots) @ prods
      in mk_earley_gram(mk_pre_grammar(prods')) end;


(* translate (from xgram.ML) *)

fun translate trfn =
  map
    (fn Terminal t => Terminal (trfn t)
      | Nonterminal s => Nonterminal s
      | Space s => Space s
      | Bg i => Bg i
      | Brk i => Brk i
      | En => En);


(* mk_gram (from syntax.ML) *)

fun str_to_tok (opl: string prod list): token prod list =
  map
    (fn Prod (t, syn, s, pa) => Prod (t, translate Token syn, s, pa))
    opl;

fun mk_gram roots prods = compile_xgram (roots, str_to_tok prods);



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


(*(* FIXME *)
fun parsable((tab,_,_):gram, root:string) =
        not(Symtab.lookup(tab,RootPref^root) = None);
*)

(* exception SYNTAX_ERROR of token list; *) (* FIXME *)

fun unknown c = error ("Unparsable category: " ^ c);

fun syn_err toks = error ("Syntax error at: " ^ space_implode " " (map str_of_token toks));

fun parse ((tab,opLA,rchA):gram) (root:string) (tl: token list): parsetree =
    let val tl' = tl;   (* FIXME was ..@[EndToken] *)
        val state_sets = mt_states(len tl' +1);
        val s0 = mt_stateS();
        val rooti = case Symtab.lookup(tab,RootPref^root) of
                Some(ri) => ri | None => unknown root;

        fun lr (tl,isi,si,t) =
(*            if ismt_stateS(si) then raise SYNTAX_ERROR(t::tl) else  *)  (* FIXME *)
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

    in update(state_sets,0,s0);
       add_state(rooti,0,0,0,[],s0);
       lr(tl',0,s0,EndToken(*dummy*));
       (*print_stat state_sets;*)
       let val St(_,_,_,_,[pt]) = fst_state(sub(state_sets,len tl'))
       in pt end
    end;


(*(* FIXME *)
fun print_gram ((st,opAA,rchA):gram,lex) =
    let val tts = Lexicon.name_of_token;
        val al = map (fn (x,y)=>(y,x)) (Symtab.alist_of st);
        fun nt i = let val Some(s) = assoc(al,i) in s end;
        fun print_sy(T(EndToken)) = prs". " |
            print_sy(T(tk)) = (prs(tts tk); prs" ") |
            print_sy(NT(i,p)) = (prs((nt i)^"[");print_int p;prs"] ");
        fun print_opA(i) =
                let val lhs = nt i;
                    val (opA,_)=sub(opAA,i);
                    fun print_op(j) =
                        let val Op(sy,n,p) = sub(opA,j)
                        in prs(lhs^" = "); forA(fn i=>print_sy(sub(sy,i)),sy);
                           if n="" then () else prs(" => \""^n^"\"");
                           prs" (";print_int p;prs")\n"
                        end;
                in forA(print_op,opA) end;
        fun print_rch(i) = (print_int i; prs" -> ";
                            print_list("[","]\n",print_int) (sub(rchA,i)))
    in forA(print_opA,opAA) (*; forA(print_rch,rchA) *) end;
*)

end;

end;

