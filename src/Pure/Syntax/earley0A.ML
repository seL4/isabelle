(*  Title:      Pure/Syntax/earley0A
    ID:         $Id$
    Author:     Tobias Nipkow

Changes:
  PARSER: renamed Prod to prod
  renamed mk_early_gram to mk_earley_gram
*)

signature PARSER =
sig
  structure XGram: XGRAM
  structure ParseTree: PARSE_TREE
  local open XGram ParseTree ParseTree.Lexicon in
  type Gram
  val compile_xgram: string list * Token prod list -> Gram
  val parse: Gram * string * Token list -> ParseTree
  val parsable: Gram * string -> bool
  exception SYNTAX_ERR of Token list
  val print_gram: Gram * Lexicon -> unit
  end
end;

functor EarleyFun(structure XGram:XGRAM and ParseTree:PARSE_TREE): PARSER =
struct

structure XGram = XGram;
structure ParseTree = ParseTree;

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
Gram: name of nt -> number, nt number -> productions array,
      nt number -> list of nt's reachable via copy ops
*)

datatype Symbol = T of Token | NT of int * int
     and Op = Op of OpSyn * string * int
withtype OpSyn = Symbol array
     and OpListA = Op array * int TokenMap
     and FastAcc = int TokenMap;

type Gram = int Symtab.table * OpListA array * int list array;

fun non_term(Nonterminal(s,_)) = if predef_term(s)=end_token then [s] else []
  | non_term(_) = [];

fun non_terms(Prod(_,symbs,_,_)) = flat(map non_term symbs);

(* mk_pre_grammar converts a list of productions in external format into an
internal Gram object. *)
val dummyTM:FastAcc = mkTokenMap[];

fun mk_pre_grammar(prods): Gram =
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
           end_token => let val Some(i) = Symtab.lookup(tab,s) in NT(i,p) end
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
        if p=copy_pri
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

type Lkhd = Token list list list;

(* subst_syn(s,k) syn = [ pref k ts | ts is a token string derivable from sy
                                      under substitution s ] *)
(* This is the general version.
fun cross l1 l2 = flat(map (fn e2 => (map (fn e1 => e1@e2) l1)) l2);

(* pref k [x1,...,xn] is [x1,...,xk] if 0<=k<=n and [x1,...,xn] otherwise *)
fun pref 0 l = []
  | pref _ [] = []
  | pref k (e::l) = e::(pref (k-1) l);

fun subst_syn(s:Lkhd,k) =
    let fun subst(ref(symb & syn)):Token list list =
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
fun mk_earley_gram(g as (tab,opLA,_):Gram):Gram =
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
                [Nonterminal(nt,0),Terminal(end_token)],"",0);
          val prods' = (map mk_root roots) @ prods
      in mk_earley_gram(mk_pre_grammar(prods')) end;

(* State: nonterminal#, production#, index in production,
          index of originating state set,
          parse trees generated so far,
*)

datatype State = St of int * int * int * int * ParseTree list
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


fun parsable((tab,_,_):Gram, root:string) =
        not(Symtab.lookup(tab,RootPref^root) = None);

exception SYNTAX_ERR of Token list;

fun unknown c = error("System Error - Trying to parse unknown category "^c);

fun parse((tab,opLA,rchA):Gram, root:string, tl: Token list): ParseTree =
    let val tl' = tl@[end_token];
        val state_sets = mt_states(len tl' +1);
        val s0 = mt_stateS();
        val rooti = case Symtab.lookup(tab,RootPref^root) of
                Some(ri) => ri | None => unknown root;

        fun lr (tl,isi,si,t) =
            if ismt_stateS(si) then raise SYNTAX_ERR(t::tl) else
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
       lr(tl',0,s0,end_token(*dummy*));
       (*print_stat state_sets;*)
       let val St(_,_,_,_,[pt]) = fst_state(sub(state_sets,len tl'))
       in pt end
    end;

fun print_gram ((st,opAA,rchA):Gram,lex) =
    let val tts = Lexicon.name_of_token;
        val al = map (fn (x,y)=>(y,x)) (Symtab.alist_of st);
        fun nt i = let val Some(s) = assoc(al,i) in s end;
        fun print_sy(T(end_token)) = prs". " |
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

end;

end;
