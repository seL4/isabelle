(* ========================================================================= *)
(* DERIVED RULES FOR CREATING FIRST ORDER LOGIC THEOREMS                     *)
(* Copyright (c) 2001-2006 Joe Hurd, distributed under the BSD License *)
(* ========================================================================= *)

structure Rule :> Rule =
struct

open Useful;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------- reflexivity                                                     *)
(*   x = x                                                                   *)
(* ------------------------------------------------------------------------- *)

val reflexivity = Thm.refl (Term.Var "x");

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------------------- symmetry                                            *)
(*   ~(x = y) \/ y = x                                                       *)
(* ------------------------------------------------------------------------- *)

val symmetry =
    let
      val x = Term.Var "x"
      and y = Term.Var "y"
      val reflTh = reflexivity
      val reflLit = Thm.destUnit reflTh
      val eqTh = Thm.equality reflLit [0] y
    in
      Thm.resolve reflLit reflTh eqTh
    end;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------------------------------- transitivity                            *)
(*   ~(x = y) \/ ~(y = z) \/ x = z                                           *)
(* ------------------------------------------------------------------------- *)

val transitivity =
    let
      val x = Term.Var "x"
      and y = Term.Var "y"
      and z = Term.Var "z"
      val eqTh = Thm.equality (Literal.mkEq (y,z)) [0] x
    in
      Thm.resolve (Literal.mkEq (y,x)) symmetry eqTh
    end;

(* ------------------------------------------------------------------------- *)
(*   x = y \/ C                                                              *)
(* -------------- symEq (x = y)                                              *)
(*   y = x \/ C                                                              *)
(* ------------------------------------------------------------------------- *)

fun symEq lit th =
    let
      val (x,y) = Literal.destEq lit
    in
      if x = y then th
      else
        let
          val sub = Subst.fromList [("x",x),("y",y)]
          val symTh = Thm.subst sub symmetry
        in
          Thm.resolve lit th symTh
        end
    end;

(* ------------------------------------------------------------------------- *)
(* An equation consists of two terms (t,u) plus a theorem (stronger than)    *)
(* t = u \/ C.                                                               *)
(* ------------------------------------------------------------------------- *)

type equation = (Term.term * Term.term) * Thm.thm;

fun ppEquation pp (eqn as (_,th)) = Thm.pp pp th;

fun equationToString x = Parser.toString ppEquation x;

fun equationLiteral (t_u,th) =
    let
      val lit = Literal.mkEq t_u
    in
      if LiteralSet.member lit (Thm.clause th) then SOME lit else NONE
    end;

fun reflEqn t = ((t,t), Thm.refl t);

fun symEqn (eqn as ((t,u), th)) =
    if t = u then eqn
    else
      ((u,t),
       case equationLiteral eqn of
         SOME t_u => symEq t_u th
       | NONE => th);

fun transEqn (eqn1 as ((x,y), th1)) (eqn2 as ((_,z), th2)) =
    if x = y then eqn2
    else if y = z then eqn1
    else if x = z then reflEqn x
    else
      ((x,z),
       case equationLiteral eqn1 of
         NONE => th1
       | SOME x_y =>
         case equationLiteral eqn2 of
           NONE => th2
         | SOME y_z =>
           let
             val sub = Subst.fromList [("x",x),("y",y),("z",z)]
             val th = Thm.subst sub transitivity
             val th = Thm.resolve x_y th1 th
             val th = Thm.resolve y_z th2 th
           in
             th
           end);

(*DEBUG
val transEqn = fn eqn1 => fn eqn2 =>
    transEqn eqn1 eqn2
    handle Error err =>
      raise Error ("Rule.transEqn:\neqn1 = " ^ equationToString eqn1 ^
                   "\neqn2 = " ^ equationToString eqn2 ^ "\n" ^ err);
*)

(* ------------------------------------------------------------------------- *)
(* A conversion takes a term t and either:                                   *)
(* 1. Returns a term u together with a theorem (stronger than) t = u \/ C.   *)
(* 2. Raises an Error exception.                                             *)
(* ------------------------------------------------------------------------- *)

type conv = Term.term -> Term.term * Thm.thm;

fun allConv tm = (tm, Thm.refl tm);

val noConv : conv = fn _ => raise Error "noConv";

fun traceConv s conv tm =
    let
      val res as (tm',th) = conv tm
      val () = print (s ^ ": " ^ Term.toString tm ^ " --> " ^
                      Term.toString tm' ^ " " ^ Thm.toString th ^ "\n")
    in
      res
    end
    handle Error err =>
      (print (s ^ ": " ^ Term.toString tm ^ " --> Error: " ^ err ^ "\n");
       raise Error (s ^ ": " ^ err));
    
fun thenConvTrans tm (tm',th1) (tm'',th2) =
    let
      val eqn1 = ((tm,tm'),th1)
      and eqn2 = ((tm',tm''),th2)
      val (_,th) = transEqn eqn1 eqn2
    in
      (tm'',th)
    end;

fun thenConv conv1 conv2 tm =
    let
      val res1 as (tm',_) = conv1 tm
      val res2 = conv2 tm'
    in
      thenConvTrans tm res1 res2
    end;

fun orelseConv (conv1 : conv) conv2 tm = conv1 tm handle Error _ => conv2 tm;

fun tryConv conv = orelseConv conv allConv;

fun changedConv conv tm =
    let
      val res as (tm',_) = conv tm
    in
      if tm = tm' then raise Error "changedConv" else res
    end;

fun repeatConv conv tm = tryConv (thenConv conv (repeatConv conv)) tm;

fun firstConv [] _ = raise Error "firstConv"
  | firstConv [conv] tm = conv tm
  | firstConv (conv :: convs) tm = orelseConv conv (firstConv convs) tm;

fun everyConv [] tm = allConv tm
  | everyConv [conv] tm = conv tm
  | everyConv (conv :: convs) tm = thenConv conv (everyConv convs) tm;

fun rewrConv (eqn as ((x,y), eqTh)) path tm =
    if x = y then allConv tm
    else if null path then (y,eqTh)
    else
      let
        val reflTh = Thm.refl tm
        val reflLit = Thm.destUnit reflTh
        val th = Thm.equality reflLit (1 :: path) y
        val th = Thm.resolve reflLit reflTh th
        val th =
            case equationLiteral eqn of
              NONE => th
            | SOME x_y => Thm.resolve x_y eqTh th
        val tm' = Term.replace tm (path,y)
      in
        (tm',th)
      end;

(*DEBUG
val rewrConv = fn eqn as ((x,y),eqTh) => fn path => fn tm =>
    rewrConv eqn path tm
    handle Error err =>
      raise Error ("Rule.rewrConv:\nx = " ^ Term.toString x ^
                   "\ny = " ^ Term.toString y ^
                   "\neqTh = " ^ Thm.toString eqTh ^
                   "\npath = " ^ Term.pathToString path ^
                   "\ntm = " ^ Term.toString tm ^ "\n" ^ err);
*)

fun pathConv conv path tm =
    let
      val x = Term.subterm tm path
      val (y,th) = conv x
    in
      rewrConv ((x,y),th) path tm
    end;

fun subtermConv conv i = pathConv conv [i];

fun subtermsConv _ (tm as Term.Var _) = allConv tm
  | subtermsConv conv (tm as Term.Fn (_,a)) =
    everyConv (map (subtermConv conv) (interval 0 (length a))) tm;

(* ------------------------------------------------------------------------- *)
(* Applying a conversion to every subterm, with some traversal strategy.     *)
(* ------------------------------------------------------------------------- *)

fun bottomUpConv conv tm =
    thenConv (subtermsConv (bottomUpConv conv)) (repeatConv conv) tm;

fun topDownConv conv tm =
    thenConv (repeatConv conv) (subtermsConv (topDownConv conv)) tm;

fun repeatTopDownConv conv =
    let
      fun f tm = thenConv (repeatConv conv) g tm
      and g tm = thenConv (subtermsConv f) h tm
      and h tm = tryConv (thenConv conv f) tm
    in
      f
    end;

(*DEBUG
val repeatTopDownConv = fn conv => fn tm =>
    repeatTopDownConv conv tm
    handle Error err => raise Error ("repeatTopDownConv: " ^ err);
*)

(* ------------------------------------------------------------------------- *)
(* A literule (bad pun) takes a literal L and either:                        *)
(* 1. Returns a literal L' with a theorem (stronger than) ~L \/ L' \/ C.     *)
(* 2. Raises an Error exception.                                             *)
(* ------------------------------------------------------------------------- *)

type literule = Literal.literal -> Literal.literal * Thm.thm;

fun allLiterule lit = (lit, Thm.assume lit);

val noLiterule : literule = fn _ => raise Error "noLiterule";

fun thenLiterule literule1 literule2 lit =
    let
      val res1 as (lit',th1) = literule1 lit
      val res2 as (lit'',th2) = literule2 lit'
    in
      if lit = lit' then res2
      else if lit' = lit'' then res1
      else if lit = lit'' then allLiterule lit
      else
        (lit'',
         if not (Thm.member lit' th1) then th1
         else if not (Thm.negateMember lit' th2) then th2
         else Thm.resolve lit' th1 th2)
    end;

fun orelseLiterule (literule1 : literule) literule2 lit =
    literule1 lit handle Error _ => literule2 lit;

fun tryLiterule literule = orelseLiterule literule allLiterule;

fun changedLiterule literule lit =
    let
      val res as (lit',_) = literule lit
    in
      if lit = lit' then raise Error "changedLiterule" else res
    end;

fun repeatLiterule literule lit =
    tryLiterule (thenLiterule literule (repeatLiterule literule)) lit;

fun firstLiterule [] _ = raise Error "firstLiterule"
  | firstLiterule [literule] lit = literule lit
  | firstLiterule (literule :: literules) lit =
    orelseLiterule literule (firstLiterule literules) lit;

fun everyLiterule [] lit = allLiterule lit
  | everyLiterule [literule] lit = literule lit
  | everyLiterule (literule :: literules) lit =
    thenLiterule literule (everyLiterule literules) lit;

fun rewrLiterule (eqn as ((x,y),eqTh)) path lit =
    if x = y then allLiterule lit
    else
      let
        val th = Thm.equality lit path y
        val th =
            case equationLiteral eqn of
              NONE => th
            | SOME x_y => Thm.resolve x_y eqTh th
        val lit' = Literal.replace lit (path,y)
      in
        (lit',th)
      end;

(*DEBUG
val rewrLiterule = fn eqn => fn path => fn lit =>
    rewrLiterule eqn path lit
    handle Error err =>
      raise Error ("Rule.rewrLiterule:\neqn = " ^ equationToString eqn ^
                   "\npath = " ^ Term.pathToString path ^
                   "\nlit = " ^ Literal.toString lit ^ "\n" ^ err);
*)

fun pathLiterule conv path lit =
    let
      val tm = Literal.subterm lit path
      val (tm',th) = conv tm
    in
      rewrLiterule ((tm,tm'),th) path lit
    end;

fun argumentLiterule conv i = pathLiterule conv [i];

fun allArgumentsLiterule conv lit =
    everyLiterule
      (map (argumentLiterule conv) (interval 0 (Literal.arity lit))) lit;

(* ------------------------------------------------------------------------- *)
(* A rule takes one theorem and either deduces another or raises an Error    *)
(* exception.                                                                *)
(* ------------------------------------------------------------------------- *)

type rule = Thm.thm -> Thm.thm;

val allRule : rule = fn th => th;

val noRule : rule = fn _ => raise Error "noRule";

fun thenRule (rule1 : rule) (rule2 : rule) th = rule1 (rule2 th);

fun orelseRule (rule1 : rule) rule2 th = rule1 th handle Error _ => rule2 th;

fun tryRule rule = orelseRule rule allRule;

fun changedRule rule th =
    let
      val th' = rule th
    in
      if not (LiteralSet.equal (Thm.clause th) (Thm.clause th')) then th'
      else raise Error "changedRule"
    end;

fun repeatRule rule lit = tryRule (thenRule rule (repeatRule rule)) lit;

fun firstRule [] _ = raise Error "firstRule"
  | firstRule [rule] th = rule th
  | firstRule (rule :: rules) th = orelseRule rule (firstRule rules) th;

fun everyRule [] th = allRule th
  | everyRule [rule] th = rule th
  | everyRule (rule :: rules) th = thenRule rule (everyRule rules) th;

fun literalRule literule lit th =
    let
      val (lit',litTh) = literule lit
    in
      if lit = lit' then th
      else if not (Thm.negateMember lit litTh) then litTh
      else Thm.resolve lit th litTh
    end;

(*DEBUG
val literalRule = fn literule => fn lit => fn th =>
    literalRule literule lit th
    handle Error err =>
      raise Error ("Rule.literalRule:\nlit = " ^ Literal.toString lit ^
                   "\nth = " ^ Thm.toString th ^ "\n" ^ err);
*)

fun rewrRule eqTh lit path = literalRule (rewrLiterule eqTh path) lit;

fun pathRule conv lit path = literalRule (pathLiterule conv path) lit;

fun literalsRule literule =
    let
      fun f (lit,th) =
          if Thm.member lit th then literalRule literule lit th else th
    in
      fn lits => fn th => LiteralSet.foldl f th lits
    end;

fun allLiteralsRule literule th = literalsRule literule (Thm.clause th) th;

fun convRule conv = allLiteralsRule (allArgumentsLiterule conv);
  
(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ---------------------------------------------- functionCongruence (f,n)   *)
(*   ~(x0 = y0) \/ ... \/ ~(x{n-1} = y{n-1}) \/                              *)
(*   f x0 ... x{n-1} = f y0 ... y{n-1}                                       *)
(* ------------------------------------------------------------------------- *)

fun functionCongruence (f,n) =
    let
      val xs = List.tabulate (n, fn i => Term.Var ("x" ^ Int.toString i))
      and ys = List.tabulate (n, fn i => Term.Var ("y" ^ Int.toString i))

      fun cong ((i,yi),(th,lit)) =
          let
            val path = [1,i]
            val th = Thm.resolve lit th (Thm.equality lit path yi)
            val lit = Literal.replace lit (path,yi)
          in
            (th,lit)
          end

      val reflTh = Thm.refl (Term.Fn (f,xs))
      val reflLit = Thm.destUnit reflTh
    in
      fst (foldl cong (reflTh,reflLit) (enumerate ys))
    end;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ---------------------------------------------- relationCongruence (R,n)   *)
(*   ~(x0 = y0) \/ ... \/ ~(x{n-1} = y{n-1}) \/                              *)
(*   ~R x0 ... x{n-1} \/ R y0 ... y{n-1}                                     *)
(* ------------------------------------------------------------------------- *)

fun relationCongruence (R,n) =
    let
      val xs = List.tabulate (n, fn i => Term.Var ("x" ^ Int.toString i))
      and ys = List.tabulate (n, fn i => Term.Var ("y" ^ Int.toString i))

      fun cong ((i,yi),(th,lit)) =
          let
            val path = [i]
            val th = Thm.resolve lit th (Thm.equality lit path yi)
            val lit = Literal.replace lit (path,yi)
          in
            (th,lit)
          end

      val assumeLit = (false,(R,xs))
      val assumeTh = Thm.assume assumeLit
    in
      fst (foldl cong (assumeTh,assumeLit) (enumerate ys))
    end;

(* ------------------------------------------------------------------------- *)
(*   ~(x = y) \/ C                                                           *)
(* ----------------- symNeq ~(x = y)                                         *)
(*   ~(y = x) \/ C                                                           *)
(* ------------------------------------------------------------------------- *)

fun symNeq lit th =
    let
      val (x,y) = Literal.destNeq lit
    in
      if x = y then th
      else
        let
          val sub = Subst.fromList [("x",y),("y",x)]
          val symTh = Thm.subst sub symmetry
        in
          Thm.resolve lit th symTh
        end
    end;

(* ------------------------------------------------------------------------- *)
(* sym (x = y) = symEq (x = y)  /\  sym ~(x = y) = symNeq ~(x = y)           *)
(* ------------------------------------------------------------------------- *)

fun sym (lit as (pol,_)) th = if pol then symEq lit th else symNeq lit th;

(* ------------------------------------------------------------------------- *)
(*   ~(x = x) \/ C                                                           *)
(* ----------------- removeIrrefl                                            *)
(*         C                                                                 *)
(*                                                                           *)
(* where all irreflexive equalities.                                         *)
(* ------------------------------------------------------------------------- *)

local
  fun irrefl ((true,_),th) = th
    | irrefl (lit as (false,atm), th) =
      case total Atom.destRefl atm of
        SOME x => Thm.resolve lit th (Thm.refl x)
      | NONE => th;
in
  fun removeIrrefl th = LiteralSet.foldl irrefl th (Thm.clause th);
end;

(* ------------------------------------------------------------------------- *)
(*   x = y \/ y = x \/ C                                                     *)
(* ----------------------- removeSym                                         *)
(*       x = y \/ C                                                          *)
(*                                                                           *)
(* where all duplicate copies of equalities and disequalities are removed.   *)
(* ------------------------------------------------------------------------- *)

local
  fun rem (lit as (pol,atm), eqs_th as (eqs,th)) =
      case total Atom.sym atm of
        NONE => eqs_th
      | SOME atm' =>
        if LiteralSet.member lit eqs then
          (eqs, if pol then symEq lit th else symNeq lit th)
        else
          (LiteralSet.add eqs (pol,atm'), th);
in
  fun removeSym th =
      snd (LiteralSet.foldl rem (LiteralSet.empty,th) (Thm.clause th));
end;

(* ------------------------------------------------------------------------- *)
(*   ~(v = t) \/ C                                                           *)
(* ----------------- expandAbbrevs                                           *)
(*      C[t/v]                                                               *)
(*                                                                           *)
(* where t must not contain any occurrence of the variable v.                *)
(* ------------------------------------------------------------------------- *)

local
  fun expand lit =
      let
        val (x,y) = Literal.destNeq lit
      in
        if (Term.isTypedVar x orelse Term.isTypedVar y) andalso x <> y then
          Subst.unify Subst.empty x y
        else raise Error "expand"
      end;
in
  fun expandAbbrevs th =
      case LiteralSet.firstl (total expand) (Thm.clause th) of
        NONE => removeIrrefl th
      | SOME sub => expandAbbrevs (Thm.subst sub th);
end;

(* ------------------------------------------------------------------------- *)
(* simplify = isTautology + expandAbbrevs + removeSym                        *)
(* ------------------------------------------------------------------------- *)

fun simplify th =
    if Thm.isTautology th then NONE
    else
      let
        val th' = th
        val th' = expandAbbrevs th'
        val th' = removeSym th'
      in
        if Thm.equal th th' then SOME th else simplify th'
      end;

(* ------------------------------------------------------------------------- *)
(*    C                                                                      *)
(* -------- freshVars                                                        *)
(*   C[s]                                                                    *)
(*                                                                           *)
(* where s is a renaming substitution chosen so that all of the variables in *)
(* C are replaced by fresh variables.                                        *)
(* ------------------------------------------------------------------------- *)

fun freshVars th = Thm.subst (Subst.freshVars (Thm.freeVars th)) th;

(* ------------------------------------------------------------------------- *)
(*               C                                                           *)
(* ---------------------------- factor                                       *)
(*   C_s_1, C_s_2, ..., C_s_n                                                *)
(*                                                                           *)
(* where each s_i is a substitution that factors C, meaning that the theorem *)
(*                                                                           *)
(*   C_s_i = (removeIrrefl o removeSym o Thm.subst s_i) C                    *)
(*                                                                           *)
(* has fewer literals than C.                                                *)
(*                                                                           *)
(* Also, if s is any substitution that factors C, then one of the s_i will   *)
(* result in a theorem C_s_i that strictly subsumes the theorem C_s.         *)
(* ------------------------------------------------------------------------- *)

local
  datatype edge =
      FactorEdge of Atom.atom * Atom.atom
    | ReflEdge of Term.term * Term.term;

  fun ppEdge p (FactorEdge atm_atm') = Parser.ppPair Atom.pp Atom.pp p atm_atm'
    | ppEdge p (ReflEdge tm_tm') = Parser.ppPair Term.pp Term.pp p tm_tm';

  datatype joinStatus =
      Joined
    | Joinable of Subst.subst
    | Apart;

  fun joinEdge sub edge =
      let
        val result =
            case edge of
              FactorEdge (atm,atm') => total (Atom.unify sub atm) atm'
            | ReflEdge (tm,tm') => total (Subst.unify sub tm) tm'
      in
        case result of
          NONE => Apart
        | SOME sub' =>
          if Portable.pointerEqual (sub,sub') then Joined else Joinable sub'
      end;

  fun updateApart sub =
      let
        fun update acc [] = SOME acc
          | update acc (edge :: edges) =
            case joinEdge sub edge of
              Joined => NONE
            | Joinable _ => update (edge :: acc) edges
            | Apart => update acc edges
      in
        update []
      end;

  fun addFactorEdge (pol,atm) ((pol',atm'),acc) =
      if pol <> pol' then acc
      else
        let
          val edge = FactorEdge (atm,atm')
        in
          case joinEdge Subst.empty edge of
            Joined => raise Bug "addFactorEdge: joined"
          | Joinable sub => (sub,edge) :: acc
          | Apart => acc
        end;

  fun addReflEdge (false,_) acc = acc
    | addReflEdge (true,atm) acc =
      let
        val edge = ReflEdge (Atom.destEq atm)
      in
        case joinEdge Subst.empty edge of
          Joined => raise Bug "addRefl: joined"
        | Joinable _ => edge :: acc
        | Apart => acc
      end;

  fun addIrreflEdge (true,_) acc = acc
    | addIrreflEdge (false,atm) acc =
      let
        val edge = ReflEdge (Atom.destEq atm)
      in
        case joinEdge Subst.empty edge of
          Joined => raise Bug "addRefl: joined"
        | Joinable sub => (sub,edge) :: acc
        | Apart => acc
      end;

  fun init_edges acc _ [] =
      let
        fun init ((apart,sub,edge),(edges,acc)) =
            (edge :: edges, (apart,sub,edges) :: acc)
      in
        snd (List.foldl init ([],[]) acc)
      end
    | init_edges acc apart ((sub,edge) :: sub_edges) =
      let
(*DEBUG
        val () = if not (Subst.null sub) then ()
                 else raise Bug "Rule.factor.init_edges: empty subst"
*)
        val (acc,apart) =
            case updateApart sub apart of
              SOME apart' => ((apart',sub,edge) :: acc, edge :: apart)
            | NONE => (acc,apart)
      in
        init_edges acc apart sub_edges
      end;

  fun mk_edges apart sub_edges [] = init_edges [] apart sub_edges
    | mk_edges apart sub_edges (lit :: lits) =
      let
        val sub_edges = List.foldl (addFactorEdge lit) sub_edges lits

        val (apart,sub_edges) =
            case total Literal.sym lit of
              NONE => (apart,sub_edges)
            | SOME lit' =>
              let
                val apart = addReflEdge lit apart
                val sub_edges = addIrreflEdge lit sub_edges
                val sub_edges = List.foldl (addFactorEdge lit') sub_edges lits
              in
                (apart,sub_edges)
              end
      in
        mk_edges apart sub_edges lits
      end;

  fun fact acc [] = acc
    | fact acc ((_,sub,[]) :: others) = fact (sub :: acc) others
    | fact acc ((apart, sub, edge :: edges) :: others) =
      let
        val others =
            case joinEdge sub edge of
              Joinable sub' =>
              let
                val others = (edge :: apart, sub, edges) :: others
              in
                case updateApart sub' apart of
                  NONE => others
                | SOME apart' => (apart',sub',edges) :: others
              end
            | _ => (apart,sub,edges) :: others
      in
        fact acc others
      end;
in
  fun factor' cl =
      let
(*TRACE6
        val () = Parser.ppTrace LiteralSet.pp "Rule.factor': cl" cl
*)
        val edges = mk_edges [] [] (LiteralSet.toList cl)
(*TRACE6
        val ppEdgesSize = Parser.ppMap length Parser.ppInt
        val ppEdgel = Parser.ppList ppEdge
        val ppEdges = Parser.ppList (Parser.ppTriple ppEdgel Subst.pp ppEdgel)
        val () = Parser.ppTrace ppEdgesSize "Rule.factor': |edges|" edges
        val () = Parser.ppTrace ppEdges "Rule.factor': edges" edges
*)
        val result = fact [] edges
(*TRACE6
        val ppResult = Parser.ppList Subst.pp
        val () = Parser.ppTrace ppResult "Rule.factor': result" result
*)
      in
        result
      end;
end;

fun factor th =
    let
      fun fact sub = removeSym (Thm.subst sub th)
    in
      map fact (factor' (Thm.clause th))
    end;

end
