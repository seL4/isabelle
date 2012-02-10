(*  Title:      HOL/Matrix/Cplex_tools.ML
    Author:     Steven Obua
*)

signature CPLEX =
sig

    datatype cplexTerm = cplexVar of string | cplexNum of string | cplexInf
                       | cplexNeg of cplexTerm
                       | cplexProd of cplexTerm * cplexTerm
                       | cplexSum of (cplexTerm list)

    datatype cplexComp = cplexLe | cplexLeq | cplexEq | cplexGe | cplexGeq

    datatype cplexGoal = cplexMinimize of cplexTerm
               | cplexMaximize of cplexTerm

    datatype cplexConstr = cplexConstr of cplexComp *
                      (cplexTerm * cplexTerm)

    datatype cplexBounds = cplexBounds of cplexTerm * cplexComp * cplexTerm
                      * cplexComp * cplexTerm
             | cplexBound of cplexTerm * cplexComp * cplexTerm

    datatype cplexProg = cplexProg of string
                      * cplexGoal
                      * ((string option * cplexConstr)
                         list)
                      * cplexBounds list

    datatype cplexResult = Unbounded
             | Infeasible
             | Undefined
             | Optimal of string *
                      (((* name *) string *
                    (* value *) string) list)

    datatype cplexSolver = SOLVER_DEFAULT | SOLVER_CPLEX | SOLVER_GLPK

    exception Load_cplexFile of string
    exception Load_cplexResult of string
    exception Save_cplexFile of string
    exception Execute of string

    val load_cplexFile : string -> cplexProg

    val save_cplexFile : string -> cplexProg -> unit

    val elim_nonfree_bounds : cplexProg -> cplexProg

    val relax_strict_ineqs : cplexProg -> cplexProg

    val is_normed_cplexProg : cplexProg -> bool

    val get_solver : unit -> cplexSolver
    val set_solver : cplexSolver -> unit
    val solve : cplexProg -> cplexResult
end;

structure Cplex  : CPLEX =
struct

datatype cplexSolver = SOLVER_DEFAULT | SOLVER_CPLEX | SOLVER_GLPK

val cplexsolver = Unsynchronized.ref SOLVER_DEFAULT;
fun get_solver () = !cplexsolver;
fun set_solver s = (cplexsolver := s);

exception Load_cplexFile of string;
exception Load_cplexResult of string;
exception Save_cplexFile of string;

datatype cplexTerm = cplexVar of string
           | cplexNum of string
           | cplexInf
                   | cplexNeg of cplexTerm
                   | cplexProd of cplexTerm * cplexTerm
                   | cplexSum of (cplexTerm list)
datatype cplexComp = cplexLe | cplexLeq | cplexEq | cplexGe | cplexGeq
datatype cplexGoal = cplexMinimize of cplexTerm | cplexMaximize of cplexTerm
datatype cplexConstr = cplexConstr of cplexComp * (cplexTerm * cplexTerm)
datatype cplexBounds = cplexBounds of cplexTerm * cplexComp * cplexTerm
                      * cplexComp * cplexTerm
                     | cplexBound of cplexTerm * cplexComp * cplexTerm
datatype cplexProg = cplexProg of string
                  * cplexGoal
                  * ((string option * cplexConstr) list)
                  * cplexBounds list

fun rev_cmp cplexLe = cplexGe
  | rev_cmp cplexLeq = cplexGeq
  | rev_cmp cplexGe = cplexLe
  | rev_cmp cplexGeq = cplexLeq
  | rev_cmp cplexEq = cplexEq

fun the NONE = raise (Load_cplexFile "SOME expected")
  | the (SOME x) = x;

fun modulo_signed is_something (cplexNeg u) = is_something u
  | modulo_signed is_something u = is_something u

fun is_Num (cplexNum _) = true
  | is_Num _ = false

fun is_Inf cplexInf = true
  | is_Inf _ = false

fun is_Var (cplexVar _) = true
  | is_Var _ = false

fun is_Neg (cplexNeg _) = true
  | is_Neg _ = false

fun is_normed_Prod (cplexProd (t1, t2)) =
    (is_Num t1) andalso (is_Var t2)
  | is_normed_Prod x = is_Var x

fun is_normed_Sum (cplexSum ts) =
    (ts <> []) andalso forall (modulo_signed is_normed_Prod) ts
  | is_normed_Sum x = modulo_signed is_normed_Prod x

fun is_normed_Constr (cplexConstr (_, (t1, t2))) =
    (is_normed_Sum t1) andalso (modulo_signed is_Num t2)

fun is_Num_or_Inf x = is_Inf x orelse is_Num x

fun is_normed_Bounds (cplexBounds (t1, c1, t2, c2, t3)) =
    (c1 = cplexLe orelse c1 = cplexLeq) andalso
    (c2 = cplexLe orelse c2 = cplexLeq) andalso
    is_Var t2 andalso
    modulo_signed is_Num_or_Inf t1 andalso
    modulo_signed is_Num_or_Inf t3
  | is_normed_Bounds (cplexBound (t1, c, t2)) =
    (is_Var t1 andalso (modulo_signed is_Num_or_Inf t2))
    orelse
    (c <> cplexEq andalso
     is_Var t2 andalso (modulo_signed is_Num_or_Inf t1))

fun term_of_goal (cplexMinimize x) = x
  | term_of_goal (cplexMaximize x) = x

fun is_normed_cplexProg (cplexProg (_, goal, constraints, bounds)) =
    is_normed_Sum (term_of_goal goal) andalso
    forall (fn (_,x) => is_normed_Constr x) constraints andalso
    forall is_normed_Bounds bounds

fun is_NL s = s = "\n"

fun is_blank s = forall (fn c => c <> #"\n" andalso Char.isSpace c) (String.explode s)

fun is_num a =
    let
    val b = String.explode a
    fun num4 cs = forall Char.isDigit cs
    fun num3 [] = true
      | num3 (ds as (c::cs)) =
        if c = #"+" orelse c = #"-" then
        num4 cs
        else
        num4 ds
    fun num2 [] = true
      | num2 (c::cs) =
        if c = #"e" orelse c = #"E" then num3 cs
        else (Char.isDigit c) andalso num2 cs
    fun num1 [] = true
      | num1 (c::cs) =
        if c = #"." then num2 cs
        else if c = #"e" orelse c = #"E" then num3 cs
        else (Char.isDigit c) andalso num1 cs
    fun num [] = true
      | num (c::cs) =
        if c = #"." then num2 cs
        else (Char.isDigit c) andalso num1 cs
    in
    num b
    end

fun is_delimiter s = s = "+" orelse s = "-" orelse s = ":"

fun is_cmp s = s = "<" orelse s = ">" orelse s = "<="
             orelse s = ">=" orelse s = "="

fun is_symbol a =
    let
    val symbol_char = String.explode "!\"#$%&()/,.;?@_`'{}|~"
    fun is_symbol_char c = Char.isAlphaNum c orelse
                   exists (fn d => d=c) symbol_char
    fun is_symbol_start c = is_symbol_char c andalso
                not (Char.isDigit c) andalso
                not (c= #".")
    val b = String.explode a
    in
    b <> [] andalso is_symbol_start (hd b) andalso
    forall is_symbol_char b
    end

fun to_upper s = String.implode (map Char.toUpper (String.explode s))

fun keyword x =
    let
    val a = to_upper x
    in
    if a = "BOUNDS" orelse a = "BOUND" then
        SOME "BOUNDS"
    else if a = "MINIMIZE" orelse a = "MINIMUM" orelse a = "MIN" then
        SOME "MINIMIZE"
    else if a = "MAXIMIZE" orelse a = "MAXIMUM" orelse a = "MAX" then
        SOME "MAXIMIZE"
    else if a = "ST" orelse a = "S.T." orelse a = "ST." then
        SOME "ST"
    else if a = "FREE" orelse a = "END" then
        SOME a
    else if a = "GENERAL" orelse a = "GENERALS" orelse a = "GEN" then
        SOME "GENERAL"
    else if a = "INTEGER" orelse a = "INTEGERS" orelse a = "INT" then
        SOME "INTEGER"
    else if a = "BINARY" orelse a = "BINARIES" orelse a = "BIN" then
        SOME "BINARY"
    else if a = "INF" orelse a = "INFINITY" then
        SOME "INF"
    else
        NONE
    end

val TOKEN_ERROR = ~1
val TOKEN_BLANK = 0
val TOKEN_NUM = 1
val TOKEN_DELIMITER = 2
val TOKEN_SYMBOL = 3
val TOKEN_LABEL = 4
val TOKEN_CMP = 5
val TOKEN_KEYWORD = 6
val TOKEN_NL = 7

(* tokenize takes a list of chars as argument and returns a list of
   int * string pairs, each string representing a "cplex token",
   and each int being one of TOKEN_NUM, TOKEN_DELIMITER, TOKEN_CMP
   or TOKEN_SYMBOL *)
fun tokenize s =
    let
    val flist = [(is_NL, TOKEN_NL),
             (is_blank, TOKEN_BLANK),
             (is_num, TOKEN_NUM),
                     (is_delimiter, TOKEN_DELIMITER),
             (is_cmp, TOKEN_CMP),
             (is_symbol, TOKEN_SYMBOL)]
    fun match_helper [] s = (fn _ => false, TOKEN_ERROR)
      | match_helper (f::fs) s =
        if ((fst f) s) then f else match_helper fs s
    fun match s = match_helper flist s
    fun tok s =
        if s = "" then [] else
        let
        val h = String.substring (s,0,1)
        val (f, j) = match h
        fun len i =
            if size s = i then i
            else if f (String.substring (s,0,i+1)) then
            len (i+1)
            else i
        in
        if j < 0 then
            (if h = "\\" then []
             else raise (Load_cplexFile ("token expected, found: "
                         ^s)))
        else
            let
            val l = len 1
            val u = String.substring (s,0,l)
            val v = String.extract (s,l,NONE)
            in
            if j = 0 then tok v else (j, u) :: tok v
            end
        end
    in
    tok s
    end

exception Tokenize of string;

fun tokenize_general flist s =
    let
    fun match_helper [] s = raise (Tokenize s)
      | match_helper (f::fs) s =
        if ((fst f) s) then f else match_helper fs s
    fun match s = match_helper flist s
    fun tok s =
        if s = "" then [] else
        let
        val h = String.substring (s,0,1)
        val (f, j) = match h
        fun len i =
            if size s = i then i
            else if f (String.substring (s,0,i+1)) then
            len (i+1)
            else i
        val l = len 1
        in
        (j, String.substring (s,0,l)) :: tok (String.extract (s,l,NONE))
        end
    in
    tok s
    end

fun load_cplexFile name =
    let
    val f = TextIO.openIn name
        val ignore_NL = Unsynchronized.ref true
    val rest = Unsynchronized.ref []

    fun is_symbol s c = (fst c) = TOKEN_SYMBOL andalso (to_upper (snd c)) = s

    fun readToken_helper () =
        if length (!rest) > 0 then
        let val u = hd (!rest) in
            (
             rest := tl (!rest);
             SOME u
            )
        end
        else
          (case TextIO.inputLine f of
            NONE => NONE
          | SOME s =>
            let val t = tokenize s in
            if (length t >= 2 andalso
                snd(hd (tl t)) = ":")
            then
                rest := (TOKEN_LABEL, snd (hd t)) :: (tl (tl t))
            else if (length t >= 2) andalso is_symbol "SUBJECT" (hd (t))
                andalso is_symbol "TO" (hd (tl t))
            then
                rest := (TOKEN_SYMBOL, "ST") :: (tl (tl t))
            else
                rest := t;
            readToken_helper ()
            end)

    fun readToken_helper2 () =
        let val c = readToken_helper () in
            if c = NONE then NONE
                    else if !ignore_NL andalso fst (the c) = TOKEN_NL then
            readToken_helper2 ()
            else if fst (the c) = TOKEN_SYMBOL
                andalso keyword (snd (the c)) <> NONE
            then SOME (TOKEN_KEYWORD, the (keyword (snd (the c))))
            else c
        end

    fun readToken () = readToken_helper2 ()

    fun pushToken a = rest := (a::(!rest))

    fun is_value token =
        fst token = TOKEN_NUM orelse (fst token = TOKEN_KEYWORD
                      andalso snd token = "INF")

        fun get_value token =
        if fst token = TOKEN_NUM then
        cplexNum (snd token)
        else if fst token = TOKEN_KEYWORD andalso snd token = "INF"
        then
        cplexInf
        else
        raise (Load_cplexFile "num expected")

    fun readTerm_Product only_num =
        let val c = readToken () in
        if c = NONE then NONE
        else if fst (the c) = TOKEN_SYMBOL
        then (
            if only_num then (pushToken (the c); NONE)
            else SOME (cplexVar (snd (the c)))
            )
        else if only_num andalso is_value (the c) then
            SOME (get_value (the c))
        else if is_value (the c) then
            let val t1 = get_value (the c)
            val d = readToken ()
            in
            if d = NONE then SOME t1
            else if fst (the d) = TOKEN_SYMBOL then
                SOME (cplexProd (t1, cplexVar (snd (the d))))
            else
                (pushToken (the d); SOME t1)
            end
        else (pushToken (the c); NONE)
        end

    fun readTerm_Signed only_signed only_num =
        let
        val c = readToken ()
        in
        if c = NONE then NONE
        else
            let val d = the c in
            if d = (TOKEN_DELIMITER, "+") then
                readTerm_Product only_num
             else if d = (TOKEN_DELIMITER, "-") then
                 SOME (cplexNeg (the (readTerm_Product
                              only_num)))
             else (pushToken d;
                   if only_signed then NONE
                   else readTerm_Product only_num)
            end
        end

    fun readTerm_Sum first_signed =
        let val c = readTerm_Signed first_signed false in
        if c = NONE then [] else (the c)::(readTerm_Sum true)
        end

    fun readTerm () =
        let val c = readTerm_Sum false in
        if c = [] then NONE
        else if tl c = [] then SOME (hd c)
        else SOME (cplexSum c)
        end

    fun readLabeledTerm () =
        let val c = readToken () in
        if c = NONE then (NONE, NONE)
        else if fst (the c) = TOKEN_LABEL then
            let val t = readTerm () in
            if t = NONE then
                raise (Load_cplexFile ("term after label "^
                           (snd (the c))^
                           " expected"))
            else (SOME (snd (the c)), t)
            end
        else (pushToken (the c); (NONE, readTerm ()))
        end

    fun readGoal () =
        let
        val g = readToken ()
        in
            if g = SOME (TOKEN_KEYWORD, "MAXIMIZE") then
            cplexMaximize (the (snd (readLabeledTerm ())))
        else if g = SOME (TOKEN_KEYWORD, "MINIMIZE") then
            cplexMinimize (the (snd (readLabeledTerm ())))
        else raise (Load_cplexFile "MAXIMIZE or MINIMIZE expected")
        end

    fun str2cmp b =
        (case b of
         "<" => cplexLe
           | "<=" => cplexLeq
           | ">" => cplexGe
           | ">=" => cplexGeq
               | "=" => cplexEq
           | _ => raise (Load_cplexFile (b^" is no TOKEN_CMP")))

    fun readConstraint () =
            let
        val t = readLabeledTerm ()
        fun make_constraint b t1 t2 =
                    cplexConstr
            (str2cmp b,
             (t1, t2))
        in
        if snd t = NONE then NONE
        else
            let val c = readToken () in
            if c = NONE orelse fst (the c) <> TOKEN_CMP
            then raise (Load_cplexFile "TOKEN_CMP expected")
            else
                let val n = readTerm_Signed false true in
                if n = NONE then
                    raise (Load_cplexFile "num expected")
                else
                    SOME (fst t,
                      make_constraint (snd (the c))
                              (the (snd t))
                              (the n))
                end
            end
        end

        fun readST () =
        let
        fun readbody () =
            let val t = readConstraint () in
            if t = NONE then []
            else if (is_normed_Constr (snd (the t))) then
                (the t)::(readbody ())
            else if (fst (the t) <> NONE) then
                raise (Load_cplexFile
                       ("constraint '"^(the (fst (the t)))^
                    "'is not normed"))
            else
                raise (Load_cplexFile
                       "constraint is not normed")
            end
        in
        if readToken () = SOME (TOKEN_KEYWORD, "ST")
        then
            readbody ()
        else
            raise (Load_cplexFile "ST expected")
        end

    fun readCmp () =
        let val c = readToken () in
        if c = NONE then NONE
        else if fst (the c) = TOKEN_CMP then
            SOME (str2cmp (snd (the c)))
        else (pushToken (the c); NONE)
        end

    fun skip_NL () =
        let val c = readToken () in
        if c <> NONE andalso fst (the c) = TOKEN_NL then
            skip_NL ()
        else
            (pushToken (the c); ())
        end

    fun make_bounds c t1 t2 =
        cplexBound (t1, c, t2)

    fun readBound () =
        let
        val _ = skip_NL ()
        val t1 = readTerm ()
        in
        if t1 = NONE then NONE
        else
            let
            val c1 = readCmp ()
            in
            if c1 = NONE then
                let
                val c = readToken ()
                in
                if c = SOME (TOKEN_KEYWORD, "FREE") then
                    SOME (
                    cplexBounds (cplexNeg cplexInf,
                         cplexLeq,
                         the t1,
                         cplexLeq,
                         cplexInf))
                else
                    raise (Load_cplexFile "FREE expected")
                end
            else
                let
                val t2 = readTerm ()
                in
                if t2 = NONE then
                    raise (Load_cplexFile "term expected")
                else
                    let val c2 = readCmp () in
                    if c2 = NONE then
                        SOME (make_bounds (the c1)
                                  (the t1)
                                  (the t2))
                    else
                        SOME (
                        cplexBounds (the t1,
                             the c1,
                             the t2,
                             the c2,
                             the (readTerm())))
                    end
                end
            end
        end

    fun readBounds () =
        let
        fun makestring _ = "?"
        fun readbody () =
            let
            val b = readBound ()
            in
            if b = NONE then []
            else if (is_normed_Bounds (the b)) then
                (the b)::(readbody())
            else (
                raise (Load_cplexFile
                       ("bounds are not normed in: "^
                    (makestring (the b)))))
            end
        in
        if readToken () = SOME (TOKEN_KEYWORD, "BOUNDS") then
            readbody ()
        else raise (Load_cplexFile "BOUNDS expected")
        end

        fun readEnd () =
        if readToken () = SOME (TOKEN_KEYWORD, "END") then ()
        else raise (Load_cplexFile "END expected")

    val result_Goal = readGoal ()
    val result_ST = readST ()
    val _ =    ignore_NL := false
        val result_Bounds = readBounds ()
        val _ = ignore_NL := true
        val _ = readEnd ()
    val _ = TextIO.closeIn f
    in
    cplexProg (name, result_Goal, result_ST, result_Bounds)
    end

fun save_cplexFile filename (cplexProg (_, goal, constraints, bounds)) =
    let
    val f = TextIO.openOut filename

    fun basic_write s = TextIO.output(f, s)

    val linebuf = Unsynchronized.ref ""
    fun buf_flushline s =
        (basic_write (!linebuf);
         basic_write "\n";
         linebuf := s)
    fun buf_add s = linebuf := (!linebuf) ^ s

    fun write s =
        if (String.size s) + (String.size (!linebuf)) >= 250 then
        buf_flushline ("    "^s)
        else
        buf_add s

        fun writeln s = (buf_add s; buf_flushline "")

    fun write_term (cplexVar x) = write x
      | write_term (cplexNum x) = write x
      | write_term cplexInf = write "inf"
      | write_term (cplexProd (cplexNum "1", b)) = write_term b
      | write_term (cplexProd (a, b)) =
        (write_term a; write " "; write_term b)
          | write_term (cplexNeg x) = (write " - "; write_term x)
          | write_term (cplexSum ts) = write_terms ts
    and write_terms [] = ()
      | write_terms (t::ts) =
        (if (not (is_Neg t)) then write " + " else ();
         write_term t; write_terms ts)

    fun write_goal (cplexMaximize term) =
        (writeln "MAXIMIZE"; write_term term; writeln "")
      | write_goal (cplexMinimize term) =
        (writeln "MINIMIZE"; write_term term; writeln "")

    fun write_cmp cplexLe = write "<"
      | write_cmp cplexLeq = write "<="
      | write_cmp cplexEq = write "="
      | write_cmp cplexGe = write ">"
      | write_cmp cplexGeq = write ">="

    fun write_constr (cplexConstr (cmp, (a,b))) =
        (write_term a;
         write " ";
         write_cmp cmp;
         write " ";
         write_term b)

    fun write_constraints [] = ()
      | write_constraints (c::cs) =
        (if (fst c <> NONE)
         then
         (write (the (fst c)); write ": ")
         else
         ();
         write_constr (snd c);
         writeln "";
         write_constraints cs)

    fun write_bounds [] = ()
      | write_bounds ((cplexBounds (t1,c1,t2,c2,t3))::bs) =
        ((if t1 = cplexNeg cplexInf andalso t3 = cplexInf
         andalso (c1 = cplexLeq orelse c1 = cplexLe)
         andalso (c2 = cplexLeq orelse c2 = cplexLe)
          then
          (write_term t2; write " free")
          else
          (write_term t1; write " "; write_cmp c1; write " ";
           write_term t2; write " "; write_cmp c2; write " ";
           write_term t3)
         ); writeln ""; write_bounds bs)
      | write_bounds ((cplexBound (t1, c, t2)) :: bs) =
        (write_term t1; write " ";
         write_cmp c; write " ";
         write_term t2; writeln ""; write_bounds bs)

    val _ = write_goal goal
        val _ = (writeln ""; writeln "ST")
    val _ = write_constraints constraints
        val _ = (writeln ""; writeln "BOUNDS")
    val _ = write_bounds bounds
        val _ = (writeln ""; writeln "END")
        val _ = TextIO.closeOut f
    in
    ()
    end

fun norm_Constr (constr as cplexConstr (c, (t1, t2))) =
    if not (modulo_signed is_Num t2) andalso
       modulo_signed is_Num t1
    then
    [cplexConstr (rev_cmp c, (t2, t1))]
    else if (c = cplexLe orelse c = cplexLeq) andalso
        (t1 = (cplexNeg cplexInf) orelse t2 = cplexInf)
    then
    []
    else if (c = cplexGe orelse c = cplexGeq) andalso
        (t1 = cplexInf orelse t2 = cplexNeg cplexInf)
    then
    []
    else
    [constr]

fun bound2constr (cplexBounds (t1,c1,t2,c2,t3)) =
    (norm_Constr(cplexConstr (c1, (t1, t2))))
    @ (norm_Constr(cplexConstr (c2, (t2, t3))))
  | bound2constr (cplexBound (t1, cplexEq, t2)) =
    (norm_Constr(cplexConstr (cplexLeq, (t1, t2))))
    @ (norm_Constr(cplexConstr (cplexLeq, (t2, t1))))
  | bound2constr (cplexBound (t1, c1, t2)) =
    norm_Constr(cplexConstr (c1, (t1,t2)))

val emptyset = Symtab.empty

fun singleton v = Symtab.update (v, ()) emptyset

fun merge a b = Symtab.merge (op =) (a, b)

fun mergemap f ts = fold (fn x => fn table => merge table (f x)) ts Symtab.empty

fun diff a b = Symtab.fold (Symtab.delete_safe o fst) b a

fun collect_vars (cplexVar v) = singleton v
  | collect_vars (cplexNeg t) = collect_vars t
  | collect_vars (cplexProd (t1, t2)) =
    merge (collect_vars t1) (collect_vars t2)
  | collect_vars (cplexSum ts) = mergemap collect_vars ts
  | collect_vars _ = emptyset

(* Eliminates all nonfree bounds from the linear program and produces an
   equivalent program with only free bounds
   IF for the input program P holds: is_normed_cplexProg P *)
fun elim_nonfree_bounds (cplexProg (name, goal, constraints, bounds)) =
    let
    fun collect_constr_vars (_, cplexConstr (_, (t1,_))) =
        (collect_vars t1)

    val cvars = merge (collect_vars (term_of_goal goal))
              (mergemap collect_constr_vars constraints)

    fun collect_lower_bounded_vars
        (cplexBounds (_, _, cplexVar v, _, _)) =
        singleton v
      |  collect_lower_bounded_vars
         (cplexBound (_, cplexLe, cplexVar v)) =
         singleton v
      |  collect_lower_bounded_vars
         (cplexBound (_, cplexLeq, cplexVar v)) =
         singleton v
      |  collect_lower_bounded_vars
         (cplexBound (cplexVar v, cplexGe,_)) =
         singleton v
      |  collect_lower_bounded_vars
         (cplexBound (cplexVar v, cplexGeq, _)) =
         singleton v
      | collect_lower_bounded_vars
        (cplexBound (cplexVar v, cplexEq, _)) =
        singleton v
      |  collect_lower_bounded_vars _ = emptyset

    val lvars = mergemap collect_lower_bounded_vars bounds
    val positive_vars = diff cvars lvars
    val zero = cplexNum "0"

    fun make_pos_constr v =
        (NONE, cplexConstr (cplexGeq, ((cplexVar v), zero)))

    fun make_free_bound v =
        cplexBounds (cplexNeg cplexInf, cplexLeq,
             cplexVar v, cplexLeq,
             cplexInf)

    val pos_constrs = rev (Symtab.fold
                  (fn (k, _) => cons (make_pos_constr k))
                  positive_vars [])
        val bound_constrs = map (pair NONE)
                (maps bound2constr bounds)
    val constraints' = constraints @ pos_constrs @ bound_constrs
    val bounds' = rev (Symtab.fold (fn (v, _) => cons (make_free_bound v)) cvars []);
    in
    cplexProg (name, goal, constraints', bounds')
    end

fun relax_strict_ineqs (cplexProg (name, goals, constrs, bounds)) =
    let
    fun relax cplexLe = cplexLeq
      | relax cplexGe = cplexGeq
      | relax x = x

    fun relax_constr (n, cplexConstr(c, (t1, t2))) =
        (n, cplexConstr(relax c, (t1, t2)))

    fun relax_bounds (cplexBounds (t1, c1, t2, c2, t3)) =
        cplexBounds (t1, relax c1, t2, relax c2, t3)
      | relax_bounds (cplexBound (t1, c, t2)) =
        cplexBound (t1, relax c, t2)
    in
    cplexProg (name,
           goals,
           map relax_constr constrs,
           map relax_bounds bounds)
    end

datatype cplexResult = Unbounded
             | Infeasible
             | Undefined
             | Optimal of string * ((string * string) list)

fun is_separator x = forall (fn c => c = #"-") (String.explode x)

fun is_sign x = (x = "+" orelse x = "-")

fun is_colon x = (x = ":")

fun is_resultsymbol a =
    let
    val symbol_char = String.explode "!\"#$%&()/,.;?@_`'{}|~-"
    fun is_symbol_char c = Char.isAlphaNum c orelse
                   exists (fn d => d=c) symbol_char
    fun is_symbol_start c = is_symbol_char c andalso
                not (Char.isDigit c) andalso
                not (c= #".") andalso
                not (c= #"-")
    val b = String.explode a
    in
    b <> [] andalso is_symbol_start (hd b) andalso
    forall is_symbol_char b
    end

val TOKEN_SIGN = 100
val TOKEN_COLON = 101
val TOKEN_SEPARATOR = 102

fun load_glpkResult name =
    let
    val flist = [(is_NL, TOKEN_NL),
             (is_blank, TOKEN_BLANK),
             (is_num, TOKEN_NUM),
             (is_sign, TOKEN_SIGN),
                     (is_colon, TOKEN_COLON),
             (is_cmp, TOKEN_CMP),
             (is_resultsymbol, TOKEN_SYMBOL),
             (is_separator, TOKEN_SEPARATOR)]

    val tokenize = tokenize_general flist

    val f = TextIO.openIn name

    val rest = Unsynchronized.ref []

    fun readToken_helper () =
        if length (!rest) > 0 then
        let val u = hd (!rest) in
            (
             rest := tl (!rest);
             SOME u
            )
        end
        else
        (case TextIO.inputLine f of
          NONE => NONE
        | SOME s => (rest := tokenize s; readToken_helper()))

    fun is_tt tok ty = (tok <> NONE andalso (fst (the tok)) = ty)

    fun pushToken a = if a = NONE then () else (rest := ((the a)::(!rest)))

    fun readToken () =
        let val t = readToken_helper () in
        if is_tt t TOKEN_BLANK then
            readToken ()
        else if is_tt t TOKEN_NL then
            let val t2 = readToken_helper () in
            if is_tt t2 TOKEN_SIGN then
                (pushToken (SOME (TOKEN_SEPARATOR, "-")); t)
            else
                (pushToken t2; t)
            end
        else if is_tt t TOKEN_SIGN then
            let val t2 = readToken_helper () in
            if is_tt t2 TOKEN_NUM then
                (SOME (TOKEN_NUM, (snd (the t))^(snd (the t2))))
            else
                (pushToken t2; t)
            end
        else
            t
        end

        fun readRestOfLine P =
        let
        val t = readToken ()
        in
        if is_tt t TOKEN_NL orelse t = NONE
        then P
        else readRestOfLine P
        end

    fun readHeader () =
        let
        fun readStatus () = readRestOfLine ("STATUS", snd (the (readToken ())))
        fun readObjective () = readRestOfLine ("OBJECTIVE", snd (the (readToken (); readToken (); readToken ())))
        val t1 = readToken ()
        val t2 = readToken ()
        in
        if is_tt t1 TOKEN_SYMBOL andalso is_tt t2 TOKEN_COLON
        then
            case to_upper (snd (the t1)) of
            "STATUS" => (readStatus ())::(readHeader ())
              | "OBJECTIVE" => (readObjective())::(readHeader ())
              | _ => (readRestOfLine (); readHeader ())
        else
            (pushToken t2; pushToken t1; [])
        end

    fun skip_until_sep () =
        let val x = readToken () in
        if is_tt x TOKEN_SEPARATOR then
            readRestOfLine ()
        else
            skip_until_sep ()
        end

    fun load_value () =
        let
        val t1 = readToken ()
        val t2 = readToken ()
        in
        if is_tt t1 TOKEN_NUM andalso is_tt t2 TOKEN_SYMBOL then
            let
            val t = readToken ()
            val state = if is_tt t TOKEN_NL then readToken () else t
            val _ = if is_tt state TOKEN_SYMBOL then () else raise (Load_cplexResult "state expected")
            val k = readToken ()
            in
            if is_tt k TOKEN_NUM then
                readRestOfLine (SOME (snd (the t2), snd (the k)))
            else
                raise (Load_cplexResult "number expected")
            end
        else
            (pushToken t2; pushToken t1; NONE)
        end

    fun load_values () =
        let val v = load_value () in
        if v = NONE then [] else (the v)::(load_values ())
        end

    val header = readHeader ()

    val result =
        case AList.lookup (op =) header "STATUS" of
        SOME "INFEASIBLE" => Infeasible
          | SOME "UNBOUNDED" => Unbounded
          | SOME "OPTIMAL" => Optimal (the (AList.lookup (op =) header "OBJECTIVE"),
                       (skip_until_sep ();
                        skip_until_sep ();
                        load_values ()))
          | _ => Undefined

    val _ = TextIO.closeIn f
    in
    result
    end
    handle (Tokenize s) => raise (Load_cplexResult ("Tokenize: "^s))
     | Option => raise (Load_cplexResult "Option")

fun load_cplexResult name =
    let
    val flist = [(is_NL, TOKEN_NL),
             (is_blank, TOKEN_BLANK),
             (is_num, TOKEN_NUM),
             (is_sign, TOKEN_SIGN),
                     (is_colon, TOKEN_COLON),
             (is_cmp, TOKEN_CMP),
             (is_resultsymbol, TOKEN_SYMBOL)]

    val tokenize = tokenize_general flist

    val f = TextIO.openIn name

    val rest = Unsynchronized.ref []

    fun readToken_helper () =
        if length (!rest) > 0 then
        let val u = hd (!rest) in
            (
             rest := tl (!rest);
             SOME u
            )
        end
        else
        (case TextIO.inputLine f of
          NONE => NONE
        | SOME s => (rest := tokenize s; readToken_helper()))

    fun is_tt tok ty = (tok <> NONE andalso (fst (the tok)) = ty)

    fun pushToken a = if a = NONE then () else (rest := ((the a)::(!rest)))

    fun readToken () =
        let val t = readToken_helper () in
        if is_tt t TOKEN_BLANK then
            readToken ()
        else if is_tt t TOKEN_SIGN then
            let val t2 = readToken_helper () in
            if is_tt t2 TOKEN_NUM then
                (SOME (TOKEN_NUM, (snd (the t))^(snd (the t2))))
            else
                (pushToken t2; t)
            end
        else
            t
        end

        fun readRestOfLine P =
        let
        val t = readToken ()
        in
        if is_tt t TOKEN_NL orelse t = NONE
        then P
        else readRestOfLine P
        end

    fun readHeader () =
        let
        fun readStatus () = readRestOfLine ("STATUS", snd (the (readToken ())))
        fun readObjective () =
            let
            val t = readToken ()
            in
            if is_tt t TOKEN_SYMBOL andalso to_upper (snd (the t)) = "VALUE" then
                readRestOfLine ("OBJECTIVE", snd (the (readToken())))
            else
                readRestOfLine ("OBJECTIVE_NAME", snd (the t))
            end

        val t = readToken ()
        in
        if is_tt t TOKEN_SYMBOL then
            case to_upper (snd (the t)) of
            "STATUS" => (readStatus ())::(readHeader ())
              | "OBJECTIVE" => (readObjective ())::(readHeader ())
              | "SECTION" => (pushToken t; [])
              | _ => (readRestOfLine (); readHeader ())
        else
            (readRestOfLine (); readHeader ())
        end

    fun skip_nls () =
        let val x = readToken () in
        if is_tt x TOKEN_NL then
            skip_nls ()
        else
            (pushToken x; ())
        end

    fun skip_paragraph () =
        if is_tt (readToken ()) TOKEN_NL then
        (if is_tt (readToken ()) TOKEN_NL then
             skip_nls ()
         else
             skip_paragraph ())
        else
        skip_paragraph ()

    fun load_value () =
        let
        val t1 = readToken ()
        val t1 = if is_tt t1 TOKEN_SYMBOL andalso snd (the t1) = "A" then readToken () else t1
        in
        if is_tt t1 TOKEN_NUM then
            let
            val name = readToken ()
            val status = readToken ()
            val value = readToken ()
            in
            if is_tt name TOKEN_SYMBOL andalso
               is_tt status TOKEN_SYMBOL andalso
               is_tt value TOKEN_NUM
            then
                readRestOfLine (SOME (snd (the name), snd (the value)))
            else
                raise (Load_cplexResult "column line expected")
            end
        else
            (pushToken t1; NONE)
        end

    fun load_values () =
        let val v = load_value () in
        if v = NONE then [] else (the v)::(load_values ())
        end

    val header = readHeader ()

    val result =
        case AList.lookup (op =) header "STATUS" of
        SOME "INFEASIBLE" => Infeasible
          | SOME "NONOPTIMAL" => Unbounded
          | SOME "OPTIMAL" => Optimal (the (AList.lookup (op =) header "OBJECTIVE"),
                       (skip_paragraph ();
                        skip_paragraph ();
                        skip_paragraph ();
                        skip_paragraph ();
                        skip_paragraph ();
                        load_values ()))
          | _ => Undefined

    val _ = TextIO.closeIn f
    in
    result
    end
    handle (Tokenize s) => raise (Load_cplexResult ("Tokenize: "^s))
     | Option => raise (Load_cplexResult "Option")

exception Execute of string;

fun tmp_file s = Path.implode (Path.expand (File.tmp_path (Path.basic s)));
fun wrap s = "\""^s^"\"";

fun solve_glpk prog =
    let
    val name = string_of_int (Time.toMicroseconds (Time.now ()))
    val lpname = tmp_file (name^".lp")
    val resultname = tmp_file (name^".txt")
    val _ = save_cplexFile lpname prog
    val cplex_path = getenv "GLPK_PATH"
    val cplex = if cplex_path = "" then "glpsol" else cplex_path
    val command = (wrap cplex)^" --lpt "^(wrap lpname)^" --output "^(wrap resultname)
    val answer = #1 (Isabelle_System.bash_output command)
    in
    let
        val result = load_glpkResult resultname
        val _ = OS.FileSys.remove lpname
        val _ = OS.FileSys.remove resultname
    in
        result
    end
    handle (Load_cplexResult s) => raise (Execute ("Load_cplexResult: "^s^"\nExecute: "^answer))
         | _ => raise (Execute answer)  (* FIXME avoid handle _ *)
    end

fun solve_cplex prog =
    let
    fun write_script s lp r =
        let
        val f = TextIO.openOut s
        val _ = TextIO.output (f, "read\n"^lp^"\noptimize\nwrite\n"^r^"\nquit")
        val _ = TextIO.closeOut f
        in
        ()
        end

    val name = string_of_int (Time.toMicroseconds (Time.now ()))
    val lpname = tmp_file (name^".lp")
    val resultname = tmp_file (name^".txt")
    val scriptname = tmp_file (name^".script")
    val _ = save_cplexFile lpname prog
    val _ = write_script scriptname lpname resultname
    in
    let
        val result = load_cplexResult resultname
        val _ = OS.FileSys.remove lpname
        val _ = OS.FileSys.remove resultname
        val _ = OS.FileSys.remove scriptname
    in
        result
    end
    end

fun solve prog =
    case get_solver () of
      SOLVER_DEFAULT =>
        (case getenv "LP_SOLVER" of
       "CPLEX" => solve_cplex prog
         | "GLPK" => solve_glpk prog
         | _ => raise (Execute ("LP_SOLVER must be set to CPLEX or to GLPK")))
    | SOLVER_CPLEX => solve_cplex prog
    | SOLVER_GLPK => solve_glpk prog

end;
