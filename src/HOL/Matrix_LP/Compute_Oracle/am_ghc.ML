(*  Title:      HOL/Matrix_LP/Compute_Oracle/am_ghc.ML
    Author:     Steven Obua
*)

structure AM_GHC : ABSTRACT_MACHINE =
struct

open AbstractMachine;

type program = string * string * (int Inttab.table)

fun count_patternvars PVar = 1
  | count_patternvars (PConst (_, ps)) =
      List.foldl (fn (p, count) => (count_patternvars p)+count) 0 ps

fun update_arity arity code a = 
    (case Inttab.lookup arity code of
         NONE => Inttab.update_new (code, a) arity
       | SOME (a': int) => if a > a' then Inttab.update (code, a) arity else arity)

(* We have to find out the maximal arity of each constant *)
fun collect_pattern_arity PVar arity = arity
  | collect_pattern_arity (PConst (c, args)) arity = fold collect_pattern_arity args (update_arity arity c (length args))
 
local
fun collect applevel (Var _) arity = arity
  | collect applevel (Const c) arity = update_arity arity c applevel
  | collect applevel (Abs m) arity = collect 0 m arity
  | collect applevel (App (a,b)) arity = collect 0 b (collect (applevel + 1) a arity)
in
fun collect_term_arity t arity = collect 0 t arity
end

fun nlift level n (Var m) = if m < level then Var m else Var (m+n) 
  | nlift level n (Const c) = Const c
  | nlift level n (App (a,b)) = App (nlift level n a, nlift level n b)
  | nlift level n (Abs b) = Abs (nlift (level+1) n b)

fun rep n x = if n = 0 then [] else x::(rep (n-1) x)

fun adjust_rules rules =
    let
        val arity = fold (fn (p, t) => fn arity => collect_term_arity t (collect_pattern_arity p arity)) rules Inttab.empty
        fun arity_of c = the (Inttab.lookup arity c)
        fun adjust_pattern PVar = PVar
          | adjust_pattern (C as PConst (c, args)) = if (length args <> arity_of c) then raise Compile ("Constant inside pattern must have maximal arity") else C
        fun adjust_rule (PVar, _) = raise Compile ("pattern may not be a variable")
          | adjust_rule (rule as (p as PConst (c, args),t)) = 
            let
                val _ = if not (check_freevars (count_patternvars p) t) then raise Compile ("unbound variables on right hand side") else () 
                val args = map adjust_pattern args              
                val len = length args
                val arity = arity_of c
                fun lift level n (Var m) = if m < level then Var m else Var (m+n) 
                  | lift level n (Const c) = Const c
                  | lift level n (App (a,b)) = App (lift level n a, lift level n b)
                  | lift level n (Abs b) = Abs (lift (level+1) n b)
                val lift = lift 0
                fun adjust_term n t = if n=0 then t else adjust_term (n-1) (App (t, Var (n-1))) 
            in
                if len = arity then
                    rule
                else if arity >= len then  
                    (PConst (c, args @ (rep (arity-len) PVar)), adjust_term (arity-len) (lift (arity-len) t))
                else (raise Compile "internal error in adjust_rule")
            end
    in
        (arity, map adjust_rule rules)
    end             

fun print_term arity_of n =
let
    fun str x = string_of_int x
    fun protect_blank s = if exists_string Symbol.is_ascii_blank s then "(" ^ s ^")" else s
                                                                                          
    fun print_apps d f [] = f
      | print_apps d f (a::args) = print_apps d ("app "^(protect_blank f)^" "^(protect_blank (print_term d a))) args
    and print_call d (App (a, b)) args = print_call d a (b::args) 
      | print_call d (Const c) args = 
        (case arity_of c of 
             NONE => print_apps d ("Const "^(str c)) args 
           | SOME a =>
             let
                 val len = length args
             in
                 if a <= len then 
                     let
                         val s = "c"^(str c)^(implode (map (fn t => " "^(protect_blank (print_term d t))) (List.take (args, a))))
                     in
                         print_apps d s (List.drop (args, a))
                     end
                 else 
                     let
                         fun mk_apps n t = if n = 0 then t else mk_apps (n-1) (App (t, Var (n-1)))
                         fun mk_lambdas n t = if n = 0 then t else mk_lambdas (n-1) (Abs t)
                         fun append_args [] t = t
                           | append_args (c::cs) t = append_args cs (App (t, c))
                     in
                         print_term d (mk_lambdas (a-len) (mk_apps (a-len) (nlift 0 (a-len) (append_args args (Const c)))))
                     end
             end)
      | print_call d t args = print_apps d (print_term d t) args
    and print_term d (Var x) = if x < d then "b"^(str (d-x-1)) else "x"^(str (n-(x-d)-1))
      | print_term d (Abs c) = "Abs (\\b"^(str d)^" -> "^(print_term (d + 1) c)^")"
      | print_term d t = print_call d t []
in
    print_term 0 
end
                                                
fun print_rule arity_of (p, t) = 
    let 
        fun str x = string_of_int x                  
        fun print_pattern top n PVar = (n+1, "x"^(str n))
          | print_pattern top n (PConst (c, [])) = (n, (if top then "c" else "C")^(str c))
          | print_pattern top n (PConst (c, args)) = 
            let
                val (n,s) = print_pattern_list (n, (if top then "c" else "C")^(str c)) args
            in
                (n, if top then s else "("^s^")")
            end
        and print_pattern_list r [] = r
          | print_pattern_list (n, p) (t::ts) = 
            let
                val (n, t) = print_pattern false n t
            in
                print_pattern_list (n, p^" "^t) ts
            end
        val (n, pattern) = print_pattern true 0 p
    in
        pattern^" = "^(print_term arity_of n t) 
    end

fun group_rules rules =
    let
        fun add_rule (r as (PConst (c,_), _)) groups =
            let
                val rs = (case Inttab.lookup groups c of NONE => [] | SOME rs => rs)
            in
                Inttab.update (c, r::rs) groups
            end
          | add_rule _ _ = raise Compile "internal error group_rules"
    in
        fold_rev add_rule rules Inttab.empty
    end

fun haskell_prog name rules = 
    let
        val buffer = Unsynchronized.ref ""
        fun write s = (buffer := (!buffer)^s)
        fun writeln s = (write s; write "\n")
        fun writelist [] = ()
          | writelist (s::ss) = (writeln s; writelist ss)
        fun str i = string_of_int i
        val (arity, rules) = adjust_rules rules
        val rules = group_rules rules
        val constants = Inttab.keys arity
        fun arity_of c = Inttab.lookup arity c
        fun rep_str s n = implode (rep n s)
        fun indexed s n = s^(str n)
        fun section n = if n = 0 then [] else (section (n-1))@[n-1]
        fun make_show c = 
            let
                val args = section (the (arity_of c))
            in
                "  show ("^(indexed "C" c)^(implode (map (indexed " a") args))^") = "
                ^"\""^(indexed "C" c)^"\""^(implode (map (fn a => "++(show "^(indexed "a" a)^")") args))
            end
        fun default_case c = 
            let
                val args = implode (map (indexed " x") (section (the (arity_of c))))
            in
                (indexed "c" c)^args^" = "^(indexed "C" c)^args
            end
        val _ = writelist [        
                "module "^name^" where",
                "",
                "data Term = Const Integer | App Term Term | Abs (Term -> Term)",
                "         "^(implode (map (fn c => " | C"^(str c)^(rep_str " Term" (the (arity_of c)))) constants)),
                "",
                "instance Show Term where"]
        val _ = writelist (map make_show constants)
        val _ = writelist [
                "  show (Const c) = \"c\"++(show c)",
                "  show (App a b) = \"A\"++(show a)++(show b)",
                "  show (Abs _) = \"L\"",
                ""]
        val _ = writelist [
                "app (Abs a) b = a b",
                "app a b = App a b",
                "",
                "calc s c = writeFile s (show c)",
                ""]
        fun list_group c = (writelist (case Inttab.lookup rules c of 
                                           NONE => [default_case c, ""] 
                                         | SOME (rs as ((PConst (_, []), _)::rs')) => 
                                           if not (null rs') then raise Compile "multiple declaration of constant"
                                           else (map (print_rule arity_of) rs) @ [""]
                                         | SOME rs => (map (print_rule arity_of) rs) @ [default_case c, ""]))
        val _ = map list_group constants
    in
        (arity, !buffer)
    end

val guid_counter = Unsynchronized.ref 0
fun get_guid () = 
    let
        val c = !guid_counter
        val _ = guid_counter := !guid_counter + 1
    in
        string_of_int (Time.toMicroseconds (Time.now ())) ^ string_of_int c
    end

fun tmp_file s = Path.implode (Path.expand (File.tmp_path (Path.basic s)));

fun writeTextFile name s = File.write (Path.explode name) s

fun fileExists name = ((OS.FileSys.fileSize name; true) handle OS.SysErr _ => false)

fun compile eqs = 
    let
        val _ = if exists (fn (a,_,_) => not (null a)) eqs then raise Compile ("cannot deal with guards") else ()
        val eqs = map (fn (_,b,c) => (b,c)) eqs
        val guid = get_guid ()
        val module = "AMGHC_Prog_"^guid
        val (arity, source) = haskell_prog module eqs
        val module_file = tmp_file (module^".hs")
        val object_file = tmp_file (module^".o")
        val _ = writeTextFile module_file source
        val _ = Isabelle_System.bash ("exec \"$ISABELLE_GHC\" -c " ^ module_file)
        val _ =
          if not (fileExists object_file) then
            raise Compile ("Failure compiling haskell code (ISABELLE_GHC='" ^ getenv "ISABELLE_GHC" ^ "')")
          else ()
    in
        (guid, module_file, arity)      
    end

fun readResultFile name = File.read (Path.explode name) 

fun parse_result arity_of result =
    let
        val result = String.explode result
        fun shift NONE x = SOME x
          | shift (SOME y) x = SOME (y*10 + x)
        fun parse_int' x (#"0"::rest) = parse_int' (shift x 0) rest
          | parse_int' x (#"1"::rest) = parse_int' (shift x 1) rest
          | parse_int' x (#"2"::rest) = parse_int' (shift x 2) rest
          | parse_int' x (#"3"::rest) = parse_int' (shift x 3) rest
          | parse_int' x (#"4"::rest) = parse_int' (shift x 4) rest
          | parse_int' x (#"5"::rest) = parse_int' (shift x 5) rest
          | parse_int' x (#"6"::rest) = parse_int' (shift x 6) rest
          | parse_int' x (#"7"::rest) = parse_int' (shift x 7) rest
          | parse_int' x (#"8"::rest) = parse_int' (shift x 8) rest
          | parse_int' x (#"9"::rest) = parse_int' (shift x 9) rest
          | parse_int' x rest = (x, rest)
        fun parse_int rest = parse_int' NONE rest

        fun parse (#"C"::rest) = 
            (case parse_int rest of 
                 (SOME c, rest) => 
                 let
                     val (args, rest) = parse_list (the (arity_of c)) rest
                     fun app_args [] t = t
                       | app_args (x::xs) t = app_args xs (App (t, x))
                 in
                     (app_args args (Const c), rest)
                 end                 
               | (NONE, _) => raise Run "parse C")
          | parse (#"c"::rest) = 
            (case parse_int rest of
                 (SOME c, rest) => (Const c, rest)
               | _ => raise Run "parse c")
          | parse (#"A"::rest) = 
            let
                val (a, rest) = parse rest
                val (b, rest) = parse rest
            in
                (App (a,b), rest)
            end
          | parse (#"L"::_) = raise Run "there may be no abstraction in the result"
          | parse _ = raise Run "invalid result"
        and parse_list n rest = 
            if n = 0 then 
                ([], rest) 
            else 
                let 
                    val (x, rest) = parse rest
                    val (xs, rest) = parse_list (n-1) rest
                in
                    (x::xs, rest)
                end
        val (parsed, rest) = parse result
        fun is_blank (#" "::rest) = is_blank rest
          | is_blank (#"\n"::rest) = is_blank rest
          | is_blank [] = true
          | is_blank _ = false
    in
        if is_blank rest then parsed else raise Run "non-blank suffix in result file"   
    end

fun run (guid, module_file, arity) t = 
    let
        val _ = if check_freevars 0 t then () else raise Run ("can only compute closed terms")
        fun arity_of c = Inttab.lookup arity c                   
        val callguid = get_guid()
        val module = "AMGHC_Prog_"^guid
        val call = module^"_Call_"^callguid
        val result_file = tmp_file (module^"_Result_"^callguid^".txt")
        val call_file = tmp_file (call^".hs")
        val term = print_term arity_of 0 t
        val call_source = "module "^call^" where\n\nimport "^module^"\n\ncall = "^module^".calc \""^result_file^"\" ("^term^")"
        val _ = writeTextFile call_file call_source
        val _ = Isabelle_System.bash ("exec \"$ISABELLE_GHC\" -e \""^call^".call\" "^module_file^" "^call_file)
        val result = readResultFile result_file handle IO.Io _ =>
          raise Run ("Failure running haskell compiler (ISABELLE_GHC='" ^ getenv "ISABELLE_GHC" ^ "')")
        val t' = parse_result arity_of result
        val _ = OS.FileSys.remove call_file
        val _ = OS.FileSys.remove result_file
    in
        t'
    end

end

