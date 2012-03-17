(*  Title:      HOL/Matrix/Compute_Oracle/am_sml.ML
    Author:     Steven Obua

TODO: "parameterless rewrite cannot be used in pattern": In a lot of
cases it CAN be used, and these cases should be handled
properly; right now, all cases raise an exception. 
*)

signature AM_SML = 
sig
  include ABSTRACT_MACHINE
  val save_result : (string * term) -> unit
  val set_compiled_rewriter : (term -> term) -> unit
  val list_nth : 'a list * int -> 'a
  val dump_output : (string option) Unsynchronized.ref 
end

structure AM_SML : AM_SML = struct

open AbstractMachine;

val dump_output = Unsynchronized.ref (NONE: string option)

type program = term Inttab.table * (term -> term)

val saved_result = Unsynchronized.ref (NONE:(string*term)option)

fun save_result r = (saved_result := SOME r)

val list_nth = List.nth

val compiled_rewriter = Unsynchronized.ref (NONE:(term -> term)Option.option)

fun set_compiled_rewriter r = (compiled_rewriter := SOME r)

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

(* We also need to find out the maximal toplevel arity of each function constant *)
fun collect_pattern_toplevel_arity PVar arity = raise Compile "internal error: collect_pattern_toplevel_arity"
  | collect_pattern_toplevel_arity (PConst (c, args)) arity = update_arity arity c (length args)

local
fun collect applevel (Var _) arity = arity
  | collect applevel (Const c) arity = update_arity arity c applevel
  | collect applevel (Abs m) arity = collect 0 m arity
  | collect applevel (App (a,b)) arity = collect 0 b (collect (applevel + 1) a arity)
in
fun collect_term_arity t arity = collect 0 t arity
end

fun collect_guard_arity (Guard (a,b)) arity  = collect_term_arity b (collect_term_arity a arity)


fun rep n x = if n < 0 then raise Compile "internal error: rep" else if n = 0 then [] else x::(rep (n-1) x)

fun beta (Const c) = Const c
  | beta (Var i) = Var i
  | beta (App (Abs m, b)) = beta (unlift 0 (subst 0 m (lift 0 b)))
  | beta (App (a, b)) = 
    (case beta a of
         Abs m => beta (App (Abs m, b))
       | a => App (a, beta b))
  | beta (Abs m) = Abs (beta m)
  | beta (Computed t) = Computed t
and subst x (Const c) t = Const c
  | subst x (Var i) t = if i = x then t else Var i
  | subst x (App (a,b)) t = App (subst x a t, subst x b t)
  | subst x (Abs m) t = Abs (subst (x+1) m (lift 0 t))
and lift level (Const c) = Const c
  | lift level (App (a,b)) = App (lift level a, lift level b)
  | lift level (Var i) = if i < level then Var i else Var (i+1)
  | lift level (Abs m) = Abs (lift (level + 1) m)
and unlift level (Const c) = Const c
  | unlift level (App (a, b)) = App (unlift level a, unlift level b)
  | unlift level (Abs m) = Abs (unlift (level+1) m)
  | unlift level (Var i) = if i < level then Var i else Var (i-1)

fun nlift level n (Var m) = if m < level then Var m else Var (m+n) 
  | nlift level n (Const c) = Const c
  | nlift level n (App (a,b)) = App (nlift level n a, nlift level n b)
  | nlift level n (Abs b) = Abs (nlift (level+1) n b)

fun subst_const (c, t) (Const c') = if c = c' then t else Const c'
  | subst_const _ (Var i) = Var i
  | subst_const ct (App (a, b)) = App (subst_const ct a, subst_const ct b)
  | subst_const ct (Abs m) = Abs (subst_const ct m)

(* Remove all rules that are just parameterless rewrites. This is necessary because SML does not allow functions with no parameters. *)
fun inline_rules rules =
  let
    fun term_contains_const c (App (a, b)) = term_contains_const c a orelse term_contains_const c b
      | term_contains_const c (Abs m) = term_contains_const c m
      | term_contains_const c (Var _) = false
      | term_contains_const c (Const c') = (c = c')
    fun find_rewrite [] = NONE
      | find_rewrite ((prems, PConst (c, []), r) :: _) = 
          if check_freevars 0 r then 
            if term_contains_const c r then 
              raise Compile "parameterless rewrite is caught in cycle"
            else if not (null prems) then
              raise Compile "parameterless rewrite may not be guarded"
            else
              SOME (c, r) 
          else raise Compile "unbound variable on right hand side or guards of rule"
      | find_rewrite (_ :: rules) = find_rewrite rules
    fun remove_rewrite _ [] = []
      | remove_rewrite (cr as (c, r)) ((rule as (prems', PConst (c', args), r')) :: rules) = 
          if c = c' then 
            if null args andalso r = r' andalso null prems' then remove_rewrite cr rules 
            else raise Compile "incompatible parameterless rewrites found"
          else
            rule :: remove_rewrite cr rules
      | remove_rewrite cr (r :: rs) = r :: remove_rewrite cr rs
    fun pattern_contains_const c (PConst (c', args)) = c = c' orelse exists (pattern_contains_const c) args
      | pattern_contains_const c (PVar) = false
    fun inline_rewrite (ct as (c, _)) (prems, p, r) = 
        if pattern_contains_const c p then 
          raise Compile "parameterless rewrite cannot be used in pattern"
        else (map (fn (Guard (a, b)) => Guard (subst_const ct a, subst_const ct b)) prems, p, subst_const ct r)
    fun inline inlined rules =
      case find_rewrite rules of 
          NONE => (Inttab.make inlined, rules)
        | SOME ct => 
            let
              val rules = map (inline_rewrite ct) (remove_rewrite ct rules)
              val inlined = ct :: (map o apsnd) (subst_const ct) inlined
            in inline inlined rules end
  in
    inline [] rules
  end


(*
   Calculate the arity, the toplevel_arity, and adjust rules so that all toplevel pattern constants have maximal arity.
   Also beta reduce the adjusted right hand side of a rule.   
*)
fun adjust_rules rules = 
    let
        val arity = fold (fn (prems, p, t) => fn arity => fold collect_guard_arity prems (collect_term_arity t (collect_pattern_arity p arity))) rules Inttab.empty
        val toplevel_arity = fold (fn (_, p, _) => fn arity => collect_pattern_toplevel_arity p arity) rules Inttab.empty
        fun arity_of c = the (Inttab.lookup arity c)
        fun test_pattern PVar = ()
          | test_pattern (PConst (c, args)) = if (length args <> arity_of c) then raise Compile ("Constant inside pattern must have maximal arity") else (map test_pattern args; ())
        fun adjust_rule (_, PVar, _) = raise Compile ("pattern may not be a variable")
          | adjust_rule (_, PConst (_, []), _) = raise Compile ("cannot deal with rewrites that take no parameters")
          | adjust_rule (rule as (prems, p as PConst (c, args),t)) = 
            let
                val patternvars_counted = count_patternvars p
                fun check_fv t = check_freevars patternvars_counted t
                val _ = if not (check_fv t) then raise Compile ("unbound variables on right hand side of rule") else () 
                val _ = if not (forall (fn (Guard (a,b)) => check_fv a andalso check_fv b) prems) then raise Compile ("unbound variables in guards") else () 
                val _ = map test_pattern args           
                val len = length args
                val arity = arity_of c
                val lift = nlift 0
                fun addapps_tm n t = if n=0 then t else addapps_tm (n-1) (App (t, Var (n-1)))
                fun adjust_term n t = addapps_tm n (lift n t)
                fun adjust_guard n (Guard (a,b)) = Guard (lift n a, lift n b)
            in
                if len = arity then
                    rule
                else if arity >= len then  
                    (map (adjust_guard (arity-len)) prems, PConst (c, args @ (rep (arity-len) PVar)), adjust_term (arity-len) t)
                else (raise Compile "internal error in adjust_rule")
            end
        fun beta_rule (prems, p, t) = ((prems, p, beta t) handle Match => raise Compile "beta_rule")
    in
        (arity, toplevel_arity, map (beta_rule o adjust_rule) rules)
    end             

fun print_term module arity_of toplevel_arity_of pattern_var_count pattern_lazy_var_count =
let
    fun str x = string_of_int x
    fun protect_blank s = if exists_string Symbol.is_ascii_blank s then "(" ^ s ^")" else s
    val module_prefix = (case module of NONE => "" | SOME s => s^".")                                                                                     
    fun print_apps d f [] = f
      | print_apps d f (a::args) = print_apps d (module_prefix^"app "^(protect_blank f)^" "^(protect_blank (print_term d a))) args
    and print_call d (App (a, b)) args = print_call d a (b::args) 
      | print_call d (Const c) args = 
        (case arity_of c of 
             NONE => print_apps d (module_prefix^"Const "^(str c)) args 
           | SOME 0 => module_prefix^"C"^(str c)
           | SOME a =>
             let
                 val len = length args
             in
                 if a <= len then 
                     let
                         val strict_a = (case toplevel_arity_of c of SOME sa => sa | NONE => a)
                         val _ = if strict_a > a then raise Compile "strict" else ()
                         val s = module_prefix^"c"^(str c)^(implode (map (fn t => " "^(protect_blank (print_term d t))) (List.take (args, strict_a))))
                         val s = s^(implode (map (fn t => " (fn () => "^print_term d t^")") (List.drop (List.take (args, a), strict_a))))
                     in
                         print_apps d s (List.drop (args, a))
                     end
                 else 
                     let
                         fun mk_apps n t = if n = 0 then t else mk_apps (n-1) (App (t, Var (n - 1)))
                         fun mk_lambdas n t = if n = 0 then t else mk_lambdas (n-1) (Abs t)
                         fun append_args [] t = t
                           | append_args (c::cs) t = append_args cs (App (t, c))
                     in
                         print_term d (mk_lambdas (a-len) (mk_apps (a-len) (nlift 0 (a-len) (append_args args (Const c)))))
                     end
             end)
      | print_call d t args = print_apps d (print_term d t) args
    and print_term d (Var x) = 
        if x < d then 
            "b"^(str (d-x-1)) 
        else 
            let
                val n = pattern_var_count - (x-d) - 1
                val x = "x"^(str n)
            in
                if n < pattern_var_count - pattern_lazy_var_count then 
                    x
                else 
                    "("^x^" ())"
            end                                                         
      | print_term d (Abs c) = module_prefix^"Abs (fn b"^(str d)^" => "^(print_term (d + 1) c)^")"
      | print_term d t = print_call d t []
in
    print_term 0 
end

fun section n = if n = 0 then [] else (section (n-1))@[n-1]

fun print_rule gnum arity_of toplevel_arity_of (guards, p, t) = 
    let 
        fun str x = string_of_int x                  
        fun print_pattern top n PVar = (n+1, "x"^(str n))
          | print_pattern top n (PConst (c, [])) = (n, (if top then "c" else "C")^(str c)^(if top andalso gnum > 0 then "_"^(str gnum) else ""))
          | print_pattern top n (PConst (c, args)) = 
            let
                val f = (if top then "c" else "C")^(str c)^(if top andalso gnum > 0 then "_"^(str gnum) else "")
                val (n, s) = print_pattern_list 0 top (n, f) args
            in
                (n, s)
            end
        and print_pattern_list' counter top (n,p) [] = if top then (n,p) else (n,p^")")
          | print_pattern_list' counter top (n, p) (t::ts) = 
            let
                val (n, t) = print_pattern false n t
            in
                print_pattern_list' (counter + 1) top (n, if top then p^" (a"^(str counter)^" as ("^t^"))" else p^", "^t) ts
            end 
        and print_pattern_list counter top (n, p) (t::ts) = 
            let
                val (n, t) = print_pattern false n t
            in
                print_pattern_list' (counter + 1) top (n, if top then p^" (a"^(str counter)^" as ("^t^"))" else p^" ("^t) ts
            end
        val c = (case p of PConst (c, _) => c | _ => raise Match)
        val (n, pattern) = print_pattern true 0 p
        val lazy_vars = the (arity_of c) - the (toplevel_arity_of c)
        fun print_tm tm = print_term NONE arity_of toplevel_arity_of n lazy_vars tm
        fun print_guard (Guard (a,b)) = "term_eq ("^(print_tm a)^") ("^(print_tm b)^")"
        val else_branch = "c"^(str c)^"_"^(str (gnum+1))^(implode (map (fn i => " a"^(str i)) (section (the (arity_of c)))))
        fun print_guards t [] = print_tm t
          | print_guards t (g::gs) = "if ("^(print_guard g)^")"^(implode (map (fn g => " andalso ("^(print_guard g)^")") gs))^" then ("^(print_tm t)^") else "^else_branch
    in
        (if null guards then gnum else gnum+1, pattern^" = "^(print_guards t guards))
    end

fun group_rules rules =
    let
        fun add_rule (r as (_, PConst (c,_), _)) groups =
            let
                val rs = (case Inttab.lookup groups c of NONE => [] | SOME rs => rs)
            in
                Inttab.update (c, r::rs) groups
            end
          | add_rule _ _ = raise Compile "internal error group_rules"
    in
        fold_rev add_rule rules Inttab.empty
    end

fun sml_prog name code rules = 
    let
        val buffer = Unsynchronized.ref ""
        fun write s = (buffer := (!buffer)^s)
        fun writeln s = (write s; write "\n")
        fun writelist [] = ()
          | writelist (s::ss) = (writeln s; writelist ss)
        fun str i = string_of_int i
        val (inlinetab, rules) = inline_rules rules
        val (arity, toplevel_arity, rules) = adjust_rules rules
        val rules = group_rules rules
        val constants = Inttab.keys arity
        fun arity_of c = Inttab.lookup arity c
        fun toplevel_arity_of c = Inttab.lookup toplevel_arity c
        fun rep_str s n = implode (rep n s)
        fun indexed s n = s^(str n)
        fun string_of_tuple [] = ""
          | string_of_tuple (x::xs) = "("^x^(implode (map (fn s => ", "^s) xs))^")"
        fun string_of_args [] = ""
          | string_of_args (x::xs) = x^(implode (map (fn s => " "^s) xs))
        fun default_case gnum c = 
            let
                val leftargs = implode (map (indexed " x") (section (the (arity_of c))))
                val rightargs = section (the (arity_of c))
                val strict_args = (case toplevel_arity_of c of NONE => the (arity_of c) | SOME sa => sa)
                val xs = map (fn n => if n < strict_args then "x"^(str n) else "x"^(str n)^"()") rightargs
                val right = (indexed "C" c)^" "^(string_of_tuple xs)
                val message = "(\"unresolved lazy call: " ^ string_of_int c ^ "\")"
                val right = if strict_args < the (arity_of c) then "raise AM_SML.Run "^message else right               
            in
                (indexed "c" c)^(if gnum > 0 then "_"^(str gnum) else "")^leftargs^" = "^right
            end

        fun eval_rules c = 
            let
                val arity = the (arity_of c)
                val strict_arity = (case toplevel_arity_of c of NONE => arity | SOME sa => sa)
                fun eval_rule n = 
                    let
                        val sc = string_of_int c
                        val left = fold (fn i => fn s => "AbstractMachine.App ("^s^(indexed ", x" i)^")") (section n) ("AbstractMachine.Const "^sc)
                        fun arg i = 
                            let
                                val x = indexed "x" i
                                val x = if i < n then "(eval bounds "^x^")" else x
                                val x = if i < strict_arity then x else "(fn () => "^x^")"
                            in
                                x
                            end
                        val right = "c"^sc^" "^(string_of_args (map arg (section arity)))
                        val right = fold_rev (fn i => fn s => "Abs (fn "^(indexed "x" i)^" => "^s^")") (List.drop (section arity, n)) right             
                        val right = if arity > 0 then right else "C"^sc
                    in
                        "  | eval bounds ("^left^") = "^right
                    end
            in
                map eval_rule (rev (section (arity + 1)))
            end

        fun convert_computed_rules (c: int) : string list = 
            let
                val arity = the (arity_of c)
                fun eval_rule () = 
                    let
                        val sc = string_of_int c
                        val left = fold (fn i => fn s => "AbstractMachine.App ("^s^(indexed ", x" i)^")") (section arity) ("AbstractMachine.Const "^sc)
                        fun arg i = "(convert_computed "^(indexed "x" i)^")" 
                        val right = "C"^sc^" "^(string_of_tuple (map arg (section arity)))              
                        val right = if arity > 0 then right else "C"^sc
                    in
                        "  | convert_computed ("^left^") = "^right
                    end
            in
                [eval_rule ()]
            end
        
        fun mk_constr_type_args n = if n > 0 then " of Term "^(rep_str " * Term" (n-1)) else ""
        val _ = writelist [                   
                "structure "^name^" = struct",
                "",
                "datatype Term = Const of int | App of Term * Term | Abs of (Term -> Term)",
                "         "^(implode (map (fn c => " | C"^(str c)^(mk_constr_type_args (the (arity_of c)))) constants)),
                ""]
        fun make_constr c argprefix = "(C"^(str c)^" "^(string_of_tuple (map (fn i => argprefix^(str i)) (section (the (arity_of c)))))^")"
        fun make_term_eq c = "  | term_eq "^(make_constr c "a")^" "^(make_constr c "b")^" = "^
                             (case the (arity_of c) of 
                                  0 => "true"
                                | n => 
                                  let 
                                      val eqs = map (fn i => "term_eq a"^(str i)^" b"^(str i)) (section n)
                                      val (eq, eqs) = (List.hd eqs, map (fn s => " andalso "^s) (List.tl eqs))
                                  in
                                      eq^(implode eqs)
                                  end)
        val _ = writelist [
                "fun term_eq (Const c1) (Const c2) = (c1 = c2)",
                "  | term_eq (App (a1,a2)) (App (b1,b2)) = term_eq a1 b1 andalso term_eq a2 b2"]
        val _ = writelist (map make_term_eq constants)          
        val _ = writelist [
                "  | term_eq _ _ = false",
                "" 
                ] 
        val _ = writelist [
                "fun app (Abs a) b = a b",
                "  | app a b = App (a, b)",
                ""]     
        fun defcase gnum c = (case arity_of c of NONE => [] | SOME a => if a > 0 then [default_case gnum c] else [])
        fun writefundecl [] = () 
          | writefundecl (x::xs) = writelist ((("and "^x)::(map (fn s => "  | "^s) xs)))
        fun list_group c = (case Inttab.lookup rules c of 
                                NONE => [defcase 0 c]
                              | SOME rs => 
                                let
                                    val rs = 
                                        fold
                                            (fn r => 
                                             fn rs =>
                                                let 
                                                    val (gnum, l, rs) = 
                                                        (case rs of 
                                                             [] => (0, [], []) 
                                                           | (gnum, l)::rs => (gnum, l, rs))
                                                    val (gnum', r) = print_rule gnum arity_of toplevel_arity_of r 
                                                in 
                                                    if gnum' = gnum then 
                                                        (gnum, r::l)::rs
                                                    else
                                                        let
                                                            val args = implode (map (fn i => " a"^(str i)) (section (the (arity_of c))))
                                                            fun gnumc g = if g > 0 then "c"^(str c)^"_"^(str g)^args else "c"^(str c)^args
                                                            val s = gnumc (gnum) ^ " = " ^ gnumc (gnum') 
                                                        in
                                                            (gnum', [])::(gnum, s::r::l)::rs
                                                        end
                                                end)
                                        rs []
                                    val rs = (case rs of [] => [(0,defcase 0 c)] | (gnum,l)::rs => (gnum, (defcase gnum c)@l)::rs)
                                in
                                    rev (map (fn z => rev (snd z)) rs)
                                end)
        val _ = map (fn z => (map writefundecl z; writeln "")) (map list_group constants)
        val _ = writelist [
                "fun convert (Const i) = AM_SML.Const i",
                "  | convert (App (a, b)) = AM_SML.App (convert a, convert b)",
                "  | convert (Abs _) = raise AM_SML.Run \"no abstraction in result allowed\""]  
        fun make_convert c = 
            let
                val args = map (indexed "a") (section (the (arity_of c)))
                val leftargs = 
                    case args of
                        [] => ""
                      | (x::xs) => "("^x^(implode (map (fn s => ", "^s) xs))^")"
                val args = map (indexed "convert a") (section (the (arity_of c)))
                val right = fold (fn x => fn s => "AM_SML.App ("^s^", "^x^")") args ("AM_SML.Const "^(str c))
            in
                "  | convert (C"^(str c)^" "^leftargs^") = "^right
            end                 
        val _ = writelist (map make_convert constants)
        val _ = writelist [
                "",
                "fun convert_computed (AbstractMachine.Abs b) = raise AM_SML.Run \"no abstraction in convert_computed allowed\"",
                "  | convert_computed (AbstractMachine.Var i) = raise AM_SML.Run \"no bound variables in convert_computed allowed\""]
        val _ = map (writelist o convert_computed_rules) constants
        val _ = writelist [
                "  | convert_computed (AbstractMachine.Const c) = Const c",
                "  | convert_computed (AbstractMachine.App (a, b)) = App (convert_computed a, convert_computed b)",
                "  | convert_computed (AbstractMachine.Computed a) = raise AM_SML.Run \"no nesting in convert_computed allowed\""] 
        val _ = writelist [
                "",
                "fun eval bounds (AbstractMachine.Abs m) = Abs (fn b => eval (b::bounds) m)",
                "  | eval bounds (AbstractMachine.Var i) = AM_SML.list_nth (bounds, i)"]
        val _ = map (writelist o eval_rules) constants
        val _ = writelist [
                "  | eval bounds (AbstractMachine.App (a, b)) = app (eval bounds a) (eval bounds b)",
                "  | eval bounds (AbstractMachine.Const c) = Const c",
                "  | eval bounds (AbstractMachine.Computed t) = convert_computed t"]                
        val _ = writelist [             
                "",
                "fun export term = AM_SML.save_result (\""^code^"\", convert term)",
                "",
                "val _ = AM_SML.set_compiled_rewriter (fn t => (convert (eval [] t)))",
                "",
                "end"]
    in
        (inlinetab, !buffer)
    end

val guid_counter = Unsynchronized.ref 0
fun get_guid () = 
    let
        val c = !guid_counter
        val _ = guid_counter := !guid_counter + 1
    in
        string_of_int (Time.toMicroseconds (Time.now ())) ^ string_of_int c
    end


fun writeTextFile name s = File.write (Path.explode name) s

fun use_source src = use_text ML_Env.local_context (1, "") false src
    
fun compile rules = 
    let
        val guid = get_guid ()
        val code = Real.toString (random ())
        val name = "AMSML_"^guid
        val (inlinetab, source) = sml_prog name code rules
        val _ = case !dump_output of NONE => () | SOME p => writeTextFile p source
        val _ = compiled_rewriter := NONE
        val _ = use_source source
    in
        case !compiled_rewriter of 
            NONE => raise Compile "broken link to compiled function"
          | SOME compiled_fun => (inlinetab, compiled_fun)
    end

fun run (inlinetab, compiled_fun) t = 
    let 
        val _ = if check_freevars 0 t then () else raise Run ("can only compute closed terms")
        fun inline (Const c) = (case Inttab.lookup inlinetab c of NONE => Const c | SOME t => t)
          | inline (Var i) = Var i
          | inline (App (a, b)) = App (inline a, inline b)
          | inline (Abs m) = Abs (inline m)
          | inline (Computed t) = Computed t
    in
        compiled_fun (beta (inline t))
    end 

end
