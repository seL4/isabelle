(* Title:       HOL/datatype.ML
   ID:          $Id$
   Author:      Max Breitling, Carsten Clasohm, Tobias Nipkow, Norbert Voelker,
                Konrad Slind
   Copyright 1995 TU Muenchen
*)


(*used for constructor parameters*)
datatype dt_type = dtVar of string |
  dtTyp of dt_type list * string |
  dtRek of dt_type list * string;

structure Datatype =
struct
local 

val mysort = sort;
open ThyParse HOLogic;
exception Impossible;
exception RecError of string;

val is_dtRek = (fn dtRek _ => true  |  _  => false);
fun opt_parens s = if s = "" then "" else enclose "(" ")" s; 

(* ----------------------------------------------------------------------- *)
(* Derivation of the primrec combinator application from the equations     *)

(* substitute fname(ls,xk,rs) by yk(ls,rs) in t for (xk,yk) in pairs  *) 

fun subst_apps (_,_) [] t = t
  | subst_apps (fname,rpos) pairs t =
    let 
    fun subst (Abs(a,T,t)) = Abs(a,T,subst t)
      | subst (funct $ body) = 
        let val (f,b) = strip_comb (funct$body)
        in 
          if is_Const f andalso fst(dest_Const f) = fname 
            then 
              let val (ls,rest) = (take(rpos,b), drop(rpos,b));
                val (xk,rs) = (hd rest,tl rest)
                  handle LIST _ => raise RecError "not enough arguments \
                   \ in recursive application on rhs"
              in 
                (case assoc (pairs,xk) of 
                   None   => list_comb(f, map subst b)
                 | Some U => list_comb(U, map subst (ls @ rs)))
              end
          else list_comb(f, map subst b)
        end
      | subst(t) = t
    in subst t end;
  
(* abstract rhs *)

fun abst_rec (fname,rpos,tc,ls,cargs,rs,rhs) =       
  let val rargs = (map #1 o 
                   (filter (fn (a,T) => is_dtRek T))) (cargs ~~ tc);
      val subs = map (fn (s,T) => (s,dummyT))
                   (rev(rename_wrt_term rhs rargs));
      val subst_rhs = subst_apps (fname,rpos)
                        (map Free rargs ~~ map Free subs) rhs;
  in 
      list_abs_free (cargs @ subs @ ls @ rs, subst_rhs) 
  end;

(* parsing the prim rec equations *)

fun dest_eq ( Const("Trueprop",_) $ (Const ("op =",_) $ lhs $ rhs))
                 = (lhs, rhs)
   | dest_eq _ = raise RecError "not a proper equation"; 

fun dest_rec eq = 
  let val (lhs,rhs) = dest_eq eq; 
    val (name,args) = strip_comb lhs; 
    val (ls',rest)  = take_prefix is_Free args; 
    val (middle,rs') = take_suffix is_Free rest;
    val rpos = length ls';
    val (c,cargs') = strip_comb (hd middle)
      handle LIST "hd" => raise RecError "constructor missing";
    val (ls,cargs,rs) = (map dest_Free ls', map dest_Free cargs'
                         , map dest_Free rs')
      handle TERM ("dest_Free",_) => 
          raise RecError "constructor has illegal argument in pattern";
  in 
    if length middle > 1 then 
      raise RecError "more than one non-variable in pattern"
    else if not(null(findrep (map fst (ls @ rs @ cargs)))) then 
      raise RecError "repeated variable name in pattern" 
         else (fst(dest_Const name) handle TERM _ => 
               raise RecError "function is not declared as constant in theory"
                 ,rpos,ls,fst( dest_Const c),cargs,rs,rhs)
  end; 

(* check function specified for all constructors and sort function terms *)

fun check_and_sort (n,its) = 
  if length its = n 
    then map snd (mysort (fn ((i : int,_),(j,_)) => i<j) its)
  else raise error "Primrec definition error:\n\
   \Please give an equation for every constructor";

(* translate rec equations into function arguments suitable for rec comb *)
(* theory parameter needed for printing error messages                   *) 

fun trans_recs _ _ [] = error("No primrec equations.")
  | trans_recs thy cs' (eq1::eqs) = 
    let val (name1,rpos1,ls1,_,_,_,_) = dest_rec eq1
      handle RecError s =>
        error("Primrec definition error: " ^ s ^ ":\n" 
              ^ "   " ^ Sign.string_of_term (sign_of thy) eq1);
      val tcs = map (fn (_,c,T,_,_) => (c,T)) cs';  
      val cs = map fst tcs;
      fun trans_recs' _ [] = []
        | trans_recs' cis (eq::eqs) = 
          let val (name,rpos,ls,c,cargs,rs,rhs) = dest_rec eq; 
            val tc = assoc(tcs,c);
            val i = (1 + find (c,cs))  handle LIST "find" => 0; 
          in
          if name <> name1 then 
            raise RecError "function names inconsistent"
          else if rpos <> rpos1 then 
            raise RecError "position of rec. argument inconsistent"
          else if i = 0 then 
            raise RecError "illegal argument in pattern" 
          else if i mem cis then
            raise RecError "constructor already occured as pattern "
               else (i,abst_rec (name,rpos,the tc,ls,cargs,rs,rhs))
                     :: trans_recs' (i::cis) eqs 
          end
          handle RecError s =>
                error("Primrec definition error\n" ^ s ^ "\n" 
                      ^ "   " ^ Sign.string_of_term (sign_of thy) eq);
    in (  name1, ls1
        , check_and_sort (length cs, trans_recs' [] (eq1::eqs)))
    end ;

in
  fun add_datatype (typevars, tname, cons_list') thy = 
    let
      val dummy = if length cons_list' < dtK then ()
                  else require_thy thy "Nat" "datatype";
      
      fun typid(dtRek(_,id)) = id
        | typid(dtVar s) = implode (tl (explode s))
        | typid(dtTyp(_,id)) = id;

      fun index_vnames(vn::vns,tab) =
            (case assoc(tab,vn) of
               None => if vn mem vns
                       then (vn^"1") :: index_vnames(vns,(vn,2)::tab)
                       else vn :: index_vnames(vns,tab)
             | Some(i) => (vn^(string_of_int i)) ::
                          index_vnames(vns,(vn,i+1)::tab))
        | index_vnames([],tab) = [];

      fun mk_var_names types = index_vnames(map typid types,[]);

      (*search for free type variables and convert recursive *)
      fun analyse_types (cons, types, syn) =
        let fun analyse(t as dtVar v) =
                  if t mem typevars then t
                  else error ("Free type variable " ^ v ^ " on rhs.")
              | analyse(dtTyp(typl,s)) =
                  if tname <> s then dtTyp(analyses typl, s)
                  else if typevars = typl then dtRek(typl, s)
                       else error (s ^ " used in different ways")
              | analyse(dtRek _) = raise Impossible
            and analyses ts = map analyse ts;
        in (cons, Syntax.const_name cons syn, analyses types,
            mk_var_names types, syn)
        end;

     (*test if all elements are recursive, i.e. if the type is empty*)
      
      fun non_empty (cs : ('a * 'b * dt_type list * 'c *'d) list) = 
        not(forall (exists is_dtRek o #3) cs) orelse
        error("Empty datatype not allowed!");

      val cons_list = map analyse_types cons_list';
      val dummy = non_empty cons_list;
      val num_of_cons = length cons_list;

     (* Auxiliary functions to construct argument and equation lists *)

     (*generate 'var_n, ..., var_m'*)
      fun Args(var, delim, n, m) = 
        space_implode delim (map (fn n => var^string_of_int(n)) (n upto m));

      fun C_exp name vns = name ^ opt_parens(space_implode ") (" vns);

     (*Arg_eqs([x1,...,xn],[y1,...,yn]) = "x1 = y1 & ... & xn = yn" *)
      fun arg_eqs vns vns' =
        let fun mkeq(x,x') = x ^ "=" ^ x'
        in space_implode " & " (ListPair.map mkeq (vns,vns')) end;

     (*Pretty printers for type lists;
       pp_typlist1: parentheses, pp_typlist2: brackets*)
      fun pp_typ (dtVar s) = "(" ^ s ^ "::term)"
        | pp_typ (dtTyp (typvars, id)) =
          if null typvars then id else (pp_typlist1 typvars) ^ id
        | pp_typ (dtRek (typvars, id)) = (pp_typlist1 typvars) ^ id
      and
        pp_typlist' ts = commas (map pp_typ ts)
      and
        pp_typlist1 ts = if null ts then "" else parens (pp_typlist' ts);

      fun pp_typlist2 ts = if null ts then "" else brackets (pp_typlist' ts);

     (* Generate syntax translation for case rules *)
      fun calc_xrules c_nr y_nr ((_, name, _, vns, _) :: cs) = 
        let val arity = length vns;
          val body  = "z" ^ string_of_int(c_nr);
          val args1 = if arity=0 then ""
                      else " " ^ Args ("y", " ", y_nr, y_nr+arity-1);
          val args2 = if arity=0 then ""
                      else "(% " ^ Args ("y", " ", y_nr, y_nr+arity-1) 
                        ^ ". ";
          val (rest1,rest2) = 
            if null cs then ("","")
            else let val (h1, h2) = calc_xrules (c_nr+1) (y_nr+arity) cs
            in (" | " ^ h1, " " ^ h2) end;
        in (name ^ args1 ^ " => " ^ body ^ rest1,
            args2 ^ body ^ (if args2 = "" then "" else ")") ^ rest2)
        end
        | calc_xrules _ _ [] = raise Impossible;
      
      val xrules =
        let val (first_part, scnd_part) = calc_xrules 1 1 cons_list
        in [Syntax.<-> (("logic", "case x of " ^ first_part),
                        ("logic", tname ^ "_case " ^ scnd_part ^ " x"))]
        end;

     (*type declarations for constructors*)
      fun const_type (id, _, typlist, _, syn) =
        (id,  
         (if null typlist then "" else pp_typlist2 typlist ^ " => ") ^
            pp_typlist1 typevars ^ tname, syn);


      fun assumpt (dtRek _ :: ts, v :: vs ,found) =
        let val h = if found then ";P(" ^ v ^ ")" else "[| P(" ^ v ^ ")"
        in h ^ (assumpt (ts, vs, true)) end
        | assumpt (t :: ts, v :: vs, found) = assumpt (ts, vs, found)
      | assumpt ([], [], found) = if found then "|] ==>" else ""
        | assumpt _ = raise Impossible;

      fun t_inducting ((_, name, types, vns, _) :: cs) =
        let
          val h = if null types then " P(" ^ name ^ ")"
                  else " !!" ^ (space_implode " " vns) ^ "." ^
                    (assumpt (types, vns, false)) ^
                    "P(" ^ C_exp name vns ^ ")";
          val rest = t_inducting cs;
        in if rest = "" then h else h ^ "; " ^ rest end
        | t_inducting [] = "";

      fun t_induct cl typ_name =
        "[|" ^ t_inducting cl ^ "|] ==> P(" ^ typ_name ^ ")";

      fun gen_typlist typevar f ((_, _, ts, _, _) :: cs) =
        let val h = if (length ts) > 0
                      then pp_typlist2(f ts) ^ "=>"
                    else ""
        in h ^ typevar ^  "," ^ (gen_typlist typevar f cs) end
        | gen_typlist _ _ [] = "";


(* -------------------------------------------------------------------- *)
(* The case constant and rules                                          *)
                
      val t_case = tname ^ "_case";

      fun case_rule n (id, name, _, vns, _) =
        let val args = if vns = [] then "" else " " ^ space_implode " " vns
        in (t_case ^ "_" ^ id,
            t_case ^ " " ^ Args("f", " ", 1, num_of_cons)
            ^ " (" ^ name ^ args ^ ") = f"^string_of_int(n) ^ args)
        end

      fun case_rules n (c :: cs) = case_rule n c :: case_rules(n+1) cs
        | case_rules _ [] = [];

      val datatype_arity = length typevars;

      val types = [(tname, datatype_arity, NoSyn)];

      val arities = 
        let val term_list = replicate datatype_arity termS;
        in [(tname, term_list, termS)] 
        end;

      val datatype_name = pp_typlist1 typevars ^ tname;

      val new_tvar_name = variant (map (fn dtVar s => s) typevars) "'z";

      val case_const =
        (t_case,
         "[" ^ gen_typlist new_tvar_name I cons_list 
         ^  pp_typlist1 typevars ^ tname ^ "] =>" ^ new_tvar_name^"::term",
         NoSyn);

      val rules_case = case_rules 1 cons_list;

(* -------------------------------------------------------------------- *)
(* The prim-rec combinator                                              *) 

      val t_rec = tname ^ "_rec"

(* adding type variables for dtRek types to end of list of dt_types      *)   

      fun add_reks ts = 
        ts @ map (fn _ => dtVar new_tvar_name) (filter is_dtRek ts); 

(* positions of the dtRek types in a list of dt_types, starting from 1  *)
      fun rek_vars ts vns = map #2 (filter (is_dtRek o fst) (ts ~~ vns))

      fun rec_rule n (id,name,ts,vns,_) = 
        let val args = opt_parens(space_implode ") (" vns)
          val fargs = opt_parens(Args("f", ") (", 1, num_of_cons))
          fun rarg vn = t_rec ^ fargs ^ " (" ^ vn ^ ")"
          val rargs = opt_parens(space_implode ") ("
                                 (map rarg (rek_vars ts vns)))
        in
          (t_rec ^ "_" ^ id,
           t_rec ^ fargs ^ " (" ^ name ^ args ^ ") = f"
           ^ string_of_int(n) ^ args ^ rargs)
        end

      fun rec_rules n (c::cs) = rec_rule n c :: rec_rules (n+1) cs 
        | rec_rules _ [] = [];

      val rec_const =
        (t_rec,
         "[" ^ (gen_typlist new_tvar_name add_reks cons_list) 
         ^ (pp_typlist1 typevars) ^ tname ^ "] =>" ^ new_tvar_name^"::term",
         NoSyn);

      val rules_rec = rec_rules 1 cons_list

(* -------------------------------------------------------------------- *)
      val consts = 
        map const_type cons_list
        @ (if num_of_cons < dtK then []
           else [(tname ^ "_ord", datatype_name ^ "=>nat", NoSyn)])
        @ [case_const,rec_const];


      fun Ci_ing ((id, name, _, vns, _) :: cs) =
           if null vns then Ci_ing cs
           else let val vns' = variantlist(vns,vns)
                in ("inject_" ^ id,
                    "(" ^ (C_exp name vns) ^ "=" ^ (C_exp name vns')
                    ^ ") = (" ^ (arg_eqs vns vns') ^ ")") :: (Ci_ing cs)
                end
        | Ci_ing [] = [];

      fun Ci_negOne (id1,name1,_,vns1,_) (id2,name2,_,vns2,_) =
            let val vns2' = variantlist(vns2,vns1)
                val ax = C_exp name1 vns1 ^ "~=" ^ C_exp name2 vns2'
        in (id1 ^ "_not_" ^ id2, ax) end;

      fun Ci_neg1 [] = []
        | Ci_neg1 (c1::cs) = (map (Ci_negOne c1) cs) @ Ci_neg1 cs;

      fun suc_expr n = 
        if n=0 then "0" else "Suc(" ^ suc_expr(n-1) ^ ")";

      fun Ci_neg2() =
        let val ord_t = tname ^ "_ord";
          val cis = ListPair.zip (cons_list, 0 upto (num_of_cons - 1))
          fun Ci_neg2equals ((id, name, _, vns, _), n) =
            let val ax = ord_t ^ "(" ^ (C_exp name vns) ^ ") = " ^ (suc_expr n)
            in (ord_t ^ "_" ^ id, ax) end
        in (ord_t ^ "_distinct", ord_t^"(x) ~= "^ord_t^"(y) ==> x ~= y") ::
          (map Ci_neg2equals cis)
        end;

      val rules_distinct = if num_of_cons < dtK then Ci_neg1 cons_list
                           else Ci_neg2();

      val rules_inject = Ci_ing cons_list;

      val rule_induct = (tname ^ "_induct", t_induct cons_list tname);

      val rules = rule_induct ::
        (rules_inject @ rules_distinct @ rules_case @ rules_rec);

      fun add_primrec eqns thy =
        let val rec_comb = Const(t_rec,dummyT)
          val teqns = map (fn neq => snd(read_axm (sign_of thy) neq)) eqns
          val (fname,ls,fns) = trans_recs thy cons_list teqns
          val rhs = 
            list_abs_free
            (ls @ [(tname,dummyT)]
             ,list_comb(rec_comb
                        , fns @ map Bound (0 ::(length ls downto 1))));
          val sg = sign_of thy;
          val defpair = (fname ^ "_" ^ tname ^ "_def",
                         Logic.mk_equals (Const(fname,dummyT), rhs))
          val defpairT as (_, _ $ Const(_,T) $ _ ) = inferT_axm sg defpair;
          val varT = Type.varifyT T;
          val ftyp = the (Sign.const_type sg fname);
        in add_defs_i [defpairT] thy end;

    in
      (thy |> add_types types
           |> add_arities arities
           |> add_consts consts
           |> add_trrules xrules
           |> add_axioms rules, add_primrec)
    end
end
end

(*
Informal description of functions used in datatype.ML for the Isabelle/HOL
implementation of prim. rec. function definitions. (N. Voelker, Feb. 1995) 

* subst_apps (fname,rpos) pairs t:
   substitute the term 
       fname(ls,xk,rs) 
   by 
      yk(ls,rs) 
   in t for (xk,yk) in pairs, where rpos = length ls. 
   Applied with : 
     fname = function name 
     rpos = position of recursive argument 
     pairs = list of pairs (xk,yk), where 
          xk are the rec. arguments of the constructor in the pattern,
          yk is a variable with name derived from xk 
     t = rhs of equation 

* abst_rec (fname,rpos,tc,ls,cargs,rs,rhs)
  - filter recursive arguments from constructor arguments cargs,
  - perform substitutions on rhs, 
  - derive list subs of new variable names yk for use in subst_apps, 
  - abstract rhs with respect to cargs, subs, ls and rs. 

* dest_eq t 
  destruct a term denoting an equation into lhs and rhs. 

* dest_req eq 
  destruct an equation of the form 
      name (vl1..vlrpos, Ci(vi1..vin), vr1..vrn) = rhs
  into 
  - function name  (name) 
  - position of the first non-variable parameter  (rpos)
  - the list of first rpos parameters (ls = [vl1..vlrpos]) 
  - the constructor (fst( dest_Const c) = Ci)
  - the arguments of the constructor (cargs = [vi1..vin])
  - the rest of the variables in the pattern (rs = [vr1..vrn])
  - the right hand side of the equation (rhs).  
 
* check_and_sort (n,its)
  check that  n = length its holds, and sort elements of its by 
  first component. 

* trans_recs thy cs' (eq1::eqs)
  destruct eq1 into name1, rpos1, ls1, etc.. 
  get constructor list with and without type (tcs resp. cs) from cs',  
  for every equation:  
    destruct it into (name,rpos,ls,c,cargs,rs,rhs)
    get typed constructor tc from c and tcs 
    determine the index i of the constructor 
    check function name and position of rec. argument by comparison
    with first equation 
    check for repeated variable names in pattern
    derive function term f_i which is used as argument of the rec. combinator
    sort the terms f_i according to i and return them together
      with the function name and the parameter of the definition (ls). 

* Application:

  The rec. combinator is applied to the function terms resulting from
  trans_rec. This results in a function which takes the recursive arg. 
  as first parameter and then the arguments corresponding to ls. The
  order of parameters is corrected by setting the rhs equal to 

  list_abs_free
            (ls @ [(tname,dummyT)]
             ,list_comb(rec_comb
                        , fns @ map Bound (0 ::(length ls downto 1))));

  Note the de-Bruijn indices counting the number of lambdas between the
  variable and its binding. 
*)



(* ----------------------------------------------- *)
(* The following has been written by Konrad Slind. *)


type dtype_info = {case_const:term, case_rewrites:thm list,
                   constructors:term list, nchotomy:thm, case_cong:thm};

signature Dtype_sig =
sig
  val build_case_cong: Sign.sg -> thm list -> cterm
  val build_nchotomy: Sign.sg -> thm list -> cterm

  val prove_case_cong: thm -> thm list -> cterm -> thm
  val prove_nchotomy: (string -> int -> tactic) -> cterm -> thm

  val case_thms : Sign.sg -> thm list -> (string -> int -> tactic)
                   -> {nchotomy:thm, case_cong:thm}

  val build_record : (theory * (string * string list)
                      * (string -> int -> tactic))
                     -> (string * dtype_info) 

end;


(*---------------------------------------------------------------------------
 * This structure is support for the Isabelle datatype package. It provides
 * entrypoints for 1) building and proving the case congruence theorem for
 * a datatype and 2) building and proving the "exhaustion" theorem for
 * a datatype (I have called this theorem "nchotomy" for no good reason).
 *
 * It also brings all these together in the function "build_record", which
 * is probably what will be used.
 *
 * Since these routines are required in order to support TFL, they have
 * been written so they will compile "stand-alone", i.e., in Isabelle-HOL
 * without any TFL code around.
 *---------------------------------------------------------------------------*)
structure Dtype : Dtype_sig =
struct

exception DTYPE_ERR of {func:string, mesg:string};

(*---------------------------------------------------------------------------
 * General support routines
 *---------------------------------------------------------------------------*)
fun itlist f L base_value =
   let fun it [] = base_value
         | it (a::rst) = f a (it rst)
   in it L 
   end;

fun end_itlist f =
let fun endit [] = raise DTYPE_ERR{func="end_itlist", mesg="list too short"}
      | endit alist = 
         let val (base::ralist) = rev alist
         in itlist f (rev ralist) base  end
in endit
end;

fun unzip L = itlist (fn (x,y) => fn (l1,l2) =>((x::l1),(y::l2))) L ([],[]);


(*---------------------------------------------------------------------------
 * Miscellaneous Syntax manipulation
 *---------------------------------------------------------------------------*)
val mk_var = Free;
val mk_const = Const
fun mk_comb(Rator,Rand) = Rator $ Rand;
fun mk_abs(r as (Var((s,_),ty),_))  = Abs(s,ty,abstract_over r)
  | mk_abs(r as (Free(s,ty),_))     = Abs(s,ty,abstract_over r)
  | mk_abs _ = raise DTYPE_ERR{func="mk_abs", mesg="1st not a variable"};

fun dest_var(Var((s,i),ty)) = (s,ty)
  | dest_var(Free(s,ty))    = (s,ty)
  | dest_var _ = raise DTYPE_ERR{func="dest_var", mesg="not a variable"};

fun dest_const(Const p) = p
  | dest_const _ = raise DTYPE_ERR{func="dest_const", mesg="not a constant"};

fun dest_comb(t1 $ t2) = (t1,t2)
  | dest_comb _ =  raise DTYPE_ERR{func = "dest_comb", mesg = "not a comb"};
val rand = #2 o dest_comb;
val rator = #1 o dest_comb;

fun dest_abs(a as Abs(s,ty,M)) = 
     let val v = Free(s, ty)
      in (v, betapply (a,v)) end
  | dest_abs _ =  raise DTYPE_ERR{func="dest_abs", mesg="not an abstraction"};


val bool = Type("bool",[])
and prop = Type("prop",[]);

fun mk_eq(lhs,rhs) = 
   let val ty = type_of lhs
       val c = mk_const("op =", ty --> ty --> bool)
   in list_comb(c,[lhs,rhs])
   end

fun dest_eq(Const("op =",_) $ M $ N) = (M, N)
  | dest_eq _ = raise DTYPE_ERR{func="dest_eq", mesg="not an equality"};

fun mk_disj(disj1,disj2) =
   let val c = Const("op |", bool --> bool --> bool)
   in list_comb(c,[disj1,disj2])
   end;

fun mk_forall (r as (Bvar,_)) = 
  let val ty = type_of Bvar
      val c = Const("All", (ty --> bool) --> bool)
  in mk_comb(c, mk_abs r)
  end;

fun mk_exists (r as (Bvar,_)) = 
  let val ty = type_of Bvar 
      val c = Const("Ex", (ty --> bool) --> bool)
  in mk_comb(c, mk_abs r)
  end;

fun mk_prop (tm as Const("Trueprop",_) $ _) = tm
  | mk_prop tm = mk_comb(Const("Trueprop", bool --> prop),tm);

fun drop_prop (Const("Trueprop",_) $ X) = X
  | drop_prop X = X;

fun mk_all (r as (Bvar,_)) = mk_comb(all (type_of Bvar), mk_abs r);
fun list_mk_all(V,t) = itlist(fn v => fn b => mk_all(v,b)) V t;
fun list_mk_exists(V,t) = itlist(fn v => fn b => mk_exists(v,b)) V t;
val list_mk_disj = end_itlist(fn d1 => fn tm => mk_disj(d1,tm))


fun dest_thm thm = 
   let val {prop,hyps,...} = rep_thm thm
   in (map drop_prop hyps, drop_prop prop)
   end;

val concl = #2 o dest_thm;


(*---------------------------------------------------------------------------
 * Names of all variables occurring in a term, including bound ones. These
 * are added into the second argument.
 *---------------------------------------------------------------------------*)
fun add_term_names tm =
let fun insert (x:string) = 
     let fun canfind[] = [x] 
           | canfind(alist as (y::rst)) = 
              if (x<y) then x::alist
              else if (x=y) then y::rst
              else y::canfind rst 
     in canfind end
    fun add (Free(s,_)) V = insert s V
      | add (Var((s,_),_)) V = insert s V
      | add (Abs(s,_,body)) V = add body (insert s V)
      | add (f$t) V = add t (add f V)
      | add _ V = V
in add tm
end;


(*---------------------------------------------------------------------------
 * We need to make everything free, so that we can put the term into a
 * goalstack, or submit it as an argument to prove_goalw_cterm.
 *---------------------------------------------------------------------------*)
fun make_free_ty(Type(s,alist)) = Type(s,map make_free_ty alist)
  | make_free_ty(TVar((s,i),srt)) = TFree(s,srt)
  | make_free_ty x = x;

fun make_free (Var((s,_),ty)) = Free(s,make_free_ty ty)
  | make_free (Abs(s,x,body)) = Abs(s,make_free_ty x, make_free body)
  | make_free (f$t) = (make_free f $ make_free t)
  | make_free (Const(s,ty)) = Const(s, make_free_ty ty)
  | make_free (Free(s,ty)) = Free(s, make_free_ty ty)
  | make_free b = b;


(*---------------------------------------------------------------------------
 * Structure of case congruence theorem looks like this:
 *
 *    (M = M') 
 *    ==> (!!x1,...,xk. (M' = C1 x1..xk) ==> (f1 x1..xk = f1' x1..xk)) 
 *    ==> ... 
 *    ==> (!!x1,...,xj. (M' = Cn x1..xj) ==> (fn x1..xj = fn' x1..xj)) 
 *    ==>
 *      (ty_case f1..fn M = ty_case f1'..fn' m')
 *
 * The input is the list of rules for the case construct for the type, i.e.,
 * that found in the "ty.cases" field of a theory where datatype "ty" is
 * defined.
 *---------------------------------------------------------------------------*)

fun build_case_cong sign case_rewrites =
 let val clauses = map concl case_rewrites
     val clause1 = hd clauses
     val left = (#1 o dest_eq) clause1
     val ty = type_of ((#2 o dest_comb) left)
     val varnames = itlist add_term_names clauses []
     val M = variant varnames "M"
     val Mvar = Free(M, ty)
     val M' = variant (M::varnames) M
     val M'var = Free(M', ty)
     fun mk_clause clause =
       let val (lhs,rhs) = dest_eq clause
           val func = (#1 o strip_comb) rhs
           val (constr,xbar) = strip_comb(rand lhs)
           val (Name,Ty) = dest_var func
           val func'name = variant (M::M'::varnames) (Name^"a")
           val func' = mk_var(func'name,Ty)
       in (func', list_mk_all
                  (xbar, Logic.mk_implies
                         (mk_prop(mk_eq(M'var, list_comb(constr,xbar))),
                          mk_prop(mk_eq(list_comb(func, xbar),
                                        list_comb(func',xbar))))))   end
     val (funcs',clauses') = unzip (map mk_clause clauses)
     val lhsM = mk_comb(rator left, Mvar)
     val c = #1(strip_comb left)
 in
 cterm_of sign
  (make_free
   (Logic.list_implies(mk_prop(mk_eq(Mvar, M'var))::clauses',
                       mk_prop(mk_eq(lhsM, list_comb(c,(funcs'@[M'var])))))))
 end
 handle _ => raise DTYPE_ERR{func="build_case_cong",mesg="failed"};

  
(*---------------------------------------------------------------------------
 * Proves the result of "build_case_cong". 
 * This one solves it a disjunct at a time, and builds the ss only once.
 *---------------------------------------------------------------------------*)
fun prove_case_cong nchotomy case_rewrites ctm =
 let val {sign,t,...} = rep_cterm ctm
     val (Const("==>",_) $ tm $ _) = t
     val (Const("Trueprop",_) $ (Const("op =",_) $ _ $ Ma)) = tm
     val (Free(str,_)) = Ma
     val thm = prove_goalw_cterm[] ctm
      (fn prems => 
        let val simplify = asm_simp_tac(HOL_ss addsimps (prems@case_rewrites))
        in [simp_tac (HOL_ss addsimps [hd prems]) 1,
            cut_inst_tac [("x",str)] (nchotomy RS spec) 1,
            REPEAT (etac disjE 1 THEN REPEAT (etac exE 1) THEN simplify 1),
            REPEAT (etac exE 1) THEN simplify 1 (* Get last disjunct *)]
        end) 
 in standard (thm RS eq_reflection)
 end
 handle _ => raise DTYPE_ERR{func="prove_case_cong",mesg="failed"};


(*---------------------------------------------------------------------------
 * Structure of exhaustion theorem looks like this:
 *
 *    !v. (EX y1..yi. v = C1 y1..yi) | ... | (EX y1..yj. v = Cn y1..yj)
 *
 * As for "build_case_cong", the input is the list of rules for the case 
 * construct (the case "rewrites").
 *---------------------------------------------------------------------------*)
fun build_nchotomy sign case_rewrites =
 let val clauses = map concl case_rewrites
     val C_ybars = map (rand o #1 o dest_eq) clauses
     val varnames = itlist add_term_names C_ybars []
     val vname = variant varnames "v"
     val ty = type_of (hd C_ybars)
     val v = mk_var(vname,ty)
     fun mk_disj C_ybar =
       let val ybar = #2(strip_comb C_ybar)
       in list_mk_exists(ybar, mk_eq(v,C_ybar))
       end
 in
 cterm_of sign
   (make_free(mk_prop (mk_forall(v, list_mk_disj (map mk_disj C_ybars)))))
 end
 handle _ => raise DTYPE_ERR{func="build_nchotomy",mesg="failed"};


(*---------------------------------------------------------------------------
 * Takes the induction tactic for the datatype, and the result from 
 * "build_nchotomy" 
 *
 *    !v. (EX y1..yi. v = C1 y1..yi) | ... | (EX y1..yj. v = Cn y1..yj)
 *
 * and proves the theorem. The proof works along a diagonal: the nth 
 * disjunct in the nth subgoal is easy to solve. Thus this routine depends 
 * on the order of goals arising out of the application of the induction 
 * tactic. A more general solution would have to use injectiveness and 
 * distinctness rewrite rules.
 *---------------------------------------------------------------------------*)
fun prove_nchotomy induct_tac ctm =
 let val (Const ("Trueprop",_) $ g) = #t(rep_cterm ctm)
     val (Const ("All",_) $ Abs (v,_,_)) = g
     (* For goal i, select the correct disjunct to attack, then prove it *)
     fun tac i 0 = (rtac disjI1 i ORELSE all_tac) THEN
                   REPEAT (rtac exI i) THEN (rtac refl i)
       | tac i n = rtac disjI2 i THEN tac i (n-1)
 in 
 prove_goalw_cterm[] ctm
     (fn _ => [rtac allI 1,
               induct_tac v 1,
               ALLGOALS (fn i => tac i (i-1))])
 end
 handle _ => raise DTYPE_ERR {func="prove_nchotomy", mesg="failed"};


(*---------------------------------------------------------------------------
 * Brings the preceeding functions together.
 *---------------------------------------------------------------------------*)
fun case_thms sign case_rewrites induct_tac =
  let val nchotomy = prove_nchotomy induct_tac
                                    (build_nchotomy sign case_rewrites)
      val cong = prove_case_cong nchotomy case_rewrites
                                 (build_case_cong sign case_rewrites)
  in {nchotomy=nchotomy, case_cong=cong}
  end;


(*---------------------------------------------------------------------------
 * Tests
 *
 * 
     Dtype.case_thms (sign_of List.thy) List.list.cases List.list.induct_tac;
     Dtype.case_thms (sign_of Prod.thy) [split] 
                     (fn s => res_inst_tac [("p",s)] PairE_lemma);
     Dtype.case_thms (sign_of Nat.thy) [nat_case_0, nat_case_Suc] nat_ind_tac;

 *
 *---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
 * Given a theory and the name (and constructors) of a datatype declared in 
 * an ancestor of that theory and an induction tactic for that datatype, 
 * return the information that TFL needs. This should only be called once for
 * a datatype, because "build_record" proves various facts, and thus is slow. 
 * It fails on the datatype of pairs, which must be included for TFL to work. 
 * The test shows how to  build the record for pairs.
 *---------------------------------------------------------------------------*)

local fun mk_rw th = (th RS eq_reflection) handle _ => th
      fun get_fact thy s = (get_axiom thy s handle _ => get_thm thy s)
in
fun build_record (thy,(ty,cl),itac) =
 let val sign = sign_of thy
     fun const s = Const(s, the(Sign.const_type sign s))
     val case_rewrites = map (fn c => get_fact thy (ty^"_case_"^c)) cl
     val {nchotomy,case_cong} = case_thms sign case_rewrites itac
 in
  (ty, {constructors = map(fn s => const s handle _ => const("op "^s)) cl,
        case_const = const (ty^"_case"),
        case_rewrites = map mk_rw case_rewrites,
        nchotomy = nchotomy,
        case_cong = case_cong})
 end
end;


(*---------------------------------------------------------------------------
 * Test
 *
 * 
    map Dtype.build_record 
          [(Nat.thy, ("nat",["0", "Suc"]), nat_ind_tac),
           (List.thy,("list",["[]", "#"]), List.list.induct_tac)]
    @
    [let val prod_case_thms = Dtype.case_thms (sign_of Prod.thy) [split] 
                                 (fn s => res_inst_tac [("p",s)] PairE_lemma)
         fun const s = Const(s, the(Sign.const_type (sign_of Prod.thy) s))
     in ("*", 
         {constructors = [const "Pair"],
            case_const = const "split",
         case_rewrites = [split RS eq_reflection],
             case_cong = #case_cong prod_case_thms,
              nchotomy = #nchotomy prod_case_thms}) end];

 *
 *---------------------------------------------------------------------------*)

end;
