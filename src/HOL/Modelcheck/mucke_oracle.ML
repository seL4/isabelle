exception MuckeOracleExn of term * theory;

val trace_mc = ref false; 


(* transform_case post-processes output strings of the syntax "Mucke" *)
(* with respect to the syntax of the case construct                   *)
local
  fun extract_argument [] = []
  | extract_argument ("*"::_) = []
  | extract_argument (x::xs) = x::(extract_argument xs);

  fun cut_argument [] = []
  | cut_argument ("*"::r) = r
  | cut_argument (_::xs) = cut_argument xs;

  fun insert_case_argument [] s = []
  | insert_case_argument ("*"::"="::xl) (x::xs) =
         (explode(x)@(" "::"="::(insert_case_argument xl (x::xs))))
  | insert_case_argument ("c"::"a"::"s"::"e"::"*"::xl) s =
        (let
        val arg=implode(extract_argument xl);
        val xr=cut_argument xl
        in
         "c"::"a"::"s"::"e"::" "::(insert_case_argument xr (arg::s))
        end)
  | insert_case_argument ("e"::"s"::"a"::"c"::"*"::xl) (x::xs) =
        "e"::"s"::"a"::"c"::(insert_case_argument xl xs)
  | insert_case_argument (x::xl) s = x::(insert_case_argument xl s);
in

fun transform_case s = implode(insert_case_argument (explode s) []);

end;


(* if_full_simp_tac is a tactic for rewriting non-boolean ifs *)
local
  (* searching an if-term as below as possible *)
  fun contains_if (Abs(a,T,t)) = [] |
  contains_if (Const("If",T) $ b $ a1 $ a2) =
  let
  fun tn (Type(s,_)) = s |
  tn _ = error "cannot master type variables in if term";
  val s = tn(body_type T);
  in
  if (s="bool") then [] else [b,a1,a2]
  end |
  contains_if (a $ b) = if ((contains_if b)=[]) then (contains_if a)
		        else (contains_if b) |
  contains_if _ = [];

  fun find_replace_term (Abs(a,T,t)) = find_replace_term (snd(variant_abs(a,T,t))) |
  find_replace_term (a $ b) = if ((contains_if (a $ b))=[]) then
  (if (snd(find_replace_term b)=[]) then (find_replace_term a) else (find_replace_term b))
  else (a $ b,contains_if(a $ b))|
  find_replace_term t = (t,[]);

  fun if_substi (Abs(a,T,t)) trm = Abs(a,T,t) |
  if_substi (Const("If",T) $ b $ a1 $ a2) t = t |
  if_substi (a $ b) t = if ((contains_if b)=[]) then ((if_substi a t)$b)
		        else (a$(if_substi b t)) |
  if_substi t v = t;

  fun deliver_term (t,[]) = [] |
  deliver_term (t,[b,a1,a2]) =
  [
  Const("Trueprop",Type("fun",[Type("bool",[]),Type("prop",[])])) $
  (
Const("op =",Type("fun",[Type("bool",[]),Type("fun",[Type("bool",[]),Type("bool",[])])]))
  $ t $
  (
Const("op &",Type("fun",[Type("bool",[]),Type("fun",[Type("bool",[]),Type("bool",[])])]))
  $
  (
Const("op -->",Type("fun",[Type("bool",[]),Type("fun",[Type("bool",[]),Type("bool",[])])]))
  $ b $ (if_substi t a1))
  $
  (
Const("op -->",Type("fun",[Type("bool",[]),Type("fun",[Type("bool",[]),Type("bool",[])])]))
  $ (Const("Not",Type("fun",[Type("bool",[]),Type("bool",[])])) $ b) $ (if_substi t a2))
  ))] |
  deliver_term _ =
  error "tactic failed due to occurence of malformed if-term" (* shouldnt occur *);

  fun search_if (*((Const("==",_)) $ _ $*) (a) = deliver_term(find_replace_term a);

  fun search_ifs [] = [] |
  search_ifs (a::r) =
  let
  val i = search_if a
  in
  if (i=[]) then (search_ifs r) else i
  end;
in

fun if_full_simp_tac sset i state =
let val sign = #sign (rep_thm state);
        val (subgoal::_) = drop(i-1,prems_of state);
        val prems = Logic.strip_imp_prems subgoal;
	val concl = Logic.strip_imp_concl subgoal;
	val prems = prems @ [concl];
        val itrm = search_ifs prems;
in
if (itrm = []) then (PureGeneral.Seq.empty) else
(
let
val trm = hd(itrm)
in
(
push_proof();
goalw_cterm [] (cterm_of sign trm);
by (simp_tac (simpset()) 1);
        let
        val if_tmp_result = result()
        in
        (
        pop_proof();
        CHANGED(full_simp_tac (sset addsimps [if_tmp_result]) i) state)
        end
)
end)
end;

end;

(********************************************************)
(* All following stuff serves for defining mk_mc_oracle *)
(********************************************************)

(***************************************)
(* SECTION 0: some auxiliary functions *)

fun list_contains_key [] _ = false |
list_contains_key ((a,l)::r) t = if (a=t) then true else (list_contains_key r t);

fun search_in_keylist [] _ = [] |
search_in_keylist ((a,l)::r) t = if (a=t) then l else (search_in_keylist r t);

(* delivers the part of a qualified type/const-name after the last dot *)
fun post_last_dot str =
let
fun fl [] = [] |
fl (a::r) = if (a=".") then [] else (a::(fl r));
in
implode(rev(fl(rev(explode str))))
end;

(* OUTPUT - relevant *)
(* converts type to string by a mucke-suitable convention *)
fun type_to_string_OUTPUT (Type(a,[])) = post_last_dot a |
type_to_string_OUTPUT (Type("*",[a,b])) =
         "P_" ^ (type_to_string_OUTPUT a) ^ "_AI_" ^ (type_to_string_OUTPUT b) ^ "_R" |
type_to_string_OUTPUT (Type(a,l)) =
let
fun ts_to_string [] = "" |
ts_to_string (a::[]) = type_to_string_OUTPUT a |
ts_to_string (a::l) = (type_to_string_OUTPUT a) ^ "_I_" ^ (ts_to_string l);
in
(post_last_dot a) ^ "_A_" ^ (ts_to_string l) ^ "_C"
end |
type_to_string_OUTPUT _ =
error "unexpected type variable in type_to_string";

(* delivers type of a term *)
fun type_of_term (Const(_,t)) = t |
type_of_term (Free(_,t)) = t |
type_of_term (Var(_,t)) = t |
type_of_term (Abs(x,t,trm)) = Type("fun",[t,type_of_term(snd(variant_abs(x,t,trm)))]) |
type_of_term (a $ b) =
let
 fun accept_fun_type (Type("fun",[x,y])) = (x,y) |
 accept_fun_type _ =
 error "no function type returned, where it was expected (in type_of_term)";
 val (x,y) = accept_fun_type(type_of_term a)
in
y
end |
type_of_term _ = 
error "unexpected bound variable when calculating type of a term (in type_of_term)";

(* makes list [a1..an] and ty to type an -> .. -> a1 -> ty *)
fun fun_type_of [] ty = ty |
fun_type_of (a::r) ty = fun_type_of r (Type("fun",[a,ty]));

(* creates a constructor term from constructor and its argument terms *)
fun con_term_of t [] = t |
con_term_of t (a::r) = con_term_of (t $ a) r;

(* creates list of constructor terms *)
fun con_term_list_of trm [] = [] |
con_term_list_of trm (a::r) = (con_term_of trm a)::(con_term_list_of trm r);

(* list multiplication *)
fun multiply_element a [] = [] |
multiply_element a (l::r) = (a::l)::(multiply_element a r);
fun multiply_list [] l = [] |
multiply_list (a::r) l = (multiply_element a l)@(multiply_list r l);

(* To a list of types, delivers all lists of proper argument terms; tl has to *)
(* be a preprocessed type list with element type: (type,[(string,[type])])    *)
fun arglist_of sg tl [] = [[]] |
arglist_of sg tl (a::r) =
let
fun ispair (Type("*",x::y::[])) = (true,(x,y)) |
ispair x = (false,(x,x));
val erg =
(if (fst(ispair a))
 then (let
        val (x,y) = snd(ispair a)
       in
        con_term_list_of (Const("pair",Type("fun",[x,Type("fun",[y,a])])))
			 (arglist_of sg tl [x,y])
       end)
 else
 (let
  fun deliver_erg sg tl _ [] = [] |
  deliver_erg sg tl typ ((c,tyl)::r) = let
                        val ft = fun_type_of (rev tyl) typ;
                        val trm = #t(rep_cterm(read_cterm sg (c,ft)));
                        in
                        (con_term_list_of trm (arglist_of sg tl tyl))
			@(deliver_erg sg tl typ r)
                        end;
  val cl = search_in_keylist tl a;
  in
  deliver_erg sg tl a cl
  end))
in
multiply_list erg (arglist_of sg tl r)
end;

(*******************************************************************)
(* SECTION 1: Robert Sandner's source was improved and extended by *)
(* generation of function declarations                             *)

fun dest_Abs (Abs s_T_t) = s_T_t
  | dest_Abs t = raise TERM("dest_Abs", [t]);

(*
fun force_Abs (Abs s_T_t) = Abs s_T_t
  | force_Abs t = Abs("x", hd(fst(strip_type (type_of t))),
		      (incr_boundvars 1 t) $ (Bound 0));

fun etaexp_dest_Abs t = dest_Abs (force_Abs t);
*)

(* replace Vars bei Frees, freeze_thaw shares code of tactic/freeze_thaw
   and thm.instantiate *)
fun freeze_thaw t =
  let val used = add_term_names (t, [])
          and vars = term_vars t;
      fun newName (Var(ix,_), (pairs,used)) = 
          let val v = variant used (string_of_indexname ix)
          in  ((ix,v)::pairs, v::used)  end;
      val (alist, _) = foldr newName (vars, ([], used));
      fun mk_inst (Var(v,T)) = 
          (Var(v,T),
           Free(the (assoc(alist,v)), T));
      val insts = map mk_inst vars;
  in subst_atomic insts t end;

fun make_fun_type (a::b::l) = Type("fun",a::(make_fun_type (b::l))::[]) 
  | make_fun_type (a::l) = a;

fun make_decl muckeType id isaType =
  let val constMuckeType = Const(muckeType,isaType);
      val constId = Const(id,isaType);
      val constDecl = Const("_decl", make_fun_type [isaType,isaType,isaType]); 
  in (constDecl $ constMuckeType) $ constId end;

fun make_MuTerm muDeclTerm ParamDeclTerm muTerm isaType =
  let val constMu = Const("_mu",
			  make_fun_type [isaType,isaType,isaType,isaType]);
      val t1 = constMu $ muDeclTerm;
      val t2 = t1 $ ParamDeclTerm;
      val t3 = t2 $  muTerm
  in t3 end;

fun make_MuDecl muDeclTerm ParamDeclTerm isaType =
  let val constMu = Const("_mudec",
                          make_fun_type [isaType,isaType,isaType]);
      val t1 = constMu $ muDeclTerm;
      val t2 = t1 $ ParamDeclTerm
  in t2 end;

fun make_NuTerm muDeclTerm ParamDeclTerm muTerm isaType =
  let val constMu = Const("_nu",
                          make_fun_type [isaType,isaType,isaType,isaType]);
      val t1 = constMu $ muDeclTerm;
      val t2 = t1 $ ParamDeclTerm;
      val t3 = t2 $  muTerm
  in t3 end;

fun make_NuDecl muDeclTerm ParamDeclTerm isaType =
  let val constMu = Const("_nudec",
                          make_fun_type [isaType,isaType,isaType]);
      val t1 = constMu $ muDeclTerm;
      val t2 = t1 $ ParamDeclTerm
  in t2 end;

fun is_mudef (( Const("==",_) $ t1) $ ((Const("MuCalculus.mu",_)) $ t2)) = true
  | is_mudef _ = false;

fun is_nudef (( Const("==",_) $ t1) $ ((Const("MuCalculus.nu",_)) $ t2)) = true
  | is_nudef _ = false;

fun make_decls sign Dtype (Const(str,tp)::n::Clist) = 
    let val const_decls = Const("_decls",make_fun_type [Dtype,Dtype,Dtype]);
        val decl = make_decl (type_to_string_OUTPUT tp) str Dtype;
    in
    ((const_decls $ decl) $ (make_decls sign Dtype (n::Clist)))
    end
  | make_decls sign Dtype [Const(str,tp)] = 
      make_decl (type_to_string_OUTPUT tp) str Dtype;


(* make_mu_def transforms an Isabelle Mu-Definition into Mucke format
   Takes equation of the form f = Mu Q. % x. t *)

fun dest_atom (Const t) = dest_Const (Const t)
  | dest_atom (Free t)  = dest_Free (Free t);

fun get_decls sign Clist (Abs(s,tp,trm)) = 
    let val VarAbs = variant_abs(s,tp,trm);
    in get_decls sign (Const(fst VarAbs,tp)::Clist) (snd VarAbs)
    end
  | get_decls sign Clist ((Const("split",_)) $ trm) = get_decls sign Clist trm
  | get_decls sign Clist trm = (Clist,trm);

fun make_mu_def sign ((tt $ LHS) $ (ttt $ RHS)) =
  let 	val LHSStr = fst (dest_atom LHS);
	val MuType = Type("bool",[]); (* always ResType of mu, also serves
					 as dummy type *)
	val (_,_,PAbs) = dest_Abs (RHS); (* RHS is %Q. ... *)
  	val (PCon_LHS,MMuTerm) = get_decls sign [] (subst_bound (LHS,PAbs));
	val PConsts = rev PCon_LHS;
	val muDeclTerm = make_decl "bool" LHSStr MuType;
	val PDeclsTerm = make_decls sign MuType PConsts;
	val MuDefTerm = make_MuTerm muDeclTerm PDeclsTerm MMuTerm MuType;		
  in MuDefTerm end;

fun make_mu_decl sign ((tt $ LHS) $ (ttt $ RHS)) =
  let   val LHSStr = fst (dest_atom LHS);
        val MuType = Type("bool",[]); (* always ResType of mu, also serves
                                         as dummy type *)
        val (_,_,PAbs) = dest_Abs (RHS); (* RHS is %Q. ... *)
        val (PCon_LHS,MMuTerm) = get_decls sign [] (subst_bound (LHS,PAbs));
        val PConsts = rev PCon_LHS;
        val muDeclTerm = make_decl "bool" LHSStr MuType;
        val PDeclsTerm = make_decls sign MuType PConsts;
        val MuDeclTerm = make_MuDecl muDeclTerm PDeclsTerm MuType;
  in MuDeclTerm end;

fun make_nu_def sign ((tt $ LHS) $ (ttt $ RHS)) =
  let   val LHSStr = fst (dest_atom LHS);
        val MuType = Type("bool",[]); (* always ResType of mu, also serves
                                         as dummy type *)
        val (_,_,PAbs) = dest_Abs (RHS); (* RHS is %Q. ... *)
        val (PCon_LHS,MMuTerm) = get_decls sign [] (subst_bound (LHS,PAbs));
        val PConsts = rev PCon_LHS;
        val muDeclTerm = make_decl "bool" LHSStr MuType;
        val PDeclsTerm = make_decls sign MuType PConsts;
        val NuDefTerm = make_NuTerm muDeclTerm PDeclsTerm MMuTerm MuType;
  in NuDefTerm end;

fun make_nu_decl sign ((tt $ LHS) $ (ttt $ RHS)) =
  let   val LHSStr = fst (dest_atom LHS);
        val MuType = Type("bool",[]); (* always ResType of mu, also serves
                                         as dummy type *)
        val (_,_,PAbs) = dest_Abs (RHS); (* RHS is %Q. ... *)
        val (PCon_LHS,MMuTerm) = get_decls sign [] (subst_bound (LHS,PAbs));
        val PConsts = rev PCon_LHS; 
        val muDeclTerm = make_decl "bool" LHSStr MuType;
        val PDeclsTerm = make_decls sign MuType PConsts; 
        val NuDeclTerm = make_NuDecl muDeclTerm PDeclsTerm MuType;
  in NuDeclTerm end;

fun make_FunMuckeTerm FunDeclTerm ParamDeclTerm Term isaType =
  let 	val constFun = Const("_fun",
			    make_fun_type [isaType,isaType,isaType,isaType]);
      	val t1 = constFun $ FunDeclTerm;
      	val t2 = t1 $ ParamDeclTerm;
      	val t3 = t2 $  Term
  in t3 end;

fun make_FunMuckeDecl FunDeclTerm ParamDeclTerm isaType =
  let   val constFun = Const("_dec",
                            make_fun_type [isaType,isaType,isaType]);
      val t1 = constFun $ FunDeclTerm;
      val t2 = t1 $ ParamDeclTerm
  in t2 end;

fun is_fundef (( Const("==",_) $ _) $ ((Const("split",_)) $ _)) = true |
is_fundef (( Const("==",_) $ _) $ Abs(x_T_t)) = true 
| is_fundef _ = false; 

fun make_mucke_fun_def sign ((_ $ LHS) $ RHS) =
  let 	(* fun dest_atom (Const t) = dest_Const (Const t)
          | dest_atom (Free t)  = dest_Free (Free t); *)
	val LHSStr = fst (dest_atom LHS);
	val LHSResType = body_type(snd(dest_atom LHS));
	val LHSResTypeStr = type_to_string_OUTPUT LHSResType;
(*	val (_,AbsType,RawTerm) = dest_Abs(RHS);
*)	val (Consts_LHS_rev,Free_RHS) = get_decls sign [] RHS;
	val Consts_LHS = rev Consts_LHS_rev;
	val PDeclsTerm = make_decls sign LHSResType Consts_LHS; 
		(* Boolean functions only, list necessary in general *)
	val DeclTerm = make_decl LHSResTypeStr LHSStr LHSResType;
	val MuckeDefTerm = make_FunMuckeTerm DeclTerm PDeclsTerm Free_RHS
					 LHSResType;	
  in MuckeDefTerm end;

fun make_mucke_fun_decl sign ((_ $ LHS) $ RHS) =
  let   (* fun dest_atom (Const t) = dest_Const (Const t)
          | dest_atom (Free t)  = dest_Free (Free t); *)
        val LHSStr = fst (dest_atom LHS);
	val LHSResType = body_type(snd(dest_atom LHS));
        val LHSResTypeStr = type_to_string_OUTPUT LHSResType;
(*      val (_,AbsType,RawTerm) = dest_Abs(RHS);
*)      val (Consts_LHS_rev,Free_RHS) = get_decls sign [] RHS;
        val Consts_LHS = rev Consts_LHS_rev;
        val PDeclsTerm = make_decls sign LHSResType Consts_LHS;
                (* Boolean functions only, list necessary in general *)
        val DeclTerm = make_decl LHSResTypeStr LHSStr LHSResType;
	val MuckeDeclTerm = make_FunMuckeDecl DeclTerm PDeclsTerm LHSResType;
in MuckeDeclTerm end;

fun elim_quantifications sign ((Const("Ex",_)) $ Abs (str,tp,t)) =
    (let val ExConst = Const("_Ex",make_fun_type [tp,tp,tp,tp]);
     	 val TypeConst = Const (type_to_string_OUTPUT tp,tp);
	 val VarAbs = variant_abs(str,tp,t);
	 val BoundConst = Const(fst VarAbs,tp);
	 val t1 = ExConst $ TypeConst;
	 val t2 = t1 $ BoundConst;
 	 val t3 = elim_quantifications sign (snd VarAbs)
     in t2 $ t3 end)
  |  elim_quantifications sign ((Const("All",_)) $ Abs (str,tp,t)) =
    (let val AllConst = Const("_All",make_fun_type [tp,tp,tp,tp]);
    	 val TypeConst = Const (type_to_string_OUTPUT tp,tp);
	 val VarAbs = variant_abs(str,tp,t);
	 val BoundConst = Const(fst VarAbs,tp);
	 val t1 = AllConst $ TypeConst;
	 val t2 = t1 $ BoundConst;
	 val t3 = elim_quantifications sign (snd VarAbs)
     in t2 $ t3 end)
  | elim_quantifications sign (t1 $ t2) = 
   	(elim_quantifications sign t1) $ (elim_quantifications sign t2)
  | elim_quantifications sign (Abs(_,_,t)) = elim_quantifications sign t
  | elim_quantifications sign t = t;
fun elim_quant_in_list sign [] = []
  | elim_quant_in_list sign (trm::list) = 
			(elim_quantifications sign trm)::(elim_quant_in_list sign list);

fun dummy true = writeln "True\n" |
    dummy false = writeln "Fals\n";

fun transform_definitions sign [] = []
  | transform_definitions sign (trm::list) = 
      if is_mudef trm 
      then (make_mu_def sign trm)::(transform_definitions sign list)
      else 
	if is_nudef trm
	 then (make_nu_def sign trm)::(transform_definitions sign list)
     	 else 
	   if is_fundef trm
 	   then (make_mucke_fun_def sign trm)::(transform_definitions sign list)
		     else trm::(transform_definitions sign list);

fun terms_to_decls sign [] = []
 | terms_to_decls sign (trm::list) =
      if is_mudef trm
      then (make_mu_decl sign trm)::(terms_to_decls sign list)
      else
        if is_nudef trm
         then (make_nu_decl sign trm)::(terms_to_decls sign list)
         else
           if is_fundef trm
           then (make_mucke_fun_decl sign trm)::(terms_to_decls sign list)
                     else (transform_definitions sign list);

fun transform_terms sign list = 
let val DefsOk = transform_definitions sign list;
in elim_quant_in_list sign DefsOk
end;

fun string_of_terms sign terms =
let fun make_string sign [] = "" |
 	make_string sign (trm::list) = 
           ((Sign.string_of_term sign trm) ^ "\n" ^(make_string sign list))
in
(setmp print_mode ["Mucke"] (make_string sign) terms)
end;

fun callmc s =
  let
    val path = Path.unpack "tmp.mu";
    val _ = File.write path s;
    val result = execute "mucke -nb tmp";
  in File.rm path; result end;

(* extract_result looks for true value before *) 
(* finishing line "===..." of mucke output    *)
local

infix is_prefix_of contains string_contains;

  val is_blank : string -> bool =
      fn " " => true | "\t" => true | "\n" => true | "\^L" => true 
       | "\160" => true | _ => false;

  fun delete_blanks [] = []
    | delete_blanks (":"::xs) = delete_blanks xs
    | delete_blanks (x::xs) = 
        if (is_blank x) then (delete_blanks xs)
	       	        else x::(delete_blanks xs);
  
  fun delete_blanks_string s = implode(delete_blanks (explode s));

  fun [] is_prefix_of s = true
    | (p::ps) is_prefix_of  [] = false
    | (p::ps) is_prefix_of (x::xs) = (p = x) andalso (ps is_prefix_of xs);

  fun [] contains [] = true
    | [] contains s = false
    | (x::xs) contains s = (s is_prefix_of (x::xs)) orelse (xs contains s);

  fun s string_contains s1 = 
      (explode s) contains (explode s1);

in 

fun extract_result goal answer =
  let 
    val search_text_true = "istrue===";
    val short_answer = delete_blanks_string answer;
  in
    short_answer string_contains search_text_true
  end;

end; 

(**************************************************************)
(* SECTION 2: rewrites case-constructs over complex datatypes *)
local

(* check_case checks, whether a term is of the form a $ "(case x of ...)", *)
(* where x is of complex datatype; the second argument of the result is    *)
(* the number of constructors of the type of x                             *) 
fun check_case sg tl (a $ b) =
let
 (* tl_contains_complex returns true in the 1st argument when argument type is *)
 (* complex; the 2nd argument is the number of constructors                    *)
 fun tl_contains_complex [] _ = (false,0) |
 tl_contains_complex ((a,l)::r) t =
 let
  fun check_complex [] p = p |
  check_complex ((a,[])::r) (t,i) = check_complex r (t,i+1) |
  check_complex ((a,_)::r) (t,i) = check_complex r (true,i+1);
 in
	if (a=t) then (check_complex l (false,0)) else (tl_contains_complex r t)
 end;
 fun check_head_for_case sg (Const(s,_)) st 0 = 
	if (post_last_dot(s) = (st ^ "_case")) then true else false |
 check_head_for_case sg (a $ (Const(s,_))) st 0 = 
	if (post_last_dot(s) = (st ^ "_case")) then true else false |
 check_head_for_case _ _ _ 0 = false |
 check_head_for_case sg (a $ b) st n = check_head_for_case sg a st (n-1) |
 check_head_for_case _ _ _ _ = false;
 fun qtn (Type(a,_)) = a | 
 qtn _ = error "unexpected type variable in check_case";
 val t = type_of_term b;
 val (bv,n) = tl_contains_complex tl t
 val st = post_last_dot(qtn t); 
in
 if (bv) then ((check_head_for_case sg a st n),n) else (false,n) 
end |
check_case sg tl trm = (false,0);

(* enrich_case_with_terms enriches a case term with additional *)
(* conditions according to the context of the case replacement *)
fun enrich_case_with_terms sg [] t = t |
enrich_case_with_terms sg [trm] (Abs(x,T,t)) =
let
 val v = variant_abs(x,T,t);
 val f = fst v;
 val s = snd v
in
(Const("Ex",Type("fun",[Type("fun",[T,Type("bool",[])]),Type("bool",[])])) $
(Abs(x,T,
abstract_over(Free(f,T),
Const("op &",Type("fun",[Type("bool",[]),Type("fun",[Type("bool",[]),Type("bool",[])])]))
$
(Const("op =",Type("fun",[T,Type("fun",[T,Type("bool",[])])])) $ (Free(f,T)) $ trm)
$ s))))
end |
enrich_case_with_terms sg (a::r) (Abs(x,T,t)) =
        enrich_case_with_terms sg [a] (Abs(x,T,(enrich_case_with_terms sg r t))) |
enrich_case_with_terms sg (t::r) trm =
let val ty = type_of_term t
in
(Const("Ex",Type("fun",[Type("fun",[ ty ,Type("bool",[])]),Type("bool",[])])) $
Abs("a", ty,
Const("op &",Type("fun",[Type("bool",[]),Type("fun",[Type("bool",[]),Type("bool",[])])]))
$
(Const("op =",Type("fun",[ ty ,Type("fun",[ ty ,Type("bool",[])])])) $ Bound(0) $ t)
$
enrich_case_with_terms sg r (trm $ (Bound(length(r))))))
end;

fun replace_termlist_with_constrs sg tl (a::l1) (c::l2) t = 
let
 fun heart_of_trm (Abs(x,T,t)) = heart_of_trm(snd(variant_abs(x,T,t))) |
 heart_of_trm t = t;
 fun replace_termlist_with_args _ _ trm _ [] _ ([],[]) = trm (* should never occur *) |
 replace_termlist_with_args sg _ trm _ [a] _ ([],[]) =
	if ((heart_of_trm trm)= Const("False",Type("bool",[]))) then trm else 
	(enrich_case_with_terms sg a trm) |
 replace_termlist_with_args sg tl trm con [] t (l1,l2) =
	(replace_termlist_with_constrs sg tl l1 l2 t) | 
 replace_termlist_with_args sg tl trm con (a::r) t (l1,l2) =
 let
  val tty = type_of_term t;
  val con_term = con_term_of con a;
 in
	(Const("If",Type("fun",[Type("bool",[]),
        Type("fun",[Type("bool",[]),Type("fun",[Type("bool",[]),Type("bool",[])])])])) $
	(Const("op =",Type("fun",[tty,Type("fun",[tty,Type("bool",[])])])) $
        t $ con_term) $
	(if ((heart_of_trm trm)= Const("False",Type("bool",[]))) then trm else 
	(enrich_case_with_terms sg a trm)) $
	(replace_termlist_with_args sg tl trm con r t (l1,l2)))
 end;
 val arglist = arglist_of sg tl (snd c);
 val tty = type_of_term t;
 val con_typ = fun_type_of (rev (snd c)) tty;
 val con = #t(rep_cterm(read_cterm sg (fst c,con_typ)));
in
 replace_termlist_with_args sg tl a con arglist t (l1,l2)
end |
replace_termlist_with_constrs _ _ _ _ _ = 
error "malformed arguments in replace_termlist_with_constrs" (* shouldnt occur *);

(* rc_in_termlist constructs a cascading if with the case terms in trm_list, *)
(* which were found in rc_in_term (see replace_case)                         *)
fun rc_in_termlist sg tl trm_list trm =  
let
 val ty = type_of_term trm;
 val constr_list = search_in_keylist tl ty;
in
	replace_termlist_with_constrs sg tl trm_list constr_list trm
end;  

in

(* replace_case replaces each case statement over a complex datatype by a cascading if; *)
(* it is normally called with a 0 in the 4th argument, it is positive, if in the course *)
(* of calculation, a "case" is discovered and then indicates the distance to that case  *)
fun replace_case sg tl (a $ b) 0 =
let
 (* rc_in_term changes the case statement over term x to a cascading if; the last *)
 (* indicates the distance to the "case"-constant                                 *)
 fun rc_in_term sg tl (a $ b) l x 0 =
	 (replace_case sg tl a 0) $ (rc_in_termlist sg tl l x) |  
 rc_in_term sg tl  _ l x 0 = rc_in_termlist sg tl l x |
 rc_in_term sg tl (a $ b) l x n = rc_in_term sg tl a (b::l) x (n-1) |
 rc_in_term sg _ trm _ _ n =
 error("malformed term for case-replacement: " ^ (Sign.string_of_term sg trm));
 val (bv,n) = check_case sg tl (a $ b);
in
 if (bv) then 
	(let
	val t = (replace_case sg tl a n) 
	in 
	rc_in_term sg tl t [] b n	
	end)
 else ((replace_case sg tl a 0) $ (replace_case sg tl b 0))
end |
replace_case sg tl (a $ b) 1 = a $ (replace_case sg tl b 0) |
replace_case sg tl (a $ b) n = (replace_case sg tl a (n-1)) $ (replace_case sg tl b 0) |
replace_case sg tl (Abs(x,T,t)) _ = 
let 
 val v = variant_abs(x,T,t);
 val f = fst v;
 val s = snd v
in
 Abs(x,T,abstract_over(Free(f,T),replace_case sg tl s 0))
end |
replace_case _ _ t _ = t;

end;

(*******************************************************************)
(* SECTION 3: replacing variables being part of a constructor term *)

(* transforming terms so that nowhere a variable is subterm of *)
(* a constructor term; the transformation uses cascading ifs   *)
fun remove_vars sg tl (Abs(x,ty,trm)) =
let
(* checks freeness of variable x in term *)
fun xFree x (a $ b) = if (xFree x a) then true else (xFree x b) |
xFree x (Abs(a,T,trm)) = xFree x trm |
xFree x (Free(y,_)) = if (x=y) then true else false |
xFree _ _ = false;
(* really substitues variable x by term c *)
fun real_subst sg tl x c (a$b) = (real_subst sg tl x c a) $ (real_subst sg tl x c b) |
real_subst sg tl x c (Abs(y,T,trm)) = Abs(y,T,real_subst sg tl x c trm) |
real_subst sg tl x c (Free(y,t)) = if (x=y) then c else Free(y,t) |
real_subst sg tl x c t = t;
(* substituting variable x by term c *)
fun x_subst sg tl x c (a $ b) =
let
 val t = (type_of_term (a $ b))
in
 if ((list_contains_key tl t) andalso (xFree x (a$b)))
 then (real_subst sg tl x c (a$b)) else ((x_subst sg tl x c a) $ (x_subst sg tl x c b))
end |
x_subst sg tl x c (Abs(y,T,trm)) = Abs(y,T,x_subst sg tl x c trm) |
x_subst sg tl x c t = t;
(* genearting a cascading if *)
fun casc_if sg tl x ty (c::l) trm =
let
 val arglist = arglist_of sg tl (snd c);
 val con_typ = fun_type_of (rev (snd c)) ty;
 val con = #t(rep_cterm(read_cterm sg (fst c,con_typ)));
 fun casc_if2 sg tl x con [] ty trm [] = trm | (* should never occur *)
 casc_if2 sg tl x con [arg] ty trm [] = x_subst sg tl x (con_term_of con arg) trm |
 casc_if2 sg tl x con (a::r) ty trm cl =
        Const("If",Type("fun",[Type("bool",[]),
        Type("fun",[Type("bool",[]),Type("fun",[Type("bool",[]),Type("bool",[])])])
        ])) $
     (Const("op =",Type("fun",[ty,Type("fun",[ty,Type("bool",[])])])) $
        Free(x,ty) $ (real_subst sg tl x (con_term_of con a) (Free(x,ty)))) $
   (x_subst sg tl x (con_term_of con a) trm) $
   (casc_if2 sg tl x con r ty trm cl) |
 casc_if2 sg tl x con [] ty trm cl = casc_if sg tl x ty cl trm;
in
 casc_if2 sg tl x con arglist ty trm l
end |
casc_if _ _ _ _ [] trm = trm (* should never occur *); 
fun if_term sg tl x ty trm =
let
 val tyC_list = search_in_keylist tl ty;
in
 casc_if sg tl x ty tyC_list trm
end;
(* checking whether a variable occurs in a constructor term *)
fun constr_term_contains_var sg tl (a $ b) x =
let
 val t = type_of_term (a $ b)
in
 if ((list_contains_key tl t) andalso (xFree x (a$b))) then true
 else
 (if (constr_term_contains_var sg tl a x) then true 
  else (constr_term_contains_var sg tl b x))
end |
constr_term_contains_var sg tl (Abs(y,ty,trm)) x =
         constr_term_contains_var sg tl (snd(variant_abs(y,ty,trm))) x |
constr_term_contains_var _ _ _ _ = false;
val vt = variant_abs(x,ty,trm);
val tt = remove_vars sg tl (snd(vt))
in
if (constr_term_contains_var sg tl tt (fst vt))
(* fst vt muss frei vorkommen, als ECHTER TeilKonstruktorterm *)
then (Abs(x,ty,
        abstract_over(Free(fst vt,ty),
	if_term sg ((Type("bool",[]),[("True",[]),("False",[])])::tl) (fst vt) ty tt)))
else Abs(x,ty,abstract_over(Free(fst vt,ty),tt))
end |
remove_vars sg tl (a $ b) = (remove_vars sg tl a) $ (remove_vars sg tl b) |
remove_vars sg tl t = t;

(* dissolves equalities "=" of boolean terms, where one of them is a complex term *)
fun remove_equal sg tl (Abs(x,ty,trm)) = Abs(x,ty,remove_equal sg tl trm) |
remove_equal sg tl (Const("op =",Type("fun",[Type("bool",[]),
	Type("fun",[Type("bool",[]),Type("bool",[])])])) $ lhs $ rhs) =
let
fun complex_trm (Abs(_,_,_)) = true |
complex_trm (_ $ _) = true |
complex_trm _ = false;
in
(if ((complex_trm lhs) orelse (complex_trm rhs)) then
(let
val lhs = remove_equal sg tl lhs;
val rhs = remove_equal sg tl rhs
in
(
Const("op &",
Type("fun",[Type("bool",[]),Type("fun",[Type("bool",[]),Type("bool",[])])])) $
(Const("op -->",
 Type("fun",[Type("bool",[]),Type("fun",[Type("bool",[]),Type("bool",[])])])) $
	lhs $ rhs) $
(Const("op -->",
 Type("fun",[Type("bool",[]),Type("fun",[Type("bool",[]),Type("bool",[])])])) $
	rhs $ lhs)
)
end)
else
(Const("op =",
 Type("fun",[Type("bool",[]),Type("fun",[Type("bool",[]),Type("bool",[])])])) $
	lhs $ rhs))
end |
remove_equal sg tl (a $ b) = (remove_equal sg tl a) $ (remove_equal sg tl b) |
remove_equal sg tl trm = trm;

(* rewrites constructor terms (without vars) for mucke *)
fun rewrite_dt_term sg tl (Abs(x,ty,t)) = Abs(x,ty,(rewrite_dt_term sg tl t)) |
rewrite_dt_term sg tl (a $ b) =
let

(* OUTPUT - relevant *)
(* transforms constructor term to a mucke-suitable output *)
fun term_OUTPUT sg (Const("Pair",_) $ a $ b) =
		(term_OUTPUT sg a) ^ "_I_" ^ (term_OUTPUT sg b) |
term_OUTPUT sg (a $ b) = (term_OUTPUT sg a) ^ "_I_" ^ (term_OUTPUT sg b) |
term_OUTPUT sg (Const(s,t)) = post_last_dot s |
term_OUTPUT _ _ = 
error "term contains an unprintable constructor term (in term_OUTPUT)";

fun contains_bound i (Bound(j)) = if (j>=i) then true else false |
contains_bound i (a $ b) = if (contains_bound i a) then true else (contains_bound i b) |
contains_bound i (Abs(_,_,t)) = contains_bound (i+1) t |
contains_bound _ _ = false;

in
        if (contains_bound 0 (a $ b)) 
	then ((rewrite_dt_term sg tl a) $ (rewrite_dt_term sg tl b))
        else
        (
        let
        val t = type_of_term (a $ b);
        in
        if (list_contains_key tl t) then (Const((term_OUTPUT sg (a $ b)),t)) else
        ((rewrite_dt_term sg tl a) $ (rewrite_dt_term sg tl b))
        end)
end |
rewrite_dt_term sg tl t = t;

fun rewrite_dt_terms sg tl [] = [] |
rewrite_dt_terms sg tl (a::r) =
let
 val c = (replace_case sg ((Type("bool",[]),[("True",[]),("False",[])])::tl) a 0);
 val rv = (remove_vars sg tl c);  
 val rv = (remove_equal sg tl rv);
in
 ((rewrite_dt_term sg tl rv) 
 :: (rewrite_dt_terms sg tl r))
end;

(**********************************************************************)
(* SECTION 4: generating type declaration and preprocessing type list *)

fun make_type_decls [] tl = "" |
make_type_decls ((a,l)::r) tl = 
let
fun comma_list_of [] = "" |
comma_list_of (a::[]) = a |
comma_list_of (a::r) = a ^ "," ^ (comma_list_of r);

(* OUTPUT - relevant *)
(* produces for each type of the 2nd argument its constant names (see *)
(* concat_constr) and appends them to prestring (see concat_types)    *)
fun generate_constnames_OUTPUT prestring [] _ = [prestring] |
generate_constnames_OUTPUT prestring ((Type("*",[a,b]))::r) tl =
 generate_constnames_OUTPUT prestring (a::b::r) tl |
generate_constnames_OUTPUT prestring (a::r) tl =
let
 fun concat_constrs [] _ = [] |
 concat_constrs ((c,[])::r) tl = c::(concat_constrs r tl)  |
 concat_constrs ((c,l)::r) tl =
         (generate_constnames_OUTPUT (c ^ "_I_") l tl) @ (concat_constrs r tl);
 fun concat_types _ [] _ _ = [] |
 concat_types prestring (a::q) [] tl = [prestring ^ a] 
				       @ (concat_types prestring q [] tl) |
 concat_types prestring (a::q) r tl = 
		(generate_constnames_OUTPUT (prestring ^ a ^ "_I_") r tl) 
		@ (concat_types prestring q r tl);
 val g = concat_constrs (search_in_keylist tl a) tl;
in
 concat_types prestring g r tl
end;

fun make_type_decl a tl =
let
        val astr = type_to_string_OUTPUT a;
        val dl = generate_constnames_OUTPUT "" [a] tl;
        val cl = comma_list_of dl;
in
        ("enum " ^ astr ^ " {" ^ cl ^ "};\n")
end;
in
 (make_type_decl a tl) ^ (make_type_decls r tl)
end;

fun check_finity gl [] [] true = true |
check_finity gl bl [] true = (check_finity gl [] bl false) |
check_finity _ _ [] false =
error "used datatypes are not finite" |
check_finity gl bl ((t,cl)::r) b =
let
fun listmem [] _ = true |
listmem (a::r) l = if (a mem l) then (listmem r l) else false;
fun snd_listmem [] _ = true |
snd_listmem ((a,b)::r) l = if (listmem b l) then (snd_listmem r l) else false;
in
(if (snd_listmem cl gl) then (check_finity (t::gl) bl r true)
else (check_finity gl ((t,cl)::bl) r b))
end;

fun preprocess_td sg t [] done = [] |
preprocess_td sg t (a::b) done =
let
fun extract_hd sg (_ $ Abs(_,_,r)) = extract_hd sg r |
extract_hd sg (Const("Trueprop",_) $ r) = extract_hd sg r |
extract_hd sg (Var(_,_) $ r) = extract_hd sg r |
extract_hd sg (a $ b) = extract_hd sg a |
extract_hd sg (Const(s,t)) = post_last_dot s |
extract_hd _ _ =
error "malformed constructor term in a induct-theorem";
fun list_of_param_types sg tl pl (_ $ Abs(_,t,r)) =
let
 fun select_type [] [] t = t |
 select_type (a::r) (b::s) t =
 if (t=b) then a else (select_type r s t) |
 select_type _ _ _ =
 error "wrong number of argument of a constructor in a induct-theorem";
in
 (select_type tl pl t) :: (list_of_param_types sg tl pl r)
end |
list_of_param_types sg tl pl (Const("Trueprop",_) $ r) = list_of_param_types sg tl pl r |
list_of_param_types _ _ _ _ = [];
fun split_constr sg tl pl a = (extract_hd sg a,list_of_param_types sg tl pl a);
fun split_constrs _ _ _ [] = [] |
split_constrs sg tl pl (a::r) = (split_constr sg tl pl a) :: (split_constrs sg tl pl r);
fun new_types [] = [] |
new_types ((t,l)::r) =
let
 fun ex_bool [] = [] |
 ex_bool ((Type("bool",[]))::r) = ex_bool r |
 ex_bool ((Type("*",[a,b]))::r) = ex_bool (a::b::r) |
 ex_bool (s::r) = s:: (ex_bool r);
 val ll = ex_bool l
in
 (ll @ (new_types r))
end;
in
        if (a mem done)
        then (preprocess_td sg t b done)
        else
        (let
	 fun qtn (Type(a,tl)) = (a,tl) |
	 qtn _ = error "unexpected type variable in preprocess_td";
	 val s =  post_last_dot(fst(qtn a));
	 fun param_types ((Const("Trueprop",_)) $ (_ $ (Var(_,Type(_,t)))))  = t |
	 param_types _ = error "malformed induct-theorem in preprocess_td";	
	 val pl = param_types (concl_of (get_thm t (s ^ ".induct")));		
         val l = split_constrs sg (snd(qtn a)) pl (prems_of (get_thm t (s ^ ".induct")));
	 val ntl = new_types l;
        in 
        ((a,l) :: (preprocess_td sg t (ntl @ b) (a :: done)))
        end)
end;

fun extract_type_names_prems sg [] = [] |
extract_type_names_prems sg (a::b) =
let
fun analyze_types sg [] = [] |
analyze_types sg [Type(a,[])] =
(let
 val s = (Sign.string_of_typ sg (Type(a,[])))
in
 (if (s="bool") then ([]) else ([Type(a,[])]))
end) |
analyze_types sg [Type("*",l)] = analyze_types sg l |
analyze_types sg [Type("fun",l)] = analyze_types sg l |
analyze_types sg [Type(t,l)] = ((Type(t,l))::(analyze_types sg l)) |
analyze_types sg (a::l) = (analyze_types sg [a]) @ (analyze_types sg l);
fun extract_type_names sg (Const("==",_)) = [] |
extract_type_names sg (Const("Trueprop",_)) = [] |
extract_type_names sg (Const(_,typ)) = analyze_types sg [typ] |
extract_type_names sg (a $ b) = (extract_type_names sg a) @ (extract_type_names sg b) |
extract_type_names sg (Abs(x,T,t)) = (analyze_types sg [T]) @ (extract_type_names sg t) |
extract_type_names _ _ = [];
in
 (extract_type_names sg a) @ extract_type_names_prems sg b
end;

(**********************************************************)
(* mk_mc_oracle:  new argument of MuckeOracleExn: source_thy *)

fun mk_mucke_mc_oracle (sign, MuckeOracleExn (subgoal,source_thy)) = 
  let 	val Freesubgoal = freeze_thaw subgoal;

	val prems = Logic.strip_imp_prems Freesubgoal; 
	val concl = Logic.strip_imp_concl Freesubgoal; 
	
	val Muckedecls = terms_to_decls sign prems;
	val decls_str = string_of_terms sign Muckedecls;
	
	val type_list = (extract_type_names_prems sign (prems@[concl]));
	val ctl =  preprocess_td sign source_thy type_list [];
	val b = if (ctl=[]) then true else (check_finity [Type("bool",[])] [] ctl false);
	val type_str = make_type_decls ctl 
				((Type("bool",[]),("True",[])::("False",[])::[])::ctl);
	
	val mprems = rewrite_dt_terms sign ctl prems;
	val mconcl = rewrite_dt_terms sign ctl [concl];

	val Muckeprems = transform_terms sign mprems;
        val prems_str = transform_case(string_of_terms sign Muckeprems);

        val Muckeconcl = elim_quant_in_list sign mconcl;
	val concl_str = transform_case(string_of_terms sign Muckeconcl);

	val MCstr = (
		"/**** type declarations: ****/\n" ^ type_str ^
		"/**** declarations: ****/\n" ^ decls_str ^
		"/**** definitions: ****/\n" ^ prems_str ^ 
		"/**** formula: ****/\n" ^ concl_str ^";");
	val result = callmc MCstr;
  in
(if !trace_mc then 
	(writeln ("\nmodelchecker input:\n" ^ MCstr ^ "\n/**** end ****/"))
          else ();
(case (extract_result concl_str result) of 
	true  =>  (Logic.strip_imp_concl subgoal) | 
	false => (error ("Mucke couldn't solve subgoal: \n" ^result)))) 
  end;
