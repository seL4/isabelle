(*  Title:      ioa_package.ML
    ID:         $Id$
*)

signature IOA_PACKAGE =
sig
  val add_ioa: string -> string ->
		 (string) list -> (string) list -> (string) list ->
		(string * string) list -> string ->
		(string * string * (string * string)list) list
	-> theory -> theory
 val add_ioa_i : string -> string ->
                 (string) list -> (string) list -> (string) list ->
                (string * string) list -> string ->
                (string * string * (string * string)list) list
	-> theory -> theory
 val add_composition : string -> (string)list -> theory -> theory
 val add_composition_i : string -> (string)list -> theory -> theory
 val add_hiding : string -> string -> (string)list -> theory -> theory
 val add_hiding_i : string -> string -> (string)list -> theory -> theory
 val add_restriction : string -> string -> (string)list -> theory -> theory
 val add_restriction_i : string -> string -> (string)list -> theory -> theory
 val add_rename : string -> string -> string -> theory -> theory
 val add_rename_i : string -> string -> string -> theory -> theory
end;

structure IoaPackage(* FIXME : IOA_PACKAGE *) =
struct

local

exception malformed;

(* for usage of hidden function no_attributes of structure Thm : *)
fun no_attributes x = (x, []);

(* stripping quotes *)
fun strip [] = [] |
strip ("\""::r) = strip r |
strip (a::r) = a :: (strip r);
fun strip_quote s = implode(strip(explode(s)));

(* used by *_of_varlist *)
fun extract_first (a,b) = strip_quote a;
fun extract_second (a,b) = strip_quote b;
(* following functions producing sth from a varlist *)
fun comma_list_of_varlist [] = "" |
comma_list_of_varlist [a] = extract_first a |
comma_list_of_varlist (a::r) = (extract_first a) ^ "," ^ (comma_list_of_varlist r);
fun primed_comma_list_of_varlist [] = "" |
primed_comma_list_of_varlist [a] = (extract_first a) ^ "'" |
primed_comma_list_of_varlist (a::r) = (extract_first a) ^ "'," ^
 (primed_comma_list_of_varlist r);
fun type_product_of_varlist [] = "" |
type_product_of_varlist [a] = "(" ^ extract_second(a) ^ ")" |
type_product_of_varlist(a::r) = "(" ^ extract_second(a) ^ ")*" ^ type_product_of_varlist r;

(* listing a list *)
fun list_elements_of [] = "" |
list_elements_of (a::r) = a ^ " " ^ (list_elements_of r);

(* extracting type parameters from a type list *)
(* fun param_tupel thy [] res = res |
param_tupel thy ((Type(_,l))::r) res = param_tupel thy (l @ r) res |
param_tupel thy ((TFree(a,_))::r) res = 
if (a mem res) then (param_tupel thy r res) else (param_tupel thy r (a::res)) |
param_tupel thy (a::r) res =
error ("one component of a statetype is a TVar: " ^ (Sign.string_of_typ (sign_of thy) a));
*)

(* used by constr_list *)
fun extract_constrs thy [] = [] |
extract_constrs thy (a::r) =
let
fun is_prefix [] s = true
| is_prefix (p::ps) [] = false
| is_prefix (p::ps) (x::xs) = (p=x) andalso (is_prefix ps xs);
fun delete_bold [] = []
| delete_bold (x::xs) = if (is_prefix ("\^["::"["::"1"::"m"::[]) (x::xs))
        then (let val (_::_::_::s) = xs in delete_bold s end)
        else (if (is_prefix ("\^["::"["::"0"::"m"::[]) (x::xs))
                then  (let val (_::_::_::s) = xs in delete_bold s end)
                else (x::delete_bold xs));
fun delete_bold_string s = implode(delete_bold(explode s));
(* from a constructor term in *.induct (with quantifiers,
"Trueprop" and ?P stripped away) delivers the head *)
fun extract_hd (_ $ Abs(_,_,r)) = extract_hd r |
extract_hd (Const("Trueprop",_) $ r) = extract_hd r |
extract_hd (Var(_,_) $ r) = extract_hd r |
extract_hd (a $ b) = extract_hd a |
extract_hd (Const(s,_)) = s |
extract_hd _ = raise malformed;
(* delivers constructor term string from a prem of *.induct *)
fun extract_constr thy (_ $ Abs(a,T,r)) = extract_constr thy (snd(variant_abs(a,T,r)))|
extract_constr thy (Const("Trueprop",_) $ r) = extract_constr thy r |
extract_constr thy (Var(_,_) $ r) =  delete_bold_string(Sign.string_of_term (sign_of thy) r) |
extract_constr _ _ = raise malformed;
in
(extract_hd a,extract_constr thy a) :: (extract_constrs thy r)
end;

(* delivering list of constructor terms of a datatype *)
fun constr_list thy atyp =
let
fun act_name thy (Type(s,_)) = s |
act_name _ s = 
error("malformed action type: " ^ (Sign.string_of_typ (sign_of thy) s));
fun afpl ("." :: a) = [] |
afpl [] = [] |
afpl (a::r) = a :: (afpl r);
fun unqualify s = implode(rev(afpl(rev(explode s))));
val q_atypstr = act_name thy atyp;
val uq_atypstr = unqualify q_atypstr;
val prem = prems_of (get_thm thy (uq_atypstr ^ ".induct"));
in
extract_constrs thy prem
handle malformed =>
error("malformed theorem : " ^ uq_atypstr ^ ".induct")
end;

fun check_for_constr thy atyp (a $ b) =
let
fun all_free (Free(_,_)) = true |
all_free (a $ b) = if (all_free a) then (all_free b) else false |
all_free _ = false; 
in 
if (all_free b) then (check_for_constr thy atyp a) else false
end |
check_for_constr thy atyp (Const(a,_)) =
let
val cl = constr_list thy atyp;
fun fstmem a [] = false |
fstmem a ((f,s)::r) = if (a=f) then true else (fstmem a r)
in
if (fstmem a cl) then true else false
end |
check_for_constr _ _ _ = false;

(* delivering the free variables of a constructor term *)
fun free_vars_of (t1 $ t2) = (free_vars_of t1) @ (free_vars_of t2) |
free_vars_of (Const(_,_)) = [] |
free_vars_of (Free(a,_)) = [a] |
free_vars_of _ = raise malformed;

(* making a constructor set from a constructor term (of signature) *)
fun constr_set_string thy atyp ctstr =
let
val trm = #t(rep_cterm(read_cterm (sign_of thy) (ctstr,atyp)));
val l = free_vars_of trm
in
if (check_for_constr thy atyp trm) then
(if (l=[]) then ("{" ^ ctstr ^ "}")
else "(UN " ^ (list_elements_of l) ^ ". {" ^ ctstr ^ "})")
else (raise malformed) 
handle malformed => 
error("malformed action term: " ^ (Sign.string_of_term (sign_of thy) trm))
end;

(* extracting constructor heads *)
fun constructor_head thy atypstr s =
let
fun hd_of (Const(a,_)) = a |
hd_of (t $ _) = hd_of t |
hd_of _ = raise malformed;
val trm = #t(rep_cterm(read_cterm (sign_of thy) (s,#T(rep_ctyp(read_ctyp (sign_of thy) atypstr))) ))
in
hd_of trm handle malformed =>
error("malformed constructor of datatype " ^ atypstr ^ ": " ^ s)
end;
fun constructor_head_list _ _ [] = [] |
constructor_head_list thy atypstr (a::r) =
 (constructor_head thy atypstr a)::(constructor_head_list thy atypstr r);

(* producing an action set *)
fun action_set_string thy atyp [] = "{}" |
action_set_string thy atyp [a] = constr_set_string thy atyp (strip_quote a) |
action_set_string thy atyp (a::r) = (constr_set_string thy atyp (strip_quote a)) ^
         " Un " ^ (action_set_string thy atyp r);

(* used by extend *)
fun pstr s [] = "(" ^ s ^ "' = " ^ s ^ ")" |
pstr s ((a,b)::r) =
if (s=a) then ("(" ^ s ^ "' = (" ^ b ^ "))") else (pstr s r);
fun poststring [] l = "" |
poststring [(a,b)] l = pstr a l |
poststring ((a,b)::r) l = (pstr a l) ^ " & " ^ (poststring r l);

(* extends a (action string,condition,assignlist) tupel by a
(action term,action string,condition,pseudo_condition,bool) tupel, used by extended_list 
(where bool indicates whether there is a precondition *)
fun extend thy atyp statetupel (actstr,r,[]) =
let
val trm = #t(rep_cterm(read_cterm (sign_of thy) (actstr,atyp)));
val rtrm = #t(rep_cterm(read_cterm (sign_of thy) (r,Type("bool",[]))));
val flag = if (rtrm=Const("True",Type("bool",[]))) then false else true
in
if (check_for_constr thy atyp trm)
then (trm,actstr, "(" ^ r ^ ") & " ^ (poststring statetupel []),r,flag)
else
error("transition " ^ actstr ^ " is not a pure constructor term")
end |
extend thy atyp statetupel (actstr,r,(a,b)::c) =
let
fun pseudo_poststring [] = "" |
pseudo_poststring ((a,b)::[]) = "(" ^ a ^ " = (" ^ b ^ "))" |
pseudo_poststring ((a,b)::r) = "(" ^ a ^ " = (" ^ b ^ ")) & " ^ (pseudo_poststring r); 
val trm = #t(rep_cterm(read_cterm (sign_of thy) (actstr,atyp)));
val rtrm = #t(rep_cterm(read_cterm (sign_of thy) (r,Type("bool",[]))));
val flag = if (rtrm=Const("True",Type("bool",[]))) then false else true
in
if (check_for_constr thy atyp trm) then
(if ((a="") andalso (b="") andalso (c=[])) then (trm,actstr,r,"True",false)
(* the case with transrel *)
 else 
 (trm,actstr,"(" ^ r ^ ") & " ^ (poststring statetupel ((a,b)::c)),
	"(" ^ r ^ ") & " ^ (pseudo_poststring ((a,b)::c)),flag))
else
error("transition " ^ actstr ^ " is not a pure constructor term")
end;
(* used by make_alt_string *) 
fun extended_list _ _ _ [] = [] |
extended_list thy atyp statetupel (a::r) =
	 (extend thy atyp statetupel a) :: (extended_list thy atyp statetupel r);

(* used by write_alts *)
fun write_alt thy (chead,tr) inp out int [] =
if (chead mem inp) then
(
error("Input action " ^ tr ^ " was not specified")
) else (
if (chead mem (out@int)) then
(writeln("Action " ^ tr ^ " was completedly disabled due to missing specification")) else print("");
(tr ^ " => False",tr ^ " => False")) |
write_alt thy (chead,ctrm) inp out int ((a,b,c,d,e)::r) =
let
fun hd_of (Const(a,_)) = a |
hd_of (t $ _) = hd_of t |
hd_of _ = raise malformed;
fun occurs_again c [] = false |
occurs_again c ((a,_,_,_,_)::r) = if (c=(hd_of a)) then true else (occurs_again c r);
in
if (chead=(hd_of a)) then 
(if ((chead mem inp) andalso e) then (
error("Input action " ^ b ^ " has a precondition")
) else (if (chead mem (inp@out@int)) then 
		(if (occurs_again chead r) then (
error("Two specifications for action: " ^ b)
		) else (b ^ " => " ^ c,b ^ " => " ^ d))
	else (
error("Action " ^ b ^ " is not in automaton signature")
))) else (write_alt thy (chead,ctrm) inp out int r)
handle malformed =>
error ("malformed action term: " ^ (Sign.string_of_term (sign_of thy) a))
end;

(* used by make_alt_string *)
fun write_alts thy (a,b) inp out int [] ttr = (a,b) |
write_alts thy (a,b) inp out int [c] ttr =
let
val wa = write_alt thy c inp out int ttr
in
 (a ^ (fst wa),b ^ (snd wa))
end |
write_alts thy (a,b) inp out int (c::r) ttr =
let
val wa = write_alt thy c inp out int ttr
in
 write_alts thy (a ^ (fst wa) ^ " | ", b ^ (snd wa) ^ " | ") inp out int r ttr
end;

fun make_alt_string thy inp out int atyp statetupel trans =
let
val cl = constr_list thy atyp;
val ttr = extended_list thy atyp statetupel trans;
in
write_alts thy ("","") inp out int cl ttr
end;

(* used in gen_add_ioa *)
fun check_free_primed (Free(a,_)) = 
let
val (f::r) = rev(explode a)
in
if (f="'") then [a] else []
end | 
check_free_primed (a $ b) = ((check_free_primed a) @ (check_free_primed b)) |
check_free_primed (Abs(_,_,t)) = check_free_primed t |
check_free_primed _ = [];

fun overlap [] _ = true |
overlap (a::r) l = if (a mem l) then (
error("Two occurences of action " ^ a ^ " in automaton signature")
) else (overlap r l);

(* delivering some types of an automaton *)
fun aut_type_of thy aut_name =
let
fun left_of (( _ $ left) $ _) = left |
left_of _ = raise malformed;
val aut_def = concl_of(get_thm thy (aut_name ^ "_def"));
in
(#T(rep_cterm(cterm_of (sign_of thy) (left_of aut_def))))
handle malformed => error ("malformed_theorem : " ^ aut_name ^ "_def")
end;

fun act_type_of thy (Type(pair1,(Type(pair_asig,(Type(actionset,[acttyp])::_))::_))) = acttyp |
act_type_of thy t = error ("could not extract action type of following automaton type:\n" ^
(Sign.string_of_typ (sign_of thy) t));
fun st_type_of thy (Type(pair1,_::(Type(pair2,Type(initial_set,[statetyp])::_))::_)) = statetyp |
st_type_of thy t = error ("could not extract state type of following automaton type:\n" ^
(Sign.string_of_typ (sign_of thy) t));

fun comp_st_type_of thy [a] = st_type_of thy (aut_type_of thy a) |
comp_st_type_of thy (a::r) = Type("*",[st_type_of thy (aut_type_of thy a), comp_st_type_of thy r]) |
comp_st_type_of _ _ = error "empty automaton list";

(* checking consistency of action types (for composition) *)
fun check_ac thy (a::r) =
let
fun ch_f_a thy acttyp [] = acttyp |
ch_f_a thy acttyp (a::r) =
let
val auttyp = aut_type_of thy a;
val ac = (act_type_of thy auttyp);
in
if (ac=acttyp) then (ch_f_a thy acttyp r) else (error "A")
end;
val auttyp = aut_type_of thy a;
val acttyp = (act_type_of thy auttyp);
in
ch_f_a thy acttyp r
end |
check_ac _ [] = error "empty automaton list";

fun clist [] = "" |
clist [a] = a |
clist (a::r) = a ^ " || " ^ (clist r);

(* gen_add_ioa *)

fun gen_add_ioa prep_term automaton_name action_type inp out int statetupel ini trans thy =
(writeln("Constructing automaton " ^ automaton_name ^ "...");
let
val state_type_string = type_product_of_varlist(statetupel);
val styp = #T(rep_ctyp (read_ctyp (sign_of thy) state_type_string)) ;
val state_vars_tupel = "(" ^ (comma_list_of_varlist statetupel) ^ ")";
val state_vars_primed = "(" ^ (primed_comma_list_of_varlist statetupel) ^ ")";
val atyp = #T(rep_ctyp (read_ctyp (sign_of thy) action_type));
val inp_set_string = action_set_string thy atyp inp;
val out_set_string = action_set_string thy atyp out;
val int_set_string = action_set_string thy atyp int;
val inp_head_list = constructor_head_list thy action_type inp;
val out_head_list = constructor_head_list thy action_type out;
val int_head_list = constructor_head_list thy action_type int;
val overlap_flag = ((overlap inp out) andalso (overlap inp int) andalso (overlap out int)); 
val alt_string = make_alt_string thy inp_head_list out_head_list int_head_list 
							atyp statetupel trans;
val thy2 = (thy
|> ContConsts.add_consts
[(automaton_name ^ "_initial", "(" ^ state_type_string ^ ")set" ,NoSyn),
(automaton_name ^ "_asig", "(" ^ action_type ^ ")signature" ,NoSyn),
(automaton_name ^ "_trans",
 "(" ^ action_type ^ "," ^ state_type_string ^ ")transition set" ,NoSyn),
(automaton_name, "(" ^ action_type ^ "," ^ state_type_string ^ ")ioa" ,NoSyn)]
|> (PureThy.add_defs o map no_attributes) (* old: Attributes.none *)
[(automaton_name ^ "_initial_def",
automaton_name ^ "_initial == {" ^ state_vars_tupel ^ "." ^ ini ^ "}"),
(automaton_name ^ "_asig_def",
automaton_name ^ "_asig == (" ^
 inp_set_string ^ "," ^ out_set_string ^ "," ^ int_set_string ^ ")"),
(automaton_name ^ "_trans_def",
automaton_name ^ "_trans == {(" ^
 state_vars_tupel ^ ", act_of_" ^ automaton_name ^ ", " ^ state_vars_primed ^
"). case act_of_" ^ automaton_name ^ " of " ^ fst(alt_string) ^ "}"),
(automaton_name ^ "_def",
automaton_name ^ " == (" ^ automaton_name ^ "_asig, " ^ automaton_name ^
"_initial, " ^ automaton_name ^ "_trans,{},{})")
])
val chk_prime_list = (check_free_primed (#t(rep_cterm(read_cterm (sign_of thy2)
( "case act_of_" ^ automaton_name ^ " of " ^ snd(alt_string),Type("bool",[]))))));
in
(
if (chk_prime_list = []) then thy2
else (
error("Precondition or assignment terms in postconditions contain following primed variables:\n"
 ^ (list_elements_of chk_prime_list)))
)
end)

fun gen_add_composition prep_term automaton_name aut_list thy =
(writeln("Constructing automaton " ^ automaton_name ^ "...");
let
val acttyp = check_ac thy aut_list; 
val st_typ = comp_st_type_of thy aut_list; 
val comp_list = clist aut_list;
in
thy
|> ContConsts.add_consts_i
[(automaton_name,
Type("*",
[Type("*",[Type("set",[acttyp]),Type("*",[Type("set",[acttyp]),Type("set",[acttyp])])]),
 Type("*",[Type("set",[st_typ]),
  Type("*",[Type("set",[Type("*",[st_typ,Type("*",[acttyp,st_typ])])]),
   Type("*",[Type("set",[Type("set",[acttyp])]),Type("set",[Type("set",[acttyp])])])])])])
,NoSyn)]
|> (PureThy.add_defs o map no_attributes)
[(automaton_name ^ "_def",
automaton_name ^ " == " ^ comp_list)]
end)

fun gen_add_restriction prep_term automaton_name aut_source actlist thy =
(writeln("Constructing automaton " ^ automaton_name ^ "...");
let
val auttyp = aut_type_of thy aut_source;
val acttyp = act_type_of thy auttyp; 
val rest_set = action_set_string thy acttyp actlist
in
thy
|> ContConsts.add_consts_i
[(automaton_name, auttyp,NoSyn)]
|> (PureThy.add_defs o map no_attributes)
[(automaton_name ^ "_def",
automaton_name ^ " == restrict " ^ aut_source ^ " " ^ rest_set)] 
end)
fun gen_add_hiding prep_term automaton_name aut_source actlist thy =
(writeln("Constructing automaton " ^ automaton_name ^ "...");
let
val auttyp = aut_type_of thy aut_source;
val acttyp = act_type_of thy auttyp; 
val hid_set = action_set_string thy acttyp actlist
in
thy
|> ContConsts.add_consts_i
[(automaton_name, auttyp,NoSyn)]
|> (PureThy.add_defs o map no_attributes)
[(automaton_name ^ "_def",
automaton_name ^ " == hide " ^ aut_source ^ " " ^ hid_set)] 
end)

fun ren_act_type_of thy funct =
let
(* going into a pseudo-proof-state to enable the use of function read *)
val _ = goal thy (funct ^ " = t");
fun arg_typ_of (Type("fun",[a,b])) = a |
arg_typ_of _ = raise malformed;
in
arg_typ_of(#T(rep_cterm(cterm_of (sign_of thy) (read(funct)))))
handle malformed => error ("could not extract argument type of renaming function term")
end;
 
fun gen_add_rename prep_term automaton_name aut_source fun_name thy =
(writeln("Constructing automaton " ^ automaton_name ^ "...");
let
val auttyp = aut_type_of thy aut_source;
val st_typ = st_type_of thy auttyp;
val acttyp = ren_act_type_of thy fun_name
in
thy
|> ContConsts.add_consts_i
[(automaton_name,
Type("*",
[Type("*",[Type("set",[acttyp]),Type("*",[Type("set",[acttyp]),Type("set",[acttyp])])]),
 Type("*",[Type("set",[st_typ]),
  Type("*",[Type("set",[Type("*",[st_typ,Type("*",[acttyp,st_typ])])]),
   Type("*",[Type("set",[Type("set",[acttyp])]),Type("set",[Type("set",[acttyp])])])])])])
,NoSyn)]
|> (PureThy.add_defs o map no_attributes)
[(automaton_name ^ "_def",
automaton_name ^ " == rename " ^ aut_source ^ " (" ^ fun_name ^ ")")]
end)

(* external interfaces *)

fun read_term sg str =
  read_cterm sg (str, HOLogic.termTVar);

fun cert_term sg tm =
  cterm_of sg tm handle TERM (msg, _) => error msg;

in

val add_ioa = gen_add_ioa read_term;
val add_ioa_i = gen_add_ioa cert_term;
val add_composition = gen_add_composition read_term;
val add_composition_i = gen_add_composition cert_term;
val add_hiding = gen_add_hiding read_term;
val add_hiding_i = gen_add_hiding cert_term;
val add_restriction = gen_add_restriction read_term;
val add_restriction_i = gen_add_restriction cert_term;
val add_rename = gen_add_rename read_term;
val add_rename_i = gen_add_rename cert_term;

end

end;
