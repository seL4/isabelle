(* MuIOA.ML declares function mk_sim_oracle used by oracle "Sim" (see MuIOAOracle.thy).
	There, implementation relations for I/O automatons are proved using
	the model checker mucke (invoking cal_mucke_tac defined in MCSyn.ML). *)

exception SimOracleExn of (term*theory*(thm list));
exception SimFailureExn of string;

val ioa_simps = [asig_of_def,starts_of_def,trans_of_def];
val asig_simps = [asig_inputs_def,asig_outputs_def,asig_internals_def,actions_def];
val comp_simps = [par_def,asig_comp_def];
val restrict_simps = [restrict_def,restrict_asig_def];
val hide_simps = [hide_def,hide_asig_def];
val rename_simps = [rename_def,rename_set_def];

local

exception malformed;

fun fst_type (Type("*",[a,_])) = a |
fst_type _ = raise malformed; 
fun snd_type (Type("*",[_,a])) = a |
snd_type _ = raise malformed;

fun element_type (Type("set",[a])) = a |
element_type t = raise malformed;

fun IntC sg (Const("Trueprop",_) $ ((Const("op <=",_) $ (_ $ concreteIOA)) $ _)) =
let
val aut_typ = #T(rep_cterm(cterm_of sg concreteIOA));
val sig_typ = fst_type aut_typ;
val int_typ = fst_type sig_typ
in 
Const("Asig.internals",Type("fun",[sig_typ,int_typ])) $
 (Const("Automata.asig_of",Type("fun",[aut_typ,sig_typ])) $ concreteIOA)
end
|
IntC sg t =
error("malformed automaton def for IntC:\n" ^ (Sign.string_of_term sg t));

fun StartC sg (Const("Trueprop",_) $ ((Const("op <=",_) $ (_ $ concreteIOA)) $ _)) =
let
val aut_typ = #T(rep_cterm(cterm_of sg concreteIOA));
val st_typ = fst_type(snd_type aut_typ)
in
Const("Automata.starts_of",Type("fun",[aut_typ,st_typ])) $ concreteIOA
end
|
StartC sg t =
error("malformed automaton def for StartC:\n" ^ (Sign.string_of_term sg t));

fun TransC sg (Const("Trueprop",_) $ ((Const("op <=",_) $ (_ $ concreteIOA)) $ _)) = 
let
val aut_typ = #T(rep_cterm(cterm_of sg concreteIOA));
val tr_typ = fst_type(snd_type(snd_type aut_typ))
in
Const("Automata.trans_of",Type("fun",[aut_typ,tr_typ])) $ concreteIOA
end
|
TransC sg t =
error("malformed automaton def for TransC:\n" ^ (Sign.string_of_term sg t));

fun IntA sg (Const("Trueprop",_) $ ((Const("op <=",_) $ _) $ (_ $ abstractIOA))) =
let
val aut_typ = #T(rep_cterm(cterm_of sg abstractIOA));
val sig_typ = fst_type aut_typ;
val int_typ = fst_type sig_typ
in
Const("Asig.internals",Type("fun",[sig_typ,int_typ])) $
 (Const("Automata.asig_of",Type("fun",[aut_typ,sig_typ])) $ abstractIOA)
end
|
IntA sg t =
error("malformed automaton def for IntA:\n" ^ (Sign.string_of_term sg t));

fun StartA sg (Const("Trueprop",_) $ ((Const("op <=",_) $ _) $ (_ $ abstractIOA))) =
let
val aut_typ = #T(rep_cterm(cterm_of sg abstractIOA));
val st_typ = fst_type(snd_type aut_typ)
in
Const("Automata.starts_of",Type("fun",[aut_typ,st_typ])) $ abstractIOA
end
|
StartA sg t =
error("malformed automaton def for StartA:\n" ^ (Sign.string_of_term sg t));

fun TransA sg (Const("Trueprop",_) $ ((Const("op <=",_) $ _) $ (_ $ abstractIOA))) =
let
val aut_typ = #T(rep_cterm(cterm_of sg abstractIOA));
val tr_typ = fst_type(snd_type(snd_type aut_typ))
in
Const("Automata.trans_of",Type("fun",[aut_typ,tr_typ])) $ abstractIOA 
end
|
TransA sg t =
error("malformed automaton def for TransA:\n" ^ (Sign.string_of_term sg t));

fun is_prefix [] s = true
| is_prefix (p::ps) [] = false
| is_prefix (p::ps) (x::xs) = (p=x) andalso (is_prefix ps xs);

fun delete_ul [] = []
| delete_ul (x::xs) = if (is_prefix ("\^["::"["::"4"::"m"::[]) (x::xs))
        then (let val (_::_::_::s) = xs in delete_ul s end)
        else (if (is_prefix ("\^["::"["::"0"::"m"::[]) (x::xs))
                then  (let val (_::_::_::s) = xs in delete_ul s end)
                else (x::delete_ul xs));

fun delete_ul_string s = implode(delete_ul (explode s));

fun type_list_of sign (Type("*",a::b::_)) = (type_list_of sign a) @ (type_list_of sign b) |
type_list_of sign a = [(Sign.string_of_typ sign a)];

fun structured_tuple l (Type("*",s::t::_)) =
let
val (r,str) = structured_tuple l s;
in
(fst(structured_tuple r t),"(" ^ str ^ "),(" ^ (snd(structured_tuple r t)) ^ ")")
end |
structured_tuple (a::r) t = (r,a) |
structured_tuple [] _ = raise malformed;

fun varlist_of _ _ [] = [] |
varlist_of n s (a::r) = (s ^ (BasisLibrary.Int.toString(n))) :: (varlist_of (n+1) s r);

fun string_of [] = "" |
string_of (a::r) = a ^ " " ^ (string_of r);

fun tupel_typed_of _ _ _ [] = "" |
tupel_typed_of sign s n [a] = s ^ (BasisLibrary.Int.toString(n)) ^ "::" ^ a |
tupel_typed_of sign s n (a::r) =
 s ^ (BasisLibrary.Int.toString(n)) ^ "::" ^ a ^ "," ^ (tupel_typed_of sign s (n+1) r);

fun double_tupel_typed_of _ _ _ _ [] = "" |
double_tupel_typed_of sign s t n [a] =
 s ^ (BasisLibrary.Int.toString(n)) ^ "::" ^ a ^ "," ^
 t ^ (BasisLibrary.Int.toString(n)) ^ "::" ^ a |
double_tupel_typed_of sign s t n (a::r) =
 s ^ (BasisLibrary.Int.toString(n)) ^ "::" ^ a ^ "," ^
 t ^ (BasisLibrary.Int.toString(n)) ^ "::" ^ a ^ "," ^ (double_tupel_typed_of sign s t (n+1) r);

fun tupel_of _ _ _ [] = "" |
tupel_of sign s n [a] = s ^ (BasisLibrary.Int.toString(n)) |
tupel_of sign s n (a::r) = s ^ (BasisLibrary.Int.toString(n)) ^ "," ^ (tupel_of sign s (n+1) r);

fun double_tupel_of _ _ _ _ [] = "" |
double_tupel_of sign s t n [a] = s ^ (BasisLibrary.Int.toString(n)) ^ "," ^
				 t ^ (BasisLibrary.Int.toString(n)) |
double_tupel_of sign s t n (a::r) = s ^ (BasisLibrary.Int.toString(n)) ^ "," ^
		t ^ (BasisLibrary.Int.toString(n)) ^ "," ^ (double_tupel_of sign s t (n+1) r);

fun eq_string _ _ _ [] = "" |
eq_string s t n [a] = s ^ (BasisLibrary.Int.toString(n)) ^ " = " ^
			 t ^ (BasisLibrary.Int.toString(n)) |
eq_string s t n (a::r) =
 s ^ (BasisLibrary.Int.toString(n)) ^ " = " ^
 t ^ (BasisLibrary.Int.toString(n)) ^ " & " ^ (eq_string s t (n+1) r);

fun merge_var_and_type [] [] = "" |
merge_var_and_type (a::r) (b::s) = "(" ^ a ^ " ::" ^ b ^ ") " ^ (merge_var_and_type r s) |
merge_var_and_type _ _ = raise malformed;

in

fun mk_sim_oracle (sign, SimOracleExn (subgoal,t,thl)) =
(let
	val concl = (Logic.strip_imp_concl subgoal);

	val ic_str = delete_ul_string(Sign.string_of_term sign (IntC sign concl));
	val ia_str = delete_ul_string(Sign.string_of_term sign (IntA sign concl));
	val sc_str = delete_ul_string(Sign.string_of_term sign (StartC sign concl));	
	val sa_str = delete_ul_string(Sign.string_of_term sign (StartA sign concl));
	val tc_str = delete_ul_string(Sign.string_of_term sign (TransC sign concl));
	val ta_str = delete_ul_string(Sign.string_of_term sign (TransA sign concl));
	
	val action_type_str =
	Sign.string_of_typ sign (element_type(#T (rep_cterm(cterm_of sign (IntA sign concl)))));

	val abs_state_type_list =
	type_list_of sign (element_type(#T (rep_cterm(cterm_of sign (StartA sign concl)))));
	val con_state_type_list =
	type_list_of sign (element_type(#T (rep_cterm(cterm_of sign (StartC sign concl)))));

	val tupel_eq = eq_string "s" "t" 0 abs_state_type_list;

	val abs_pre_tupel_typed = tupel_typed_of sign "s" 0 abs_state_type_list;
	val abs_s_t_tupel_typed = double_tupel_typed_of sign "s" "t" 0 abs_state_type_list;
	val con_pre_tupel_typed = tupel_typed_of sign "cs" 0 con_state_type_list;
	val con_s_t_tupel_typed = double_tupel_typed_of sign "cs" "ct" 0 con_state_type_list;
	
	val abs_pre_tupel = tupel_of sign "s" 0 abs_state_type_list;
	val abs_post_tupel = tupel_of sign "t" 0 abs_state_type_list;
	val abs_s_t_tupel = double_tupel_of sign "s" "t" 0 abs_state_type_list;
	val abs_s_u_tupel = double_tupel_of sign "s" "u" 0 abs_state_type_list;
	val abs_u_t_tupel = double_tupel_of sign "u" "t" 0 abs_state_type_list;
	val abs_u_v_tupel = double_tupel_of sign "u" "v" 0 abs_state_type_list;
	val abs_v_t_tupel = double_tupel_of sign "v" "t" 0 abs_state_type_list;
	val con_pre_tupel = tupel_of sign "cs" 0 con_state_type_list;
        val con_post_tupel = tupel_of sign "ct" 0 con_state_type_list;
	val con_s_t_tupel = double_tupel_of sign "cs" "ct" 0 con_state_type_list;

        val abs_pre_varlist = varlist_of 0 "s" abs_state_type_list;
        val abs_post_varlist = varlist_of 0 "t" abs_state_type_list;
        val abs_u_varlist = varlist_of 0 "u" abs_state_type_list;
        val abs_v_varlist = varlist_of 0 "v" abs_state_type_list;
	val con_pre_varlist = varlist_of 0 "cs" con_state_type_list;
        val con_post_varlist = varlist_of 0 "ct" con_state_type_list;

        val abs_post_str = string_of abs_post_varlist;
	val abs_u_str = string_of abs_u_varlist;
	val con_post_str = string_of con_post_varlist;
	
	val abs_pre_str_typed = merge_var_and_type abs_pre_varlist abs_state_type_list;
	val abs_u_str_typed = merge_var_and_type abs_u_varlist abs_state_type_list;
        val abs_v_str_typed = merge_var_and_type abs_v_varlist abs_state_type_list;
	val con_pre_str_typed = merge_var_and_type con_pre_varlist con_state_type_list;

	val abs_pre_tupel_struct = snd(
structured_tuple abs_pre_varlist (element_type(#T(rep_cterm(cterm_of sign (StartA sign concl))))));
	val abs_post_tupel_struct = snd(
structured_tuple abs_post_varlist (element_type(#T(rep_cterm(cterm_of sign (StartA sign concl))))));
	val con_pre_tupel_struct = snd(
structured_tuple con_pre_varlist (element_type(#T(rep_cterm(cterm_of sign (StartC sign concl))))));
	val con_post_tupel_struct = snd(
structured_tuple con_post_varlist (element_type(#T(rep_cterm(cterm_of sign (StartC sign concl))))));
in
(
push_proof();
goal t 
( "(Internal_of_A = (% a::(" ^ action_type_str ^ "). a:(" ^ ia_str^
  "))) --> (Internal_of_C = (% a::(" ^ action_type_str ^ "). a:(" ^ ic_str ^ 
  "))) --> (Start_of_A = (% (" ^ abs_pre_tupel_typed ^
	"). (" ^ abs_pre_tupel_struct ^ "):(" ^ sa_str ^
  "))) --> (Start_of_C = (% (" ^ con_pre_tupel_typed ^
	"). (" ^ con_pre_tupel_struct ^ "):(" ^ sc_str ^
  "))) --> (Trans_of_A = (% (" ^ abs_s_t_tupel_typed ^ ") (a::(" ^ action_type_str ^ 
	")). ((" ^ abs_pre_tupel_struct ^ "),a,(" ^ abs_post_tupel_struct ^ ")):(" ^ ta_str ^
  "))) --> (Trans_of_C = (% (" ^ con_s_t_tupel_typed ^ ") (a::(" ^ action_type_str ^ 
	")). ((" ^ con_pre_tupel_struct ^ "),a,(" ^ con_post_tupel_struct ^ ")):(" ^ tc_str ^
  "))) --> (IntStep_of_A = (% (" ^ abs_s_t_tupel_typed ^ 
	"). ? (a::(" ^ action_type_str ^
	")). Internal_of_A a & Trans_of_A (" ^ abs_s_t_tupel ^ ") a" ^
  ")) --> (IntStepStar_of_A =  mu (% P (" ^ abs_s_t_tupel_typed ^
	 "). (" ^ tupel_eq ^ ") | (? " ^ abs_u_str ^ ". IntStep_of_A (" ^ abs_s_u_tupel ^
	 ") & P(" ^ abs_u_t_tupel ^ ")))" ^
  ") --> (Move_of_A = (% (" ^ abs_s_t_tupel_typed ^ ") (a::(" ^ action_type_str ^ 
	")). (Internal_of_C a & IntStepStar_of_A(" ^ abs_s_t_tupel ^ 
	")) | (? " ^ abs_u_str_typed ^ ". ? " ^ abs_v_str_typed ^
	". IntStepStar_of_A(" ^ abs_s_u_tupel ^ ") & " ^
	"Trans_of_A (" ^ abs_u_v_tupel ^ ") a  & IntStepStar_of_A(" ^ abs_v_t_tupel ^ "))" ^
  ")) --> (isSimCA = nu (% P (" ^ con_pre_tupel_typed ^ "," ^ abs_pre_tupel_typed ^ 
	"). (! (a::(" ^ action_type_str ^ ")) " ^ con_post_str ^
	". Trans_of_C (" ^ con_s_t_tupel ^ ") a  -->" ^ " (? " ^ abs_post_str ^
  ". Move_of_A (" ^ abs_s_t_tupel ^ ") a  & P(" ^ con_post_tupel ^ "," ^ abs_post_tupel ^ "))))" ^
 ") --> (! " ^ con_pre_str_typed ^ ". ! " ^ abs_pre_str_typed ^
	". (Start_of_C (" ^ con_pre_tupel ^ ") & Start_of_A (" ^ abs_pre_tupel ^
	")) --> isSimCA(" ^ con_pre_tupel ^ "," ^ abs_pre_tupel ^ "))");
by (REPEAT (rtac impI 1));
by (REPEAT (dtac eq_reflection 1));
(* Bis hierher wird im Kapitel 4 erl"autert, ab hier im Kapitel 5 *)
by (full_simp_tac ((simpset() delsimps [not_iff,split_part])
			      addsimps (thl @ comp_simps @ restrict_simps @ hide_simps @
                                        rename_simps @ ioa_simps @ asig_simps)) 1);
by (full_simp_tac (Mucke_ss delsimps [not_iff,split_part]) 1);
by (REPEAT (if_full_simp_tac (simpset() delsimps [not_iff,split_part]) 1));
by (call_mucke_tac t 1);
(* Bis hierher wird im Kapitel 5 erl"autert, ab hier wieder im Kapitel 4 *)
by (atac 1);
result();
pop_proof();
Logic.strip_imp_concl subgoal
)
end)
handle malformed =>
error("No suitable match to IOA types in " ^ (Sign.string_of_term sign subgoal));

end
