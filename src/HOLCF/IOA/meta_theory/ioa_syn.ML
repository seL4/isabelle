local 

open ThyParse;

(* encoding transition specifications with a element of ParseTrans *)
datatype ParseTrans = Rel of string | PP of string*(string*string)list;
fun mk_trans_of_rel s = Rel(s);
fun mk_trans_of_prepost (s,l) = PP(s,l); 

(* stripping quotes of a string *)
fun strip [] = [] |
strip ("\""::r) = strip r |
strip (a::b) = a :: (strip b);
fun strip_quote s = implode(strip(explode(s)));

fun comma_list_of [] = "" |
comma_list_of [a] = a |
comma_list_of (a::r) = a ^ ", " ^ (comma_list_of r);

fun pair_of (a,b) = "(" ^ a ^ "," ^ b ^ ")";
fun pair_list_of [] = "" |
pair_list_of [a] = pair_of a |
pair_list_of (a::r) = (pair_of a) ^ ", " ^ (pair_list_of r);

fun trans_of (a,Rel(b)) = "(" ^ a ^ "," ^ b ^ ", [(\"\",\"\")])" |
trans_of (a,PP(b,l)) = "(" ^ a ^ "," ^ b ^ ",[" ^ (pair_list_of l) ^ "])";
fun trans_list_of [] = "" |
trans_list_of [a] = trans_of a |
trans_list_of (a::r) = (trans_of a) ^ ", " ^ (trans_list_of r);

(**************************************************************************)
(* In den folgenden Funktionen stehen in der ersten Komponente des        *)
(* Ergebnispaares die entsprechenden Funktionsaufrufe aus ioa_package.ML, *)
(* welche die entsprechenden Automatendefinitionen generieren.            *)
(* In der zweiten Komponente m"ussen diese Definitionen nochmal           *)
(* aufgef"uhrt werden, damit diese dann als Axiome genutzt werden k"onnen *)
(**************************************************************************)
fun mk_ioa_decl t (aut,((((((action_type,inp),out),int),states),initial),trans)) =
let
val automaton_name = strip_quote aut;
in
(
"|> IoaPackage.add_ioa " ^ aut ^ " " ^ action_type ^ "\n" ^
"[" ^ (comma_list_of inp) ^ "]\n" ^
"[" ^ (comma_list_of out) ^ "]\n" ^
"[" ^ (comma_list_of int) ^ "]\n" ^
"[" ^ (pair_list_of states) ^ "]\n" ^
initial ^ "\n" ^
"[" ^ (trans_list_of trans) ^ "]"
,
[automaton_name ^ "_initial_def", automaton_name ^ "_asig_def"
,automaton_name ^ "_trans_def",automaton_name ^ "_def"]
)
end;

fun mk_composition_decl (aut,autlist) =
let
val automaton_name = strip_quote aut;
in
(
"|> IoaPackage.add_composition " ^ aut ^ "\n" ^
"[" ^ (comma_list_of autlist) ^ "]"
,
[automaton_name ^ "_def"]
)
end;

fun mk_hiding_decl (aut,(actlist,source_aut)) =
let
val automaton_name = strip_quote aut;
val source_name = strip_quote source_aut;
in
(
"|> IoaPackage.add_hiding " ^ aut ^ " " ^ source_aut ^ "\n" ^
"[" ^ (comma_list_of actlist) ^ "]"
,
[automaton_name ^ "_def"]
)
end;

fun mk_restriction_decl (aut,(source_aut,actlist)) =
let
val automaton_name = strip_quote aut;
val source_name = strip_quote source_aut;
in
(
"|> IoaPackage.add_restriction " ^ aut ^ " " ^ source_aut ^ "\n" ^
"[" ^ (comma_list_of actlist) ^ "]"
,
[automaton_name ^ "_def"]
)
end;

fun mk_rename_decl (aut,(source_aut,rename_f)) = 
let
val automaton_name = strip_quote aut;
in
("|> IoaPackage.add_rename " ^ aut ^ " " ^ source_aut ^ " " ^ rename_f
,
[automaton_name ^ "_def"]
)
end;

(****************************************************************)
(* Ab hier Angabe der Einlesepattern f"ur die Sektion automaton *)
(****************************************************************)
val actionlist = enum1 "," (string)
val inputslist = "inputs" $$-- actionlist
val outputslist = "outputs" $$-- actionlist
val internalslist = "internals" $$-- actionlist
val stateslist =
	"states" $$--
	repeat1 (name --$$ "::" -- typ)
val initial = 
	"initially" $$-- string
val assign_list = enum1 "," (name --$$ ":=" -- string)
val pre =
	"pre" $$-- string
val post =
	"post" $$-- assign_list
val post1 = ((optional pre "\"True\"") -- post) >> mk_trans_of_prepost
val pre1 = (pre -- (optional post [])) >> mk_trans_of_prepost
val transrel =	("transrel" $$-- string) >> mk_trans_of_rel
val transition = string -- 
	(transrel || pre1 || post1)
val translist = "transitions" $$--
	repeat1 (transition)
val ioa_decl =
  (name -- ("="  $$--
	("signature" $$-- 
	("actions" $$--
	(typ --
	(optional inputslist []) --
	(optional outputslist []) --
	(optional internalslist []) --
	 stateslist --
	(optional initial "\"True\"") --
	translist)
	)))
  >> mk_ioa_decl thy)
||
  (name -- ("=" $$--
	("compose" $$-- (enum1 "," name))) >> mk_composition_decl)
||
  (name -- ("=" $$--
	("hide" $$-- (enum1 "," string) --
		("in" $$-- name))) >> mk_hiding_decl)
||
  (name -- ("=" $$--
        ("restrict" $$-- name --
                ("to" $$-- (enum1 "," string)))) >> mk_restriction_decl)
||
  (name -- ("=" $$--
	("rename" $$-- name -- ("using" $$-- string))) >> mk_rename_decl)
;

in
(******************************************************************)
(* im folgenden werden in der ersten Liste alle beim Einlesen von *)
(* Automaten vorkommende Schl"usselw"orter aufgef"uhrt, in der    *)
(* zweiten Liste wird die Syntaxsektion automaton definiert       *)
(* mitsamt dessen Einlesepattern ioa_decl                         *)
(******************************************************************)
val _ = ThySyn.add_syntax
 ["signature","actions","inputs", "outputs", "internals", "states", "initially",
  "transitions", "pre", "post", "transrel",":=",
"compose","hide","in","restrict","to","rename","using"]
 [axm_section "automaton" "" ioa_decl];

end; 
