(*  Title:      Pure/Thy/syntax.ML
    ID:         $Id$
    Author:     Sonia Mahjoub and Tobias Nipkow and Markus Wenzel, TU Muenchen

Definition of theory syntax together with translation to ML code.
*)

signature THYSYN =
 sig
  datatype basetype = Thy  of string
                    | File of string

   val read: string list -> string
 end;



functor ThySynFUN (Parse: PARSE): THYSYN =
struct


(*-------------- OBJECT TO STRING TRANSLATION ---------------*)

fun parent s = "(" ^ s ^ ")";

fun pair(a, b) = parent(a ^ ", " ^ b);

fun triple(a, b, c) = parent(a ^ ", " ^ b ^ ", " ^ c);

fun pair_quote(a, b) = pair(quote a, quote b);

fun pair_quote2(a, b) = pair(a, quote b);

fun bracket s = "[" ^ s ^ "]";

val comma = space_implode ", ";

val bracket_comma = bracket o comma;

val big_bracket_comma = bracket o space_implode ",\n";

fun big_bracket_comma_ind ind strs = bracket (space_implode (",\n" ^ ind) strs);

val bracket_comma_quote = bracket_comma o (map quote);


(*------------------- ABSTRACT SYNTAX FUNCTIONS ---------------------*)

datatype mixfix = Mixfix of string * string * string
                | Delimfix of string
                | Infixl of string
                | Infixr of string
                | Binder of string * string
                | TInfixl of string
                | TInfixr of string;


datatype pfix_or_mfix = Pref of string | Mixf of string;
datatype type_or_abbr = Typed of pfix_or_mfix | Abbrd of pfix_or_mfix;

fun pm_proj(Pref s) = s
  | pm_proj(Mixf s) = s;

fun ta_proj(Typed s) = s
  | ta_proj(Abbrd s) = s;

fun split_decls l =
    let val (p, m) = partition (fn Pref _ => true | _ => false) l;
    in (big_bracket_comma_ind "   " (map pm_proj p), map pm_proj m) end;

fun split_decls_type l =
  let val (t,a) = partition (fn Typed _ => true | _ => false) l
      val (tp,tm) = partition (fn Pref _ => true | _ => false) (map ta_proj t)
      val (ap,am) = partition (fn Pref _ => true | _ => false) (map ta_proj a)
    in (big_bracket_comma_ind "   " (map pm_proj tp),
         big_bracket_comma_ind "   " (map pm_proj ap),
         (map pm_proj tm) @ (map pm_proj am))
  end;


fun delim_mix (s, None) = Delimfix(s)
  | delim_mix (s, Some(l, n)) = Mixfix(s, l, n);

fun mixfix (sy, c, ty, l, n) =  "Mixfix(" ^ comma[quote sy, c, ty, l, n] ^ ")";

fun infixrl(ty, c, n) = parent(comma[ty, c, n]);

fun binder(sy, c, ty, n) = "Binder(" ^ comma[quote sy, c, ty, "0", n] ^ ")";

fun delimfix (sy, c, ty) = "Delimfix(" ^ comma[quote sy, c, ty] ^ ")";

fun tinfixrl (ty, n) = "(" ^ comma[ty, ty, n] ^ ")";

fun mk_mfix((c, ty), mfix) =
      let val cs = quote c and tys = quote ty
      in case mfix of
           Mixfix(sy, l, n) => mixfix (sy, tys, cs, l, n)
         | Infixr(n) => "Infixr" ^ infixrl(cs, tys, n)
         | Infixl(n) => "Infixl" ^ infixrl(cs, tys, n)
         | Binder(sy, n) => binder(sy, tys, cs, n)
         | TInfixl(n) => "TInfixl" ^ tinfixrl(cs, n)
         | TInfixr(n) => "TInfixr" ^ tinfixrl(cs, n)
         | Delimfix(sy) => delimfix(sy, tys, cs)
      end;


fun mk_mixfix((cs, ty), None) =
      [Pref(pair(bracket_comma_quote cs, quote ty))]
  | mk_mixfix((c::cs, ty), Some(mfix)) =
      Mixf(mk_mfix((c, ty), mfix)) :: mk_mixfix((cs, ty), Some(mfix))
  | mk_mixfix(([], _), _) = [];

fun mk_type_decl((ts, n), None) = [Typed(Pref(pair(bracket_comma_quote ts, n)))]
  | mk_type_decl((t::ts, n), Some(tinfix)) =
      [Typed(Pref(pair(bracket(quote t), n))), Typed(Mixf(mk_mfix((t, n), tinfix)))] @
      mk_type_decl((ts, n), Some(tinfix))
  | mk_type_decl(([], n), Some(tinfix)) = [];

fun mk_abbr_decl(((ts, a), b), None) =
    [Abbrd(Pref(triple(quote a, ts, quote b)))]
  | mk_abbr_decl(((ts, a), b), Some(tinfix)) =
      [Abbrd(Pref(triple(quote a, ts, quote b))), Abbrd(Mixf(mk_mfix((a, "0"), tinfix)))];

fun mk_extension (((((((cl, def), (ty, ab, tinfix)), ar), (co, mfix)), tr), ax), ml) =
  ((cl, def, ty, ab, ar, co, ax), big_bracket_comma_ind "    " tinfix,
    big_bracket_comma_ind "     " mfix, big_bracket_comma_ind "     " tr, ml);

fun add_val((id, _), s) = "val " ^ id ^ " = get_axiom thy " ^ quote id ^ "\n" ^ s;

fun mk_rules ps =
  let
    val axs = big_bracket_comma_ind "  " (map pair_quote ps);
    val vals = foldr add_val (ps, "")
  in
    axs ^ "\n\n" ^ vals
  end;

fun mk_struct (id, s) = "structure " ^ id ^ " =\nstruct\n" ^ s ^ "\nend;\n";


fun mk_sext mfix trans =
  "Some (NewSext {\n\
\   mixfix =\n    " ^ mfix ^ ",\n\
\   xrules =\n    " ^ trans ^ ",\n\
\   parse_ast_translation = parse_ast_translation,\n\
\   parse_translation = parse_translation,\n\
\   print_translation = print_translation,\n\
\   print_ast_translation = print_ast_translation})";

fun mk_simple_sext mfix =
  "Some (Syntax.simple_sext\n   " ^ mfix ^ ")";

fun mk_ext ((cl, def, ty, ab, ar, co, ax), sext) =
  " (" ^ space_implode ",\n  " [cl, def, ty, ab, ar, co, sext] ^ ")\n " ^ ax ^ "\n";

fun mk_ext_thy (base, name, ext, sext) =
  "extend_theory (" ^ base ^ ")\n " ^ quote name ^ "\n" ^ mk_ext (ext, sext);

val preamble =
  "\nlocal\n\
  \ val parse_ast_translation = []\n\
  \ val parse_translation = []\n\
  \ val print_translation = []\n\
  \ val print_ast_translation = []\n\
  \in\n\n\
  \(**** begin of user section ****)\n";

val postamble = "\n(**** end of user section ****)\n";

fun mk_structure ((name, base), Some (ext, tinfix, mfix, trans, ml)) =
      let
        val noext = ("[]", "[]", "[]", "[]", "[]", "[]", "[]");
        val basethy =
          if tinfix = "[]" then base ^ (quote name)
          else mk_ext_thy (base ^ (quote name), name ^ "(type infix)", noext, mk_simple_sext tinfix);
        val sext =
          if mfix = "[]" andalso trans = "[]" andalso ml = "" then "None"
          else mk_sext mfix trans;
        val thy = "val thy = " ^ mk_ext_thy (basethy, name, ext, sext);
      in
        mk_struct (name, preamble ^ ml ^ postamble ^ thy ^ "\nend")
      end
  | mk_structure ((name, base), None) =
      mk_struct (name, "\nval thy = " ^ base ^ (quote name));

datatype basetype = Thy  of string
                  | File of string;

fun merge thys =
  let fun make_list (Thy t :: ts) =
            ("Thy \"" ^ t ^ "\"") :: make_list ts
        | make_list (File t :: ts) =
            ("File \"" ^ t ^ "\"") :: make_list ts
        | make_list [] = []
  in "base_on " ^ (bracket (space_implode "," (make_list thys))) ^ " " end;



(*------------------------ PARSERS -------------------------*)


open Parse

(*------------------- VARIOUS PARSERS ----------------------*)

val emptyl = empty >> K "[]";

val ids  =  list_of1 id >> bracket_comma_quote;
(* -> "[id1, id2, ..., idn]" *)

val stgorids =  list_of1 (stg || id);
val stgorid = stg || id;

val sort =    id >> (bracket o quote)
           || "{" $$-- (ids || emptyl) --$$ "}";
(* -> "[id]"
   -> "[id1, ..., idn]"  *)

val infxl = "infixl" $$-- !! nat
and infxr = "infixr" $$-- !! nat


(*------------------- CLASSES PARSER ----------------------*)




val class  =  (id >> quote) -- ( "<" $$-- (!! ids)  ||  emptyl)   >> pair;

(* -> "(id, [id1, ..., idn])"
   ||
   -> "(id, [])"  *)


val classes =  "classes" $$-- !!(repeat1 class) >> bracket_comma
            || emptyl;


(* "[(id, [..]), ..., (id, [...])]" *)



(*------------------- DEFAULT PARSER ---------------------*)


val default =  "default" $$-- !!sort
           ||  emptyl;

(* -> "[]"
   -> "[id]"
   -> "[id1, ..., idn]"  *)


(*-------------------- TYPES  PARSER  ----------------------*)

val xtypevar = typevar >> quote;

val type_vars_decl = xtypevar >> (fn t => [t])
                 ||  "(" $$-- list_of1(xtypevar) --$$ ")"
                 ||  empty >> K [];

val abbr_vars_decl = xtypevar >> bracket
                 ||  "(" $$-- list_of1(xtypevar) --$$ ")" >> bracket_comma
                 ||  empty >> K "[]";

val type_decl =  stgorids -- nat
              || type_vars_decl -- stgorid
                         >> (fn (ns,t) => ([t], string_of_int(length(ns))));

val abbr_decl = abbr_vars_decl -- stgorid --$$ "=" -- stg;

val tyinfix =  infxl  >> (Some o TInfixl)
            || infxr  >> (Some o TInfixr);

val type_infix =   "(" $$-- tyinfix --$$ ")"
               || empty                           >> K None;

val types =  "types" $$--
                !! (repeat1 ((abbr_decl -- type_infix >> mk_abbr_decl)
                          || (type_decl -- type_infix >> mk_type_decl)))
                >> (split_decls_type o flat)
          || empty >> (K ("[]", "[]", []));

  (* ==> ("[(id, nat), ... ]", "[(id, typevars, stg), ...]", [strg, ...]) *)



(*-------------------- ARITIES PARSER ----------------------*)


val sorts =  list_of sort >> bracket_comma;

(* -> "[[id1, ...], ..., [id, ...]]" *)


val arity =  id                           >> (fn s => pair("[]", quote s))
          || "(" $$-- sorts --$$")" -- id >> (fn (l, s) => pair(l, quote s));

(* -> "([], id)"
   -> "([[id, ..], ..., [id, ..]], id)" *)

val tys = stgorids >> bracket_comma_quote;

val arities =  "arities" $$-- !! (repeat1 (tys --$$ "::" -- arity >> pair))
               >> bracket_comma
            || emptyl;

(* -> "[([id, ..], ([[id, ...], ...], id))]" *)


(*--------------------- CONSTS PARSER ---------------------*)

val natlist = "[" $$--  !!(list_of nat --$$ "]") >> bracket_comma
            || empty                             >> K "[]";


  (* "[nat, ...]"  || "[]" *)


val prio_opt =  natlist -- nat  >> Some
             || empty           >> K None;

val mfix =  stg -- !! prio_opt            >> delim_mix
         || infxl                         >> Infixl
         || infxr                         >> Infixr
         || "binder" $$-- !!(stg -- nat)  >> Binder

val const_decl = stgorids -- !! ("::" $$-- stg);

(*("[exid, ...]", stg)  *)


val mixfix =  "(" $$-- !! (mfix --$$ ")")  >> Some
           || empty                        >> K None;

(* (s, e, l, n) *)


val consts = "consts" $$--
                 !! (repeat1 (const_decl -- mixfix >> mk_mixfix))
                 >> (split_decls o flat)
           || empty >> K ("[]", []);

(* ("[([exid, ...], stg), ....]", [strg, ..])  *)


(*---------------- TRANSLATIONS PARSER --------------------*)

val xpat = "(" $$-- id --$$ ")" -- stg >> pair_quote
         || stg >> (fn s => pair_quote ("logic", s));

val arrow = $$ "=>" >> K " |-> "
         || $$ "<=" >> K " <-| "
         || $$ "==" >> K " <-> ";

val xrule = xpat -- !! (arrow -- xpat) >> (fn (xp1, (a, xp2)) => xp1 ^ a ^ xp2);

val translations = "translations" $$-- !! (repeat1 xrule)
                 || empty;


(*------------------- RULES PARSER -----------------------*)

val rules  = "rules" $$-- !! (repeat1 (id -- !! stg) >> mk_rules)
           || emptyl;

(* "[(id, stg), ...]" *)

(*----------------------- BASE PARSER -------------------------*)


fun base toks =
  let fun make_thy (b, toks) = (Thy b, toks);

      fun make_file (b, toks) = (File b, toks);

      val (b, toks) = make_thy (id toks)
                      handle _ => make_file (stg toks)
  in (b, toks) end;


(*----------------------- ML_TEXT -------------------------*)

val mltxt =  txt || empty >> K "";


(*---------------------------------------------------------*)

val extension = "+" $$-- !! (classes -- default -- types -- arities
                             -- consts -- translations -- rules --$$ "end" -- mltxt)
                       >> (Some o mk_extension)
              || empty >> K None;


val bases = base -- repeat("+" $$-- base) >> op:: ;

val theoryDef = !!(id --$$ "=" -- (bases >> merge) -- extension)
                >> mk_structure;

val read = reader theoryDef

end;

