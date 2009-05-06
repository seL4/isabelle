(* Author: Tobias Nipkow, Florian Haftmann, TU Muenchen *)

header {* Character and string types *}

theory String
imports List
uses "Tools/string_syntax.ML"
begin

subsection {* Characters *}

datatype nibble =
    Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 | Nibble6 | Nibble7
  | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD | NibbleE | NibbleF

lemma UNIV_nibble:
  "UNIV = {Nibble0, Nibble1, Nibble2, Nibble3, Nibble4, Nibble5, Nibble6, Nibble7,
    Nibble8, Nibble9, NibbleA, NibbleB, NibbleC, NibbleD, NibbleE, NibbleF}" (is "_ = ?A")
proof (rule UNIV_eq_I)
  fix x show "x \<in> ?A" by (cases x) simp_all
qed

instance nibble :: finite
  by default (simp add: UNIV_nibble)

datatype char = Char nibble nibble
  -- "Note: canonical order of character encoding coincides with standard term ordering"

lemma UNIV_char:
  "UNIV = image (split Char) (UNIV \<times> UNIV)"
proof (rule UNIV_eq_I)
  fix x show "x \<in> image (split Char) (UNIV \<times> UNIV)" by (cases x) auto
qed

instance char :: finite
  by default (simp add: UNIV_char)

lemma size_char [code, simp]:
  "size (c::char) = 0" by (cases c) simp

lemma char_size [code, simp]:
  "char_size (c::char) = 0" by (cases c) simp

primrec nibble_pair_of_char :: "char \<Rightarrow> nibble \<times> nibble" where
  "nibble_pair_of_char (Char n m) = (n, m)"

declare nibble_pair_of_char.simps [code del]

setup {*
let
  val nibbles = map (Thm.cterm_of @{theory} o HOLogic.mk_nibble) (0 upto 15);
  val thms = map_product
   (fn n => fn m => Drule.instantiate' [] [SOME n, SOME m] @{thm nibble_pair_of_char.simps})
      nibbles nibbles;
in
  PureThy.note_thmss Thm.lemmaK [((Binding.name "nibble_pair_of_char_simps", []), [(thms, [])])]
  #-> (fn [(_, thms)] => fold_rev Code.add_eqn thms)
end
*}

lemma char_case_nibble_pair [code, code inline]:
  "char_case f = split f o nibble_pair_of_char"
  by (simp add: expand_fun_eq split: char.split)

lemma char_rec_nibble_pair [code, code inline]:
  "char_rec f = split f o nibble_pair_of_char"
  unfolding char_case_nibble_pair [symmetric]
  by (simp add: expand_fun_eq split: char.split)

syntax
  "_Char" :: "xstr => char"    ("CHR _")


subsection {* Strings *}

types string = "char list"

syntax
  "_String" :: "xstr => string"    ("_")

setup StringSyntax.setup


subsection {* Strings as dedicated datatype *}

datatype message_string = STR string

lemmas [code del] =
  message_string.recs message_string.cases

lemma [code]: "size (s\<Colon>message_string) = 0"
  by (cases s) simp_all

lemma [code]: "message_string_size (s\<Colon>message_string) = 0"
  by (cases s) simp_all


subsection {* Code generator *}

text {* This also covers pretty syntax for list literals. *}

ML {*
local

open Basic_Code_Thingol;

fun implode_list naming t = case pairself
  (Code_Thingol.lookup_const naming) (@{const_name Nil}, @{const_name Cons})
   of (SOME nil', SOME cons') => let
          fun dest_cons (IConst (c, _) `$ t1 `$ t2) =
                if c = cons'
                then SOME (t1, t2)
                else NONE
            | dest_cons _ = NONE;
          val (ts, t') = Code_Thingol.unfoldr dest_cons t;
        in case t'
         of IConst (c, _) => if c = nil' then SOME ts else NONE
          | _ => NONE
        end
    | _ => NONE

fun decode_char naming (IConst (c1, _), IConst (c2, _)) = (case map_filter
  (Code_Thingol.lookup_const naming)[@{const_name Nibble0}, @{const_name Nibble1},
   @{const_name Nibble2}, @{const_name Nibble3},
   @{const_name Nibble4}, @{const_name Nibble5},
   @{const_name Nibble6}, @{const_name Nibble7},
   @{const_name Nibble8}, @{const_name Nibble9},
   @{const_name NibbleA}, @{const_name NibbleB},
   @{const_name NibbleC}, @{const_name NibbleD},
   @{const_name NibbleE}, @{const_name NibbleF}]
   of nibbles' as [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _] => let
          fun idx c = find_index (curry (op =) c) nibbles';
          fun decode ~1 _ = NONE
            | decode _ ~1 = NONE
            | decode n m = SOME (chr (n * 16 + m));
        in decode (idx c1) (idx c2) end
    | _ => NONE)
 | decode_char _ _ = NONE
   
fun implode_string naming mk_char mk_string ts = case
  Code_Thingol.lookup_const naming @{const_name Char}
   of SOME char' => let
        fun implode_char (IConst (c, _) `$ t1 `$ t2) =
              if c = char' then decode_char naming (t1, t2) else NONE
          | implode_char _ = NONE;
        val ts' = map implode_char ts;
      in if forall is_some ts'
        then (SOME o Code_Printer.str o mk_string o implode o map_filter I) ts'
        else NONE
      end
    | _ => NONE;

fun default_list (target_fxy, target_cons) pr fxy t1 t2 =
  Code_Printer.brackify_infix (target_fxy, Code_Printer.R) fxy [
    pr (Code_Printer.INFX (target_fxy, Code_Printer.X)) t1,
    Code_Printer.str target_cons,
    pr (Code_Printer.INFX (target_fxy, Code_Printer.R)) t2
  ];

fun pretty_list literals =
  let
    val mk_list = Code_Printer.literal_list literals;
    fun pretty pr naming thm vars fxy [(t1, _), (t2, _)] =
      case Option.map (cons t1) (implode_list naming t2)
       of SOME ts => mk_list (map (pr vars Code_Printer.NOBR) ts)
        | NONE => default_list (Code_Printer.infix_cons literals) (pr vars) fxy t1 t2;
  in (2, pretty) end;

fun pretty_list_string literals =
  let
    val mk_list = Code_Printer.literal_list literals;
    val mk_char = Code_Printer.literal_char literals;
    val mk_string = Code_Printer.literal_string literals;
    fun pretty pr naming thm vars fxy [(t1, _), (t2, _)] =
      case Option.map (cons t1) (implode_list naming t2)
       of SOME ts => (case implode_string naming mk_char mk_string ts
           of SOME p => p
            | NONE => mk_list (map (pr vars Code_Printer.NOBR) ts))
        | NONE => default_list (Code_Printer.infix_cons literals) (pr vars) fxy t1 t2;
  in (2, pretty) end;

fun pretty_char literals =
  let
    val mk_char = Code_Printer.literal_char literals;
    fun pretty _ naming thm _ _ [(t1, _), (t2, _)] =
      case decode_char naming (t1, t2)
       of SOME c => (Code_Printer.str o mk_char) c
        | NONE => Code_Printer.nerror thm "Illegal character expression";
  in (2, pretty) end;

fun pretty_message literals =
  let
    val mk_char = Code_Printer.literal_char literals;
    val mk_string = Code_Printer.literal_string literals;
    fun pretty _ naming thm _ _ [(t, _)] =
      case implode_list naming t
       of SOME ts => (case implode_string naming mk_char mk_string ts
           of SOME p => p
            | NONE => Code_Printer.nerror thm "Illegal message expression")
        | NONE => Code_Printer.nerror thm "Illegal message expression";
  in (1, pretty) end;

in

fun add_literal_list target thy =
  let
    val pr = pretty_list (Code_Target.the_literals thy target);
  in
    thy
    |> Code_Target.add_syntax_const target @{const_name Cons} (SOME pr)
  end;

fun add_literal_list_string target thy =
  let
    val pr = pretty_list_string (Code_Target.the_literals thy target);
  in
    thy
    |> Code_Target.add_syntax_const target @{const_name Cons} (SOME pr)
  end;

fun add_literal_char target thy =
  let
    val pr = pretty_char (Code_Target.the_literals thy target);
  in
    thy
    |> Code_Target.add_syntax_const target @{const_name Char} (SOME pr)
  end;

fun add_literal_message str target thy =
  let
    val pr = pretty_message (Code_Target.the_literals thy target);
  in
    thy
    |> Code_Target.add_syntax_const target str (SOME pr)
  end;

end;
*}

setup {*
  fold (fn target => add_literal_list target) ["SML", "OCaml", "Haskell"]
*}

code_type message_string
  (SML "string")
  (OCaml "string")
  (Haskell "String")

setup {*
  fold (fn target => add_literal_message @{const_name STR} target)
    ["SML", "OCaml", "Haskell"]
*}

code_instance message_string :: eq
  (Haskell -)

code_const "eq_class.eq \<Colon> message_string \<Rightarrow> message_string \<Rightarrow> bool"
  (SML "!((_ : string) = _)")
  (OCaml "!((_ : string) = _)")
  (Haskell infixl 4 "==")

code_reserved SML string
code_reserved OCaml string


types_code
  "char" ("string")
attach (term_of) {*
val term_of_char = HOLogic.mk_char o ord;
*}
attach (test) {*
fun gen_char i =
  let val j = random_range (ord "a") (Int.min (ord "a" + i, ord "z"))
  in (chr j, fn () => HOLogic.mk_char j) end;
*}

setup {*
let

fun char_codegen thy defs dep thyname b t gr =
  let
    val i = HOLogic.dest_char t;
    val (_, gr') = Codegen.invoke_tycodegen thy defs dep thyname false
      (fastype_of t) gr;
  in SOME (Codegen.str (ML_Syntax.print_string (chr i)), gr')
  end handle TERM _ => NONE;

in Codegen.add_codegen "char_codegen" char_codegen end
*}

end