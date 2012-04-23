(*  Title:      HOL/TPTP/TPTP_Parser/tptp.lex
    Author:     Nik Sultana, Cambridge University Computer Laboratory

 Notes:
 * Omit %full in definitions to restrict alphabet to ascii.
 * Could include %posarg to ensure that we'd start counting character positions
   from 0, but it would punish performance.
 * %s AF F COMMENT; -- could improve by making stateful.

 Acknowledgements:
 * Geoff Sutcliffe for help with TPTP.
 * Timothy Bourke for his tips on getting ML-Yacc working with Poly/ML.
 * An early version of this was ported from the specification shipped with
   Leo-II, written by Frank Theiss.
 * Some boilerplate bits were taken from the ml-yacc/ml-lex manual by Roger Price.
 * Jasmin Blanchette and Makarius Wenzel for help with Isabelle integration.
*)

structure T = Tokens
type pos = int             (* Position in file *)
type lineNo = int
type svalue = T.svalue
type ('a,'b) token = ('a,'b) T.token
type lexresult = (svalue,pos) token
type lexarg = string
type arg = lexarg
val col = ref 0;
val linep = ref 1;         (* Line pointer *)
val eolpos = ref 0;

val badCh : string * string * int * int -> unit = fn
    (file_name, bad, line, col) =>
    TextIO.output(TextIO.stdOut, file_name ^ "["
          ^ Int.toString line ^ "." ^ Int.toString col
          ^ "] Invalid character \"" ^ bad ^ "\"\n");

val eof = fn file_name =>
  let
    val result = T.EOF (!linep,!col);
    val _ = linep := 0;
  in result end
(*here could check whether file ended prematurely:
 see if have open brackets, or if we're in some state other than INITIAL*)

val count_commentlines : string -> unit = fn str =>
  let
    val str' = String.explode str
    val newlines = List.filter (fn x => x = #"\n") str'
  in linep := (!linep) + (List.length newlines) end

%%
%header (functor TPTPLexFun(structure Tokens: TPTP_TOKENS));
%arg (file_name:string);

percentage_sign           = "%";
double_quote              = ["];
do_char                   = ([^"\\]|[\\]["\\]);
single_quote              = ['];
sq_char                   = ([^'\\]|[\\]['\\]);
sign                      = [+-];
dot                       = [.];
exponent                  = [Ee];
slash                     = [/];
zero_numeric              = [0];
non_zero_numeric          = [1-9];
numeric                   = [0-9];
lower_alpha               = [a-z];
upper_alpha               = [A-Z];
alpha_numeric             = ({lower_alpha}|{upper_alpha}|{numeric}|_);
dollar                    = \$;
printable_char            = .;
viewable_char             = [.\n];

dot_decimal               = {dot}{numeric}+;

ddollar                   = \$\$;
unsigned_integer          = {numeric}+;
divide                    = [/];

signed_integer            = {sign}{unsigned_integer};
exp_suffix                = {exponent}({signed_integer}|{unsigned_integer});
real                      = ({signed_integer}|{unsigned_integer}){dot_decimal}{exp_suffix}?;
rational                  = ({signed_integer}|{unsigned_integer}){divide}{unsigned_integer};

lower_word                = {lower_alpha}{alpha_numeric}*;
upper_word                = {upper_alpha}{alpha_numeric}*;
dollar_dollar_word        = {ddollar}{lower_word};
dollar_word               = {dollar}{lower_word};

distinct_object           = {double_quote}{do_char}+{double_quote};

ws                        = ([\ ]|[\t]);
single_quoted             = {single_quote}{sq_char}+{single_quote};

system_comment_one        = [%][\ ]*{ddollar}[_]*;
system_comment_multi      = [/][\*][\ ]*(ddollar)([^\*]*[\*][\*]*[^/\*])*[^\*]*[\*][\*]*[/];
system_comment            = (system_comment_one)|(system_comment_multi);

comment_line              = {percentage_sign}[^\n]*;
comment_block             = [/][\*]([^\*]*[\*]+[^/\*])*[^\*]*[\*]+[/];
comment                   = ({comment_line}|{comment_block})+;

eol                       = ("\013\010"|"\010"|"\013");

%%

{ws}*           => (col:=(!col)+size yytext; continue () );

{eol}           => (linep:=(!linep)+1;
                   eolpos:=yypos+size yytext; continue ());

"&"             => (col:=yypos-(!eolpos); T.AMPERSAND(!linep,!col));

"@+"            => (col:=yypos-(!eolpos); T.INDEF_CHOICE(!linep,!col));
"@-"            => (col:=yypos-(!eolpos); T.DEFIN_CHOICE(!linep,!col));

"!!"            => (col:=yypos-(!eolpos); T.OPERATOR_FORALL(!linep,!col));
"??"            => (col:=yypos-(!eolpos); T.OPERATOR_EXISTS(!linep,!col));

"@"             => (col:=yypos-(!eolpos); T.AT_SIGN(!linep,!col));
"^"             => (col:=yypos-(!eolpos); T.CARET(!linep,!col));

":"             => (col:=yypos-(!eolpos); T.COLON(!linep,!col));
","             => (col:=yypos-(!eolpos); T.COMMA(!linep,!col));
"="             => (col:=yypos-(!eolpos); T.EQUALS(!linep,!col));
"!"             => (col:=yypos-(!eolpos); T.EXCLAMATION(!linep,!col));
":="            => (col:=yypos-(!eolpos); T.LET(!linep,!col));
">"             => (col:=yypos-(!eolpos); T.ARROW(!linep,!col));

"<="            => (col:=yypos-(!eolpos); T.FI(!linep,!col));
"<=>"           => (col:=yypos-(!eolpos); T.IFF(!linep,!col));
"=>"            => (col:=yypos-(!eolpos); T.IMPLIES(!linep,!col));
"["             => (col:=yypos-(!eolpos); T.LBRKT(!linep,!col));
"("             => (col:=yypos-(!eolpos); T.LPAREN(!linep,!col));
"->"            => (col:=yypos-(!eolpos); T.MAP_TO(!linep,!col));
"--"            => (col:=yypos-(!eolpos); T.MMINUS(!linep,!col));
"~&"            => (col:=yypos-(!eolpos); T.NAND(!linep,!col));
"!="            => (col:=yypos-(!eolpos); T.NEQUALS(!linep,!col));
"<~>"           => (col:=yypos-(!eolpos); T.XOR(!linep,!col));
"~|"            => (col:=yypos-(!eolpos); T.NOR(!linep,!col));
"."             => (col:=yypos-(!eolpos); T.PERIOD(!linep,!col));
"++"            => (col:=yypos-(!eolpos); T.PPLUS(!linep,!col));
"?"             => (col:=yypos-(!eolpos); T.QUESTION(!linep,!col));
"]"             => (col:=yypos-(!eolpos); T.RBRKT(!linep,!col));
")"             => (col:=yypos-(!eolpos); T.RPAREN(!linep,!col));
"~"             => (col:=yypos-(!eolpos); T.TILDE(!linep,!col));
"|"             => (col:=yypos-(!eolpos); T.VLINE(!linep,!col));

{distinct_object}    => (col:=yypos-(!eolpos); T.DISTINCT_OBJECT(yytext,!linep,!col));
{rational}           => (col:=yypos-(!eolpos); T.RATIONAL(yytext,!linep,!col));
{real}               => (col:=yypos-(!eolpos); T.REAL(yytext,!linep,!col));
{signed_integer}     => (col:=yypos-(!eolpos); T.SIGNED_INTEGER(yytext,!linep,!col));
{unsigned_integer}   => (col:=yypos-(!eolpos); T.UNSIGNED_INTEGER(yytext,!linep,!col));
{dot_decimal}        => (col:=yypos-(!eolpos); T.DOT_DECIMAL(yytext,!linep,!col));
{single_quoted}      => (col:=yypos-(!eolpos); T.SINGLE_QUOTED(yytext,!linep,!col));
{upper_word}         => (col:=yypos-(!eolpos); T.UPPER_WORD(yytext,!linep,!col));
{comment}            => (col:=yypos-(!eolpos); count_commentlines yytext;T.COMMENT(yytext,!linep,!col));

"thf"          => (col:=yypos-(!eolpos); T.THF(!linep,!col));
"fof"          => (col:=yypos-(!eolpos); T.FOF(!linep,!col));
"cnf"          => (col:=yypos-(!eolpos); T.CNF(!linep,!col));
"tff"          => (col:=yypos-(!eolpos); T.TFF(!linep,!col));
"include"      => (col:=yypos-(!eolpos); T.INCLUDE(!linep,!col));

"$thf"          => (col:=yypos-(!eolpos); T.DTHF(!linep,!col));
"$fof"          => (col:=yypos-(!eolpos); T.DFOF(!linep,!col));
"$cnf"          => (col:=yypos-(!eolpos); T.DCNF(!linep,!col));
"$fot"          => (col:=yypos-(!eolpos); T.DFOT(!linep,!col));
"$tff"          => (col:=yypos-(!eolpos); T.DTFF(!linep,!col));

"$ite_f"        => (col:=yypos-(!eolpos); T.ITE_F(!linep,!col));
"$ite_t"        => (col:=yypos-(!eolpos); T.ITE_T(!linep,!col));
"$let_tf"        => (col:=yypos-(!eolpos); T.LET_TF(!linep,!col));
"$let_ff"        => (col:=yypos-(!eolpos); T.LET_FF(!linep,!col));
"$let_ft"        => (col:=yypos-(!eolpos); T.LET_FT(!linep,!col));
"$let_tt"        => (col:=yypos-(!eolpos); T.LET_TT(!linep,!col));

{lower_word}   => (col:=yypos-(!eolpos); T.LOWER_WORD(yytext,!linep,!col));
{dollar_word}  => (col:=yypos-(!eolpos); T.DOLLAR_WORD(yytext,!linep,!col));
{dollar_dollar_word}  => (col:=yypos-(!eolpos); T.DOLLAR_DOLLAR_WORD(yytext,!linep,!col));

"+"           => (col:=yypos-(!eolpos); T.PLUS(!linep,!col));
"*"           => (col:=yypos-(!eolpos); T.TIMES(!linep,!col));
"-->"         => (col:=yypos-(!eolpos); T.GENTZEN_ARROW(!linep,!col));
"<<"          => (col:=yypos-(!eolpos); T.SUBTYPE(!linep,!col));
"!>"          => (col:=yypos-(!eolpos); T.DEP_PROD(!linep,!col));
"?*"          => (col:=yypos-(!eolpos); T.DEP_SUM(!linep,!col));

":-"          => (col:=yypos-(!eolpos); T.LET_TERM(!linep,!col));
