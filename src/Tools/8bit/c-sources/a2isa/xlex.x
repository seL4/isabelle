/*  Title:      Tools/8bit/c-sources/a2isa/xlex.x
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1996 TU Muenchen

Isabelle ASCII to 8bit converter
definitions for the lexical analyzer

WARNING: the translations should be consistent with the configuration in
         8bit/config/conv-tables.inp
*/


%{
extern FILE *finput, *foutput;

void put(char *s)
{
  while(*s)
  {
    fputc(*s++, yyout);
  }
}       
%}

%option 8bit
%option yylineno
%option noyywrap
%x STRING

%%
  yyin  = finput;
  yyout = foutput;

\\I@			{ ECHO; BEGIN(STRING); }
.			{ ECHO; }
<STRING>\\I@		{ ECHO; BEGIN(INITIAL); }
<STRING>\\[ \t]*\n[ \t]*\\	{ ECHO; }
<STRING>\n		{ ECHO; /* fprintf(stderr, 
			  	"WARNING: line %d ends inside string\n", 
				yylineno-1); */}
<STRING><<EOF>>		{ 	fprintf(stderr, 
			  	"WARNING: EOF inside string\n"); 
				yyterminate(); }

<STRING>{
   /* Pure */
!!		put("Ä");
\[\|		put("Ë");
\|\]		put("Ì");
==>		put("êë");
==		put("Ú");
=>		put("ë");
::		put("å");
'a		put("ª");
'b		put("«");
'c		put("¬");
'r		put("¸");
's		put("¹");
't		put("º");

   /* HOL */
\ \*\ 		put(" ò ");
@[ A-Za-z]	{ *yytext='®'; put(yytext); }
\ &\ 		put(" À ");
\ \|\ 		put(" Á ");
~\ 		put("¿ ");
-->		put("çè");
~=		put("Û");
\%[ A-Za-z]	{ *yytext='³'; put(yytext); }
EX!		put("Ã!");
\?!		put("Ã!");
EX\ 		put("Ã");
\?\ 		put("Ã");
ALL\ 		put("Â");
![ A-Za-z]	{ *yytext='Â'; put(yytext); }

   /* Set */
~:		put("ñ");
:		put("Î");
  /*
  > "{}"		"\mbox{$\emptyset$}"
# > "<="		"\mbox{$\subseteq$}"
  */
\ Int\ 		put("Ð");
\ Un\ 		put("Ñ");
Inter\ 		put("Ò");
Union\ 		put("Ó");

   /* Nat */
LEAST\ 		put("´");

   /* HOLCF */
->		put("è");
\*\*		put("õ");
\+\+		put("ó");

\<\<\|		put("<<|");
\<\|		put("<|");
\<\<		put("Ý");
LAM\ 		put("¤");
lub\ 		put("×");
UU		put("Ø");

  /* misc */
\|-		put("É");
\|=		put("Ê");

  /*
  >  "\Gamma\ "		"\mbox{$\Gamma$}" 
  >  "\Delta\ "		"\mbox{$\Delta$}" 
  >  "\Theta\ "		"\mbox{$\Theta$}" 
  >  "\Pi\ "		"\mbox{$\Pi$}" 
  >  "\Sigma\ "		"\mbox{$\Sigma$}" 
  >  "\Phi\ "		"\mbox{$\Phi$}" 
  >  "\Psi\ "		"\mbox{$\Psi$}" 
  >  "\Omega\ "		"\mbox{$\Omega$}" 

  >  "\delta\ "		"\mbox{$\delta$}" 
  >  "\epsilon\ "	"\mbox{$\varepsilon$}" 
  >  "\zeta\ "		"\mbox{$\zeta$}" 
  >  "\eta\ "		"\mbox{$\eta$}" 
  >  "\theta\ "		"\mbox{$\vartheta$}" 
  >  "\kappa\ "		"\mbox{$\kappa$}" 
  >  "\mu\ "		"\mbox{$\mu$}" 
  >  "\nu\ "		"\mbox{$\nu$}" 
  >  "\xi\ "		"\mbox{$\xi$}" 
  >  "\pi\ "		"\mbox{$\pi$}" 
  >  "\phi\ "		"\mbox{$\varphi$}" 
  >  "\chi\ "		"\mbox{$\chi$}" 
  >  "\psi\ "		"\mbox{$\psi$}" 
  >  "\omega\ "		"\mbox{$\omega$}" 

  >  "\lceil\ "		"\mbox{$\lceil$}" 
  >  "\rceil\ "		"\mbox{$\rceil$}" 
  >  "\lfloor\ "	"\mbox{$\lfloor$}" 
  >  "\rfloor\ "	"\mbox{$\rfloor$}" 
  >  "\sqcap\ "		"\mbox{$\sqcap$}" 
  >  "\sqcup\ "		"\mbox{$\sqcup$}"
  >  "\cdot\ "		"\mbox{$\cdot$}"

glb\ 		put("Ö");
===		put("Ù");

  /*
  >  "\sqsubset\ "	"\mbox{$\sqsubset$}" 
  >  "\prec\ "		"\mbox{$\prec$}" 
  >  "\preceq\ "	"\mbox{$\preceq$}" 
  >  "\Succ\ "		"\mbox{$\succ$}" 
  >  "\approx\ "	"\mbox{$\approx$}" 
  >  "\sim\ "		"\mbox{$\sim$}" 
  >  "\simeq\ "		"\mbox{$\simeq$}" 
  >  "\le\ "		"\mbox{$\le$}" 
  >  "\ge\ "		"\mbox{$\ge$}" 
  */

\<==		put("éê");
\<=>		put("éë");
\<--		put("æç");
\<->		put("æè");
\<-		put("æ");

  /*
  >  "\frown\ "		"\mbox{$\frown$}" 
  >  "\mapsto\ "	"\mbox{$\mapsto$}" 
  >  "\leadsto\ "	"\mbox{$\leadsto$}" 
  >  "\uparrow\ "	"\mbox{$\uparrow$}" 
  >  "\downarrow\ "	"\mbox{$\downarrow$}" 

  >  "\ominus\ "	"\mbox{$\varominus$}" 
  >  "\oslash\ "	"\mbox{$\varoslash$}" 
  >  "\subset\ "	"\mbox{$\subset$}" 
  >  "\infty\ "		"\mbox{$\infty$}" 
  >  "\Box\ "		"\mbox{$\Box$}" 
  >  "\Diamond\ "	"\mbox{$\Diamond$}" 
  >  "\circ\ "		"\mbox{$\circ$}" 
  >  "\bullet\ "	"\mbox{$\bullet$}" 
  >  "||"		"\mbox{$\parallel$}" 
  >  "\tick\ "		"\mbox{$\surd$}" 
  >  "\filter\ "	"\mbox{\copyright}"
  */
}
%%
