/*  Title:      Tools/8bit/c-sources/isa2latex/conv-main.c
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1996 TU Muenchen

converter for isabelle files
main file (ANSI-C)

   derived from

      spec2latex: Version from 30.3.93
      Authors  Franz Huber, B. Rumpe, David v. Oheimb 

   New or changed features:

     - flex is used to scan for multi character sequences
     - automatic generation of flex source from user translation tables
     - semantics of modes have changed, see the manpage 
     - flag for latex2e
*/         

#include <stdio.h>

/*
 * VERSION:
 */

void version(void) {
  fprintf(stderr, "Isabelle Converter, Version 1.4, 30 May 1996\n");
}

#include "conv-defs.h"
#include "conv-tables.h"

extern char *translateHi(int ch, int code);
extern char *translateLow(int ch);
extern char *translateLong(int ch);
extern void reset_tabs(void);

extern int yylex(void);

FILE* finput;                /* input file, default = stdin */
FILE* foutput;               /* output file,default = stdout */

int use2e = FALSE;           /* generate latex2e output */
int bigTabs = FALSE;         /* flag for big tabs */
int tabBlanks = TABBLANKS;   /* number of blanks subsituted for a tab */
char isa_env_beg0[200],      /* latex command to begin isa environment */
     isa_env_beg1[200];
char isa_env_end[200];       /* latex command to end   isa environment */
int cc;                      /* character counter in line  */
int tabcount;                /* counter for tab positions  */

int destCode = DEFAULT_DEST; /* default destination */
int convMode = DEFAULT_MODE; /* default conversion mode  */
int accept_ASCII = FALSE;    /* accept ASCII input for 8bit characters */

/*
 * einfache Fehlerbehandlung:
 */
 
void error(char* s, char* t) {
  fprintf(stderr, "Error! %s: %s\n", s, t);
}


/*
 * erklaert Programmbenutzung:
 */
 
void usage(void) {
  fprintf(stderr, "Isabelle converter. Valid Options:\n");
  fprintf(stderr, "<file>:    input file other than stdin\n");
  fprintf(stderr, "-o <file>: output file other than stdout\n");
  fprintf(stderr, "-a:        generate 7 bit ASCII representation\n");
  fprintf(stderr, "-A:        accept ASCII representation of graphical characters (unsafe)\n");
  fprintf(stderr, "-i:        generate LaTeX representation (default)\n");
  fprintf(stderr, "           (for inclusion into other LaTeX documents)\n"); 
  fprintf(stderr, "-s:        generate standalone LaTeX document\n");
  fprintf(stderr, "-x:        allows mixture of specifications and given LaTeX parts\n");
  fprintf(stderr, "-e:        generate LaTeX2e code (if option -s given)\n");
  fprintf(stderr, "-t <num>:  set tabulator every <num> characters\n");
  fprintf(stderr, "           (for conversion to LaTeX; default: 8)\n");
  fprintf(stderr, "-b:        'BigTabs'; generates bigger tabbings\n");
  fprintf(stderr, "           than standard for the LaTeX conversion\n");
  fprintf(stderr, "-f <strg>: use another font than the default cmr-font when converting\n");
  fprintf(stderr, "           to LaTeX. <strg> is the font-string in LaTeX syntax\n");
  fprintf(stderr, "-v:        show version number and release date\n");
  fprintf(stderr, "-h(elp):   print this message\n");
}


/*
 * main programm
 */

int main(int argc, char* argv[]) {
  char *s;                /* pointer to traverse components of argv */
  char texFont[200];      /* string for TeX font change if destCode==TO_LaTeX */
  int i,j;

  /*
   * initialize users font string:
   */
  texFont[0] = '\0';

  finput = stdin;
  foutput = stdout;

  /*
   * process command line
   */
  while (--argc > 0) {
    s = *++argv;
    if (*s++ == '-')
      switch (*s) {
        case 'v':
          version();
          exit(0);
        case 'h':
          usage();
          exit(0);
        case 'a':
          destCode = TO_7bit;
          break;
        case 'A':
          accept_ASCII = TRUE;
          break;
        case 'i':
          destCode = TO_LaTeX;
	  convMode = INCLUDE;
          break;
        case 's':
          destCode = TO_LaTeX;
	  convMode = STANDALONE;
          break;
        case 'x':
          destCode = TO_LaTeX;
	  convMode = MIXED;
          break;
        case 'e':
          use2e = TRUE;
          break;
        case 'b':
          bigTabs = TRUE;
          break;
        case 'f':
          if (--argc)
            strncpy(texFont, *++argv, 200);
          else
            error("No font specified with -f option, using default", s);
          break;
        case 'o':
          if (--argc) {
            if ((foutput = fopen(*++argv, "w")) == NULL) {
             error("Creating output file", *argv);
              exit(-1);
            }
          } else {
            error("No output file specified for option", s);
            usage();
            exit(-1);
          }
          break;
        case 't':
          { int temp;
            if (--argc) {
              if (temp = atoi(*++argv))
			    tabBlanks = temp;
			  else {
                error("Not a valid tabulator value", *argv);
                exit(-1);
              }
            } else {
              error("No value specified for option", s);
              usage();
              exit(-1);
            }
		  }
          break;
        default:
          error("Unknown option", s);
          usage();
          exit(-1);
      } /* switch */
    else
      /*
       * no further parameters with "-"; therefore we see input file:
       */
       if ((finput = fopen(--s, "r")) == NULL) {
         error("Opening input file", s);
         exit(-1);
        }
  }

  /*
   * if destination is TO_LaTeX and mode is STANDALONE then produce LaTeX header
   */
  
  if (convMode == STANDALONE) {
    if (use2e){
      fprintf(foutput, 
	 "\\documentclass[]{article}\n");
      fprintf(foutput, 
	 "\\usepackage{latexsym,amssymb,isa2latex}\n");
    } else {
      fprintf(foutput, 
	 "\\documentstyle[10pt,latexsym,amssymb,isa2latex]{article}\n");
    }
      fprintf(foutput, "\\topmargin-8ex\n"
	               "\\oddsidemargin0ex\n"
	               "\\textheight158ex\n"
	               "\\begin{document}\n");
  }

  if(texFont[0] != '\0') /* adjust font definition */
    fprintf(foutput, "%s\n", texFont);

  /*
   * prepare a tabbing environment with tabstops every 'tabBlanks' blanks:
  strcpy(isa_env_beg, "{\\isamode\\begin{tabbing}");
  for (i = 0; i < NUM_TABS; i++) {
    for (j = 0; j < tabBlanks; j++)
      strcat(isa_env_beg, bigTabs ? BIG_TABBING_UNIT : NORMAL_TABBING_UNIT);
    strcat(isa_env_beg, "\\=");
  }
  strcat(isa_env_beg, "\\kill{}\\hspace{-1.2ex}\n");
  strcpy(isa_env_end, "\n\\end{tabbing}}");
   */
  strcpy(isa_env_beg0, "{\\isabegin{}\\noindent ");
  strcpy(isa_env_beg1, "{\\isabegin{\\isamodify}\\noindent ");
  strcpy(isa_env_end , "\\isaend}\\noindent ");
  
  if (convMode == STANDALONE || (convMode == INCLUDE) && (destCode != TO_7bit))
    fprintf(foutput, isa_env_beg0);

  /*
   * start the conversion: use lexer in all modes to do the job.
   */
  
  reset_tabs();
  yylex();

  /*
   * output footers
   */

  if(convMode == STANDALONE || (convMode == INCLUDE) && (destCode != TO_7bit))
    fprintf(foutput, isa_env_end);

  if(convMode == STANDALONE) 
      fprintf(foutput, "\\end{document}\n");
  return(0);
}


