/*  Title:      Tools/8bit/c-sources/a2isa/main.c
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1996 TU Muenchen

converter for isabelle files, from ASCII to graphical characters
main file (ANSI-C)
*/

#include <stdio.h>

extern int yylex(void);

FILE* finput;                /* input file, default = stdin */
FILE* foutput;               /* output file,default = stdout */

void error(char* s, char* t)
{
  fprintf(stderr, "Error! %s: %s\n", s, t);
}

void usage(void)
{
  fprintf(stderr, "Isabelle ASCII to 8bit converter. Valid Options:\n");
  fprintf(stderr, "<file>:    input file other than stdin\n");
  fprintf(stderr, "-o <file>: output file other than stdout\n");
  fprintf(stderr, "-h(elp):   print this message\n");
}

int main(int argc, char* argv[])
{
  char *s;                /* pointer to traverse components of argv */

  finput = stdin;
  foutput = stdout;

  while (--argc > 0) {
    s = *++argv;
    if (*s++ == '-')
      switch (*s) {
        case 'h':
          usage();
          exit(0);
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

  yylex();

  return(0);
}


