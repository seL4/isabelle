/*
 * Definitions for the isabelle converster
 */

#define TRUE 1
#define FALSE 0
#define TAB 0x09

/*
 * Destination codes for translation; used for variable destCode
 */

#define TO_7bit   0
#define TO_LaTeX  1
#define DEFAULT_DEST TO_LaTeX

/*
 * Conversion modes: used for variable  convMode
 */

#define INCLUDE 1
#define STANDALONE 2
#define MIXED 3
#define DEFAULT_MODE INCLUDE


/*
 * Number of tab positions in tabbing environment (see file isa2latex.sty)
 */
#define NUM_TABS 12

/*
 * character for tab definitions in LaTeX:
 */
#define NORMAL_TABBING_UNIT "x"
#define BIG_TABBING_UNIT "g"

/*
 * units for tab used in tab calculations:
 */
#define TABBLANKS 8
/* 
   do not change below, the following definitions are automatically 
   configured by the perl script gen-isa2latex
*/

/*
 * Start and end index of translation tables
 * LOW: ASCII characters with bit 8 unset
 * HI:  ASCII characters with bit 8 set
 * SEQ_TABLE: length of code table for long ASCII sequences 
 */

/* BEGIN gen-isa2latex */
#define START_LOW_TABLE 32
#define END_LOW_TABLE   126
#define START_HI_TABLE  160
#define END_HI_TABLE    255
#define SEQ_TABLE       28
/* END gen-isa2latex */

