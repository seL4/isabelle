/*
 * translation functions
 * table ranges are checked
 */


#include <stdio.h>
#include "conv-defs.h"

extern char *translationTableLow[END_LOW_TABLE - START_LOW_TABLE + 1];
extern char *translationTableHi[END_HI_TABLE - START_HI_TABLE + 1][2];
extern char *translationTableSeq[SEQ_TABLE][2];

char *translateLow(int ch) {
  if ((ch >= START_LOW_TABLE) && (ch <= END_LOW_TABLE))
    return (translationTableLow[ch - START_LOW_TABLE]);
  else {
    fprintf(stderr, "Error in translateLow!\n");
	exit(-1);
  }
}

char *translateHi(int ch, int code) { 
  /*(256 + ch) is used to convert from character to unsigned short */ 
  if (((256 + ch) >= START_HI_TABLE) && ((256 + ch) <= END_HI_TABLE))
    return (translationTableHi[(256 + ch) - START_HI_TABLE][code]);
  else {   
    fprintf(stderr, "Sorry, the file contains a high-bit character which\n");
    fprintf(stderr, "is not in the translation table!\n");
    exit(-1);
  }
}

char *translateLong(int ch, int code) {
  if ((ch < SEQ_TABLE))
    return (translationTableSeq[ch][code]);
  else {
    fprintf(stderr, "Error in translateLong!\n");
	exit(-1);
  }
}

