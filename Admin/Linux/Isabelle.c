/*  Author:     Makarius

Main Isabelle application executable.
*/

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>


static void fail(const char *msg)
{
  fprintf(stderr, "%s\n", msg);
  exit(2);
}


int main(int argc, char *argv[])
{
  char **cmd_line = NULL;
  int i = 0;

  cmd_line = malloc(sizeof(char *) * argc);
  if (cmd_line == NULL) fail("Failed to allocate command line");

  cmd_line[0] = malloc(strlen(argv[0]) + 5);
  if (cmd_line[0] == NULL) fail("Failed to allocate command line");

  strcpy(cmd_line[0], argv[0]);
  strcat(cmd_line[0], ".run");

  for (i = 1; i < argc; i++) cmd_line[i] = argv[i];

  execvp(cmd_line[0], cmd_line);
  fail("Failed to execute application script");
}

