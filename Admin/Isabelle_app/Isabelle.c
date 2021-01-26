/*  Author:     Makarius

Main Isabelle application executable.
*/

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>
#include <libgen.h>


static void fail(const char *msg)
{
  fprintf(stderr, "%s\n", msg);
  exit(2);
}


int main(int argc, char *argv[])
{
  char **cmd_line = NULL, *cmd = NULL, *dcmd = NULL, *dname = NULL;
  int i = 0;

  dcmd = strdup(argv[0]);
  if (dcmd == NULL) fail("Failed to allocate memory");

  dname = dirname(dcmd);

  cmd_line = malloc(sizeof(char *) * (argc + 1));
  if (cmd_line == NULL) fail("Failed to allocate memory");

  cmd = malloc(strlen(dname) + strlen("/lib/scripts/Isabelle_app") + 1);
  if (cmd == NULL) fail("Failed to allocate memory");
  sprintf(cmd, "%s/lib/scripts/Isabelle_app", dname);

  cmd_line[0] = cmd;
  for (i = 1; i < argc; i++) cmd_line[i] = argv[i];
  cmd_line[argc] = NULL;

  execvp(cmd, cmd_line);
  fprintf(stderr, "Failed to execute application script \"%s\"\n", cmd);
  exit(2);
}
