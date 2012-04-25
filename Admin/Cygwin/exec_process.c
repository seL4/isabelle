/*  Author:     Makarius

Bash process group invocation on Cygwin.
*/

#include <stdlib.h>
#include <stdio.h>
#include <sys/types.h>
#include <unistd.h>
#include <process.h>


static void fail(const char *msg)
{
  printf("%s\n", msg);
  exit(2);
}


int main(int argc, char *argv[])
{
  /* args */

  if (argc != 3) {
    printf("Bad arguments\n");
    exit(1);
  }
  char *pid_name = argv[1];
  char *script = argv[2];


  /* report pid */

  FILE *pid_file;
  pid_file = fopen(pid_name, "w");
  if (pid_file == NULL) fail("Cannot open pid file");
  fprintf(pid_file, "%d", getpid());
  fclose(pid_file);


  /* setsid */

  if (getgid() == getpid()) fail("Cannot set session id");
  setsid();


  /* exec */

  char *cmd_line[4];
  cmd_line[0] = "/bin/bash";
  cmd_line[1] = "-c";
  cmd_line[2] = script;
  cmd_line[3] = NULL;

  int pid = spawnv(_P_NOWAIT, "/bin/bash", cmd_line);
  if (pid == -1) fail("Bad process");
  waitpid(pid);
}

