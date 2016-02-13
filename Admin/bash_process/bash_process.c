/*  Author:     Makarius

Bash process with separate process group id.
*/

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

static void fail(const char *msg)
{
  fprintf(stderr, "%s\n", msg);
  fflush(stderr);
  exit(2);
}


int main(int argc, char *argv[])
{
  /* args */

  if (argc < 2) {
    fprintf(stderr, "Bad arguments: missing pid file\n");
    fflush(stderr);
    exit(1);
  }
  char *pid_name = argv[1];


  /* setsid */

  if (setsid() == -1) {
    pid_t pid = fork();
    int status;

    if (pid == -1) fail("Cannot set session id (failed to fork)");
    else if (pid != 0) {
      if (waitpid(pid, &status, 0) == -1) {
        fail("Cannot join forked process");
      }

      if (WIFEXITED(status)) {
        exit(WEXITSTATUS(status));
      }
      else if (WIFSIGNALED(status)) {
        exit(128 + WTERMSIG(status));
      }
      else {
        fail("Unknown status of forked process");
      }
    }
    else if (setsid() == -1) fail("Cannot set session id (after fork)");
  }


  /* report pid */

  if (strcmp(pid_name, "-") == 0) {
    fprintf(stdout, "%d\n", getpid());
    fflush(stdout);
  }
  else if (strlen(pid_name) > 0) {
    FILE *pid_file;
    pid_file = fopen(pid_name, "w");
    if (pid_file == NULL) fail("Cannot open pid file");
    fprintf(pid_file, "%d", getpid());
    fclose(pid_file);
  }


  /* shift command line */

  int i;
  for (i = 2; i < argc; i++) {
    argv[i - 2] = argv[i];
  }
  argv[argc - 2] = NULL;
  argv[argc - 1] = NULL;


  /* exec */

  execvp("bash", argv);
  fail("Cannot exec process");
}
