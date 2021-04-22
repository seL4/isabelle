/*  Author:     Makarius

Bash process with separate process group id.
*/

#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static void fail(const char *msg)
{
  fprintf(stderr, "%s\n", msg);
  fflush(stderr);
  exit(2);
}

static time_t now()
{
  struct timeval tv;
  if (gettimeofday(&tv, NULL) == 0) {
    return tv.tv_sec * 1000 + tv.tv_usec / 1000;
  }
  else {
    return time(NULL) * 1000;
  }
}


int main(int argc, char *argv[])
{
  /* args */

  if (argc < 2) {
    fprintf(stderr, "Bad arguments: missing TIMING_FILE\n");
    fflush(stderr);
    exit(1);
  }
  char *timing_name = argv[1];


  /* potential fork */

  time_t time_start = now();

  if (strlen(timing_name) > 0 || setsid() == -1) {
    pid_t pid = fork();

    if (pid == -1) fail("Cannot set session id (failed to fork)");
    else if (pid != 0) {
      int status;

      // ingore SIGINT
      struct sigaction sa;
      memset(&sa, 0, sizeof(sa));
      sa.sa_handler = SIG_IGN;
      sigaction(SIGINT, &sa, 0);

      if (waitpid(pid, &status, 0) == -1) {
        fail("Cannot join forked process");
      }

      /* report timing */

      if (strlen(timing_name) > 0) {
        long long timing_elapsed = now() - time_start;

        struct rusage ru;
        getrusage(RUSAGE_CHILDREN, &ru);

        long long timing_cpu =
          ru.ru_utime.tv_sec * 1000 + ru.ru_utime.tv_usec / 1000 +
          ru.ru_stime.tv_sec * 1000 + ru.ru_stime.tv_usec / 1000;

        FILE *timing_file = fopen(timing_name, "w");
        if (timing_file == NULL) fail("Cannot open timing file");
        fprintf(timing_file, "%lld %lld", timing_elapsed, timing_cpu);
        fclose(timing_file);
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

  fprintf(stdout, "%d\n", getpid());
  fflush(stdout);


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
