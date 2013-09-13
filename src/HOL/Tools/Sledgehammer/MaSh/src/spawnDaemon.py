# http://stackoverflow.com/questions/972362/spawning-process-from-python/972383#972383
import os

def spawnDaemon(path_to_executable, *args):
    """Spawn a completely detached subprocess (i.e., a daemon).

    E.g. for mark:
    spawnDaemon("../bin/producenotify.py", "producenotify.py", "xx")
    """
    # fork the first time (to make a non-session-leader child process)
    try:
        pid = os.fork()
    except OSError, e:
        raise RuntimeError("1st fork failed: %s [%d]" % (e.strerror, e.errno))
    if pid != 0:
        # parent (calling) process is all done
        return

    # detach from controlling terminal (to make child a session-leader)
    os.setsid()
    try:
        pid = os.fork()
    except OSError, e:
        raise RuntimeError("2nd fork failed: %s [%d]" % (e.strerror, e.errno))
        raise Exception, "%s [%d]" % (e.strerror, e.errno)
    if pid != 0:
        # child process is all done
        os._exit(0)

    # and finally let's execute the executable for the daemon!
    try:
        os.execv(path_to_executable, [path_to_executable])
    except Exception, e:
        # oops, we're cut off from the world, let's just give up
        os._exit(255)
