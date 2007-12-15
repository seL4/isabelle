/*
 * $Id$
 *
 * Simple demo for IsabelleProcess wrapper.
 *
 */

package isabelle;

public class IsabelleDemo extends IsabelleProcess {

    /* console thread */

    private class ConsoleThread extends Thread
    {
        public void run()
        {
            IsabelleProcess.Result result = null;
            while (result == null || result.kind != IsabelleProcess.Result.Kind.EXIT) {
                try {
                    result = results.take();
                    System.err.println(result.toString());
                } catch (InterruptedException ex) { }
            }
            System.err.println("Console thread terminated");
        }
    }
    private ConsoleThread consoleThread;


    /* create process */

    public IsabelleDemo(String logic) throws IsabelleProcessException
    {
        super(logic);
        consoleThread = new ConsoleThread();
        consoleThread.start();
    }
}
