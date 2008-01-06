/*
 * $Id$
 *
 * Simple demo for IsabelleProcess wrapper.
 *
 * Example session with Beanshell:
 *
 *    $ cd [ISABELLE_HOME]/lib/classes
 *    $ javac isabelle/*.java
 *
 *    $ bsh
 * or
 *    $ java -Disabelle.home=[ISABELLE_HOME] -jar bsh.jar
 *    % addClassPath(".");
 *
 *    % import isabelle.*;
 *    % isabelle = new IsabelleDemo("HOL");
 *    % isabelle.command("theory Test imports Main begin");
 *    % isabelle.command("lemma \"A --> A\"");
 *    % isabelle.command("..");
 *    % isabelle.command("end");
 *    % isabelle.close();
 *
 */

package isabelle;

public class IsabelleDemo extends IsabelleProcess {
    public IsabelleDemo(String logic) throws IsabelleProcessException
    {
        super(logic);
        new Thread (new Runnable () {
            public void run()
            {
                IsabelleProcess.Result result = null;
                do {
                  try {
                    result = results.take();
                  } catch (NullPointerException ex) {
                    result = null;
                  } catch (InterruptedException ex) {
                    result = null;
                  }
                  if (result != null)
                    System.err.println(result.toString());
                  if (result.kind == IsabelleProcess.Result.Kind.EXIT) {
                    result = null;
                  }
                } while (result != null);
                System.err.println("Console thread terminated");
            }
        }).start();
    }
    
    public IsabelleDemo() throws IsabelleProcessException {
        this(null);
    }
}
