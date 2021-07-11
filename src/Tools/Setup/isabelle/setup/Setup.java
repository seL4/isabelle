/*  Title:      Tools/Setup/isabelle/setup/Setup.java
    Author:     Makarius

Isabelle setup tool: bootstrap from generic Java environment.
*/

package isabelle.setup;


import java.io.IOException;
import java.security.NoSuchAlgorithmException;


class Setup
{
    private static void echo(String msg)
    {
        System.out.println(msg);

    }
    private static void fail(String msg)
    {
        echo(msg);
        System.exit(2);
    }

    private static void check_args(boolean b)
    {
        if (!b) { fail("Bad command-line arguments"); }
    }

    public static void main(String[] args)
    {
        int n = args.length;
        check_args(n > 0);

        String op = args[0];
        try {
            switch (op) {
                case "build":
                    check_args(n == 1);
                    Build.build_components(false);
                    break;
                case "build_fresh":
                    check_args(n == 1);
                    Build.build_components(true);
                    break;
                case "classpath":
                    check_args(n == 1);
                    echo(Environment.join_standard_paths(Build.classpath()));
                    break;
                case "services":
                    check_args(n == 1);
                    for (String s : Build.services()) { echo(s); }
                    break;
                default:
                    fail("Bad setup operation " + Environment.quote(op));
                    break;
            }
        }
        catch (InterruptedException e) {
            echo("Interrupt");
            System.exit(139);
        }
        catch (IOException | RuntimeException | NoSuchAlgorithmException e) {
            echo(e.getMessage());
            System.exit(1);
        }
    }
}
