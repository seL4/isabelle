/*  Title:      Tools/Setup/src/Setup.java
    Author:     Makarius

Isabelle setup tool: bootstrap from generic Java environment.
*/

package isabelle.setup;


class Setup
{
    private static void echo(String msg)
    {
        System.out.print(msg + "\n");
    }
    private static void echo_err(String msg)
    {
        System.err.print(msg + "\n");
    }
    private static void fail(String msg)
    {
        echo_err(msg);
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
                    fail("Bad setup operation " + Library.quote(op));
                    break;
            }
        }
        catch (Throwable exn) {
            echo_err(Exn.print_error(exn));
            System.exit(Exn.return_code(exn, 2));
        }
    }
}
