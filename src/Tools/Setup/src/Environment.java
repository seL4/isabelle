/*  Title:      Tools/Setup/src/Environment.java
    Author:     Makarius

Fundamental Isabelle system environment: quasi-static module with
optional init operation.
*/

package isabelle.setup;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.regex.Matcher;
import java.util.regex.Pattern;


public class Environment
{
    /** Support for Cygwin as POSIX emulation on Windows **/

    public static boolean is_windows()
    {
        return System.getProperty("os.name", "").startsWith("Windows");
    }
    public static boolean is_linux() { return System.getProperty("os.name", "").equals("Linux"); }
    public static boolean is_macos() { return System.getProperty("os.name", "").equals("Mac OS X"); }



    /* system path representations */

    public static String slashes(String s) { return s.replace('\\', '/'); }

    public static String standard_path(String cygwin_root, String platform_path)
    {
        if (is_windows()) {
            String backslashes = platform_path.replace('/', '\\');

            Pattern root_pattern =
                Pattern.compile("(?i)" + Pattern.quote(cygwin_root) + "(?:\\\\+|\\z)(.*)");
            Matcher root_matcher = root_pattern.matcher(backslashes);

            Pattern drive_pattern = Pattern.compile("([a-zA-Z]):\\\\*(.*)");
            Matcher drive_matcher = drive_pattern.matcher(backslashes);

            if (root_matcher.matches()) {
                String rest = root_matcher.group(1);
                return "/" + slashes(rest);
            }
            else if (drive_matcher.matches()) {
                String letter = drive_matcher.group(1).toLowerCase(Locale.ROOT);
                String rest = drive_matcher.group(2);
                return "/cygdrive/" + letter + (rest.isEmpty() ? "" : "/" + slashes(rest));
            }
            else { return slashes(backslashes); }
        }
        else { return platform_path; }
    }

    private static class Expand_Platform_Path
    {
        private String _cygwin_root;
        private StringBuilder _result = new StringBuilder();

        public Expand_Platform_Path(String cygwin_root)
        {
            _cygwin_root = cygwin_root;
        }

        public String result() { return _result.toString(); }

        void clear() { _result.setLength(0); }
        void add(char c) { _result.append(c); }
        void add(String s) { _result.append(s); }
        void separator()
        {
            int n = _result.length();
            if (n > 0 && _result.charAt(n - 1) != java.io.File.separatorChar) {
                add(java.io.File.separatorChar);
            }
        }

        public String check_root(String standard_path)
        {
            String rest = standard_path;
            boolean is_root = standard_path.startsWith("/");

            if (is_windows()) {
                Pattern cygdrive_pattern = Pattern.compile("/cygdrive/([a-zA-Z])($|/.*)");
                Matcher cygdrive_matcher = cygdrive_pattern.matcher(standard_path);

                Pattern named_root_pattern = Pattern.compile("//+([^/]*)(.*)");
                Matcher named_root_matcher = named_root_pattern.matcher(standard_path);

                if (cygdrive_matcher.matches()) {
                    String drive = cygdrive_matcher.group(1).toUpperCase(Locale.ROOT);
                    rest = cygdrive_matcher.group(2);
                    clear();
                    add(drive);
                    add(':');
                    add(java.io.File.separatorChar);
                }
                else if (named_root_matcher.matches()) {
                    String root = named_root_matcher.group(1);
                    rest = named_root_matcher.group(2);
                    clear();
                    add(java.io.File.separatorChar);
                    add(java.io.File.separatorChar);
                    add(root);
                }
                else if (is_root) {
                    clear();
                    add(_cygwin_root);
                }
            }
            else if (is_root) {
                clear();
                add(java.io.File.separatorChar);
            }
            return rest;
        }

        public void check_rest(Map<String,String> env, String main)
            throws IOException, InterruptedException
        {
            for (String p : main.split("/", -1)) {
                if (env != null && p.startsWith("$")) {
                    String var = p.substring(1);
                    String res = env.getOrDefault(var, "");
                    if (res.isEmpty()) {
                        throw new RuntimeException(
                            "Bad Isabelle environment variable: " + Library.quote(var));
                    }
                    else check(null, res);
                }
                else if (!p.isEmpty()) {
                    separator();
                    add(p);
                }
            }
        }

        public void check(Map<String,String> env, String path)
            throws IOException, InterruptedException
        {
            check_rest(env, check_root(path));
        }
    }

    public static String expand_platform_path(
        Map<String,String> env, String cygwin_root, String standard_path)
        throws IOException, InterruptedException
    {
        Expand_Platform_Path expand = new Expand_Platform_Path(cygwin_root);
        expand.check(env, standard_path);
        return expand.result();
    }


    /* init (e.g. after extraction via 7zip) */

    private static String bootstrap_directory(
        String preference, String variable, String property, String description)
    {
        String a = preference;  // explicit argument
        String b = System.getenv(variable);  // e.g. inherited from running isabelle tool
        String c = System.getProperty(property);  // e.g. via JVM application boot process
        String dir;

        if (a != null && !a.isEmpty()) { dir = a; }
        else if (b != null && !b.isEmpty()) { dir = b; }
        else if (c != null && !c.isEmpty()) { dir = c; }
        else { throw new RuntimeException("Unknown " + description + " directory"); }

        if ((new java.io.File(dir)).isDirectory()) { return dir; }
        else {
            throw new RuntimeException("Bad " + description + " directory " + Library.quote(dir));
        }
    }

    private static void cygwin_exec(String isabelle_root, List<String> cmd)
        throws IOException, InterruptedException
    {
        java.io.File cwd = new java.io.File(isabelle_root);
        Map<String,String> env = new HashMap<String,String>(System.getenv());
        env.put("CYGWIN", "nodosfilewarning");
        Process.Exec_Result res = Process.exec(cmd, cwd, env, true);
        if (!res.ok()) throw new RuntimeException(res.out());
    }

    public static void cygwin_init(String isabelle_root, String cygwin_root)
        throws IOException, InterruptedException
    {
        if (is_windows()) {
            java.io.File uninitialized_file = new java.io.File(cygwin_root, "isabelle\\uninitialized");
            boolean uninitialized = uninitialized_file.isFile() && uninitialized_file.delete();

            if (uninitialized) {
                Path symlinks_path = (new java.io.File(cygwin_root + "\\isabelle\\symlinks")).toPath();
                String[] symlinks = Files.readAllLines(symlinks_path).toArray(new String[0]);

                // recover symlinks
                int i = 0;
                int m = symlinks.length;
                int n = (m > 0 && symlinks[m - 1].isEmpty()) ? m - 1 : m;
                while (i < n) {
                    if (i + 1 < n) {
                        String target = symlinks[i];
                        String content = symlinks[i + 1];
                        File.cygwin_link(content, new java.io.File(isabelle_root, target));
                        i += 2;
                    } else { throw new RuntimeException("Unbalanced symlinks list"); }
                }

                cygwin_exec(isabelle_root,
                    List.of(cygwin_root + "\\bin\\dash.exe", "/isabelle/rebaseall"));
                cygwin_exec(isabelle_root,
                    List.of(cygwin_root + "\\bin\\bash.exe", "/isabelle/postinstall"));
            }
        }
    }


    /* implicit settings environment */

    private static volatile Map<String,String> _settings = null;

    public static Map<String,String> settings()
        throws IOException, InterruptedException
    {
        if (_settings == null) { init("", ""); }  // unsynchronized check
        return _settings;
    }

    public static String getenv(String name)
        throws IOException, InterruptedException
    {
        return settings().getOrDefault(name, "");
    }

    public static synchronized void init(String _isabelle_root, String _cygwin_root)
        throws IOException, InterruptedException
    {
        if (_settings == null) {
            String isabelle_root =
                bootstrap_directory(_isabelle_root, "ISABELLE_ROOT", "isabelle.root", "Isabelle root");

            String cygwin_root = "";
            if (is_windows()) {
                cygwin_root = bootstrap_directory(_cygwin_root, "CYGWIN_ROOT", "cygwin.root", "Cygwin root");
                cygwin_init(isabelle_root, cygwin_root);
            }

            Map<String,String> env = new HashMap<String,String>(System.getenv());

            BiFunction<String,String,Void> env_default =
                (String a, String b) -> { if (!b.isEmpty()) env.putIfAbsent(a, b); return null; };

            env_default.apply("CYGWIN_ROOT", cygwin_root);
            env_default.apply("ISABELLE_JDK_HOME",
                standard_path(cygwin_root, System.getProperty("java.home", "")));
            env_default.apply("HOME", System.getProperty("user.home", ""));
            env_default.apply("ISABELLE_APP", System.getProperty("isabelle.app", ""));

            Map<String,String> settings = new HashMap<String,String>();
            Path settings_file = Files.createTempFile(null, null);
            try {
                List<String> cmd = new LinkedList<String>();
                if (is_windows()) {
                    cmd.add(cygwin_root + "\\bin\\bash");
                    cmd.add("-l");
                    cmd.add(standard_path(cygwin_root, isabelle_root + "\\bin\\isabelle"));
                } else {
                    cmd.add(isabelle_root + "/bin/isabelle");
                }
                cmd.add("getenv");
                cmd.add("-d");
                cmd.add(settings_file.toString());

                Process.Exec_Result res = Process.exec(cmd, null, env, true);
                if (!res.ok()) throw new RuntimeException(res.out());

                for (String s : File.read(settings_file).split("\u0000", -1)) {
                    int i = s.indexOf('=');
                    if (i > 0) { settings.put(s.substring(0, i), s.substring(i + 1)); }
                    else if (i < 0 && !s.isEmpty()) { settings.put(s, ""); }
                }
            }
            finally { Files.delete(settings_file); }

            if (is_windows()) { settings.put("CYGWIN_ROOT", cygwin_root); }

            settings.put("PATH", settings.get("PATH_JVM"));
            settings.remove("PATH_JVM");

            _settings = Map.copyOf(settings);
        }
    }


    /* Cygwin root (after init) */

    public static String cygwin_root()
        throws IOException, InterruptedException
    {
        return getenv("CYGWIN_ROOT");
    }

    public static String standard_path(String platform_path)
        throws IOException, InterruptedException
    {
        return standard_path(cygwin_root(), platform_path);
    }

    public static String expand_platform_path(String standard_path)
            throws IOException, InterruptedException
    {
        return expand_platform_path(settings(), cygwin_root(), standard_path);
    }

    public static String platform_path(String standard_path)
        throws IOException, InterruptedException
    {
        return expand_platform_path(null, cygwin_root(), standard_path);
    }
}
