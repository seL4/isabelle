/*  Title:      Tools/Setup/isabelle/setup/Build_Scala.java
    Author:     Makarius

Build Isabelle/Scala modules.
*/

package isabelle.setup;


import java.io.File;
import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Properties;
import java.util.stream.Stream;


public class Build_Scala
{
    public static class Context
    {
        private final Path component_dir;
        private Properties props;

        public Context(Path dir) throws IOException
        {
            component_dir = dir;
            props = new Properties();
            Path path = component_dir.resolve("etc/scala.props");
            if (Files.exists(path)) { props.load(Files.newBufferedReader(path)); }
        }

        @Override public String toString() { return component_dir.toString(); }

        public String component_name() { return component_dir.toFile().getName(); }
        public String name() { return props.getProperty("name", component_name()); }
        public String description() { return props.getProperty("description", name()); }

        public String lib_name() { return props.getProperty("lib", "lib") + "/" + name(); }
        public String jar_name() { return lib_name() + ".jar"; }
        public String shasum_name() { return lib_name() + ".shasum"; }

        public String main() { return props.getProperty("main", ""); }

        public String[] sources() { return props.getProperty("sources", "").split("\\s+"); }
        public String[] resources() { return props.getProperty("resources", "").split("\\s+"); }
        public String[] services() { return props.getProperty("services", "").split("\\s+"); }

        public Path path(String file) { return component_dir.resolve(file); }
        public boolean exists(String file) { return Files.exists(path(file)); }

        public String resource_name(String s)
        {
            int i = s.indexOf(':');
            return i > 0 ? s.substring(0, i) : s;
        }

        public String resource_target(String s)
        {
            int i = s.indexOf(':');
            return i > 0 ? s.substring(i + 1) : s;
        }

        public String shasum(String file)
            throws IOException, NoSuchAlgorithmException
        {
            if (exists(file)) {
                MessageDigest sha = MessageDigest.getInstance("SHA");
                sha.update(Files.readAllBytes(path(file)));
                String digest = String.format(Locale.ROOT, "%040x", new BigInteger(1, sha.digest()));
                return digest + " *" + file + "\n";
            }
            else { return ""; }
        }
    }

    public static void build_scala(Context context, boolean fresh)
        throws IOException, InterruptedException, NoSuchAlgorithmException
    {
        String jar_name = context.jar_name();
        String shasum_name = context.shasum_name();

        String[] sources = context.sources();
        String[] resources = context.resources();

        if (sources.length == 0) {
            Files.deleteIfExists(context.path(jar_name));
            Files.deleteIfExists(context.path(shasum_name));
        }
        else {
            String shasum_old =
                context.exists(shasum_name) ? Files.readString(context.path(shasum_name)) : "";
            String shasum_sources;
            {
                StringBuilder _shasum = new StringBuilder();
                for (String s : resources) {
                    _shasum.append(context.shasum(context.resource_name(s)));
                }
                for (String s : sources) { _shasum.append(context.shasum(s)); }
                shasum_sources = _shasum.toString();
            }
            if (fresh || !shasum_old.equals(context.shasum(jar_name) + shasum_sources)) {
                System.out.println("### Building " + context.description() + " ...");

                String java_home = Environment.getenv("JAVA_HOME");
                String scala_home = Environment.getenv("SCALA_HOME");
                String scalac_options = Environment.getenv("ISABELLE_SCALAC_OPTIONS");
                String isabelle_class_path = Environment.getenv("ISABELLE_CLASSPATH");

                if (java_home.isEmpty()) {
                    throw new RuntimeException("Unknown JAVA_HOME -- Java unavailable");
                }
                if (scala_home.isEmpty()) {
                    throw new RuntimeException("Unknown SCALA_HOME -- Scala unavailable");
                }

                Path build_dir = Files.createTempDirectory("isabelle");
                try {
                    /* classpath */

                    List<String> classpath = new LinkedList<String>();
                    for (String s : isabelle_class_path.split(":", -1)) {
                        classpath.add(Environment.platform_path(s));
                    }

                    Map<String,String> env = new HashMap<String,String>(Environment.settings());
                    env.put("CLASSPATH", String.join(File.pathSeparator, classpath));


                    /* compile sources */

                    List<String> cmd = new LinkedList<String>();
                    Environment.Exec_Result res;

                    cmd.add(Environment.platform_path(scala_home + "/bin/scalac"));
                    for (String s : scalac_options.split("\\s+")) { cmd.add(s); }
                    cmd.add("-d");
                    cmd.add(build_dir.toString());
                    for (String s : sources) { cmd.add(context.path(s).toString()); }

                    res = Environment.exec_process(cmd, build_dir.toFile(), env, false);
                    if (!res.ok()) throw new RuntimeException(res.err());


                    /* copy resources */

                    for (String s : context.resources()) {
                        String name = context.resource_name(s);
                        String target = context.resource_target(s);
                        Path file_name = Path.of(name).normalize().getFileName();
                        Path target_path = Path.of(target).normalize();

                        Path target_dir;
                        Path target_file;
                        {
                            if (target.endsWith("/") || target.endsWith("/.")) {
                                target_dir = build_dir.resolve(target_path);
                                target_file = target_dir.resolve(file_name);
                            }
                            else {
                                target_file = build_dir.resolve(target_path);
                                target_dir = target_file.getParent();
                            }
                        }
                        Files.createDirectories(target_dir);
                        Files.copy(context.path(name), target_file,
                            StandardCopyOption.COPY_ATTRIBUTES);
                    }


                    /* jar */

                    cmd.clear();
                    cmd.add(Environment.platform_path(java_home + "/bin/jar"));
                    cmd.add("-c");
                    cmd.add("-f");
                    cmd.add(context.path(jar_name).toString());
                    if (!context.main().isEmpty()) {
                        cmd.add("-e");
                        cmd.add(context.main());
                    }
                    cmd.add(".");

                    res = Environment.exec_process(cmd, build_dir.toFile(), env, false);
                    if (!res.ok()) throw new RuntimeException(res.err());


                    /* shasum */

                    String shasum = context.shasum(jar_name) + shasum_sources;
                    Files.writeString(context.path(shasum_name), shasum);
                }
                finally {
                    try (Stream<Path> walk = Files.walk(build_dir)) {
                        walk.sorted(Comparator.reverseOrder())
                            .map(Path::toFile)
                            .forEach(File::delete);
                    }
                }
            }
        }
    }
}
