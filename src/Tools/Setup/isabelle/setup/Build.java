/*  Title:      Tools/Setup/isabelle/setup/Build.java
    Author:     Makarius

Build Isabelle/Scala/JVM modules.
*/

package isabelle.setup;


import java.io.BufferedOutputStream;
import java.io.File;
import java.io.IOException;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;
import java.util.Locale;
import java.util.Properties;
import java.util.jar.Attributes;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.jar.JarOutputStream;
import java.util.jar.Manifest;
import java.util.stream.Stream;

import scala.tools.nsc.MainClass;


public class Build
{
    /** component directory context **/

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

        public String main() { return props.getProperty("main", ""); }

        private List<String> get_list(String name)
        {
            List<String> list = new LinkedList<String>();
            for (String s : props.getProperty(name, "").split("\\s+")) {
                if (!s.isEmpty()) { list.add(s); }
            }
            return List.copyOf(list);
        }
        public List<String> requirements() { return get_list("requirements"); }
        public List<String> sources() { return get_list("sources"); }
        public List<String> resources() { return get_list("resources"); }
        public List<String> services() { return get_list("services"); }

        public Path path(String file) { return component_dir.resolve(file); }
        public boolean exists(String file) { return Files.exists(path(file)); }

        // historic
        public Path shasum_path() { return path(lib_name() + ".shasum"); }

        public String item_name(String s)
        {
            int i = s.indexOf(':');
            return i > 0 ? s.substring(0, i) : s;
        }

        public String item_target(String s)
        {
            int i = s.indexOf(':');
            return i > 0 ? s.substring(i + 1) : s;
        }

        public String shasum(String name, List<Path> paths)
            throws IOException, NoSuchAlgorithmException
        {
            boolean exists = false;
            MessageDigest sha = MessageDigest.getInstance("SHA");
            for (Path file : paths) {
                if (Files.exists(file)) {
                    exists = true;
                    sha.update(Files.readAllBytes(file));
                }
            }
            if (exists) {
                String digest = String.format(Locale.ROOT, "%040x", new BigInteger(1, sha.digest()));
                return digest + " " + name + "\n";
            }
            else { return ""; }
        }

        public String shasum(String file)
            throws IOException, NoSuchAlgorithmException
        {
            return shasum(file, List.of(path(file)));
        }
    }


    /** compile sources **/

    public static void compile_sources(
        Path target_dir, List<Path> deps, String options, List<Path> sources)
    {
        ArrayList<String> args = new ArrayList<String>();
        args.add("-d");
        args.add(target_dir.toString());
        args.add("-bootclasspath");
        args.add(Environment.join_paths(deps));
        for (String s : options.split("\\s+")) {
          if (!s.isEmpty()) { args.add(s); }
        }
        args.add("--");
        for (Path p : sources) { args.add(p.toString()); }

        MainClass main = new MainClass();
        boolean ok = main.process(args.toArray(String[]::new));
        if (!ok) throw new RuntimeException("Failed to compile sources");
    }


    /** shasum for jar content **/

    private static String SHASUM = "META-INF/shasum";

    public static String get_shasum(Path jar_path)
        throws IOException
    {
        if (Files.exists(jar_path)) {
            try (JarFile jar_file = new JarFile(jar_path.toFile()))
            {
                JarEntry entry = jar_file.getJarEntry(SHASUM);
                if (entry != null) {
                    byte[] bytes = jar_file.getInputStream(entry).readAllBytes();
                    return new String(bytes, StandardCharsets.UTF_8);
                }
                else { return ""; }
            }
        }
        else { return ""; }
    }

    public static void create_shasum(Path dir, String shasum)
        throws IOException
    {
        Path path = dir.resolve(SHASUM);
        Files.createDirectories(path.getParent());
        Files.writeString(path, shasum);
    }


    /** create jar **/

    public static void create_jar(Path dir, String main, Path jar)
        throws IOException
    {
        Files.createDirectories(dir.resolve(jar).getParent());
        Files.deleteIfExists(jar);

        Manifest manifest = new Manifest();
        Attributes attributes = manifest.getMainAttributes();
        attributes.put(Attributes.Name.MANIFEST_VERSION, "1.0");
        attributes.put(new Attributes.Name("Created-By"),
            System.getProperty("java.version") + " (" + System.getProperty("java.vendor") + ")");
        if (!main.isEmpty()) { attributes.put(Attributes.Name.MAIN_CLASS, main); }

        try (JarOutputStream out =
            new JarOutputStream(new BufferedOutputStream(Files.newOutputStream(jar)), manifest))
        {
            for (Path path : Files.walk(dir).sorted().toArray(Path[]::new)) {
                boolean is_dir = Files.isDirectory(path);
                boolean is_file = Files.isRegularFile(path);
                if (is_dir || is_file) {
                    String name = Environment.slashes(dir.relativize(path).toString());
                    JarEntry entry = new JarEntry(is_dir ? name + "/" : name);
                    entry.setTime(path.toFile().lastModified());
                    out.putNextEntry(entry);
                    if (is_file) { out.write(Files.readAllBytes(path)); }
                    out.closeEntry();
                }
            }
        }
    }



    /** build scala **/

    public static void build_scala(Context context, boolean fresh)
        throws IOException, InterruptedException, NoSuchAlgorithmException
    {
        String jar_name = context.jar_name();
        Path jar_path = context.path(jar_name);

        List<String> requirements = context.requirements();
        List<String> resources = context.resources();
        List<String> sources = context.sources();

        Files.deleteIfExists(context.shasum_path());

        if (sources.isEmpty() && resources.isEmpty()) {
            Files.deleteIfExists(jar_path);
        }
        else {
            String shasum_old = get_shasum(jar_path);
            String shasum;
            List<Path> compiler_deps = new LinkedList<Path>();
            {
                StringBuilder _shasum = new StringBuilder();
                for (String s : requirements) {
                    if (s.startsWith("@$")) {
                        List<Path> paths = new LinkedList<Path>();
                        for (String p : Environment.getenv(s.substring(2)).split(":", -1)) {
                            if (!p.isEmpty()) {
                                Path path = Path.of(Environment.platform_path(p));
                                compiler_deps.add(path);
                                paths.add(path);
                            }
                        }
                        _shasum.append(context.shasum(s, paths));
                    }
                    else {
                        compiler_deps.add(context.path(s));
                        _shasum.append(context.shasum(s));
                    }
                }
                for (String s : resources) {
                    _shasum.append(context.shasum(context.item_name(s)));
                }
                for (String s : sources) { _shasum.append(context.shasum(s)); }
                shasum = _shasum.toString();
            }
            if (fresh || !shasum_old.equals(shasum)) {
                System.out.println(
                    "### Building " + context.description() + " (" + jar_path + ") ...");

                String scalac_options = Environment.getenv("ISABELLE_SCALAC_OPTIONS");
                String isabelle_class_path = Environment.getenv("ISABELLE_CLASSPATH");

                Path build_dir = Files.createTempDirectory("isabelle");
                try {
                    /* compile sources */

                    for (String s : isabelle_class_path.split(":", -1)) {
                        if (!s.isEmpty()) {
                          compiler_deps.add(Path.of(Environment.platform_path(s)));
                        }
                    }

                    List<Path> compiler_sources = new LinkedList<Path>();
                    for (String s : sources) { compiler_sources.add(context.path(s)); }

                    compile_sources(build_dir, compiler_deps, scalac_options, compiler_sources);


                    /* copy resources */

                    for (String s : context.resources()) {
                        String name = context.item_name(s);
                        String target = context.item_target(s);
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


                    /* packaging */

                    create_shasum(build_dir, shasum);
                    create_jar(build_dir, context.main(), jar_path);
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
