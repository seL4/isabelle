# Isabelle system components #

## Multi-platform support of Isabelle ##

### Preamble ###

The general programming model is that of a stylized ML + Scala + POSIX
environment, with a minimum of system-specific code in user-space tools.

The Isabelle system infrastructure provides some facilities to make this work,
e.g. see the ML and Scala modules `File` and `Path`, or functions like
`Isabelle_System.bash`. The settings environment also provides some means for
portability, e.g. the `bash` function `platform_path` to keep the impression
that Windows/Cygwin adheres to Isabelle/POSIX standards, although most
executables are running natively on Windows.

When producing add-on tools, it is important to stay within this clean room of
Isabelle, and refrain from non-portable access to operating system functions.
The Isabelle environment uses Isabelle/Scala as portable system
infrastructure, and Isabelle/ML refers to that for anything non-trivial.


### Supported platforms ###

A broad range of hardware and operating system platforms are supported by
building executables on base-line versions that are neither too old nor too
new. Common OS families should work: Linux, macOS, Windows. Exotic platforms
are unsupported: NixOS, BSD, Solaris etc.

The official platforms, with **base-line operating systems**, and reference
machines are as follows:

  * `x86_64-linux` and `arm64-linux`
      - **Ubuntu 18.04 LTS** (e.g. via `docker run -it ubuntu:18.04 bash`)

  * `x86_64-darwin`
      - **macOS 12 Monterey** (`mini1` Macmini8,1, 6 cores) (`aleppo` Macmini7,1, 2 cores)
      - macOS 13 Ventura (`mini3` Mac14,12 -- MacMini M2 Pro, 6+4 cores)
      - macOS 14 Sonoma (`mini2` Macmini8,1, 6 cores)
      - macOS 15 Sequoia (`hattusa` Mac16,11 -- MacMini M4 Pro, 10+4 cores)
  * `arm64-darwin`
      - **macOS 12 Monterey** (`assur` Macmini9,1 -- MacMini M1, 4+4 cores)
      - macOS 13 Ventura (`mini3` Mac14,12 -- MacMini M2 Pro, 6+4 cores)
      - macOS 14 Sonoma (`studio1` Mac13,2 M1 Ultra, 16+4 cores)
      - macOS 15 Sequoia (`hattusa` Mac16,11 -- MacMini M4 Pro, 10+4 cores)

  * `x86_64-windows`
      - Windows Server 2019 (minimum for Java ZGC)
      - **Windows Server 2022** (`se0.proof.cit.tum.de`)
      - **Windows 10**
      - Windows 11
  * `x86_64-cygwin`
      - **Cygwin 3.5.x**
        https://isabelle.sketis.net/cygwin_2025 (`x86_64/release`)

Multi-platform tools require thorough testing on all platforms: base-line and
latest versions. It "works for me on my system" is not sufficient for the
general public.


### Multiple platform personalities ###

Isabelle works with current 64 bit hardware and 64 bit operating systems,
which usually means Intel (`x86_64`) and very often ARM (`arm64`). Windows and
macOS provide `x86_64` emulation on their ARM versions, so that is in theory
sufficient, but native `arm64` is more efficient. Linux lacks proper
emulation, so tools should be provided for `x86_64-linux` and `arm64-linux`
whenever possible. Also note that `arm64-linux` is the standard platform for
Docker on ARM hardware (e.g. Apple Silicon).

For extra performance on macOS, Isabelle tools are usually included in both
variants: `x86_64-darwin` and `arm64-darwin` (or as hybrid executable that
pretends to be `x86_64-darwin`, the default platform). Windows support is only
for Intel so far: this could mean `x86_64-windows` or `x86_64-cygwin`, but
also `x86-windows` for old binary-only tools.

The Isabelle settings environment provides variable `ISABELLE_PLATFORM64` to
refer to the standard POSIX platform personality (Linux/ARM, Linux/Intel,
macOS/Intel, Windows/Cygwin64/Intel). Alternative settings are available for
native platforms as show below. In summary, the symbolic platform names from
the settings environment are as follows:

  * Linux (Intel)
    - `ISABELLE_PLATFORM64` is `x86_64-linux`

  * Linux (ARM)
    - `ISABELLE_PLATFORM64` is `arm64-linux`

  * Windows
    - `ISABELLE_PLATFORM64` is `x86_64-cygwin`
    - `ISABELLE_WINDOWS_PLATFORM64` is `x86_64-windows`
    - `ISABELLE_WINDOWS_PLATFORM32` is `x86-windows`

  * macOS (Intel)
    - `ISABELLE_PLATFORM64` is `x86_64-darwin`

  * macOS (ARM)
    - `ISABELLE_PLATFORM64` is `x86_64-darwin`
    - `ISABELLE_APPLE_PLATFORM64` is `arm64-darwin`

When used outside their proper system context, platform settings remain empty.
This allows to refer symbolically to various combinations, using conditional
expressions in GNU `bash` like this:

  * `"${ISABELLE_WINDOWS_PLATFORM64:-$ISABELLE_PLATFORM64}"`
    -- native Windows, or default POSIX platform (always Intel on macOS)

  * `"${ISABELLE_WINDOWS_PLATFORM64:-${ISABELLE_APPLE_PLATFORM64:-$ISABELLE_PLATFORM64}}"`
    -- native Windows platform, native Apple Silicon platform, or default/native Linux platform


### Dependable system tools ###

The following portable system tools can be taken for granted:

* Scala on top of Java. Isabelle/Scala irons out many fine points of the Java
  platform to make it fully portable as described above.

* GNU `bash` as uniform shell on all platforms. The POSIX "standard" shell
  `/bin/sh` does not work portably -- there are too many non-standard
  implementations of it. On Debian and Ubuntu `/bin/sh` is actually
  `/bin/dash` and causes many problems.


### Common problems ###

* The traditional `uname` Unix tool only tells about its own executable
  format, not the underlying platform! There are special tricks to get
  underlying platform details, depending on OS versions: Isabelle/Scala and
  the Isabelle settings environment provide sanitized versions of that.
  Isabelle tools should not attempt anything on their own account.

* Common Unix tools like `/bin/sh`, `/bin/kill`, `sed`, `ulimit` are
  notoriously non-portable an should be avoided.

* macOS: If Homebrew or MacPorts is installed, there is some danger that
  accidental references to its shared libraries are created (e.g. `libgmp`).
  Use `otool -L` to check if compiled binaries also work without MacPorts.

* macOS as SSH server: The target user shell needs to be set to `/bin/bash`
  instead of the default `/bin/zsh`, to make shell script escapes work
  reliably.


## The Isabelle component repository at TUM and sketis.net ##

Isabelle repository versions and administrative tools download components via
HTTPS from `ISABELLE_COMPONENT_REPOSITORY`, the default is
`https://isabelle.sketis.net/components`, and alternative is
`https://isabelle.in.tum.de/components`.

Isabelle releases have all required components bundled, but additional
components may be included via suitable manual configuration.


### Quick reference ###

The subsequent steps serve as a reminder of how to maintain components:

  * local setup (and test) of component directory, e.g. in

      - `screwdriver-3.14/`

  * packaging (with associated SHA1 digest), e.g.

      - `$ isabelle components_build screwdriver-3.14`

  * publishing, e.g.

      - `$ isabelle components_build -P screwdriver-3.14.tar.gz`

  * manual editing of `Admin/components/main`: `screwdriver-3.14`


### Unique names ###

Component names are globally unique over time and space: names of published
components are never re-used! If some component needs to be re-packaged, extra
indices may be added to the official version number like this:

  * `screwdriver-3.14` -- default packaging/publishing, no index
  * `screwdriver-3.14-1` -- another refinement of the same
  * `screwdriver-3.14-2` -- yet another refinement of the same

There is no standard format for the structure of component names: they are
compared for equality only, without any guess at an ordering (notions of
"older", "newer", "better" etc. are irrelevant).

Components are registered in `Admin/components/main` (or similar) for use of
that particular Isabelle repository version, subject to regular Mercurial
history. This allows to bisect Isabelle versions with full record of the
required components for testing.


### Authentic archives ###

TUM provides the shared administrative directory `/p/home/isabelle/components`
where the single source of all components is located as authentic `.tar.gz`
archives. The file `Admin/components/components.sha1` contains SHA1
identifiers within the Isabelle repository, for integrity checking of the
archives that are exposed to the public file-system. The command-line tool
`isabelle components_build` maintains these hash-keys automatically.

Components are published on https://isabelle.sketis.net/components and
https://isabelle.in.tum.de/components --- visibility on the web server depends
on local Unix file permission: nonfree components should omit "read" mode for
the Unix group/other; regular components should be world-readable.


### Unpacked copy ###

A second unpacked copy is provided in `/p/home/isabelle/contrib/`. This allows
users and administrative services within the TUM network to activate arbitrary
snapshots of the repository with all standard components being available,
without extra copying or unpacking of the authentic archives.

The command-line tool `isabelle components_build -P` takes care of uploading
the `.tar.gz` archive and unpacking it, unless it is a special component (e.g.
for multiplatform application bundling).


### Repeatable component builds ###

Historically, Isabelle components have often been assembled by hand, packaged
as `.tar.gz` and uploaded to the administrative directory. This model no
longer fits the typical complexity of multi-platform tools.

The current quality standard demands a separate tool in Isabelle/Scala, to
build a component in a repeatable manner: e.g. see `isabelle component_jdk` or
`isabelle component_e` with sources in `src/Pure/Admin`. Such tools often
require a Unix platform (Linux or macOS), or the specific platform for which
the target is built. In the latter case, the component build tool is run
manually in each operating-system context, using the base-line versions
specified above (e.g. via Docker); all results are assembled into one big
`.tar.gz` archive.


### Dynamic setup of large components ###

An alternative approach, especially for components that are very large and/or
rarely used, is to provide an Isabelle setup tool that interested users may
run for themselves. This works particularly well for software products that
have their own "store" of downloadable artifacts. For example, see
`isabelle dotnet_setup` as defined in `src/Pure/Tools/dotnet_setup.scala`.
