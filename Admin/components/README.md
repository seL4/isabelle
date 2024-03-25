# Isabelle system components #

## Multi-platform support of Isabelle ##

### Preamble ###

The general programming model is that of a stylized ML + Scala + POSIX
environment, with a minimum of system-specific code in user-space tools.

The Isabelle system infrastructure provides some facilities to make this work,
e.g. see the ML and Scala modules `File` and `Path`, or functions like
`Isabelle_System.bash`. The settings environment also provides some means for
portability, e.g. the `bash` function `platform_path` to keep the impression
that Windows/Cygwin adheres to Isabelle/POSIX standards, although many
executables are native on Windows (notably Poly/ML and Java).

When producing add-on tools, it is important to stay within this clean room of
Isabelle, and refrain from non-portable access to operating system functions.
The Isabelle environment uses GNU `bash` and Isabelle/Scala as portable system
infrastructure, using somewhat peculiar implementation techniques.


### Supported platforms ###

A broad range of hardware and operating system platforms are supported by
building executables on base-line versions that are neither too old nor too
new. Common OS families should work: Linux, macOS, Windows. More exotic
platforms are unsupported: NixOS, BSD, Solaris.

Official platforms:

  * `x86_64-linux`
      - Ubuntu 18.04 LTS
  * `arm64-linux`
      - Ubuntu 18.04 LTS (e.g. via `docker run -it ubuntu:18.04 bash`)

  * `x86_64-darwin`
      - macOS 11 Big Sur (`mini1` Macmini8,1)
      - macOS 12 Monterey (???)
      - macOS 13 Ventura (`mini3` Mac14,12 -- MacMini M2 Pro, 6+4 cores)
      - macOS 14 Sonoma (`mini2` Macmini8,1)
  * `arm64-darwin`
      - macOS 11 Big Sur (`assur` Macmini9,1 -- MacMini M1, 4+4 cores)
      - macOS 12 Monterey (???)
      - macOS 13 Ventura (`mini3` Mac14,12 -- MacMini M2 Pro, 6+4 cores)
      - macOS 14 Sonoma (`studio1` Mac13,2 M1 Ultra, 16+4 cores)

  * `x86_64-windows`
      - Windows 10
  * `x86_64-cygwin`
      - Cygwin 3.5.x https://isabelle.sketis.net/cygwin_2024 (`x86_64/release`)


### 64 bit vs. 32 bit platform personality ###

Isabelle requires 64 bit hardware running a 64 bit operating system. Only
Windows still supports native `x86` executables, but the POSIX emulation on
Windows via Cygwin64 works exclusively for `x86_64`.

The Isabelle settings environment provides variable `ISABELLE_PLATFORM64` to
refer to the standard platform personality. On Windows this is for Cygwin64,
but the following native platform identifiers are available as well:

  * `ISABELLE_WINDOWS_PLATFORM64`
  * `ISABELLE_WINDOWS_PLATFORM32`

These are always empty on Linux and macOS, and non-empty on Windows. For
example, this is how to refer to native Windows and fall-back on Unix (always
64 bit):

  * `"${ISABELLE_WINDOWS_PLATFORM64:-$ISABELLE_PLATFORM64}"`

And this is for old 32 bit executables on Windows, but still 64 bit on Unix:

  * `"${ISABELLE_WINDOWS_PLATFORM32:-$ISABELLE_PLATFORM64}"`

For Apple Silicon the native platform is `"$ISABELLE_APPLE_PLATFORM64"`
(`arm64-darwin`), but thanks to Rosetta 2 `"$ISABELLE_PLATFORM64"`
(`x64_64-darwin`) works routinely with fairly good performance.


### Dependable system tools ###

The following portable system tools can be taken for granted:

* Scala on top of Java. Isabelle/Scala irons out many fine points of the Java
  platform to make it fully portable as described above.

* GNU `bash` as uniform shell on all platforms. The POSIX "standard" shell
  `/bin/sh` does not work portably -- there are too many non-standard
  implementations of it. On Debian and Ubuntu `/bin/sh` is actually
  `/bin/dash` and introduces many oddities.


### Known problems ###

* macOS: If Homebrew or MacPorts is installed, there is some danger that
  accidental references to its shared libraries are created (e.g. `libgmp`).
  Use `otool -L` to check if compiled binaries also work without MacPorts.

* Common Unix tools like `/bin/sh`, `/bin/kill`, `sed`, `ulimit` are
  notoriously non-portable an should be avoided.

* The traditional `uname` Unix tool only tells about its own executable
  format, not the underlying platform!


## Notes on maintaining the Isabelle component repository at TUM ##

### Quick reference ###


  * local setup (and test) of component directory, e.g. in

      - `screwdriver-3.14/`

  * packaging (with associated SHA1 digest), e.g.

      - `$ isabelle components_build screwdriver-3.14`

  * publishing, e.g.

      - `$ isabelle components_build -P screwdriver-3.14.tar.gz`

  * manual editing of `Admin/components/main`: `screwdriver-3.14`


### Unique names ###

Component names are globally unique over time and space: names of published
components are never re-used. If some component needs to be re-packaged, extra
indices may be added to the official version number like this:

  * `screwdriver-3.14` -- default packaging/publishing, no index
  * `screwdriver-3.14-1` -- another refinement of the same
  * `screwdriver-3.14-2` -- yet another refinement of the same

There is no standard format for the structure of component names: they are
compared for equality only, without any guess at an ordering.

Components are registered in Admin/components/main (or similar) for use of
that particular Isabelle repository version, subject to regular Mercurial
history. This allows to bisect Isabelle versions with full record of the
required components for testing.


### Authentic archives ###

Isabelle components are managed as authentic .tar.gz archives in
`/home/isabelle/components` from where they are made publicly available on
https://isabelle.in.tum.de/components/.

Visibility on the HTTP server depends on local Unix file permission: nonfree
components should omit "read" mode for the Unix group/other; regular
components should be world-readable.

The file `Admin/components/components.sha1` contains SHA1 identifiers within
the Isabelle repository, for integrity checking of the archives that are
exposed to the public file-system. The command-line tool `isabelle
components_build` maintains these hash-keys automatically.


### Unpacked copy ###

A second unpacked copy is provided in `/home/isabelle/contrib/`. This allows
users and administrative services within the TUM network to activate arbitrary
snapshots of the repository with all standard components being available,
without extra copying or unpacking of the authentic archives. The
`isabelle_cronjob` does this routinely: it will break if the unpacked version
is omitted.

The command-line tool `isabelle components_build -P` takes care of uploading
the `.tar.gz` archive and unpacking it, unless it is a special component (e.g.
for multiplatform application bundling).
