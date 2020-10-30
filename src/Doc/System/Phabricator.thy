(*:maxLineLen=78:*)

theory Phabricator
imports Base
begin

chapter \<open>Phabricator server setup \label{ch:phabricator}\<close>

text \<open>
  Phabricator\<^footnote>\<open>\<^url>\<open>https://www.phacility.com/phabricator\<close>\<close> is an open-source
  product to support the development process of complex software projects
  (open or closed ones). The official slogan is:

  \begin{quote}
    Discuss. Plan. Code. Review. Test. \\
    Every application your project needs, all in one tool.
  \end{quote}

  Ongoing changes and discussions about changes are maintained uniformly
  within a MySQL database. There are standard connections to major version
  control systems: \<^bold>\<open>Subversion\<close>, \<^bold>\<open>Mercurial\<close>, \<^bold>\<open>Git\<close>. So Phabricator offers
  a counter-model to trends of monoculture and centralized version control,
  especially due to Microsoft's Github and Atlassian's Bitbucket.

  The small company behind Phabricator provides paid plans for support and
  hosting of servers, but it is easy to do \<^emph>\<open>independent self-hosting\<close> on a
  standard LAMP server (Linux, Apache, MySQL, PHP). This merely requires a
  virtual machine on the Net, which can be rented cheaply from local hosting
  providers --- there is no need to follow big cloud corporations. So it is
  feasible to remain the master of your virtual home, following the slogan
  ``own all your data''. In many respects, Phabricator is similar to the
  well-known Nextcloud\<^footnote>\<open>\<^url>\<open>https://nextcloud.org\<close>\<close> product, concerning both
  the technology and sociology.

  \<^medskip>
  The following Phabricator instances may serve as examples:

    \<^item> Phabricator development \<^url>\<open>https://secure.phabricator.com\<close>
    \<^item> Wikimedia development \<^url>\<open>https://phabricator.wikimedia.org\<close>
    \<^item> Blender development \<^url>\<open>https://developer.blender.org\<close>
    \<^item> LLVM development \<^url>\<open>https://reviews.llvm.org\<close>
    \<^item> Mozilla development \<^url>\<open>https://phabricator.services.mozilla.com\<close>
    \<^item> Mercurial development \<^url>\<open>https://phab.mercurial-scm.org\<close>
    \<^item> Isabelle development \<^url>\<open>https://isabelle-dev.sketis.net\<close>

  \<^medskip>
  Initial Phabricator configuration requires many details to be done right.
  Isabelle provides some command-line tools to help with the setup, and
  afterwards Isabelle support is optional: it is possible to run and maintain
  the server, without requiring the somewhat bulky Isabelle distribution
  again.

  \<^medskip>
  Assuming an existing Phabricator installation, the command-line tool @{tool
  hg_setup} (\secref{sec:hg-setup}) helps to create new repositories or to
  migrate old ones. In particular, this avoids the lengthy sequence of clicks
  in Phabricator to make a new private repository with hosting on the server.
  (Phabricator is a software project management platform, where initial
  repository setup happens rarely in practice.)
\<close>


section \<open>Quick start\<close>

text \<open>
  The starting point is a fresh installation of \<^bold>\<open>Ubuntu 18.04 or 20.04
  LTS\<close>\<^footnote>\<open>\<^url>\<open>https://ubuntu.com/download\<close>\<close>: this version is mandatory due to
  subtle dependencies on system packages and configuration that is assumed by
  the Isabelle setup tool.

  For production use, a proper \<^emph>\<open>Virtual Server\<close> or \<^emph>\<open>Root Server\<close> product
  from a hosting provider will be required, including an Internet Domain Name
  (\secref{sec:phabricator-domain}).

  Initial experimentation also works on a local host, e.g.\ via
  VirtualBox\<^footnote>\<open>\<^url>\<open>https://www.virtualbox.org\<close>\<close>. The Internet domain \<^verbatim>\<open>lvh.me\<close>
  is used by default: it maps arbitrary subdomains to \<^verbatim>\<open>localhost\<close>.

  All administrative commands need to be run as \<^verbatim>\<open>root\<close> user (e.g.\ via
  \<^verbatim>\<open>sudo\<close>). Note that Isabelle refers to user-specific configuration in the
  user home directory via @{setting ISABELLE_HOME_USER}
  (\secref{sec:settings}); that may be different or absent for the root user
  and thus cause confusion.
\<close>


subsection \<open>Initial setup\<close>

text \<open>
  Isabelle can manage multiple named Phabricator installations: this allows to
  separate administrative responsibilities, e.g.\ different approaches to user
  management for different projects. Subsequently we always use the default
  name ``\<^verbatim>\<open>vcs\<close>'': the name will appear in file and directory locations,
  internal database names and URLs.

  The initial setup works as follows (with full Linux package upgrade):

  @{verbatim [display] \<open>  isabelle phabricator_setup -U -M:\<close>}

  After installing many packages, cloning the Phabricator distribution,
  initializing the MySQL database and Apache, the tool prints an URL for
  further configuration. Now the following needs to be provided by the web
  interface.

    \<^item> An initial user that will get administrator rights. There is no need to
    create a special \<^verbatim>\<open>admin\<close> account. Instead, a regular user that will take
    over this responsibility can be used here. Subsequently we assume that
    user \<^verbatim>\<open>makarius\<close> becomes the initial administrator.

    \<^item> An \<^emph>\<open>Auth Provider\<close> to manage user names and passwords. None is provided
    by default, and Phabricator points out this omission prominently in its
    overview of \<^emph>\<open>Setup Issues\<close>: following these hints quickly leads to the
    place where a regular \<^emph>\<open>Username/Password\<close> provider can be added.

    Alternatively, Phabricator can delegate the responsibility of
    authentication to big corporations like Google and Facebook, but these can
    be easily ignored. Genuine self-hosting means to manage users directly,
    without outsourcing of authentication.

    \<^item> A proper password for the administrator can now be set, e.g.\ by the
    following command:

    @{verbatim [display] \<open>  isabelle phabricator bin/auth recover makarius\<close>}

    The printed URL gives access to a login and password dialog in the web
    interface.

    Any further users will be able to provide a password directly, because the
    Auth Provider is already active.

    \<^item> The list of Phabricator \<^bold>\<open>Setup Issues\<close> should be studied with some
    care, to make sure that no serious problems are remaining. For example,
    the request to lock the configuration can be fulfilled as follows:

    @{verbatim [display] \<open>  isabelle phabricator bin/auth lock\<close>}

    \<^medskip> A few other Setup Issues might be relevant as well, e.g.\ the timezone
    of the server. Some more exotic points can be ignored: Phabricator
    provides careful explanations about what it thinks could be wrong, while
    leaving some room for interpretation.
\<close>


subsection \<open>Mailer configuration\<close>

text \<open>
  The next important thing is messaging: Phabricator needs to be able to
  communicate with users on its own account, e.g.\ to reset passwords. The
  documentation has many variations on \<^emph>\<open>Configuring Outbound
  Email\<close>\<^footnote>\<open>\<^url>\<open>https://secure.phabricator.com/book/phabricator/article/configuring_outbound_email\<close>\<close>,
  but a conventional SMTP server with a dedicated \<^verbatim>\<open>phabricator\<close> user is
  sufficient. There is no need to run a separate mail server on the
  self-hosted Linux machine: hosting providers often include such a service
  for free, e.g.\ as part of a web-hosting package. As a last resort it is
  also possible to use a corporate service like Gmail, but such dependency
  dilutes the whole effort of self-hosting.

  \<^medskip>
  Mailer configuration requires a few command-line invocations as follows:

  @{verbatim [display] \<open>  isabelle phabricator_setup_mail\<close>}

  \<^noindent> This generates a JSON template file for the the mail account details.
  After editing that, the subsequent command will add and test it with
  Phabricator:

  @{verbatim [display] \<open>  isabelle phabricator_setup_mail -T makarius\<close>}

  This tells Phabricator to send a message to the administrator created
  before; the output informs about success or errors.

  The mail configuration process can be refined and repeated until it works
  properly: host name, port number, protocol etc.\ all need to be correct. The
  \<^verbatim>\<open>key\<close> field in the JSON file identifies the name of the configuration that
  will be overwritten each time, when taking over the parameters via
  \<^verbatim>\<open>isabelle phabricator_setup_mail\<close>.

  \<^medskip>
  The effective mail configuration can be queried like this:

  @{verbatim [display] \<open>  isabelle phabricator bin/config get cluster.mailers\<close>}
\<close>


subsection \<open>SSH configuration\<close>

text \<open>
  SSH configuration is important to access hosted repositories with public-key
  authentication. It is done by a separate tool, because it affects the
  operating-system and all installations of Phabricator simultaneously.

  The subsequent configuration is convenient (and ambitious): it takes away
  the standard port 22 from the operating system and assigns it to
  Isabelle/Phabricator.

  @{verbatim [display] \<open>  isabelle phabricator_setup_ssh -p 22 -q 222\<close>}

  Afterwards, remote login to the server host needs to use that alternative
  port 222. If there is a problem connecting again, the administrator can
  usually access a remote console via some web interface of the virtual server
  provider.

  \<^medskip>
  The following alternative is more modest: it uses port 2222 for Phabricator,
  and retains port 22 for the operating system.

  @{verbatim [display] \<open>  isabelle phabricator_setup_ssh -p 2222 -q 22\<close>}

  \<^medskip>
  The tool can be invoked multiple times with different parameters; ports are
  changed back and forth each time and services restarted.
\<close>


subsection \<open>Internet domain name and HTTPS configuration \label{sec:phabricator-domain}\<close>

text \<open>
  So far the Phabricator server has been accessible only on \<^verbatim>\<open>localhost\<close> (via
  the alias \<^verbatim>\<open>lvh.me\<close>). Proper configuration of a public Internet domain name
  (with HTTPS certificate from \<^emph>\<open>Let's Encrypt\<close>) works as follows.

    \<^item> Register a subdomain (e.g.\ \<^verbatim>\<open>vcs.example.org\<close>) as an alias for the IP
    address of the underlying Linux host. This usually works by some web
    interface of the hosting provider to edit DNS entries; it might require
    some time for updated DNS records to become publicly available.

    \<^item> Edit the Phabricator website configuration file in
    \<^path>\<open>/etc/apache2/sites-available/\<close> to specify \<^verbatim>\<open>ServerName\<close> and
    \<^verbatim>\<open>ServerAdmin\<close> like this: @{verbatim [display] \<open>  ServerName vcs.example.org
  ServerAdmin webmaster@example.org\<close>}

    Then reload (or restart) Apache like this:
    @{verbatim [display] \<open>  systemctl reload apache2\<close>}

    \<^item> Install \<^verbatim>\<open>certbot\<close> from \<^url>\<open>https://certbot.eff.org\<close> following the
    description for Apache and Ubuntu 18.04 or 20.04 on
    \<^url>\<open>https://certbot.eff.org/lets-encrypt/ubuntubionic-apache\<close>. Run
    \<^verbatim>\<open>certbot\<close> interactively and let it operate on the domain
    \<^verbatim>\<open>vcs.example.org\<close>.

    \<^item> Inform Phabricator about its new domain name like this:
    @{verbatim [display] \<open>  isabelle phabricator bin/config set \
    phabricator.base-uri https://vcs.example.org\<close>}

    \<^item> Visit the website \<^verbatim>\<open>https://vcs.example.org\<close> and configure Phabricator
    as described before. The following options are particularly relevant for a
    public website:

      \<^item> \<^emph>\<open>Auth Provider / Username/Password\<close>: disable \<^emph>\<open>Allow Registration\<close> to
      avoid uncontrolled registrants; users can still be invited via email
      instead.

      \<^item> Enable \<^verbatim>\<open>policy.allow-public\<close> to allow read-only access to resources,
      without requiring user registration.

    \<^item> Adjust \<^verbatim>\<open>phabricator.cookie-prefix\<close> for multiple installations with
    overlapping domains (see also the documentation of this configuration
    option within Phabricator).
\<close>


section \<open>Global data storage and backups \label{sec:phabricator-backup}\<close>

text \<open>
  The global state of a Phabricator installation consists of two main parts:

    \<^enum> The \<^emph>\<open>root directory\<close> according to
    \<^path>\<open>/etc/isabelle-phabricator.conf\<close> or \<^verbatim>\<open>isabelle phabricator -l\<close>: it
    contains the main PHP program suite with administrative tools, and some
    configuration files. The default setup also puts hosted repositories here
    (subdirectory \<^verbatim>\<open>repo\<close>).

    \<^enum> Multiple \<^emph>\<open>MySQL databases\<close> with a common prefix derived from the
    installation name --- the same name is used as database user name.

  The root user may invoke \<^verbatim>\<open>/usr/local/bin/isabelle-phabricator-dump\<close> to
  create a complete database dump within the root directory. Afterwards it is
  sufficient to make a conventional \<^bold>\<open>file-system backup\<close> of everything. To
  restore the database state, see the explanations on \<^verbatim>\<open>mysqldump\<close> in
  \<^url>\<open>https://secure.phabricator.com/book/phabricator/article/configuring_backups\<close>;
  some background information is in
  \<^url>\<open>https://secure.phabricator.com/book/phabflavor/article/so_many_databases\<close>.

  \<^medskip> The following command-line tools are particularly interesting for advanced
  database maintenance (within the Phabricator root directory):
  @{verbatim [display] \<open>  phabricator/bin/storage help dump
  phabricator/bin/storage help shell
  phabricator/bin/storage help destroy
  phabricator/bin/storage help renamespace\<close>}

  For example, copying a database snapshot from one installation to another
  works as follows. Run on the first installation root directory:

  @{verbatim [display] \<open>  phabricator/bin/storage dump > dump1.sql
  phabricator/bin/storage renamespace --from phabricator_vcs \
    --to phabricator_xyz --input dump1.sql --output dump2.sql\<close>}

  Them run on the second installation root directory:
  @{verbatim [display] \<open>  phabricator/bin/storage destroy
  phabricator/bin/storage shell < .../dump2.sql\<close>}

  Local configuration in \<^verbatim>\<open>phabricator/config/local/\<close> and hosted repositories
  need to be treated separately within the file-system. For the latter
  see also these tools:
  @{verbatim [display] \<open>  phabricator/bin/repository help list-paths
  phabricator/bin/repository help move-paths\<close>}
\<close>


section \<open>Upgrading Phabricator installations\<close>

text \<open>
  The Phabricator developers publish a new version approx.\ every 1--4 weeks:
  see also \<^url>\<open>https://secure.phabricator.com/w/changelog\<close>. There is no need to
  follow such frequent updates on the spot, but it is a good idea to upgrade
  occasionally --- with the usual care to avoid breaking a production system
  (see also \secref{sec:phabricator-backup} for database dump and backup).

  The Isabelle/Phabricator setup provides a convenience tool to upgrade all
  installations uniformly:
  @{verbatim [display] \<open>  /usr/local/bin/isabelle-phabricator-upgrade\<close>}

  This refers to the \<^verbatim>\<open>stable\<close> branch of the distribution repositories by
  default. Alternatively, it also possible to use the \<^verbatim>\<open>master\<close> like this:
  @{verbatim [display] \<open>  /usr/local/bin/isabelle-phabricator-upgrade master\<close>}

  \<^medskip>
  See
  \<^url>\<open>https://secure.phabricator.com/book/phabricator/article/upgrading\<close> for
  further explanations on Phabricator upgrade.
\<close>


section \<open>Reference of command-line tools\<close>

text \<open>
  The subsequent command-line tools usually require root user privileges on
  the underlying Linux system (e.g.\ via \<^verbatim>\<open>sudo bash\<close> to open a subshell, or
  directly via \<^verbatim>\<open>sudo isabelle phabricator ...\<close>).
\<close>


subsection \<open>\<^verbatim>\<open>isabelle phabricator\<close>\<close>

text \<open>
  The @{tool_def phabricator} tool invokes a GNU bash command-line within the
  Phabricator home directory:
  @{verbatim [display]
\<open>Usage: isabelle phabricator [OPTIONS] COMMAND [ARGS...]

  Options are:
    -l           list available Phabricator installations
    -n NAME      Phabricator installation name (default: "vcs")

  Invoke a command-line tool within the home directory of the named
  Phabricator installation.\<close>}

  Isabelle/Phabricator installations are registered in the global
  configuration file \<^path>\<open>/etc/isabelle-phabricator.conf\<close>, with name and
  root directory separated by colon (no extra whitespace). The home directory
  is the subdirectory \<^verbatim>\<open>phabricator\<close> within the root.

  \<^medskip> Option \<^verbatim>\<open>-l\<close> lists the available Phabricator installations with name and
  root directory --- without invoking a command.

  Option \<^verbatim>\<open>-n\<close> selects the explicitly named Phabricator installation.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Print the home directory of the Phabricator installation:
  @{verbatim [display] \<open>  isabelle phabricator pwd\<close>}

  Print some Phabricator configuration information:
  @{verbatim [display] \<open>  isabelle phabricator bin/config get phabricator.base-uri\<close>}

  The latter conforms to typical command templates seen in the original
  Phabricator documentation:
  @{verbatim [display] \<open>  phabricator/ $ ./bin/config get phabricator.base-uri\<close>}

  Here the user is meant to navigate to the Phabricator home manually, in
  contrast to \<^verbatim>\<open>isabelle phabricator\<close> doing it automatically thanks to the
  global configuration \<^path>\<open>/etc/isabelle-phabricator.conf\<close>.
\<close>


subsection \<open>\<^verbatim>\<open>isabelle phabricator_setup\<close>\<close>

text \<open>
  The @{tool_def phabricator_setup} tool installs a fresh Phabricator instance
  on Ubuntu 18.04 or 20.04 LTS:
  @{verbatim [display] \<open>Usage: isabelle phabricator_setup [OPTIONS]

  Options are:
    -M SOURCE    install Mercurial from source: local PATH, or URL, or ":"
    -R DIR       repository directory (default: "/var/www/phabricator-NAME/repo")
    -U           full update of system packages before installation
    -n NAME      Phabricator installation name (default: "vcs")
    -o OPTION    override Isabelle system OPTION (via NAME=VAL or NAME)
    -r DIR       installation root directory (default: "/var/www/phabricator-NAME")

  Install Phabricator as LAMP application (Linux, Apache, MySQL, PHP).

  The installation name (default: "vcs") is mapped to a regular
  Unix user; this is relevant for public SSH access.\<close>}

  Installation requires Linux root permissions. All required packages are
  installed automatically beforehand, this includes the Apache web server and
  the MySQL database engine.

  Global configuration in \<^verbatim>\<open>/etc\<close> or a few other directories like \<^verbatim>\<open>/var/www\<close>
  uses name prefixes like \<^verbatim>\<open>isabelle-phabricator\<close> or \<^verbatim>\<open>phabricator\<close>. Local
  configuration for a particular installation uses more specific names derived
  from \<^verbatim>\<open>phabricator-\<close>\<open>NAME\<close>, e.g.\ \<^verbatim>\<open>/var/www/phabricator-vcs\<close> for the
  default.

  Knowing the naming conventions, it is possible to purge a Linux installation
  from Isabelle/Phabricator with some effort, but there is no automated
  procedure for de-installation. In the worst case, it might be better to
  re-install the virtual machine from a clean image.

  \<^medskip>
  Option \<^verbatim>\<open>-U\<close> ensures a full update of system packages, before installing
  further packages required by Phabricator. This might require a reboot.

  Option \<^verbatim>\<open>-M:\<close> installs a standard Mercurial release from source --- the one
  that is used by the Phabricator hosting service
  \<^url>\<open>https://admin.phacility.com\<close>. This avoids various problems with the
  package provided by Ubuntu 18.04 or 20.04. Alternatively, an explicit file
  path or URL the source archive (\<^verbatim>\<open>.tar.gz\<close>) may be given here. This option
  is recommended for production use, but it requires to \<^emph>\<open>uninstall\<close> existing
  Mercurial packages provided by the operating system.

  Option \<^verbatim>\<open>-n\<close> provides an alternative installation name. The default name
  \<^verbatim>\<open>vcs\<close> means ``version control system''. The name appears in the URL for SSH
  access, and thus has some relevance to end-users. The initial server URL
  also uses the same suffix, but that can (and should) be changed later via
  regular Apache configuration.

  Option \<^verbatim>\<open>-o\<close> augments the environment of Isabelle system options: relevant
  options for Isabelle/Phabricator have the prefix ``\<^verbatim>\<open>phabricator_\<close>'' (see
  also the result of e.g. ``\<^verbatim>\<open>isabelle options -l\<close>'').

  Option \<^verbatim>\<open>-r\<close> specifies an alternative installation root directory: it needs
  to be accessible for the Apache web server.

  Option \<^verbatim>\<open>-R\<close> specifies an alternative directory for repositories that are
  hosted by Phabricator. Provided that it is accessible for the Apache web
  server, the directory can be reused for the \<^verbatim>\<open>hgweb\<close> view by Mercurial.\<^footnote>\<open>See
  also the documentation
  \<^url>\<open>https://www.mercurial-scm.org/wiki/PublishingRepositories\<close> and the
  example \<^url>\<open>https://isabelle.sketis.net/repos\<close>.\<close>
\<close>


subsection \<open>\<^verbatim>\<open>isabelle phabricator_setup_mail\<close>\<close>

text \<open>
  The @{tool_def phabricator_setup_mail} tool provides mail configuration for
  an existing Phabricator installation:
  @{verbatim [display] \<open>Usage: isabelle phabricator_setup_mail [OPTIONS]

  Options are:
    -T USER      send test mail to Phabricator user
    -f FILE      config file (default: "mailers.json" within
                 Phabricator root)
    -n NAME      Phabricator installation name (default: "vcs")

  Provide mail configuration for existing Phabricator installation.\<close>}

  Proper mail configuration is vital for Phabricator, but the details can be
  tricky. A common approach is to re-use an existing SMTP mail service, as is
  often included in regular web hosting packages. It is sufficient to create
  one mail account for multiple Phabricator installations, but the
  configuration needs to be set for each installation.

  The first invocation of \<^verbatim>\<open>isabelle phabricator_setup_mail\<close> without options
  creates a JSON template file. Its \<^verbatim>\<open>key\<close> entry should be changed to
  something sensible to identify the configuration, e.g.\ the Internet Domain
  Name of the mail address. The \<^verbatim>\<open>options\<close> specify the SMTP server address and
  account information.

  Another invocation of \<^verbatim>\<open>isabelle phabricator_setup_mail\<close> with updated JSON
  file will change the underlying Phabricator installation. This can be done
  repeatedly, until everything works as expected.

  Option \<^verbatim>\<open>-T\<close> invokes a standard Phabricator test procedure for the mail
  configuration. The argument needs to be a valid Phabricator user: the mail
  address is derived from the user profile.

  Option \<^verbatim>\<open>-f\<close> refers to an existing JSON configuration file, e.g.\ from a
  previous successful Phabricator installation: sharing mailers setup with the
  same mail address is fine for outgoing mails; incoming mails are optional
  and not configured here.
\<close>


subsection \<open>\<^verbatim>\<open>isabelle phabricator_setup_ssh\<close>\<close>

text \<open>
  The @{tool_def phabricator_setup_ssh} tool configures a special SSH service
  for all Phabricator installations:
  @{verbatim [display] \<open>Usage: isabelle phabricator_setup_ssh [OPTIONS]

  Options are:
    -p PORT      sshd port for Phabricator servers (default: 2222)
    -q PORT      sshd port for the operating system (default: 22)

  Configure ssh service for all Phabricator installations: a separate sshd
  is run in addition to the one of the operating system, and ports need to
  be distinct.

  A particular Phabricator installation is addressed by using its
  name as the ssh user; the actual Phabricator user is determined via
  stored ssh keys.\<close>}

  This is optional, but very useful. It allows to refer to hosted repositories
  via ssh with the usual public-key authentication. It also allows to
  communicate with a Phabricator server via the JSON API of
  \<^emph>\<open>Conduit\<close>\<^footnote>\<open>\<^url>\<open>https://secure.phabricator.com/book/phabricator/article/conduit\<close>\<close>.

  \<^medskip> The Phabricator SSH server distinguishes installations by their name,
  e.g.\ \<^verbatim>\<open>vcs\<close> as SSH user name. The public key that is used for
  authentication identifies the user within Phabricator: there is a web
  interface to provide that as part of the user profile.

  The operating system already has an SSH server (by default on port 22) that
  remains important for remote administration of the machine.

  \<^medskip>
  Options \<^verbatim>\<open>-p\<close> and \<^verbatim>\<open>-q\<close> allow to change the port assignment for both
  servers. A common scheme is \<^verbatim>\<open>-p 22 -q 222\<close> to leave the standard port to
  Phabricator, to simplify the ssh URL that users will see for remote
  repository clones.\<^footnote>\<open>For the rare case of hosting Subversion repositories,
  port 22 is de-facto required. Otherwise Phabricator presents malformed
  \<^verbatim>\<open>svn+ssh\<close> URLs with port specification.\<close>

  Redirecting the operating system sshd to port 222 requires some care: it
  requires to adjust the remote login procedure, e.g.\ in \<^verbatim>\<open>$HOME/.ssh/config\<close>
  to add a \<^verbatim>\<open>Port\<close> specification for the server machine.
\<close>

end
