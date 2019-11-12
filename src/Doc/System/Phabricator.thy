(*:maxLineLen=78:*)

theory Phabricator
imports Base
begin

chapter \<open>Phabricator server administration\<close>

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
  hosting of servers, but it is relatively easy to do \<^emph>\<open>independent
  self-hosting\<close> on a standard LAMP server (Linux, Apache, MySQL, PHP). This
  merely requires a virtual Ubuntu server on the net, which can be rented
  rather cheaply from local hosting providers (there is no need to follow big
  cloud corporations). So it is feasible to remain the master of your virtual
  home, following the slogan ``own all your data''. In many respects,
  Phabricator is similar to the well-known
  Nextcloud\<^footnote>\<open>\<^url>\<open>https://nextcloud.com\<close>\<close> product, concerning both the
  technology and sociology.

  \<^medskip>
  The following Phabricator instances may serve as examples:

    \<^item> Phabricator development \<^url>\<open>https://secure.phabricator.com\<close>
    \<^item> Wikimedia development \<^url>\<open>https://phabricator.wikimedia.org\<close>
    \<^item> Mercurial development \<^url>\<open>https://phab.mercurial-scm.org\<close>
    \<^item> Isabelle development \<^url>\<open>https://isabelle-dev.sketis.net\<close>

  \<^medskip> Initial Phabricator server configuration requires many details to be done
  right.\<^footnote>\<open>See also
  \<^url>\<open>https://secure.phabricator.com/book/phabricator/article/installation_guide\<close>
  in the context of \<^url>\<open>https://help.ubuntu.com/lts/serverguide\<close>.\<close> Isabelle
  provides some command-line tools to help with the setup, and afterwards
  Isabelle support is optional: it is possible to run and maintain the server,
  without requiring a full Isabelle distribution again.
\<close>


section \<open>Quick start\<close>

text \<open>
  The starting point is a fresh installation of \<^bold>\<open>Ubuntu 18.04 LTS\<close>: that
  particular version is required due to subtle dependencies on system
  configuration and add-on packages.

  For production use, a proper \<^emph>\<open>Virtual Server\<close> or \<^emph>\<open>Root Server\<close> product
  from a hosting provider will be required, including an Internet Domain Name
  (a pseudo sub-domain in the style of Apache is sufficient).

  Initial experimentation also works on a local host, e.g.\ via
  VirtualBox\<^footnote>\<open>\<^url>\<open>https://www.virtualbox.org\<close>\<close>. The public server behind
  \<^verbatim>\<open>lvh.me\<close> provides arbitrary subdomains as an alias to \<^verbatim>\<open>localhost\<close>, which
  will be used for the default installation below.

  All administrative commands need to be run as \<^verbatim>\<open>root\<close> user (e.g.\ via
  \<^verbatim>\<open>sudo\<close>).
\<close>


subsection \<open>Initial setup\<close>

text \<open>
  Isabelle can managed multiple named installations Phabricator installations:
  this allows to separate administrative responsibilities, e.g.\ different
  approaches to user management for different projects. Subsequently we always
  use the implicit default name ``\<^verbatim>\<open>vcs\<close>'': it will appear in file and
  directory locations, internal database names and URLs.

  The initial setup (with full Linux package upgrade) works as follows:

  @{verbatim [display] \<open>  isabelle phabricator_setup -U\<close>}

  After installing many packages and cloning the Phabricator distribution, the
  final output of the tool should be the URL for further manual configuration
  (using a local web browser). Here the key points are:

    \<^item> An initial user account that will get administrator rights. There is no
    need to create a separate \<^verbatim>\<open>admin\<close> account. Instead, a regular user that
    will take over this responsibility can be used here. Subsequently we
    assume that user \<^verbatim>\<open>makarius\<close> becomes the initial administrator.

    \<^item> An \<^emph>\<open>Auth Provider\<close> to manage user names and passwords. None is provided
    by default, and Phabricator points out this omission prominently in its
    overview of \<^emph>\<open>Setup Issues\<close>: following these hints quickly leads to the
    place where a regular \<^emph>\<open>Username/Password\<close> provider can be added.

  Note that Phabricator allows to delegate the responsibility of
  authentication to big corporations like Google and Facebook, but these can
  be easily avoided. Genuine self-hosting means to manage users directly,
  without outsourcing of authentication.

  \<^medskip>
  With the Auth Provider available, the administrator can now set a proper
  password. This works e.g.\ by initiating a local password reset procedure:

  @{verbatim [display] \<open>  isabelle phabricator bin/auth recover makarius\<close>}

  The printed URL gives access to a password dialog in the web browser.

  Further users will be able to provide a password more directly, because the
  Auth Provider is now active.

  \<^medskip>
  The pending request in Phabricator \<^bold>\<open>Setup Issues\<close> to lock the configuration
  can be fulfilled as follows:

  @{verbatim [display] \<open>  isabelle phabricator bin/auth lock\<close>}

  \<^medskip>
  Most other Setup Issues can be ignored, after reading through them briefly
  to make sure that there are no genuine problems remaining.
\<close>


subsection \<open>Mailer configuration\<close>

text \<open>
  The next important thing is messaging: Phabricator needs to be able to
  communicate with users. There are many variations on \<^emph>\<open>Mailer
  Configuration\<close>, but a conventional SMTP server connection with a dedicated
  \<^verbatim>\<open>phabricator\<close> user is sufficient. Note that there is no need to run a mail
  server on the self-hosted Linux machine: regular web-hosting packages
  usually allow to create new mail accounts easily. (As a last resort it is
  possible to use a service like Gmail, but that would again introduce
  unnecessary dependency on Google.)

  \<^medskip>
  Mailer configuration requires a few command-line invocations as follows:

  @{verbatim [display] \<open>  isabelle phabricator_setup_mail\<close>}

  \<^noindent> Now edit the generated JSON file to provide the mail account details. Then
  add and test it with Phabricator like this (to let Phabricator send a
  message to the administrator from above):

  @{verbatim [display] \<open>  isabelle phabricator_setup_mail -T makarius\<close>}

  The mail configuration process can be refined and repeated until it really
  works: host name, port number, protocol etc.\ all need to be correct. The
  \<^verbatim>\<open>key\<close> field in the JSON file identifies the name of the configuration; it
  will be overwritten each time, when taking over the parameters via
  \<^verbatim>\<open>isabelle phabricator_setup_mail\<close>.

  \<^medskip>
  For information, the resulting mailer configuration can be queried like
  this:

  @{verbatim [display] \<open>  isabelle phabricator bin/config get cluster.mailers\<close>}
\<close>


section \<open>Reference of command-line tools\<close>

text \<open>
  The subsequent command-line tools usually require root user privileges on
  the underlying Linux system (e.g.\ via \<^verbatim>\<open>sudo bash\<close> to open a subshell, or
  directly via \<^verbatim>\<open>sudo isabelle ...\<close>). Note that Isabelle refers to
  user-specific configuration in the user home directory via @{setting
  ISABELLE_HOME_USER} (\secref{sec:settings}); that may be different or absent
  for the root user and thus cause confusion.
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
  root directory.

  Option \<^verbatim>\<open>-n\<close> selects the explicitly named Phabricator installation.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  Print the home directory of the Phabricator installation:
  @{verbatim [display] \<open>isabelle phabricator pwd\<close>}

  Print some Phabricator configuration information:
  @{verbatim [display] \<open>isabelle phabricator bin/config get phabricator.base-uri\<close>}

  The latter conforms to typical command templates seen in the original
  Phabricator documentation:
  @{verbatim [display] \<open>phabricator/ $ ./bin/config get phabricator.base-uri\<close>}

  Here the user is meant to navigate to the Phabricator home manually, in
  contrast to \<^verbatim>\<open>isabelle phabricator\<close> doing it automatically based on
  \<^path>\<open>/etc/isabelle-phabricator.conf\<close>.
\<close>


subsection \<open>\<^verbatim>\<open>isabelle phabricator_setup\<close>\<close>

text \<open>
  The @{tool_def phabricator_setup} installs a fresh Phabricator instance on
  Ubuntu Linux (notably 18.04 LTS):
  @{verbatim [display] \<open>Usage: isabelle phabricator_setup [OPTIONS]

  Options are:
    -R DIR       repository directory (default: "/var/www/phabricator-NAME/repo")
    -U           full update of system packages before installation
    -n NAME      Phabricator installation name (default: "vcs")
    -r DIR       installation root directory (default: "/var/www/phabricator-NAME")

  Install Phabricator as LAMP application (Linux, Apache, MySQL, PHP).

  The installation name (default: "vcs") is mapped to a regular
  Unix user; this is relevant for public SSH access.\<close>}

  Installation requires Linux root user access. All required packages are
  installed automatically beforehand, this includes the Apache web server and
  the MySQL database engine.

  Global configuration in \<^verbatim>\<open>/etc\<close> and other directories like \<^verbatim>\<open>/var/www\<close>
  always use name prefixes \<^verbatim>\<open>isabelle-phabricator\<close> or \<^verbatim>\<open>phabricator\<close>. Local
  configuration for a particular installation uses more specific names derived
  from \<^verbatim>\<open>phabricator-\<close>\<open>NAME\<close>, e.g. \<^verbatim>\<open>/var/www/phabricator-vcs\<close> for a default
  installation.

  Knowing the conventions, it is possible to purge a Linux installation from
  Isabelle/Phabricator with some effort. There is no automated
  de-installation: it is often better to re-install a clean virtual machine
  image.

  \<^medskip>
  Option \<^verbatim>\<open>-U\<close> ensures a full update of system packages, before installing
  further packages required by Phabricator.

  Option \<^verbatim>\<open>-n\<close> provides an alternative installation name. The default name
  \<^verbatim>\<open>vcs\<close> means ``Version Control System''. The name will appear in the URL for
  SSH access, and thus has some relevance to end-users. The initial server URL
  also uses that name suffix, but it can be changed later via regular Apache
  configuration.

  Option \<^verbatim>\<open>-r\<close> specifies an alternative installation root directory: it needs
  to be accessible for the Apache web server.

  Option \<^verbatim>\<open>-R\<close> specifies an alternative directory for repositories that are
  hosted by Phabricator. Provided that it is accessible for the Apache web
  server, the directory can be re-used directly for the builtin \<^verbatim>\<open>hgweb\<close> view
  by Mercurial. See also the documentation
  \<^url>\<open>https://www.mercurial-scm.org/wiki/PublishingRepositories#hgweb\<close> and the
  example \<^url>\<open>https://isabelle.sketis.net/repos\<close> for repositories in
  \<^url>\<open>https://isabelle-dev.sketis.net/diffusion\<close>.
\<close>


subsection \<open>\<^verbatim>\<open>isabelle phabricator_setup_mail\<close>\<close>

text \<open>
  The @{tool_def phabricator_setup_mail} provides mail configuration for an
  existing Phabricator installation (preferably via SMTP):
  @{verbatim [display] \<open>Usage: isabelle phabricator_setup_mail [OPTIONS]

  Options are:
    -T USER      send test mail to Phabricator user
    -f FILE      config file (default: "mailers.json" within
                 Phabricator root)
    -n NAME      Phabricator installation name (default: "vcs")

  Provide mail configuration for existing Phabricator installation.\<close>}

  Proper mail configuration is vital for Phabricator, but the details can be
  tricky. A common approach is to re-use an existing SMTP mail service, as is
  often included in regular web hosting packages. A single account for
  multiple Phabricator installations is sufficient, but the configuration
  needs to be set for each installation separately.

  The first invocation of \<^verbatim>\<open>isabelle phabricator_setup_mail\<close> without options
  creates a JSON template file. Its \<^verbatim>\<open>key\<close> entry should be changed to
  something sensible to identify the configuration, e.g.\ the Internet Domain
  Name of the mail address being used here. The \<^verbatim>\<open>options\<close> specify the SMTP
  server address and account information.

  Another invocation of \<^verbatim>\<open>isabelle phabricator_setup_mail\<close> with updated JSON
  file will change the underlying Phabricator installation. This can be done
  repeatedly, until everything works as expected.

  Option \<^verbatim>\<open>-T\<close> invokes a standard Phabricator test procedure for the mail
  configuration. The argument needs to be a valid Phabricator user: the mail
  address is derived from the user profile.

  Option \<^verbatim>\<open>-f\<close> refers to an existing JSON configuration file, e.g.\ from a
  different Phabricator installation: sharing mailers setup with the same mail
  address works for outgoing mails; incoming mails are not strictly needed.
\<close>

end
