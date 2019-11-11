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
  right. Isabelle provides some command-line tools to help with it, but
  afterwards Isabelle support is optional: it is possible to run and maintain
  the server, without requiring a full Isabelle distribution again.
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

  @{verbatim [display] \<open>  isabelle phabricator ./bin/auth recover makarius\<close>}

  The printed URL gives access to a password dialog in the web browser.

  Further users will be able to provide a password more directly, because the
  Auth Provider is now active.

  \<^medskip>
  The pending request in Phabricator Setup Issues to lock the configuration
  can be fulfilled as follows:

  @{verbatim [display] \<open>  isabelle phabricator ./bin/auth lock\<close>}
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

  @{verbatim [display] \<open>  isabelle phabricator ./bin/config get cluster.mailers\<close>}
\<close>

end
