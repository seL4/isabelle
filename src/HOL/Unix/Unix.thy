(*  Title:      HOL/Unix/Unix.thy
    Author:     Markus Wenzel, TU Muenchen
*)

section \<open>Unix file-systems \label{sec:unix-file-system}\<close>

theory Unix
  imports
    Nested_Environment
    "HOL-Library.Sublist"
begin

text \<open>
  We give a simple mathematical model of the basic structures underlying the
  Unix file-system, together with a few fundamental operations that could be
  imagined to be performed internally by the Unix kernel. This forms the basis
  for the set of Unix system-calls to be introduced later (see
  \secref{sec:unix-trans}), which are the actual interface offered to
  processes running in user-space.

  \<^medskip>
  Basically, any Unix file is either a \<^emph>\<open>plain file\<close> or a \<^emph>\<open>directory\<close>,
  consisting of some \<^emph>\<open>content\<close> plus \<^emph>\<open>attributes\<close>. The content of a plain
  file is plain text. The content of a directory is a mapping from names to
  further files.\<^footnote>\<open>In fact, this is the only way that names get associated with
  files. In Unix files do \<^emph>\<open>not\<close> have a name in itself. Even more, any number
  of names may be associated with the very same file due to \<^emph>\<open>hard links\<close>
  (although this is excluded from our model).\<close> Attributes include information
  to control various ways to access the file (read, write etc.).

  Our model will be quite liberal in omitting excessive detail that is easily
  seen to be ``irrelevant'' for the aspects of Unix file-systems to be
  discussed here. First of all, we ignore character and block special files,
  pipes, sockets, hard links, symbolic links, and mount points.
\<close>


subsection \<open>Names\<close>

text \<open>
  User ids and file name components shall be represented by natural numbers
  (without loss of generality). We do not bother about encoding of actual
  names (e.g.\ strings), nor a mapping between user names and user ids as
  would be present in a reality.
\<close>

type_synonym uid = nat
type_synonym name = nat
type_synonym path = "name list"


subsection \<open>Attributes\<close>

text \<open>
  Unix file attributes mainly consist of \<^emph>\<open>owner\<close> information and a number of
  \<^emph>\<open>permission\<close> bits which control access for ``user'', ``group'', and
  ``others'' (see the Unix man pages \<open>chmod(2)\<close> and \<open>stat(2)\<close> for more
  details).

  \<^medskip>
  Our model of file permissions only considers the ``others'' part. The
  ``user'' field may be omitted without loss of overall generality, since the
  owner is usually able to change it anyway by performing \<open>chmod\<close>.\<^footnote>\<open>The
  inclined Unix expert may try to figure out some exotic arrangements of a
  real-world Unix file-system such that the owner of a file is unable to apply
  the \<open>chmod\<close> system call.\<close> We omit ``group'' permissions as a genuine
  simplification as we just do not intend to discuss a model of multiple
  groups and group membership, but pretend that everyone is member of a single
  global group.\<^footnote>\<open>A general HOL model of user group structures and related
  issues is given in \<^cite>\<open>"Naraschewski:2001"\<close>.\<close>
\<close>

datatype perm =
    Readable
  | Writable
  | Executable    \<comment> \<open>(ignored)\<close>

type_synonym perms = "perm set"

record att =
  owner :: uid
  others :: perms

text \<open>
  For plain files \<^term>\<open>Readable\<close> and \<^term>\<open>Writable\<close> specify read and write
  access to the actual content, i.e.\ the string of text stored here. For
  directories \<^term>\<open>Readable\<close> determines if the set of entry names may be
  accessed, and \<^term>\<open>Writable\<close> controls the ability to create or delete any
  entries (both plain files or sub-directories).

  As another simplification, we ignore the \<^term>\<open>Executable\<close> permission
  altogether. In reality it would indicate executable plain files (also known
  as ``binaries''), or control actual lookup of directory entries (recall that
  mere directory browsing is controlled via \<^term>\<open>Readable\<close>). Note that the
  latter means that in order to perform any file-system operation whatsoever,
  all directories encountered on the path would have to grant
  \<^term>\<open>Executable\<close>. We ignore this detail and pretend that all directories
  give \<^term>\<open>Executable\<close> permission to anybody.
\<close>


subsection \<open>Files\<close>

text \<open>
  In order to model the general tree structure of a Unix file-system we use
  the arbitrarily branching datatype \<^typ>\<open>('a, 'b, 'c) env\<close> from the
  standard library of Isabelle/HOL \<^cite>\<open>"Bauer-et-al:2002:HOL-Library"\<close>.
  This type provides constructors \<^term>\<open>Val\<close> and \<^term>\<open>Env\<close> as follows:

  \<^medskip>
  {\def\isastyleminor{\isastyle}
  \begin{tabular}{l}
  @{term [source] "Val :: 'a \<Rightarrow> ('a, 'b, 'c) env"} \\
  @{term [source] "Env :: 'b \<Rightarrow> ('c \<Rightarrow> ('a, 'b, 'c) env option) \<Rightarrow> ('a, 'b, 'c) env"} \\
  \end{tabular}}
  \<^medskip>

  Here the parameter \<^typ>\<open>'a\<close> refers to plain values occurring at leaf
  positions, parameter \<^typ>\<open>'b\<close> to information kept with inner branch
  nodes, and parameter \<^typ>\<open>'c\<close> to the branching type of the tree
  structure. For our purpose we use the type instance with \<^typ>\<open>att \<times>
  string\<close> (representing plain files), \<^typ>\<open>att\<close> (for attributes of
  directory nodes), and \<^typ>\<open>name\<close> (for the index type of directory nodes).
\<close>

type_synonym "file" = "(att \<times> string, att, name) env"

text \<open>
  \<^medskip>
  The HOL library also provides \<^term>\<open>lookup\<close> and \<^term>\<open>update\<close> operations
  for general tree structures with the subsequent primitive recursive
  characterizations.

  \<^medskip>
  {\def\isastyleminor{\isastyle}
  \begin{tabular}{l}
  @{term [source] "lookup :: ('a, 'b, 'c) env \<Rightarrow> 'c list \<Rightarrow> ('a, 'b, 'c) env option"} \\
  @{term [source]
  "update :: 'c list \<Rightarrow> ('a, 'b, 'c) env option \<Rightarrow> ('a, 'b, 'c) env \<Rightarrow> ('a, 'b, 'c) env"} \\
  \end{tabular}}

  @{thm [display, indent = 2, eta_contract = false] lookup_eq [no_vars]}
  @{thm [display, indent = 2, eta_contract = false] update_eq [no_vars]}

  Several further properties of these operations are proven in \<^cite>\<open>"Bauer-et-al:2002:HOL-Library"\<close>. These will be routinely used later on
  without further notice.

  \<^bigskip>
  Apparently, the elements of type \<^typ>\<open>file\<close> contain an \<^typ>\<open>att\<close>
  component in either case. We now define a few auxiliary operations to
  manipulate this field uniformly, following the conventions for record types
  in Isabelle/HOL \<^cite>\<open>"Nipkow-et-al:2000:HOL"\<close>.
\<close>

definition
  "attributes file =
    (case file of
      Val (att, text) \<Rightarrow> att
    | Env att dir \<Rightarrow> att)"

definition
  "map_attributes f file =
    (case file of
      Val (att, text) \<Rightarrow> Val (f att, text)
    | Env att dir \<Rightarrow> Env (f att) dir)"

lemma [simp]: "attributes (Val (att, text)) = att"
  by (simp add: attributes_def)

lemma [simp]: "attributes (Env att dir) = att"
  by (simp add: attributes_def)

lemma [simp]: "attributes (map_attributes f file) = f (attributes file)"
  by (cases "file") (simp_all add: attributes_def map_attributes_def
    split_tupled_all)

lemma [simp]: "map_attributes f (Val (att, text)) = Val (f att, text)"
  by (simp add: map_attributes_def)

lemma [simp]: "map_attributes f (Env att dir) = Env (f att) dir"
  by (simp add: map_attributes_def)


subsection \<open>Initial file-systems\<close>

text \<open>
  Given a set of \<^emph>\<open>known users\<close> a file-system shall be initialized by
  providing an empty home directory for each user, with read-only access for
  everyone else. (Note that we may directly use the user id as home directory
  name, since both types have been identified.) Certainly, the very root
  directory is owned by the super user (who has user id 0).
\<close>

definition
  "init users =
    Env \<lparr>owner = 0, others = {Readable}\<rparr>
      (\<lambda>u. if u \<in> users then Some (Env \<lparr>owner = u, others = {Readable}\<rparr> Map.empty)
        else None)"


subsection \<open>Accessing file-systems\<close>

text \<open>
  The main internal file-system operation is access of a file by a user,
  requesting a certain set of permissions. The resulting \<^typ>\<open>file option\<close>
  indicates if a file had been present at the corresponding \<^typ>\<open>path\<close> and if
  access was granted according to the permissions recorded within the
  file-system.

  Note that by the rules of Unix file-system security (e.g.\ \<^cite>\<open>"Tanenbaum:1992"\<close>) both the super-user and owner may always access a file
  unconditionally (in our simplified model).
\<close>

definition
  "access root path uid perms =
    (case lookup root path of
      None \<Rightarrow> None
    | Some file \<Rightarrow>
        if uid = 0
          \<or> uid = owner (attributes file)
          \<or> perms \<subseteq> others (attributes file)
        then Some file
        else None)"

text \<open>
  \<^medskip>
  Successful access to a certain file is the main prerequisite for
  system-calls to be applicable (cf.\ \secref{sec:unix-trans}). Any
  modification of the file-system is then performed using the basic
  \<^term>\<open>update\<close> operation.

  \<^medskip>
  We see that \<^term>\<open>access\<close> is just a wrapper for the basic \<^term>\<open>lookup\<close>
  function, with additional checking of attributes. Subsequently we establish
  a few auxiliary facts that stem from the primitive \<^term>\<open>lookup\<close> used
  within \<^term>\<open>access\<close>.
\<close>

lemma access_empty_lookup: "access root path uid {} = lookup root path"
  by (simp add: access_def split: option.splits)

lemma access_some_lookup:
  "access root path uid perms = Some file \<Longrightarrow>
    lookup root path = Some file"
  by (simp add: access_def split: option.splits if_splits)

lemma access_update_other:
  assumes parallel: "path' \<parallel> path"
  shows "access (update path' opt root) path uid perms = access root path uid perms"
proof -
  from parallel obtain y z xs ys zs where
      "y \<noteq> z" and "path' = xs @ y # ys" and "path = xs @ z # zs"
    by (blast dest: parallel_decomp)
  then have "lookup (update path' opt root) path = lookup root path"
    by (blast intro: lookup_update_other)
  then show ?thesis by (simp only: access_def)
qed


section \<open>File-system transitions \label{sec:unix-trans}\<close>

subsection \<open>Unix system calls \label{sec:unix-syscall}\<close>

text \<open>
  According to established operating system design (cf.\ \<^cite>\<open>"Tanenbaum:1992"\<close>) user space processes may only initiate system operations
  by a fixed set of \<^emph>\<open>system-calls\<close>. This enables the kernel to enforce
  certain security policies in the first place.\<^footnote>\<open>Incidently, this is the very
  same principle employed by any ``LCF-style'' theorem proving system
  according to Milner's principle of ``correctness by construction'', such as
  Isabelle/HOL itself.\<close>

  \<^medskip>
  In our model of Unix we give a fixed datatype \<open>operation\<close> for the syntax of
  system-calls, together with an inductive definition of file-system state
  transitions of the form \<open>root \<midarrow>x\<rightarrow> root'\<close> for the operational semantics.
\<close>

datatype operation =
    Read uid string path
  | Write uid string path
  | Chmod uid perms path
  | Creat uid perms path
  | Unlink uid path
  | Mkdir uid perms path
  | Rmdir uid path
  | Readdir uid "name set" path

text \<open>
  The \<^typ>\<open>uid\<close> field of an operation corresponds to the \<^emph>\<open>effective user id\<close>
  of the underlying process, although our model never mentions processes
  explicitly. The other parameters are provided as arguments by the caller;
  the \<^term>\<open>path\<close> one is common to all kinds of system-calls.
\<close>

primrec uid_of :: "operation \<Rightarrow> uid"
  where
    "uid_of (Read uid text path) = uid"
  | "uid_of (Write uid text path) = uid"
  | "uid_of (Chmod uid perms path) = uid"
  | "uid_of (Creat uid perms path) = uid"
  | "uid_of (Unlink uid path) = uid"
  | "uid_of (Mkdir uid path perms) = uid"
  | "uid_of (Rmdir uid path) = uid"
  | "uid_of (Readdir uid names path) = uid"

primrec path_of :: "operation \<Rightarrow> path"
  where
    "path_of (Read uid text path) = path"
  | "path_of (Write uid text path) = path"
  | "path_of (Chmod uid perms path) = path"
  | "path_of (Creat uid perms path) = path"
  | "path_of (Unlink uid path) = path"
  | "path_of (Mkdir uid perms path) = path"
  | "path_of (Rmdir uid path) = path"
  | "path_of (Readdir uid names path) = path"

text \<open>
  \<^medskip>
  Note that we have omitted explicit \<open>Open\<close> and \<open>Close\<close> operations, pretending
  that \<^term>\<open>Read\<close> and \<^term>\<open>Write\<close> would already take care of this behind
  the scenes. Thus we have basically treated actual sequences of real
  system-calls \<open>open\<close>--\<open>read\<close>/\<open>write\<close>--\<open>close\<close> as atomic.

  In principle, this could make big a difference in a model with explicit
  concurrent processes. On the other hand, even on a real Unix system the
  exact scheduling of concurrent \<open>open\<close> and \<open>close\<close> operations does \<^emph>\<open>not\<close>
  directly affect the success of corresponding \<open>read\<close> or \<open>write\<close>. Unix allows
  several processes to have files opened at the same time, even for writing!
  Certainly, the result from reading the contents later may be hard to
  predict, but the system-calls involved here will succeed in any case.

  \<^bigskip>
  The operational semantics of system calls is now specified via transitions
  of the file-system configuration. This is expressed as an inductive relation
  (although there is no actual recursion involved here).
\<close>

inductive transition :: "file \<Rightarrow> operation \<Rightarrow> file \<Rightarrow> bool"
  (\<open>(\<open>open_block notation=\<open>mixfix transition\<close>\<close>_ \<midarrow>_\<rightarrow> _)\<close> [90, 1000, 90] 100)
  where
    read:
      "root \<midarrow>(Read uid text path)\<rightarrow> root"
      if "access root path uid {Readable} = Some (Val (att, text))"
  | "write":
      "root \<midarrow>(Write uid text path)\<rightarrow> update path (Some (Val (att, text))) root"
      if "access root path uid {Writable} = Some (Val (att, text'))"
  | chmod:
      "root \<midarrow>(Chmod uid perms path)\<rightarrow>
        update path (Some (map_attributes (others_update (\<lambda>_. perms)) file)) root"
      if "access root path uid {} = Some file" and "uid = 0 \<or> uid = owner (attributes file)"
  | creat:
      "root \<midarrow>(Creat uid perms path)\<rightarrow>
        update path (Some (Val (\<lparr>owner = uid, others = perms\<rparr>, []))) root"
      if "path = parent_path @ [name]"
      and "access root parent_path uid {Writable} = Some (Env att parent)"
      and "access root path uid {} = None"
  | unlink:
      "root \<midarrow>(Unlink uid path)\<rightarrow> update path None root"
      if "path = parent_path @ [name]"
      and "access root parent_path uid {Writable} = Some (Env att parent)"
      and "access root path uid {} = Some (Val plain)"
  | mkdir:
      "root \<midarrow>(Mkdir uid perms path)\<rightarrow>
        update path (Some (Env \<lparr>owner = uid, others = perms\<rparr> Map.empty)) root"
      if "path = parent_path @ [name]"
      and "access root parent_path uid {Writable} = Some (Env att parent)"
      and "access root path uid {} = None"
  | rmdir:
      "root \<midarrow>(Rmdir uid path)\<rightarrow> update path None root"
      if "path = parent_path @ [name]"
      and "access root parent_path uid {Writable} = Some (Env att parent)"
      and "access root path uid {} = Some (Env att' Map.empty)"
  | readdir:
      "root \<midarrow>(Readdir uid names path)\<rightarrow> root"
      if "access root path uid {Readable} = Some (Env att dir)"
      and "names = dom dir"

text \<open>
  \<^medskip>
  Certainly, the above specification is central to the whole formal
  development. Any of the results to be established later on are only
  meaningful to the outside world if this transition system provides an
  adequate model of real Unix systems. This kind of ``reality-check'' of a
  formal model is the well-known problem of \<^emph>\<open>validation\<close>.

  If in doubt, one may consider to compare our definition with the informal
  specifications given the corresponding Unix man pages, or even peek at an
  actual implementation such as \<^cite>\<open>"Torvalds-et-al:Linux"\<close>. Another common
  way to gain confidence into the formal model is to run simple simulations
  (see \secref{sec:unix-examples}), and check the results with that of
  experiments performed on a real Unix system.
\<close>


subsection \<open>Basic properties of single transitions \label{sec:unix-single-trans}\<close>

text \<open>
  The transition system \<open>root \<midarrow>x\<rightarrow> root'\<close> defined above determines a unique
  result \<^term>\<open>root'\<close> from given \<^term>\<open>root\<close> and \<^term>\<open>x\<close> (this is
  holds rather trivially, since there is even only one clause for each
  operation). This uniqueness statement will simplify our subsequent
  development to some extent, since we only have to reason about a partial
  function rather than a general relation.
\<close>

theorem transition_uniq:
  assumes root': "root \<midarrow>x\<rightarrow> root'"
    and root'': "root \<midarrow>x\<rightarrow> root''"
  shows "root' = root''"
  using root''
proof cases
  case read
  with root' show ?thesis by cases auto
next
  case "write"
  with root' show ?thesis by cases auto
next
  case chmod
  with root' show ?thesis by cases auto
next
  case creat
  with root' show ?thesis by cases auto
next
  case unlink
  with root' show ?thesis by cases auto
next
  case mkdir
  with root' show ?thesis by cases auto
next
  case rmdir
  with root' show ?thesis by cases auto
next
  case readdir
  with root' show ?thesis by cases blast+
qed

text \<open>
  \<^medskip>
  Apparently, file-system transitions are \<^emph>\<open>type-safe\<close> in the sense that the
  result of transforming an actual directory yields again a directory.
\<close>

theorem transition_type_safe:
  assumes tr: "root \<midarrow>x\<rightarrow> root'"
    and inv: "\<exists>att dir. root = Env att dir"
  shows "\<exists>att dir. root' = Env att dir"
proof (cases "path_of x")
  case Nil
  with tr inv show ?thesis
    by cases (auto simp add: access_def split: if_splits)
next
  case Cons
  from tr obtain opt where
      "root' = root \<or> root' = update (path_of x) opt root"
    by cases auto
  with inv Cons show ?thesis
    by (auto simp add: update_eq split: list.splits)
qed

text \<open>
  The previous result may be seen as the most basic invariant on the
  file-system state that is enforced by any proper kernel implementation. So
  user processes --- being bound to the system-call interface --- may never
  mess up a file-system such that the root becomes a plain file instead of a
  directory, which would be a strange situation indeed.
\<close>


subsection \<open>Iterated transitions\<close>

text \<open>
  Iterated system transitions via finite sequences of system operations are
  modeled inductively as follows. In a sense, this relation describes the
  cumulative effect of the sequence of system-calls issued by a number of
  running processes over a finite amount of time.
\<close>

inductive transitions :: "file \<Rightarrow> operation list \<Rightarrow> file \<Rightarrow> bool"
    (\<open>(\<open>open_block notation=\<open>mixfix transitions\<close>\<close>_ \<Midarrow>_\<Rightarrow> _)\<close> [90, 1000, 90] 100)
  where
    nil: "root \<Midarrow>[]\<Rightarrow> root"
  | cons: "root \<Midarrow>(x # xs)\<Rightarrow> root''" if "root \<midarrow>x\<rightarrow> root'" and "root' \<Midarrow>xs\<Rightarrow> root''"

text \<open>
  \<^medskip>
  We establish a few basic facts relating iterated transitions with single
  ones, according to the recursive structure of lists.
\<close>

lemma transitions_nil_eq: "root \<Midarrow>[]\<Rightarrow> root' \<longleftrightarrow> root = root'"
proof
  assume "root \<Midarrow>[]\<Rightarrow> root'"
  then show "root = root'" by cases simp_all
next
  assume "root = root'"
  then show "root \<Midarrow>[]\<Rightarrow> root'" by (simp only: transitions.nil)
qed

lemma transitions_cons_eq:
  "root \<Midarrow>(x # xs)\<Rightarrow> root'' \<longleftrightarrow> (\<exists>root'. root \<midarrow>x\<rightarrow> root' \<and> root' \<Midarrow>xs\<Rightarrow> root'')"
proof
  assume "root \<Midarrow>(x # xs)\<Rightarrow> root''"
  then show "\<exists>root'. root \<midarrow>x\<rightarrow> root' \<and> root' \<Midarrow>xs\<Rightarrow> root''"
    by cases auto
next
  assume "\<exists>root'. root \<midarrow>x\<rightarrow> root' \<and> root' \<Midarrow>xs\<Rightarrow> root''"
  then show "root \<Midarrow>(x # xs)\<Rightarrow> root''"
    by (blast intro: transitions.cons)
qed

text \<open>
  The next two rules show how to ``destruct'' known transition sequences. Note
  that the second one actually relies on the uniqueness property of the basic
  transition system (see \secref{sec:unix-single-trans}).
\<close>

lemma transitions_nilD: "root \<Midarrow>[]\<Rightarrow> root' \<Longrightarrow> root' = root"
  by (simp add: transitions_nil_eq)

lemma transitions_consD:
  assumes list: "root \<Midarrow>(x # xs)\<Rightarrow> root''"
    and hd: "root \<midarrow>x\<rightarrow> root'"
  shows "root' \<Midarrow>xs\<Rightarrow> root''"
proof -
  from list obtain r' where r': "root \<midarrow>x\<rightarrow> r'" and root'': "r' \<Midarrow>xs\<Rightarrow> root''"
    by cases simp_all
  from r' hd have "r' = root'" by (rule transition_uniq)
  with root'' show "root' \<Midarrow>xs\<Rightarrow> root''" by simp
qed

text \<open>
  \<^medskip>
  The following fact shows how an invariant \<^term>\<open>Q\<close> of single transitions
  with property \<^term>\<open>P\<close> may be transferred to iterated transitions. The
  proof is rather obvious by rule induction over the definition of
  \<^term>\<open>root \<Midarrow>xs\<Rightarrow> root'\<close>.
\<close>

lemma transitions_invariant:
  assumes r: "\<And>r x r'. r \<midarrow>x\<rightarrow> r' \<Longrightarrow> Q r \<Longrightarrow> P x \<Longrightarrow> Q r'"
    and trans: "root \<Midarrow>xs\<Rightarrow> root'"
  shows "Q root \<Longrightarrow> \<forall>x \<in> set xs. P x \<Longrightarrow> Q root'"
  using trans
proof induct
  case nil
  show ?case by (rule nil.prems)
next
  case (cons root x root' xs root'')
  note P = \<open>\<forall>x \<in> set (x # xs). P x\<close>
  then have "P x" by simp
  with \<open>root \<midarrow>x\<rightarrow> root'\<close> and \<open>Q root\<close> have Q': "Q root'" by (rule r)
  from P have "\<forall>x \<in> set xs. P x" by simp
  with Q' show "Q root''" by (rule cons.hyps)
qed

text \<open>
  As an example of applying the previous result, we transfer the basic
  type-safety property (see \secref{sec:unix-single-trans}) from single
  transitions to iterated ones, which is a rather obvious result indeed.
\<close>

theorem transitions_type_safe:
  assumes "root \<Midarrow>xs\<Rightarrow> root'"
    and "\<exists>att dir. root = Env att dir"
  shows "\<exists>att dir. root' = Env att dir"
  using transition_type_safe and assms
proof (rule transitions_invariant)
  show "\<forall>x \<in> set xs. True" by blast
qed


section \<open>Executable sequences\<close>

text \<open>
  An inductively defined relation such as the one of \<open>root \<midarrow>x\<rightarrow> root'\<close> (see
  \secref{sec:unix-syscall}) has two main aspects. First of all, the resulting
  system admits a certain set of transition rules (introductions) as given in
  the specification. Furthermore, there is an explicit least-fixed-point
  construction involved, which results in induction (and case-analysis) rules
  to eliminate known transitions in an exhaustive manner.

  \<^medskip>
  Subsequently, we explore our transition system in an experimental style,
  mainly using the introduction rules with basic algebraic properties of the
  underlying structures. The technique closely resembles that of Prolog
  combined with functional evaluation in a very simple manner.

  Just as the ``closed-world assumption'' is left implicit in Prolog, we do
  not refer to induction over the whole transition system here. So this is
  still purely positive reasoning about possible executions; exhaustive
  reasoning will be employed only later on (see \secref{sec:unix-bogosity}),
  when we shall demonstrate that certain behavior is \<^emph>\<open>not\<close> possible.
\<close>


subsection \<open>Possible transitions\<close>

text \<open>
  Rather obviously, a list of system operations can be executed within a
  certain state if there is a result state reached by an iterated transition.
\<close>

definition "can_exec root xs \<longleftrightarrow> (\<exists>root'. root \<Midarrow>xs\<Rightarrow> root')"

lemma can_exec_nil: "can_exec root []"
  unfolding can_exec_def by (blast intro: transitions.intros)

lemma can_exec_cons:
    "root \<midarrow>x\<rightarrow> root' \<Longrightarrow> can_exec root' xs \<Longrightarrow> can_exec root (x # xs)"
  unfolding can_exec_def by (blast intro: transitions.intros)

text \<open>
  \<^medskip>
  In case that we already know that a certain sequence can be executed we may
  destruct it backwardly into individual transitions.
\<close>

lemma can_exec_snocD: "can_exec root (xs @ [y])
    \<Longrightarrow> \<exists>root' root''. root \<Midarrow>xs\<Rightarrow> root' \<and> root' \<midarrow>y\<rightarrow> root''"
proof (induct xs arbitrary: root)
  case Nil
  then show ?case
    by (simp add: can_exec_def transitions_nil_eq transitions_cons_eq)
next
  case (Cons x xs)
  from \<open>can_exec root ((x # xs) @ [y])\<close> obtain r root'' where
      x: "root \<midarrow>x\<rightarrow> r" and
      xs_y: "r \<Midarrow>(xs @ [y])\<Rightarrow> root''"
    by (auto simp add: can_exec_def transitions_nil_eq transitions_cons_eq)
  from xs_y Cons.hyps obtain root' r'
    where xs: "r \<Midarrow>xs\<Rightarrow> root'" and y: "root' \<midarrow>y\<rightarrow> r'"
    unfolding can_exec_def by blast
  from x xs have "root \<Midarrow>(x # xs)\<Rightarrow> root'"
    by (rule transitions.cons)
  with y show ?case by blast
qed


subsection \<open>Example executions \label{sec:unix-examples}\<close>

text \<open>
  We are now ready to perform a few experiments within our formal model of
  Unix system-calls. The common technique is to alternate introduction rules
  of the transition system (see \secref{sec:unix-trans}), and steps to solve
  any emerging side conditions using algebraic properties of the underlying
  file-system structures (see \secref{sec:unix-file-system}).
\<close>

lemmas eval = access_def init_def

theorem "u \<in> users \<Longrightarrow> can_exec (init users)
    [Mkdir u perms [u, name]]"
  apply (rule can_exec_cons)
    \<comment> \<open>back-chain \<^term>\<open>can_exec\<close> (of @{term [source] Cons})\<close>
  apply (rule mkdir)
    \<comment> \<open>back-chain \<^term>\<open>Mkdir\<close>\<close>
  apply (force simp add: eval)+
    \<comment> \<open>solve preconditions of \<^term>\<open>Mkdir\<close>\<close>
  apply (simp add: eval)
    \<comment> \<open>peek at resulting dir (optional)\<close>
  txt \<open>@{subgoals [display]}\<close>
  apply (rule can_exec_nil)
    \<comment> \<open>back-chain \<^term>\<open>can_exec\<close> (of @{term [source] Nil})\<close>
  done

text \<open>
  By inspecting the result shown just before the final step above, we may gain
  confidence that our specification of Unix system-calls actually makes sense.
  Further common errors are usually exhibited when preconditions of transition
  rules fail unexpectedly.

  \<^medskip>
  Here are a few further experiments, using the same techniques as before.
\<close>

theorem "u \<in> users \<Longrightarrow> can_exec (init users)
   [Creat u perms [u, name],
    Unlink u [u, name]]"
  apply (rule can_exec_cons)
  apply (rule creat)
  apply (force simp add: eval)+
  apply (simp add: eval)
  apply (rule can_exec_cons)
  apply (rule unlink)
  apply (force simp add: eval)+
  apply (simp add: eval)
  txt \<open>peek at result: @{subgoals [display]}\<close>
  apply (rule can_exec_nil)
  done

theorem "u \<in> users \<Longrightarrow> Writable \<in> perms\<^sub>1 \<Longrightarrow>
  Readable \<in> perms\<^sub>2 \<Longrightarrow> name\<^sub>3 \<noteq> name\<^sub>4 \<Longrightarrow>
  can_exec (init users)
   [Mkdir u perms\<^sub>1 [u, name\<^sub>1],
    Mkdir u' perms\<^sub>2 [u, name\<^sub>1, name\<^sub>2],
    Creat u' perms\<^sub>3 [u, name\<^sub>1, name\<^sub>2, name\<^sub>3],
    Creat u' perms\<^sub>3 [u, name\<^sub>1, name\<^sub>2, name\<^sub>4],
    Readdir u {name\<^sub>3, name\<^sub>4} [u, name\<^sub>1, name\<^sub>2]]"
  apply (rule can_exec_cons, rule transition.intros,
    (force simp add: eval)+, (simp add: eval)?)+
  txt \<open>peek at result: @{subgoals [display]}\<close>
  apply (rule can_exec_nil)
  done

theorem "u \<in> users \<Longrightarrow> Writable \<in> perms\<^sub>1 \<Longrightarrow> Readable \<in> perms\<^sub>3 \<Longrightarrow>
  can_exec (init users)
   [Mkdir u perms\<^sub>1 [u, name\<^sub>1],
    Mkdir u' perms\<^sub>2 [u, name\<^sub>1, name\<^sub>2],
    Creat u' perms\<^sub>3 [u, name\<^sub>1, name\<^sub>2, name\<^sub>3],
    Write u' ''foo'' [u, name\<^sub>1, name\<^sub>2, name\<^sub>3],
    Read u ''foo'' [u, name\<^sub>1, name\<^sub>2, name\<^sub>3]]"
  apply (rule can_exec_cons, rule transition.intros,
    (force simp add: eval)+, (simp add: eval)?)+
  txt \<open>peek at result: @{subgoals [display]}\<close>
  apply (rule can_exec_nil)
  done


section \<open>Odd effects --- treated formally \label{sec:unix-bogosity}\<close>

text \<open>
  We are now ready to give a completely formal treatment of the slightly odd
  situation discussed in the introduction (see \secref{sec:unix-intro}): the
  file-system can easily reach a state where a user is unable to remove his
  very own directory, because it is still populated by items placed there by
  another user in an uncouth manner.
\<close>


subsection \<open>The general procedure \label{sec:unix-inv-procedure}\<close>

text \<open>
  The following theorem expresses the general procedure we are following to
  achieve the main result.
\<close>

theorem general_procedure:
  assumes cannot_y: "\<And>r r'. Q r \<Longrightarrow> r \<midarrow>y\<rightarrow> r' \<Longrightarrow> False"
    and init_inv: "\<And>root. init users \<Midarrow>bs\<Rightarrow> root \<Longrightarrow> Q root"
    and preserve_inv: "\<And>r x r'. r \<midarrow>x\<rightarrow> r' \<Longrightarrow> Q r \<Longrightarrow> P x \<Longrightarrow> Q r'"
    and init_result: "init users \<Midarrow>bs\<Rightarrow> root"
  shows "\<not> (\<exists>xs. (\<forall>x \<in> set xs. P x) \<and> can_exec root (xs @ [y]))"
proof -
  {
    fix xs
    assume Ps: "\<forall>x \<in> set xs. P x"
    assume can_exec: "can_exec root (xs @ [y])"
    then obtain root' root'' where xs: "root \<Midarrow>xs\<Rightarrow> root'" and y: "root' \<midarrow>y\<rightarrow> root''"
      by (blast dest: can_exec_snocD)
    from init_result have "Q root" by (rule init_inv)
    from preserve_inv xs this Ps have "Q root'"
      by (rule transitions_invariant)
    from this y have False by (rule cannot_y)
  }
  then show ?thesis by blast
qed

text \<open>
  Here \<^prop>\<open>P x\<close> refers to the restriction on file-system operations that
  are admitted after having reached the critical configuration; according to
  the problem specification this will become \<^prop>\<open>uid_of x = user\<^sub>1\<close> later
  on. Furthermore, \<^term>\<open>y\<close> refers to the operations we claim to be
  impossible to perform afterwards, we will take \<^term>\<open>Rmdir\<close> later. Moreover
  \<^term>\<open>Q\<close> is a suitable (auxiliary) invariant over the file-system; choosing
  \<^term>\<open>Q\<close> adequately is very important to make the proof work (see
  \secref{sec:unix-inv-lemmas}).
\<close>


subsection \<open>The particular situation\<close>

text \<open>
  We introduce a few global declarations and axioms to describe our particular
  situation considered here. Thus we avoid excessive use of local parameters
  in the subsequent development.
\<close>

context
  fixes users :: "uid set"
    and user\<^sub>1 :: uid
    and user\<^sub>2 :: uid
    and name\<^sub>1 :: name
    and name\<^sub>2 :: name
    and name\<^sub>3 :: name
    and perms\<^sub>1 :: perms
    and perms\<^sub>2 :: perms
  assumes user\<^sub>1_known: "user\<^sub>1 \<in> users"
    and user\<^sub>1_not_root: "user\<^sub>1 \<noteq> 0"
    and users_neq: "user\<^sub>1 \<noteq> user\<^sub>2"
    and perms\<^sub>1_writable: "Writable \<in> perms\<^sub>1"
    and perms\<^sub>2_not_writable: "Writable \<notin> perms\<^sub>2"
  notes facts = user\<^sub>1_known user\<^sub>1_not_root users_neq
    perms\<^sub>1_writable perms\<^sub>2_not_writable
begin

definition
  "bogus =
     [Mkdir user\<^sub>1 perms\<^sub>1 [user\<^sub>1, name\<^sub>1],
      Mkdir user\<^sub>2 perms\<^sub>2 [user\<^sub>1, name\<^sub>1, name\<^sub>2],
      Creat user\<^sub>2 perms\<^sub>2 [user\<^sub>1, name\<^sub>1, name\<^sub>2, name\<^sub>3]]"

definition "bogus_path = [user\<^sub>1, name\<^sub>1, name\<^sub>2]"

text \<open>
  The \<^term>\<open>bogus\<close> operations are the ones that lead into the uncouth
  situation; \<^term>\<open>bogus_path\<close> is the key position within the file-system
  where things go awry.
\<close>


subsection \<open>Invariance lemmas \label{sec:unix-inv-lemmas}\<close>

text \<open>
  The following invariant over the root file-system describes the bogus
  situation in an abstract manner: located at a certain \<^term>\<open>path\<close> within
  the file-system is a non-empty directory that is neither owned nor writable
  by \<^term>\<open>user\<^sub>1\<close>.
\<close>

definition
  "invariant root path \<longleftrightarrow>
    (\<exists>att dir.
      access root path user\<^sub>1 {} = Some (Env att dir) \<and> dir \<noteq> Map.empty \<and>
      user\<^sub>1 \<noteq> owner att \<and>
      access root path user\<^sub>1 {Writable} = None)"

text \<open>
  Following the general procedure (see \secref{sec:unix-inv-procedure}) we
  will now establish the three key lemmas required to yield the final result.

    \<^enum> The invariant is sufficiently strong to entail the pathological case
    that \<^term>\<open>user\<^sub>1\<close> is unable to remove the (owned) directory at
    \<^term>\<open>[user\<^sub>1, name\<^sub>1]\<close>.

    \<^enum> The invariant does hold after having executed the \<^term>\<open>bogus\<close> list of
    operations (starting with an initial file-system configuration).

    \<^enum> The invariant is preserved by any file-system operation performed by
    \<^term>\<open>user\<^sub>1\<close> alone, without any help by other users.

  As the invariant appears both as assumptions and conclusions in the course
  of proof, its formulation is rather critical for the whole development to
  work out properly. In particular, the third step is very sensitive to the
  invariant being either too strong or too weak. Moreover the invariant has to
  be sufficiently abstract, lest the proof become cluttered by confusing
  detail.

  \<^medskip>
  The first two lemmas are technically straight forward --- we just have to
  inspect rather special cases.
\<close>

lemma cannot_rmdir:
  assumes inv: "invariant root bogus_path"
    and rmdir: "root \<midarrow>(Rmdir user\<^sub>1 [user\<^sub>1, name\<^sub>1])\<rightarrow> root'"
  shows False
proof -
  from inv obtain "file" where "access root bogus_path user\<^sub>1 {} = Some file"
    unfolding invariant_def by blast
  moreover
  from rmdir obtain att where "access root [user\<^sub>1, name\<^sub>1] user\<^sub>1 {} = Some (Env att Map.empty)"
    by cases auto
  then have "access root ([user\<^sub>1, name\<^sub>1] @ [name\<^sub>2]) user\<^sub>1 {} = Map.empty name\<^sub>2"
    by (simp only: access_empty_lookup lookup_append_some) simp
  ultimately show False by (simp add: bogus_path_def)
qed

lemma
  assumes init: "init users \<Midarrow>bogus\<Rightarrow> root"
  shows init_invariant: "invariant root bogus_path"
  supply eval = facts access_def init_def
  using init
  apply (unfold bogus_def bogus_path_def)
  apply (drule transitions_consD, rule transition.intros,
      (force simp add: eval)+, (simp add: eval)?)+
    \<comment> \<open>evaluate all operations\<close>
  apply (drule transitions_nilD)
    \<comment> \<open>reach final result\<close>
  apply (simp add: invariant_def eval)
    \<comment> \<open>check the invariant\<close>
  done

text \<open>
  \<^medskip>
  At last we are left with the main effort to show that the ``bogosity''
  invariant is preserved by any file-system operation performed by
  \<^term>\<open>user\<^sub>1\<close> alone. Note that this holds for any \<^term>\<open>path\<close> given,
  the particular \<^term>\<open>bogus_path\<close> is not required here.
\<close>

lemma preserve_invariant:
  assumes tr: "root \<midarrow>x\<rightarrow> root'"
    and inv: "invariant root path"
    and uid: "uid_of x = user\<^sub>1"
  shows "invariant root' path"
proof -
  from inv obtain att dir where
      inv1: "access root path user\<^sub>1 {} = Some (Env att dir)" and
      inv2: "dir \<noteq> Map.empty" and
      inv3: "user\<^sub>1 \<noteq> owner att" and
      inv4: "access root path user\<^sub>1 {Writable} = None"
    by (auto simp add: invariant_def)

  from inv1 have lookup: "lookup root path = Some (Env att dir)"
    by (simp only: access_empty_lookup)

  from inv1 inv3 inv4 and user\<^sub>1_not_root
  have not_writable: "Writable \<notin> others att"
    by (auto simp add: access_def split: option.splits)

  show ?thesis
  proof cases
    assume "root' = root"
    with inv show "invariant root' path" by (simp only:)
  next
    assume changed: "root' \<noteq> root"
    with tr obtain opt where root': "root' = update (path_of x) opt root"
      by cases auto
    show ?thesis
    proof (rule prefix_cases)
      assume "path_of x \<parallel> path"
      with inv root'
      have "\<And>perms. access root' path user\<^sub>1 perms = access root path user\<^sub>1 perms"
        by (simp only: access_update_other)
      with inv show "invariant root' path"
        by (simp only: invariant_def)
    next
      assume "prefix (path_of x) path"
      then obtain ys where path: "path = path_of x @ ys" ..

      show ?thesis
      proof (cases ys)
        assume "ys = []"
        with tr uid inv2 inv3 lookup changed path and user\<^sub>1_not_root
        have False
          by cases (auto simp add: access_empty_lookup dest: access_some_lookup)
        then show ?thesis ..
      next
        fix z zs assume ys: "ys = z # zs"
        have "lookup root' path = lookup root path"
        proof -
          from inv2 lookup path ys
          have look: "lookup root (path_of x @ z # zs) = Some (Env att dir)"
            by (simp only:)
          then obtain att' dir' file' where
              look': "lookup root (path_of x) = Some (Env att' dir')" and
              dir': "dir' z = Some file'" and
              file': "lookup file' zs = Some (Env att dir)"
            by (blast dest: lookup_some_upper)

          from tr uid changed look' dir' obtain att'' where
              look'': "lookup root' (path_of x) = Some (Env att'' dir')"
            by cases (auto simp add: access_empty_lookup lookup_update_some
              dest: access_some_lookup)
          with dir' file' have "lookup root' (path_of x @ z # zs) =
              Some (Env att dir)"
            by (simp add: lookup_append_some)
          with look path ys show ?thesis
            by simp
        qed
        with inv show "invariant root' path"
          by (simp only: invariant_def access_def)
      qed
    next
      assume "strict_prefix path (path_of x)"
      then obtain y ys where path: "path_of x = path @ y # ys" ..

      obtain dir' where
        lookup': "lookup root' path = Some (Env att dir')" and
        inv2': "dir' \<noteq> Map.empty"
      proof (cases ys)
        assume "ys = []"
        with path have parent: "path_of x = path @ [y]" by simp
        with tr uid inv4 changed obtain "file" where
            "root' = update (path_of x) (Some file) root"
          by cases auto
        with lookup parent have "lookup root' path = Some (Env att (dir(y\<mapsto>file)))"
          by (simp only: update_append_some update_cons_nil_env)
        moreover have "dir(y\<mapsto>file) \<noteq> Map.empty" by simp
        ultimately show ?thesis ..
      next
        fix z zs assume ys: "ys = z # zs"
        with lookup root' path
        have "lookup root' path = Some (update (y # ys) opt (Env att dir))"
          by (simp only: update_append_some)
        also obtain file' where
          "update (y # ys) opt (Env att dir) = Env att (dir(y\<mapsto>file'))"
        proof -
          have "dir y \<noteq> None"
          proof -
            have "dir y = lookup (Env att dir) [y]"
              by (simp split: option.splits)
            also from lookup have "\<dots> = lookup root (path @ [y])"
              by (simp only: lookup_append_some)
            also have "\<dots> \<noteq> None"
            proof -
              from ys obtain us u where rev_ys: "ys = us @ [u]"
                by (cases ys rule: rev_cases) simp
              with tr path
              have "lookup root ((path @ [y]) @ (us @ [u])) \<noteq> None \<or>
                  lookup root ((path @ [y]) @ us) \<noteq> None"
                by cases (auto dest: access_some_lookup)
              then show ?thesis
                by (fastforce dest!: lookup_some_append)
            qed
            finally show ?thesis .
          qed
          with ys show ?thesis using that by auto
        qed
        also have "dir(y\<mapsto>file') \<noteq> Map.empty" by simp
        ultimately show ?thesis ..
      qed

      from lookup' have inv1': "access root' path user\<^sub>1 {} = Some (Env att dir')"
        by (simp only: access_empty_lookup)

      from inv3 lookup' and not_writable user\<^sub>1_not_root
      have "access root' path user\<^sub>1 {Writable} = None"
        by (simp add: access_def)
      with inv1' inv2' inv3 show ?thesis unfolding invariant_def by blast
    qed
  qed
qed


subsection \<open>Putting it all together \label{sec:unix-main-result}\<close>

text \<open>
  The main result is now imminent, just by composing the three invariance
  lemmas (see \secref{sec:unix-inv-lemmas}) according the the overall
  procedure (see \secref{sec:unix-inv-procedure}).
\<close>

corollary
  assumes bogus: "init users \<Midarrow>bogus\<Rightarrow> root"
  shows "\<not> (\<exists>xs. (\<forall>x \<in> set xs. uid_of x = user\<^sub>1) \<and>
    can_exec root (xs @ [Rmdir user\<^sub>1 [user\<^sub>1, name\<^sub>1]]))"
proof -
  from cannot_rmdir init_invariant preserve_invariant
    and bogus show ?thesis by (rule general_procedure)
qed

end

end
