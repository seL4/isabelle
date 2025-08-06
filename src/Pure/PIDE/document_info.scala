/*  Title:      Pure/PIDE/document_info.scala
    Author:     Makarius

Persistent document information --- for presentation purposes.
*/

package isabelle


object Document_Info {
  sealed case class Session(
    name: String,
    used_theories: List[String],
    loaded_theories: Map[String, Theory],
    build_uuid: String
  ) {
    if (build_uuid.isEmpty) error("Missing build_uuid for session " + quote(name))
  }

  object Theory {
    def apply(
      name: String,
      files: List[String],
      static_session: String,
      dynamic_session: String,
      entities: List[Export_Theory.Entity0],
      others: List[String]
    ): Theory = {
      val entities1 =
        entities.filter(e => e.file.nonEmpty && Position.Range.unapply(e.pos).isDefined)
      new Theory(name, files, static_session, dynamic_session, entities1, others)
    }
  }

  class Theory private(
    val name: String,
    val files: List[String],
    val static_session: String,
    val dynamic_session: String,
    entities: List[Export_Theory.Entity0],
    others: List[String]
  ) {
    override def toString: String = name

    val (thy_file, blobs_files) =
      files match {
        case Nil => error("Unknown theory file for " + quote(name))
        case a :: bs =>
          def for_theory: String = " for theory " + quote(name)
          if (!File.is_thy(a)) error("Bad .thy file " + quote(a) + for_theory)
          for (b <- bs if File.is_thy(b)) error("Bad auxiliary file " + quote(b) + for_theory)
          (a, bs)
      }

    def home_session: Boolean = static_session == dynamic_session

    def print_short: String =
      if (home_session) Long_Name.base_name(name) else name

    def print_long: String =
      "theory " + quote(name) +
      (if (home_session) "" else " (session " + quote(dynamic_session) + ")")

    private lazy val by_file_range: Map[(String, Symbol.Range), List[Export_Theory.Entity0]] =
      entities.groupBy(entity => (entity.file, entity.range))

    private lazy val by_file_kname: Map[(String, String), Export_Theory.Entity0] =
      (for {
        entity <- entities
        file <- Position.File.unapply(entity.pos)
      } yield (file, entity.kname) -> entity).toMap

    def get_defs(file: String, range: Symbol.Range): List[Export_Theory.Entity0] =
      by_file_range.getOrElse((file, range), Nil)

    def get_def(file: String, kind: String, name: String): Option[Export_Theory.Entity0] =
      by_file_kname.get((file, Export_Theory.export_kind_name(kind, name)))

    def elements(elements: Browser_Info.Elements): Browser_Info.Elements =
      elements.copy(entity = others.foldLeft(elements.entity)(_ + _))
  }

  val empty: Document_Info = new Document_Info(Map.empty)

  def read(
    database_context: Export.Database_Context,
    deps: Sessions.Deps,
    sessions: List[String]
  ): Document_Info = {
    val sessions_structure = deps.sessions_structure
    val sessions_requirements = sessions_structure.build_requirements(sessions)

    def read_theory(theory_context: Export.Theory_Context): Option[Document_Info.Theory] =
    {
      val session_name = theory_context.session_context.session_name
      val theory_name = theory_context.theory

      theory_context.files0(permissive = true) match {
        case Nil => None
        case files =>
          val theory_export = Export_Theory.read_theory(theory_context, permissive = true)
          val theory =
            Theory(theory_name,
              static_session = sessions_structure.theory_qualifier(theory_name),
              dynamic_session = session_name,
              files = files.map(_._2),
              entities = theory_export.entity_iterator.toList,
              others = theory_export.others.keySet.toList)
          Some(theory)
      }
    }

    def read_session(session_name: String): Document_Info.Session = {
      val static_theories = deps(session_name).used_theories.map(_._1.theory)
      val (thys, build_uuid) = {
        using(database_context.open_session(deps.background(session_name))) { session_context =>
          val thys =
            for {
              theory_name <- static_theories
              theory <- read_theory(session_context.theory(theory_name))
            } yield theory_name -> theory
          val build_uuid =
            (for {
              db <- session_context.session_db(session_name)
              build <- database_context.store.read_build(db, session_name)
            } yield build.uuid).getOrElse("")
          (thys, build_uuid)
        }
      }
      val loaded_theories0 = thys.toMap
      val used_theories = static_theories.filter(loaded_theories0.keySet)
      Session(session_name, used_theories, loaded_theories0, build_uuid)
    }

    val result0 =
      (for (session <- Par_List.map(read_session, sessions_requirements).iterator)
        yield session.name -> session).toMap

    val result1 =
      sessions_requirements.foldLeft(Map.empty[String, Session]) {
        case (seen, session_name) =>
          val session0 = result0(session_name)
          val loaded_theories1 =
            sessions_structure(session_name).parent.map(seen) match {
              case None => session0.loaded_theories
              case Some(parent_session) =>
                parent_session.loaded_theories ++ session0.loaded_theories
            }
          val session1 = session0.copy(loaded_theories = loaded_theories1)
          seen + (session_name -> session1)
      }

    new Document_Info(result1)
  }
}

class Document_Info private(sessions: Map[String, Document_Info.Session]) {
  override def toString: String =
    sessions.keysIterator.toList.sorted.mkString("Document_Info(", ", ", ")")

  def the_session(session: String): Document_Info.Session =
    sessions.getOrElse(session,
      error("Unknown document information for session: " + quote(session)))

  def theory_by_name(session: String, theory: String): Option[Document_Info.Theory] =
    by_session_and_theory_name.get((session, theory))

  def theory_by_file(session: String, file: String): Option[Document_Info.Theory] =
    by_session_and_theory_file.get((session, file))

  private lazy val by_session_and_theory_name: Map[(String, String), Document_Info.Theory] =
    (for {
      session <- sessions.valuesIterator
      theory <- session.loaded_theories.valuesIterator
    } yield (session.name, theory.name) -> theory).toMap

  private lazy val by_session_and_theory_file: Map[(String, String), Document_Info.Theory] = {
    (for {
      session <- sessions.valuesIterator
      theory <- session.loaded_theories.valuesIterator
      file <- theory.files.iterator
    } yield (session.name, file) -> theory).toMap
  }
}
