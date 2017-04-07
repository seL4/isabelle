object profile extends isabelle.CI_Profile
{

  import isabelle._

  def threads = 2
  def jobs = 3
  def include = Nil
  def select = Nil

  def pre_hook(args: List[String]) = {}
  def post_hook(results: Build.Results) = {}

  def selection = Sessions.Selection(all_sessions = true)

}
