package pisa

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.pure.Theory

import java.nio.file.Path
import scala.concurrent.ExecutionContext

object Easy {
  implicit val ec: ExecutionContext = ExecutionContext.global
  val path_to_isa_bin: String = "/Applications/Isabelle2020.app/Isabelle"
  val setup: Isabelle.Setup = Isabelle.Setup(
    isabelleHome = Path.of(path_to_isa_bin),
    sessionRoots = Seq(Path.of("/Users/qj213/Projects/afp-2021-02-11/thys")),
    userDir = None,
    logic = "Functional-Automata",
    workingDirectory = Path.of("/Users/qj213/Projects/afp-2021-02-11/thys"),
    build = false
  )
  implicit val isabelle: Isabelle = new Isabelle(setup)

  def main(args: Array[String]): Unit = {
    //    Theory("Functional-Automata.RegExp2NA").force.await
    Theory("Abstract-Rewriting.Seq").force.await
  }
}
