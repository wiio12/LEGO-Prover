package pisa

import de.unruh.isabelle.control.Isabelle

import java.nio.file.Path

object TestIsa {
  val setup: Isabelle.Setup = Isabelle.Setup(isabelleHome = Path.of("/Applications/Isabelle2020.app/Isabelle"),
    sessionRoots = Nil,
    userDir = None,
    logic = "HOL",
    workingDirectory = Path.of("./"),
    build = false
  )

  implicit val isabelle: Isabelle = new Isabelle(setup)

  println("Initialised isabelle")


  def main(args: Array[String]): Unit = {
    Thread.sleep(10000)
    isabelle.destroy()
    println("Destroyed isabelle")
    Thread.sleep(100000)
  }
}
