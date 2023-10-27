package pisa.agent

import pisa.utils.TheoryManager

import de.unruh.isabelle.control.Isabelle
import de.unruh.isabelle.control.Isabelle.Setup
import de.unruh.isabelle.mlvalue.MLFunction4
import de.unruh.isabelle.mlvalue.MLValue.{compileFunction, compileFunction0}
import de.unruh.isabelle.mlvalue.AdHocConverter
import de.unruh.isabelle.pure.{Theory, TheoryHeader, ToplevelState}
import de.unruh.isabelle.control.{Isabelle, OperationCollection}
import de.unruh.isabelle.mlvalue.MLValue.compileFunction
import de.unruh.isabelle.pure.{Position, Theory, TheoryHeader}

import java.nio.file.{Path, Paths}

import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._
import scala.concurrent.ExecutionContext.Implicits.global

object Transition extends AdHocConverter("Toplevel.transition")


object RepHammer {
  val isabelleHome: Path = Paths.get("/Applications/Isabelle2022.app")
  val setup: Setup = Setup(isabelleHome = isabelleHome)
  val theoryManager: TheoryManager = new TheoryManager(
    path_to_isa_bin="/Applications/Isabelle2022.app",
    wd="/Applications/Isabelle2022.app/src/HOL"
  )
  def main(args: Array[String]): Unit = {
    implicit val isabelle: Isabelle = new Isabelle(setup)

    val theorySource = TheoryManager.Text(
      """ theory Test imports Main begin lemma test: "1+1=(2::nat)" """,
      Paths.get("Test.thy").toAbsolutePath)

    val thy0 = theoryManager.beginTheory(theorySource)
    val init_toplevel = compileFunction0[ToplevelState]("Toplevel.init_toplevel")
    var toplevel = init_toplevel().force.retrieveNow

    val parse_text = compileFunction[Theory, String, List[(Transition.T, String)]](
      """fn (thy, text) => let
        |  val transitions = Outer_Syntax.parse_text thy (K thy) Position.start text
        |  fun addtext symbols [tr] =
        |        [(tr, implode symbols)]
        |    | addtext _ [] = []
        |    | addtext symbols (tr::nextTr::trs) = let
        |        val (this,rest) = Library.chop (Position.distance_of (Toplevel.pos_of tr, Toplevel.pos_of nextTr) |> Option.valOf) symbols
        |        in (tr, implode this) :: addtext rest (nextTr::trs) end
        |  in addtext (Symbol.explode text) transitions end""".stripMargin)

    val command_exception = compileFunction[Boolean, Transition.T, ToplevelState, ToplevelState](
      "fn (int, tr, st) => Toplevel.command_exception int tr st")

    for ((transition, text) <- parse_text(thy0, theorySource.text).force.retrieveNow) {
      println(s"""Transition: "${text.strip}"""")
      toplevel = command_exception(true, transition, toplevel).retrieveNow.force
    }

    //    val finalThy = toplevel_end_theory(toplevel).retrieveNow.force

    val thy_for_sledgehammer = thy0
    val Sledgehammer: String = thy_for_sledgehammer.importMLStructureNow("Sledgehammer")
    val Sledgehammer_Commands: String = thy_for_sledgehammer.importMLStructureNow("Sledgehammer_Commands")
    val Sledgehammer_Prover: String = thy_for_sledgehammer.importMLStructureNow("Sledgehammer_Prover")

    val normal_with_Sledgehammer: MLFunction4[ToplevelState, Theory, List[String], List[String], (Boolean, (String, List[String]))] =
      compileFunction[ToplevelState, Theory, List[String], List[String], (Boolean, (String, List[String]))](
        s""" fn (state, thy, adds, dels) =>
           |    let
           |       val override = {add=[],del=[],only=false};
           |       fun go_run (state, thy) =
           |          let
           |             val p_state = Toplevel.proof_of state;
           |             val ctxt = Proof.context_of p_state;
           |             val params = ${Sledgehammer_Commands}.default_params thy
           |                [("provers", "e"),("timeout","30"),("verbose","true")];
           |             val results = ${Sledgehammer}.run_sledgehammer params ${Sledgehammer_Prover}.Normal NONE 1 override p_state;
           |             val (result, (outcome, step)) = results;
           |           in
           |             (result, (${Sledgehammer}.short_string_of_sledgehammer_outcome outcome, [YXML.content_of step]))
           |           end;
           |    in
           |      Timeout.apply (Time.fromSeconds 35) go_run (state, thy) end
           |""".stripMargin
      )

    // Apply transitions to toplevel such that it is at a "hammerable" place
    // Then
    val result = normal_with_Sledgehammer(toplevel, thy0, List[String](), List[String]()).force.retrieveNow
    println(result)

  }
}
