package pisa.agent

import de.unruh.isabelle.control.{Isabelle, IsabelleMLException}
import de.unruh.isabelle.mlvalue.MLFunction2
import de.unruh.isabelle.pure.{Theory, ToplevelState}
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._
import pisa.server.{PisaOS, Transition}

import _root_.java.nio.file.{Files, Path}
import java.io.PrintWriter
import scala.collection.mutable.ListBuffer
import scala.concurrent.ExecutionContext
import scala.concurrent._
import scala.concurrent.duration._

class CheckSyntax(path_to_isa_bin: String, path_to_file: String, working_directory: String) {
  def divide_by_theorem(total_string: String): (String, List[String]) = {
    val keyword = "theorem"
    val split_theorems = total_string.split(keyword)
    split_theorems.foreach(println)
    val header = split_theorems.head
    (header, split_theorems.drop(1).map(x => keyword + x).toList)
  }

  def try_to_parse_theorem(theorem_string: String): Boolean = {
    var trial_state = pisaos.copy_tls.retrieveNow
    try {
      for ((transition, text) <- parse_text(thy, theorem_string).force.retrieveNow) {
        if (text.trim.isEmpty) {}
        else {
          println(text)
          trial_state = step(text, trial_state)
        }
      }
      true
    } catch {
      case e: Throwable =>
        println(e); false
    }
  }

  // def try_to_parse_theorem_with_hammer(theorem_string: String): (Boolean, String) = {
  //   var trial_state = pisaos.copy_tls.retrieveNow
  //   var stateActionTotal: String = ""
  //   var current_state_string: String = pisaos.getStateString(trial_state)
  //   var current_proof_level: Int = pisaos.getProofLevel(trial_state)
  //   try {
  //     for ((_, text) <- parse_text(thy, theorem_string).force.retrieveNow) {
  //       if (text.trim.isEmpty) {}
  //       else if (text.trim == "sledgehammer") {
  //         val hammer_results = pisaos.normal_with_hammer(trial_state, List[String](), List[String](), 60000)
  //         val hammered_string = {
  //           if (hammer_results._1) {
  //             val hammer_strings = hammer_results._2
  //             var found = false
  //             var real_string = ""
  //             for (attempt_string <- hammer_strings) {
  //               if (!found && (attempt_string contains "Try this:")) {
  //                 found = true
  //                 real_string = attempt_string.trim.stripPrefix("Try this:").trim.split('(').dropRight(1).mkString("(")
  //               }
  //             }
  //             if (found) real_string
  //             else throw new IsabelleMLException
  //           } else {
  //             throw IsabelleMLException
  //           }
  //         }.trim
  //         trial_state = step(hammered_string, trial_state, 20000)
  //         stateActionTotal = stateActionTotal + (current_state_string + "<\\STATESEP>" + hammered_string.trim + "<\\STATESEP>" + s"$current_proof_level" + "<\\TRANSEP>")
  //         current_state_string = pisaos.getStateString(trial_state)
  //         current_proof_level = pisaos.getProofLevel(trial_state)
  //       } else {
  //         trial_state = step(text, trial_state)
  //         stateActionTotal = stateActionTotal + (current_state_string + "<\\STATESEP>" + text.trim + "<\\STATESEP>" + s"$current_proof_level" + "<\\TRANSEP>")
  //         current_state_string = pisaos.getStateString(trial_state)
  //         current_proof_level = pisaos.getProofLevel(trial_state)
  //       }
  //     }
  //     (true, stateActionTotal)
  //   } catch {
  //     case e: Throwable => (false, "")
  //   }
  // }

  def try_to_drive_contradictions_from_theorem(theorem_string: String): Boolean = {
    val theorem_lines = theorem_string.split("\n")
    val theorem_decl = theorem_lines.head
    //  Find where the keyword "shows" starts in theorem_decl
    val show_start = theorem_decl.indexOf("shows")
    if (show_start == -1) false
    else if (theorem_string.contains("sos")) false
    else {
      val modified_theorem_decl = theorem_decl.substring(0, show_start) + """shows "False""""
      val modified_theorem_string = modified_theorem_decl + "\n" + theorem_lines.drop(1).mkString("\n")
      try_to_parse_theorem(modified_theorem_string)
    }
  }

  def get_all_parsable_theorems(list_of_theorem_strings: List[String]): List[String] = {
    list_of_theorem_strings.filter(x => try_to_parse_theorem(x))
  }

  def get_all_parsable_theorems : List[String] = get_all_parsable_theorems(individual_theorem_strings)

  // def get_all_parsable_hammer_theorems(list_of_theorem_strings: List[String]): String = {
  //   val list_of_theorem_strings_parsed: List[(Boolean, String)] = list_of_theorem_strings.map(try_to_parse_theorem_with_hammer)
  //   val parsable_strings: List[String] = list_of_theorem_strings_parsed.filter(x => x._1).map(x => x._2)
  //   parsable_strings.mkString
  // }

  // def get_all_parsable_hammer_theorems: String = get_all_parsable_hammer_theorems(individual_theorem_strings)

  def get_all_contradictions(list_of_theorem_strings: List[String]): List[String] = {
    list_of_theorem_strings.filter(x => try_to_drive_contradictions_from_theorem(x))
  }

  def get_all_contradictions: List[String] = get_all_contradictions(individual_theorem_strings)

  def step(isar_string: String, top_level_state: ToplevelState, timeout_in_millis: Int = 10000): ToplevelState = {
    pisaos.step(isar_string, top_level_state, timeout_in_millis)
  }

  // Load PisaOS and useful methods and attributes
  val pisaos = new PisaOS(path_to_isa_bin = path_to_isa_bin, path_to_file = path_to_file, working_directory = working_directory)
  implicit val isabelle: Isabelle = pisaos.isabelle
  implicit val ec: ExecutionContext = pisaos.ec
  val thy: Theory = pisaos.thy1
  val parse_text: MLFunction2[Theory, String, List[(Transition.T, String)]] = pisaos.parse_text
  val top_level_state: ToplevelState = pisaos.toplevel
  // Names of all the parsable theorems
  var parsable_theorem_names: ListBuffer[String] = ListBuffer[String]()
  // String of the entire file
  val file_string: String = Files.readString(Path.of(path_to_file))
  val (header: String, individual_theorem_strings: List[String]) = divide_by_theorem(file_string)
  pisaos.step(header)


  // Some constants
  val header_script: String = """(*
                        |  Authors: Codex from Lean
                        |*)
                        |
                        |theory miniF2F_correct
                        |  imports
                        |  HOL.HOL
                        |  Complex_Main
                        |  "HOL-Library.Code_Target_Numeral"
                        |  "HOL-Library.Sum_of_Squares"
                        |  "Symmetric_Polynomials.Vieta"
                        |  "HOL-Computational_Algebra.Computational_Algebra"
                        |  "HOL-Number_Theory.Number_Theory"
                        |begin
                        |""".stripMargin
  val ending_script: String = """
                                |end
                                |""".stripMargin
}

object CheckSyntax {
  def main(args: Array[String]): Unit = {
    val theory_path: String = args(0).trim
    val dump_path: String = args(1).trim
    val syntax_checker: CheckSyntax = new CheckSyntax(
      path_to_isa_bin = "/home/qj213/Isabelle2021",
      path_to_file = theory_path,
      working_directory = "/home/qj213/afp-2021-10-22/thys/Symmetric_Polynomials"
    )

    new PrintWriter("syntax_correct_theorem_names") {
      for (str <- syntax_checker.get_all_parsable_theorems) {
        write(str.replaceAll("\n", " ").replaceAll(" +", " ").trim)
        write("\n")
      }
      close()
    }

    for ((theorem_full, i) <- syntax_checker.get_all_parsable_theorems.zipWithIndex) {
      val theorem_name: String = theorem_full.split(":").head.split(" ")(1)
      val theorem_decl: String = theorem_full.trim.split("\n").dropRight(1).mkString.replaceAll(" +", " ")
      val theory_path = dump_path + s"/$theorem_name.thy"
      new PrintWriter(theory_path) {
        write(s"""(*
                |  Authors: Codex from Lean
                |*)
                |
                |theory $theorem_name
                |  imports
                |  HOL.HOL
                |  Complex_Main
                |  "HOL-Library.Code_Target_Numeral"
                |  "HOL-Library.Sum_of_Squares"
                |  "Symmetric_Polynomials.Vieta"
                |  "HOL-Computational_Algebra.Computational_Algebra"
                |  "HOL-Number_Theory.Number_Theory"
                |begin
                |""".stripMargin)
        write(theorem_full)
        write("""
              |end
              |""".stripMargin)
        close()
      }

      new PrintWriter(dump_path + s"/test_name_$i") {
        write(theory_path)
        write("\n")
        write(theorem_decl)
        close()
      }
    }


//    new PrintWriter(dump_path) {
//      write(syntax_checker.header_script)
//      for (theorem_decl <- syntax_checker.get_all_parsable_theorems) {
//        write(theorem_decl)
//      }
//      write(syntax_checker.ending_script)
//      close()
//    }
  }
}

// object ParseWithHammer {
//   def main(args: Array[String]): Unit = {
//     val theory_path: String = args(0).trim
//     val dump_path: String = args(1).trim
//     val syntax_checker: CheckSyntax = new CheckSyntax(
//       path_to_isa_bin = "/home/qj213/Isabelle2021",
//       path_to_file = theory_path,
//       working_directory = "/home/qj213/afp-2021-10-22/thys/Symmetric_Polynomials"
//     )
//     new PrintWriter(dump_path) {
//       write(syntax_checker.get_all_parsable_hammer_theorems)
//       close()
//     }
//   }
// }


object DriveContradictions {
  def main(args: Array[String]) : Unit = {
    val theory_path: String = args(0).trim
    val dump_path: String = args(1).trim
    val syntax_checker: CheckSyntax = new CheckSyntax(
      path_to_isa_bin = "/home/qj213/Isabelle2021",
      path_to_file = theory_path,
      working_directory = "/home/qj213/afp-2021-10-22/thys/Symmetric_Polynomials"
    )
    new PrintWriter(dump_path) {
      write(syntax_checker.get_all_contradictions.mkString("\n"))
      close()
    }
  }
}
