package pisa.agent

import net.liftweb.json.{DefaultFormats, parse}
import pisa.server.PisaOS

import java.io.PrintWriter
import scala.io.Source

object PisaStat {
  implicit val formats: DefaultFormats = DefaultFormats

  def main(args: Array[String]): Unit = {
    val test_theorem_number: String = args(0).split('/').last.split('.').head.split('_').last
    val dump_path: String = "results/pisa_stat"
    val json_element = parse(
      {
        val textSource = Source.fromFile(args(0))
        val str = textSource.mkString
        textSource.close()
        str
      }
    ).children.head
    val theory_path = json_element(0).extract[String].replaceAll("/home/ywu/afp-2021-02-11", "/home/qj213/afp-2021-10-22")
    val thys_index = theory_path.split("/").indexOf("thys")
    val working_directory = {
      if (theory_path.contains("miniF2F")) "/home/qj213/afp-2021-10-22/thys/Symmetric_Polynomials"
      else theory_path.split("/").take(thys_index + 2).mkString("/")
    }
    val theorem_name = json_element(1).extract[String].replaceAll("\n", " ").replaceAll(" +", " ").trim
    val starting_point = System.nanoTime
    val pisaos = new PisaOS(
      path_to_isa_bin = "/home/qj213/Isabelle2021",
      path_to_file = theory_path,
      working_directory = working_directory
    )
    val load_timestamp = System.nanoTime
    val load_library_time = (load_timestamp - starting_point) / 1e9d
    pisaos.step_to_transition_text(theorem_name)
    val proceed_to_line_time = (System.nanoTime - load_timestamp) / 1e9d

    new PrintWriter(s"$dump_path/$test_theorem_number" + "_time.info") {
      write(s"load_library_time: $load_library_time\nproceed_to_line_time: $proceed_to_line_time")
      close()
    }
  }
}
