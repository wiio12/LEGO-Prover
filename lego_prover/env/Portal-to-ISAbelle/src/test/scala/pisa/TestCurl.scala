package pisa

import net.liftweb.json._

import scala.collection.mutable.ListBuffer
import scala.sys.process._
import scala.io.Source

case class GetText(text: String)

object TestCurl {
  implicit val formats : DefaultFormats = DefaultFormats
  def preprocess(cmd : String, state_only : Boolean): String = {
    if (state_only) {
      cmd.trim.replace("State:", "[IS] GOAL").replace("\\", "\\\\").replace("\n", "\\n")
        .replace("\"", "\\\"").replace("\'", "\\u0027")
    } else {
      cmd.replace("Proof:", "[IS] PROOF").replace("State:", "[IS] GOAL").replace("\\", "\\\\")
      .replace("\n", "\\n").replace("\"", "\\\"").replace("\'", "\\u0027")
    }
  }

  def main(args: Array[String]): Unit = {
    val state_only : Boolean = {
      if (args(0).startsWith("state")) true
      else false
    }

    val path_to_dir : String = {
      if (state_only) "pisa_seq2seq/state_only"
      else "pisa_seq2seq/proof_and_state"
    }
    val preceding_line : String = {
      if (state_only) "curl https://api.openai.com/v1/engines/formal-small-isabelle-v6-c4/completions -H 'Content-Type: application/json' -H 'Authorization: Bearer <OPENAI_TOKEN>' -d '{\"prompt\": \""
      else "curl https://api.openai.com/v1/engines/formal-small-isabelle-wproof-v1-c4/completions -H 'Content-Type: application/json' -H 'Authorization: Bearer <OPENAI_TOKEN>' -d '{\"prompt\": \""
    }
    val final_line = " PROOFSTEP\", \"best_of\": 1, \"temperature\": 0.1, \"max_tokens\": 128, \"n\": 1}'"

    val src_name : String = path_to_dir + "/" + "val.src"
    val tgt_name : String = path_to_dir + "/" + "val.tgt"

    val src_open = Source.fromFile(src_name)
    val src_list : List[String] = src_open.getLines.toList
    src_open.close
    val tgt_open = Source.fromFile(tgt_name)
    val tgt_list : List[String] = tgt_open.getLines.toList
    tgt_open.close

    var src2tgt : Map[String, ListBuffer[String]] = Map()
    for (i <- List.range(0, src_list.length)) {
      val src : String = src_list(i)
      if (src2tgt.contains(src)) {
        var tgt_old_list : ListBuffer[String] = src2tgt(src)
        tgt_old_list += tgt_list(i)
        src2tgt += (src -> tgt_old_list)
      } else {
        src2tgt += (src_list(i) -> ListBuffer(tgt_list(i)))
      }
    }

    val src_keys = src2tgt.keys.toList.take(1000)

    var correct = 0
    for (key <- src_keys) {
      val test_value = src2tgt(key)
      val test_str = preceding_line + preprocess(key, state_only) + final_line
//      println(test_str)

      val returned_str = test_str.!!
      if (returned_str.contains("error")) {}
      else {
        val parsed_value = (parse(returned_str) \ "choices")(0).extract[GetText].text.trim

        if (test_value.contains(parsed_value)) {
          correct += 1
        }
      }
    }
    println(correct/1000.0)

  }
}
