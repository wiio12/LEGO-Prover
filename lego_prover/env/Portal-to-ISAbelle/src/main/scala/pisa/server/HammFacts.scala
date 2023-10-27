package pisa.server

import pisa.server.PisaOS
import pisa.server.Pretty
import de.unruh.isabelle.mlvalue.{AdHocConverter, MLFunction}
import de.unruh.isabelle.pure.{Context, ToplevelState}
import de.unruh.isabelle.mlvalue.MLValue.compileFunction
import de.unruh.isabelle.mlvalue.Implicits._
import de.unruh.isabelle.pure.Implicits._


object HammFacts {
  val path_to_isa_bin: String = "/home/qj213/Isabelle2021"
  val path_to_afp: String = "/home/qj213/afp-2021-10-22"
  val path_to_file : String = s"$path_to_afp/thys/Functional-Automata/NA.thy"
  val working_directory : String = s"$path_to_afp/thys/Functional-Automata"
  val theorem_name = "lemma accepts_conv_steps: \"accepts A w = (\\<exists>q. (start A,q) \\<in> steps A w \\<and> fin A q)\""
  def main(args: Array[String]): Unit = {
    val pisaos = new PisaOS(
      path_to_isa_bin = path_to_isa_bin,
      path_to_file = path_to_file,
      working_directory = working_directory
    )
      
    val parsed : String = pisaos.step_to_transition_text(theorem_name)
    println(parsed)
    implicit val isabelle = pisaos.isabelle
    implicit val ec = pisaos.ec

    // val facts_of : MLFunction[ToplevelState, List[String]] = compileFunction[ToplevelState, List[String]](
    // """fn tls => map Pretty.unformatted_string_of (let
    //   |    val ctxt = (Toplevel.context_of tls);
    //   |    val facts = Proof_Context.facts_of ctxt;
    //   |    val props = map #1 (Facts.props facts);
    //   |    val true_global_facts =
    //   |      (if null props then [] else [("<unnamed>", props)]) @
    //   |      Facts.dest_static false [Global_Theory.facts_of (Proof_Context.theory_of ctxt)] facts;
    //   |  in
    //   |    if null true_global_facts then []
    //   |    else
    //   |      [Pretty.big_list "true_global facts:"
    //   |        (map #1 (sort_by (#1 o #2) (map (`(Proof_Context.pretty_fact ctxt)) true_global_facts)))]
    //   |  end)""".stripMargin
    // )
    // for (fact <- facts_of(pisaos.toplevel).force.retrieveNow) {
    //     println(fact)
    // }
    // val all_theorems_of : MLFunction[ToplevelState, List[(String, String)]] = compileFunction[ToplevelState, List[(String, String)]](
    //     g
    // )
    // val local_theorems : MLFunction[ToplevelState, List[String]] = compileFunction[ToplevelState, List[String]](
    //     """fn tls => map Pretty.unformatted_string_of (Proof_Context.pretty_local_facts false (Toplevel.context_of tls))"""
    // )
    // val theorems = all_theorems_of(pisaos.toplevel).force.retrieveNow
    // println(theorems.length)
    // val local_ts = local_theorems(pisaos.toplevel).force.retrieveNow
    // println(local_ts.length)
    // for (thm <- theorems.take(5)) {
    //     println(thm)
    // }
    // println(pisaos.total_facts(pisaos.toplevel).length())
  }
}