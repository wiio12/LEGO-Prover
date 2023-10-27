name := "PISA"

version := "0.1"

scalaVersion := "2.13.4"

val grpcVersion = "1.34.0"

PB.targets in Compile := Seq(
  scalapb.gen(grpc = true) -> (sourceManaged in Compile).value,
  scalapb.zio_grpc.ZioCodeGenerator -> (sourceManaged in Compile).value,
)

libraryDependencies ++= Seq(
  "com.thesamet.scalapb" %% "scalapb-runtime-grpc" % scalapb.compiler.Version.scalapbVersion,
  "io.grpc" % "grpc-netty" % grpcVersion
)
// libraryDependencies += "de.unruh" %% "scala-isabelle" % "master-SNAPSHOT" from "file:/large_experiments/theorem/aqj/third_party_software/Portal-to-ISAbelle/lib/scala-isabelle_2.13.jar"// development snapshot
// libraryDependencies += "de.unruh" %% "scala-isabelle" % "master-SNAPSHOT" from "file:/Users/qj213/Projects/Portal-to-ISAbelle/lib/scala-isabelle_2.13.jar"// development snapshot
libraryDependencies += "de.unruh" %% "scala-isabelle" % "0.4.1"  // release
// libraryDependencies += "de.unruh" %% "scala-isabelle" % "master-SNAPSHOT"
resolvers += Resolver.sonatypeRepo("snapshots")

libraryDependencies += "net.liftweb" %% "lift-json" % "3.4.3"
// https://mvnrepository.com/artifact/org.log4s/log4s
libraryDependencies += "org.log4s" %% "log4s" % "1.10.0"
// https://mvnrepository.com/artifact/org.slf4j/slf4j-simple
libraryDependencies += "org.slf4j" % "slf4j-simple" % "1.7.32"
// https://mvnrepository.com/artifact/commons-io/commons-io
libraryDependencies += "commons-io" % "commons-io" % "2.11.0"
// https://mvnrepository.com/artifact/org.scalaz/scalaz-core
libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.3.5"
// https://mvnrepository.com/artifact/org.apache.commons/commons-lang3
libraryDependencies += "org.apache.commons" % "commons-lang3" % "3.12.0"
// https://mvnrepository.com/artifact/org.apache.commons/commons-text
libraryDependencies += "org.apache.commons" % "commons-text" % "1.9"
// https://mvnrepository.com/artifact/com.google.guava/guava
libraryDependencies += "com.google.guava" % "guava" % "31.0.1-jre"
libraryDependencies += "org.jetbrains" % "annotations" % "23.0.0"
libraryDependencies += "com.ibm.icu" % "icu4j" % "70.1"

assemblyMergeStrategy in assembly := {
    case x if x.contains("de/unruh") => MergeStrategy.first
    case PathList("META-INF", "MANIFEST.MF") => MergeStrategy.discard
    case x if x.contains("META-INF") => MergeStrategy.first
    case x =>
        val oldStrategy = (assemblyMergeStrategy in assembly).value
        oldStrategy(x)
}
