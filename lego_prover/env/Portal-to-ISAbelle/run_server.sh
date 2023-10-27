
export PATH="$HOME/Isabelle2022/bin:$PATH"
echo "running PisaOneStageServer$1"
java -Xms1024m -Xmx1024m -Xss4M -XX:ReservedCodeCacheSize=128m -cp PISA-assembly-0.1.jar pisa.server.PisaOneStageServer$1