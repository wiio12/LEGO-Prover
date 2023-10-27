sbt "runMain pisa.server.PisaOneStageServer8000" &
PIDmain=$!
sleep 12
python src/main/python/extract_and_load_problems.py --json-path first_stage_output/Functional-Automata/Automata.json --isa-path /home/ywu/Isabelle2020 --afp /home/ywu/afp-2021-02-11 --saving-directory second_stage_output &
PID0=$!
python src/main/python/extract_and_load_problems.py --json-path first_stage_output/Functional-Automata/MaxChop.json --isa-path /home/ywu/Isabelle2020 --afp /home/ywu/afp-2021-02-11 --saving-directory second_stage_output &
PID1=$!
python src/main/python/extract_and_load_problems.py --json-path first_stage_output/Functional-Automata/DA.json --isa-path /home/ywu/Isabelle2020 --afp /home/ywu/afp-2021-02-11 --saving-directory second_stage_output &
PID2=$!
python src/main/python/extract_and_load_problems.py --json-path first_stage_output/Functional-Automata/RegExp2NA.json --isa-path /home/ywu/Isabelle2020 --afp /home/ywu/afp-2021-02-11 --saving-directory second_stage_output &
PID3=$!
wait $PID0
wait $PID1
wait $PID2
wait $PID3
ps aux |grep scala |awk '{print $2}' |xargs kill
ps aux |grep java |awk '{print $2}' |xargs kill
ps aux |grep poly |awk '{print $2}' |xargs kill
ps aux | grep "bash sbt" | awk '{print $2}' | xargs kill
