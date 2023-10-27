#!/bin/bash

echo "SCALA CONFIGURATION"
curl -s "https://get.sdkman.io" | bash
source ~/.bashrc

sdk install java 11.0.11-open
sdk install sbt

echo "CHECKOUT origin/state_initiate"
git checkout origin/state_initiate
echo "RUNNING sbt compile"
sbt compile

echo "DOWNLOAD ISABELLE"
cd ~
wget https://isabelle.in.tum.de/website-Isabelle2020/dist/Isabelle2020_linux.tar.gz
tar -xzf Isabelle2020_linux.tar.gz
alias isabelle=~/Isabelle2020/bin/isabell

echo "DOWNLOAD AND BUILD AFP"
wget https://www.isa-afp.org/release/afp-2021-02-11.tar.gz
tar -xzf afp-2021-02-11.tar.gz
export AFP=afp-2021-02-11/thys
python ./PISA/command_generation/generate_build_commands_afp.py
./PISA/scripts/build_isabelle_afp.sh
