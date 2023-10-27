# Update and install zip
sudo apt-get update
sudo apt-get install zip
# Set up sdk
curl -s "https://get.sdkman.io" | bash
source "/home/qj213/.sdkman/bin/sdkman-init.sh"
source .bashrc
source .zshrc
# Install java and sbt
sdk install java 11.0.11-open
sdk install sbt
# Decompress and compile
(cd Portal-to-ISAbelle; tar -zxf universal_test_theorems.tar.gz; sbt compile)
cd ~
# Install Isabelle
wget https://isabelle.in.tum.de/website-Isabelle2021/dist/Isabelle2021_linux.tar.gz
tar -xzf Isabelle2021_linux.tar.gz
# Get afp
wget https://www.isa-afp.org/release/afp-2021-10-22.tar.gz
tar -xzf afp-2021-10-22.tar.gz
# Get heaps
wget https://storage.googleapis.com/n2formal-public-data/isabelle_heaps.tar.gz
tar -xzf isabelle_heaps.tar.gz
# Clean up
rm *.tar.gz
