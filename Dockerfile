# Docker container to work with Stainless, the verification tool

# COMMANDS:

# BUILD:
## docker build -t stainless:ubuntu22.04 .

# START AND RUN:
## 'docker run --rm -v $PWD:/pwd -d --name stainless -i stainless:ubuntu22.04 && docker exec -it stainless /bin/bash'

FROM ubuntu:22.04

ENV DEBIAN_FRONTEND noninteractive

RUN apt-get update --fix-missing

# Installing basic packages 
RUN apt-get update --fix-missing
RUN apt-get install -y apt
# RUN apt-get install -y software-properties-common  
# RUN add-apt-repository universe 
RUN apt-get install -y zip 
RUN apt-get install -y unzip 
RUN apt-get install -y build-essential 
RUN apt-get install -y jq 
RUN apt-get install -y curl 
RUN apt-get install -y wget 
RUN apt-get install -y rubygems 
RUN apt-get install -y gcc 
RUN apt-get install -y gdb 
RUN apt-get install -y python3.9 
RUN apt-get install -y wget 
RUN apt-get install -y git 
RUN apt-get install -y nano 
RUN apt-get install -y openjdk-17-jdk scala
RUN apt-get install -y  sudo
RUN apt-get install -y net-tools

RUN apt-get install apt-transport-https curl gnupg -yqq
RUN echo "deb https://repo.scala-sbt.org/scalasbt/debian all main" | tee /etc/apt/sources.list.d/sbt.list
RUN echo "deb https://repo.scala-sbt.org/scalasbt/debian /" | tee /etc/apt/sources.list.d/sbt_old.list
RUN curl -sL "https://keyserver.ubuntu.com/pks/lookup?op=get&search=0x2EE0EA64E40A89B84B2DF73499E82A75642AC823" | gpg --no-default-keyring --keyring gnupg-ring:/etc/apt/trusted.gpg.d/scalasbt-release.gpg --import
RUN chmod 644 /etc/apt/trusted.gpg.d/scalasbt-release.gpg
RUN apt-get update --fix-missing
RUN apt-get install sbt

RUN apt-get install -y z3
RUN apt-get install -y cvc4



# Change root's password
RUN echo 'root:stainless' | chpasswd

# Add non-root user
RUN useradd -rm -d /home/sam -s /bin/bash -g root -G sudo -u 1001 sam
RUN echo 'sam:stainless' | chpasswd

USER sam
WORKDIR /home/sam

# Install Stainless from source
RUN git clone https://github.com/epfl-lara/stainless.git

RUN cd stainless && sbt universal:stage

# Update env variables
ENV PATH="/home/sam/stainless/frontends/dotty/target/universal/stage/bin/:${PATH}"
