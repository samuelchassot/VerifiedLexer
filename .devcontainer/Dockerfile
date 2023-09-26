# To build the image: docker build -t stainless_sam:ubuntu23.10 .

# To run the image to test locally: docker run --rm -v .:/pwd -d --name stainless_sam -i stainless_sam:ubuntu23.10 && docker exec -it stainless_sam /bin/bash

FROM ubuntu:23.10


ENV DEBIAN_FRONTEND noninteractive

SHELL ["/bin/bash", "-c"]

RUN apt-get update --fix-missing
RUN apt-get install -y apt

RUN apt-get install -y zip 
RUN apt-get install -y unzip 
RUN apt-get install -y build-essential 
RUN apt-get install -y python3.11
RUN apt-get install -y curl
RUN apt-get install -y wget 
RUN apt-get install -y git 
RUN apt-get install -y nano 
RUN apt-get install -y sudo
RUN apt-get install -y net-tools
RUN apt-get install -y python3 python3-pip
RUN apt-get install -y jq 
RUN apt-get install -y gcc 
RUN apt-get install -y gdb 
RUN apt-get update --fix-missing
RUN apt-get install -y ssh


RUN apt-get install -y z3
RUN apt-get install -y cvc4

ENV SDKMAN_DIR /tools/.sdkman
ENV SCALA_VERSION 3.3.0 
ENV JAVA_VERSION 17-open
ENV SBT_VERSION 1.9.1


RUN mkdir /tools
RUN chmod -R 775 /tools

RUN curl -s "https://get.sdkman.io" | bash

RUN source "$SDKMAN_DIR/bin/sdkman-init.sh"

RUN bash -c "source $SDKMAN_DIR/bin/sdkman-init.sh && \
    yes | sdk install java $JAVA_VERSION && \
    yes | sdk install scala $SCALA_VERSION && \
    yes | sdk install sbt $SBT_VERSION && \
    rm -rf $SDKMAN_DIR/.sdkman/archives/* && \
    rm -rf $SDKMAN_DIR/.sdkman/tmp/*"

RUN source "$SDKMAN_DIR/bin/sdkman-init.sh"

RUN pip3 install shutils==0.1.0 --break-system-packages

RUN cd /tools && git clone https://github.com/epfl-lara/stainless.git
RUN cd /tools/stainless && source "$SDKMAN_DIR/bin/sdkman-init.sh" && sbt universal:stage

ENV PATH="/tools/stainless/frontends/dotty/target/universal/stage/bin:${PATH}"
ENV PATH="/tools/stainless/frontends/scalac/target/universal/stage/bin:${PATH}"
