FROM debian:stretch AS builder

## ensure locale is set during build
ENV LANG C.UTF-8

RUN apt-get update
RUN apt-get install -y --no-install-recommends gnupg ca-certificates dirmngr curl git
RUN echo 'deb http://downloads.haskell.org/debian stretch main' > /etc/apt/sources.list.d/ghc.list
RUN apt-key adv --keyserver keyserver.ubuntu.com --recv-keys BA3CBA3FFE22B574
RUN apt-get update
RUN apt-get install -y --no-install-recommends zlib1g-dev libtinfo-dev libsqlite3-dev \
    g++ netbase xz-utils libgmp-dev make

ENV STACK_VERSION=2.7.5
RUN curl -fSL https://github.com/commercialhaskell/stack/releases/download/v${STACK_VERSION}/stack-${STACK_VERSION}-linux-x86_64.tar.gz -o stack.tar.gz
RUN tar -xf stack.tar.gz -C /usr/local/bin --strip-components=1

## stack installed binaries are placed here
ENV PATH /root/.local/bin:$PATH

RUN mkdir -p /opt/boxprover
COPY boxprover.cabal /opt/boxprover/
COPY stack.yaml /opt/boxprover/

WORKDIR /opt/boxprover
RUN stack setup
RUN stack install --only-dependencies --no-interleaved-output

COPY LICENSE /opt/boxprover/
COPY src /opt/boxprover/src
RUN stack install --no-interleaved-output
RUN /bin/bash -c "cp $(stack path --local-install-root)/bin/boxprover ."

FROM debian:stretch

RUN apt-get update
RUN apt-get install libgmp10
RUN mkdir -p /opt/boxprover
COPY --from=builder /opt/boxprover/boxprover /opt/boxprover/boxprover
COPY twelf-server /opt/boxprover/twelf-server
COPY data /opt/boxprover/data
COPY frontend /opt/boxprover/frontend
COPY start.sh /opt/boxprover/start.sh
WORKDIR /opt/boxprover
ENTRYPOINT ["./start.sh"]
