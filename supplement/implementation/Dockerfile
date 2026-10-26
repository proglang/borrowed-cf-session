FROM docker.io/rust:1.96 AS cstb
WORKDIR /cstb
COPY . .
RUN cargo install --path .

FROM docker.io/haskell:9.4.8 AS freest
RUN git clone https://github.com/freest-lang/freest.git
WORKDIR /freest
RUN GHC_NO_UNICODE=1 stack install --system-ghc freest

FROM debian:trixie-slim
RUN apt-get update && apt-get -y install locales && rm -rf /var/lib/apt/lists/*
RUN sed -i '/en_US.UTF-8/s/^# //g' /etc/locale.gen && locale-gen
ENV LANG=en_US.UTF-8
ENV LANGUAGE=en_US:en
ENV LC_ALL=en_US.UTF-8
RUN mkdir -p /freest/.stack-work
WORKDIR /cstb
COPY --from=cstb /cstb/examples ./examples
COPY --from=cstb /usr/local/cargo/bin/cstb /usr/local/bin/cstb
COPY --from=freest /root/.local/bin/freest /usr/local/bin/freest
COPY --from=freest /freest/.stack-work/install /freest/.stack-work/install
CMD ["bash"]
