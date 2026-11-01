# Linux environment for the checks that do not run on macOS: `lake check` and
# `lake comparator`. Same Ubuntu release as the CI runners.
FROM ubuntu:24.04

ARG ELAN_VERSION=v4.2.4
ARG LEAN_TOOLCHAIN

RUN apt-get update -qq \
 && apt-get install -y -qq --no-install-recommends \
      bubblewrap ca-certificates curl git make procps \
 && rm -rf /var/lib/apt/lists/*

# Non-root, as in CI. ELAN_HOME is outside any home directory because the
# sandbox of `lake check` hides home directories; CI uses the same path.
# The sandbox also expects /run/user/<uid> to exist.
ENV ELAN_HOME=/opt/elan
ENV PATH=/opt/elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
RUN useradd --create-home lean \
 && mkdir -p /opt/elan /workspace/.lake /run/user/$(id -u lean) \
 && chown -R lean:lean /opt/elan /workspace /run/user/$(id -u lean)
USER lean

RUN cd /tmp \
 && curl -sSfL "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-x86_64-unknown-linux-gnu.tar.gz" \
    | tar xz \
 && ./elan-init -y --no-modify-path --default-toolchain none \
 && rm elan-init \
 && elan toolchain install "${LEAN_TOOLCHAIN}"

WORKDIR /workspace
