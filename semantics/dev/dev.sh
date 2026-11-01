#!/usr/bin/env bash
# Run from macOS. Starts the dev container if needed, then opens a shell in it,
# or runs the given command: semantics/dev/dev.sh lake build KaplaSemantics
#
# The repo is mounted at /workspace. `.lake` is a named volume per checkout
# folder, so the macOS build and other worktrees keep their own build output.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
name="$(basename "$root" | tr '[:upper:]' '[:lower:]')"
toolchain="$(cat "$root/lean-toolchain")"

# The tag changes when the Dockerfile or the toolchain changes.
tag="$(cat "$here/Dockerfile" "$root/lean-toolchain" | shasum | cut -c1-12)"
image="kapla-dev:$tag"
container="kapla-dev-$name"

if ! docker image inspect "$image" >/dev/null 2>&1; then
  docker build --platform linux/amd64 --build-arg "LEAN_TOOLCHAIN=$toolchain" \
    -t "$image" "$here"
fi

# Replace a container left over from an older image.
current="$(docker inspect -f '{{.Config.Image}}' "$container" 2>/dev/null || true)"
if [[ -n "$current" && "$current" != "$image" ]]; then
  docker rm -f "$container" >/dev/null
  current=""
fi

if [[ -z "$current" ]]; then
  # The four security settings are what bubblewrap, the sandbox of
  # `lake check` and `lake comparator`, needs inside a container.
  docker run -d --init --platform linux/amd64 --name "$container" \
    --cap-add SYS_ADMIN \
    --security-opt seccomp=unconfined \
    --security-opt apparmor=unconfined \
    --security-opt systempaths=unconfined \
    -v "$root:/workspace" \
    -v "kapla-lake-$name:/workspace/.lake" \
    "$image" sleep infinity >/dev/null
else
  docker start "$container" >/dev/null
fi

if [[ $# -eq 0 ]]; then
  exec docker exec -it "$container" bash
fi
exec docker exec "$container" "$@"
