# `make install && make run` must just work (rules.md).
.PHONY: install run build check clean

install:
	@command -v elan >/dev/null || { echo "Install elan first: https://github.com/leanprover/elan"; exit 1; }
	lake build

run:
	lake exe kapla

build:
	lake build

# What CI checks, minus `lake check` / `lake comparator` (Linux only; they run in CI).
check:
	scripts/check_imports.sh
	scripts/check_forbidden.sh
	lake build --fail-level=warning
	lake build KaplaSpecs

clean:
	lake clean
