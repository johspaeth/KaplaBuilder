# `make install && make run` must just work (rules.md).
.PHONY: install run build check smoke clean

install:
	@command -v elan >/dev/null || { echo "Install elan first: https://github.com/leanprover/elan"; exit 1; }
	lake build

# The demo: the Defy Gravity website on http://localhost:8000. The API key comes from
# .env in this folder, or else from ANTHROPIC_API_KEY in the shell. Without one the chat is off;
# the rest of the site works.
run:
	lake exe kapla serve

build:
	lake build

# What CI checks, minus `lake check` and `lake comparator` (Linux only; they run in CI).
check:
	scripts/check_imports.sh
	scripts/check_forbidden.sh
	lake build --fail-level=warning
	lake build KaplaSpecs
	lake exe kapla gallery-check

# What a judge does after `make install`: example commands and the website, no API key.
# Uses port 8000 like `make run`; set KAPLA_SMOKE_PORT=N to use another port.
smoke:
	scripts/smoke_test.sh

clean:
	lake clean
