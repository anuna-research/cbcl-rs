# SPDX-License-Identifier: Apache-2.0
PREFIX ?= $(HOME)/.local
CARGO ?= cargo
# Respect custom Cargo build directories when installing or staging artifacts.
TARGET_DIR ?= $(if $(CARGO_TARGET_DIR),$(CARGO_TARGET_DIR),target)

.PHONY: all build test check lint clippy fmt fmt-fix run install uninstall dist clean doc doc-open proof release help
all: build

build:
	$(CARGO) build --release --locked -p cbcl-cli

test:
	$(CARGO) test --workspace --locked

check: lint test

lint: fmt clippy

clippy:
	$(CARGO) clippy --workspace --all-targets --locked -- -D warnings

fmt:
	$(CARGO) fmt --all --check

fmt-fix:
	$(CARGO) fmt --all

run:
	$(CARGO) run -p cbcl-cli -- $(ARGS)

install: build
	install -d "$(PREFIX)/bin"
	install -m 755 "$(TARGET_DIR)/release/cbcl-cli" "$(PREFIX)/bin/cbcl"

uninstall:
	rm -f "$(PREFIX)/bin/cbcl"

dist: build
	@set -eu; \
	os=$$(uname -s); arch=$$(uname -m); \
	case "$$os" in Darwin) os=darwin ;; Linux) os=linux ;; *) echo "Unsupported OS: $$os" >&2; exit 1 ;; esac; \
	case "$$arch" in arm64|aarch64) arch=arm64 ;; x86_64|amd64) arch=x64 ;; *) echo "Unsupported architecture: $$arch" >&2; exit 1 ;; esac; \
	artifact="cbcl-$$os-$$arch"; \
	mkdir -p dist; \
	cp "$(TARGET_DIR)/release/cbcl-cli" "dist/$$artifact"; \
	if command -v sha256sum >/dev/null 2>&1; then \
	  (cd dist && sha256sum "$$artifact" > "$$artifact.sha256"); \
	else \
	  (cd dist && shasum -a 256 "$$artifact" > "$$artifact.sha256"); \
	fi; \
	echo "Staged dist/$$artifact and its SHA-256 checksum (no upload)."

proof:
	cd lean-cbcl && lake build
	cd lean-cbcl && lake exe runLinter LeanCbcl
	./scripts/check-axioms.sh

doc:
	$(CARGO) doc --workspace --no-deps --locked

doc-open:
	$(CARGO) doc --workspace --no-deps --locked --open

clean:
	$(CARGO) clean
	rm -rf dist

release:
	./release.sh $(VERSION)

help:
	@echo 'CBCL development and release targets:'
	@echo '  build / run ARGS="..."   Build the release CLI / run from source'
	@echo '  test / check            Workspace tests / formatting, clippy and tests'
	@echo '  lint / clippy / fmt     Check code quality'
	@echo '  fmt-fix                 Apply Rust formatting'
	@echo '  proof                   Build Lean, run linter and axiom audit'
	@echo '  install / uninstall     Install/remove cbcl under PREFIX (default ~/.local)'
	@echo '  dist                    Stage host CLI binary and checksum locally'
	@echo '  doc / doc-open / clean  Documentation / build cleanup'
	@echo '  release VERSION=X.Y.Z   Check, bump, commit, tag and push from main'
