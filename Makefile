BIN := .lake/build/bin/linproof
JOBS ?= 4
DIFF_N ?= 1000

.PHONY: build proofs test test-lean test-cli test-tools test-porcupine lint diff bench clean

build:
	lake build

# No sorry/admit/native_decide/axiom/partial/unsafe in the library; print the axioms of
# the main theorems and fail on anything but propext, Classical.choice and Quot.sound.
proofs:
	./scripts/check-proofs.sh

test: build test-lean test-cli test-tools test-porcupine

test-lean:
	lake build linproof-tests
	.lake/build/bin/linproof-tests

test-cli: build
	./test/cli-tests.sh

test-tools:
	python3 tools/test_jepsen2jsonl.py

# Differential test against Porcupine (fetched as a Go module) and Porcupine's test data.
test-porcupine: build
	cd test/porcupine && LINPROOF_DIFF_N=$(DIFF_N) go test -count=1 -p $(JOBS) ./...

lint: proofs
	test -z "$$(gofmt -l test/porcupine)"
	cd test/porcupine && go vet ./...

# A larger differential run: DIFF_N histories per model.
diff: build
	cd test/porcupine && go build -o ../../.lake/build/bin/porcupine-diff .
	for m in register cas-register kv; do \
		.lake/build/bin/porcupine-diff diff -linproof $(BIN) -model $$m -seed 1 -n $(DIFF_N) || exit 1; \
	done

bench: build
	./bench/run.sh

clean:
	rm -rf .lake/build
