TARGET_PACKAGE ?= smtt-composition

all: build

.PHONY: setup
setup:
	stack setup
	stack build --only-dependencies --test --no-run-tests

.PHONY: build
build:
	stack build --test --no-run-tests --bench --no-run-benchmarks

.PHONY: install
install:
	stack install

.PHONY: test
test:
	stack test $(TARGET_PACKAGE)

.PHONY: coverage
coverage:
	stack test --coverage

.PHONY: bench
bench:
	stack bench $(TARGET_PACKAGE)
