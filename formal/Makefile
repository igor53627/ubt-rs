# Makefile for UBT Formal Verification

# Rocq 9 uses rocqc/rocqdep, fallback to coqc/coqdep for compatibility
COQC := $(shell which rocqc 2>/dev/null || echo coqc)
COQDEP := $(shell which rocqdep 2>/dev/null || echo coqdep)

# Path to RocqOfRust library
# Can be overridden: make linking ROCQOFRUST_PATH=/custom/path
# See docs/LINKING_LAYER_SETUP.md for setup instructions
ROCQOFRUST_PATH ?= $(HOME)/pse/paradigm/rocq-of-rust/RocqOfRust

# Flags for our code (specs, simulations, proofs)
COQFLAGS := -Q specs UBT.Specs -Q simulations UBT.Sim -Q proofs UBT.Proofs

# QuickChick library path (auto-detected via opam)
QUICKCHICK_PATH := $(shell opam var coq-quickchick:lib 2>/dev/null)
COQFLAGS_QC := $(COQFLAGS) $(if $(QUICKCHICK_PATH),-Q $(QUICKCHICK_PATH) QuickChick,)

# Flags for translated code (needs RocqOfRust)
# Note: Uses -Q src src to match the auto-generated "Require Export src.xxx" paths
COQFLAGS_TRANS := -R $(ROCQOFRUST_PATH) RocqOfRust -Q src src

# Source files
SPEC_FILES := specs/tree_spec.v specs/embedding_spec.v
SIM_FILES := $(wildcard simulations/*.v)
PROOF_FILES := $(wildcard proofs/*.v)
# Core proofs (without QuickChick dependency)
PROOF_CORE_FILES := proofs/correctness.v
TRANS_FILES := $(wildcard src/*.v)

ALL_V := $(SPEC_FILES) $(SIM_FILES) $(PROOF_FILES)
ALL_VO := $(ALL_V:.v=.vo)
TRANS_VO := $(TRANS_FILES:.v=.vo)
LINKING_FILES := $(wildcard linking/*.v)
LINKING_VO := $(LINKING_FILES:.v=.vo)

# Flags for linking layer (needs RocqOfRust + simulations + src)
COQFLAGS_LINKING := -R $(ROCQOFRUST_PATH) RocqOfRust -Q simulations UBT.Sim -Q src src -Q linking UBT.Linking

.PHONY: all clean specs simulations proofs proofs-core quickchick quickchick-ci test translate translation linking extract extract-test extract-clean docs docs-clean check-deps help ci ci-full audit verify-axioms check-admits

all: specs simulations proofs

# Combined test target: builds proofs and runs QuickChick
test: proofs-core quickchick
	@echo "All tests passed!"

# Build specifications
specs: $(SPEC_FILES:.v=.vo)

# Build simulations (depends on specs)
simulations: specs $(SIM_FILES:.v=.vo)

# Build proofs (depends on simulations) - requires QuickChick
proofs: simulations $(PROOF_FILES:.v=.vo)

# Build core proofs only (no QuickChick dependency) - for CI
proofs-core: simulations $(PROOF_CORE_FILES:.v=.vo)

# Run QuickChick property-based tests (requires coq-quickchick)
# Full tests: 10,000 per property (50,000 total)
quickchick: simulations proofs/quickchick_tests.vo
	@echo "QuickChick tests completed successfully!"

# Run QuickChick CI tests (reduced count for faster CI builds)
# CI tests: 1,000 per property (5,000 total)
quickchick-ci: simulations proofs/quickchick_tests_ci.vo
	@echo "QuickChick CI tests completed successfully!"

# Build translated Rust code (requires RocqOfRust library)
translation: $(TRANS_VO)

# Build linking layer (requires RocqOfRust + simulations + translation)
linking: simulations translation $(LINKING_VO)

# Compile spec/sim/proof .v to .vo
specs/%.vo: specs/%.v
	$(COQC) $(COQFLAGS) $<

simulations/%.vo: simulations/%.v
	$(COQC) $(COQFLAGS) $<

proofs/%.vo: proofs/%.v
	$(COQC) $(COQFLAGS_QC) $<

# Compile translated .v to .vo
src/%.vo: src/%.v
	@if [ ! -d "$(ROCQOFRUST_PATH)" ]; then \
		echo "Error: RocqOfRust not found at $(ROCQOFRUST_PATH)"; \
		echo "See docs/LINKING_LAYER_SETUP.md for setup instructions."; \
		exit 1; \
	elif [ ! -f "$(ROCQOFRUST_PATH)/M.vo" ]; then \
		echo "Error: RocqOfRust not compiled. Run: cd $(ROCQOFRUST_PATH) && make"; \
		exit 1; \
	else \
		$(COQC) $(COQFLAGS_TRANS) $<; \
	fi

# Compile linking .v to .vo
linking/%.vo: linking/%.v
	@if [ ! -d "$(ROCQOFRUST_PATH)" ]; then \
		echo ""; \
		echo "==========================================================="; \
		echo "ERROR: RocqOfRust library not found"; \
		echo "==========================================================="; \
		echo ""; \
		echo "Expected location: $(ROCQOFRUST_PATH)"; \
		echo ""; \
		echo "Setup instructions:"; \
		echo "  1. git clone https://github.com/formal-land/rocq-of-rust.git ~/pse/paradigm/rocq-of-rust"; \
		echo "  2. cd ~/pse/paradigm/rocq-of-rust/RocqOfRust"; \
		echo "  3. eval \$$(opam env --switch=rocq-9)"; \
		echo "  4. make -j4"; \
		echo ""; \
		echo "Or specify custom path:"; \
		echo "  make linking ROCQOFRUST_PATH=/your/path/RocqOfRust"; \
		echo ""; \
		echo "See docs/LINKING_LAYER_SETUP.md for full documentation."; \
		echo "==========================================================="; \
		exit 1; \
	elif [ ! -f "$(ROCQOFRUST_PATH)/M.vo" ]; then \
		echo ""; \
		echo "==========================================================="; \
		echo "ERROR: RocqOfRust library not compiled"; \
		echo "==========================================================="; \
		echo ""; \
		echo "Found directory: $(ROCQOFRUST_PATH)"; \
		echo "But M.vo is missing (library not built)."; \
		echo ""; \
		echo "Run:"; \
		echo "  cd $(ROCQOFRUST_PATH)"; \
		echo "  eval \$$(opam env --switch=rocq-9)"; \
		echo "  make -j4"; \
		echo ""; \
		echo "See docs/LINKING_LAYER_SETUP.md for full documentation."; \
		echo "==========================================================="; \
		exit 1; \
	else \
		$(COQC) $(COQFLAGS_LINKING) $<; \
	fi

# Explicit dependencies for linking layer
linking/operations.vo: linking/types.vo
linking/monad.vo: linking/types.vo linking/operations.vo
linking/interpreter.vo: linking/monad.vo linking/operations.vo linking/types.vo

# Explicit dependencies for proofs layer
proofs/spec_linking.vo: simulations/tree.vo
proofs/multiproof.vo: simulations/tree.vo
proofs/correctness.vo: simulations/tree.vo

# Explicit dependencies for specs layer (tree_spec imports simulations)
specs/tree_spec.vo: simulations/tree.vo

# Explicit dependencies for simulations layer
simulations/tree.vo: simulations/crypto.vo
simulations/verkle.vo: simulations/tree.vo
simulations/security.vo: simulations/crypto.vo simulations/tree.vo
simulations/iterator.vo: simulations/tree.vo
simulations/serialization.vo: simulations/tree.vo
simulations/complexity.vo: simulations/tree.vo
simulations/streaming.vo: simulations/tree.vo
simulations/verkle_linking.vo: simulations/verkle.vo

# Generate dependencies
depend:
	$(COQDEP) $(COQFLAGS) $(ALL_V) > .depend

# Translate Rust to Rocq using rocq-of-rust
translate:
	@echo "Translating UBT Rust code to Rocq..."
	cd .. && cargo +nightly-2024-12-07 rocq-of-rust
	@echo "Translation complete. Check src/ for generated .v files."

# OCaml Extraction
# Flags for extraction (needs simulations)
COQFLAGS_EXTRACT := -Q specs UBT.Specs -Q simulations UBT.Sim -Q extraction UBT.Extract

# Extract to OCaml (depends on simulations being compiled)
extract: simulations extraction/extract.vo
	@echo "OCaml extraction complete!"
	@echo "Generated files:"
	@echo "  extraction/extracted.ml"
	@echo "  extraction/extracted.mli"
	@echo ""
	@echo "To compile the tests (optional):"
	@echo "  cd extraction && ocamlfind ocamlopt extracted.ml test_extracted.ml -o test_ubt"

extraction/extract.vo: extraction/extract.v
	$(COQC) $(COQFLAGS_EXTRACT) $<
	@if [ -f extracted.ml ]; then mv extracted.ml extracted.mli extraction/; fi

# Build and run extracted OCaml tests (optional - requires OCaml toolchain)
extract-test: extract
	@echo "Compiling extracted OCaml code..."
	@cd extraction && ocamlfind ocamlopt -package zarith -linkpkg extracted.ml test_extracted.ml -o test_ubt 2>/dev/null || \
		(ocamlopt extracted.ml test_extracted.ml -o test_ubt 2>/dev/null || \
		echo "OCaml compilation failed - this is optional, extracted.ml is still usable")
	@if [ -f extraction/test_ubt ]; then \
		echo "Running tests..."; \
		./extraction/test_ubt; \
	fi

extract-clean:
	rm -f extraction/*.vo extraction/*.glob extraction/*.vok extraction/*.vos
	rm -f extraction/extracted.ml extraction/extracted.mli
	rm -f extraction/test_ubt extraction/*.cmi extraction/*.cmx extraction/*.o

# Documentation generation using coqdoc
COQDOC := coqdoc
COQDOC_FLAGS := --toc --interpolate --utf8 --html \
	-Q specs UBT.Specs -Q simulations UBT.Sim -Q proofs UBT.Proofs
DOC_DIR := docs/html

# Generate HTML documentation
docs: specs simulations proofs
	@mkdir -p $(DOC_DIR)
	@echo "Generating HTML documentation..."
	$(COQDOC) $(COQDOC_FLAGS) -d $(DOC_DIR) \
		$(SPEC_FILES) $(SIM_FILES) $(PROOF_FILES)
	@echo "Documentation generated in $(DOC_DIR)/"
	@echo "Open docs/html/toc.html to browse."

# Clean generated documentation
docs-clean:
	rm -rf $(DOC_DIR)

# Clean generated files
clean: extract-clean docs-clean
	rm -f specs/*.vo specs/*.glob specs/*.vok specs/*.vos
	rm -f simulations/*.vo simulations/*.glob simulations/*.vok simulations/*.vos
	rm -f proofs/*.vo proofs/*.glob proofs/*.vok proofs/*.vos
	rm -f src/*.vo src/*.glob src/*.vok src/*.vos
	rm -f linking/*.vo linking/*.glob linking/*.vok linking/*.vos
	rm -f .depend

# Check if dependencies are installed
check-deps:
	@which $(COQC) > /dev/null || (echo "Error: coqc not found. Install Rocq first." && exit 1)
	@echo "Rocq version: $$($(COQC) --version)"
	@if [ -d "$(ROCQOFRUST_PATH)" ]; then \
		echo "RocqOfRust: $(ROCQOFRUST_PATH)"; \
		if [ -f "$(ROCQOFRUST_PATH)/M.vo" ]; then \
			echo "RocqOfRust library: compiled"; \
		else \
			echo "RocqOfRust library: NOT compiled (run 'make' in RocqOfRust/)"; \
		fi \
	else \
		echo "RocqOfRust: NOT FOUND"; \
	fi

# CI Targets
# Basic CI build (for PRs)
ci: clean all linking
	@echo "CI build complete!"

# Full CI build with all checks (for release verification)
ci-full: ci extract docs audit check-admits
	@echo "Full CI verification complete!"

# Audit axioms and admits (generates report)
audit:
	@chmod +x scripts/count_axioms.sh
	@./scripts/count_axioms.sh | tee audit-report.txt

# List all axioms with counts (for review)
verify-axioms:
	@echo "=== Axiom Verification Report ==="
	@echo ""
	@echo "Axiom declarations:"
	@grep -rn '^Axiom' specs/ simulations/ proofs/ linking/ 2>/dev/null || echo "  (none in specs/sim/proofs/linking)"
	@echo ""
	@echo "Parameter declarations:"
	@grep -rn '^Parameter' specs/ simulations/ proofs/ linking/ 2>/dev/null || echo "  (none in specs/sim/proofs/linking)"
	@echo ""
	@echo "Summary:"
	@AXIOMS=$$(grep -rh '^Axiom' specs/ simulations/ proofs/ linking/ 2>/dev/null | wc -l); \
	PARAMS=$$(grep -rh '^Parameter' specs/ simulations/ proofs/ linking/ 2>/dev/null | wc -l); \
	echo "  Total Axioms: $$AXIOMS"; \
	echo "  Total Parameters: $$PARAMS"

# Threshold for allowed admits (set to current count)
ADMIT_THRESHOLD ?= 10

# Check admits don't exceed threshold
check-admits:
	@echo "Checking admit count against threshold ($(ADMIT_THRESHOLD))..."
	@ADMITS=$$(grep -rn '\badmit\.' proofs/ linking/ 2>/dev/null | wc -l | tr -d ' '); \
	if [ "$$ADMITS" -gt "$(ADMIT_THRESHOLD)" ]; then \
		echo "ERROR: admit count ($$ADMITS) exceeds threshold ($(ADMIT_THRESHOLD))"; \
		exit 1; \
	else \
		echo "OK: admit count ($$ADMITS) within threshold ($(ADMIT_THRESHOLD))"; \
	fi

# Help
help:
	@echo "UBT Formal Verification Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  all         - Build specs, simulations, and proofs (default)"
	@echo "  specs       - Build specification files"
	@echo "  simulations - Build simulation files"
	@echo "  proofs      - Build proof files (requires QuickChick)"
	@echo "  proofs-core - Build core proofs (no QuickChick needed)"
	@echo "  quickchick  - Run QuickChick tests (full: 10k/property)"
	@echo "  quickchick-ci - Run QuickChick tests (CI: 1k/property)"
	@echo "  test        - Run all tests (proofs-core + quickchick)"
	@echo "  translation - Build translated Rust code (requires RocqOfRust)"
	@echo "  translate   - Re-translate Rust to Rocq (requires rocq-of-rust)"
	@echo "  linking     - Build linking layer (requires RocqOfRust)"
	@echo "  extract     - Extract to OCaml (generates extraction/extracted.ml)"
	@echo "  extract-test- Build and run OCaml tests (optional)"
	@echo "  extract-clean- Clean extraction artifacts"
	@echo "  docs        - Generate HTML documentation (coqdoc)"
	@echo "  docs-clean  - Remove generated documentation"
	@echo "  clean       - Remove all generated files"
	@echo "  check-deps  - Verify dependencies are installed"
	@echo "  ci          - CI build (clean + all + linking)"
	@echo "  ci-full     - Full CI with extraction, docs, audit, and checks"
	@echo "  audit       - Count axioms and admits, generate report"
	@echo "  verify-axioms - List all axioms with locations"
	@echo "  check-admits - Fail if admits exceed threshold"
	@echo "  help        - Show this message"
	@echo ""
	@echo "Prerequisites:"
	@echo "  - Rocq 9.x (opam switch rocq-9)"
	@echo "  - RocqOfRust library (for 'translation' and 'linking' targets)"
	@echo "  - coqdoc (included with Rocq, for 'docs' target)"

-include .depend
