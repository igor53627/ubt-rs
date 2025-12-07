# Makefile for UBT Formal Verification

COQC := coqc
COQDEP := coqdep

# Path to RocqOfRust library (adjust if installed elsewhere)
ROCQOFRUST_PATH := $(HOME)/pse/paradigm/rocq-of-rust/RocqOfRust

# Flags for our code (specs, simulations, proofs)
COQFLAGS := -Q specs UBT.Specs -Q simulations UBT.Sim -Q proofs UBT.Proofs

# Flags for translated code (needs RocqOfRust)
COQFLAGS_TRANS := -R $(ROCQOFRUST_PATH) RocqOfRust -Q src UBT.Src

# Source files
SPEC_FILES := specs/tree_spec.v specs/embedding_spec.v
SIM_FILES := $(wildcard simulations/*.v)
PROOF_FILES := $(wildcard proofs/*.v)
TRANS_FILES := $(wildcard src/*.v)

ALL_V := $(SPEC_FILES) $(SIM_FILES) $(PROOF_FILES)
ALL_VO := $(ALL_V:.v=.vo)
TRANS_VO := $(TRANS_FILES:.v=.vo)

.PHONY: all clean specs simulations proofs translate translation check-deps help

all: specs simulations proofs

# Build specifications
specs: $(SPEC_FILES:.v=.vo)

# Build simulations (depends on specs)
simulations: specs $(SIM_FILES:.v=.vo)

# Build proofs (depends on simulations)
proofs: simulations $(PROOF_FILES:.v=.vo)

# Build translated Rust code (requires RocqOfRust library)
translation: $(TRANS_VO)

# Compile spec/sim/proof .v to .vo
specs/%.vo: specs/%.v
	$(COQC) $(COQFLAGS) $<

simulations/%.vo: simulations/%.v
	$(COQC) $(COQFLAGS) $<

proofs/%.vo: proofs/%.v
	$(COQC) $(COQFLAGS) $<

# Compile translated .v to .vo
src/%.vo: src/%.v
	@if [ -d "$(ROCQOFRUST_PATH)" ]; then \
		$(COQC) $(COQFLAGS_TRANS) $<; \
	else \
		echo "Error: RocqOfRust not found at $(ROCQOFRUST_PATH)"; \
		echo "Build it first: cd rocq-of-rust/RocqOfRust && make"; \
		exit 1; \
	fi

# Generate dependencies
depend:
	$(COQDEP) $(COQFLAGS) $(ALL_V) > .depend

# Translate Rust to Rocq using rocq-of-rust
translate:
	@echo "Translating UBT Rust code to Rocq..."
	cd .. && cargo +nightly-2024-12-07 rocq-of-rust
	@echo "Translation complete. Check src/ for generated .v files."

# Clean generated files
clean:
	rm -f specs/*.vo specs/*.glob specs/*.vok specs/*.vos
	rm -f simulations/*.vo simulations/*.glob simulations/*.vok simulations/*.vos
	rm -f proofs/*.vo proofs/*.glob proofs/*.vok proofs/*.vos
	rm -f src/*.vo src/*.glob src/*.vok src/*.vos
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

# Help
help:
	@echo "UBT Formal Verification Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  all         - Build specs, simulations, and proofs (default)"
	@echo "  specs       - Build specification files"
	@echo "  simulations - Build simulation files"
	@echo "  proofs      - Build proof files"
	@echo "  translation - Build translated Rust code (requires RocqOfRust)"
	@echo "  translate   - Re-translate Rust to Rocq (requires rocq-of-rust)"
	@echo "  clean       - Remove generated files"
	@echo "  check-deps  - Verify dependencies are installed"
	@echo "  help        - Show this message"
	@echo ""
	@echo "Prerequisites:"
	@echo "  - Rocq 9.x (opam switch rocq-9)"
	@echo "  - RocqOfRust library (for 'translation' target)"

-include .depend
