# 1. Grab all .sv files in the current directory and subdirectories
ALL_SV := $(shell find . -name '*.sv' -type f | sed 's|^\./||')

# 2. Filter out anything whose filename starts with 'synth_'
SOURCES := $(foreach sv,$(ALL_SV),$(if $(filter synth_%,$(notdir $(sv))),,$(sv)))

# 3. Define the targets: insert synth_ before the filename in the same directory
TARGETS := $(foreach src,$(SOURCES),$(dir $(src))synth_$(notdir $(src)))

.PHONY: clean all test

all: $(TARGETS)

# Pattern rule: synth_%.sv synthesizes %.sv
synth_%.sv: %.sv
	@echo "$< -> $@ (Log: $(basename $@).log)"
	@env SV_INPUT=$< SV_OUTPUT=$@ yosys -c synth.tcl > $(basename $@).log 2>&1

clean:
	find \( -name synth_*.sv -or -name synth_*.log \) -printf "rm %p\n" -delete

test: $(TARGETS)
	./run_all.sh
