TEMPLATES_DIR := templates

# --- Template instantiation ---
# Discover template groups (e.g., templates/adder/ -> adder)
TEMPLATE_GROUPS := $(patsubst $(TEMPLATES_DIR)/%/,%,$(wildcard $(TEMPLATES_DIR)/*/))

# Generate rules for each (group, template) pair.
# Per-file rule example:
#   adder_%/ripple_carry.sv: templates/adder/ripple_carry.sv.j2
# Group rule example:
#   adder_%: adder_%/ripple_carry.sv adder_%/plus_operator.sv
define template_rule
$(1)_%/$(patsubst %.j2,%,$(notdir $(2))): $(2)
	@mkdir -p $$(dir $$@)
	jinja2 -D N=$$* $$< > $$@
endef

define group_rule
.PHONY: $(1)_%
$(1)_%: $(foreach t,$(wildcard $(TEMPLATES_DIR)/$(1)/*.j2),$(1)_%/$(patsubst %.j2,%,$(notdir $(t))))
	@true

.PRECIOUS: $(foreach t,$(wildcard $(TEMPLATES_DIR)/$(1)/*.j2),$(1)_%/$(patsubst %.j2,%,$(notdir $(t))))
endef

$(foreach g,$(TEMPLATE_GROUPS),\
  $(eval $(call group_rule,$(g)))\
  $(foreach t,$(wildcard $(TEMPLATES_DIR)/$(g)/*.j2),\
    $(eval $(call template_rule,$(g),$(t)))))

# --- Synthesis ---
# Find all .sv files, excluding synth_ outputs
ALL_SV := $(shell find . -name '*.sv' -type f | sed 's|^\./||')
SOURCES := $(foreach sv,$(ALL_SV),$(if $(filter synth_%,$(notdir $(sv))),,$(sv)))
TARGETS := $(foreach src,$(SOURCES),$(dir $(src))synth_$(notdir $(src)))

synth_%.sv: %.sv
	@echo "$< -> $@ (Log: $(basename $@).log)"
	@env SV_INPUT=$< SV_OUTPUT=$@ yosys -c synth.tcl > $(basename $@).log 2>&1

synth: $(TARGETS)

# --- Cleanup ---
clean:
	find \( -name 'synth_*.sv' -o -name '*.log' \) -printf "rm %p\n" -delete

clean-generated:
	@for g in $(TEMPLATE_GROUPS); do \
		find . -maxdepth 1 -type d -name "$${g}_*" -printf "rm -r %p\n" -exec rm -r {} +; \
	done

clean-all: clean clean-generated

test: synth
	./run_all.sh

.PHONY: clean clean-generated clean-all synth test
