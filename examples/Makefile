SYSTEMVERILOG_FILES := $(wildcard *.sv)
AST_FILES := $(SYSTEMVERILOG_FILES:%.sv:%.ast.json)
SV_ := $(patsubst %.c,%.o,$(wildcard *.c))

.PHONY: all
all: $(AST_FILES)

%.ast.json: %.sv
	slang --ast-json $@ $<
