---
name: verilog-testcase
description: Generate equivalent Verilog test case modules for the Vera equivalence checker
argument-hint: "[operation] [implementation-style]"
---

# Generating Verilog Test Cases for Vera

You are writing a SystemVerilog module that will be used as a test case for Vera,
a formally verified Verilog equivalence checker. The module must implement the
requested operation in the requested style, and must be semantically equivalent
to the other implementations of the same operation that already exist in the
same directory.

## Step-by-step process

1. Read the existing test cases in `examples/` for the same operation to
   determine the interface (input/output names, widths, module naming).
   - **If creating a new test category** with no existing examples, design a clean interface with descriptive input/output names and appropriate bit widths for the operation.
2. Write a new `.sv` file implementing the same operation in the requested style.
3. Place it alongside the existing implementations in the same
   `examples/<operation>/` directory.
4. Verify equivalence by running Vera against an existing implementation:
   ```bash
   dune exec vera -- compare --solver=z3 examples/<operation>/existing.sv examples/<operation>/new.sv
   ```
   The expected output for equivalent modules is `Equivalent (UNSAT)`.

## Vera's supported Verilog subset

Only **purely combinational** logic using `assign` statements is supported.

### Supported constructs

- `assign` statements (continuous assignment only)
- Arithmetic operators: `+`, `-`, `*`
- Bitwise operators: `&`, `|`, `^`, `~`
- Shift operators: `<<`, `>>`, `<<<`
- Conditional (ternary) operator: `? :`
- Bit selection: `signal[idx]`
- Concatenation: `{a, b}`
- `wire` declarations for intermediate values

### NOT supported (do not use any of these)

- `always` blocks of any kind (`always`, `always_comb`, `always_ff`)
- Non-blocking assignments (`<=`)
- Sequential logic (clocks, flip-flops, registers)
- Arrays, structs, unions
- `for`, `generate`, `while` loops
- `case`, `if`/`else` statements (use the ternary `? :` operator instead)
- `function`, `task` definitions
- Module instantiation / sub-modules
- Multi-driven nets
- `integer`, `real`, or other non-logic types

## Important rules

- Use sized literals everywhere: `8'd0`, `4'b0000`, `1'b0`, etc.
- Bit selection indices should use sized literals (e.g., `8'd0` not `0`).

## Module structure template

```systemverilog
module <descriptive_name> (
    input  logic [W_IN-1:0] <input_names>,
    output logic [W_OUT-1:0] <output_names>
);
    wire [N:0] intermediate;
    assign intermediate = ...;
    assign <output> = ...;
endmodule
```

- The module name should describe the implementation style.
- Input/output names and widths **must exactly match** the other implementations
  of the same operation.
- Keep the implementation clean and readable.

## Troubleshooting

**If equivalence checking fails unexpectedly:**

1. **Check for unimplemented features** - Even if an operator is listed as supported, it may not be fully implemented yet. Look for error messages like "Unary operators not supported" or "Unknown operator".

2. **Test operators in isolation** - If a complex expression fails, create a minimal test case using just the suspect operator to verify it works:
   ```systemverilog
   // Simple test for operator ~
   assign out = ~a;
   ```

3. **Build incrementally** - Start with simple test cases before creating complex ones. For example, test `~(a & b)` before testing nested expressions like `~((a & b) | c)`.

4. **It's okay to create tests for future features** - You can write test cases that use unimplemented operators. They'll error out now but will work once the feature is implemented.
