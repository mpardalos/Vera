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
- Replication: `{N{expr}}` syntax (e.g., `{8{1'b0}}`)
- Dynamic bit selection with out-of-bounds index (index width must guarantee in-bounds access)

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

## Width-Generic Templates (Jinja2)

For testing across multiple bit widths, use Jinja2 templates instead of hardcoded modules.

### Template Location & Build

- **Template files**: `examples/templates/<category>/<name>.sv.j2`
- **Generated output**: `examples/gen_<category>_<N>/<name>.sv`
- **Build command**: `shake examples/summary.csv` generates and tests all configured widths
- **Manual render**: `jinja2 -D N=8 examples/templates/<category>/<name>.sv.j2`

### Template Patterns

```jinja2
{% set N = N | int -%}
{% set HALF = N // 2 -%}
{% set OUT_W = 2 * N -%}
module example (
    input  logic [{{ N-1 }}:0] in,
    output logic [{{ OUT_W-1 }}:0] out
);
```

**Common patterns:**

| Pattern | Jinja2 Syntax |
|---------|---------------|
| Width parameter | `{% set N = N \| int -%}` |
| Derived width | `{% set HALF = N // 2 -%}` |
| Verilog `{` brace | `{% raw %}{{% endraw %}` |
| Whitespace control | `{%-` and `-%}` to trim newlines |
| Loop (descending) | `{% for i in range(N-1, -1, -1) %}...{% endfor %}` |
| Conditional | `{% if COND %}...{% else %}...{% endif %}` |

**Manual log2** (Jinja2 has no log function):
```jinja2
{%- if N < 2 -%}{% set IDX_W = 0 %}
{%- elif N < 4 -%}{% set IDX_W = 1 %}
{%- elif N < 8 -%}{% set IDX_W = 2 %}
{%- elif N < 16 -%}{% set IDX_W = 3 %}
...
{%- endif -%}
```

### Asymmetric Splits (for odd N)

For algorithms like Karatsuba that split inputs in half, handle odd widths with asymmetric splits:

```jinja2
{% set H_LOW = N // 2 -%}
{% set H_HIGH = N - H_LOW -%}

wire [{{ H_HIGH-1 }}:0] a_high;  // Larger half
wire [{{ H_LOW-1 }}:0] a_low;    // Smaller half
assign a_high = in[{{ N-1 }}:{{ H_LOW }}];
assign a_low = in[{{ H_LOW-1 }}:0];
```

**Key width calculations:**
- Products: `z_low = 2*H_LOW` bits, `z_high = 2*H_HIGH` bits
- Sums with overflow: `H_HIGH + 1` bits (zero-extend smaller operand)
- Shift amounts: based on `H_LOW`, not `N`

### Existing Templates

Reference implementations in `examples/templates/`:
- `adder/` - plus_operator, ripple_carry, carry_lookahead
- `multiplier/` - star_operator, shift_and_add, karatsuba
- `rangeselect/` - rangeselect, concat
- `bitselect/` - bitselect, shift
- `conditional/` - ternary, gates
