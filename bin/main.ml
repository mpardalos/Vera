open Format

let () =
  printf "Verilog\n";
  printf "=======\n";
  List.iter
    (fun v -> printf "%a\n---\n" VerilogPP.vmodule v)
    Verilog.examples;

  printf "\n";
  printf "Netlists\n";
  printf "========\n";
  List.iter
    (fun c -> printf "%a\n---\n" NetlistPP.circuit c)
    Netlist.examples
