open Format

let () =
  printf "Verilog\n";
  printf "=======\n";
  List.iter
    (fun v ->
      printf "%a\n" VerilogPP.vmodule v;
      printf "--------\n";
      printf "%a\n" NetlistPP.circuit (VerilogToNetlist.transfer_module v);
      printf "\n==========================================================\n\n")
    Verilog.examples;
