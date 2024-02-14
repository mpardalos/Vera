open Format

let () =
  List.iter
    (fun v ->
      printf "%a\n" VerilogPP.vmodule v;
      printf "--------\n";
      match VVEquiv.verilog_to_netlist v with
      | VVEquiv.Inl err -> printf "Error: %s\n" (Util.lst_to_string err)
      | VVEquiv.Inr circuit -> printf "%a\n" NetlistPP.circuit circuit;
      printf "\n==========================================================\n\n")
    VVEquiv.Verilog.examples
