open Format

let eval_transf a n = fst (StateMonad.runState a n)

let () =
  List.iter
    (fun v ->
      printf "%a\n" VerilogPP.vmodule v;
      printf "--------\n";
      printf "%a\n" NetlistPP.circuit
        (eval_transf (VerilogToNetlist.transfer_module v) 0);
      printf "\n==========================================================\n\n")
    Verilog.examples
