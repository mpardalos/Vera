open Format

let ( >>= ) (x : ('err, 'a) VVEquiv.sum) (f : 'a -> ('err, 'b) VVEquiv.sum) =
  match x with VVEquiv.Inl e -> VVEquiv.Inl e | VVEquiv.Inr x -> f x

let ( let* ) = ( >>= )
let ( =<< ) a b = b >>= a
let ret x = VVEquiv.Inr x

let () =
  List.iter
    (fun v ->
      let result =
        printf "%a\n" VerilogPP.vmodule v;
        printf "--------\n";
        let* circuit = VVEquiv.verilog_to_netlist v in
        printf "%a\n" NetlistPP.circuit circuit;
        printf "--------\n";
        let smt_netlist = VVEquiv.netlist_to_smt circuit in
        printf "%a\n" SMTPP.Core.smt_netlist smt_netlist;
        printf
          "\n==========================================================\n\n";
        ret ()
      in
      match result with
      | VVEquiv.Inl err -> printf "Error: %s\n" (Util.lst_to_string err)
      | _ -> ())
    VVEquiv.Verilog.examples
