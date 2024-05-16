open Format

module IntSMT = SMTPP.SMT (struct
  type t = int

  let format fmt n = fprintf fmt "v%d" n
end)

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
        printf "%a\n" IntSMT.smt_netlist smt_netlist;
        printf "--------\n";
        let* query = VVEquiv.equivalence_query v v in
        List.iter (printf "%a\n" IntSMT.smt) query;
        printf
          "\n==========================================================\n\n";
        ret ()
      in
      match result with
      | VVEquiv.Inl err -> printf "Error: %s\n" (Util.lst_to_string err)
      | _ -> ())
    VVEquiv.Verilog.examples
