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
    (fun (v1, v2) ->
      let result =
        printf "\n-- Verilog a --\n";
        printf "%a\n" VerilogPP.vmodule v1;
        printf "\n-- Verilog b --\n";
        printf "%a\n" VerilogPP.vmodule v2;
        printf "\n---------------------------\n";
        let* (nl1, st) = VVEquiv.verilog_to_netlist 1 v1 in
        let* (nl2, _) = VVEquiv.verilog_to_netlist st v2 in
        printf "\n-- Netlist a --\n";
        printf "%a\n" NetlistPP.circuit nl1;
        printf "\n-- Netlist b --\n";
        printf "%a\n" NetlistPP.circuit nl2;
        printf "\n---------------------------\n";
        let* query = VVEquiv.equivalence_query v1 v2 in
        printf "\n-- SMT Query --\n";
        List.iter (printf "%a\n" IntSMT.smt) query;
        printf
          "\n==========================================================\n\n";
        ret ()
      in
      match result with
      | VVEquiv.Inl err -> printf "Error: %s\n" (Util.lst_to_string err)
      | _ -> ())
    VVEquiv.Verilog.examples
