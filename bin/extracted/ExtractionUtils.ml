let trace_enabled = ref false
let trace_indent = ref 0
let trace_start = ref 0.0
let trace_started = ref false

let make_prefix n marker =
  let buf = Buffer.create (n * 3 + 4) in
  for _ = 1 to n do Buffer.add_string buf "│ " done;
  Buffer.add_string buf marker;
  Buffer.contents buf

let my_rocq_trace msg f =
  if not !trace_enabled then f ()
  else begin
    if not !trace_started then begin
      trace_start := Unix.gettimeofday ();
      trace_started := true
    end;
    let elapsed () = Unix.gettimeofday () -. !trace_start in
    let n = !trace_indent in
    Printf.eprintf "[%8.3f] %s %s\n%!" (elapsed ()) (make_prefix n "┌") msg;
    incr trace_indent;
    let t0 = Unix.gettimeofday () in
    let result = f () in
    let took = Unix.gettimeofday () -. t0 in
    decr trace_indent;
    Printf.eprintf "[%8.3f] %s %s (%.3fs)\n%!" (elapsed ()) (make_prefix n "└") msg took;
    result
  end
