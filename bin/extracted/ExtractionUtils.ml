let trace_enabled = ref false
let trace_indent = ref 0
let trace_start = Unix.gettimeofday ()

let make_prefix n marker fmt =
  let buf = Buffer.create (n * 3 + 4) in
  for _ = 1 to n do Buffer.add_string buf "| " done;
  Buffer.add_string buf marker;
  Printf.fprintf fmt "[%8.3f] %s" (Unix.gettimeofday () -. trace_start) (Buffer.contents buf)

let my_rocq_traceBracket msg f =
  if not !trace_enabled then f ()
  else begin
    let n = !trace_indent in
    Printf.eprintf "%t %s\n%!" (make_prefix n "/") msg;
    incr trace_indent;
    let t0 = Unix.gettimeofday () in
    let result = f () in
    let took = Unix.gettimeofday () -. t0 in
    decr trace_indent;
    Printf.eprintf "%t %s (%.3fs)\n%!" (make_prefix n "\\") msg took;
    result
  end

let my_rocq_trace msg f =
  if !trace_enabled
    then Printf.eprintf "%t %s\n%!" (make_prefix !trace_indent ">") msg;
  f ()
