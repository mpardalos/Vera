open Testlib ;;


let t n v b = Alcotest_lwt.test_case n `Slow (fun _ () -> test_verilog_blif n v b)

let () =
  setup ();
  Lwt_main.run @@ Alcotest_lwt.run "Vera" [
    "EPFL-benchmarks", [
      t "adder-depth" "EPFL-benchmarks/arithmetic/adder.v" "EPFL-benchmarks/best_results/depth/adder_depth_2021.blif"
    ]
  ]
  (* let test_result = *)
  (*   run "EPFL-benchmarks" [] *)
  (* in Async.Deferred.value_exn test_result *)
    (* test "adder-depth"       "EPFL-benchmarks/arithmetic/adder.v"         "EPFL-benchmarks/best_results/depth/adder_depth_2021.blif"; *)
    (* test "bar-depth"         "EPFL-benchmarks/arithmetic/bar.v"           "EPFL-benchmarks/best_results/depth/bar_depth_2015.blif"; *)
    (* test "div-depth"         "EPFL-benchmarks/arithmetic/div.v"           "EPFL-benchmarks/best_results/depth/div_depth_2021.blif"; *)
    (* test "hyp-depth"         "EPFL-benchmarks/arithmetic/hyp.v"           "EPFL-benchmarks/best_results/depth/hyp_depth_2021.blif"; *)
    (* test "log2-depth"        "EPFL-benchmarks/arithmetic/log2.v"          "EPFL-benchmarks/best_results/depth/log2_depth_2022.blif"; *)
    (* test "max-depth"         "EPFL-benchmarks/arithmetic/max.v"           "EPFL-benchmarks/best_results/depth/max_depth_2021.blif"; *)
    (* test "multiplier-depth"  "EPFL-benchmarks/arithmetic/multiplier.v"    "EPFL-benchmarks/best_results/depth/multiplier_depth_2022.blif"; *)
    (* test "sin-depth"         "EPFL-benchmarks/arithmetic/sin.v"           "EPFL-benchmarks/best_results/depth/sin_depth_2021.blif"; *)
    (* test "sqrt-depth"        "EPFL-benchmarks/arithmetic/sqrt.v"          "EPFL-benchmarks/best_results/depth/sqrt_depth_2021.blif"; *)
    (* test "square-depth"      "EPFL-benchmarks/arithmetic/square.v"        "EPFL-benchmarks/best_results/depth/square_depth_2022.blif"; *)
    (* test "arbiter-depth"     "EPFL-benchmarks/random_control/arbiter.v"   "EPFL-benchmarks/best_results/depth/arbiter_depth_2021.blif"; *)
    (* test "cavlc-depth"       "EPFL-benchmarks/random_control/cavlc.v"     "EPFL-benchmarks/best_results/depth/cavlc_depth_2018.blif"; *)
    (* test "ctrl-depth"        "EPFL-benchmarks/random_control/ctrl.v"      "EPFL-benchmarks/best_results/depth/ctrl_depth_2017.blif"; *)
    (* test "dec-depth"         "EPFL-benchmarks/random_control/dec.v"       "EPFL-benchmarks/best_results/depth/dec_depth_2018.blif"; *)
    (* test "i2c-depth"         "EPFL-benchmarks/random_control/i2c.v"       "EPFL-benchmarks/best_results/depth/i2c_depth_2022.blif"; *)
    (* test "int2float-depth"   "EPFL-benchmarks/random_control/int2float.v" "EPFL-benchmarks/best_results/depth/int2float_depth_2018.blif"; *)
    (* test "mem_ctrl-depth"    "EPFL-benchmarks/random_control/mem_ctrl.v"  "EPFL-benchmarks/best_results/depth/mem_ctrl_depth_2018.blif"; *)
    (* test "priority-depth"    "EPFL-benchmarks/random_control/priority.v"  "EPFL-benchmarks/best_results/depth/priority_depth_2022.blif"; *)
    (* test "router-depth"      "EPFL-benchmarks/random_control/router.v"    "EPFL-benchmarks/best_results/depth/router_depth_2021.blif"; *)
    (* test "voter-depth"       "EPFL-benchmarks/random_control/voter.v"     "EPFL-benchmarks/best_results/depth/voter_depth_2021.blif"; *)
    (* test "adder-size"        "EPFL-benchmarks/arithmetic/adder.v"         "EPFL-benchmarks/best_results/size/adder_size_2022.blif"; *)
    (* test "bar-size"          "EPFL-benchmarks/arithmetic/bar.v"           "EPFL-benchmarks/best_results/size/bar_size_2015.blif"; *)
    (* test "div-size"          "EPFL-benchmarks/arithmetic/div.v"           "EPFL-benchmarks/best_results/size/div_size_2021.blif"; *)
    (* test "hyp-size"          "EPFL-benchmarks/arithmetic/hyp.v"           "EPFL-benchmarks/best_results/size/hyp_size_2021.blif"; *)
    (* test "log2-size"         "EPFL-benchmarks/arithmetic/log2.v"          "EPFL-benchmarks/best_results/size/log2_size_2021.blif"; *)
    (* test "max-size"          "EPFL-benchmarks/arithmetic/max.v"           "EPFL-benchmarks/best_results/size/max_size_2018.blif"; *)
    (* test "multiplier-size"   "EPFL-benchmarks/arithmetic/multiplier.v"    "EPFL-benchmarks/best_results/size/multiplier_size_2022.blif"; *)
    (* test "sin-size"          "EPFL-benchmarks/arithmetic/sin.v"           "EPFL-benchmarks/best_results/size/sin_size_2021.blif"; *)
    (* test "sqrt-size"         "EPFL-benchmarks/arithmetic/sqrt.v"          "EPFL-benchmarks/best_results/size/sqrt_size_2021.blif"; *)
    (* test "square-size"       "EPFL-benchmarks/arithmetic/square.v"        "EPFL-benchmarks/best_results/size/square_size_2021.blif"; *)
    (* test "arbiter-size"      "EPFL-benchmarks/random_control/arbiter.v"   "EPFL-benchmarks/best_results/size/arbiter_size_2022.blif"; *)
    (* test "cavlc-size"        "EPFL-benchmarks/random_control/cavlc.v"     "EPFL-benchmarks/best_results/size/cavlc_size_2018.blif"; *)
    (* test "ctrl-size"         "EPFL-benchmarks/random_control/ctrl.v"      "EPFL-benchmarks/best_results/size/ctrl_size_2017.blif"; *)
    (* test "dec-size"          "EPFL-benchmarks/random_control/dec.v"       "EPFL-benchmarks/best_results/size/dec_size_2018.blif"; *)
    (* test "i2c-size"          "EPFL-benchmarks/random_control/i2c.v"       "EPFL-benchmarks/best_results/size/i2c_size_2018.blif"; *)
    (* test "int2float-size"    "EPFL-benchmarks/random_control/int2float.v" "EPFL-benchmarks/best_results/size/int2float_size_2020.blif"; *)
    (* test "mem_ctrl-size"     "EPFL-benchmarks/random_control/mem_ctrl.v"  "EPFL-benchmarks/best_results/size/mem_ctrl_size_2021.blif"; *)
    (* test "priority-size"     "EPFL-benchmarks/random_control/priority.v"  "EPFL-benchmarks/best_results/size/priority_size_2021.blif"; *)
    (* test "router-size"       "EPFL-benchmarks/random_control/router.v"    "EPFL-benchmarks/best_results/size/router_size_2018.blif"; *)
    (* test "voter-size"        "EPFL-benchmarks/random_control/voter.v"     "EPFL-benchmarks/best_results/size/voter_size_2022.blif" *)
