open Yojson.Basic.Util
open Jit_eval

(* 定义测试用例类型 *)
type test_case = {
  dis : string;
  lp_std : int64 list;  (* eBPF 字节码 *)
  lx_std : int64 list;  (* JIT 编译后的机器码 *)
}

let green = "\027[32m"  (* ANSI green *)
let red = "\027[31m"    (* ANSI red *)
let reset = "\027[0m"   (* Reset color *)

let n = ref 0

let run_test_case test_case =
  let ebpf_prog         = Jit_eval.int_list_of_standard_int_list test_case.lp_std in
  let compiled_program  = Jit_eval.int_list_of_standard_int_list test_case.lx_std in
  let result            = Jit_eval.jit_evaluation ebpf_prog compiled_program in
  let color             = if result then green else red in
  n := !n + 1;
  Printf.printf "%s%d %-40s result: %s%b%s\n" color !n test_case.dis color result reset


let parse_test_case json =
  let dis = json |> member "dis" |> to_string in

  let lp_std_str_list = json |> member "lp_std" |> to_list |> List.map to_string in
  let lp_std = List.map Int64.of_string lp_std_str_list in

  let lx_std_int_list = json |> member "lx_std" |> to_list |> List.map to_int in
  let lx_std = List.map Int64.of_int lx_std_int_list in

  { dis; lp_std; lx_std }

let read_test_cases filename =
  let json = Yojson.Basic.from_file filename in
  match json with
  | `List test_cases_json -> List.map parse_test_case test_cases_json
  | _ -> failwith "Expected a list of test cases"

let () =
  let test_cases = read_test_cases "jit_in1.json" in
  List.iter run_test_case test_cases