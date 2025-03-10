import { exit } from "process";
import { Lang, TestCase, ExecResult, SimpleType, ExecFailure } from "./types";
import { execSync } from "child_process";
import path from "path";
import { PathLike, unlink } from "fs";
import { lang_to_ext, lang_to_lbox_arg, print_line, replace_ext } from "./utils";
var exec_timeout = 30000; // 30 seconds
var compile_timeout = 30000; // 30 seconds
var remove_output = true;

var failed_tests = [];
function print_result(res: ExecResult, test: string) {
  switch (res.type) {
    case "error":
      failed_tests.push(test);
      switch (res.reason) {
        case "incorrect result":
          print_line(`expected ${res.expected} but received ${res.actual}`);
          break;
        case "runtime error":
          print_line(`"runtime error (${res.error})`);
          break;
        case "timeout":
          print_line("program timed out");
          break;
        case "compile error":
          print_line(`${res.compiler} failed with code ${res.code}`);
          print_line(res.error);
          break;
      }
      return false;
    case "success":
      print_line(`test succeeded in ${res.time} ms`);
      return true;
  }
}

function rm(f: PathLike) {
  if (!remove_output) return;

  unlink(f, (err) => {
    if (err) print_line(`could not remove ${f}`);
  });
}
/* (backend, lbox flags) pair configurations */
var test_configurations: TestConfiguration[] = [
  // [Lang.OCaml, ""],
  [Lang.C, "--cps"],
  [Lang.Wasm, "--cps"],
  [Lang.Wasm, ""],
  // [Lang.Rust, ""],
  // [Lang.Elm ""],
];
var tests: TestCase[] = [
  // Exceeds stack size
  // { src: "agda/BigDemo.ast", main: "", output_type: { type: "list", a_t: SimpleType.Nat }, expected_output: "", parameters: [] },

  // Not wellformed
  // { src: "agda/Equality.ast", main: "", output_type: SimpleType.Nat, expected_output: "", parameters: [] },

  // No main in program
  // { src: "agda/EtaCon.ast", main: "", output_type: SimpleType.Bool, expected_output: "???", parameters: [] },
  // { src: "agda/Test.ast", main: "", output_type: SimpleType.Bool, expected_output: "???", parameters: [] },
  // { src: "agda/Types.ast", main: "", output_type: SimpleType.Bool, expected_output: "???", parameters: [] },


  { src: "agda/Demo.ast", main: "main", output_type: { type: "list", a_t: SimpleType.Bool }, expected_output: "(cons true (cons false (cons true (cons false (cons true nil)))))", parameters: [] },
  { src: "agda/Demo2.ast", main: "main", output_type: { type: "list", a_t: { type: "list", a_t: SimpleType.Bool } }, expected_output: "(cons (cons true nil) (cons (cons false nil) nil))", parameters: [] },
  { src: "agda/Hello.ast", main: "", output_type: { type: "list", a_t: SimpleType.Nat }, expected_output: "(cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (cons (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))) nil))))))", parameters: [] },
  { src: "agda/Imports.ast", main: "", output_type: { type: "list", a_t: SimpleType.Nat }, expected_output: "(cons (S (S (S (S (S (S O)))))) nil)", parameters: [] },
  { src: "agda/Irr.ast", main: "", output_type: SimpleType.Other, expected_output: undefined, parameters: [] },
  { src: "agda/K.ast", main: "", output_type: SimpleType.Other, expected_output: undefined, parameters: [] },
  { src: "agda/Levels.ast", main: "", output_type: SimpleType.Nat, expected_output: "(S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))))))))))))", parameters: [] },
  { src: "agda/Map.ast", main: "", output_type: { type: "list", a_t: SimpleType.Nat }, expected_output: "(cons (S (S O)) (cons (S (S (S (S (S (S O)))))) (cons (S (S (S (S (S (S (S (S (S (S O)))))))))) nil)))", parameters: [] },
  { src: "agda/Mutual.ast", main: "", output_type: SimpleType.Nat, expected_output: "(S O)", parameters: [] },
  { src: "agda/Nat.ast", main: "", output_type: SimpleType.Nat, expected_output: "(S (S (S O)))", parameters: [] },
  { src: "agda/OddEven.ast", main: "main", output_type: SimpleType.Bool, expected_output: "true", parameters: [] },
  { src: "agda/PatternLambda.ast", main: "", output_type: SimpleType.Bool, expected_output: "false", parameters: [] },
  { src: "agda/Proj.ast", main: "", output_type: SimpleType.Bool, expected_output: "false", parameters: [] },
  { src: "agda/STLC.ast", main: "", output_type: SimpleType.Nat, expected_output: "(S (S O))", parameters: [] },
  { src: "agda/With.ast", main: "", output_type: { type: "list", a_t: SimpleType.Bool }, expected_output: "(cons true nil)", parameters: [] },
];

async function main() {
  for (var backend of test_configurations) {
    await run_tests(backend[0], backend[1], tests);
  }

  if (failed_tests.length == 0) {
    print_line("All tests passed");
    exit(0);
  } else {
    print_line(`${failed_tests.length} tests failed`);
    exit(1);
  }
}

main();
