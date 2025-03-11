import { exit } from "process";
import { Lang, TestCase, ExecResult, SimpleType, ExecFailure, TestConfiguration } from "./types";
import { run_wasm } from "./wasm";
import { execSync } from "child_process";
import path from "path";
import { existsSync, mkdirSync, PathLike, unlink } from "fs";
import { lang_to_ext, lang_to_lbox_arg, print_line, replace_ext } from "./utils";
import { compile_c, set_c_env } from "./c";
import { compile_types } from "./ocaml";
import { compile_ocaml } from "./ocaml";


// Timeout used when executing the compiled code
var exec_timeout = 30000; // 30 seconds
// Timeout for the compilation phases
var compile_timeout = 30000; // 30 seconds
var remove_output = true;

// List of failed tests
var failed_tests: string[] = [];

var tmpdir = process.env.TMPDIR;


// Calls the lambda box compiler with
// `file` input program
// `lang` language that we compile to
// `opts` compiler options
// returns a string containing the location of the compiled code or an ExecFailure object
function compile_box(file: string, lang: Lang, opts: string): string | ExecFailure {
  const out_f = path.join(tmpdir, path.basename(replace_ext(file, lang_to_ext(lang))));
  const cmd = `dune exec --no-print-directory lbox -- ${lang_to_lbox_arg(lang)} ${file} -o ${out_f} ${opts}`;

  try {
    execSync(cmd, { stdio: "pipe", timeout: compile_timeout });
    return out_f;
  } catch (e) {
    if (e.signal == "SIGTERM") {
      return { type: "error", reason: "timeout" };
    }

    return { type: "error", reason: "compile error", compiler: "lbox", code: e.status, error: e.stdout.toString('utf8') };
  }
}


// Run the given executable and compare against the expected test result
function run_exec(file: string, test: TestCase): ExecResult {
  // Command to run
  const cmd = file;

  try {
    // Run and time the command
    const start_main = Date.now();
    const res = execSync(cmd, { stdio: "pipe", timeout: exec_timeout, encoding: "utf8" }).trim();
    const stop_main = Date.now();
    const time_main = stop_main - start_main;

    // Return success if there is no expected output to compare against or if the program
    // returns a type that we don't know how to print
    if (test.expected_output === undefined || test.output_type === SimpleType.Other) {
      return { type: "success", time: time_main };
    }

    // Compare output against the expected output
    if (res !== test.expected_output) {
      return { type: "error", reason: "incorrect result", actual: res, expected: test.expected_output };
    }

    return { type: "success", time: time_main };
  } catch (e) {
    if (e.signal == "SIGTERM") {
      return { type: "error", reason: "timeout" };
    }

    return { type: "error", reason: "runtime error", error: e }; // TODO
  }
}


// Print result of execution
function print_result(res: ExecResult, test: string): boolean {
  switch (res.type) {
    case "error":
      // Add failed test program to list of failed tests
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

// Compile and run all `tests` test programs with the `lang` backend and `opts` compiler options
async function run_tests(lang: Lang, opts: string, tests: TestCase[]) {
  print_line(`Running ${lang} tests with options "${opts}":`);
  switch (lang) {
    case Lang.OCaml:
      compile_types(compile_timeout);
      for (var test of tests) {
        process.stdout.write(`  ${test.src}: `);

        // Compile lbox
        const f_mlf = compile_box(test.src, Lang.OCaml, "");
        if (typeof f_mlf !== "string") {
          print_result(f_mlf, test.src);
          continue;
        }

        // Compile OCaml
        const f_exec = compile_ocaml(f_mlf, test, compile_timeout, tmpdir);
        if (typeof f_exec !== "string") {
          print_result(f_exec, test.src);
          continue;
        }

        // Run executable
        const res = run_exec(f_exec, test);

        // Report result
        print_result(res, test.src);
      }
      break;
    case Lang.C:
      await set_c_env(compile_timeout);
      for (var test of tests) {
        process.stdout.write(`  ${test.src}: `);

        // Compile lbox
        const f_c = compile_box(test.src, Lang.C, opts);
        if (typeof f_c !== "string") {
          print_result(f_c, test.src);
          continue;
        }

        // Compile C
        const f_exec = compile_c(f_c, test, compile_timeout);
        if (typeof f_exec !== "string") {
          print_result(f_exec, test.src);
          continue;
        }

        // Run executable
        const res = run_exec(f_exec, test);

        // Report result
        print_result(res, test.src);
      }
      break;
    case Lang.Wasm:
      for (var test of tests) {
        process.stdout.write(`  ${test.src}: `);

        // Compile lbox
        const f = compile_box(test.src, Lang.Wasm, opts);
        if (typeof f !== "string") {
          print_result(f, test.src);
          continue;
        }

        // Run wasm
        const res = await run_wasm(f, test);

        // Report result
        print_result(res, test.src);
      }
      break;
    case Lang.Rust:
      // TODO
      print_line("Not implemented yet");
      break;
    case Lang.Elm:
      // TODO
      print_line("Not implemented yet");
      break;

    default:
      print_line("Error: unkown backedn");
      exit(1);
  }
}

/* (backend, lbox flags) pair configurations */
var test_configurations: TestConfiguration[] = [
  [Lang.OCaml, ""],
  [Lang.C, "--cps"],
  [Lang.Wasm, "--cps"],
  [Lang.Wasm, ""],
  // [Lang.Rust, ""],
  // [Lang.Elm ""],
];

// List of programs to be tested
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
  // Create tmp dir
  if (tmpdir === undefined) {
    print_line("error: could not find tmpdir");
    exit(1);
  }
  tmpdir = path.join(tmpdir, "lbox/");
  if (!existsSync(tmpdir)) mkdirSync(tmpdir, { recursive: false });

  // For each test configuration run all test programs
  for (var backend of test_configurations) {
    await run_tests(backend[0], backend[1], tests);
  }

  // Report test suite result
  if (failed_tests.length == 0) {
    print_line("All tests passed");
    exit(0);
  } else {
    print_line(`${failed_tests.length} tests failed`);
    exit(1);
  }
}

main();
