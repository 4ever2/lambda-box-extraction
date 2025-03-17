import { exit } from "process";
import { Lang, TestCase, ExecResult, SimpleType, ExecFailure } from "./types";
import { run_wasm } from "./wasm";
import { execSync } from "child_process";
import path from "path";
import { existsSync, mkdirSync } from "fs";
import { lang_to_ext, lang_to_lbox_arg, print_line, replace_ext } from "./utils";
import { compile_c, set_c_env } from "./c";
import { compile_types } from "./ocaml";
import { compile_ocaml } from "./ocaml";
import { compile_rust, prepare_cargo, run_rust } from "./rust";
import { prepare_elm_project, run_elm } from "./elm";
import { test_configurations, tests } from "./tests";


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
function compile_box(file: string, outdir: string, lang: Lang, opts: string): string | ExecFailure {
  const out_f = path.join(outdir, path.basename(replace_ext(file, lang_to_ext(lang))));
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
    if (res !== test.expected_output[0]) {
      return { type: "error", reason: "incorrect result", actual: res, expected: test.expected_output[0] };
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
async function run_tests(lang: Lang, n: string, opts: string, tests: TestCase[]) {
  print_line(`Running ${lang}${n.length > 0 ? "-"+n : ""} tests:`);
  switch (lang) {
    case Lang.OCaml:
      compile_types(compile_timeout);
      for (var test of tests) {
        if (test.src === undefined) continue;
        process.stdout.write(`  ${test.src}: `);

        // Compile lbox
        const f_mlf = compile_box(test.src, tmpdir, Lang.OCaml, opts);
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
        if (test.src === undefined) continue;
        process.stdout.write(`  ${test.src}: `);

        // Compile lbox
        const f_c = compile_box(test.src, tmpdir, Lang.C, opts);
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
        if (test.src === undefined) continue;
        process.stdout.write(`  ${test.src}: `);

        // Compile lbox
        const f = compile_box(test.src, tmpdir, Lang.Wasm, opts);
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
      var otudir = prepare_cargo(tmpdir);
      let cargodir = path.join(tmpdir, "rust/");

      for (var test of tests) {
        if (test.tsrc === undefined) continue;
        process.stdout.write(`  ${test.tsrc}: `);

        // Compile lbox
        const f_rs = compile_box(test.tsrc, otudir, Lang.Rust, opts);
        if (typeof f_rs !== "string") {
          print_result(f_rs, test.tsrc);
          continue;
        }

        // Compile Rust
        const err = compile_rust(f_rs, cargodir, test, compile_timeout);
        if (err !== undefined) {
          print_result(err, test.tsrc);
          continue;
        }

        // Run Rust
        const res = run_rust(f_rs, cargodir, test, exec_timeout);

        // Report result
        print_result(res, test.tsrc);
      }
      break;
    case Lang.Elm:
      var otudir = prepare_elm_project(tmpdir);
      let elmdir = path.join(tmpdir, "elm/");

      for (var test of tests) {
        if (test.tsrc === undefined) continue;
        process.stdout.write(`  ${test.tsrc}: `);

        // Compile lbox
        const f_elm = compile_box(test.tsrc, otudir, Lang.Elm, opts);
        if (typeof f_elm !== "string") {
          print_result(f_elm, test.tsrc);
          continue;
        }

        // Run Elm
        const res = run_elm(f_elm, elmdir, test, exec_timeout);

        // Report result
        print_result(res, test.tsrc);
      }
      break;

    default:
      print_line("Error: unkown backend");
      exit(1);
  }
}

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
    await run_tests(backend[0], backend[1], backend[2], tests);
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
