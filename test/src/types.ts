export type Timeout = { type: "error", reason: "timeout" };
export type RuntimeError = { type: "error", reason: "runtime error", error: string };
export type CompileError = { type: "error", reason: "compile error", compiler: string, code: number, error: string };
export type IncorrectResult = { type: "error", reason: "incorrect result", expected: string, actual: string };
export type ExecFailure = Timeout | RuntimeError | CompileError | IncorrectResult;
export type ExecSuccess = { type: "success", time: number }
export type ExecResult = ExecFailure | ExecSuccess;

export enum SimpleType {
  Nat,
  Bool,
  UInt63,
  Other /* For programs using types not in the list, when using this type the output won't be checked */
}

export type ProgramType =
  SimpleType
  | { type: "list", a_t: ProgramType }
  | { type: "option", a_t: ProgramType }
  | { type: "prod", a_t: ProgramType, b_t: ProgramType }

export enum Lang {
  OCaml = "OCaml",
  C = "C",
  Wasm = "WebAssembly",
  Rust = "Rust",
  Elm = "Elm",
}

export type TestCase = {
  src: string,
  main: string,
  output_type: ProgramType,
  expected_output?: string,
  parameters?: ProgramType[],
}

export type TestConfiguration = [Lang, string]
