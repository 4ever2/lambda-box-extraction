type verbose = Normal | Quiet | Verbose

type copts = { verbose: verbose; debug: bool; output_file: string option; bypass_wf: bool }
let mk_copts verbose debug output_file bypass_wf = { verbose; debug; output_file; bypass_wf }

type certicoq_opts = { cps : bool; typed : string option; optimize : bool }
let mk_certicoq_opts cps typed optimize = { cps; typed; optimize }

type typed_opts = { optimize : bool }
let mk_typed_opts optimize = { optimize }

type import =
    FromRelativePath of string
  | FromAbsolutePath of string
  | FromLibrary of string * string option
