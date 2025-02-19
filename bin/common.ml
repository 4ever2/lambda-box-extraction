type verbose = Normal | Quiet | Verbose

type copts = { verbose: verbose; debug: bool; output_file: string option; bypass_wf: bool }
let mk_copts verbose debug output_file bypass_wf = { verbose; debug; output_file; bypass_wf }

type erasure_opts = { typed : string option; optimize : bool }
let mk_erasure_opts typed optimize = { typed; optimize }
let mk_typed_erasure_opts optimize = { typed=None; optimize }

type certicoq_opts = { cps : bool }
let mk_certicoq_opts cps = { cps }


type import =
    FromRelativePath of string
  | FromAbsolutePath of string
  | FromLibrary of string * string option
