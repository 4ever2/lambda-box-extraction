type verbose = Normal | Quiet | Verbose

type copts = {verbose: verbose; debug: bool; output_file: string option}
let mk_copts verbose debug output_file = { verbose; debug; output_file }
