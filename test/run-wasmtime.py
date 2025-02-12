from wasmtime import Store, Module, Instance, Func, FuncType, ValType, Config, Engine
import pp
import sys
import time
import os

assert (
    len(sys.argv) == 2 or len(sys.argv) == 3
), "1: program, optionally 2: --precompile"

program = sys.argv[1]

precompile = False
if "--precompile" in sys.argv:
    precompile = True

config = Config()
config.wasm_tail_call = True


# mapping for pretty print functions
def pp_function_not_found(value, memory, store):
    print("pp_function not found, please specify in run-wasmtime.py")


pp_function_map = {
    "test": pp.print_bool
}


if program not in pp_function_map:
    print(f"Please specify pp function for {program} in run-wasmtime.py")
    exit(1)


# Old version of our module needed the imports
def print_int(n):
    sys.stdout.write(str(n))


def print_char(n):
    sys.stdout.write(str(chr(n)))


# Shared amongst objects
store = Store(Engine(config))
print_char_stdout = Func(store, FuncType([ValType.i32()], []), print_char)
print_int_stdout = Func(store, FuncType([ValType.i32()], []), print_int)

# Here we compile a `Module` which is then ready for instantiation
start_startup = time.time()

if precompile:
    module = Module.deserialize_file(
        store.engine, f"{program}.cwasm"
    )
else:
    module = Module.from_file(
        store.engine, f"{program}.wasm"
    )

# instantiate module
if len(module.imports) == 0:
    # new version
    instance = Instance(store, module, [])
elif len(module.imports) == 2:
    # old debugging version with the 2 imported functions
    instance = Instance(store, module, [print_char_stdout, print_int_stdout])

stop_startup = time.time()
time_startup = round((stop_startup - start_startup) * 1000)

# run main
start_main = time.time()
instance.exports(store)["main_function"](store)
stop_main = time.time()
time_main = round((stop_main - start_main) * 1000)

result = instance.exports(store)["result"].value(store)
sys.stdout.write("====> ")

# previously, the generated module contained a pp function
# this is no longer the case with the new representation of constructor values
if "pretty_print_constructor" in instance.exports(store):
    start_pp = time.time()
    instance.exports(store)["pretty_print_constructor"](store, result)
    stop_pp = time.time()
    time_pp = round((stop_pp - start_pp) * 1000)
else:
    start_pp = time.time()
    memory = instance.exports(store)["memory"]
    pp_function = pp_function_map[program]
    pp_function(result, memory, store)
    stop_pp = time.time()
    time_pp = round((stop_pp - start_pp) * 1000)

print()

try:
    # old name bytes_used renamed into mem_ptr
    bytes_used = instance.exports(store)["bytes_used"].value(store)
except KeyError:
    bytes_used = instance.exports(store)["mem_ptr"].value(store)

print(
    f"Benchmark {path}:"
    + "{{"
    + f'"time_startup": "{time_startup}", "time_main": "{time_main}", "time_pp": "{time_pp}", "bytes_used": "{bytes_used}", "program": "{program}"'
    + "}} ms, bytes."
)
