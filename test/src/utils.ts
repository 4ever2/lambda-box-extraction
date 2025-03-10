import path from "path";
import { Lang } from "./types";

export function replace_ext(file: string, ext: string): string {
    return path.join(path.dirname(file), path.basename(file, path.extname(file)) + ext);
}

export function print_line(s: string) {
  process.stdout.write(s + "\n");
}

export function lang_to_lbox_arg(lang: Lang): string {
  switch (lang) {
    case Lang.OCaml:
      return "ocaml";
    case Lang.C:
      return "c";
    case Lang.Wasm:
      return "wasm";
    case Lang.Rust:
      return "rust";
    case Lang.Elm:
      return "elm";
  }
}

export function lang_to_ext(lang: Lang): string {
  switch (lang) {
    case Lang.OCaml:
      return ".mlf";
    case Lang.C:
      return ".c";
    case Lang.Wasm:
      return ".wasm";
    case Lang.Rust:
      return ".rs";
    case Lang.Elm:
      return ".elm";
  }
}
