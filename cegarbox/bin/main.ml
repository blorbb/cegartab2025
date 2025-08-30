open Cegarbox
open Printf

let check fml =
  let solution = Solver.solve_fml fml in
  match solution with
  | Solver.Solution.Sat -> print_endline "SAT"
  | Solver.Solution.Unsat _ -> print_endline "UNSAT"
;;

let check_file filename =
  printf "%s: " filename;
  flush stdout;
  let file_text = In_channel.open_text filename in
  let lexbuf = Lexing.from_channel file_text in
  let fml =
    try Parser.file Lexer.next_token lexbuf with
    | Lexer.SyntaxError s ->
      print_string s;
      exit 1
  in
  check fml;
  print_string "unsat ";
  check (Fml.And (fml, Fml.Neg fml))
;;

let rec check_files = function
  | [] -> ()
  | a :: b ->
    check_file a;
    check_files b
;;

let () =
  check_files (Array.sub Sys.argv 1 ((Sys.argv |> Array.length) - 1) |> Array.to_list)
;;
