
let _ = print_endline "Expanding site variables..." in
let lexbuf = Lexing.from_channel stdin in
let ast = Kappa_grammar.Kparser4.model Kappa_grammar.Klexer4.token lexbuf in
let cst = Kappa_grammar.Cst.append_to_ast_compil ast Kappa_grammar.Ast.empty_compil in
Kappa_grammar.Ast.print_parsing_compil_kappa Format.std_formatter cst 

  