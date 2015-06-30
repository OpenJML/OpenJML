{
  let p l = print_endline (Lexing.lexeme l);;
}

let ALPHA = ['a'-'z' 'A'-'Z' '\'' '~' '#' '$' '.' '?' '_' '^']
let ID = ALPHA (ALPHA | ['`' '0'-'9'])*
let WS = [' ' '\t' '\n' '\r' '(' ')']+
let INT = ['0'-'9']+

rule token = parse
    ID | INT          { p lexbuf; token lexbuf }
  | "/*"              { comment lexbuf }
  | WS | "//"[^'\n']* { token lexbuf }
  | ":=" | "==" | "!="
  | "::" | ":"
  | ";"
  | "[" | "]"
  | "{" | "}"
  | "!" | "-"
  | "%" | "/" | "+" | "*"
  | ","
  | "<==>"
  | "==>"
  | "<" | ">"
  | "<=" | ">="
  | "&&"
  | "||"         { p lexbuf; token lexbuf }
  | eof          { () }
  | _            
    { prerr_endline ("Unknown token: <" ^ (Lexing.lexeme lexbuf) ^ ">") }


and comment = parse
    "*/"         { token lexbuf }
  | eof          { prerr_endline "EOF in comment" }
  | _            { comment lexbuf }

{
  token (Lexing.from_channel stdin);;
}
