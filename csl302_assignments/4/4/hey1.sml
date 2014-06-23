
structure Tokens=
struct
type svalue=int
datatype token
  = VAR of string
  | NAME of string
  | INT of int
  | CONSTANT of real
  | SPACE
  | NEWLINE
  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | COMMA
  | PERIOD
  | OPER of string
  | COMPOPER of string
  | IF
  | VERTICAL
  | EOF
  
  end
  
  
  
  structure  Ast =
  struct
  
  datatype exp1= leaf of string| node of string*exp1 list

  
end