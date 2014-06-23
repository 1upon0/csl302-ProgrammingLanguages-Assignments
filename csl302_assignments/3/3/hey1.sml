
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
  
  datatype exp1= node of exp1*exp1|period|iff of exp1*exp1|comma of exp1*exp1|par of exp1|leaf of string 
end