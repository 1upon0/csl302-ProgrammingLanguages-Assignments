functor CalcLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : Calc_TOKENS
   end
 = 
struct
structure ParserData=
struct
structure Header = 
struct

open Ast

end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\022\000\002\000\021\000\000\000\
\\001\000\002\000\008\000\000\000\
\\001\000\003\000\034\000\004\000\036\000\000\000\
\\001\000\003\000\010\000\000\000\
\\001\000\003\000\011\000\000\000\
\\001\000\004\000\009\000\000\000\
\\001\000\005\000\025\000\007\000\024\000\000\000\
\\001\000\008\000\000\000\000\000\
\\030\000\002\000\008\000\000\000\
\\031\000\000\000\
\\032\000\000\000\
\\033\000\000\000\
\\035\000\000\000\
\\037\000\005\000\023\000\000\000\
\\038\000\000\000\
\\039\000\006\000\015\000\000\000\
\\040\000\000\000\
\\041\000\000\000\
\\042\000\000\000\
\\043\000\000\000\
\\044\000\000\000\
\\045\000\000\000\
\\046\000\006\000\015\000\000\000\
\\047\000\000\000\
\\048\000\000\000\
\"
val actionRowNumbers =
"\001\000\005\000\002\000\003\000\
\\004\000\008\000\015\000\001\000\
\\011\000\010\000\009\000\017\000\
\\016\000\000\000\012\000\013\000\
\\024\000\006\000\019\000\022\000\
\\023\000\001\000\018\000\000\000\
\\021\000\014\000\020\000\007\000"
val gotoT =
"\
\\001\000\027\000\002\000\005\000\003\000\004\000\004\000\003\000\
\\005\000\002\000\006\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\001\000\010\000\002\000\005\000\003\000\004\000\004\000\003\000\
\\005\000\002\000\006\000\001\000\000\000\
\\008\000\012\000\011\000\011\000\000\000\
\\005\000\015\000\007\000\014\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\009\000\018\000\010\000\017\000\012\000\016\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\008\000\024\000\011\000\011\000\000\000\
\\000\000\
\\005\000\015\000\007\000\025\000\000\000\
\\000\000\
\\009\000\026\000\012\000\016\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 28
val numrules = 19
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = string
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit ->  unit
 | COMPOPER of unit ->  (string) | OPER of unit ->  (string)
 | CONSTANT of unit ->  (real) | INT of unit ->  (int)
 | NAME of unit ->  (string) | VAR of unit ->  (string)
 | T of unit ->  (exp1) | S of unit ->  (exp1) | F of unit ->  (exp1)
 | TERM of unit ->  (exp1) | TUPLETERM of unit ->  (exp1)
 | BODY of unit ->  (exp1) | HEAD of unit ->  (exp1)
 | LITERAL of unit ->  (exp1) | RULE of unit ->  (exp1)
 | FACT of unit ->  (exp1) | STATEMENT of unit ->  (exp1)
 | PROGRAM of unit ->  (exp1 list)
end
type svalue = MlyValue.svalue
type result = exp1 list
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn _ => false
val preferred_change : (term list * term list) list = 
nil
val noShift = 
fn (T 7) => true | _ => false
val showTerminal =
fn (T 0) => "VAR"
  | (T 1) => "NAME"
  | (T 2) => "PERIOD"
  | (T 3) => "IF"
  | (T 4) => "COMMA"
  | (T 5) => "LPAREN"
  | (T 6) => "RPAREN"
  | (T 7) => "EOF"
  | (T 8) => "INT"
  | (T 9) => "CONSTANT"
  | (T 10) => "SPACE"
  | (T 11) => "NEWLINE"
  | (T 12) => "LBRACKET"
  | (T 13) => "RBRACKET"
  | (T 14) => "OPER"
  | (T 15) => "COMPOPER"
  | (T 16) => "VERTICAL"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 16) $$ (T 13) $$ (T 12) $$ (T 11) $$ (T 10) $$ (T 7) $$ (T 6)
 $$ (T 5) $$ (T 4) $$ (T 3) $$ (T 2)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (fileName):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.STATEMENT STATEMENT1, STATEMENT1left, 
STATEMENT1right)) :: rest671)) => let val  result = MlyValue.PROGRAM
 (fn _ => let val  (STATEMENT as STATEMENT1) = STATEMENT1 ()
 in ([STATEMENT])
end)
 in ( LrTable.NT 0, ( result, STATEMENT1left, STATEMENT1right), 
rest671)
end
|  ( 1, ( ( _, ( MlyValue.PROGRAM PROGRAM1, _, PROGRAM1right)) :: ( _,
 ( MlyValue.STATEMENT STATEMENT1, STATEMENT1left, _)) :: rest671)) =>
 let val  result = MlyValue.PROGRAM (fn _ => let val  (STATEMENT as 
STATEMENT1) = STATEMENT1 ()
 val  (PROGRAM as PROGRAM1) = PROGRAM1 ()
 in (STATEMENT::PROGRAM)
end)
 in ( LrTable.NT 0, ( result, STATEMENT1left, PROGRAM1right), rest671)

end
|  ( 2, ( ( _, ( _, _, PERIOD1right)) :: ( _, ( MlyValue.FACT FACT1, 
FACT1left, _)) :: rest671)) => let val  result = MlyValue.STATEMENT
 (fn _ => let val  (FACT as FACT1) = FACT1 ()
 in (FACT)
end)
 in ( LrTable.NT 1, ( result, FACT1left, PERIOD1right), rest671)
end
|  ( 3, ( ( _, ( _, _, PERIOD1right)) :: ( _, ( MlyValue.RULE RULE1, 
RULE1left, _)) :: rest671)) => let val  result = MlyValue.STATEMENT
 (fn _ => let val  (RULE as RULE1) = RULE1 ()
 in (RULE)
end)
 in ( LrTable.NT 1, ( result, RULE1left, PERIOD1right), rest671)
end
|  ( 4, ( ( _, ( MlyValue.LITERAL LITERAL1, LITERAL1left, 
LITERAL1right)) :: rest671)) => let val  result = MlyValue.FACT (fn _
 => let val  (LITERAL as LITERAL1) = LITERAL1 ()
 in (LITERAL)
end)
 in ( LrTable.NT 2, ( result, LITERAL1left, LITERAL1right), rest671)

end
|  ( 5, ( ( _, ( MlyValue.BODY BODY1, _, BODY1right)) :: _ :: ( _, ( 
MlyValue.HEAD HEAD1, HEAD1left, _)) :: rest671)) => let val  result = 
MlyValue.RULE (fn _ => let val  (HEAD as HEAD1) = HEAD1 ()
 val  (BODY as BODY1) = BODY1 ()
 in (iff(HEAD,BODY))
end)
 in ( LrTable.NT 3, ( result, HEAD1left, BODY1right), rest671)
end
|  ( 6, ( ( _, ( MlyValue.LITERAL LITERAL1, LITERAL1left, 
LITERAL1right)) :: rest671)) => let val  result = MlyValue.HEAD (fn _
 => let val  (LITERAL as LITERAL1) = LITERAL1 ()
 in (LITERAL)
end)
 in ( LrTable.NT 5, ( result, LITERAL1left, LITERAL1right), rest671)

end
|  ( 7, ( ( _, ( MlyValue.LITERAL LITERAL1, LITERAL1left, 
LITERAL1right)) :: rest671)) => let val  result = MlyValue.BODY (fn _
 => let val  (LITERAL as LITERAL1) = LITERAL1 ()
 in (LITERAL)
end)
 in ( LrTable.NT 6, ( result, LITERAL1left, LITERAL1right), rest671)

end
|  ( 8, ( ( _, ( MlyValue.BODY BODY1, _, BODY1right)) :: _ :: ( _, ( 
MlyValue.LITERAL LITERAL1, LITERAL1left, _)) :: rest671)) => let val  
result = MlyValue.BODY (fn _ => let val  (LITERAL as LITERAL1) = 
LITERAL1 ()
 val  (BODY as BODY1) = BODY1 ()
 in (comma(LITERAL,BODY))
end)
 in ( LrTable.NT 6, ( result, LITERAL1left, BODY1right), rest671)
end
|  ( 9, ( ( _, ( MlyValue.NAME NAME1, NAME1left, NAME1right)) :: 
rest671)) => let val  result = MlyValue.LITERAL (fn _ => let val  (
NAME as NAME1) = NAME1 ()
 in (leaf(NAME))
end)
 in ( LrTable.NT 4, ( result, NAME1left, NAME1right), rest671)
end
|  ( 10, ( ( _, ( MlyValue.TUPLETERM TUPLETERM1, _, TUPLETERM1right))
 :: ( _, ( MlyValue.NAME NAME1, NAME1left, _)) :: rest671)) => let
 val  result = MlyValue.LITERAL (fn _ => let val  (NAME as NAME1) = 
NAME1 ()
 val  (TUPLETERM as TUPLETERM1) = TUPLETERM1 ()
 in (node(leaf(NAME),TUPLETERM))
end)
 in ( LrTable.NT 4, ( result, NAME1left, TUPLETERM1right), rest671)

end
|  ( 11, ( ( _, ( MlyValue.S S1, S1left, S1right)) :: rest671)) => let
 val  result = MlyValue.TUPLETERM (fn _ => let val  (S as S1) = S1 ()
 in (S)
end)
 in ( LrTable.NT 7, ( result, S1left, S1right), rest671)
end
|  ( 12, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.F F1, _, _))
 :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result = 
MlyValue.S (fn _ => let val  (F as F1) = F1 ()
 in (par(F))
end)
 in ( LrTable.NT 10, ( result, LPAREN1left, RPAREN1right), rest671)

end
|  ( 13, ( ( _, ( MlyValue.TERM TERM1, TERM1left, TERM1right)) :: 
rest671)) => let val  result = MlyValue.F (fn _ => let val  (TERM as 
TERM1) = TERM1 ()
 in (TERM)
end)
 in ( LrTable.NT 9, ( result, TERM1left, TERM1right), rest671)
end
|  ( 14, ( ( _, ( MlyValue.TERM TERM1, _, TERM1right)) :: _ :: ( _, ( 
MlyValue.F F1, F1left, _)) :: rest671)) => let val  result = 
MlyValue.F (fn _ => let val  (F as F1) = F1 ()
 val  (TERM as TERM1) = TERM1 ()
 in (comma(F,TERM))
end)
 in ( LrTable.NT 9, ( result, F1left, TERM1right), rest671)
end
|  ( 15, ( ( _, ( MlyValue.TUPLETERM TUPLETERM1, _, TUPLETERM1right))
 :: ( _, ( MlyValue.NAME NAME1, NAME1left, _)) :: rest671)) => let
 val  result = MlyValue.T (fn _ => let val  (NAME as NAME1) = NAME1 ()
 val  (TUPLETERM as TUPLETERM1) = TUPLETERM1 ()
 in (node(leaf(NAME),TUPLETERM) )
end)
 in ( LrTable.NT 11, ( result, NAME1left, TUPLETERM1right), rest671)

end
|  ( 16, ( ( _, ( MlyValue.NAME NAME1, NAME1left, NAME1right)) :: 
rest671)) => let val  result = MlyValue.TERM (fn _ => let val  (NAME
 as NAME1) = NAME1 ()
 in (leaf(NAME))
end)
 in ( LrTable.NT 8, ( result, NAME1left, NAME1right), rest671)
end
|  ( 17, ( ( _, ( MlyValue.VAR VAR1, VAR1left, VAR1right)) :: rest671)
) => let val  result = MlyValue.TERM (fn _ => let val  (VAR as VAR1) =
 VAR1 ()
 in (leaf(VAR))
end)
 in ( LrTable.NT 8, ( result, VAR1left, VAR1right), rest671)
end
|  ( 18, ( ( _, ( MlyValue.T T1, T1left, T1right)) :: rest671)) => let
 val  result = MlyValue.TERM (fn _ => let val  (T as T1) = T1 ()
 in (T)
end)
 in ( LrTable.NT 8, ( result, T1left, T1right), rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.PROGRAM x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : Calc_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun VAR (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VAR (fn () => i),p1,p2))
fun NAME (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.NAME (fn () => i),p1,p2))
fun PERIOD (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun IF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun INT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.INT (fn () => i),p1,p2))
fun CONSTANT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.CONSTANT (fn () => i),p1,p2))
fun SPACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun NEWLINE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun LBRACKET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun RBRACKET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun OPER (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.OPER (fn () => i),p1,p2))
fun COMPOPER (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.COMPOPER (fn () => i),p1,p2))
fun VERTICAL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID,p1,p2))
end
end
