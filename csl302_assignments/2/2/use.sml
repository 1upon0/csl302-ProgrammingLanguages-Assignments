open TextIO;
use "keshav.lex.sml";
open KeshavLex;
open UserDeclarations;
val lexer = makeLexer( fn n => valOf(inputLine( stdIn ) ));
lexer();
