open TextIO;
use "my.lex.sml";
open KeshavLex;
open UserDeclarations;
val lexer = makeLexer( fn n => valOf(inputLine( stdIn ) ));
lexer();
