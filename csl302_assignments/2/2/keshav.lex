datatype lexresult
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
  
val linenum = ref 1
val error = fn x => output(stdOut,x ^ "\n")
val eof = fn () => EOF
fun inc( i ) = i := !(i) + 1

fun cal(k,r) = if k=0 then r else  cal(k-1,(real)10*r)
fun final2(x,y)=  let val k = length(y);  val k1=foldl(fn(a,r)=>ord(a)-ord(#"0")+10*r) 0 (y)  ; val k2= real(k1)/cal(k,1.0) ;  val k3=foldl(fn(a,r)=>ord(a)-ord(#"0")+10*r) 0 (x) in  (real) k3 +  k2   end
fun final(x,y)=final2(rev(x),y)
fun doit2(y ,x::xs) = if x= #"."  then final(y,xs) else doit2(x::y , xs)
fun doit(c)  =   doit2 ([],explode c)

%%

%structure KeshavLex

alphanumeral=[A-Za-z0-9];
capital=[A-Z];
small=[a-z];
prime=['];
digit=[0-9];
operator=[-+/*%];
ws=[\ \t];

%%

\n              => (NEWLINE;inc linenum;lex());
{ws}+           => (SPACE);

":-"|"if"   => (IF);
{operator}|"div"|"mod"      => (OPER yytext);
"<"|">"|"="|"<="|">="    =>(COMPOPER yytext);

({capital}+({prime}|"_"|{alphanumeral})*   ({prime}|{alphanumeral})+  )|  {capital}     => (VAR yytext);
({small}+({prime}|"_"|{alphanumeral})*   ({prime}|{alphanumeral})+   )| {small}     => (NAME yytext);


{digit}+ =>  (INT(foldl(fn(a,r)=>ord(a)-ord(#"0")+10*r) 0 (explode yytext)));
{digit}+("."){digit}+   =>   (CONSTANT (doit(yytext))) ;

"."             => (PERIOD);
","             => (COMMA); 
"("             => (LPAREN);
")"             => (RPAREN);
"["             => (LBRACKET);
"]"             => (RBRACKET);
"|"             => (VERTICAL);

.               => (error ("lambda: ignoring bad character "^yytext); lex());