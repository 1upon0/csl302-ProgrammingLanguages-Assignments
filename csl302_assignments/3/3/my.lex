
  structure T = Tokens

  type pos = int
  type svalue = T.svalue
  type ('a,'b) token = ('a,'b) T.token
type lexresult  = (svalue,pos) token
type lexarg = string;
type arg = lexarg;
val lin = ref 1;
val col = ref 0;
val eolpos = ref 0;
val error = fn (x,a,b) => TextIO.output(TextIO.stdOut,x ^ "\n");
val eof = fn fileName => T.EOF(!lin,!col);
fun inc( i ) = i := !(i) + 1;

fun cal(k,r) = if k=0 then r else  cal(k-1,(real)10*r);
fun final2(x,y)=  let val k = length(y);  val k1=foldl(fn(a,r)=>ord(a)-ord(#"0")+10*r) 0 (y)  ; val k2= real(k1)/cal(k,1.0) ;  val k3=foldl(fn(a,r)=>ord(a)-ord(#"0")+10*r) 0 (x) in  (real) k3 +  k2   end;
fun final(x,y)=final2(rev(x),y);
fun doit2(y ,x::xs) = if x= #"."  then final(y,xs) else doit2(x::y , xs);
fun doit(c)  =   doit2 ([],explode c);



%%
%full
%header (functor CalcLexFun(structure Tokens: Calc_TOKENS));
%arg ("test.txt")  ;

capital=[A-Z];
alphanumeral=[A-Za-z0-9];

small=[a-z];
prime=['];
digit=[0-9];
operator=[-+/*%];
ws=[\ \t];

%%

\n              => (inc lin;eolpos:=yypos+size yytext; continue ());
{ws}+           => (continue());

":-"|"if"   => (col:=yypos-(!eolpos);T.IF(!lin,!col));
{operator}|"div"|"mod"      => (col:=yypos-(!eolpos);T.OPER (yytext,!lin,!col));
"<"|">"|"="|"<="|">="    =>(col:=yypos-(!eolpos);T.COMPOPER (yytext,!lin,!col));

({capital}+({prime}|"_"|{alphanumeral})*   ({prime}|{alphanumeral})+  )|  {capital}     => (col:=yypos-(!eolpos);T.VAR (yytext,!lin,!col));
({small}+({prime}|"_"|{alphanumeral})*   ({prime}|{alphanumeral})+   )| {small}     => (col:=yypos-(!eolpos);T.NAME (yytext,!lin,!col));


{digit}+ => (col:=yypos-(!eolpos);     T.INT( foldl(fn(a,r)=>ord(a)-ord(#"0")+10*r) 0 (explode yytext),!lin,!col )       );
{digit}+("."){digit}+   => (col:=yypos-(!eolpos);  T.CONSTANT (doit(yytext),!lin,!col)  ) ;

"."             => (col:=yypos-(!eolpos);T.PERIOD(!lin,!col));
","             => (col:=yypos-(!eolpos);T.COMMA(!lin,!col)); 
"("             => (col:=yypos-(!eolpos);T.LPAREN(!lin,!col));
")"             => (col:=yypos-(!eolpos);T.RPAREN(!lin,!col));
"["             => (col:=yypos-(!eolpos);T.LBRACKET(!lin,!col));
"]"             => (col:=yypos-(!eolpos);T.RBRACKET(!lin,!col));
"|"             => (col:=yypos-(!eolpos);T.VERTICAL(!lin,!col));

.               => (error ("keshav: ignoring bad character "^yytext,!lin,!col); continue());