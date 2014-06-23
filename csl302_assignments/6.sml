exception Match
exception NotExist

datatype exp = mult of exp*exp|add of exp*exp|Variable of string|Unit of unit
		|Integ of int|Boool of bool|tuple of exp list|iff of exp*exp*exp |lett of def*exp|Lambda of string*exp|Funct of exp*exp
and def = equal of string*exp|sequential of def list|parallel of def list|locall of def*def

datatype opcodes = AP|RET|BIND of string|CLOS of string*opcodes list|LOAD1 of int|LOAD2 of bool|PLUS|SAVE
			|TUPLE of int|TIMES|UNIT|COND of opcodes list * opcodes list|LOOKUP of string|POP of int

datatype output= Uni of unit|Integer of int|Boolean of bool|Tuple of output list|Varr of string

fun augment(f,g)= fn(a) => f(a) handle Match=> g(a)


fun push(w,[])=[w]
|push(w,x) = rev(rev(x) @ [w] )



fun pop(x::xs) = (x,xs)

fun callength(a,[]) = a
|callength(a,equal(x,s)::xs) = callength(a+1,xs)
|callength(a,sequential(y::ys) :: xs ) = let val k = callength(0,y::ys) in  callength(a+k , xs) end
|callength(a,parallel(y::ys) :: xs ) = let val k = callength(0,y::ys) in  callength(a+k , xs) end



			
fun compile(Unit(()))=[UNIT]
|compile(Integ(a))=[LOAD1(a)]
|compile(Boool(a))=[LOAD2(a)]
|compile(mult(a,b))=compile(a) @ compile(b) @ [TIMES]
|compile(add(a,b))=compile(a) @ compile(b) @ [PLUS]
|compile(Variable(a))=[LOOKUP(a)]
|compile(tuple(x::xs))= let val l = length(x::xs) 

	fun help(l,[]) = [TUPLE(l)]
	|help(l,x::xs) = compile(x) @ help(l,xs)

in  help(l,x::xs) end

|compile(iff(a,b,c))=compile(a) @ [ COND(compile(b),compile(c))]
|compile(Lambda(x,e))=[CLOS(x,compile(e)@[RET])]
|compile(Funct(e1,e2))= compile(e1)@compile(e2)@[AP]

|compile(lett(equal(x,e1),e2))= [SAVE]@compile(e1) @ [BIND(x)] @ compile(e2) @ [POP(1)]


|compile(lett( sequential(d::xs)  ,e2))= let val l = callength (0,d::xs)


		fun helpir(sequential([]))= []
		|helpir( sequential(equal(x,e1)::xs))=compile(e1)@[BIND(x)]@  helpir( sequential(xs))
		|helpir( sequential(parallel(y::ys)::xs))=   help1(parallel(y::ys)) @ help2(parallel(rev(y::ys)))  @  helpir(sequential(xs))

		and	
		 help1( parallel([]) )= []
		|help1(parallel(equal(x,e1)::xs) )=compile(e1)@ help1( parallel(xs) )
		|help1(parallel(sequential(y::ys)::xs) )= helpir(sequential(y::ys)) @ help1(parallel(xs)) 

		and help2( parallel([])  )= []
		|help2( parallel(equal(x,e1)::xs))=[BIND(x)]@ help2(parallel(xs)  )
		|help2( parallel(sequential(y::ys)::xs))= help2( parallel(xs))
			
			
			
in  	[SAVE]@ helpir(sequential(d::xs)) @ compile(e2) @[POP(l)]	  end




|compile(lett( parallel(d::xs)  ,e2))= let val l = callength (0,d::xs)


		fun helpir(sequential([]))= []
		|helpir( sequential(equal(x,e1)::xs))=compile(e1)@[BIND(x)]@  helpir( sequential(xs))
		|helpir( sequential(parallel(y::ys)::xs))=   help1(parallel(y::ys)) @ help2(parallel(rev(y::ys)))  @  helpir(sequential(xs))

		and	
		 help1( parallel([]) )= []
		|help1(parallel(equal(x,e1)::xs) )=compile(e1)@ help1( parallel(xs) )
		|help1(parallel(sequential(y::ys)::xs) )= helpir(sequential(y::ys)) @ help1(parallel(xs)) 

		and help2( parallel([])  )= []
		|help2( parallel(equal(x,e1)::xs))=[BIND(x)]@ help2(parallel(xs)  )
		|help2( parallel(sequential(y::ys)::xs))= help2( parallel(xs))
			
			
			
in  	[SAVE]@ help1(parallel(d::xs))@ help2(parallel(rev(d::xs))) @ compile(e2) @[POP(l)]	  end









fun helpout(0,x::xs) = []
|helpout(0,[])=[]
|helpout(n,x::xs) = let val (k,k1,k2) = x in [k]@helpout(n-1,xs) end

fun remove(n,[]) = []
|remove(n,x::xs) = if n=0 then x::xs else remove(n-1,xs)




fun machine (s,e,[],d)= (s,e,d)
|machine(s,e,CLOS(x,c)::ys,d) = machine( push((Varr(x),c,e),s) , e,ys,d)
|machine(s,e,AP::ys,d) = let val ((q,a,z),rest)=pop(s) ; val ((Varr(q2),a2,z2),rest2)=pop(rest) in 
machine([],augment(fn(v)=>if v=q2 then q else raise Match , z2),a2,push((rest2,e,ys),d)) end

|machine(s,e,RET::ys,d) = let val ((a,b,c),df) = pop(d) ; val (u1,h) = pop(s) in 
			machine( push(u1,a) , b , c , df ) end
			
|machine(s,e,LOAD1(a)::ys,d) = machine(push((Integer(a),[],fn(a)=>Boolean(false)),s) ,e,ys,d)
|machine(s,e,LOAD2(a)::ys,d) = machine(push((Boolean(a),[],fn(a)=>Boolean(false)),s) ,e,ys,d)

|machine((Integer(a),w,q)::(Integer(b),f,f4)::s,e,PLUS::ys,d) = machine((Integer(a+b),f,f4)::s,e,ys,d)
|machine((Integer(a),w,q)::(Integer(b),f,f4)::s,e,TIMES::ys,d) = machine((Integer(a*b),f,f4)::s,e,ys,d)

|machine(s,e,LOOKUP(x)::ys,d) =    machine(push((e(x),[],fn(a)=>Boolean(false)),s),e,ys,d) 

|machine(s,e,TUPLE(n)::ys,d) = let val oo =helpout(n,s) ;  val s1=remove(n,s) ; val l=Tuple(oo) in    machine( push((l,[],fn(a)=>Boolean(false)),s1) , e , ys , d) end

|machine( (Boolean(true),w,w1)::s , e , COND(c11,c21)::ys,d ) = machine( s , e , c11@ys , d)
|machine( (Boolean(false),w,w1)::s , e , COND(c11,c21)::ys,d ) = machine( s , e , c21@ys , d)
|machine(s,e,UNIT::ys,d    )= machine (   push( (Uni(()),[],fn(a)=>Boolean(false)),s ) ,e,ys,d )


|machine(s,e,SAVE::c,d) = machine(s,e,c, push( (s,e,c)   ,d)  )
|machine(s,e,POP(n)::c,d) =    let val ( (s2,e2,c2) ,d2)=pop(d)   in    machine(s,e2,c,d2)  end
|machine((a,w,q)::s,e,BIND(x)::ys,d)= machine(s,   augment( fn(aa)=>if aa=x then a else raise Match  ,e)    ,ys,d)


(*  -- This method of popping is wrong--

|machine(s,e,POP(1)::c,r::d) =   let val (e1,e2,e3)=r ; val (Varr(k1),k2,k3)=hd(e1)  in  machine(s, fn(a3)=>   if a3=k1 then raise Match else e(a3) , c , d ) end
|machine(s,e,POP(n)::c,r::d) =  let val (e1,e2,e3)=r ; val (Varr(k1),k2,k3)=hd(e1)  in  machine(s, fn(a3)=>   if a3=k1 then raise Match else e(a3) ,POP(n-1):: c , d ) end

*)
			











datatype outinL = Integr of int|Boolan of bool|Closure of (string->outinL)*exp


(*Note in below , h is a table which takes string as input and gives output as closures.or values  -- outinL type*)

fun pureLmachine(Closure(h,Funct(e1,e2)),s)= pureLmachine( Closure(h,e1), push(Closure(h,e2),s)   )

|pureLmachine(Closure(h,Lambda(x,e)),Closure(a,b)::s)= pureLmachine(Closure(  augment( fn(s)=>if s=x then Closure(a,b) else raise Match , h )     ,e),s)

|pureLmachine( Closure(h,Lambda(x,e)), s) = ( Closure(h,Lambda(x,e)),s)

|pureLmachine(Closure(h   ,Variable(x)) ,s)=   pureLmachine(  h(x)  , s      ) (* handle Match=> ( Closure(h,Variable(x)),s)
*)
|pureLmachine( Closure(h,Integ(a)) , s) = ( Integr(a) , s)
|pureLmachine( Closure(h,Boool(a)) , s) = ( Boolan(a) , s)

|pureLmachine( Integr(a) , s) = ( Integr(a) , s)
|pureLmachine( Boolan(a) , s) = ( Boolan(a) , s)

	

(*trial cases*)

val keshav = compile( Funct(Lambda("x",add(Variable("x"),Variable("y"))),Integ(4))  )
val ker = compile ( lett( equal("x",Integ(6))  ,Variable("x")))
val kery = compile ( lett( parallel([  sequential([ equal("w",Integ(34)) ,equal("r",Variable("w"))  ])     ,equal("x",Integ(4)) ,equal("z",Variable("y"))  ])  ,mult(Variable("z"),Variable("r")	) ) ) 

val c1 = compile (Integ(3))
val c2 = compile (Boool(true))
val c3 = compile ( mult( Integ(5) ,Integ(3)))
val c4 = compile (tuple([ Integ(2),Integ(4) ]))
val c5 = compile (iff(Boool(true),Integ(4),Integ(5)))

val doing = machine([],fn(a)=>if a="y" then Integer(3) else raise Match  ,    kery(* can ker/kery/c1/c2/c3/c4/c5 *)  , [])


val keshav1 = pureLmachine(  Closure(fn(a)=>if a="y" then Integr(3) else raise Match , Funct(Lambda("x",Variable("x")) ,Lambda("y",Variable("y") ) )         )     ,[] )




