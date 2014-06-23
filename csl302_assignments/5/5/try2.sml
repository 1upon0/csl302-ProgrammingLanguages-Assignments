

exception NotExist
exception Match
fun augment(f,g)= fn(a) => f(a) handle Match=> g(a)

datatype exp = mult of exp*exp|add of exp*exp|Variable of string|Unit of unit
		|Integ of int|Boool of bool|tuple of exp list|proj of int* exp|iff of exp*exp*exp |lett of def*exp
and def = equal of string*exp|sequential of def list|parallel of def list|locall of def*def

datatype output= Uni of unit|Integer of int|Boolean of bool|Tuple of output list

fun value(p,Integ(a)) = Integer(a)
|value(p,Boool(a))= Boolean(a)
|value(p,Unit(()))= Uni(())
|value(p,Variable(x))= p(x)
|value(p,add(a,b))= let fun final((Integer(a),Integer(b)))=Integer(a+b) ; 
			fun helper(p,a,b)=final(value(p,a),value(p,b)) in helper(p,a,b) end
|value(p,mult(a,b))= let fun final((Integer(a),Integer(b)))=Integer(a*b) ; 
			fun helper(p,a,b)=final(value(p,a),value(p,b)) in helper(p,a,b) end			
|value(p,tuple(x::xs))= let fun helper(p,tuple(x::[]))=[value(p,x)]
				|helper(p,tuple(x::xs))=value(p,x)::helper(p,tuple(xs)) in
	Tuple( helper(p,tuple(x::xs)) ) end

|value(p,proj(i,e))= let fun helper(i,Tuple(x::xs))= if i=1 then x else helper(i-1,Tuple(xs)) in  helper(i, value(p,e)) end
|value(p,iff(e1,e2,e3))=if e1=Boool(true) then value(p,e2) else value(p,e3)

|value(p,lett(D,E))=  value(augment( elab(p,D,fn(a) => raise Match) , p)  , E )    


and elab(p,equal(x,e),p1) = augment( fn(a)=> if a=x then value(p,e) else raise Match , p1 )
|elab(p,sequential(x::[]),p1)= augment(elab(p,x,p1),p1)
|elab(p,sequential(x::xs),p1)=  elab( augment(elab(p,x,p1),p) , sequential(xs) , augment(elab(p,x,p1),p1) )
|elab(p,parallel(x::[]),p1)= augment(elab(p,x,p1),p1)
|elab(p,parallel(x::xs),p1)=  elab( p , parallel(xs) , augment(elab(p,x,p1),p1) )
|elab(p,locall(d1,d2),p1)=  elab( augment(elab(p,d1,p1),p) , d2 , p1 )




(*
elab(fn("x")=>Integer(3) , sequential([ equal("y",add(Integ(4),Integ(5))) , equal("z",add(Variable("y"),Integ(5))) , equal("y",add(Variable("x"),Integ(5))) ]) , fn("x")=>raise Match);
*)
(*equal("y",add(Integ(4),Integ(5))) , equal("z",add(Integ(44),Integ(5))) , equal("y",add(Variable("x"),Integ(5)))

value(fn("x")=>Integer(4),  lett( sequential([ equal("y",add(Integ(4),Integ(5))) , equal("z",add(Variable("y"),Integ(5))) , equal("y",add(Variable("x"),Integ(5))) ]) ,add(Variable("y"),Variable("x")))  );
*)