exception Wrong
datatype exp = Lambda of string*exp | Variable of string | Funct of exp*exp
datatype out = L of out | Integer of int | At of out*out


fun countfree(a,[],z,k)=  (~k,rev(a::rev(z)) )
|countfree(a,z::zs,y,k) = if a=z then (~k,y) else countfree(a,zs,y,k+1)

fun count(a,[],z,k)= countfree(a,z,z,1)
|count(a,x::xs,z,k) = if a=x then (k,z) else count(a,xs,z,k+1)

(* call this function with empty lists*)
fun debryn(Lambda(x,a),y,z)= let val (s,d,e) = debryn(a,x::y,z) in (L(s),d,e) end
|debryn(Funct(e1,e2),y ,z )= let val (s,d,g1)= debryn(e1,y,z) ; val (w,e,g2) = debryn(e2,y,d)  in if length(g2)>length(g1) then   ( At( s,w ) , e ,g2) else ( At( s,w ) , e ,g1) end
|debryn( Variable(y) ,x::xs,z)=  let val (a,b) = count(y,x::xs,z,0)  in  (Integer( a ) ,b,x::xs)   end

fun adding(L(a),k) =  L(adding(a,k))
|adding(At(a,b),k) =  At(adding(a,k) , adding(b,k) )
|adding(Integer(a),k) = if a>=0 then Integer(a) else Integer(k-a)

(*THIS IS THE MAIN DEBRYN INDICES SOLUTION OF FIRST PART*)
fun maindebryn(e) = let val (k1,k2,k3) = debryn(e,[],[]); val max = length(k3) in adding(k1,max-1) end

(*trial cases*)

val keshav =maindebryn(Lambda("x",Funct(Lambda("y",Variable("z")),Variable("x"))))
val keshav1= maindebryn(Lambda("x",Funct(Lambda("z",Funct(Variable("z"),Variable("x"))),Lambda("y",Variable("z")))))


fun make(k)="x"^(Int.toString(k))
fun search(a,[])=raise Wrong
|search(a,x::xs) = if a=0 then x else search(a-1,xs)
fun countrev(a,x,i) =  if a >=i then "y"^(Int.toString(a))  else   search(a,x)

(*call this with empth list*)
fun reverse(L(e),y,i) = Lambda( make(length(y)) , reverse(e,make(length(y))::y,i+1) )
|reverse( At(e1,e2),y ,i)= Funct( reverse(e1,y,i) , reverse(e2,y,i) )
|reverse(Integer(a),y,i)= Variable(countrev(a,y,i))

(*MAIN FUNCTION FOR REVERSING OF DEBRYN*)
fun mainreverse(e) = reverse(e,[],0)


fun shift(c,d,Integer(a)) = if a<c then Integer(a) else Integer(a+d)
|shift(c,d,At(e1,e2)) = At( shift(c,d,e1) , shift(c,d,e2))
|shift(c,d,L(e)) = L( shift(c+1,d,e) )


fun subst(Integer(k) , t , Integer(j) ) = if k=j then t else Integer(k)
|subst(At(t1,t2),t,Integer(j))=At(subst(t1,t,Integer(j)) ,subst(t2,t,Integer(j)) )
|subst(L(e),t,Integer(j)) = L(  subst(e,shift(0,1,t),Integer(j+1))   )

fun b_subst(At(L(t1),t2))=    shift(0,~1,     subst( t1 , shift( 0,1,t2) , Integer(0) )      )






(*aivee*)
fun h1(L(a))=a
fun h2(At(a,b))=b