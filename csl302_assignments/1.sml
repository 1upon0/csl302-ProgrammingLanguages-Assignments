val mine1=["a","b","c","d"]
val mine2=[0,0,2,1]
val mine3=["x","y","z"]

(*DECLARATION OF THE DATATYPE FOR THE SIGNATURE*)
datatype tree = leaf of string | node of string*tree list

fun mine4("x")=leaf "z"

|mine4("z")=node("c",[leaf "a",leaf "b"])

exception Wrong
exception Not
exception NotDefined
exception NotExist


fun max(y,[])=y
|max(y,x::xs)= if x>y then max (x,xs) else max(y,xs)

fun create(0)=[[]]
|create(y)=[]::create(y-1)

fun hey(x,y,r::rs) = if y=0 then  ([x]@r) :: rs else r :: hey(x,y-1,rs)

fun check([])=false
|check(x::xs)=if x>=0 then check(xs) else true

fun givelist(x::xs,y::ys)= if check(y::ys) then raise Wrong else
	let 
	val k=max(0,y::ys) ; val u=create(k) 
	in
		let
  		fun yes(x::xs,y::ys,u)=
			let val u =hey(x,y,u)   
			in	
				if xs=[] then u else 			
				yes(xs,ys,u) 
			end
		in
		yes(x::xs,y::ys,u) 
		end
	end
			 
val r = givelist(mine1,mine2)	
val p=( hd(r)@mine3 ) :: tl(r)

fun isit(a,[])=false
|isit(a,x::xs)=if a=x then true else isit(a,xs)

fun tellarity(a,[],k)=raise Not 
|tellarity(a,x::xs,k)= if isit(a,x) then k else tellarity(a,xs,k+1) 



fun check(leaf a)=if tellarity(a,p,0)=0 then true else false
|check(node (a,b))=if tellarity(a,p,0)=length(b) then
let
	fun hr([])=true
	|hr(x::xs)= if check(x) then hr(xs) else false
in
	if hr(b) then true else false
end
else false

fun height(leaf a)= if check(leaf a)=false then raise Not else 1
|height(node(a,b))=if check(node(a,b))=false then raise Not else 
let 
	fun max(r,[])=r
	|max(r,x::xs)=if height(x)>r then max(height(x),xs) else
			max(r,xs)
in
	1+ max(0,b)
end

fun size(leaf a)=if check(leaf a)=false then raise Not else 1
|size(node(a,b))=if check(node(a,b))=false then raise Not else
let
	fun cum(r,[])=r
	|cum(r,x::xs)=cum(r+size(x),xs)
in
	1+cum(0,b)
end

fun var(leaf a) = if check(leaf a)=false then raise Not else
	let 
		fun h(a,[])= []
		|h(a,x::xs)=if a=x then [a] else h(a,xs)
	in 
		h(a,mine3)
	end
|var(node(a,b))= if check(node(a,b))=false then raise Not else
	let
		fun total(x,[]) = x
		|total(x,y::ys)=total(var(y)@x,ys)
	in
		total([],b)
end


fun subst(f,leaf a)=if check(leaf a)=false then raise Not else
if var(leaf a)=[] then leaf a else let val k=f(a) handle Match => leaf a  in k     end

|subst(f,node(a,b))=if check(node(a,b))=false then raise Not else
if var(node(a,b))=[] then node(a,b) else
let
	fun replace([])=[]
	|replace(x::xs)=(subst(f,x)::[])@replace(xs)
in
	node (a,replace(b))
end

fun composeee(f1,f2)= fn(a)=> f2(f1(a) handle Match=> raise NotDefined   ) handle Match=>raise NotDefined
fun compose1(f1,f2)= fn(a)=>     subst(f2,subst(f1,a))

(*
val r = subst(mine4,node("c",[node("c",[leaf "z",leaf "x"]),leaf "y"]));
val u = var(r)

val r = compose(mine4a,mine4,node("c",[node("c",[leaf "z",leaf "x"]),leaf "y"]));
val u = var(r)
*)


fun subst1(f) = fn(t) => subst(f,t) 

fun belongto(s,[])=false
|belongto(s,x::xs)=if s=x then true else belongto(s,xs)

fun union(f,g)= fn(a)=> f(a)  handle Match=> g(a)  handle Match=> raise NotDefined 
	
fun getback(f,x)= fn(x)=>f(leaf x) 
fun  getback2(f,x::[]) = getback(f,x)
|getback2(f,x::xs) = union(   getback(f,x)  ,  getback2(f,xs)    )


 

fun unifier(leaf a,leaf b) = if var(leaf a) = [] andalso var(leaf b)=[] then 
	if a=b then subst1(fn(x)=>leaf x) else raise NotExist  
	else if var(leaf a)=[] andalso var(leaf b)<>[] then subst1(fn q=> if q=b then leaf a else raise Match)
	else if not(var(leaf a)=[]) andalso var(leaf b)=[] then  subst1(fn q=> if q=a then leaf b else raise Match)
	else if var(leaf a)=var(leaf b) then subst1(fn(x)=>leaf x) else let val k3=hd(var(leaf a)) in  subst1(fn(w)=>if w=a then leaf b else raise Match) end

|unifier(leaf a,node (b,c))=if var(leaf a)=[] then raise NotExist else
				if belongto(hd(var(leaf a)) , var(node (b,c)) ) then raise NotExist else let val k2=hd(var(leaf a)) in subst1(fn(q)=>if q=a then node (b,c) else raise Match) end
|unifier(node(b,c) , leaf a)= if var(leaf a)=[] then raise NotExist else
				if belongto(hd(var(leaf a)) , var(node (b,c)) ) then raise NotExist else let val k2=hd(var(leaf a)) in subst1(fn(q)=>if q=a then node (b,c) else raise Match) end
|unifier(node(a,b) , node(c,d) ) = if not(a=c) then raise NotExist else 
let 
      fun help(x,[],[])=x
	|help(f,x::xs,y::ys)= let val q=unifier( f(x),f(y) ) handle NotExist=> raise NotExist ;  val qq=composeee(f,q) ;   in
					help(qq,xs,ys)
end
in
	help(fn(x)=>x , b,d) 
end	

	
fun unifiermain(a,b) =      getback2 ( unifier(a,b) , mine3 )				
			


val keshav=unifiermain(    node("c",[node("d",[leaf "a"]),leaf "x"  ])   ,   node("c",[leaf "y",leaf "b" ])     )

 
