open Ast
val k = Calc.compile "test.txt"


exception Wrong
exception Not
exception NotDefined
exception NotExist
exception Empt



fun height(leaf a)= 1
|height(node(a,b))=
let 
	fun max(r,[])=r
	|max(r,x::xs)=if height(x)>r then max(height(x),xs) else
			max(r,xs)
in
	1+ max(0,b)
end




fun size(leaf a)= 1
|size(node(a,b))=
let
	fun cum(r,[])=r
	|cum(r,x::xs)=cum(r+size(x),xs)
in
	1+cum(0,b)
end


	

fun vars(a)= let val k = hd(explode(a)) in 
		if ord(k)>64 andalso ord(k)<91 then true else false	end
		
	
fun mem(y,[])=false 
|mem(y,x::xs)= if y=x then true else mem(y,xs)	
	
fun union([],[])=[]
|union([],x::xs)=x::xs
|union(y::ys,[])=y::ys
|union(y::ys,x::xs)=if mem(y,x::xs) then union(ys,x::xs) else union(ys,y::x::xs)	
	
	
	
fun 	variable(x,leaf s) = if vars(s)=true then union([s],x) else x
	|variable(x,node(a,b))= let 
	
		fun helpp(z,[])=z
		|helpp(z,x::xs)=    helpp(  union (   variable([],x) ,  z )    ,  xs  )
	in

	if vars(a)=true then helpp( union([a],x) , b ) else helpp(x,b)
	end
	
	
	



fun 	Print(a,leaf s)= a@[s]

	|Print(a,node(x,y))= 
	let
		fun help(y,[])=y
		|help(y,x::xs)= help(y@Print([],x),xs)
	in
	a@([x])@help([],y) 
	end
	



fun 	var(x,leaf s) = if vars(s)=true then [s]@x else x
	|var(x,node(a,b))= let 
	
		fun helpp(z,[])=z
		|helpp(z,x::xs)=    helpp( var([],x)@z     ,  xs  )
	in

	if vars(a)=true then helpp( [a]@x , b ) else helpp(x,b)
	end


val mine3 = variable([],k);





fun subst(f,leaf a)=
if var([],leaf a)=[] then leaf a else let val k=f(a) handle Match => leaf a  in k     end

|subst(f,node(a,b))=
if var([],node(a,b))=[] then node(a,b) else
let
	fun replace([])=[]
	|replace(x::xs)=(subst(f,x)::[])@replace(xs)
in
	node (a,replace(b))
end


fun composeee(f1,f2)= fn(a)=> f2(f1(a) handle Match=> raise NotDefined   ) handle Match=>raise NotDefined
fun compose1(f1,f2)= fn(a)=>     subst(f2,subst(f1,a))

fun subst1(f) = fn(t) => subst(f,t) 

fun belongto(s,[])=false
|belongto(s,x::xs)=if s=x then true else belongto(s,xs)

fun union1(f,g)= fn(a)=> f(a)  handle Match=> g(a)  handle Match=> raise NotDefined 
	
fun getback(f,x)= fn(x)=>f(leaf x) 
fun  getback2(f,x::[]) = getback(f,x)
|getback2(f,x::xs) = union1(   getback(f,x)  ,  getback2(f,xs)    )


 

fun unifier(leaf a,leaf b) = if var([],leaf a) = [] andalso var([],leaf b)=[] then 
	if a=b then subst1(fn(x)=>leaf x) else raise NotExist  
	else if var([],leaf a)=[] andalso var([],leaf b)<>[] then subst1(fn q=> if q=b then leaf a else raise Match)
	else if not(var([],leaf a)=[]) andalso var([],leaf b)=[] then  subst1(fn q=> if q=a then leaf b else raise Match)
	else if var([],leaf a)=var([],leaf b) then subst1(fn(x)=>leaf x) else let val k3=hd(var([],leaf a)) in  subst1(fn(w)=>if w=a then leaf b else raise Match) end

|unifier(leaf a,node (b,c))=if var([],leaf a)=[] then raise NotExist else
				if belongto(hd(var([],leaf a)) , var([],node (b,c)) ) then raise NotExist else let val k2=hd(var([],leaf a)) in subst1(fn(q)=>if q=a then node (b,c) else raise Match) end
|unifier(node(b,c) , leaf a)= if var([],leaf a)=[] then raise NotExist else
				if belongto(hd(var([],leaf a)) , var([],node (b,c)) ) then raise NotExist else let val k2=hd(var([],leaf a)) in subst1(fn(q)=>if q=a then node (b,c) else raise Match) end
|unifier(node(a,b) , node(c,d) ) = if not(a=c) then raise NotExist else 
let 
      fun help(x,[],[])=x
	|help(f,x::xs,y::ys)= let val q=unifier( f(x),f(y) ) handle NotExist=> raise NotExist ;  val qq=composeee(f,q) ;   in
					help(qq,xs,ys)
end
in
	help(fn(x)=>x , b,d) 
end	

	
fun unifiermain(a,b) =      getback2 ( unifier(a,b) , mine3 )	handle NotExist=>raise NotExist






val keshav2=unifiermain(    node("path",[leaf "a",leaf "b"])   ,   node("path",[leaf "X",leaf "Y" ])     )   















fun push(y,[]) = [y]
|push(y,x::xs) = y::x::xs
fun pop([]) = raise Empt
|pop(x::xs) = xs























fun callunify(h,leaf a) =  [unifiermain(h,leaf a) handle NotExist => raise NotExist ]

|callunify(h,node("sTART",b)) =  let    

				fun help(y,h,[])= y
				|help(y,h,x::xs)=   let val u=y@callunify(h,x) handle NotExist => y in    help(u  , h , xs ) end
			in
		
		help([],h,b)
	end
		


|callunify(h,node("iff",b)) = callunify(h,hd(b))			
|callunify(h,node(a,b)) = [ unifiermain(h,node(a,b)) ]



























val stack = []









fun leave(i,[])= []
|leave(0,b) = b
|leave(i,b) = leave(i-1,tl(b))





fun getunifymain(i,h,node("sTART",b)) = 

let

val bb = leave(i,b)

fun getunify2(h,leaf a) = unifiermain(h,leaf a) 
|getunify2(h,node("iff",b)) = getunify2(h,hd(b))			
|getunify2(h,node(a,b)) =  unifiermain(h,node(a,b))  

	
				fun help(y,h,[],i)= (0,fn(x)=>leaf "o",h)
				|help(y,h,x::xs,i)= let val k = getunify2(h,x) handle NotExist=>fn(x)=>leaf "o"   in  if k("a")=leaf "o" then  help(y+1,h,xs,i)  else (y+i,k,x)    end
					


in	
		
		help(1,h,bb,i)

end








fun getunify(h,node("sTART",b)) = 

let


fun getunify2(h,leaf a) = unifiermain(h,leaf a) 
|getunify2(h,node("iff",b)) = getunify2(h,hd(b))			
|getunify2(h,node(a,b)) =  unifiermain(h,node(a,b))  

	
				fun help(y,h,[])= (0,fn(x)=>leaf "o",h)
				|help(y,h,x::xs)= let val k = getunify2(h,x) handle NotExist=>fn(x)=>leaf "o"   in  if k("a")=leaf "o" then  help(y+1,h,xs)  else (y,k,x)    end
					


in	
		
		help(1,h,b)

end



exception NoJob




(* add h3 to sequence and let stack be empty and call dojob with them *)



fun read2(f,[]) = []
|read2(f,x::[]) =   [(x,f(x))]
|read2(f,x::xs) =   [(x,f(x))]@read2(f,xs)

fun read(f,x) = let val k = variable([],x) in  (x, read2(f,k)) end

fun givedetail([]) = []
|givedetail(x::[]) = let val (a,b,c,d) = x in [read(b,c)] end
|givedetail(x::xs) = let val (a,b,c,d) = x in [read(b,c)]@givedetail(xs) end



fun sew(t,[]) = t
|sew(t,x::xs) = let val (a,b,c,d,e)=x  val t1=subst(e,t) in if variable([],t1)=[] then t1 else sew(t1,xs) end  
fun givedetail2(x::xs) = let val (a,b,c,d,e) = x in if variable([],d)=[] then d else   sew(subst(e,d),xs) end



fun popseq(Emptyy) = raise Empt
|popseq(Cons(x,xt)) = xt()

fun pushseq(y,Emptyy) = Cons(y,fn()=>Emptyy)
|pushseq(y,Cons(x,xt)) =   Cons(y,fn()=>Cons(x,xt) )      


fun del([])= []
|del(leaf(a)::x) = [leaf(a)]
|del(node(a,b)::x) = if a="commaa" then del(b) @ del(x)  else [node(a,b)]@del(x)

fun listjob(leaf a) = (false,[])
|listjob(node(a,b))= if a="iff" then (true,del(tl(b)) ) else (false,b) 





 


fun callength(k,[]) = k
|callength(k,leaf(a)::x) = callength(k+1,x)
|callength(k,node(a,b)::x) = if a="commaa" then  callength(0,b) + callength(k,x)    else callength(k+1,x)

fun cal(k,[])=k
|cal(k,node(a,b)::xs) = cal(k+1,xs)
|cal(k,(leaf a)::xs) = cal (k,xs) 

fun checkk(leaf a) = 0
|checkk(node(a,b)) = if a="iff" then callength(0,tl(b)) else cal(0,b)



fun doo(x)= fn(r)=> if r=x then leaf(x^"1") else raise Match


fun composer(f,g) = fn(a) => g(a) handle Match => f(a)

fun getfun(f,[]) = f
|getfun(f,x::xs) =  let val u = doo(x) ;  val ff= composer(f,u)    in  getfun(ff,xs) end  

fun getvarr([]) = [] 
|getvarr(x::xs) =  let val i=variable([],x) ; val ii= getvarr(xs): string list   in union(i,ii ) end


fun rewq(f,[]) = []
|rewq(f,x::xs) = [subst(f,x)]@rewq(f,xs)

fun wen(x::xs) = let val u= getvarr(x::xs) ;  val f= getfun(fn(x)=>leaf x,u) in rewq(f,x::xs) end


fun concaat(s,i) = s^(Int.toString(i))

fun fnl(f,Emptyy)=Emptyy
|fnl(f,Cons(x,xt))= let val (a,z) = x in    Cons (  (subst(f,a),z)  , fn()=>  fnl(f,xt()) ) end

fun topp([]) = raise Not
|topp(x::xs)= let val (a3,c4,v5,b3,n2) = x in n2  end


fun fresh( Emptyy ) = Emptyy
|fresh(Cons(x,xt)) = let val (g,e) = x in  Cons( (g,0) , fn()=>fresh(xt()) ) end

fun dojob(i1,[],Emptyy ) = []
|dojob( i1,x::xs  , Emptyy ) =  let val k =[ givedetail2(rev(x::xs)) ]  ;  val (r4,r5,r6,r61,r7)=x ; val bed=dojob( i1,xs , Cons( (r61,r4),fn()=>Emptyy  )) handle NotExist=>[]     in  k :: bed end 

|dojob(i1,y , Cons(x ,xt) ) =  let val (r,e)=x   ; val q1=topp(y)  handle Not=> fn(x)=>leaf x   ; val r = subst(q1,r) ; val mtree = subst(fn(x)=>leaf (concaat(x,i1)) , k)    ;val (a,b,c) = getunifymain(e,r,mtree) 



fun failed(i1,[],Cons(x,xt))= raise NotExist
|failed(i1,y::ys,Cons(x,xt))= let val (k0,k1,k2,k3,k4) = y ;  val y1 = checkk(k2) ;
fun dropSeq(0, xs) = xs  | dropSeq(i, Emptyy) = if i>0 then raise Empt  else Emptyy
| dropSeq(i, Cons(x, xt)) = dropSeq(i-1, xt()); val t  = dropSeq(y1,Cons(x,xt)) ;  val tti = fresh(t)     ; val r =  Cons( (k3,k0) ,fn()=>  tti )       in  
		dojob( i1+1,ys , r) end


fun success(i1,(a,b,c),y1,Cons(z,zt))=    let val (a1,u) = listjob( subst(b,c)  ) ; val i  = zt();val (v,v1)=z;


fun addjob((true,y::ys) , g ) =   addjob( (true,ys)    ,  pushseq((y,0),g)   ) 
|addjob((true,[]) , a ) = a
|addjob((false,[]) , a ) = a

|addjob((false,leaf(a)::y), g) = addjob((false,y), g)
|addjob((false,node(a,b)::y), g) =  addjob( (false,y)    ,  pushseq((node(a,b),0),g)      )

;  val he = rev(u)    ;    val bbg=topp(y1) handle Not => fn(x)=>leaf x  ;  val d4 = composer(bbg,b)         ;val j= addjob((a1,he),i) in     
 						dojob(  i1+1,push((a,b,c,v,d4),y1)  , j )    end



in  if a=0 then failed(i1,y,Cons(x,xt)) else success(i1,(a,b,c),y,Cons(x,xt)) end







val h3 = node("edge",[leaf "X",leaf "e"])

val keshav = dojob(0,[],Cons((h3,0),fn()=> Emptyy))  




(*

todo-
-



steps
-create a function taking 2 parameters stack and sequence checking backtracking and all
-initialise stack empty and sequence with main job h3
-put citem in stack and subgoals in sequence
--perform the first sequence by again calling it to getunify
-the result of which is again accordingly

-if unification fails at any moment do backtracking
-if its unification of "iff" remove x items from sequence and pop out 1 item from stack and find next unifier by making a function

-if its not unification of "iff" , then ..............(see it)

-


*)





