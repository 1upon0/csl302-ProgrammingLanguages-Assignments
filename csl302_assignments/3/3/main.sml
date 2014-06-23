open Ast
val k = Calc.compile "test.txt"

fun 	height(leaf s)= 1
	
	
	|height(par(x))=1+height(x) 
	|height(comma(x,y))=if height(x)>height(y) then 1+height(x) else 1+height(y) 
	|height(node(x,y))= if height(x)>height(y) then 1+height(x) else 1+height(y)
	|height(iff(x,y))=if height(x)>height(y) then 1+height(x) else 1+height(y) 
				
				
fun	mheight(a,[])=a 
	|mheight(a,x::xs)= let val k1c=height(x) in 
			if k1c>a then mheight(k1c,xs) else mheight(a,xs) end  
			
	
fun 	size(leaf s)= 1
	
	
	|size(par(x))= 1+size(x) 
	|size(comma(x,y))=1+size(x)+size(y) 
	|size(node(x,y))= 1+size(x)+size(y) 
	|size(iff(x,y))=1+size(x)+size(y) 
				
				
fun msize(a,[])=a
	|msize(a,x::xs)= msize(a+size(x),xs)
	
	

fun var(a)= let val k = hd(explode(a)) in 
		if ord(k)>64 andalso ord(k)<91 then true else false	end
		
	
fun mem(y,[])=false 
|mem(y,x::xs)= if y=x then true else mem(y,xs)	
	
fun union([],[])=[]
|union([],x::xs)=x::xs
|union(y::ys,[])=y::ys
|union(y::ys,x::xs)=if mem(y,x::xs) then union(ys,x::xs) else union(ys,y::x::xs)	
	
fun 	variable(x,leaf s) = if var(s)=true then union([s],x) else x
	|variable(x,par(y))= variable(x,y)
	|variable(x,comma(a,b))= union (  variable(x,a) , variable(x,b)  )
	|variable(x,node(a,b))= union (  variable(x,a) , variable(x,b)  )
	|variable(x,iff(a,b))= union (  variable(x,a) , variable(x,b)  )
	
	
fun mvariable(x,[])=x
|mvariable(x,y::ys) = mvariable(  variable(x,y) , ys )


fun 	Print(a,leaf s)= a@[s]
	|Print(a,par(x))=  a@(["("]@Print([],x)@ [")"] )
	|Print(a,comma(x,y))= a@(Print([],x)@["comma"]@Print([],y) )
	|Print(a,node(x,y))= a@( Print([],x)@Print([],y) )
	|Print(a,iff(x,y))= a@(Print([],x)@[":-"]@Print([],y) )
	
fun 	mPrint(a,[]) = a
	|mPrint(a,x::xs) =  mPrint(a@[Print([],x)] , xs )






