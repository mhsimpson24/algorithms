datatype Peg = Red | Orange | Yellow | Green | Blue | Violet;

val allColors = [Red, Orange, Yellow, Green, Blue, Violet];

fun cons first rest = first::rest;
fun consAll lst elt = map (cons elt) lst;

fun possibilities elts k =
        if k < 0
           then []
        else if k = 0
           then [[]]
           else List.concat (map (consAll(possibilities elts (k-1))) elts);

val allCodes = possibilities allColors;

val generator = Random.rand(19,21);

fun knuthShuffle generator lst =
	if List.length lst < 2 then
		lst
	else
		let 
			val ran = Random.randRange (0, List.length lst -1) generator
			val first = List.take (lst, ran) 
			val second = List.drop (lst, ran+1)
		in
			(List.nth(lst,ran))::(knuthShuffle generator first@second)
		end;

fun exactMatches [] [] = 0
	|exactMatches [] (y::ys) = 0
	|exactMatches (x::xs) [] = 0
	|exactMatches (x::xs) (y::ys) =
	let 
		val count = 0
	in
		if x = y then
			1 + exactMatches xs ys
		else
			exactMatches xs ys
	end;

fun helper peg [] = 0
	|helper peg (x::xs) = 
		if peg = x then
			1 +  helper peg xs
		else 
			helper peg xs;

fun countColors [] = [0,0,0,0,0,0]
	| countColors (x::xs) =
		let 
			val redCounts = helper Red (x::xs)
			val orangeCounts = helper Orange (x::xs)
			val yellowCounts = helper Yellow (x::xs)
			val greenCounts = helper Green (x::xs)
			val blueCounts = helper Blue (x::xs)
			val violetCounts = helper Violet (x::xs)
		in 
			[redCounts, orangeCounts, yellowCounts, greenCounts, 
			blueCounts, violetCounts]
		end;

fun totalMatches [] [] = 0
	|totalMatches [] _ = 0
	|totalMatches _ [] = 0
	|totalMatches (x::xs) (y::ys) = 
		let
			fun sumList []      = 0
  			    |sumList (x::xs) = x + (sumList xs)
  			fun minList [] [] = []
  				|minList (x::xs) [] = []
  				|minList [] (y::ys) = []
  				|minList (x::xs) (y::ys) = 
  					if x < y then
  						x::(minList xs ys)
  					else
  						y::(minList xs ys)
			val list1 = (countColors (x::xs))
			val list2 = (countColors (y::ys))
			val min = minList list1 list2
			val sum = sumList min
		in
			sum
		end;

fun matches [] [] = (0,0)
	|matches [] (y::ys) = (0,0)
	|matches (x::xs) [] = (0,0)
	|matches (x::xs) (y::ys) =
		let
			fun exactMatches [] [] = 0
				|exactMatches [] (y::ys) = 0
				|exactMatches (x::xs) [] = 0
				|exactMatches (x::xs) (y::ys) =
					let 
						val count = 0
					in
						if x = y then
						(1 + (exactMatches xs ys))
					else
						exactMatches xs ys
					end
				
			fun totalMatches [] [] = 0
				|totalMatches [] _ = 0
				|totalMatches _ [] = 0
				|totalMatches (x::xs) (y::ys) = 
					let
						fun sumList []      = 0
			  			    |sumList (x::xs) = x + (sumList xs)
			  			fun minList [] [] = []
			  				|minList (x::xs) [] = []
			  				|minList [] (y::ys) = []
			  				|minList (x::xs) (y::ys) = 
			  					if x < y then
			  						x::(minList xs ys)
			  					else
			  						y::(minList xs ys)
						val list1 = (countColors (x::xs))
						val list2 = (countColors (y::ys))
						val min = minList list1 list2
						val sum = sumList min
					in
						sum
					end

				val exact = (exactMatches (x::xs) (y::ys))
				val total = (totalMatches (x::xs) (y::ys))
				val partial = total - exact
		in
			(exact, total- exact)
		end;

fun isConsistent [] (a, b) [] = false
	|isConsistent [] (a,b) (y::ys) = false
	|isConsistent (x::ys) (a,b) [] = false
	|isConsistent (x::xs) (a,b) (y::ys) = 
		let
			val response = matches (x::xs) (y::ys)
		in
			if response = (a,b) then
				true
			else
				false
		end;

 fun filterCodes [] _ _ = []
   | filterCodes _ _ [] = []
   | filterCodes guess (a,b) (x::xs) =
		if (isConsistent guess (a,b) x) then 
			(x::(filterCodes guess (a,b) (xs)))
		else 
			(filterCodes guess (a,b) (xs));

exception internalInconsistency;

val test = matches [Red, Green, Yellow, Violet];

fun codebreaker _ _ [] = raise internalInconsistency
   |codebreaker f prevGuesses (x::xs) = 
   		if f x = (List.length x, 0) then
   			List.rev(x::prevGuesses)
   		else
   			(codebreaker f (x::prevGuesses)(filterCodes x (f x) (x::xs)));

fun solve code = codebreaker (matches code) [] (allCodes (List.length code)); 

exception RadixException;

fun digitToChar c =
	let val numCharList = [#"0",#"1",#"2",#"3",#"4",#"5",#"6",#"7",
		#"8",#"9"];
		val letCharList = [#"A",#"B",#"C",#"D",#"E",#"F",#"G",#"H",
		#"J",#"K",#"L"];
	in 
		if c >=0  andalso c <= 9 then
			List.nth(numCharList, c)
		else if c >= 10 andalso c <= 20 then
			List.nth(letCharList, c-10)
		else
			raise RadixException
	end;



exception RadixException;

fun charToDigit c = 
		let 
			val alpha = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 
			12, 13, 14, 15, 16, 17, 18, 19, 20]
			val beta = [#"0", #"1", #"2", #"3", #"4", #"5", #"6", 
			#"7", #"8", #"9", #"A", #"B", #"C", #"D", #"E", #"F", 
			#"G", #"H", #"J", #"K", #"L"]
			val zip = ListPair.zip (beta, alpha)
			fun funPairs default []           _ = default
  				| funPairs default ((u,v)::uvs) x =
    				if u = x then
       				 	v
				    else
				        funPairs default uvs x
		in
			funPairs 0 zip c
		end; 


fun toRadixString (r,n) = 
	if r < 2 orelse r > 20 then
		raise RadixException
	else 
		let 
			fun createCharList rem num acc = 
		      	   if num = 0
		           	 then acc
		           else (createCharList rem (num div rem) 
		           	((digitToChar(num mod rem))::acc));
			val charList = createCharList r n []
		in 
			implode charList
		end;

fun fromRadixString (0, _) = 0
  | fromRadixString (_,"") = 0
  | fromRadixString (r, s) = 
  	let
  		fun power x n = if n = 0
			then 1
			else x * (power x (n-1));
  		val charList = explode s
		val digitList = map charToDigit charList
		val exp = power r ((length digitList) -1)
		val new = implode (List.drop (map digitToChar digitList, 1))
  	in
  		if r < 2 orelse r > 20 then 
  			0 
  		else 
  			((List.nth (digitList, 0) * exp)) + fromRadixString (r, new)
  	end;
