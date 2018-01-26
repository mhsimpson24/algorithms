Control.Print.printDepth := 100;

fun member e = List.exists (fn x => x = e);

fun uniquify nil     = nil
  | uniquify (x::xs) =
    let
        val recResult = uniquify xs;
    in
        if member x recResult
           then recResult
           else x::recResult
    end;

fun cartesian nil     _       = nil
  | cartesian _       nil     = nil
  | cartesian [x]     (y::ys) = (x,y) :: (cartesian [x] ys)
  | cartesian (x::xs) yList   = (cartesian [x] yList) @ (cartesian xs yList);

(* The datatype from Bits and Logic *)
datatype booleanExpression =
           False
         | True    
         | Prop of int
         | Not of booleanExpression
         | And of booleanExpression * booleanExpression
         | Or of booleanExpression * booleanExpression
         | Xor of booleanExpression * booleanExpression
         | Implies of booleanExpression * booleanExpression
         | Iff of booleanExpression * booleanExpression;

(* The function evalExp from Bits and Logic *)
fun evalExp _      False                  = false
  | evalExp _      True                   = true
  | evalExp truths (Prop j)               = member j truths
  | evalExp truths (Not exp)              = not (evalExp truths exp)
  | evalExp truths (And (exp0, exp1))     =
        (evalExp truths exp0) andalso (evalExp truths exp1) 
  | evalExp truths (Or (exp0, exp1))      =
        (evalExp truths exp0) orelse (evalExp truths exp1) 
  | evalExp truths (Xor (exp0, exp1))     =
        (evalExp truths exp0) <> (evalExp truths exp1) 
  | evalExp truths (Implies (exp0, exp1)) =
        (not (evalExp truths exp0)) orelse (evalExp truths exp1)
  | evalExp truths (Iff (exp0, exp1))     =
        (evalExp truths exp0) = (evalExp truths exp1);

(* A handy function to avoid some double negations *)
fun negate False     = True
  | negate True      = False
  | negate (Not exp) = exp
  | negate exp       = Not exp;

(* A function to check your results *)
local
    fun isLiteral (Prop _)       = true
      | isLiteral (Not (Prop _)) = true
      | isLiteral _              = false;

    fun checkDNF dnfExpn = List.all (List.all isLiteral) dnfExpn;
    
    fun powerList nil     = [nil]
      | powerList (x::xs) =
            let
                val recResult = powerList xs;
            in
                recResult @ (map (fn set => x::set) recResult)
            end;

    fun subscriptsExp False                  = nil
      | subscriptsExp True                   = nil
      | subscriptsExp (Prop j)               = [j]
      | subscriptsExp (Not exp)              = subscriptsExp exp
      | subscriptsExp (And (exp0, exp1))     =
            (subscriptsExp exp0) @ (subscriptsExp exp1)
      | subscriptsExp (Or (exp0, exp1))      =
            (subscriptsExp exp0) @ (subscriptsExp exp1)
      | subscriptsExp (Xor (exp0, exp1))     =
            (subscriptsExp exp0) @ (subscriptsExp exp1)
      | subscriptsExp (Implies (exp0, exp1)) =
            (subscriptsExp exp0) @ (subscriptsExp exp1)
      | subscriptsExp (Iff (exp0, exp1))   =
            (subscriptsExp exp0) @ (subscriptsExp exp1);

    fun subscriptsDNF dnfExp =
        List.concat (map (List.concat o (map subscriptsExp)) dnfExp);
    
    fun evalDNF truths dnfExpn = List.exists (List.all (evalExp truths))
                                             dnfExpn;
    
in
    fun checkEquivalence boolExp dnfExp =
            let
                val subscripts = uniquify ((subscriptsExp boolExp) @
                                           (subscriptsDNF dnfExp));
	        val truthValues = powerList subscripts;
	        fun sameValue truths = (evalExp truths boolExp) =
                                       (evalDNF truths dnfExp);
            in
                if checkDNF dnfExp
                   then List.all sameValue truthValues
                   else (print "Not valid DNF!\n"; false)
            end;
end;

fun elimConnectives False                  = False
  | elimConnectives True                   = True
  | elimConnectives (Prop j)               = (Prop j)
  | elimConnectives (Not exp)              = (Not (elimConnectives exp))
  | elimConnectives (And (exp0, exp1))     = (And ((elimConnectives exp0), (elimConnectives exp1))) 
  | elimConnectives (Or (exp0, exp1))      = (Or ((elimConnectives exp0), (elimConnectives exp1))) 
  | elimConnectives (Xor (exp0, exp1))     = 
        (Or((And((elimConnectives exp0), (Not (elimConnectives exp1)))), (And((Not (elimConnectives exp0)), (elimConnectives exp1)))))
  | elimConnectives (Implies (exp0, exp1)) = (Or((Not (elimConnectives exp0)), (elimConnectives exp1)))
  | elimConnectives (Iff (exp0, exp1))     = 
        (Or((And((elimConnectives exp0), (elimConnectives exp1))), (And((Not (elimConnectives exp0)), (Not (elimConnectives exp1))))));

exception ConversionException;

fun applyDeMorgan (Not True) = False
  | applyDeMorgan (Not False) = True
  | applyDeMorgan (Prop j) = (Prop j)
  | applyDeMorgan (Not(Not exp0)) = applyDeMorgan exp0
  | applyDeMorgan (Not(And(exp0, exp1))) = (Or ((applyDeMorgan (Not exp0)), (applyDeMorgan (Not exp1))))
  | applyDeMorgan (Not(Or(exp0, exp1))) = (And ((applyDeMorgan (Not exp0)), (applyDeMorgan (Not exp1))))
  | applyDeMorgan (And(exp0, exp1)) = And((applyDeMorgan exp0), (applyDeMorgan exp1))
  | applyDeMorgan (Or(exp0, exp1)) = Or((applyDeMorgan exp0), (applyDeMorgan exp1))
  | applyDeMorgan (Not (Prop j)) = (Not (Prop j))
  | applyDeMorgan (Xor (exp0, exp1)) = raise ConversionException
  | applyDeMorgan (Implies (exp0, exp1)) = raise ConversionException
  | applyDeMorgan (Iff (exp0, exp1)) = raise ConversionException
  | applyDeMorgan exp0 = exp0; 

    fun toDNF True               = [[]]
      | toDNF False              = []
      | toDNF (Prop j)           = [[Prop j]]
      | toDNF (Not (Prop j))     = [[Not (Prop j)]]
      | toDNF (Or (exp0, exp1))  = (toDNF(exp0))@(toDNF(exp1))
      | toDNF (And (exp0, exp1)) = List.map (op @) (cartesian (toDNF exp0) (toDNF exp1))
      | toDNF _                  = raise ConversionException;

fun expToDNF exp = toDNF(applyDeMorgan(elimConnectives(exp)));

fun checkForDuplicates nil 	   = nil
   |checkForDuplicates [x]	   = [x]
   |checkForDuplicates (x::xs) = let
										val neg = negate x
								 in
										if (member neg xs) then
											[]
										else 
										 (x::xs)
								 end;
fun betterExpToDNF exp = let
                            fun toDNFNew True               = [[]]
                              | toDNFNew False              = []
                              | toDNFNew (Prop j)           = [[Prop j]]
                              | toDNFNew (Not (Prop j))     = [[Not (Prop j)]]
                              | toDNFNew (Or (exp0, exp1))  = uniquify ((toDNFNew exp0)@(toDNFNew exp1))
                              | toDNFNew (And (exp0, exp1)) = List.map (op @) (cartesian (toDNFNew exp0) (toDNFNew exp1))                                                                  
                              | toDNFNew _                  = raise ConversionException
                            val result = List.map (checkForDuplicates) (toDNFNew(applyDeMorgan(elimConnectives(exp))))	
                            fun removeEmpty [] 		= []
                               |removeEmpty (x::xs)		= if x = [] then
                               								 removeEmpty xs
                               							  else
                               							  	(x::(removeEmpty xs));		  	
                          in	
                          	removeEmpty result
                          end;
