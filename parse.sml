datatype oper =
    Negate
  | Plus
  | Minus
  | Times
  | Divide
  | Remainder;

datatype token = 
    Number of int
  | Operation of oper
  | LParen
  | RParen
  | Semicolon;

datatype syntaxTree =
    Uninode of oper * syntaxTree
  | Binode of syntaxTree * oper * syntaxTree
  | Leaf of int;

exception LexicalException of string;
exception GrammarException of string;
exception CodeException of string;

val exitCode = ref OS.Process.success;
fun errorln str = (exitCode := OS.Process.failure;
                   TextIO.output (TextIO.stdErr, str ^ "\n");
                   TextIO.flushOut TextIO.stdErr;
                   nil);

fun scan nil = nil
    |scan (#"~"::xs) = Operation Negate::(scan xs)
    |scan (#"+"::xs) = Operation Plus::(scan xs)
    |scan (#"-"::xs) = Operation Minus::(scan xs)
    |scan (#"*"::xs) = Operation Times::(scan xs)
    |scan (#"/"::xs) = Operation Divide::(scan xs)
    |scan (#"%"::xs) = Operation Remainder::(scan xs)
    |scan (#")"::xs) = RParen::(scan xs)
    |scan (#"("::xs) = LParen::(scan xs)
    |scan (#";"::xs) = Semicolon::(scan xs)
    |scan (#" "::xs) = scan xs
    |scan (x::xs) = 
      if Char.isDigit x then
          charCount 0 (x::xs)
          handle Overflow => raise LexicalException "integer too large"
      else 
          raise LexicalException "illegal character"

and charCount acc nil = [Number acc]
  | charCount acc (x::xs) = 
    if Char.isDigit x then 
      charCount (acc*10 + ((ord x) - (ord #"0"))) xs
    else 
      (Number acc)::(scan (x::xs));

fun makeBinode (ltree, ope, (rtree, rest)) = (Binode(ltree, ope, rtree), rest);
fun makeUninode (ope, (rtree, rest)) = (Uninode(ope, rtree), rest);

fun parse tknList =
  case expr tknList of
    (tree, [Semicolon]) => tree
    | (_, Semicolon::_) => raise GrammarException "extra tokens in input stream"
    | (tree, []) => raise GrammarException "semicolon expected"

and expr tknList = exprAux (term tknList)
  and exprAux (tr, (Operation Plus)::rest) = exprAux (makeBinode (tr, Plus, term rest))
    | exprAux (tr, (Operation Minus)::rest) = exprAux (makeBinode (tr, Minus, term rest))
    | exprAux (tr, rest) = (tr, rest)

and term tknList = termAux (factor tknList)
  and termAux (tr, (Operation Times)::rest)  = termAux (makeBinode (tr, Times, factor rest))
    | termAux (tr, (Operation Divide)::rest) = termAux (makeBinode (tr, Divide, factor rest))
    | termAux (tr, (Operation Remainder)::rest) = termAux (makeBinode (tr, Remainder, factor rest))
    | termAux (tr, rest) = (tr, rest)

and factor ((Operation Negate)::rest) = makeUninode(Negate, (posFactor rest))
  | factor tknList = posFactor tknList

and posFactor (LParen::rest) = 
    (case expr rest of
      (tr, RParen::rrest) => (tr, rrest)
     |(_, _) => raise GrammarException "right parenthesis expected")
    |posFactor n = num n

and  num ((Number x)::rest) = (Leaf x, rest)
    |num _ = raise GrammarException "number expected";

 val beginprogram = ["BEGIN", " lcw r1 stack"];
 val endprogram = [" pop r3", " sto r3 r0", " hlt",  " inc mullib", " inc divilib", " dat 100", "stack", "END"];
 val minusprogram = [" pop r3", " pop r2", " sub r3 r2 r3", " psh r3"];
 val addprogram = [" pop r3", " pop r2", " add r3 r2 r3", " psh r3"];
 val timesprogram = [" pop r3", " lcw r2 mlmul", " cal r2 r2", " pop r0", " psh r3"];
 val divideprogram = [" pop r3", " lcw r2 dldiv", " cal r2 r2", " pop r0", " psh r3"];
 val remprogram = [" pop r3", " lcw r2 dldiv", " cal r2 r2"];
 val negprogram = [" pop r3", " neg r3 r3", " psh r3"];
 fun leafpush k = [ " lcw r3 " ^ (Int.toString k), " psh r3"];

fun encAux (Leaf n) = leafpush n
  |encAux (Binode (ltree, Minus, rtree)) = (encAux ltree) @ (encAux rtree) @ minusprogram
  |encAux (Binode (ltree, Plus, rtree)) = (encAux ltree) @ (encAux rtree) @ addprogram
  |encAux (Binode (ltree, Times, rtree)) = (encAux ltree) @ (encAux rtree) @ timesprogram
  |encAux (Binode (ltree, Divide, rtree)) = (encAux ltree) @ (encAux rtree) @ divideprogram
  |encAux (Binode (ltree, Remainder, rtree)) = (encAux ltree) @ (encAux rtree) @ remprogram
  |encAux (Uninode (Negate, n)) = (encAux n) @ negprogram
  |encAux _ = raise CodeException "invalid syntax tree";
  
fun encode tree = beginprogram @ (encAux tree) @ endprogram;  

fun compile "" = nil
  | compile s = encode(parse(scan(explode(s)))) 
          handle (GrammarException msg) => errorln("GrammarException: " ^ msg)
          | (CodeException msg) => errorln("CodeException: " ^ msg)
          | (LexicalException msg) =>  errorln("LexicalException: " ^ msg);
