

Control.Print.intinfDepth := 1000;

val op +    = IntInf.+;
val op -    = IntInf.-;
val op *    = IntInf.*;
val op div  = IntInf.div;
val op mod  = IntInf.mod;
val op <    = IntInf.<;
val op <=   = IntInf.<=;
val divMod  = IntInf.divMod;
val fromInt = IntInf.fromInt;
val toInt   = IntInf.toInt;

val zero    = fromInt 0;
val one     = fromInt 1;
val two     = fromInt 2;
val three   = fromInt 3;

fun pow2 k  = IntInf.<<(one, Word.fromInt k);

exception RandomIntInfError;
local
    fun randomBits b gen =
        let
            val bound = case b of
                             1 =>   1
                           | 2 =>   3
                           | 3 =>   7
                           | 4 =>  15
                           | 5 =>  31
                           | 6 =>  63
                           | 7 => 127
                           | 8 => 255
                           | _ =>   0;
        in
            fromInt(Random.randRange(0,bound) gen)
        end;
    fun randomIntInf bits gen =
        if Int.<=(bits,8)
           then randomBits bits gen
           else randomBits 8 gen +
                IntInf.<<(randomIntInf (Int.-(bits,8)) gen, Word.fromInt 8);
in
    fun randomRangeIntInf (low,high) gen =
        if high < low
           then raise RandomIntInfError
        else if low = high
           then low
           else
                let
                    val top = high - low;
                    val bitCount = Int.+(1,IntInf.log2 top);
                    fun trialValue () =
                        let
                            val trial = randomIntInf bitCount gen;
                        in
                            if trial <= top
                               then trial
                               else trialValue()
                        end;
                in
                    low + trialValue()
                end;
end;

fun inverseMod (u,m) =
        let
            (*
             * Invariant: There are constants b and d
             * satisfying
             *     x = au+bm  and  y = cu+dm.
             * If ever x=1, then 1 = au+bm, and a
             * is the inverse of u, mod m.
             *)
            fun extendedEuclid(x,y,a,c) =
                if x = zero
                   then NONE
                else if x = one
                   then SOME a 
                else let
                         val (q,r) = divMod(y,x);
                         val newA = (c - a * q) mod m;
                     in
                         extendedEuclid(r,x,newA,a)
                     end;
        in
            extendedEuclid(u,m,one,zero)
        end;

fun powerMod (b, e, n) = 
        if e = zero then 
          one
        else 
         let 
            fun squareMod (k, n) = k * k mod n;
            val b_e = powerMod (b, (e div 2), n) 
            val b_e_2 = squareMod (b_e, n)
          in
          if e mod 2 = zero andalso zero < e then
          
            b_e_2 
          else 
            (b_e_2 * b) mod n
        end;


fun block (n, m) = 
  if n = zero orelse m = zero then
    []
  else if zero < m then 
       ((m mod n )::(block(n, (m div n))))
  else 
    [];
  
fun unblock (n, []) = zero
  | unblock (n, (x::xs)) = x + (n * (unblock (n, xs)));


fun messageToIntInf str = 
    let 
        val expStr = String.explode str
        val ordList = map ord expStr
        val ordList2 = map IntInf.fromInt ordList
    in 
        unblock (256, ordList2)
    end;

fun intInfToMessage n = 
    let 
        val numList = block (256, n)
        val numList2 = map IntInf.toInt numList
        val chrList = map chr numList2
    in 
        implode chrList
    end;

fun rsaEncode (e, n) m = powerMod (m, e, n);

fun encodeString (e, n) s = 
    let 
        val m = messageToIntInf s 
        val b = block (n, m)
        val c = map (rsaEncode (e, n)) b 
    in 
        unblock (n, c)
    end;

val sampleEncryption = encodeString (7, 111) "Don't panic and always carry your towel";

(*val sampleEncryption =
  6191105058469365298186596480275568152766445829254488829305771243768167613394924747807605371837
  : IntInf.int*)

fun decodeString (e, n) c = 
  let 
    val b = block (n, c)
    val r = map (rsaEncode (e, n)) b
    val u = unblock (n, r)
  in 
    intInfToMessage u
  end;


val sampleDecryption = decodeString (31, 111) 6191105058469365298186596480275568152766445829254488829305771243768167613394924747807605371837;

val seed = (47, 74);
val generator = Random.rand seed;

fun industrialStrengthPrime r i = 
  let 
    val p = randomRangeIntInf(pow2 (Int.-(r,1)), pow2 r - one) i
    val rlist = List.tabulate (20, fn ran => (randomRangeIntInf(pow2 (Int.-(r,1)), pow2 r - one) i) mod p);
    fun check a = 
      if powerMod (a, p, p) = a then
        true
      else
        false;
  in 
    if one < p andalso (List.all check rlist) then
      p
    else
      industrialStrengthPrime r i
  end;

fun newRSAKeys r k = 
  let 
    val p = industrialStrengthPrime r k;
    val q = industrialStrengthPrime r k;
    val n = p * q 
    val t = (p-1) * (q-1)
    fun check () = 
      let 
        (*val d = randomIntInf r (Int.*(2,k))*)
        val d = randomRangeIntInf(0, n) generator
      in 
        case 
          (if d < n  then
            inverseMod (d, t)
           else
            NONE) 
          of SOME e => ((d, n), (e, n))
          | NONE => check()

      end
  in
    check()
  end;

fun findPrivateKey (d, n) = 
  let 
    fun findPrimes n x =
      if n mod x = zero then 
         (x -1)*((n div x)-1)
      else
        findPrimes n (x-1);
    val primes = findPrimes n d;
    val e = valOf (inverseMod(d, primes))
  in 
    (e,n)
  end;
    
val crackedPrivateKey = findPrivateKey (22821, 52753);

(*val crackedPrivateKey = (701,52753) : IntInf.int * IntInf.int*)
