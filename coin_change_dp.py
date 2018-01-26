def dpMakeChange(denoms,change):
	used = [0]*(change+1)
    numCoins = [0]*(change+1)
	# Determine number of coins in minimum size multi-set of coins that makes change for the given input
   for thisChange in range(change+1):
      coinCount = thisChange
      newCoin = 1
      for j in [c for c in denoms if c <= thisChange]:
            if numCoins[thisChange-j] + 1 < coinCount:
               coinCount = numCoins[thisChange-j]+1
               newCoin = j
      numCoins[thisChange] = coinCount
      used[thisChange] = newCoin
   print(numCoins[change])
   # Backtrack to determine the composition 
   # of the minimum size multi-set of coins
   coins = [0 for x in range(0, numCoins[change])]
   coin = change
   while coin > 0:
      thisCoin = used[coin]
      if (thisCoin > 0):
        coins.append(thisCoin)
      coin = coin - thisCoin
   coinsNoZeros = [i for i in coins if i!=0]
   return (coinsNoZeros)

# Main method to test dpMakeChange 
def main():
    # Example using 47 cents and standard U.S. currency
    amnt = 47
    clist = [1, 5, 10, 25]
    print(dpMakeChange(clist,amnt))

main()
