def makeChange(val, denoms):
	val = val * 100
	result = []
	totalCount = 0
	while (val > 0):
		if (val >= denoms[0]):
			numCoin = val // denoms[0]
			totalCount+= numCoin
			val -= (numCoin * denoms[0])
			for x in range(0, int(numCoin)):
				result.append(denoms[0]) 
		denoms = denoms[1:]
	return int(totalCount), result
