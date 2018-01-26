
def binomialCoeffDP(n , k):
    C = [[0 for x in range(k+1)] for x in range (n+1)]
    for i in range(n+1):
    	   for j in range (min(i,k)+1):
            if j == 0 or j == i:
    	           C[i][j] = 1
	          else:
                 C[i][j] = C[i-1][j-1] + C[i-1][j]
    return C[n][k]
    
def catDP(n):
    if (n == 0 or n == 1):
        return 1
    catalan = [0 for i in range(n + 1)]
    catalan[0] = 1
    catalan[1] = 1
    for i in range(2, n + 1):
        catalan[i] = 0
        for j in range(i):
            catalan[i] = catalan[i] + catalan[j] * catalan[i-j-1]
    return catalan[n]

def pellDP(n):
    pellArray = [0 for x in range(n+1)]
    pellArray[0] = 0
    pellArray[1] = 1
    for i in range(2, n+1):
        pellArray[i] = 2*pellArray[i-1]+ pellArray[i-2]
    return pellArray[n]
