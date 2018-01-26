def LCS(X, Y):
    m = len(X)
    n = len(Y)
    # Initialize an (m+1) times (n+1) matrix/2D array for memoization
    C = [[0] * (n + 1) for _ in range(m + 1)]
    for i in range(1, m+1):
        for j in range(1, n+1):
            # Case 1: If last characters in string are the same
            if X[i-1] == Y[j-1]: 
                C[i][j] = C[i-1][j-1] + 1
            # Case 2: If last characters in string are different, 
            # shorten one or the other and recurse
            else:
                C[i][j] = max(C[i][j-1], C[i-1][j])
     # If LCS exists, print length and call backTrack 
     # to print actual sequence
     if C[m][n] > 0:
        print "Length of LCS is %s." % C[m][n]
        print "LCS is %s." % backTrack(C, X, Y, m, n)
     else:
        print "No LCS exists."
    
def backTrack(C, X, Y, i, j):
    # Base case: length of either string is 0
    if i == 0 or j == 0:
        return ""
    # Case 1: If last characters in string are the same
    elif X[i-1] == Y[j-1]:
        return backTrack(C, X, Y, i-1, j-1) + X[i-1]
    # Case 2: If last characters in string are different, 
    # shorten one or the other and recurse
    else:
        if C[i][j-1] > C[i-1][j]:
            return backTrack(C, X, Y, i, j-1)
        else:
            return backTrack(C, X, Y, i-1, j)
