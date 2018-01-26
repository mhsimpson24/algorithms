class Graph():

    def __init__(self, V):
        self.V = V
        self.adj =  [[0 * self.V] * self.V]

    def twoColor(self, start):
        if self.V == 0:
            return "Trivially two colorable"  
        color = ["NULL"] * self.V
        color[start] = "red"

        queue = []
        queue.append(start)

        while len(queue) > 0:
            print queue
            p = queue.pop()
            if p in (self.adj[p]):
                return "Not two colorable"
            for p in range(self.V):
                for u in self.adj[p]:
                    print queue
                    if color[u] == "NULL":
                            if color[p] == "NULL":
                                color[p] = "red"
                            if color[p] == "red":
                                color[u] = "blue"
                            else:
                                color[u] = "red"   
                            queue.append(u)
                    elif p in self.adj[u] and color[p] == color[u]:
                        return "Not two colorable"
                if self.V == 1:
                    return "Trivially two colorable" 
        return "Two colorable with adjacency lists %s and vertex colors %s" % (self.adj, color) 
