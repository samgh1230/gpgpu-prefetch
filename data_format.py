f = open("./sssp/USA-road-d.FLA.gr","r")
output = open("usa-road.csv","w")
for line in f:
    if(line.startswith("a")):
        line = line.strip()
        mark,start_vertex, end_vertex,weight = line.split(" ")
        output.writelines(str(start_vertex)+" "+str(end_vertex)+"\n")
f.close()
output.close()
