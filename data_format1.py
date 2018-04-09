import sys
if __name__ == '__main__':
    print sys.argv[1]
    print sys.argv[2]
    f = open(sys.argv[1],"r")
    output = open(sys.argv[2],"w")
    for line in f:
        if( not line.startswith("#")):
            line = line.strip()
            # print line
            start_vertex, end_vertex = line.split()
            # print start_vertex, end_vertex
            output.writelines(str(start_vertex)+"|"+str(end_vertex)+"\n")
    f.close()
    output.close()
