BindGlobal( "__SIMPLICIAL_DiskSymbol_BoundaryWalk",
function(disk, startVertex, firstEdge)
    local boundaryVertexPath, boundaryVertexDegrees, faceByBoundaryEdge,
          newStartVertex, newFirstEdge, boundaryVertex, boundaryEdge,
          boundaryFace, edge, foundNewEdge;

    boundaryVertexPath    := [];
    boundaryVertexDegrees := [];
    faceByBoundaryEdge    := [];

    if Length(Faces(disk)) = 0 then
        newStartVertex := 0;
        newFirstEdge   := 0;

        return [boundaryVertexPath, boundaryVertexDegrees, faceByBoundaryEdge,
                newStartVertex, newFirstEdge];
    fi;

    # Create a cyclic vertex path from startVertex in direction of firstEdge
    boundaryVertex     := 0;
    boundaryEdge       := firstEdge;
    while boundaryVertex <> startVertex do
        if VerticesOfEdge(disk, edge)[1] = boundaryVertex then
            boundaryVertex := VerticesOfEdge(disk, edge)[2];
        else
            boundaryVertex := VerticesOfEdge(disk, edge)[1];
        fi;
        Add(boundaryVertexPath   , boundaryVertex);
        Add(boundaryVertexDegrees, FacesOfEdge(disk, edge));

        # Find new boundary edge by checking the edges of vertex incidence
        # for the new boundary vertex
        foundNewEdge := false;
        for edge in EdgesOfVertex(disk, boundaryVertex) do
            if edge <> boundaryEdge and IsBoundaryEdge(disk, edge) then
                boundaryEdge := edge;
                foundNewEdge := true;
                break;
            fi;
        od;

        # Catch the case where the while loop would not terminate for a given
        # value of arg disk
        if not foundNewEdge then
            Error("boundary face walk failed: given complex is not a disk\n");
        fi;
    od;

    # Collect the face of each boundary edge
    for boundaryEdge in BoundaryEdges(disk) do
        # faces of edge incidence of a boundary edge has exactly one face
        boundaryFace := FacesOfEdge(disk, boundaryEdge)[1];

        Add(faceByBoundaryEdge, boundaryFace, boundaryEdge);
    od;

    # Find new starting vertex of enclosed complex (disk/tree)
    newStartVertex := 0;
    #
    # boundaryEdge is the edge that connects the last two vertices of the
    # boundary vertex path, so we can use the incident face to find the
    # next starting vertex and the next first edge
    boundaryFace   := faceByBoundaryEdge[boundaryEdge];
    for edge in EdgesOfFace(disk, boundaryFace) do
        if not IsBoundaryEdge(edge) then
            if VerticesOfEdge(disk, edge)[1] = startVertex then
                newStartVertex := VerticesOfEdge(disk, edge)[2];
            else
                newStartVertex := VerticesOfEdge(disk, edge)[1];
            fi;
            break;
        fi;
    od;

    # Find new first edge of enclosed complex (disk/tree)
    newFirstEdge := 0;
    #
    # If there is no new starting vertex, we do not need to check for
    # a new first edge
    if newStartVertex <> 0 then
        boundaryFace := faceByBoundaryEdge[1];

        for edge in EdgesOfFace(disk, boundaryFace) do
            if newStartVertex in VerticesOfEdge(disk, edge) then
                newFirstEdge := edge;
                break;
            fi;
        od;
    fi;

    return [boundaryVertexPath, boundaryVertexDegrees, faceByBoundaryEdge,
            newStartVertex, newFirstEdge];
end);

BindGlobal( "__SIMPLICIAL_DiskSymbol_ShrinkDisk",
function(disk, boundaryVertexPath)
    local verticesOfEdges, edgesOfFaces, removedEdgeLabels, i,
          vertices, edges, newDisk;

    verticesOfEdges   := [];
    removedEdgeLabels := [];
    for i in [1..Length(VerticesOfEdges(disk))] do
        vertices := VerticesOfEdges(disk)[i];

        if not ForAny(vertices, v -> v in boundaryVertexPath) then
            Add(verticesOfEdges, vertices, i);
        else
            Add(removedEdgeLabels, i);
        fi;
    od;

    edgesOfFaces := [];
    for i in [1..Length(EdgesOfFaces(disk))] do
        edges := EdgesOfFaces(disk)[i];

        if not ForAny(edges, e -> e in removedEdgeLabels) then
            Add(edgesOfFaces, edges, i);
        fi;
    od;

    return SimplicialComplexByDownwardIncidence(verticesOfEdges, edgesOfFaces);
end);

BindGlobal( "__SIMPLICIAL_DiskSymbol_FindSubdisks",
function(disk)
    local subdisks, subdisk, trees, tree, separator, componentLinks,
          v, e, vertexHasIsolatedEdge, vertexSCCs, vertexIsTreeComponent,
          vertices, edges, edgesOfVertices, facesOfEdges, complex,
          looseEdgesByTree, looseEdges;

    # Split into subdisks by computing the strongly connected components.
    subdisks := StronglyConnectedComponents(disk);

    # If disk consists of just one SCC and that SCC equals disk, return early.
    if Length(subdisks) = 1 and subdisks[1] = disk then
        return [[disk], [], [], []];
    fi;

    # Find all vertices of a subdisk that match one of the two cases:
    # - incidence to at least two different subdisks
    # - incidence to one subdisk and at least one isolated edge
    #
    vertexHasIsolatedEdge := List([1..Length(Vertices(disk))], v -> false);
    for e in IsolatedEdges(disk) do
        for v in VerticesOfEdge(disk, e) do
            vertexHasIsolatedEdge[v] := true;
        od;
    od;
    #
    vertexSCCs            := List([1..Length(Vertices(disk))], v -> []);
    for v in Vertices(disk) do
        for subdisk in subdisks do
            if v in Vertices(subdisk) then
                Add(vertexSCCs, subdisk, v);
            fi;
        od;
    od;
    #
    vertexIsTreeComponent := List([1..Length(Vertices(disk))], v -> false);
    for v in Vertices(disk) do
        if   Length(vertexSCCs[v]) >= 2 then
            vertexIsTreeComponent[v] := true;

            Add(componentLinks, vertexSCCs, v);
        elif vertexHasIsolatedEdge[v] and Length(vertexSCCs[v]) = 1 then
            vertexIsTreeComponent[v] := true;

            Add(componentLinks, [ vertexSCCs[v][1] ], v);
        elif Length(vertexSCCs[v]) = 0 then
            vertexIsTreeComponent[v] := true;
        fi;
    od;

    # Derive trees by first building a simplicial complex not containing any
    # subdisk component despite allow separator vertices.
    #
    edgesOfVertices := [];
    for v in [1..Length(EdgesOfVertices(disk))] do
        if vertexIsTreeComponent[v] then
            edges := EdgesOfVertex(disk, v);
        else
            edges := [];
        fi;

        Add(edgesOfVertices, edges, v);
    od;
    facesOfEdges    := [];
    for e in Union(edgesOfVertices) do
        Add(facesOfEdges   , [], e);
    od;
    #
    complex := SimplicialComplexByUpwardIncidence(edgesOfVertices, facesOfEdges);
    #
    trees   := ConnectedComponents(complex);

    # Compute the remaining component links which are the ones containing a tree.
    for tree in trees do
        for separator in [1..Length(componentLinks)] do
            if not IsBound(componentLinks[separator]) then
                continue;
            fi;

            for v in Vertices(tree) do
                if v = separator then
                    Add(componentLinks[separator], tree);
                    break;
                fi;
            od;
        od;
    od;

    # Find tree edges that are loose which are edges that have
    # only one neighbour edge and whose outer vertex is not a separator
    looseEdgesByTree := [];
    for tree in trees do
        looseEdges := [];

        for v in Vertices(tree, v) do
            if Length(EdgesOfVertex(v, tree)) = 1 and not IsBound(componentLinks[v]) then
                e := EdgesOfVertex(v, tree)[1];
                Add(looseEdges, e);
            fi;
        od;

        Add(looseEdgesByTree, looseEdges);
    od;

    return [subdisks, trees, componentLinks, looseEdgesByTree];
end);

BindGlobal( "__SIMPLICIAL_DiskSymbol_BuildSymbol",
function(disk, startVertex, firstEdge)
    local layerPathDirections, layerComponentLinks, nextLayerConnects, diskQueue,
          boundaryWalkRes, findSubdisksRes, boundaryVertexPath,
          boundaryVertexDegrees, faceByBoundaryEdge, newStartVertex, newFirstEdge,
          shrinkedDisk, subdisks, trees, componentLinks, looseEdgesByTree;

    layerPathDirections := [];
    layerComponentLinks := [];
    nextLayerConnects   := [];

    diskQueue := [disk];

    while Length(diskQueue) > 0 do
        disk := Remove(diskQueue);

        boundaryWalkRes := __SIMPLICIAL_DiskSymbol_BoundaryWalk(disk, startVertex, firstEdge);
        #
        boundaryVertexPath    := boundaryWalkRes[1];
        boundaryVertexDegrees := boundaryWalkRes[2];
        faceByBoundaryEdge    := boundaryWalkRes[3];
        newStartVertex        := boundaryWalkRes[4];
        newFirstEdge          := boundaryWalkRes[5];

        Add(nextLayerConnects  , [newStartVertex, startVertex]);
        Add(layerPathDirections, firstEdge);

        startVertex := newStartVertex;
        firstEdge   := newFirstEdge;

        shrinkedDisk := __SIMPLICIAL_DiskSymbol_ShrinkDisk(disk, boundaryVertexPath);

        findSubdisksRes := __SIMPLICIAL_DiskSymbol_FindSubdisks(shrinkedDisk);
        #
        subdisks         := findSubdisksRes[1];
        trees            := findSubdisksRes[2];
        componentLinks   := findSubdisksRes[3];
        looseEdgesByTree := findSubdisksRes[4];

        # TODO: Check if we need euler characteristic check for each subdisk
        # before adding it to the disk queue.

        diskQueue := Concatenation(diskQueue, subdisks);
    od;
end);

InstallMethod( DiskSymbolOfSimplicialComplex,
"for a simplicial complex and two positive integers",
[IsSimplicialComplex, IsPosInt, IsPosInt],
function(complex, startVertex, firstEdge)
    # Check if complex is a simplicial disk
    if   EulerCharacteristic(complex) <> 1 then
        Error("DiskSymbolOfSimplicialComplex: euler characteristic of complex must be equal to 1\n");
    elif not IsClosedComplex(complex)      then
        Error("DiskSymbolOfSimplicialComplex: complex must be closed\n");
    elif not IsConnectedComplex(complex)   then
        Error("DiskSymbolOfSimplicialComplex: complex must be connected\n");
    fi;

    if   not IsBoundaryVertex(complex, startVertex) then
        Error(Concatenation("DiskSymbolOfSimplicialComplex: given value for argument ",
                            "startVertex must be a boundary vertex of given complex\n"));
    elif not IsBoundaryEdge  (complex, firstEdge  ) then
        Error(Concatenation("DiskSymbolOfSimplicialComplex: given value for argument ",
                            "firstEdge must be a boundary edge of given complex\n"));
    fi;

    return DiskSymbolOfSimplicialComplexNC(complex, startVertex, firstEdge);
end);

InstallMethod( DiskSymbolOfSimplicialComplexNC,
"for a simplicial complex and two positive integers",
[IsSimplicialComplex, IsPosInt, IsPosInt],
function(complex, startVertex, firstEdge)
    local disk;

    disk := ShallowCopy(complex);

    __SIMPLICIAL_DiskSymbol_BuildSymbol(disk, startVertex, firstEdge);
end);