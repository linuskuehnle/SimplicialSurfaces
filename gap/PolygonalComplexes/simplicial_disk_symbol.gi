BindGlobal( "__SIMPLICIAL_DiskSymbol_BoundaryWalk",
function(disk, startVertex, firstEdge)
    local boundaryVertexPath, boundaryVertexDegrees, faceByBoundaryEdge,
          newStartVertex, newFirstEdge, boundaryVertex, boundaryEdge,
          boundaryFace, innerFace, edge, foundNewEdge;

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
    boundaryVertex := startVertex;
    boundaryEdge   := firstEdge;
    repeat
        Add(boundaryVertexPath   , boundaryVertex);
        Add(boundaryVertexDegrees, Length(FacesOfEdge(disk, boundaryEdge)));

        if VerticesOfEdge(disk, boundaryEdge)[1] = boundaryVertex then
            boundaryVertex := VerticesOfEdge(disk, boundaryEdge)[2];
        else
            boundaryVertex := VerticesOfEdge(disk, boundaryEdge)[1];
        fi;

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
    until boundaryVertex = startVertex;

    # Collect the face of each boundary edge
    for edge in BoundaryEdges(disk) do
        # faces of edge incidence of a boundary edge has exactly one face
        boundaryFace := FacesOfEdge(disk, edge)[1];

        Add(faceByBoundaryEdge, boundaryFace, edge);
    od;

    # Find new starting vertex of enclosed complex (disk/tree)
    newStartVertex := 0;
    #
    # We need the face incident to the edge connecting the start vertex
    # and the last vertex relative to the vertex path.
    boundaryEdge := Filtered( EdgesOfVertex(disk, startVertex),
                              e -> e <> firstEdge and IsBoundaryEdge(disk, e) )[1];
    boundaryFace := faceByBoundaryEdge[boundaryEdge];
    for edge in EdgesOfFace(disk, boundaryFace) do
        if not IsBoundaryEdge(disk, edge) then
            if VerticesOfEdge(disk, edge)[1] = startVertex then
                newStartVertex := VerticesOfEdge(disk, edge)[2];
            else
                newStartVertex := VerticesOfEdge(disk, edge)[1];
            fi;

            innerFace := Filtered(FacesOfEdge(disk, edge), f -> f <> boundaryFace)[1];

            newFirstEdge := Filtered( EdgesOfFace(disk, innerFace),
                                      e -> e <> edge and
                                           e in EdgesOfVertex(disk, newStartVertex))[1];
            break;
        fi;
    od;

    return [boundaryVertexPath, boundaryVertexDegrees, faceByBoundaryEdge,
            newStartVertex, newFirstEdge];
end);

BindGlobal( "__SIMPLICIAL_DiskSymbol_PeelDisk",
function(disk, boundaryVertexPath)
    local isBoundaryVertex, peeledVerticesOfEdges, peeledEdgesOfFaces,
          isEdgeOfBoundaryVertex, e, f, vertices, edges, newDisk;

    isBoundaryVertex := List(Vertices(disk), v -> v in boundaryVertexPath);

    peeledVerticesOfEdges := [];
    isEdgeOfBoundaryVertex    := [];
    for e in [1..Length(VerticesOfEdges(disk))] do
        vertices := VerticesOfEdge(disk, e);

        if not ForAny(vertices, v -> isBoundaryVertex[v]) then
            Add(peeledVerticesOfEdges, vertices, e);
            Add(isEdgeOfBoundaryVertex, false);
        else
            Add(isEdgeOfBoundaryVertex, true);
        fi;
    od;

    peeledEdgesOfFaces := [];
    for f in [1..Length(EdgesOfFaces(disk))] do
        edges := EdgesOfFace(disk, f);

        if not ForAny(edges, e -> isEdgeOfBoundaryVertex[e]) then
            Add(peeledEdgesOfFaces, edges, f);
        fi;
    od;

    return SimplicialComplexByDownwardIncidence(peeledVerticesOfEdges, peeledEdgesOfFaces);
end);

BindGlobal( "__SIMPLICIAL_DiskSymbol_FindSubdisks",
function(disk)
    local subdisks, subdisk, trees, tree, separator, vertexComponentLinks,
          v, e, vertexHasIsolatedEdge, vertexSCCs, vertexIsTreeComponent,
          vertices, isolatedEdges, edgesOfVertices, facesOfEdges, complex,
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
                Add(vertexSCCs[v], subdisk);
            fi;
        od;
    od;
    #
    vertexIsTreeComponent := List([1..Length(Vertices(disk))], v -> false);
    vertexComponentLinks  := List([1..Length(Vertices(disk))], v -> []);
    for v in Vertices(disk) do
        if   Length(vertexSCCs[v]) >= 2 then
            vertexIsTreeComponent[v] := true;

            vertexComponentLinks[v] := vertexSCCs[v];
        elif vertexHasIsolatedEdge[v] and Length(vertexSCCs[v]) = 1 then
            vertexIsTreeComponent[v] := true;

            Add(vertexComponentLinks[v], vertexSCCs[v][1]);
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
            if vertexHasIsolatedEdge[v] then
                isolatedEdges := Filtered(EdgesOfVertex(disk, v), e -> e in IsolatedEdges(disk));

                Add(edgesOfVertices, isolatedEdges, v);
            else
                Add(edgesOfVertices, [], v);
            fi;
        fi;
    od;

    facesOfEdges    := [];
    for e in Union(edgesOfVertices) do
        Add(facesOfEdges, [], e);
    od;
    #
    complex := SimplicialComplexByUpwardIncidence(edgesOfVertices, facesOfEdges);
    #
    trees   := ConnectedComponents(complex); # TODO: find out why ConnectedComponents
                                             # does not return the trees as expected.

    # Compute the remaining component links which are the ones containing a tree.
    for tree in trees do
        for separator in [1..Length(vertexComponentLinks)] do
            if Length(vertexComponentLinks) = 0 then
                continue;
            fi;

            for v in Vertices(tree) do
                if v = separator then
                    Add(vertexComponentLinks[separator], tree);
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
            if Length(EdgesOfVertex(v, tree)) = 1 and not IsBound(vertexComponentLinks[v]) then
                e := EdgesOfVertex(v, tree)[1];
                Add(looseEdges, e);
            fi;
        od;

        Add(looseEdgesByTree, looseEdges);
    od;

    return [subdisks, trees, vertexComponentLinks, looseEdgesByTree];
end);

BindGlobal( "__SIMPLICIAL_DiskSymbol_BuildSymbol",
function(disk, startVertex, firstEdge)
    local layerPathDirections, layerComponentLinks, nextLayerConnects, diskQueue,
          boundaryWalkRes, findSubdisksRes, boundaryVertexPath,
          boundaryVertexDegrees, faceByBoundaryEdge, newStartVertex, newFirstEdge,
          peeledDisk, subdisks, trees, componentLinks, looseEdgesByTree;

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

        peeledDisk := __SIMPLICIAL_DiskSymbol_PeelDisk(disk, boundaryVertexPath);

        findSubdisksRes := __SIMPLICIAL_DiskSymbol_FindSubdisks(peeledDisk);
        #
        subdisks         := findSubdisksRes[1];
        trees            := findSubdisksRes[2];
        componentLinks   := findSubdisksRes[3];
        looseEdgesByTree := findSubdisksRes[4];

        # TODO: Compute loose tree edge connects with boundary vertex path. Mark
        # both vertices that form the face which connects to the loose tree edge.

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