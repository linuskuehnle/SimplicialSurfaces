BindGlobal( "__SIMPLICIAL_DiskBoundaryWalk",
function(disk, startVertex, firstEdge)
    local boundaryVertexPath, boundaryVertexDegrees, faceByBoundaryEdge,
          newStartVertex, newFirstEdge, boundaryVertex, boundaryEdge, boundaryFace,
          edge, foundNewEdge;

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

BindGlobal( "__SIMPLICIAL_DiskShrink",
function(disk, boundaryVertexPath)
    local verticesOfEdges, edgesOfFaces, removedEdgeLabels, i, vertices, edges, newDisk;

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

BindGlobal( "__SIMPLICIAL_FindSubDisks",
function(disk)
    local subDisks;

    # Check for any vertices that do not fulfill umbrella condition. If there
    # are none, we do not have any subdisks.

    subDisks     := [];
    diskConnects := [];

    return [subDisks, diskConnects];
end);

BindGlobal( "__SIMPLICIAL_SymbolDiskStep",
function(disk, startVertex, firstEdge)
    local layerInterconnects, layerDirections, boundaryWalkRet, boundaryVertexPath,
          faceByBoundaryEdge, newStartVertex, newFirstEdge, shrinkedDisk, findSubDisksRet;

    layerInterconnects := [];
    layerDirections    := [];

    # TODO: Build while loop from here

    boundaryWalkRet := __SIMPLICIAL_DiskBoundaryWalk(disk, startVertex, firstEdge);

    boundaryVertexPath    := boundaryWalkRet[1];
    boundaryVertexDegrees := boundaryWalkRet[2];
    faceByBoundaryEdge    := boundaryWalkRet[3];
    newStartVertex        := boundaryWalkRet[4];
    newFirstEdge          := boundaryWalkRet[5];

    Add(layerInterconnects, [newStartVertex, startVertex]);
    Add(layerDirections   , firstEdge);

    startVertex := newStartVertex;
    firstEdge   := newFirstEdge;

    shrinkedDisk := __SIMPLICIAL_DiskShrink(disk, boundaryVertexPath);

    findSubDisksRet := __SIMPLICIAL_FindSubDisks(shrinkedDisk);

    subDisks     := findSubDisksRet[1];
    diskConnects := findSubDisksRet[2];
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

    __SIMPLICIAL_SymbolDiskStep(disk, startVertex, firstEdge);
end);