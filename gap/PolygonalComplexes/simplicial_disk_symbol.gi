BindGlobal( "__SIMPLICIAL_DiskSymbol_BoundaryWalk",
function(disk, startVertex, firstEdge)
    local boundaryVertexPath, boundaryEdgePath, boundaryVertexDegrees, faceByBoundaryEdge,
          newStartVertex, newFirstEdge, boundaryVertex, boundaryEdge,
          boundaryFace, innerFace, edge, foundNewEdge;

    boundaryVertexPath    := [];
    boundaryEdgePath      := [];
    boundaryVertexDegrees := [];
    faceByBoundaryEdge    := [];

    if Length(Faces(disk)) = 0 then
        return [ boundaryVertexPath, boundaryEdgePath,
                 boundaryVertexDegrees, faceByBoundaryEdge ];
    fi;

    # Create a cyclic vertex path from startVertex in direction of firstEdge
    boundaryVertex := startVertex;
    boundaryEdge   := firstEdge;
    repeat
        Add(boundaryVertexPath   , boundaryVertex);
        Add(boundaryEdgePath     , boundaryEdge);
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

    return [ boundaryVertexPath, boundaryEdgePath,
             boundaryVertexDegrees, faceByBoundaryEdge ];
end);

BindGlobal( "__SIMPLICIAL_DiskSymbol_FindBoundaryStart",
function(disk, subdisk, boundaryVertexPath, boundaryEdgePath)
    local hookVertex, hookFirstEdge, startVertex, firstEdge, v, n, e, boundaryFace, innerFace;

    # First compute hook vertex
    for v in BoundaryVertices(subdisk) do
        for n in NeighbourVerticesOfVertex(disk, v) do
            if n in boundaryVertexPath then
                if not IsBound(hookVertex) or Position(boundaryVertexPath, n) < Position(boundaryVertexPath, hookVertex) then
                    hookVertex := n;
                    break;
                fi;
            fi;
        od;
    od;
    #
    hookFirstEdge := boundaryEdgePath[Position(boundaryVertexPath, hookVertex)];

    # We need the face incident to the edge connecting the start vertex
    # and the last vertex relative to the vertex path.
    boundaryFace := FacesOfEdge(disk, boundaryEdgePath[Length(boundaryEdgePath)])[1];
    for e in EdgesOfFace(disk, boundaryFace) do
        if not IsBoundaryEdge(disk, e) then
            if   VerticesOfEdge(disk, e)[1] = hookVertex then
                startVertex := VerticesOfEdge(disk, e)[2];
            elif VerticesOfEdge(disk, e)[2] = hookVertex then
                startVertex := VerticesOfEdge(disk, e)[1];
            else
                continue;
            fi;

            innerFace := Filtered(FacesOfEdge(disk, e), f -> f <> boundaryFace)[1];

            firstEdge := Filtered( EdgesOfFace(disk, innerFace),
                                      faceEdge -> faceEdge <> e and
                                           faceEdge in EdgesOfVertex(disk, startVertex))[1];
            break;
        fi;
    od;

    return [hookVertex, startVertex, firstEdge];
end);

BindGlobal( "__SIMPLICIAL_DiskSymbol_BuildCore",
function(disk, boundaryVertexPath)
    local isBoundaryVertex, peeledVerticesOfEdges, peeledEdgesOfFaces,
          isEdgeOfBoundaryVertex, v, e, f, vertices, edges, newDisk;

    isBoundaryVertex := [];
    for v in Vertices(disk) do
        Add(isBoundaryVertex, v in boundaryVertexPath, v);
    od;

    peeledVerticesOfEdges  := [];
    isEdgeOfBoundaryVertex := [];
    for e in [1..Length(VerticesOfEdges(disk))] do
        if not IsBound(VerticesOfEdges(disk)[e]) then
            continue;
        fi;
        vertices := VerticesOfEdge(disk, e);

        if not ForAny(vertices, v -> isBoundaryVertex[v]) then
            Add(peeledVerticesOfEdges, vertices, e);
            Add(isEdgeOfBoundaryVertex, false, e);
        else
            Add(isEdgeOfBoundaryVertex, true, e);
        fi;
    od;

    peeledEdgesOfFaces := [];
    for f in [1..Length(EdgesOfFaces(disk))] do
        if not IsBound(EdgesOfFaces(disk)[f]) then
            continue;
        fi;
        edges := EdgesOfFace(disk, f);

        if not ForAny(edges, e -> isEdgeOfBoundaryVertex[e]) then
            Add(peeledEdgesOfFaces, edges, f);
        fi;
    od;

    return SimplicialComplexByDownwardIncidence(peeledVerticesOfEdges, peeledEdgesOfFaces);
end);

BindGlobal( "__SIMPLICIAL_DiskSymbol_FindSubcomponents",
function(disk)
    local subdisks, subdisk, trees, tree, separator, vertexComponentLinks,
          v, e, vertexHasIsolatedEdge, vertexSCCs, vertexIsTreeComponent,
          verts, treeVerticesOfEdges, treeComplex,
          looseVerticesByTree, looseVertices, i;

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
    vertexHasIsolatedEdge := [];
    for v in Vertices(disk) do
        Add(vertexHasIsolatedEdge, false, v);
    od;

    for e in IsolatedEdges(disk) do
        for v in VerticesOfEdge(disk, e) do
            vertexHasIsolatedEdge[v] := true;
        od;
    od;
    #
    vertexSCCs := [];
    for v in Vertices(disk) do
        Add(vertexSCCs, [], v);

        for i in [1..Length(subdisks)] do
            subdisk := subdisks[i];

            if v in Vertices(subdisk) then
                Add(vertexSCCs[v], i);
            fi;
        od;
    od;
    #
    vertexIsTreeComponent := [];
    vertexComponentLinks  := [];
    for v in Vertices(disk) do
        Add(vertexIsTreeComponent, false, v);
        Add(vertexComponentLinks , []   , v);

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

    # Derive trees
    #
    treeVerticesOfEdges := [];
    for e in [1..Length(VerticesOfEdges(disk))] do
        if not IsBound(VerticesOfEdges(disk)[e]) then
            continue;
        fi;
        verts := VerticesOfEdge(disk, e);

        if not ForAll( verts, v -> vertexIsTreeComponent[v] ) then
            continue;
        fi;

        Add(treeVerticesOfEdges, verts, e);
    od;
    #
    treeComplex := SimplicialComplexByDownwardIncidence( treeVerticesOfEdges, [] );
    trees       := ConnectedComponents(treeComplex);

    # Compute the remaining component links which are the ones containing a tree.
    for i in [1..Length(trees)] do
        tree := trees[i];

        for separator in [1..Length(vertexComponentLinks)] do
            if not IsBound(vertexComponentLinks[separator]) or
               Length(vertexComponentLinks[separator]) = 0 then
                continue;
            fi;

            for v in Vertices(tree) do
                if v = separator then
                    Add(vertexComponentLinks[separator], Length(subdisks) + i);
                    break;
                fi;
            od;
        od;
    od;

    # Find tree vertices that are loose which are vertices that have
    # only one incident edge and are not a separator.
    looseVerticesByTree := [];
    for tree in trees do
        looseVertices := Filtered( Vertices(tree),
                                   v -> Length(EdgesOfVertex(tree, v) ) = 1 and
                                        Length(vertexComponentLinks[v]) = 0 );

        Add(looseVerticesByTree, looseVertices);
    od;

    return [subdisks, trees, vertexComponentLinks, looseVerticesByTree];
end);


BindGlobal( "__SIMPLICIAL_DiskSymbol_HookLooseVertices",
function(disk, looseVertices, boundaryVertexPath)
    local v, hookVertices, hookVerticesByLooseVertex;

    hookVerticesByLooseVertex := [];
    for v in looseVertices do
        hookVertices := Filtered( NeighbourVerticesOfVertex(disk, v),
                                  n -> n in boundaryVertexPath );

        Add(hookVerticesByLooseVertex, hookVertices, v);
    od;

    return hookVerticesByLooseVertex;
end);


BindGlobal( "__SIMPLICIAL_DiskSymbol_BuildSymbol",
function(disk, startVertex, firstEdge)
    local allSubdisks, boundaryVertexPathOfDisk, boundaryVertexDegreesOfDisk,
          pathDataOfDisk, layerConnectsOfDisk, componentLinksOfDisk,
          hookVertsByLooseVertOfDisk, diskQueue, queueElem,
          boundaryWalkRes, findSubcompsRes, boundaryVertexPath, boundaryEdgePath,
          boundaryVertexDegrees, faceByBoundaryEdge, newStartVertex, newFirstEdge,
          peeledDisk, subdisks, subdisk, trees, newComponentLinks, looseVerticesByTree,
          looseVerts, hookVertsByLooseVert, diskComponentLinks, boundaryStartRet,
          layerConnects, hookVertex;
        
    allSubdisks := [];

    boundaryVertexPathOfDisk    := [];
    boundaryVertexDegreesOfDisk := [];

    layerConnectsOfDisk   := [];
    componentLinksOfDisk := [[]]; # first disk does not have any subcomponents.
    #
    hookVertsByLooseVertOfDisk := [];

    diskQueue := [[disk, startVertex, firstEdge]];

    while Length(diskQueue) > 0 do
        queueElem := Remove(diskQueue);
        #
        disk        := queueElem[1];
        startVertex := queueElem[2];
        firstEdge   := queueElem[3];

        Add(allSubdisks, disk);

        boundaryWalkRes := __SIMPLICIAL_DiskSymbol_BoundaryWalk(disk, startVertex, firstEdge);
        #
        boundaryVertexPath    := boundaryWalkRes[1];
        boundaryEdgePath      := boundaryWalkRes[2];
        boundaryVertexDegrees := boundaryWalkRes[3];
        faceByBoundaryEdge    := boundaryWalkRes[4];
        #
        Add(boundaryVertexPathOfDisk   , boundaryVertexPath);
        Add(boundaryVertexDegreesOfDisk, boundaryVertexDegrees);

        if Length(Faces(disk)) = 1 then
            # TODO: check if this is the correct way of handling disks containing
            # just one face.
            continue;
        fi;

        peeledDisk := __SIMPLICIAL_DiskSymbol_BuildCore(disk, boundaryVertexPath);
        if Length(Vertices(peeledDisk)) = 1 then
            # TODO: check if this is the correct way of handling disks whose
            # core is empty.
            continue;
        fi;
        #
        findSubcompsRes := __SIMPLICIAL_DiskSymbol_FindSubcomponents(peeledDisk);
        #
        subdisks            := findSubcompsRes[1];
        trees               := findSubcompsRes[2];
        newComponentLinks   := findSubcompsRes[3];
        looseVerticesByTree := findSubcompsRes[4];
        #
        if ForAny(subdisks, subdisk -> EulerCharacteristic(subdisk) <> 1) then
            Error("euler characteristic of a subdisk does not equal 1\n");
        fi;
        #
        Add(componentLinksOfDisk, newComponentLinks);
        #
        # Compute each subdisks boundary walk starting vertex and first edge along
        # with its boundary hook.
        layerConnects := [];
        #
        for subdisk in subdisks do
            boundaryStartRet := __SIMPLICIAL_DiskSymbol_FindBoundaryStart( disk,
                                                                           subdisk,
                                                                           boundaryVertexPath,
                                                                           boundaryEdgePath );
            #
            hookVertex  := boundaryStartRet[1];
            startVertex := boundaryStartRet[2];
            firstEdge   := boundaryStartRet[3];
            #
            Add(layerConnects, [hookVertex, startVertex, firstEdge]);

            Add(diskQueue, [subdisk, startVertex, firstEdge]);
        od;
        Add(layerConnectsOfDisk, layerConnects);

        looseVerts := Union(looseVerticesByTree);
        #
        hookVertsByLooseVert := __SIMPLICIAL_DiskSymbol_HookLooseVertices(
                                    disk,
                                    looseVerts,
                                    boundaryVertexPath
                                );
        #
        if ForAny(hookVertsByLooseVert, hookVerts -> Length(hookVerts) = 0) then
            Error("a loose vertex has no boundary neighbour vertices\n");
        fi;
        #
        Add(hookVertsByLooseVertOfDisk, hookVertsByLooseVert);
    od;

    # TODO: compute the code.

    return Error("Not implemented yet\n");
end);


InstallMethod( DiskSymbolOfSimplicialComplex,
"for a simplicial complex and two positive integers",
[IsSimplicialComplex, IsPosInt, IsPosInt],
function(complex, startVertex, firstEdge)
    # Check if complex is a simplicial disk
    if   not IsSimplicialSurface(complex) then
        Error("DiskSymbolOfSimplicialComplex: complex must be a simplicial surface\n");
    elif EulerCharacteristic(complex) <> 1 then
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
    local complexCpy;

    complexCpy := ShallowCopy(complex);

    __SIMPLICIAL_DiskSymbol_BuildSymbol(complexCpy, startVertex, firstEdge);
end);