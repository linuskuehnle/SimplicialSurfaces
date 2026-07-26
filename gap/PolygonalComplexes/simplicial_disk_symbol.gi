BindGlobal( "__SIMPLICIAL_Disk_BoundaryFaceWalk",
function(disk, startVertex, firstEdge)
    local boundaryEdge, boundaryFace, faceByBoundaryEdge, boundaryVertex, 
          boundaryVertexPath, edge, foundNewEdge, newStartVertex, newFirstEdge;

    # Create a cyclic vertex path from startVertex in direction of firstEdge
    boundaryVertex := 0;
    boundaryVertexPath := [];
    boundaryEdge := firstEdge;
    while boundaryVertex <> startVertex do
        if VerticesOfEdge(disk, edge)[1] = boundaryVertex then
            boundaryVertex := VerticesOfEdge(disk, edge)[2];
        else
            boundaryVertex := VerticesOfEdge(disk, edge)[1];
        fi;
        Add(boundaryVertexPath, boundaryVertex);

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
            Error("boundary face walk failed: given complex is not a disk");
        fi;
    od;

    # Collect the face of each boundary edge
    faceByBoundaryEdge := [];
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
    boundaryFace := faceByBoundaryEdge[boundaryEdge];
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
    newFirstEdge   := 0;
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

    return boundaryVertex, faceByBoundaryEdge, newStartVertex, newFirstEdge;
end);

