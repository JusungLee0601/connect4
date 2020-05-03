#lang forge

----------------Sigs----------------

sig Row {
    prev_row: lone Row,
    next_row: lone Row
}

sig Column {
    prev_col: lone Column,
    next_col: lone Column
}

//sig Player {moves: set Row->Column}

sig Board {
    p1: set Row->Column,
    p2: set Row->Column
}

----------------Setup----------------

//Ensures the prev and next relations are properly formed for rows and columns
pred wellformed {
    one a: Row | no a.prev_row //First row has no previous
    one b: Row | no b.next_row //Last row has no next
    prev_row = ~next_row //Prev and next should be mirrored (transpose)
    all a: Row, b: Row | {
        //Any 2 distinct rows should be connected via prev or next
        not(a = b) implies (a in b.^prev_row) or (a in b.^next_row)
    }

    //Apply the same contrictions for columns
    one a: Column | no a.prev_col
    one b: Column | no b.next_col
    prev_col = ~next_col
    all a: Column, b: Column | {
        not(a = b) implies (a in b.^prev_col) or (a in b.^next_col)
    }

    //Two players cannot have played the same index
    no Board.p1 & Board.p2 //test if necessary?
}

//Checks that given board complies with gravity constrictions
//pred valid_gravity[b: Board] {
//    //For every move between both players
//    all a: (p1.moves + p2.moves) | {
//        
//    }
//}

----------------Turns----------------

//p1's turn if both players have the same # of moves
pred p1_turn[b: Board] {
    #(b.p1) = #(b.p2)
}

//p2's turn otherwise
pred p2_turn[b: Board] {
    subtract[#(b.p1),1] = #(b.p2)
}

pred valid[b: Board] {
    p1_turn[b] or p2_turn[b]
}

----------------Win Cons----------------

//Checks if given player has won vertically
pred vertical_w[p: set Row->Column] {
    //Look for 3 distinct, vertically adjacent indices for given player
    some x,y,z: Row | some c: Column | {
        not x = y
        not x = z
        not y = z
        (x->c + y->c + z->c) in p
        x.prev_row = y
        y.prev_row = z
    }
}

//Checks if given player has won horizontally
pred horizontal_w[p: set Row->Column] {
    //Look for 3 distinct, horizontally adjacent indices for given player
    some r: Row | some x,y,z: Column | {
        not x = y
        not x = z
        not y = z
        (r->x + r->y + r->z) in p
        x.next_col = y
        y.next_col = z
    }
}

//Checks if given player has won diagonally
pred diagonal_w[p: set Row->Column] {
    //Look for distinct, diagonally adjacent indices for given player
    some a,b,c: Row | some x,y,z: Column | {
        not a = b
        not a = c
        not b = c
        not x = y
        not x = z
        not y = z
        (a->x + b->y + c->z) in p
        a.prev_row = b
        b.prev_row = c
        x.next_col = y
        y.next_col = z
    }
}

//Combined win conditions
pred won[p: set Row->Column] {
    vertical_w[p] or diagonal_w[p] or horizontal_w[p]
}

pred finished[b: Board] {
    won[b.p1] or won[b.p2]
}

--------------------Win/Turn Tests---------------------

inst boiler {
  Board = Board0
  Row = Row0 + Row1 + Row2 + Row3
  Column = Column0 + Column1 + Column2 + Column3
  next_row = Row0 -> Row1 + Row1 -> Row2 + Row2 -> Row3
  prev_row = Row3 -> Row2 + Row2 -> Row1 + Row1 -> Row0
  next_col = Column0 -> Column1 + Column1 -> Column2 + Column2 -> Column3
  prev_col = Column3 -> Column2 + Column2 -> Column1 + Column1 -> Column0
}

inst emptyGame {
  boiler
  p1 = none
  p2 = none
}

//Empty game
expect {
    wfEmpty1: {wellformed} for exactly emptyGame is sat
    wfEmpty2: {not wellformed} for exactly emptyGame is unsat    
}

inst horizontal {
    boiler
    p1 = Board -> (Row3 -> Column0 + Row2 -> Column0 + Row2 -> Column1)
    p2 = Board -> (Row3 -> Column1 + Row3 -> Column2 + Row3 -> Column3)
}

inst vertical {
    boiler
    p1 = Board -> (Row3 -> Column0 + Row2 -> Column0 + Row1 -> Column0)
    p2 = Board -> (Row3 -> Column1 + Row3 -> Column2)
}

inst diagonal {
    boiler
    p1 = Board -> (Row3 -> Column1 + Row3 -> Column2 + Row2 -> Column2)
    p2 = Board -> (Row3 -> Column0 + Row2 -> Column1 + Row1 -> Column2)
}

inst moreX {
    boiler
    p1 = Board -> (Row3 -> Column0 + Row2 -> Column0 + Row2 -> Column1)
    p2 = Board -> (Row3 -> Column1)
}

//Win tests
expect {
    wellformed: {wellformed} for exactly horizontal is sat
    ht: {won[Board.p2]} for exactly horizontal is sat
    hf: {vertical_w[Board.p1]} for exactly horizontal is unsat
    vt: {won[Board.p1]} for exactly vertical is sat
    vf: {won[Board.p2]} for exactly vertical is unsat
    dt: {won[Board.p2]} for exactly diagonal is sat
}

//Turn tests
expect {
    valid: {valid[Board]} for exactly horizontal is sat
    p1: {p1_turn[Board]} for exactly horizontal is sat
    p2: {p2_turn[Board]} for exactly horizontal is unsat
    moreX: {p1_turn[Board] or p2_turn[Board]} for exactly moreX is unsat
    noWin: {won[Board.p1] or won[Board.p2]} for exactly moreX is unsat
}

----------------Trace----------------

//Define initial state of the game
state[Board] initialBoard {
    no p1 //No moves have been made yet
    no p2
}

//Define parameters for transitioning (making a move)
transition[Board] move[r: Row, c: Column] {
    //Move being made on an empty index
    not r->c in (p1 + p2)

    //if r is not the bottom row, there must already be a move below r->c
    some r.prev_row implies (r.prev_row)->c in (p1 + p2) //GRAVITY
    
    //Player whose turn it is gets r->c
    p1_turn[this] implies {
        p1' = p1 + r->c
        p2' = p2
    }
    p2_turn[this] implies {
        p2' = p2 + r->c
        p1' = p1
    }

    //Game cannot already have been won
    not finished[this]
}

//No gravity
transition[Board] moveZeroGrav[r: Row, c: Column] {
    not r->c in (p1 + p2)
   
    p1_turn[this] implies {
        p1' = p1 + r->c
        p2' = p2
    }
    p2_turn[this] implies {
        p2' = p2 + r->c
        p1' = p1
    }
    
    not finished[this]
}

transition[Board] moveIntel[r: Row, c: Column] {
    not r->c in (p1 + p2)

    some r.prev_row implies (r.prev_row)->c in (p1 + p2) //GRAVITY
    
    p1_turn[this] implies {
        some a: Row | some b: Column | {
            not a->b in (p1 + p2)
            some a.prev_row implies (a.prev_row)->b in (p1 + p2)
            won[p1 + a->b]
        } implies r = a and c = b
        p1' = p1 + r->c
        p2' = p2
    }
    p2_turn[this] implies {
        some a: Row | some b: Column | {
            not a->b in (p1 + p2)
            some a.prev_row implies (a.prev_row)->b in (p1 + p2)
            won[p2 + a->b]
        } implies r = a and c = b
        p2' = p2 + r->c
        p1' = p1
    }

    not finished[this]
}


transition[Board] game {
    some r: Row | some c: Column | moveIntel[this, this', r, c]
}

transition[Board] gameZeroGrav {
    some r: Row | some c: Column | moveZeroGrav[this, this', r, c]
}

trace<|Board, initialBoard, game, _|> T {}

run<|T|> {wellformed some b: Board | finished[b]}
    for exactly 4 Row, exactly 4 Column, exactly 6 Board

//run {wellformed} for exactly 4 Row, exactly 4 Column, exactly 1 Board

----------------Invariants----------------

pred invariant1 {
  -- (1) At the start of the game, p1 and p2 indices should be empty
  initialBoard implies {
    no p1
    no p2
  }
} 

test expect {
    --INVAR1: <|T|> {not invariant1} for 5 Ref, 4 LinkedList is unsat
}

pred invariant2 {
  -- (2) Assuming there is gravity, you can't place into a spot without a piece below it
  all s: LinkedList | 
    no s.ghost implies {
      no s.start
      no s.end
    }
} 

test expect {
    --INVAR2: <|T|> {not invariant2} for 5 Ref, 4 LinkedList is unsat
}

pred invariant3 {
  -- (3) Two players cannot have put pieces into the same index
  no Board.p1 & Board.p2
} 

test expect {
    --INVAR3: <|T|> {not invariant2} for 5 Ref, 4 LinkedList is unsat
}
    
