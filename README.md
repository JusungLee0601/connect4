# connect4
Connect 4 final project for CSCI1950Y
(CONNECT FORGE)

Properties

Winning condition, first move, solved game
- regardless of opponent move, move possible to a win

Extensible/Flexible model
- connect N
  * discuss complexity
  * must occur during checking phase
- no gravity
  * in trace we'll have restrictions on placing "above"
  * remove for no gravity
  * own pred
- dimensions
  * n or n+1, does size affect win
- variable starting move 
  * constrain to a certain move
  * just easier to visualize
  * change initial board
  
Some Notes on Model
- connect N
  * possible, but must be hard coded
  * currently 3 by 3 works
- no gravity
  * pretty easy to manipulate
- dimensions
  * thanks to stephen's model, easy to manipulate
  * 6 by 7 with all 42 possible boards is impossible to model
  * we can fiddle around with the exact limit, but still dicey
- variable starting move
  * possible with trace stuff

Some Notes on Solved Game
- possibly do it by modeling "smart" moves with boolean conditions
- could also just show wins are sat, but don't imply "perfect" games
- I think our best bet for properties, at least beyond just board manipulations
  is to model these perfect plays as best we can. I'm not sure its possible through
  just showing traces of our current model.
