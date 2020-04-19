# connect4
Connect 4 final project for CSCI1950Y

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
