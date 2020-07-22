# Playing sudoku in the Lean theorem prover

![Screenshot](/screenshot/screenshot.jpg)

## How to start playing

Assumes that you have a C++ compiler via `g++`. On Debian/Ubuntu,
`sudo apt install build-essential` should do the trick.

First, we download the code.
1. `leanproject get TwoFx/sudoku`

Next, we compile the program that generates levels for us.

2. `cd sudoku`
3. `g++ -std=gnu++11 -O2 scripts/gen.cpp -o gen`

Next, we will use it to generate a level for us.

4. Put a sudoku in a file (as 81 numbers separated by white space, 0 is blank). See `scripts/easy1` for an example.
5. `./gen < your_sudoku_file > src/play.lean`

Next, we have to tell Visual Studio code to not time out our code. This is needed because I wrote very inefficient and slow code. You will notice this while playing.

6. `code .`
7. Open the settings (Ctrl+Comma), search for Lean Time Limit, and set it to 0.

Finally, we are ready to go.

8. Restart VS Code, and open `play.lean`.

## How to play

Please look at the screenshot for an example of how a game of sudoku can look.

Cells are zero-indexed from the top left. You place the number z in cell (x, y) by saying

```lean
have cxy : s.f (x, y) = z,
```

but now you have to prove why this is the case. There are four main tactics for that:

* `box_logic` splits along the statement "there is a z somewhere in the box of (x, y)" and tries to find a conflict in the board for ever position other than (x, y)
* `row_logic` and `col_logic` are the same as `box_logic`, but (you guessed it) for rows and columns rather than boxes
* `cell_logic` is like the others, but splits along the statement "there is a number in (x, y)"
* `naked_single` is a synonym for `cell_logic` to conform to usual sudoku terminology

There is also support for two kinds of pencil marks: Snyder notation on the edges of cells and doubles and triples in the center of cells:

If you say

```lean
have p0 : s.snyder w x y z a
```
then you have to prove that there is an a in (w, x) or (y, z). You will usually use row, box or column logic for this.

If you say
```lean
have p1 : s.double x y a b
````
then you have to prove that there is either an a or a b in (x, y).

Doing this will give you a pencil mark. To later use such a pencil mark in a deduction, you can say things like `box_logic with p0 p1`, which for every possible position in the box will first try to find an unconditional conflict and then splits over p0 and p1 in the cases where it gets stuck.

Finally, you can use `pencil with p0 p1` to make case distinctions over pencil marks only.

For hard sudokus, you'll want to formalize some actual sudoku theory. I have started doing that in the file `basic.lean`, but that work is still in its very early stages.
