# Playing sudoku in the Lean theorem prover

![Screenshot](/screenshot/screenshot.jpg)

## How to play

Assumes that you have a C++ compiler via `g++`. On Debian/Ubuntu,
`sudo apt install build-essential` should to the trick.

1. `leanproject get TwoFx/sudoku`
2. `cd sudoku`
3. `g++ -O2 scripts/gen.cpp -o gen`
4. Put a sudoku in a file (as 81 numbers separated by white space, 0 is blank). See `scripts/easy1` for an example.
5. `./gen < your_sudoku_file > src/play.lean`
6. `code .`
7. Open the settings (Ctrl+Comma), search for Lean Time Limit, and set it to 0.
8. Restart VS Code, and open `play.lean`.
