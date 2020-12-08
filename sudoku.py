#!/usr/bin/env python3

import itertools
import sys
import z3

class Sudoku:

    _grid = [[ None for _ in range(9) ] for _ in range(9) ]
    _nums = [[ '.' for _ in range(9) ] for _ in range(9) ]
    _solver = None
    
    def __init__(self, sudoku_string=""):
        self._solver = z3.Solver()

        for r in range(9):
            for c in range(9):
                v = z3.Int('cell_%d_%d' % (r, c))
                self._grid[r][c] = v

        self.add_classic_constraints()

        if(len(sudoku_string) > 0):
            assert (len(sudoku_string) == 81), "Invalid sudoku string provided! (length)"
            for r in range(9):
                for c in range(9):
                    x = sudoku_string[r*9+c]
                    if(x != '.'):
                        self._nums[r][c] = x
                        self._solver.add(self._grid[r][c] == int(x))

    def print(self):
        for r in range(9):
            print('   '.join(["{} {} {}".format(a,b,c) for a,b,c in zip(self._nums[r][::3], self._nums[r][1::3], self._nums[r][2::3])]))
            if(r in [2, 5]):
                print()

    def add_classic_constraints(self):
        # Digits from 1-9
        for r in range(9):
            for c in range(9):
                v = self._grid[r][c]
                self._solver.add(v >= 1)
                self._solver.add(v <= 9)

        # Distinct digits in row/column
        for i in range(9):
            self._solver.add(z3.Distinct(self._grid[i])) # Row
            col = [self._grid[r][i] for r in range(9)]
            self._solver.add(z3.Distinct(col)) # Column

        # Distinct digits in boxes
        offset = list(itertools.product(range(0,3), range(0,3)))
        for r in range(0, 9, 3):
            for c in range(0, 9, 3):
                box = [self._grid[r+dy][c+dx] for dy,dx in offset]
                self._solver.add(z3.Distinct(box))

    def solve(self):
        if self._solver.check() == z3.sat:
            m = self._solver.model()
            for r in range(9):
                for c in range(9):
                    self._nums[r][c] = m.evaluate(self._grid[r][c])
        else:
            print("Not enough info -- cannot solve")

usage = "{} [sudoku]".format(sys.argv[0])

if __name__ == "__main__":
    if(len(sys.argv) < 2):
        print("Error: Not enough arguments!")
        print(usage)
        sys.exit(1)

    with open(sys.argv[1], 'r') as in_file:
        data = "".join(in_file.read().split()) # Remove all whitespaces
        s = Sudoku(data[:81])

        print("Entered sudoku:")
        s.print()

        s.solve()

        print()
        print("Solved sudoku:")
        s.print()
