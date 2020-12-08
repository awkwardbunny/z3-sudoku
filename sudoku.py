#!/usr/bin/env python3

import itertools
import sys
import z3
from enum import Enum

class SudokuType(Enum):
    Classic = 1
    Miracle = 2

class Sudoku:

    _grid = [[ None for _ in range(9) ] for _ in range(9) ]
    _nums = [[ '.' for _ in range(9) ] for _ in range(9) ]
    _solver = None
    _valid_charset = set([str(x) for x in range(1,10)])
    sudoku_type = SudokuType.Classic

    _extra_constraints = []
    
    def __init__(self, sudoku_string=""):
        self._solver = z3.Solver()
        sudoku_string = "".join(sudoku_string.split())
        self._valid_charset.add('.')

        # Create variables
        for r in range(9):
            for c in range(9):
                v = z3.Int('cell_%d_%d' % (r, c))
                self._grid[r][c] = v

        # Add constraints for classic sudoku
        self.add_classic_constraints()

        assert (len(sudoku_string) >= 81), "Invalid sudoku string provided! (length)"
        self.load_numbers(sudoku_string[:81])

        if(len(sudoku_string) > 81):
            self.load_extra_constraints(sudoku_string[81:])

    def load_extra_constraints(self, constraints_string):
        cs = constraints_string.split(';')
        for c in cs:
            if not c:
                continue
            elif c[0] == 'M':
                self.sudoku_type = SudokuType.Miracle
                self._extra_constraints = c[0]
                self.add_miracle_constraints()

    def load_numbers(self, sudoku_string):
            for r in range(9):
                for c in range(9):
                    x = sudoku_string[r*9+c]
                    assert (x in self._valid_charset), "Invalid sudoku string provided! (invalid character \'{}\')".format(x)
                    if(x != '.'):
                        self._nums[r][c] = int(x)
                        self._solver.add(self._grid[r][c] == int(x))

    def print(self):
        for r in range(9):
            print('   '
                    .join(["{} {} {}".format(a,b,c) for a,b,c in 
                        zip(self._nums[r][::3], self._nums[r][1::3], self._nums[r][2::3])]))
            if(r in [2, 5]):
                print()

    def add_miracle_constraints(self):
        self.add_chess_constraints('knight')
        self.add_chess_constraints('king')

        # Add neighboring sequence constraints
        offsets = ((0,-1), (1,0), (0,1), (-1, 0))
        for v, t in self.get_offset_constraints(offsets, False):
            self._solver.add(t-v != 1)

    def get_offset_constraints(self, offsets, symmetrical):
        pairs = set()
        for r in range(9):
            for c in range(9):
                for dy,dx in offsets:
                    y = r+dy
                    x = c+dx
                    if not ((0 <= x <= 8) and (0 <= y <= 8)):
                        continue
                    pair = tuple(sorted([(r,c), (y,x)]))
                    if symmetrical and (pair in pairs):
                        continue
                    pairs.add(pair)
                    yield self._grid[r][c], self._grid[y][x]

    def add_chess_constraints(self, chess_type):
        if(chess_type.lower() == 'knight'):
            offsets = ((1,-2), (2,-1), (2,1), (1,2), (-1,2), (-2,1), (-2,-1), (-1,2))
            for v,t in self.get_offset_constraints(offsets, True):
                self._solver.add(v != t)
        elif(chess_type.lower() == 'king'):
            offsets = list(itertools.product((-1,1), (-1,1)))
            for v,t in self.get_offset_constraints(offsets, True):
                self._solver.add(v != t)

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
            self._solver.add(z3.Distinct([self._grid[r][i] for r in range(9)])) # Column

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
            return True
        else:
            return False

usage = "{} [sudoku]".format(sys.argv[0])

if __name__ == "__main__":
    if(len(sys.argv) < 2):
        print("Error: Not enough arguments!")
        print(usage)
        sys.exit(1)

    with open(sys.argv[1], 'r') as in_file:
        data = "".join(in_file.read().split()) # Remove all whitespaces
        s = Sudoku(data)

        print("Entered sudoku:")
        print(s.sudoku_type)
        s.print()
        print()

        if(s.solve()):
            print("Solved sudoku:")
            s.print()
        else:
            print("Too many constraints? -- cannot solve")
