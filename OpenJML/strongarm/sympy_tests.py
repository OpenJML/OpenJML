#%% 
from sympy import *
init_printing(use_latex='mathjax')

x, y, z, t = symbols('x y z t')
k, m, n = symbols('k m n', integer=True)
f, g, h = symbols('f g h', cls=Function)

F = (x**2 + 2*x + 1)

F


#%% 
from sympy.logic import simplify_logic
x,y,g,k, d, b, i, m, n, s, a, h, l, q, c, o, r, e, f, j, p = symbols('x,y,g,k, d, b, i, m, n, s, a, h, l, q, c, o, r, e, f, j, p')

f0 = y | (x & y)
f0
#%%
simplify_logic(f0, form='dnf')


#%%
init_printing(use_latex='text')

f1 = (((((a & b) & c) & d) | (((((((a & b) & e) & f) & g) & h) | (((((((((a & b) & e) & f) & i) & j) & k) & l) | (((((((a & b) & e) & f) & i) & j) & m) & n)) | ((((((((a & b) & e) & f) & i) & o) & p) & l) | (((((((a & b) & e) & f) & i) & o) & q) & n)))) | ((((((a & b) & e) & r) & p) & h) | (((((((((a & b) & e) & r) & q) & j) & k) & l) | (((((((a & b) & e) & r) & q) & j) & m) & n)) | ((((((((a & b) & e) & r) & q) & o) & p) & l) | (((((((a & b) & e) & r) & q) & o) & q) & n)))))) | ((((a & s) & p) & d) | (((((((a & s) & q) & f) & g) & h) | (((((((((a & s) & q) & f) & i) & j) & k) & l) | (((((((a & s) & q) & f) & i) & j) & m) & n)) | ((((((((a & s) & q) & f) & i) & o) & p) & l) | (((((((a & s) & q) & f) & i) & o) & q) & n)))) | ((((((a & s) & q) & r) & p) & h) | (((((((((a & s) & q) & r) & q) & j) & k) & l) | (((((((a & s) & q) & r) & q) & j) & m) & n)) | ((((((((a & s) & q) & r) & q) & o) & p) & l) | (((((((a & s) & q) & r) & q) & o) & q) & n)))))))

f1

#%%
simplify_logic(f1, form='dnf')
