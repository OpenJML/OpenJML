#%%
from pyeda.inter import *
 

g, k, d, b, i, m, n, s, a, h, l, q, c, o, r, e, f, j, p = map(exprvar, ["g", "k", "d", "b", "i", "m", "n", "s", "a", "h", "l", "q", "c", "o", "r", "e", "f", "j", "p"])
f1 = (((((a & b) & c) & d) | (((((((a & b) & e) & f) & g) & h) | (((((((((a & b) & e) & f) & i) & j) & k) & l) | (((((((a & b) & e) & f) & i) & j) & m) & n)) | ((((((((a & b) & e) & f) & i) & o) & p) & l) | (((((((a & b) & e) & f) & i) & o) & q) & n)))) | ((((((a & b) & e) & r) & p) & h) | (((((((((a & b) & e) & r) & q) & j) & k) & l) | (((((((a & b) & e) & r) & q) & j) & m) & n)) | ((((((((a & b) & e) & r) & q) & o) & p) & l) | (((((((a & b) & e) & r) & q) & o) & q) & n)))))) | ((((a & s) & p) & d) | (((((((a & s) & q) & f) & g) & h) | (((((((((a & s) & q) & f) & i) & j) & k) & l) | (((((((a & s) & q) & f) & i) & j) & m) & n)) | ((((((((a & s) & q) & f) & i) & o) & p) & l) | (((((((a & s) & q) & f) & i) & o) & q) & n)))) | ((((((a & s) & q) & r) & p) & h) | (((((((((a & s) & q) & r) & q) & j) & k) & l) | (((((((a & s) & q) & r) & q) & j) & m) & n)) | ((((((((a & s) & q) & r) & q) & o) & p) & l) | (((((((a & s) & q) & r) & q) & o) & q) & n)))))))
f1m = espresso_exprs(f1.to_dnf())
print(f1m)


(Or(And(a, s, l, q, o, r, p), And(a, f, k, i, s, l, q, j), And(a, b, f, e, i, l, o, p), And(a, m, n, s, q, r, j), And(a, b, h, f, g, e), And(a, n, s, q, o, r), And(a, b, f, e, i, n, q, o), And(a, f, i, n, s, q, o), And(a, f, i, m, n, s, q, j), And(a, b, c, d), And(a, b, e, n, q, o, r), And(a, f, i, s, l, q, o, p), And(a, h, s, q, r, p), And(a, b, e, m, n, q, r, j), And(a, b, f, e, k, i, l, j), And(a, b, e, k, l, q, r, j), And(a, k, s, l, q, r, j), And(a, b, e, l, q, o, r, p), And(a, b, h, e, r, p), And(a, b, f, e, i, m, n, j), And(a, h, f, g, s, q), And(a, d, s, p)),)


Or(Or(And(And(And(a, b), c), d), Or(Or(And(And(And(And(And(a, b), e), f), g), h), Or(Or(And(And(And(And(And(And(And(a, b), e), f), i), j), k), l), And(And(And(And(And(And(And(a, b), e), f), i), j), m), n)), Or(And(And(And(And(And(And(And(a, b), e), f), i), o), p), l), And(And(And(And(And(And(And(a, b), e), f), i), o), q), n)))), Or(And(And(And(And(And(a, b), e), r), p), h), Or(Or(And(And(And(And(And(And(And(a, b), e), r), q), j), k), l), And(And(And(And(And(And(And(a, b), e), r), q), j), m), n)), Or(And(And(And(And(And(And(And(a, b), e), r), q), o), p), l), And(And(And(And(And(And(And(a, b), e), r), q), o), q), n)))))), Or(And(And(And(a, s), p), d), Or(Or(And(And(And(And(And(a, s), q), f), g), h), Or(Or(And(And(And(And(And(And(And(a, s), q), f), i), j), k), l), And(And(And(And(And(And(And(a, s), q), f), i), j), m), n)), Or(And(And(And(And(And(And(And(a, s), q), f), i), o), p), l), And(And(And(And(And(And(And(a, s), q), f), i), o), q), n)))), Or(And(And(And(And(And(a, s), q), r), p), h), Or(Or(And(And(And(And(And(And(And(a, s), q), r), q), j), k), l), And(And(And(And(And(And(And(a, s), q), r), q), j), m), n)), Or(And(And(And(And(And(And(And(a, s), q), r), q), o), p), l), And(And(And(And(And(And(And(a, s), q), r), q), o), q), n)))))))

 also
            {|
              requires !(c >= '0'); 
              requires !(false); 
              requires c >= 'A'; 
              requires !(c <= 'F'); 
              requires !(c >= 'a'); 
              requires (false); 
              ensures \result == (int)c - ((int)'a' - 10); 
            also
              requires !(c >= '0'); 
              requires c >= 'A'; 
              requires !(c <= 'F'); 
              requires !(c >= 'a'); 
              requires !(false); 
              ensures \result == -1; 
            |}
          |}