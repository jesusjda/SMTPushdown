; L0: i = 0; 
; L1: while (i < n) {
;         j = 0;
;     L2: while (j <= i) {
;             j = j + 1;
;         }
;         i = i + 1;
;     }
; L3:

(declare-sort Loc 0)
(declare-const loc0 Loc)
(declare-const loc1 Loc)
(declare-const loc2 Loc)
(declare-const loc3 Loc)

(assert (distinct loc0 loc1 loc2 loc3))


(define-fun cfg_init ( (pc Loc) (src Loc) (rel Bool) ) Bool
  (and (= pc src) rel)
)

(define-fun cfg_trans2 ( (pc Loc) (src Loc) (pc1 Loc) (dst Loc) (rel Bool) ) Bool
  (and (= pc src) (= pc1 dst) rel)
)


(define-fun init_main ( (pc Loc) (i Int) (j Int) (n Int)) Bool 
  (cfg_init pc loc0 true)
)

(define-fun incr ((x Int)) Int (+ x 1))
(define-fun next_main ( (pc Loc)  (i Int)  (j Int)  (n Int)
                   (pc1 Loc) (i1 Int) (j1 Int) (n1 Int)
        ) Bool 
  (or 
    (cfg_trans2 pc loc0 pc1 loc1 (= i1 0))
    (cfg_trans2 pc loc1 pc1 loc2 (and (< i n) (= i1 i) (= n1 n) (= j1 0)) )
    (cfg_trans2 pc loc2 pc1 loc2 (and (<= j i) (= i1 i) (= n1 n) (= j1 (incr j))) )
    (cfg_trans2 pc loc2 pc1 loc1 (and (not (< j i)) (= i1 (incr i)) (= n1 n) (= j1 j)) )
    (cfg_trans2 pc loc1 pc1 loc3 (and (not (< i n)) (= i1 i) (= n1 n) (= j1 j)) )
  )
)
