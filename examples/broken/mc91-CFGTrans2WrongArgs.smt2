;    int x;
;
;    int mc91(int n) {
;      int t;
; L1:  if (n > 100) {
; L2:    return n - 10;
;      } else {
; L3:    t = mc91(n+11);
; L4:    return mc91(t);
;      }
;    } // E_MC91:
;
;     main() {
;       int y;
; L5:   assume(y <= 100);
; L6:   x = mc91(y);
; L7:   assert(x == 91)
;     }  // E_MAIN:


(declare-sort Loc 0)

; mc91 locations
(declare-const l1 Loc)
(declare-const l2 Loc)
(declare-const l3 Loc)
(declare-const l4 Loc)
(declare-const e_mc91 Loc)
; main locations
(declare-const l5 Loc)
(declare-const l6 Loc)
(declare-const l7 Loc)

(assert (distinct l1 l2 l3 l4 e_mc91 l5 l6 l7))

(define-fun cfg_init ( (pc Loc) (src Loc) (rel Bool) ) Bool
  (and (= pc src) rel))

(define-fun cfg_trans2 ( (pc Loc) (src Loc)
                   (pc1 Loc) (dst Loc)
                   (rel Bool) (rel2 Bool) ) Bool
  (and (= pc src) (= pc1 dst) rel))

(define-fun cfg_trans3 ( (pc Loc) (exit Loc)
                  (pc1 Loc) (call Loc)
                  (pc2 Loc) (return Loc)
                  (rel Bool) ) Bool
  (and (= pc exit) (= pc1 call) (= pc2 return) rel))

; init
(define-fun init_main ((pc Loc) (x Int) (y Int)) Bool 
  (cfg_init pc l5 true))

; main
(define-fun next_main (
                        (pc Loc) (x Int) (y Int)
                        (pc1 Loc) (x1 Int) (y1 Int)
                      ) Bool
  (or
   (cfg_trans2 pc l5 pc1 l6 (and (<= y 100) (= x1 x) (= y1 y)))
   (cfg_trans2 pc l6 pc1 l7 (and (<= y 100) (= x1 x) (= y1 y)))))

(define-fun main_call_mc91 (
                             (pc Loc) (x Int) (y Int)
                             (pc1 Loc) (x1 Int) (n1 Int) (t1 Int) (r1 Int)
                           ) Bool
  (or
   (cfg_trans2 pc l6 pc1 l1 (and (= x1 x) (= n1 y)))))

(define-fun mc91_ret_main (
                            (pc Loc) (x Int) (n Int) (t Int) (r Int)
                            (pc1 Loc) (x1 Int) (y1 Int)
                            (pc2 Loc) (x2 Int) (y2 Int)
                          ) Bool
  (or
   (cfg_trans3 pc e_mc91 pc1 l6 pc2 l7 (and (= x2 r) (= y2 y1)))))

(define-fun main_safe ((x Int) (y Int) (pc Loc)) Bool
  (=> (= pc l7) (= x 91)))

; mc91
(define-fun next_mc91 (
                        (pc Loc) (x Int) (n Int) (t Int) (r Int)
                        (pc1 Loc) (x1 Int) (n1 Int) (t1 Int) (r1 Int)
                      ) Bool
  (or
   (cfg_trans2 pc l1 pc1 l2     (and (> n 100) (= x x1) (= n1 n) (= t1 t) (= r1 r)))
   (cfg_trans2 pc l1 pc1 l3     (and (not(> n 100)) (= x x1) (= n1 n) (= t1 t) (= r1 r)))
   (cfg_trans2 pc l2 pc1 e_mc91 (and (= x x1) (= n1 n) (= t1 t) (= r1 (- n 10))))))

(define-fun mc91_call_mc91 (
                             (pc Loc) (x Int) (n Int) (t Int) (r Int); caller
                             (pc1 Loc) (x1 Int) (n1 Int) (t1  Int) (r1 Int) ; callee
                           ) Bool
  (or
   (cfg_trans2 pc l3 pc1 l1 (and (= n1 (+ n 11)) (= x1 x)))
   (cfg_trans2 pc l4 pc1 l1 (and (= n1 t) (= x1 x)))))
  
(define-fun mc91_ret_mc91 (
                            (pc Loc)  (x Int) (n Int) (t Int) (r Int) ; callee
                            (pc1 Loc) (x1 Int) (n1 Int) (t1 Int) (r1 Int) ; caller call
                            (pc2 Loc) (x2 Int) (n2 Int) (t2 Int) (r2 Int) ; caller return
                          ) Bool
  (or
   (cfg_trans3 pc e_mc91 pc1 l3 pc2 l4     (and (= n2 n1) (= r2 r1) (= x2 x) (= t2 r)))
   (cfg_trans3 pc e_mc91 pc1 l4 pc2 e_mc91 (and (= n2 n1) (= t2 t1) (= x2 x) (= r2 r)))))
