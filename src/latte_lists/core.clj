(ns latte-lists.core
  "A formalization of the inductive type of polymorphic lists."

  (:refer-clojure :exclude [list cons and or not int =])

  (:require [latte.core :as latte :refer [defaxiom defthm definition try-definition
                                          lambda forall pose
                                          proof try-proof assume have qed]]

            [latte.utils :as u :refer [decomposer]]

            [latte-prelude.prop :as p :refer [not or and]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.fun :as fun]
            ))

(defaxiom list
  "The type of lists of `T`'s."
  [[T :type]]
  :type)

(defn fetch-list-type [def-env ctx l-type]
  (decomposer (fn [t]
                (if (and (seq? t)
                         (= (count t) 2)
                         (= (first t) #'latte-lists.core/list))
                  (second t)
                  (throw (ex-info "Not a list type" {:type t}))))
              def-env ctx l-type))

;; Implicit type parameter: to infer `T` from `(list T)`
(u/register-implicit-type-parameters-handler! 'list fetch-list-type 1)

(defaxiom null
  "The empty list"
  []
  (∀ [T :type] (list T)))

(defaxiom cons
  "The list constructor: `(cons e l)` builds the list
with head `e` and tail `l`"
  [[?T :type] [e T] [l (list T)]]
  (list T))

(defaxiom cons-injective-head
  [[T :type]]
  (∀ [e1 e2 T]
   (∀ [l1 l2 (list T)]
    (==> (equal (cons e1 l1) (cons e2 l2))
         (equal e1 e2)))))

(defaxiom cons-injective-tail
  [[T :type]]
  (∀ [e1 e2 T]
   (∀ [l1 l2 (list T)]
    (==> (equal (cons e1 l1) (cons e2 l2))
         (equal l1 l2)))))

(defaxiom cons-not-null
  [[T :type]]
  (∀ [e T] (∀ [l (list T)] (not (equal (cons e l) (null T))))))

(defaxiom list-induct
  [[T :type] [P (==> (list T) :type)]]
  (==> (P (null T))
       (∀ [l (list T)]
        (==> (P l) 
             (∀ [e T] (P (cons e l)))))
       (∀ [l (list T)] 
        (P l))))


(defthm list-case
  [[T :type] [P (==> (list T) :type)]]
  (==> (P (null T))
       (∀ [l (list T)]
        (∀ [e T] (P (cons e l))))
       (∀ [l (list T)] 
        (P l))))

(proof 'list-case
  (assume [Hnull _
           Hcons _]
    (assume [l (list T)
             Hind (P l)
             e T]
      (have <a> (P (cons e l)) :by (Hcons l e)))

    (assume [l (list T)]
      (have <b> (P l) :by ((list-induct T P) Hnull <a> l))))
  
  (qed <b>))


(defthm list-split
  [[?T :type] [l (list T)]]
  (or (equal l (null T))
      (exists [r (list T)]
        (exists [e T] (equal l (cons e r))))))


(proof 'list-split-thm
  (pose P := (lambda [l (list T)]
               (or (equal l (null T))
                   (exists [r (list T)]
                     (exists [e T] (equal l (cons e r)))))))

  (have <a> (P (null T)) :by (p/or-intro-left (eq/eq-refl (null T))
                                              (exists [r (list T)]
                                                (exists [e T] (equal (null T) (cons e r))))))
  
  (assume [r (list T)
           e T]
      (have <b> (equal (cons e r) (cons e r)) :by (eq/eq-refl (cons e r)))
      (have <c> _ :by ((q/ex-intro (lambda [$ T] (equal (cons e r) (cons $ r))) e) <b>))
      (have <d> _ :by ((q/ex-intro (lambda [$ (list T)]
                                     (exists [e2 T] (equal (cons e r) (cons e2 $)))) r) <c>))
      (have <e> (P (cons e r)) 
            :by (p/or-intro-right (equal (cons e r) (null T)) <d>)))

  (have <f> (P l) :by ((list-case T P) <a> <e> l))
  (qed <f>))

(definition list-recur-prop
  "The property of the recursion principle for inductive lists"
  [[T U :type] [x U] [f (==> T U U)]]
  (lambda [g (==> (list T) U)]
    (and (equal (g (null T)) x)
         (forall [ys (list T)]
           (forall [y T]
             (equal (g (cons y ys)) (f y (g ys))))))))

(defaxiom list-recur
  "The recursion principle for inductive lists, cf. [[list-recur-prop]].

Remark: this is for now defined as an axiom, but it is provable
 (and shall we proved in the future)"
  [[T U :type] [x U] [f (==> T U U)]]
  (q/unique (list-recur-prop T U x f)))

