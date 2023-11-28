(ns latte-lists.append
  "The append function on lists."
  (:refer-clojure :exclude [list cons and or not int =])

  (:require [latte.core :as latte :refer [defaxiom defthm try-defthm
                                          definition try-definition
                                          lambda forall pose
                                          proof try-proof assume have qed]]

            [latte.utils :as u :refer [decomposer]]

            [latte-prelude.prop :as p :refer [not or and]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]

            [latte-lists.core :as lists :refer [list null cons]]
            )
  )

(definition append-property
  [[?T :type] [ys (list T)]]
  (lambda [g (==> (list T) (list T))]
    (and (equal (g (null T)) ys)
         (∀ [xs (list T)]
          (∀ [x T]
           (equal (g (cons x xs)) (cons x (g xs))))))))

(defthm append-unique
  [[?T :type] [ys (list T)]]
  (q/unique (append-property ys)))

(proof 'append-unique-thm
  (qed (lists/list-recur ys  (lists/cons-ax T))))

(definition append-fun
  [[?T :type] [ys (list T)]]
  (q/the (append-unique ys)))

(defthm append-fun-prop
  [[?T :type] [ys (list T)]]
  (and (equal ((append-fun ys) (null T)) ys)
       (forall [xs (list T)]
         (forall [x T]
           (equal ((append-fun ys) (cons x xs))
                  (cons x ((append-fun ys) xs)))))))

(proof 'append-fun-prop-thm
  (qed (q/the-prop (append-unique ys))))

(definition append
  [[?T :type] [xs ys (list T)]]
  ((append-fun ys) xs))

(defthm append-null-left
  [[?T :type] [xs (list T)]]
  (equal (append (null T) xs) xs))

(proof 'append-null-left-thm
  (qed (p/and-elim-left (append-fun-prop xs))))

(defthm append-cons
  [[?T :type] [x T] [xs ys (list T)]]
  (equal (append (cons x xs) ys)
         (cons x (append xs ys))))

(proof 'append-cons-thm
  (qed ((p/and-elim-right (append-fun-prop ys)) xs x)))

(defthm append-null-right
  [[?T :type] [xs (list T)]]
  (equal (append xs (null T)) xs))

(proof 'append-null-right-thm
  (pose P := (lambda [xs (list T)] 
               (equal (append xs (null T)) xs)))
  
  "By structural induction"

  "case (null T)"
  (have <a> (P (null T))
        :by (append-null-left (null T)))

  "inductive case"

  (assume [xs (list T)
           Hind (P xs)
           x T]
    "Now we have to prove (P (cons x xs))"
    

    (have <b1> (equal (cons x (append xs (null T)))
                      (cons x xs))
          :by (eq/eq-cong (lambda [$ (list T)] (cons x $)) Hind))

    (have <b2> (equal (append (cons x xs) (null T))
                      (cons x (append xs (null T))))
          :by (append-cons x xs (null T)))
    
    (have <b> (P (cons x xs)) :by (eq/eq-trans <b2> <b1>)))

  "Use the induction principle"
  (qed ((lists/list-induct P) <a> <b> xs)))











