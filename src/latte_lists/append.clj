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
  [[T :type] [ys (list T)]]
  (lambda [g (==> (list T) (list T))]
    (and (equal (g (null T)) ys)
         (∀ [xs (list T)]
          (∀ [x T]
           (equal (g (cons x xs)) (cons x (g xs))))))))

(defthm append-unique
  [[T :type] [ys (list T)]]
  (q/unique (append-property T ys)))

(proof 'append-unique
  (qed (lists/list-recur T (list T) ys 
                         (lists/cons-ax T))))

(definition append-fun
  [[T :type] [ys (list T)]]
  (q/the (append-unique T ys)))

(definition append
  [[?T :type] [xs ys (list T)]]
  ((append-fun T xs) ys))

(defthm append-prop
  [[?T :type] [ys (list T)]]
  (and (equal ((append-fun T ys) (null T)) ys)
       (forall [xs (list T)]
         (forall [x T]
           (equal ((append-fun T ys) (cons x xs))
                  (cons x ((append-fun T ys) xs)))))))

(proof 'append-prop-thm
  (qed (q/the-prop (append-unique T ys))))

(defthm append-null
  [[?T :type] [xs (list T)]]
  (equal (append-def T xs (null T)) xs))

(proof 'append-null-thm
  (qed (p/and-elim-left (append-prop-thm T xs))))





