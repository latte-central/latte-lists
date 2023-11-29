(ns latte-lists.length
  "The length of finite lists."

  (:refer-clojure :exclude [list cons and or not int =])

  (:require [latte.core :as latte :refer [defaxiom defthm try-defthm
                                          definition try-definition
                                          lambda forall pose
                                          proof try-proof assume have qed]]

            [latte.utils :as u :refer [decomposer]]

            [latte-prelude.prop :as p :refer [not or and]]
            [latte-prelude.equal :as eq :refer [equal]]
            [latte-prelude.quant :as q :refer [exists]]
            [latte-prelude.algebra :as alg]

            [latte-lists.core :as l]

            [latte-nats.core :as n]
            )

)

(definition length-property
  [T :type]
  (lambda [g (==> (l/list T) n/nat)]
    (and (equal (g (l/null T)) n/zero)
         (forall [xs (l/list T)]
           (forall [x T]
             (equal (g (l/cons x xs)) (n/succ (g xs))))))))


(defthm length-unique
  [T :type]
  (q/unique (length-property T)))

(proof 'length-unique
  (qed (l/list-recur n/zero (lambda [x T] (lambda [k n/nat] (n/succ k))))))

(definition length-fun
  [T :type]
  (q/the (length-unique T)))

(defthm length-fun-prop
  [T :type]
  (and (equal ((length-fun T) (l/null T)) n/zero)
       (forall [xs (l/list T)]
         (forall [x T]
           (equal ((length-fun T) (l/cons x xs))
                  (n/succ ((length-fun T) xs)))))))

(proof 'length-fun-prop
  (qed (q/the-prop (length-unique T))))


(definition length
  "The length of list `xs`"
  [[?T :type] [xs (l/list T)]]
  ((length-fun T) xs))

(defthm length-null
  [T :type]
  (n/= (length (l/null T)) n/zero))

(proof 'length-null
  (qed (p/and-elim-left (length-fun-prop T))))

(defthm length-cons
  [[?T :type] [x T] [xs (l/list T)]]
  (n/= (length (l/cons x xs))
       (n/succ (length xs))))

(proof 'length-cons-thm
  (qed ((p/and-elim-right (length-fun-prop T)) xs x)))


