(ns com.wsscode.pathom.misc
  #?(:clj (:import (java.util UUID))))

#?(:clj  (def INCLUDE_SPECS true)
   :cljs (goog-define INCLUDE_SPECS true))

(defn pathom-random-uuid []
  #?(:clj  (UUID/randomUUID)
     :cljs (random-uuid)))

(defn dedupe-by
  "Returns a lazy sequence removing consecutive duplicates in coll when passed to a function f.
  Returns a transducer when no collection is provided."
  {:added "1.7"}
  ([f]
   (fn [rf]
     (let [pv (volatile! ::none)]
       (fn
         ([] (rf))
         ([result] (rf result))
         ([result x]
          (let [prior @pv
                fx    (f x)]
            (vreset! pv fx)
            (if (= prior fx)
              result
              (rf result x))))))))
  ([f coll] (sequence (dedupe-by f) coll)))

(defn index-by
  "Like group by, but will keep only the last result."
  [f coll]
  (reduce
    (fn [m x]
      (assoc m (f x) x))
    {}
    coll))

(def sconj (fnil conj #{}))
(def vconj (fnil conj []))
