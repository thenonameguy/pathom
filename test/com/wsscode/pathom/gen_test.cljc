(ns com.wsscode.pathom.gen-test
  (:require [com.wsscode.pathom.gen :as sgen]
            [com.wsscode.pathom.specs.query :as spec.query]
            [clojure.test :refer :all]
            [clojure.test.check :as tc]
            [clojure.test.check.properties :as props]
            [clojure.spec.alpha :as s]
            [fulcro.client.primitives :as fp]))

(def gen-env
  {::sgen/settings
   {:id               {::sgen/gen (s/gen string?)}
    :name             {::sgen/gen (s/gen string?)}
    :title            {::sgen/gen (s/gen string?)}
    :foo              {::sgen/gen (s/gen string?)}
    :bar              {::sgen/gen (s/gen string?)}
    :other            {::sgen/gen (s/gen string?)}
    :price            {::sgen/gen (s/gen string?)}
    :namespaced/value {::sgen/gen (s/gen string?)}}})

(s/def ::coll (s/coll-of int?))
(s/def ::not-coll int?)
(s/def ::fixed-number #{42})
(s/def ::fixed-str #{"bla"})

(fp/defsc Component [_ _ _]
  {:ident (fn [] [:fixed "here"])
   :query [::fixed-number ::fixed-str]}
  (identity nil))

(deftest test-coll-spec?
  (is (true? (sgen/coll-spec? ::coll)))
  (is (false? (sgen/coll-spec? ::not-coll)))
  (is (false? (sgen/coll-spec? ::invalid))))

(deftest test-query->props
  (is (= (sgen/query->props [::fixed-number ::fixed-str ::undefined])
         {::fixed-number 42 ::fixed-str "bla"}))

  (is (= (sgen/query->props {::sgen/settings {::number-list {::sgen/coll 10}}}
           [{::number-list [::fixed-number]}])
         {::number-list (repeat 10 {::fixed-number 42})}))

  (is (= (sgen/query->props {::sgen/settings {::fixed-number {::sgen/gen (s/gen #{43})}}}
           [::fixed-number])
         {::fixed-number 43}))

  (is (= (sgen/query->props [[::fixed-number '_]])
         {::fixed-number 42}))

  (is (true? (-> (tc/quick-check 100
                   (props/for-all [query (s/gen ::spec.query/query)]
                     (sgen/query->props gen-env query)))
                 :result))))

(deftest test-comp->props
  (is (= (sgen/comp->props Component)
         {::fixed-number 42 ::fixed-str "bla"})))

(deftest test-comp->db
  (is (= (sgen/comp->db Component)
         {::fixed-number 42 ::fixed-str "bla"})))
