(ns com.wsscode.pathom.parser
  #?@
   (:clj
    [(:require
      [clojure.core.async :as async :refer [<! go]]
      [clojure.set :as set]
      [clojure.spec.alpha :as s]
      [com.fulcrologic.guardrails.core :refer [>def]]
      [com.wsscode.async.async-clj :refer [<? <?maybe chan? go-catch]]
      [com.wsscode.pathom.trace :as pt :refer [trace tracing]]
      [edn-query-language.core :as eql])
     (:import clojure.lang.IDeref)]
    :cljs
    [(:require
      [clojure.core.async :as async :refer [<! go]]
      [clojure.set :as set]
      [clojure.spec.alpha :as s]
      [com.fulcrologic.guardrails.core :refer [>def]]
      [com.wsscode.async.async-cljs :refer [<? <?maybe chan? go-catch]]
      [com.wsscode.pathom.trace :as pt :refer [trace tracing]]
      [edn-query-language.core :as eql])]))

(>def ::provides (s/coll-of (s/or :attr :com.wsscode.pathom.connect/attribute
                                  :sym :com.wsscode.pathom.connect/sym
                                  :ident ::eql/ident
                                  :join-context ::eql/join-context) :kind set?))
(>def ::max-key-iterations int?)
(>def ::processing-recheck-timer (s/nilable pos-int?))
(>def ::external-wait-ignore-timeout (s/nilable pos-int?))

(defn- atom? [x]
  #?(:clj  (instance? IDeref x)
     :cljs (satisfies? IDeref x)))

(declare focus-subquery*)

(defn- focus-subquery-union*
  [query-ast sub-ast]
  (let [s-index (into {} (map #(vector (:union-key %) %)) (:children sub-ast))]
    (assoc query-ast
           :children
           (reduce
            (fn [children {:keys [union-key] :as union-entry}]
              (if-let [sub (get s-index union-key)]
                (conj children (focus-subquery* union-entry sub))
                (conj children union-entry)))
            []
            (:children query-ast)))))

(defn- focus-subquery*
  [query-ast sub-ast]
  (let [q-index (group-by :key (:children query-ast))]
    (assoc query-ast
           :children
           (reduce
            (fn [children {:keys [key type] :as focus}]
              (if-let [source (get q-index key)]
                (reduce
                 (fn [children source]
                   (cond
                     (= :join type (:type source))
                     (conj children (focus-subquery* source focus))

                     (= :union type (:type source))
                     (conj children (focus-subquery-union* source focus))

                     :else
                     (conj children source)))
                 children
                 source)
                children))
            []
            (:children sub-ast)))))

(defn focus-subquery
  "Given a query, focus it along the specified query expression.

  Examples:
    (focus-query [:foo :bar :baz] [:foo])
    => [:foo]

    (fulcro.client.primitives/focus-query [{:foo [:bar :baz]} :woz] [{:foo [:bar]} :woz])
    => [{:foo [:bar]} :woz]"
  [query sub-query]
  (let [query-ast (eql/query->ast query)
        sub-ast   (eql/query->ast sub-query)]
    (eql/ast->expr (focus-subquery* query-ast sub-ast) true)))

(defn ast->out-key [ast]
  (or (get-in ast [:params :pathom/as])
      (get ast :key)))

(defn parser [{:keys [read mutate]}]
  (fn self [env tx]
    (tracing env {::pt/event ::parse-loop}
             (let [{:keys [children] :as tx-ast} (eql/query->ast tx)
                   tx                            (vary-meta tx assoc ::ast tx-ast)
                   env                           (assoc env :parser self :com.wsscode.pathom.core/parent-query tx)]
               (loop [res                                              {}
                      [{:keys [query key type params] :as ast} & tail] children]
                 (if ast
                   (let [_     (trace env {::pt/event ::process-key :key key})
                         env   (cond-> (merge env {:ast ast :query query})
                                 (nil? query)   (dissoc :query)
                                 (= '... query) (assoc :query tx))
                         value (case type
                                 :call
                                 (do
                                   (assert mutate "Parse mutation attempted but no :mutate function supplied")
                                   (let [{:keys [action]} (mutate env key params)]
                                     (when action
                                       (action))))

                                 (:prop :join :union)
                                 (do
                                   (assert read "Parse read attempted but no :read function supplied")
                                   (read env))

                                 nil)]
                     (recur (assoc res (ast->out-key ast) value) tail))
                   res))))))

(defn async-parser [{:keys [read mutate]}]
  (fn self [env tx]
    (go-catch
     (tracing env {::pt/event ::parse-loop}
              (let [{:keys [children] :as tx-ast} (eql/query->ast tx)
                    tx  (vary-meta tx assoc ::ast tx-ast)
                    env (assoc env :parser self :com.wsscode.pathom.core/parent-query tx)]
                (loop [res {}
                       [{:keys [query key type params] :as ast} & tail] children]
                  (if ast
                    (let [_     (trace env {::pt/event ::process-key :key key})
                          env   (cond-> (merge env {:ast ast :query query})
                                  (nil? query) (dissoc :query)
                                  (= '... query) (assoc :query tx))
                          value (case type
                                  :call
                                  (do
                                    (assert mutate "Parse mutation attempted but no :mutate function supplied")
                                    (let [{:keys [action]} (mutate env key params)]
                                      (when action
                                        (action))))

                                  (:prop :join :union)
                                  (do
                                    (assert read "Parse read attempted but no :read function supplied")
                                    (read env))

                                  nil)
                          value (if (chan? value) (<? value) value)]
                      (recur (assoc res (ast->out-key ast) value) tail))
                    res)))))))

(defn watch-pending-key [{::keys [key-watchers external-wait-ignore-timeout]
                          :or    {external-wait-ignore-timeout 3000}
                          :as    env} key]
  (let [ch (async/chan)]
    (swap! key-watchers update key conj ch)
    (go
      ; sometimes the watcher is too fast and finishes the process before we get to register
      ; the watcher. This timeout ensures that in those cases we still flush out the watched key
      ;; FIXME: this race should be resolved to not introduce 1ms latency per resolver
      (<! (async/timeout 1))
      (when (contains? @(get env :com.wsscode.pathom.core/entity) key)
        (trace env {::pt/event ::flush-watcher-safeguard :key key})
        (async/put! ch {::provides #{key}})
        (async/close! ch)))

    (if external-wait-ignore-timeout
      (go
        (let [timer    (async/timeout external-wait-ignore-timeout)
              [res ch] (async/alts! [ch timer]
                                    :priority true)]
          (if (= ch timer)
            (do
              (pt/trace env {::pt/event                     ::watch-pending-timeout
                             ::external-wait-ignore-timeout external-wait-ignore-timeout})
              {::error    ::watch-pending-timeout
               ::provides #{}})
            res)))
      ch)))

; urh, ugly copy from core but needed to avoid dep cycles
(defn- process-error [{:com.wsscode.pathom.core/keys [process-error] :as env} e]
  (if process-error (process-error env e) e))

(defn- parallel-process-value [env tx ast
                               key-watchers
                               res waiting processing
                               read mutate key-iterations tail]
  (let [{:keys [query key type params]} ast
        env   (cond-> (merge env {:ast           ast
                                  :query         query
                                  ::waiting      waiting
                                  ::key-watchers key-watchers})
                (nil? query) (dissoc :query)
                (= '... query) (assoc :query tx))
        value (case type
                :call
                (do
                  (assert mutate "Parse mutation attempted but no :mutate function supplied")
                  (let [{:keys [action]} (mutate env key params)]
                    (when action
                      (go
                        (try
                          (trace env {::pt/event ::call-mutation
                                      :mutation  key})
                          (<?maybe (action))
                          (catch #?(:clj Throwable :cljs :default) e
                            {::error (process-error env e)}))))))

                (:prop :join :union)
                (do
                  (assert read "Parse read attempted but no :read function supplied")
                  (tracing env {::pt/event ::call-read :key key}
                           (read env)))

                nil)]
    (cond
      (chan? value)
      (let [provides #{key}
            stream   (go
                       {::provides       provides
                        ::merge-result?  true
                        ::response-value {key        (<! value)
                                          :pathom/as (ast->out-key ast)}})]
        (trace env {::pt/event ::async-return
                    :key       key})
        [res
         (into waiting provides)
         (conj processing {::process-channel stream
                           ::process-source  ::channel-response
                           ::provides        provides})
         key-iterations
         tail])

      (::provides value)
      (let [provides (::provides value)
            stream   (::response-stream value)]
        (trace env {::pt/event ::provided-return
                    ::provides provides})
        [res
         (into waiting provides)
         (conj processing {::process-channel stream
                           ::process-source  ::parallel-reader
                           ::provides        provides})
         key-iterations
         tail])

      :else
      (do
        (trace env {::pt/event ::value-return
                    :key       key})
        [(assoc res (ast->out-key ast) value) waiting processing key-iterations tail]))))

(defn- parallel-flush-watchers [env key-watchers provides error]
  (pt/tracing env {::pt/event ::flush-watchers-loop}
              (doseq [[pkey watchers] @key-watchers]
                (when (contains? provides pkey)
                  (trace env {::pt/event      ::flush-watchers
                              :key            pkey
                              ::watcher-count (count watchers)})
                  (doseq [out watchers]
                    (async/put! out {::provides provides
                                     ::error    error})
                    (async/close! out))
                  (swap! key-watchers dissoc pkey)))))

(defn default-step-fn [amount min]
  (fn [_ x] (Math/max (- x amount) min)))

(defn remove-error-values [m]
  (into {}
        (remove (fn [[_ v]] (= v :com.wsscode.pathom.core/reader-error)))
        m))

(defn value-merge
  "This is used for merging new parsed attributes from entity, works like regular merge but if the value from the right
  direction is not found, then the previous value will be kept."
  [x y]
  (if (or (identical? y :com.wsscode.pathom.core/reader-error)
          (identical? y :com.wsscode.pathom.core/not-found))
    x
    y))

(defn process-next-message
  [{::keys                        [done-signal* processing-recheck-timer active-paths]
    :com.wsscode.pathom.core/keys [path]
    :as                           env}
   tx waiting indexed-props processing key-iterations key-watchers res]
  (go-catch
   (let [_           (trace env {::pt/event         ::processing-wait-next
                                 ::processing-count (count processing)})
         recheck-ch  (when processing-recheck-timer (async/timeout processing-recheck-timer))
         processing' (cond-> (into [] (map ::process-channel) processing)
                       recheck-ch
                       (conj recheck-ch))
         [msg p]     (async/alts! processing' :priority true)]
     (if (= p recheck-ch)
       (let [all-props     (set (keys indexed-props))
             current-props (set (keys res))
             missing-props (set/difference all-props current-props)]
         (pt/trace env {::pt/event   ::trigger-reader-retry
                        ::processing {:processes     processing
                                      :missing-props missing-props}})
         (if (some #(contains? @active-paths (conj path %)) missing-props)
           [res waiting processing key-iterations []]
           (do
             (pt/trace env {::pt/event      ::trigger-recheck-schedule
                            ::missing-props missing-props})
             (doseq [{::keys [process-channel]} processing]
               (async/close! process-channel))
             (if @done-signal*
               [res #{} #{} key-iterations []]
               [res #{} #{} key-iterations (into [] (map indexed-props) missing-props)]))))
       (let [{::keys [response-value provides merge-result? error]} msg
             waiting'                                               (::waiting msg)
             provides'                                              (set/difference provides waiting')
             key-as                                                 (:pathom/as response-value)
             response-value                                         (dissoc response-value :pathom/as)
             waiting                                                (into waiting waiting')]
         (if msg
           (do
             (trace env (cond-> {::pt/event       ::process-pending
                                 ::provides       provides
                                 ::response-value response-value
                                 ::merge-result?  (boolean merge-result?)}
                          waiting' (assoc ::waiting waiting')))
             (swap! (:com.wsscode.pathom.core/entity env) #(merge-with value-merge response-value %))

             (parallel-flush-watchers env key-watchers provides' error)

             (if merge-result?
               (do
                 (pt/trace env {::pt/event ::merge-result ::response-value response-value})
                 [(assoc res key-as (first (vals response-value)))
                  (into #{} (remove provides') waiting)
                  processing
                  key-iterations
                  []])

               (let [next-children (->> (vec provides')
                                        (focus-subquery tx)
                                        (eql/query->ast)
                                        :children
                                        (remove (comp (-> res remove-error-values keys set) ast->out-key))
                                        (distinct))]
                 (pt/trace env {::pt/event  ::reset-loop
                                ::loop-keys (mapv :key next-children)})
                 [res
                  (into #{} (remove provides') waiting)
                  processing
                  key-iterations
                  next-children])))
           [res waiting (into #{} (remove (comp #{p} ::process-channel)) processing) key-iterations []]))))))

(def zero-inc (fnil inc 0))

(defn call-parallel-parser
  [{:keys [read mutate]}
   {::keys                        [waiting key-watchers max-key-iterations
                                   key-process-timeout key-process-timeout-step]
    :com.wsscode.pathom.core/keys [entity-path-cache path]
    :or                           {max-key-iterations 5}
    :as                           env}
   tx]
  (go-catch
   (let [key-process-timeout-step (or key-process-timeout-step (default-step-fn 1000 1000))
         key-process-timeout      (when key-process-timeout (key-process-timeout-step env key-process-timeout))
         {:keys [children]}       (eql/query->ast tx)
         key-watchers             (or key-watchers (atom {}))
         path-entity              (get @entity-path-cache path {})
         env                      (-> env
                                      (assoc ::parallel? true
                                             ::key-process-timeout key-process-timeout)
                                      (update :com.wsscode.pathom.core/entity
                                              (fn [x]
                                                (if (atom? x)
                                                  (do
                                                    (swap! x #(merge path-entity %))
                                                    x)
                                                  (atom (merge path-entity x))))))
         indexed-props            (into {} (map (fn [{:keys [key] :as ast}] [key ast])) children)]
     (tracing env {::pt/event            ::parse-loop
                   ::key-process-timeout key-process-timeout}
              (loop [res                            {}
                     waiting                        (or waiting #{})
                     processing                     #{}
                     key-iterations                 {}
                     [{:keys [key] :as ast} & tail] children]
                (cond
            ; processing attributes
                  ast
                  (let [out-key (ast->out-key ast)]
                    (trace env {::pt/event ::process-key :key key})
                    (cond
                      (> (get key-iterations key 0) (dec max-key-iterations))
                      (do
                        (trace env {::pt/event ::max-iterations-reached :key key ::max-key-iterations max-key-iterations})
                        (recur (cond-> res
                                 (not (contains? res out-key))
                                 (assoc out-key :com.wsscode.pathom.core/not-found)) waiting processing key-iterations tail))

                      (and (contains? res out-key) (not= :com.wsscode.pathom.core/reader-error (get res out-key)))
                      (do
                        (trace env {::pt/event ::skip-resolved-key :key key})
                        (recur res waiting processing key-iterations tail))

                      (and (::key-watchers env)
                           (contains? waiting key))
                      (do
                        (trace env {::pt/event ::external-wait-key :key key})
                        (recur res waiting
                               (conj processing {::process-channel (watch-pending-key env key)
                                                 ::process-source  ::pending-key-watch
                                                 ::provides        #{key}})
                               key-iterations
                               tail))

                      (contains? waiting key)
                      (do
                        (trace env {::pt/event ::skip-wait-key :key key})
                        (recur res waiting processing key-iterations tail))

                      :else
                      (let [[res waiting processing key-iterations tail]
                            (parallel-process-value
                             env tx ast
                             key-watchers
                             res waiting processing
                             read mutate (update key-iterations out-key zero-inc) tail)]
                        (recur res waiting processing key-iterations tail))))

                                        ; waiting for results
                  (seq processing)
                  (let [[res waiting processing key-iterations tail] (<! (process-next-message env tx waiting indexed-props processing key-iterations key-watchers res))]
                    (recur res waiting processing key-iterations tail))

                                        ; done
                  :else
                  res))))))

(defn parallel-parser [{:keys [add-error] :as pconfig}]
  (fn self [{::keys                        [key-process-timeout active-paths]
             :com.wsscode.pathom.core/keys [path root-query]
             :or                           {key-process-timeout 60000}
             :as                           env} tx]
    (go-catch
     (swap! active-paths conj path)
     (let [res-ch   (call-parallel-parser pconfig (assoc env :parser self
                                                         ::key-process-timeout key-process-timeout
                                                         :com.wsscode.pathom.core/parent-query tx) tx)
           channels (cond-> [res-ch] key-process-timeout (conj (async/timeout key-process-timeout)))
           [res p]  (async/alts! channels)]

       (swap! active-paths disj path)

       (if (= res-ch p)
         res
         (do
           (trace env {::pt/event            ::timeout-reach
                       ::key-process-timeout key-process-timeout})
           (add-error env
                      (ex-info "Parallel read timeout" {:timeout    key-process-timeout
                                                        :path       path
                                                        :root-query root-query}))
           {}))))))

(defn unique-ident?
  #?(:cljs {:tag boolean})
  [x]
  (and (ident? x) (= '_ (second x))))
