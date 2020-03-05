(defproject com.wsscode/pathom "2.2.31"
  :description "A Clojure library designed to provide a collection of helper functions to support Clojure(script) graph parsers using\nom.next graph syntax."
  :url "https://github.com/wilkerlucio/pathom"
  :license {:name "MIT"
            :url  "https://opensource.org/licenses/MIT"}

  :source-paths ["src"]

  :dependencies [[camel-snake-kebab "0.4.0"]
                 [edn-query-language/eql "0.0.9"]
                 [org.clojure/core.async "0.4.490"]
                 [org.clojure/test.check "0.10.0-alpha3"]

                 [com.cognitect/transit-clj "0.8.313" :scope "test"]
                 [com.cognitect/transit-cljs "0.8.256" :scope "test"]

                 ; provided

                 [cheshire/cheshire "5.8.1" :scope "provided"]
                 [fulcrologic/fulcro "2.6.0" :scope "provided"]
                 [org.clojure/clojure "1.10.0" :scope "provided"]
                 [org.clojure/clojurescript "1.9.946" :scope "provided"]
                 [clj-http "3.8.0" :scope "provided"]]

  :plugins [[lein-cljsbuild "1.1.7"]]

  :cljsbuild {:builds [{:id           "sanity"
                        :source-paths ["src"]
                        :compiler     {:optimizations :whitespace
                                       :verbose       true
                                       :main          com.wsscode.pathom.connect}}]}

  :jar-exclusions [#"src-docs/.*" #"docs/.+" #"node-modules/.+"]

  :deploy-repositories [["releases" :clojars]]

  :aliases {"pre-release"  [["vcs" "assert-committed"]
                            ["change" "version" "leiningen.release/bump-version" "release"]
                            ["vcs" "commit"]
                            ["vcs" "tag" "v"]]

            "post-release" [["change" "version" "leiningen.release/bump-version"]
                            ["vcs" "commit"]
                            ["vcs" "push"]]}

  :profiles {:dev {:source-paths ["src" "src-docs" "workspaces/src"]
                   :dependencies [[criterium "0.4.4"]
                                  [nubank/workspaces "1.0.0-preview7"]
                                  [com.cognitect/transit-clj "0.8.313"]
                                  [com.cognitect/transit-cljs "0.8.256"]]}})
