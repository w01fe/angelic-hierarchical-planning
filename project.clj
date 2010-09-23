(defproject angelic "1.0.0-SNAPSHOT"
  :description "Angelic hierarchical planning"
  :dependencies [[org.clojure/clojure "1.2.0-RC2"]
                 [org.clojure/clojure-contrib "1.2.0-RC2"]
;                [org.clojars.robertpfeiffer/vijual "0.1.0-SNAPSHOT"]
                 [org.swinglabs/pdf-renderer "1.0.5"]
                 [incanter "1.2.3-SNAPSHOT"]
                 ]
  :dev-dependencies [[swank-clojure "1.2.1"] [mycroft/mycroft "0.0.2"]]
  :jvm-opts ["-server" "-Xmx1g" "-agentpath:/Applications/YourKit_Java_Profiler_9.0.0.app/bin/mac/libyjpagent.jnilib"]
)