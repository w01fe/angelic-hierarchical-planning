(in-ns 'edu.berkeley.ai.util)

(import '(java.io File ObjectInputStream FileInputStream ObjectOutputStream FileOutputStream))

(defn dirname [path]
  (.getParent (File. path))) 

(defmacro current-file []
  `(if *file*
       (let [f# (ClassLoader/getSystemResource *file*)]
         (if f#
           (.getCanonicalPath (java.io.File. (.toURI f#)))
           (.getCanonicalPath (java.io.File. *file*))))))

(defmacro current-dir []
  `(dirname (current-file)))

(def *local-root* (str (nth (iterate dirname (current-file)) 5) "/"))

(defn path-local [s]
  (str *local-root* (.getParent (File. *file*)) "/" s))

(defn root-local [s]
  (str *local-root* s))

(defn slurp-object [f]
  (.readObject (ObjectInputStream. (FileInputStream. f))))

(defn spit-object [f o]
  (.writeObject (ObjectOutputStream. (FileOutputStream. f)) o))

(defn read-file [f]
  (read-string (slurp f)))