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

(def *base-root* (str (nth (iterate dirname (current-file)) 6) "/"))

(defn path-local [s]
  (str *local-root* (.getParent (File. *file*)) "/" s))

(defn root-local [s]
  (str *local-root* s))

(defn base-local [s]
  (str *base-root* s))

(defn file-exists? [s] 
  (.exists (File. s)))

(defn fresh-filename 
  ([prefix] (fresh-filename prefix ""))
  ([prefix suffix]  
  (first 
   (for [i (iterate inc 1)
	 :let [fn (str prefix (when-not (= i 1) i) suffix)]
	 :when (not (.exists (File. fn)))]
     fn))))

(defn mkdirs [& fs]
  (doseq [f fs]
    (.mkdirs (File. f))))

(defn slurp-object [f]
  (.readObject (ObjectInputStream. (FileInputStream. f))))

(defn spit-object [f o]
  (.writeObject (ObjectOutputStream. (FileOutputStream. f)) o))

(defn read-file [f]
  (read-string (slurp f)))