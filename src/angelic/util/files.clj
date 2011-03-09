(in-ns 'angelic.util)

(import '(java.io RandomAccessFile File ObjectInputStream FileInputStream ObjectOutputStream FileOutputStream))

(import '(java.nio ByteBuffer) '(java.nio.channels FileChannel FileChannel$MapMode))

(defn dirname [#^String path]
  (.getParent (File. path))) 

(defn file-stem [#^String path]
  (let [i (.lastIndexOf path ".")]
    (if (>= i 0)
      (.substring path 0 i)
      path)))

(defmacro current-file []
  `(if *file*
       (let [f# (ClassLoader/getSystemResource #^String *file*)]
         (if f#
           (.getCanonicalPath (java.io.File. (.toURI f#)))
           (.getCanonicalPath (java.io.File. #^String *file*))))))

(defmacro current-dir []
  `(dirname (current-file)))

(def *local-root* (str (nth (iterate dirname (current-file)) 5) "/"))

(def *base-root* (str (nth (iterate dirname (current-file)) 6) "/"))

(defn path-local [s]
  (str *local-root* (.getParent (File. #^String *file*)) "/" s))

(defn root-local [s]
  (str *local-root* s))

(defn base-local [s]
  (str *base-root* s))

(defn file-exists? [#^String s] 
  (.exists (File. s)))

(defn fresh-filename 
  ([prefix] (fresh-filename prefix ""))
  ([prefix suffix]  
  (first 
   (for [i (iterate inc 1)
	 :let [fn (str prefix (when-not (= i 1) i) suffix)]
	 :when (not (.exists (File. fn)))]
     fn))))

(defn fresh-random-filename 
  ([prefix] (fresh-random-filename prefix ""))
  ([prefix suffix]  
  (first 
   (for [i (repeatedly #(rand-int 10000000))
	 :let [fn (str prefix (when-not (= i 1) i) suffix)]
	 :when (not (.exists (File. fn)))]
     fn))))


(defn mkdirs [& fs]
  (doseq [f fs]
    (.mkdirs (File. #^String f))))

(defn slurp-object [#^String f]
  (.readObject (ObjectInputStream. (FileInputStream. f))))

(defn spit-object [#^String f o]
  (.writeObject (ObjectOutputStream. (FileOutputStream. f)) o))

(defn read-file [f]
  (read-string (slurp f)))

(defn file-as-byte-buffer [#^String f]
  (let [channel (.getChannel (RandomAccessFile. (File. f) "r"))]
    (.map channel FileChannel$MapMode/READ_ONLY 0 (.size channel))))