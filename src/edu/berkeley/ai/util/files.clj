(in-ns 'edu.berkeley.ai.util)

(import '(java.io ObjectInputStream FileInputStream ObjectOutputStream FileOutputStream))

(defn slurp-object [f]
  (.readObject (ObjectInputStream. (FileInputStream. f))))

(defn spit-object [f o]
  (.writeObject (ObjectOutputStream. (FileOutputStream. f)) o))

(defn read-file [f]
  (read-string (slurp f)))