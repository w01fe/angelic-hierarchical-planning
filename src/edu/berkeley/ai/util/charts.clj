(ns edu.berkeley.ai.util.charts
  (:use edu.berkeley.ai.util edu.berkeley.ai.util.pdf)
  )

(def *default-gnuplot-dir* "/tmp/")

(defstruct series
  :title :data  
  :type :lw :lt :lc :ps :pt)

(defstruct chart
  :size :pointsize
  :xrange :xtics :mxtics :xlog :xlabel
  :yrange :ytics :mytics :ylog :ylabel
  :key :title :term :extra-commands
  :default-series-options :series
  )

(def *default-series-options* 
     (struct-map series 
       :type "linespoints" 
       :lw   2
       :lt  (cycle [1 2 3 4 5 6 7])
       :pt  (cycle [1 2 3 4 5 6 7])))

(def *default-chart-options*
     (struct-map chart
       :pointsize 1
       :key       "off"
       :term      "dashed color"))
       

(defn single-quote [s] (str "'" s "'"))
(defn double-quote [s] (str "\"" s "\""))

(defn fn-or [& args]
  (some identity (reverse args)))

(defn dump-series 
  ([series] (dump-series series (fresh-random-filename *default-gnuplot-dir* ".tmpgd")))
  ([series filename]
    (assert-is (contains? #{1 2} (count (first (:data series)))))
    (spit filename
      (str-join "\n"
	(map (fn [dp] (str-join ", " dp)) 
	     (safe-get series :data))))
    (apply str (single-quote filename)
	 " using " (if (= 1 (count (first (:data series)))) "0:1" "1:2")
	 (when (:title series) (str " t " (double-quote (:title series))))
	 (when (:type series)  (str " with " (:type series)))
	 (for [field ["lt" "lw" "lc" "ps" "pt"] :when  ((keyword field) series)]
	   (str " " field " " ((keyword field) series))))
    ))

(defn peel-series [m]
  [(map-vals #(if (coll? %) (first %) %) m)
   (map-vals #(if (coll? %) (next %) %) m)])


(defn dump-chart 
  ([chart] (dump-chart chart (fresh-random-filename *default-gnuplot-dir* ".pdf")))
  ([chart pdf-file] (dump-chart chart pdf-file (fresh-random-filename *default-gnuplot-dir* ".tmpgp")))
  ([chart pdf-file filename]
     (let [chart                  (merge-with fn-or *default-chart-options* chart)
	   default-series-options (merge-with fn-or *default-series-options* 
					 (:default-series-options chart))]
;       (println chart)
       (spit filename
	 (str
	  "set autoscale x \n"
	  "set autoscale y \n"
	  (apply str
	    (for [field ["pointsize" "size" "title" "key"
			 "xlabel" "xrange" "xtics" "mxtics" 
			 "ylabel" "yrange" "ytics" "mytics"]
		  :when ((keyword field) chart)]
	      (str "set " field " " ((keyword field) chart) "\n")))
	  (if (:xlog chart) "set logscale x\n" "unset logscale x\n")
	  (if (:ylog chart) "set logscale y\n" "unset logscale y\n")
	  "set term pdf enhanced " (:term chart) "\n"
	  "set output " (single-quote pdf-file) "\n"
	  (apply str (for [c (:extra-commands chart)] (str c "\n")))
	  "plot " 
	    (str-join ", \\\n"
	      (loop [in (seq (:series chart)), out [], dso default-series-options]
		(if in
		    (let [[cso next-dso] (peel-series dso)]
		      (recur 
		       (next in) 
		       (conj out (dump-series (merge-with fn-or cso (first in))))
		       next-dso))
		  out)))
	    "\n"
;	  "quit \n"
	  ))
       filename)))


(defn plot 
  ([chart] (plot chart (fresh-random-filename *default-gnuplot-dir* ".pdf")))
  ([chart pdf-file] (plot chart pdf-file true))
  ([chart pdf-file show?]
     (prln (sh "gnuplot" (prln (dump-chart chart pdf-file))))
     (when show?
       (show-pdf-page pdf-file))
     pdf-file))
;       (sh "fixbb" ps-file)
;       (sh "open" "-a" "texshop" ps-file))))


(defn gp-rgb [r g b]
  (doseq [x [r g b]] (assert-is (and (>= x 0) (< x 256))))
  (format "rgbcolor \"#%02x%02x%02x\"" (int r) (int g) (int b)))


