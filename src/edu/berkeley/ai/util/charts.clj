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
	    (for [field ["pointsize" "size" "key"
			 "xrange" "xtics" "mxtics" 
			 "yrange" "ytics" "mytics"]
		  :when ((keyword field) chart)]
	      (str "set " field " " ((keyword field) chart) "\n")))
	  (apply str
	    (for [field ["title" "xlabel" "ylabel"]
		  :when ((keyword field) chart)]
	      (str "set " field " " (double-quote ((keyword field) chart)) "\n")))
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




(comment 

(quick-plot 
   (mapcar (lambda (Series) (subset->series (apply #'cons series) '(n-refs cost)))
	   (Ds->list (get-subsets (ds-summarize *ww* '(type n-refs) '(cost)
						(lambda (x) (list (mean (ds->list x 'cost)))))
				  '(type) :outer-sort #'string>)))
   :extras '("set ylabel offset 2,-.5 font \"Times-Roman-Bold,28\""
	     "set xlabel offset 0,.3 font \"Times-Roman-Bold,28\""
	     "set title font \"Times-Roman-Bold,30\"  offset 0,-.1 "
	     "set border lw 3"  "set size ratio .4")
   :term "\"Times-Roman\" 28 dashlength 3"
   :default-lw '(9) :default-ps 1  :xrange "[0:5000]"
   :xtics "out scale 2,1" :ylog t :ytics "out scale 2,1" :mytics 10
   :default-lc (list (gp-rgb 200 0 0) (gp-rgb 0 150 0))
   :default-lt '(1 2 5 6) :default-pt '( 1 2 0 0 0 1 0 1 4) ;:size ".3,.3" 
   :key "at 4500,600" 
   :xlabel "refinements per env. step" 
   :ylabel "total solution cost"  
   :title "online results" 
   :ps-file (Format nil "~Afigs/ww.eps" *path*))


(plot (ds->chart [{:a 1 :b 1} {:a 2 :b 2} {:a 3 :b 3}] [] :a :b {:xrange "[0:4]" :yrange "[0:4]" :default-series-options {:type "boxes"}} {}))
)