(ns edu.berkeley.ai.util.charts
  (:import 
   [org.jfree.chart ChartFrame ChartPanel JFreeChart ChartFactory]
   [org.jfree.chart.plot PlotOrientation]
   [org.jfree.data.category CategoryDataset DefaultCategoryDataset]
   [org.jfree.data.xy XYDataset XYSeries XYSeriesCollection])
  (:use edu.berkeley.ai.util)
  )


(defn- make-xy-series [title xys]
  (let [ret (XYSeries. title)]
    (doseq [[x y] xys] (.add ret x y))
    ret))

(defn- make-xy-series-collection [xys-map]
  (let [ret (XYSeriesCollection.)]
    (doseq [[title xys] xys-map]
       (.addSeries ret (make-xy-series title xys)))
     ret))

(defn scatter-plot 
  ([data] (scatter-plot data "" "" ""))
  ([data title x-label y-label]
     (ChartFactory/createScatterPlot
      title x-label y-label 
      (make-xy-series-collection data)
      PlotOrientation/VERTICAL
      true true false)))

(import '[org.jfree.chart.renderer.xy XYLineAndShapeRenderer]
	'[org.jfree.chart.event RendererChangeEvent])
(defn line-plot 
  ([data] (line-plot data "" "" ""))
  ([data title x-label y-label]
     (let [plot 
	   (ChartFactory/createScatterPlot
	    title x-label y-label 
	    (make-xy-series-collection data)
	    PlotOrientation/VERTICAL
	    true true false)
	   #^XYLineAndShapeRenderer renderer (.getRenderer (.getPlot plot))]
       (.setBaseLinesVisible renderer true)
       (.setDefaultEntityRadius renderer 100)
;       (.setSeriesLinesVisible renderer true)
;       (.setRenderer (.getPlot plot) (XYLineAndShapeRenderer. true true))
;       (.rendererChanged plot (RendererChangeEvent. renderer))
       plot)))
       

(defn show-chart 
  ([chart] (show-chart "Chart" chart))
  ([title chart]
     (doto (ChartFrame. title chart)
       (.pack)
       (.setVisible true))
     chart))





