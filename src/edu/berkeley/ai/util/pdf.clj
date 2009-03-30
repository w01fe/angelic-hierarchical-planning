(ns edu.berkeley.ai.util.pdf
  (:import [com.sun.pdfview PDFFile PDFPage PagePanel]
	   [javax.swing JFrame JMenu JMenuBar JMenuItem KeyStroke AbstractAction ])
  (:use edu.berkeley.ai.util)
  )


(defn show-pdf-page 
  ([f] (show-pdf-page f 1))
  ([f pg]
     (let [frame (JFrame. "PDF")
	   panel (PagePanel.)] 
       (doto frame
	 (.add panel)
	 (.pack)
	 (.setVisible true))
;       (.put (.getInputMap panel) (KeyStroke/getKeyStroke "w") "closeWindow")
;       (.put (.getActionMap panel) "closeWindow" 
;	     (proxy [AbstractAction] ["closeWindow"] [actionPerformed [e] (.setVisible frame false)]))  
       (doto panel 
	 (.showPage (.getPage (PDFFile. (file-as-byte-buffer f)) (dec pg) true)))
       (.pack frame)
;       (future (.requestFocus frame) (.setVisible frame true) (.toFront frame))
       )))

