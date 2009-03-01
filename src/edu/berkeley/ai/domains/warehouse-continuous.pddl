;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Warehouse world
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; (0,0) is at bottom left.
; gripper is basically a point unless holding a block.
; Positions are [left, right) and [bottom, top) intervals.?
; Edge must be flush with blocks to pick up / put down.

(define (domain WAREHOUSE-HYBRID)
  (:requirements :strips :typing :equality :numbers)
  (:types block)
  (:numeric-types x y n)
  (:predicates 
   (on ?b - block ?c - block)
   (holding ?b - block)
   (gripperempty))
  (:numeric-functions
   (width)              - x
   (height)             - y
   (gripperx)           - x
   (grippery)           - y
   (blockcx ?b - block) - x
   (blockty ?b - block) - y
   (blocklw ?b - block) - x
   (blockrw ?b - block) - x
   (blockh ?b - block)  - y)

  (:action get
     :parameters   (?b - block ?c - block)
     :precondition 
       (and (on ?b ?c)
	    (forall (?d - block) nil (not (on ?d ?b)))
	    (gripperempty)
	    (= (gripperx) (blockcx ?b))
	    (= (grippery) (blockty ?b)))
     :effect       
       (and (not (gripperempty))
	    (not (on ?b ?c))
	    (holding ?b)))

  (:action put
     :parameters   (?b - block ?c - block)
     :precondition 
       (and (holding? b)
	    (= (- (blockty ?b) (blockh ?b)) (blockty ?c))
	    (<= (- (blockcx ?c) (blocklw ?c)) (- (blockcx ?b) (blocklw ?b)))
	    (>= (+ (blockcx ?c) (blockrw ?c)) (+ (blockcx ?b) (blockrw ?b))))
     :effect       
       (and (not (holding ?b))
	    (on ?b ?c)
	    (gripperempty)))


  (:action left-empty
     :parameters   (?ngx - x)
     :precondition 
       (and (gripperempty)
	    (< ?ngx (gripperx))
	    (>= ?ngx 0)
	    (forall (?b - block)
		    (>= (blockty ?b) (grippery))
		    (<= (+ (blockcx ?b) (blockrw ?b)) ?ngx)))
     :effect (= (gripperx) ?ngx)
     :cost   (* .1 (- (gripperx) ?ngx)))

  (:action right-empty
     :parameters   (?ngx - x)
     :precondition 
       (and (gripperempty)
	    (> ?ngx (gripperx))
	    (<= ?ngx (width))
	    (forall (?b - block)
		    (>= (blockty ?b) (grippery))
		    (>= (- (blockcx ?b) (blocklw ?b)) ?ngx)))
     :effect (= (gripperx) ?ngx)
     :cost   (* .1 (- ?ngx (gripperx))))

  (:action up-empty
     :parameters   (?ngy - y)
     :precondition 
       (and (gripperempty)
	    (> ?ngy (grippery))
	    (<= ?ngy (height)))
     :effect (= (grippery) ?ngy)
     :cost   (* .1 (- ?ngy (grippery))))

  (:action down-empty
     :parameters   (?ngy - y)
     :precondition 
       (and (gripperempty)
	    (< ?ngy (grippery))
	    (forall (?b - block)
		    (and (<= (- (blockcx ?b) (blocklw ?b)) (gripperx))
			 (>= (+ (blockcx ?b) (blockrw ?b)) (gripperx)))
		    (<= (blockty ?b) ?ngy)))
     :effect (= (grippery) ?ngy)
     :cost   (* .1 (- (grippery) ?ngy)))


  (:action up-holding
     :parameters   (?b - block ?ngy - y)
     :precondition 
       (and (holding? b)
	    (> ?ngy (grippery))
	    (<= ?ngy (height)))
     :effect       
       (and (= (grippery) ?ngy)
	    (= (blockty ?b) ?ngy))
     :cost (* .2 (- ?ngy (grippery))))


  (:action down-holding
     :parameters   (?b - block ?ngy - y)
     :precondition 
       (and (holding? b)
	    (< ?ngy (grippery))
	    (forall (?c - block)
		    (and (not (block= ?b ?c)) 
			 (>= (+ (blockcx ?c) (blockrw ?c)) (- (blockcx ?b) (blocklw ?b)))
			 (>= (blockty ?c) (- ?ngy (blockh ?b))))
		    (>= (- (blockcx ?c) (blocklw ?c)) (+ (blockcx ?b) (blockrw ?b))))
	    (forall (?c - block)
		    (and (not (block= ?b ?c)) 
			 (<= (- (blockcx ?c) (blocklw ?c)) (+ (blockcx ?b) (blockrw ?b)))
			 (>= (blockty ?c) (- ?ngy (blockh ?b))))
		    (<= (+ (blockcx ?c) (blockrw ?c)) (- (blockcx ?b) (blocklw ?b)))))
     :effect       
       (and (= (grippery)   ?ngy)
	    (= (blockty ?b) ?ngy))
     :cost (* .2 (- (grippery) ?ngy)))


  (:action left-holding
     :parameters   (?b - block ?ngx - x)
     :precondition 
       (and (holding? b)
	    (< ?ngx (gripperx))
	    (>= ?ngx (blocklw ?b))
	    (forall (?c - block)
		    (and (not (block= ?b ?c)) 
			 (>= (blockty ?c) (- (blockty ?b) (blockh ?b))))
		    (<= (+ (blockcx ?c) (blockrw ?c)) (- ?ngx (blocklw ?b)))))
     :effect       
       (and (gripperx   ?ngx)
	    (blockcx ?b ?ngx))
     :cost (* .2 (- (gripperx) ?ngx)))

  (:action right-holding
     :parameters   (?b - block ?ngx - x)
     :precondition 
       (and (holding? b)
	    (< (gripperx) ?bngx)
	    (<= ?ngx (blockrw ?b))
	    (forall (?c - block)
		    (and (not (block= ?b ?c)) 
			 (>= (blockty ?c) (- (blockty ?b) (blockh ?b))))
		    (>= (- (blockcx ?c) (blocklw ?c)) (+ ?ngx (blockrw ?b)))))
     :effect       
       (and (gripperx   ?ngx)
	    (blockcx ?b ?ngx))
     :cost (* .2 (- ?ngx (gripperx))))

  )
