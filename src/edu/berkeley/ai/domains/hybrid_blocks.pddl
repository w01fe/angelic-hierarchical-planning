;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Hybrid blocks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; (0,0) is at bottom left.
; gripper is basically a point unless holding a block.
; Edge must be flush with blocks to pick up / put down.
; TODO: make carrying cost a fn of block size or something ?

(define (domain hybrid-blocks)
  (:requirements :strips :typing :equality :numbers)
  (:types block)
  (:numeric-types x y)
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
       (and (holding ?b)
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
	    (<= ?ngx (gripperx))
	    (>= ?ngx 0)
	    (forall (?b - block)
		    (and (> (blockty ?b) (grippery))
			 (>= (gripperx) (blockcx ?b)))
		    (>= ?ngx (+ (blockcx ?b) (blockrw ?b)))))
     :effect (= (gripperx) ?ngx)
     :cost   (* 0.1 (- (gripperx) ?ngx)))

  (:action right-empty
     :parameters   (?ngx - x)
     :precondition 
       (and (gripperempty)
	    (>= ?ngx (gripperx))
	    (<= ?ngx (width))
	    (forall (?b - block)
		    (and (> (blockty ?b) (grippery))
			 (<= (gripperx) (blockcx ?b)))
		    (<= ?ngx (- (blockcx ?b) (blocklw ?b)))))
     :effect (= (gripperx) ?ngx)
     :cost   (* 0.1 (- ?ngx (gripperx))))

  (:action up-empty
     :parameters   (?ngy - y)
     :precondition 
       (and (gripperempty)
	    (>= ?ngy (grippery))
	    (<= ?ngy (height)))
     :effect (= (grippery) ?ngy)
     :cost   (* 0.1 (- ?ngy (grippery))))

  (:action down-empty
     :parameters   (?ngy - y)
     :precondition 
       (and (gripperempty)
	    (<= ?ngy (grippery))
	    (forall (?b - block)
		    (and (<= (- (blockcx ?b) (blocklw ?b)) (gripperx))
			 (>= (+ (blockcx ?b) (blockrw ?b)) (gripperx)))
		    (>= ?ngy (blockty ?b))))
     :effect (= (grippery) ?ngy)
     :cost   (* 0.1 (- (grippery) ?ngy)))


  (:action up-holding
     :parameters   (?b - block ?ngy - y)
     :precondition 
       (and (holding ?b)
	    (>= ?ngy (grippery))
	    (<= ?ngy (height)))
     :effect       
       (and (= (grippery) ?ngy)
	    (= (blockty ?b) ?ngy))
     :cost (* 0.2 (- ?ngy (grippery))))


  (:action down-holding
     :parameters   (?b - block ?ngy - y)
     :precondition 
       (and (holding ?b)
	    (<= ?ngy (grippery))
	    (forall (?c - block)
		    (and (not (block= ?b ?c)) 
			 (> (+ (blockcx ?c) (blockrw ?c)) (- (blockcx ?b) (blocklw ?b)))
			 (< (- (blockcx ?c) (blocklw ?c)) (+ (blockcx ?b) (blockrw ?b))))
		    (>= ?ngy (+ (blockty ?c) (blockh ?b)))))
     :effect       
       (and (= (grippery)   ?ngy)
	    (= (blockty ?b) ?ngy))
     :cost (* 0.2 (- (grippery) ?ngy)))


  (:action left-holding
     :parameters   (?b - block ?ngx - x)
     :precondition 
       (and (holding ?b)
	    (<= ?ngx (gripperx))
	    (>= ?ngx (blocklw ?b))
	    (forall (?c - block)
		    (and (not (block= ?b ?c)) 
			 (> (blockty ?c) (- (blockty ?b) (blockh ?b)))
			 (>= (gripperx) (blockcx ?c)))
		    (>= ?ngx (+ (+ (blockcx ?c) (blockrw ?c)) (blocklw ?b)))))
     :effect       
       (and (= (gripperx)   ?ngx)
	    (= (blockcx ?b) ?ngx))
     :cost (* 0.2 (- (gripperx) ?ngx)))

  (:action right-holding
     :parameters   (?b - block ?ngx - x)
     :precondition 
       (and (holding ?b)
	    (>= ?ngx (gripperx))
	    (<= ?ngx (- (width) (blockrw ?b)))
	    (forall (?c - block)
		    (and (not (block= ?b ?c)) 
			 (> (blockty ?c) (- (blockty ?b) (blockh ?b)))
			 (<= (gripperx) (blockcx ?c)))
		    (<= ?ngx (- (- (blockcx ?c) (blocklw ?c)) (blockrw ?b)))))
     :effect       
       (and (= (gripperx)   ?ngx)
	    (= (blockcx ?b) ?ngx))
     :cost (* 0.2 (- ?ngx (gripperx))))

  )
