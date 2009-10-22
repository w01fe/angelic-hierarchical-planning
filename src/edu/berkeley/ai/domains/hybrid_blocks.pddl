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
  (:numeric-types x y i)
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
   (blockh ?b - block)  - y
   (nblockson ?b - block) - i)

  (:action get
     :parameters   (?b - block ?c - block)
     :precondition 
       (and (on ?b ?c)
;	    (forall (?d - block) nil (not (on ?d ?b)))
            (= 0 (nblockson ?b))
	    (gripperempty)
	    (= (gripperx) (blockcx ?b))
	    (= (grippery) (blockty ?b)))
     :effect       
       (and (not (gripperempty))
	    (not (on ?b ?c))
	    (holding ?b)
            (= (nblockson ?c) (- (nblockson ?c) 1)))
      :cost 1)

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
	    (gripperempty)
            (= (nblockson ?c) (+ (nblockson ?c) 1))
            )
     :cost 1)


  (:action left-empty
     :parameters   (?ngx - x)
     :split-points (forall (?b - block)
			   (and (<= (blockty ?b) (grippery))
				(<= (blockcx ?b) (gripperx))
				(forall (?c - block) nil (not (on ?c ?b))))
			   (= ?ngx (blockcx ?b)))
     :precondition 
       (and (gripperempty)
	    (<= ?ngx (gripperx))
	    (>= ?ngx 0)
	    (forall (?b - block)
		    (and (> (blockty ?b) (grippery))
			 (>= (gripperx) (blockcx ?b)))
		    (>= ?ngx (+ (blockcx ?b) (blockrw ?b)))))
     :effect (= (gripperx) ?ngx)
     :cost   (+ 1 (* 1 (- (gripperx) ?ngx))))

  (:action right-empty
     :parameters   (?ngx - x)
     :split-points (forall (?b - block)
			   (and (<= (blockty ?b) (grippery))
				(>= (blockcx ?b) (gripperx))
				(forall (?c - block) nil (not (on ?c ?b))))
			   (= ?ngx (blockcx ?b)))
     :precondition 
       (and (gripperempty)
	    (>= ?ngx (gripperx))
	    (<= ?ngx (width))
	    (forall (?b - block)
		    (and (> (blockty ?b) (grippery))
			 (<= (gripperx) (blockcx ?b)))
		    (<= ?ngx (- (blockcx ?b) (blocklw ?b)))))
     :effect (= (gripperx) ?ngx)
     :cost   (+ 1 (* 1 (- ?ngx (gripperx)))))

  (:action up-empty
     :parameters   (?ngy - y)
     :split-points (forall (?b - block)
			   (and (>= (blockty ?b) (grippery))
				(forall (?c - block) nil (not (on ?c ?b))))
			   (= ?ngy (blockty ?b)))
     :precondition 
       (and (gripperempty)
	    (>= ?ngy (grippery))
	    (<= ?ngy (height)))
     :effect (= (grippery) ?ngy)
     :cost   (+ 1 (* 1 (- ?ngy (grippery)))))

  (:action down-empty
     :parameters   (?ngy - y)
     :split-points (forall (?b - block)
			   (and (<= (- (blockcx ?b) (blocklw ?b)) (gripperx))
				(>= (+ (blockcx ?b) (blockrw ?b)) (gripperx)))
			   (= ?ngy (blockty ?b)))
     :precondition 
       (and (gripperempty)
	    (<= ?ngy (grippery))
	    (>= ?ngy 0)
	    (forall (?b - block)
		    (and (< (- (blockcx ?b) (blocklw ?b)) (gripperx))
			 (> (+ (blockcx ?b) (blockrw ?b)) (gripperx)))
		    (>= ?ngy (blockty ?b))))
     :effect (= (grippery) ?ngy)
     :cost   (+ 1  (* 1 (- (grippery) ?ngy))))


  (:action up-holding
     :parameters   (?b - block ?ngy - y)
     :split-points (forall (?c - block)
			   (and (not (block= ?b ?c))
				(>= (+ (blockty ?c) (blockh ?b)) (grippery)))
			   (= ?ngy (+ (blockty ?c) (blockh ?b))))
     :precondition 
       (and (holding ?b)
	    (>= ?ngy (grippery))
	    (<= ?ngy (height)))
     :effect       
       (and (= (grippery) ?ngy)
	    (= (blockty ?b) ?ngy))
       :cost (+ 1 (* 2 (- ?ngy (grippery)))))


  (:action down-holding
     :parameters   (?b - block ?ngy - y)
     :split-points (forall (?c - block)
			   (and (not (block= ?b ?c))
			        (<= (- (blockcx ?c) (blocklw ?c)) (gripperx))
				(>= (+ (blockcx ?c) (blockrw ?c)) (gripperx)))
			   (= ?ngy (+ (blockty ?c) (blockh ?b))))
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
       :cost (+ 1 (* 2 (- (grippery) ?ngy))))


  (:action left-holding
     :parameters   (?b - block ?ngx - x)
     :split-points (forall (?c - block)
			   (and ;(<= (blockty ?c) (grippery))
			        (not (block= ?b ?c))
				(<= (- (blockcx ?c) (blocklw ?c)) (gripperx)))
			   (and (= ?ngx (- (+ (blockcx ?c) (blockrw ?c)) (blockrw ?b)))
				(= ?ngx (+ (- (blockcx ?c) (blocklw ?c)) (blocklw ?b)))
				(= ?ngx (+ (+ (blockcx ?c) (blockrw ?c)) (blocklw ?b)))
				(= ?ngx (- (- (blockcx ?c) (blocklw ?c)) (blockrw ?b)))))
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
       :cost (+ 1  (* 2 (- (gripperx) ?ngx))))

  (:action right-holding
     :parameters   (?b - block ?ngx - x)
     :split-points (forall (?c - block)
			   (and ;(<= (blockty ?c) (grippery))
			        (not (block= ?b ?c))
				(>= (+ (blockcx ?c) (blockrw ?c)) (gripperx)))
			   (and (= ?ngx (- (+ (blockcx ?c) (blockrw ?c)) (blockrw ?b)))
				(= ?ngx (+ (- (blockcx ?c) (blocklw ?c)) (blocklw ?b)))
				(= ?ngx (+ (+ (blockcx ?c) (blockrw ?c)) (blocklw ?b)))
				(= ?ngx (- (- (blockcx ?c) (blocklw ?c)) (blockrw ?b)))))
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
       :cost (+ 1  (* 2 (- ?ngx (gripperx)))))

  )
