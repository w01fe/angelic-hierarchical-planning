;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Nav-switch world
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (domain nav-switch)
  (:requirements :strips :typing)
  (:types xc yc)
  (:predicates (atx ?x - xc)
	       (aty ?y - yc) 
	       (horiz)
	       (above ?y1 - yc ?y2 - yc)
	       (left-of ?x1 - xc ?x2 - xc)
	       (switch-at ?x - xc ?y - yc)
	       )

  (:action flip-v
	     :parameters   (?x - xc ?y - yc)
	     :precondition (and (switch-at ?x ?y) (horiz) (atx ?x) (aty ?y))
	     :effect       (and (not (horiz)))
	     :cost         1)

  (:action flip-h
	     :parameters   (?x - xc ?y - yc)
	     :precondition (and (switch-at ?x ?y) (not (horiz)) (atx ?x) (aty ?y))
	     :effect       (and (horiz))
	     :cost         1)

  (:action good-left
	     :parameters   (?old - xc ?new - xc)
	     :precondition (and (left-of ?new ?old) (horiz) (atx ?old)) 
	     :effect       (and (not (atx ?old)) (atx ?new))
	     :cost         2)

  (:action bad-left
	     :parameters   (?old - xc ?new - xc)
	     :precondition (and (left-of ?new ?old) (not (horiz)) (atx ?old)) 
	     :effect       (and (not (atx ?old)) (atx ?new))
	     :cost         4)

  (:action good-right
	     :parameters   (?old - xc ?new - xc)
	     :precondition (and (left-of ?old ?new) (horiz) (atx ?old)) 
	     :effect       (and (not (atx ?old)) (atx ?new))
	     :cost         2)

  (:action bad-right
	     :parameters   (?old - xc ?new - xc)
	     :precondition (and (left-of ?old ?new) (not (horiz)) (atx ?old)) 
	     :effect       (and (not (atx ?old)) (atx ?new))
	     :cost         4)

  (:action good-up
	     :parameters   (?old - yc ?new - yc)
	     :precondition (and (above ?new ?old) (not (horiz)) (aty ?old)) 
	     :effect       (and (not (aty ?old)) (aty ?new))
	     :cost         2)

  (:action bad-up
	     :parameters   (?old - yc ?new - yc)
	     :precondition (and (above ?new ?old) (horiz) (aty ?old)) 
	     :effect       (and (not (aty ?old)) (aty ?new))
	     :cost         4)

  (:action good-down
	     :parameters   (?old - yc ?new - yc)
	     :precondition (and (above ?old ?new) (not (horiz)) (aty ?old)) 
	     :effect       (and (not (aty ?old)) (aty ?new))
	     :cost         2)

  (:action bad-down
	     :parameters   (?old - yc ?new - yc)
	     :precondition (and (above ?old ?new) (horiz) (aty ?old)) 
	     :effect       (and (not (aty ?old)) (aty ?new))
	     :cost         4)
  )
