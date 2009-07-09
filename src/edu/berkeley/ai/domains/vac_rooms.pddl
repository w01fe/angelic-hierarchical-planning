;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Vac-rooms world
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (domain vac-rooms)
  (:requirements :strips :typing)
  (:types xc yc room)
  (:predicates (atx ?x - xc)
	       (aty ?y - yc) 
	       (clean ?x - xc ?y - yc)
	       (in-room ?r - room)
	       (roomx ?r - room ?x - xc)
	       (roomy ?r - room ?y - yc)
	       (rooml ?r - room ?x - xc)
	       (roomr ?r - room ?x - xc)
	       (roomt ?r - room ?y - yc)
	       (roomb ?r - room ?y - yc)
	       (hall  ?x1 - xc ?y1 - yc ?r2 - room ?x2 - xc ?y2 - yc)
	       (above ?y1 - yc ?y2 - yc)
	       (left-of ?x1 - xc ?x2 - xc)
	       )

  (:action left
	   :parameters   (?r - room ?old - xc ?new - xc)
	   :precondition (and (atx ?old) (in-room ?r) (left-of ?new ?old) (roomx ?r ?new)) 
	   :effect       (and (not (atx ?old)) (atx ?new))
	   :cost         1)

  (:action right
	   :parameters   (?r - room ?old - xc ?new - xc)
	   :precondition (and (atx ?old) (in-room ?r) (left-of ?old ?new) (roomx ?r ?new)) 
	   :effect       (and (not (atx ?old)) (atx ?new))
	   :cost         1)

  (:action up
	   :parameters   (?r - room ?old - yc ?new - yc)
	   :precondition (and (aty ?old) (in-room ?r) (above ?new ?old) (roomy ?r ?new)) 
	   :effect       (and (not (aty ?old)) (aty ?new))
	   :cost         1)

  (:action down
	   :parameters   (?r - room ?old - yc ?new - yc)
	   :precondition (and (aty ?old) (in-room ?r) (above ?old ?new) (roomy ?r ?new)) 
	   :effect       (and (not (aty ?old)) (aty ?new))
	   :cost         1)

  (:action suck 
	   :parameters   (?x - xc ?y - yc)
	   :precondition (and (atx ?x) (aty ?y))
	   :effect       (clean ?x ?y)
	   :cost         1)

  (:action tunnel
	   :parameters   (?x - xc ?y - yc ?r - room ?nx - xc ?ny - yc ?nr - room)
	   :precondition (and (atx ?x) (aty ?y) (in-room ?r) (hall ?x ?y ?nr ?nx ?ny))
	   :effect       (and (not (atx ?x)) (not (aty ?y)) (not (in-room ?r))
			      (atx ?nx)      (aty ?ny)      (in-room ?nr))
	   :cost 2))