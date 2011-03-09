;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Nav-switch world
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (domain nav-2d)
  (:requirements :strips :typing)
  (:types xc yc)
  (:predicates (atx ?x - xc)
	       (aty ?y - yc) 
	       (above ?y1 - yc ?y2 - yc)
	       (left-of ?x1 - xc ?x2 - xc)
	       (border ?x - xc ?y - yc)
	       )


  (:action left
	     :parameters   (?oldx - xc ?oldy - yc ?newx - xc)
	     :precondition (and (left-of ?newx ?oldx) 
				(atx ?oldx) (aty ?oldy) (not (border ?newx ?oldy) ) )
	     :effect       (and (not (atx ?oldx)) (atx ?newx))
	     :cost         1)

  (:action right
	     :parameters   (?oldx - xc ?oldy - yc  ?newx - xc)
	     :precondition (and (left-of ?oldx ?newx)
				(atx ?oldx) (aty ?oldy) (not (border ?newx ?oldy)) )
	     :effect       (and (not (atx ?oldx)) (atx ?newx))
	     :cost         1)


  (:action up
	     :parameters   (?oldx - xc ?oldy - yc ?newy - yc)
	     :precondition (and (above ?newy ?oldy)
				(atx ?oldx) (aty ?oldy) (not (border ?oldx ?newy)) )
	     :effect       (and (not (aty ?oldy)) (aty ?newy))
	     :cost         1)

  (:action down
	     :parameters   (?oldx - xc ?oldy - yc ?newy - yc)
	     :precondition (and (above ?oldy ?newy) 
				(atx ?oldx) (aty ?oldy) (not (border ?oldx ?newy)) )
	     :effect       (and (not (aty ?oldy)) (aty ?newy))
	     :cost         1)
  )
