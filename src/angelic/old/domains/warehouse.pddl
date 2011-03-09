;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Warehouse world
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; y0 at bottom, x0 at left

(define (domain WAREHOUSE)
  (:requirements :strips :typing :equality)
  (:types block xc yc)
  (:predicates (leftof ?x1 - xc ?x2 - xc)
  	       (above ?y1 - yc ?y2 - yc)
	       (topy ?y - yc)
               (on ?x - block ?y - block)
	       (clear ?x - block)
	       (blockat ?b - block ?x - xc ?y - yc)
	       (someblockat ?x - xc ?y - yc)
	       (holding ?x - block)
	       (facingright)
	       (gripperempty)
	       (gripperat ?x - xc ?y - yc)
	      )

  (:action get-l
             :parameters (?b - block ?c - block ?bx - xc ?gx - xc ?y - yc)
	     :precondition (and (leftof ?bx ?gx)
				(gripperat ?gx ?y)
				(blockat ?b ?bx ?y)
	                        (on ?b ?c)
				(clear ?b)
				(gripperempty)
				(not (facingright)))
	     :effect       (and (not (blockat ?b ?bx ?y))
				(not (someblockat ?bx ?y))
				(not (gripperempty))
				(not (on ?b ?c))
				(holding ?b)
				(clear ?c)))

  (:action get-r
             :parameters (?b - block ?c - block ?bx - xc ?gx - xc ?y - yc)
	     :precondition (and (leftof ?gx ?bx)
				(gripperat ?gx ?y)
				(blockat ?b ?bx ?y)
	                        (on ?b ?c)
				(clear ?b)
				(gripperempty)
				(facingright))
	     :effect       (and (not (blockat ?b ?bx ?y))
				(not (someblockat ?bx ?y))
				(not (gripperempty))
				(not (on ?b ?c))
				(holding ?b)
				(clear ?c)))

  (:action put-l
             :parameters (?b - block ?c - block ?bx - xc ?gx - xc ?cy - yc ?gy - yc)
	     :precondition (and (leftof ?bx ?gx)
				(above ?gy ?cy)
				(gripperat ?gx ?gy)
				(blockat ?c ?bx ?cy)
				(holding ?b)
				(clear ?c)
				(not (facingright)))
	     :effect       (and (blockat ?b ?bx ?gy)
				(someblockat ?bx ?gy)
				(gripperempty)
				(on ?b ?c)
				(not (holding ?b))
				(not (clear ?c))))

  (:action put-r
             :parameters (?b - block ?c - block ?bx - xc ?gx - xc ?cy - yc ?gy - yc)
	     :precondition (and (leftof ?gx ?bx)
				(above ?gy ?cy)
				(gripperat ?gx ?gy)
				(blockat ?c ?bx ?cy)
				(holding ?b)
				(clear ?c)
				(facingright))
	     :effect       (and (blockat ?b ?bx ?gy)
				(someblockat ?bx ?gy)
				(gripperempty)
				(on ?b ?c)
				(not (holding ?b))
				(not (clear ?c))))

  (:action left
             :parameters (?cx - xc ?dx - xc ?y - yc)
	     :precondition (and (leftof ?dx ?cx)
				(gripperat ?cx ?y)
				(not (someblockat ?dx ?y)))
	     :effect       (and (not (gripperat ?cx ?y))
				(gripperat ?dx ?y)))

  (:action right
             :parameters (?cx - xc ?dx - xc ?y - yc)
	     :precondition (and (leftof ?cx ?dx)
				(gripperat ?cx ?y)
				(not (someblockat ?dx ?y)))
	     :effect       (and (not (gripperat ?cx ?y))
				(gripperat ?dx ?y)))

  (:action up
             :parameters (?x - xc ?cy - yc ?dy - yc)
	     :precondition (and (above ?dy ?cy)
				(gripperat ?x ?cy)
				(not (someblockat ?x ?dy)))
	     :effect       (and (not (gripperat ?x ?cy))
				(gripperat ?x ?dy)))

  (:action down
             :parameters (?x - xc ?cy - yc ?dy - yc)
	     :precondition (and (above ?cy ?dy)
				(gripperat ?x ?cy)
				(not (someblockat ?x ?dy)))
	     :effect       (and (not (gripperat ?x ?cy))
				(gripperat ?x ?dy)))

  (:action turn-l
	     :parameters (?x - xc ?y - yc)
	     :precondition (and (gripperat ?x ?y)
				(topy ?y)
				(facingright))
	     :effect       (not (facingright)))

  (:action turn-r
	     :parameters (?x - xc ?y - yc)
	     :precondition (and (gripperat ?x ?y)
				(topy ?y)
				(not (facingright)))
	     :effect       (facingright))

  )
