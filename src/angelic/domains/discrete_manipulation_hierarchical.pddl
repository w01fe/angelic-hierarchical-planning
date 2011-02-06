;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;         Discrete manipulation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; 0, 0 at top left

(define (domain DM)
  (:requirements :strips :typing :equality                  :action-costs
                 )
  
  (:types object xc yc xrel yrel)
  (:predicates
   ;; Constant preds
   (leftof                   ?x1 - xc ?x2 - xc)
   (above                    ?y1 - yc ?y2 - yc)
   (leftof-rel               ?x1 - xrel ?x2 - xrel)
   (above-rel                ?y1 - yrel ?y2 - yrel)
   (sum-x        ?x - xc ?xr - xrel ?xsum - xc)
   (sum-y        ?y - yc ?yr - yrel ?ysum - yc)
   (zerox-rel    ?x - xrel)
   (zeroy-rel    ?y - yrel)
   (object-goal  ?o - object ?x - xc  ?y - yc)
   (base-obstacle ?x - xc  ?y - yc)
   (base-pick-position ?o - object ?x - xc ?y - yc) ; new
   (base-place-position ?o - object ?x - xc ?y - yc) ; new
   (base-switch-pick-position ?o - object ?x - xc ?y - yc) ; new
   (base-switch-place-position ?o - object ?x - xc ?y - yc) ; new

   ;; Robot base
   (parked       )
   (base-pos      ?x - xc  ?y - yc)

   ;; Objects
   (object-pos   ?o - object ?x - xc  ?y - yc)
   (object-done  ?o - object)

   ;; Gripper
   (holding       ?o - object)
   (gripper-empty )
   (gripper-rel      ?x - xrel ?y - yrel)
   (gripper-obstacle ?x - xc  ?y - yc)

   ;; Intentions (new)
   (picking ?o - object)
   (placing ?o - object))
  
  (:functions (total-cost) - number)

  ;; Base movement actions
  (:action unpark-picking
   :parameters (?o - object ?x - xrel ?y - yrel)
   :precondition (and (parked) (picking ?o) (gripper-rel ?x ?y) (zerox-rel ?x) (zeroy-rel ?y)
                      (holding ?o))   
   :effect       (and (not (parked)) (not (picking ?o))
                    (increase (total-cost) 2)
                      ))

  (:action unpark-placing
   :parameters (?o - object ?x - xrel ?y - yrel)
   :precondition (and (parked) (placing ?o)  (gripper-rel ?x ?y) (zerox-rel ?x) (zeroy-rel ?y)
                      (not (holding ?o)))   
   :effect       (and (not (parked)) (not (placing ?o))
                    (increase (total-cost) 2)
                      ))
  
  (:action park-picking
   :parameters   (?o - object ?x - xc ?y - yc)
   :precondition (and (not (parked)) (base-pos ?x ?y)
                      (base-pick-position ?o ?x ?y) (gripper-empty) (not (object-done ?o)))
   :effect       (and (parked) (picking ?o)
                    (increase (total-cost) 5)
                     ))

  (:action park-placing
   :parameters   (?o - object ?x - xc ?y - yc)
   :precondition (and (not (parked)) (base-pos ?x ?y)
                      (base-place-position ?o ?x ?y) (holding ?o))
   :effect       (and (parked) (placing ?o)
                    (increase (total-cost) 5)
                     ))

  (:action repark-picking
   :parameters   (?po - object ?no - object ?x - xc ?y - yc ?xr - xrel ?yr - yrel)
   :precondition (and (parked) (placing ?po) (base-pos ?x ?y)
                      (gripper-rel ?xr ?yr) (zerox-rel ?xr) (zeroy-rel ?yr)
                      (base-switch-pick-position ?no ?x ?y) (not (holding ?po)) (not (object-done ?no)))
   :effect       (and (not (placing ?po)) (picking ?no)
                    (increase (total-cost) 0)
                      ))

  (:action repark-placing
   :parameters   (?o - object ?x - xc ?y - yc)
   :precondition (and (parked) (picking ?o) (base-pos ?x ?y)
                      (base-switch-place-position ?o ?x ?y) (holding ?o))
   :effect       (and (not (picking ?o)) (placing ?o)
                    (increase (total-cost) 0)
                      ))  
  

  
  
  (:action base-left
   :parameters (?cx - xc ?dx - xc ?y - yc)
   :precondition (and (not (parked))
                      (leftof ?dx ?cx)
                      (base-pos ?cx ?y)
                      (not (base-obstacle ?dx ?y)))
   :effect       (and (not (base-pos ?cx ?y)) (base-pos ?dx ?y)
                     (increase (total-cost) 2)
                      ))
  
  (:action base-right
   :parameters (?cx - xc ?dx - xc ?y - yc)
   :precondition (and (not (parked))
                      (leftof ?cx ?dx)
                      (base-pos ?cx ?y)
                      (not (base-obstacle ?dx ?y)))
   :effect       (and (not (base-pos ?cx ?y)) (base-pos ?dx ?y)
                     (increase (total-cost) 2)
                      ))
  
  (:action base-up
   :parameters (?x - xc ?cy - yc ?dy - yc)
   :precondition (and (not (parked))
                      (above ?dy ?cy)
                      (base-pos ?x ?cy)
                      (not (base-obstacle ?x ?dy)))
   :effect       (and (not (base-pos ?x ?cy)) (base-pos ?x ?dy)
                     (increase (total-cost) 2)
                      ))
  
  (:action base-down
   :parameters (?x - xc ?cy - yc ?dy - yc)
   :precondition (and (not (parked))
                      (above ?cy ?dy)
                      (base-pos ?x ?cy)
                      (not (base-obstacle ?x ?dy)))
   :effect       (and (not (base-pos ?x ?cy)) (base-pos ?x ?dy)
                     (increase (total-cost) 2)
                      ))
  

  ;;;Gripper movement actions
  (:action gripper-left
   :parameters (?basex - xc ?basey - yc
                ?cgxrel - xrel ?dgxrel - xrel ?cgxabs - xc ?dgxabs - xc
                ?gyrel - yrel ?gyabs - yc)
   :precondition (and (parked)
                      (base-pos ?basex ?basey)
                      (gripper-rel ?cgxrel ?gyrel)
                      (leftof-rel ?dgxrel ?cgxrel)
                      (sum-x ?basex ?cgxrel ?cgxabs)
                      (sum-x ?basex ?dgxrel ?dgxabs)
                      (sum-y ?basey ?gyrel  ?gyabs)
                      (not (gripper-obstacle ?dgxabs ?gyabs)))
   :effect       (and (not (gripper-rel ?cgxrel ?gyrel)) (gripper-rel ?dgxrel ?gyrel)
                     (increase (total-cost) 1)
                      ))
  

  (:action gripper-right
   :parameters (?basex - xc ?basey - yc
                ?cgxrel - xrel ?dgxrel - xrel ?cgxabs - xc ?dgxabs - xc
                ?gyrel - yrel ?gyabs - yc)
   :precondition (and (parked)
                      (base-pos ?basex ?basey)
                      (gripper-rel ?cgxrel ?gyrel)
                      (leftof-rel ?cgxrel ?dgxrel)
                      (sum-x ?basex ?cgxrel ?cgxabs)
                      (sum-x ?basex ?dgxrel ?dgxabs)
                      (sum-y ?basey ?gyrel  ?gyabs)
                      (not (gripper-obstacle ?dgxabs ?gyabs)))
   :effect       (and (not (gripper-rel ?cgxrel ?gyrel)) (gripper-rel ?dgxrel ?gyrel)
                     (increase (total-cost) 1)
                      ))
  
  (:action gripper-up
   :parameters (?basex - xc ?basey - yc
                ?gxrel - xrel ?gxabs - xc
                ?cgyrel - yrel ?dgyrel - yrel ?cgyabs - yc ?dgyabs - yc)   
   :precondition (and (parked)
                      (base-pos ?basex ?basey)
                      (gripper-rel ?gxrel ?cgyrel)
                      (above-rel ?dgyrel ?cgyrel)
                      (sum-x ?basex ?gxrel  ?gxabs)
                      (sum-y ?basey ?cgyrel ?cgyabs)
                      (sum-y ?basey ?dgyrel ?dgyabs)
                      (not (gripper-obstacle ?gxabs ?dgyabs)))
   :effect       (and (not (gripper-rel ?gxrel ?cgyrel)) (gripper-rel ?gxrel ?dgyrel)
                     (increase (total-cost) 1)
                      ))
  

  (:action gripper-down
   :parameters (?basex - xc ?basey - yc
                ?gxrel - xrel ?gxabs - xc
                ?cgyrel - yrel ?dgyrel - yrel ?cgyabs - yc ?dgyabs - yc)   
   :precondition (and (parked)
                      (base-pos ?basex ?basey)
                      (gripper-rel ?gxrel ?cgyrel)
                      (above-rel ?cgyrel ?dgyrel)
                      (sum-x ?basex ?gxrel  ?gxabs)
                      (sum-y ?basey ?cgyrel ?cgyabs)
                      (sum-y ?basey ?dgyrel ?dgyabs)
                      (not (gripper-obstacle ?gxabs ?dgyabs)))
   :effect       (and (not (gripper-rel ?gxrel ?cgyrel)) (gripper-rel ?gxrel ?dgyrel)
                      (increase (total-cost) 1)
                      ))
  
  
  ;;;Object manipulation actions
  (:action get-left
   :parameters (?basex - xc ?basey - yc
                ?gxrel - xrel ?gxabs - xc ?gyrel - yrel ?gyabs - yc
                ?o - object ?ox - xc)   
   :precondition (and (parked) (picking ?o)
                      (base-pos ?basex ?basey)
                      (gripper-rel ?gxrel ?gyrel)
                      (sum-x ?basex ?gxrel ?gxabs)
                      (sum-y ?basey ?gyrel ?gyabs)
                      (gripper-empty)
                      (leftof ?ox ?gxabs)
                      (not (object-done ?o)) (object-pos ?o ?ox ?gyabs))
   :effect       (and (not (object-pos ?o ?ox ?gyabs))
                      (not (gripper-obstacle ?ox ?gyabs))
                      (not (gripper-empty))
                      (holding ?o)
                      (increase (total-cost) 1)
                      ))
  
  (:action get-right
   :parameters (?basex - xc ?basey - yc
                ?gxrel - xrel ?gxabs - xc ?gyrel - yrel ?gyabs - yc
                ?o - object ?ox - xc)   
   :precondition (and (parked) (picking ?o)
                      (base-pos ?basex ?basey)
                      (gripper-rel ?gxrel ?gyrel)
                      (sum-x ?basex ?gxrel ?gxabs)
                      (sum-y ?basey ?gyrel ?gyabs)
                      (gripper-empty)
                      (leftof ?gxabs ?ox)
                      (not (object-done ?o)) (object-pos ?o ?ox ?gyabs))
   :effect       (and (not (object-pos ?o ?ox ?gyabs))
                      (not (gripper-obstacle ?ox ?gyabs))
                      (not (gripper-empty))
                      (holding ?o)
                       (increase (total-cost) 1)
                      ))
  
  (:action get-up
   :parameters (?basex - xc ?basey - yc
                ?gxrel - xrel ?gxabs - xc ?gyrel - yrel ?gyabs - yc
                ?o - object ?oy - yc)   
   :precondition (and (parked) (picking ?o)
                      (base-pos ?basex ?basey)
                      (gripper-rel ?gxrel ?gyrel)
                      (sum-x ?basex ?gxrel ?gxabs)
                      (sum-y ?basey ?gyrel ?gyabs)
                      (gripper-empty)
                      (above ?oy ?gyabs)
                      (not (object-done ?o)) (object-pos ?o ?gxabs ?oy))
   :effect       (and (not (object-pos ?o ?gxabs ?oy))
                      (not (gripper-obstacle ?gxabs ?oy))
                      (not (gripper-empty))
                      (holding ?o)
                       (increase (total-cost) 1)
                      ))
  
  
  (:action get-down
   :parameters (?basex - xc ?basey - yc
                ?gxrel - xrel ?gxabs - xc ?gyrel - yrel ?gyabs - yc
                ?o - object ?oy - yc)   
   :precondition (and (parked) (picking ?o)
                      (base-pos ?basex ?basey)
                      (gripper-rel ?gxrel ?gyrel)
                      (sum-x ?basex ?gxrel ?gxabs)
                      (sum-y ?basey ?gyrel ?gyabs)
                      (gripper-empty)
                      (above ?gyabs ?oy)
                      (not (object-done ?o)) (object-pos ?o ?gxabs ?oy))
   :effect       (and (not (object-pos ?o ?gxabs ?oy))
                      (not (gripper-obstacle ?gxabs ?oy))
                      (not (gripper-empty))
                      (holding ?o)
                        (increase (total-cost) 1)
                      ))
    
  (:action put-left
   :parameters (?basex - xc ?basey - yc
                ?gxrel - xrel ?gxabs - xc ?gyrel - yrel ?gyabs - yc
                ?o - object ?ox - xc)   
   :precondition (and (parked)
                      (base-pos ?basex ?basey)
                      (gripper-rel ?gxrel ?gyrel)
                      (sum-x ?basex ?gxrel ?gxabs)
                      (sum-y ?basey ?gyrel ?gyabs)
                      (holding ?o)
                      (leftof ?ox ?gxabs)
                      (not (gripper-obstacle ?ox ?gyabs))
                      (object-goal ?o ?ox ?gyabs))
   :effect       (and (not (holding ?o))
                      (object-pos ?o ?ox ?gyabs)
                      (object-done ?o)
                      (gripper-obstacle ?ox ?gyabs)
                      (gripper-empty)
                         (increase (total-cost) 1)
                      ))
  

  (:action put-right
   :parameters (?basex - xc ?basey - yc
                ?gxrel - xrel ?gxabs - xc ?gyrel - yrel ?gyabs - yc
                ?o - object ?ox - xc)   
   :precondition (and (parked)
                      (base-pos ?basex ?basey)
                      (gripper-rel ?gxrel ?gyrel)
                      (sum-x ?basex ?gxrel ?gxabs)
                      (sum-y ?basey ?gyrel ?gyabs)
                      (holding ?o)
                      (leftof ?gxabs ?ox)
                      (not (gripper-obstacle ?ox ?gyabs))
                      (object-goal ?o ?ox ?gyabs))
   :effect       (and (not (holding ?o))
                      (object-pos ?o ?ox ?gyabs)
                      (object-done ?o)
                      (gripper-obstacle ?ox ?gyabs)
                      (gripper-empty)
                          (increase (total-cost) 1)
                      ))
  
  (:action put-up
   :parameters (?basex - xc ?basey - yc
                ?gxrel - xrel ?gxabs - xc ?gyrel - yrel ?gyabs - yc
                ?o - object ?oy - yc)   
   :precondition (and (parked)
                      (base-pos ?basex ?basey)
                      (gripper-rel ?gxrel ?gyrel)
                      (sum-x ?basex ?gxrel ?gxabs)
                      (sum-y ?basey ?gyrel ?gyabs)
                      (holding ?o)
                      (above ?oy ?gyabs)
                      (not (gripper-obstacle ?gxabs ?oy))
                      (object-goal ?o ?gxabs ?oy))
   :effect       (and (not (holding ?o))
                      (object-pos ?o ?gxabs ?oy)
                      (object-done ?o)
                      (gripper-obstacle ?gxabs ?oy)
                      (gripper-empty)
                           (increase (total-cost) 1)
                      ))
  

  (:action put-down
   :parameters (?basex - xc ?basey - yc
                ?gxrel - xrel ?gxabs - xc ?gyrel - yrel ?gyabs - yc
                ?o - object ?oy - yc)   
   :precondition (and (parked)
                      (base-pos ?basex ?basey)
                      (gripper-rel ?gxrel ?gyrel)
                      (sum-x ?basex ?gxrel ?gxabs)
                      (sum-y ?basey ?gyrel ?gyabs)
                      (holding ?o)
                      (above ?gyabs ?oy)
                      (not (gripper-obstacle ?gxabs ?oy))
                      (object-goal ?o ?gxabs ?oy))
   :effect       (and (not (holding ?o))
                      (object-pos ?o ?gxabs ?oy)
                      (object-done ?o)                      
                      (gripper-obstacle ?gxabs ?oy)
                      (gripper-empty)
                            (increase (total-cost) 1)
                      )))


