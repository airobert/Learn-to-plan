globals [
  ;==============input/output/goal related===================
  time
  csv
  fileList ;
  width      ; the width of the patches
  height     ; the height of the patches
  color-list ; a list of color for agents
  goal       ; the goal pattern

  ;==============buttons related attributes==============
  noise ; the randomly set points in each button that belongs to solution.
  buttons; a list of buttons, each button is a pair setting some patches to green and some to black
  button-chosen; the (index of the) button choosen to be pressed in current hour. For day 0, hour 0, it is randomly choosen
  buttons-chosen-before; all the buttons chosen before

  ;==============time related attributes==================
  num-hours  ; the length of solution
  day        ; the day
  hour       ; the hour
  ticks-per-hour; totoal number of ticks per day. It may vary from hour to hour
  succeed-initialise-game; an attribute to indicate the beginning of the game

  ;==============status and planning=======================
  trying ; a sign of status if the agents are trying or bidding
  bidding ; for each action, we record a value
  bidding-day; total amount of days where buttons are chosen by bidding

  ;==============other attributes==================
  can-walk ; if the agent can move around. In this game, the agents are assumed to be able to
  ]

turtles-own[
  ;======================beliefs===================================================================
  own-color; color set to the agent
  buttons-assigned; the order of buttons it owns, relating to the matrix buttons
  observation ; the agent's observation
  action-knowledge; knowledge about the actions. each action is a pair: (know-true, know-false).
  ; know-true consists of the propositions the agent is sure about.
  ; know false consists of the propositions the agent knows not going to be the case.
  personal-plan;
  button-owners;agents' belief about the owner of each buttons
  pattern-and-plan; when the learning for this pattern finishes, the agent store the pattern and the corresponding personal plan
  ;======================desire====================================================================
  ; the agent has the desire to maximise the knowledge of the buttons it is in charge of
  ; to stop itself when informed
  desire; the agent is aiming at a stop when the pattern was reached (and the agent will be informed)
  ;======================intention=================================================================
  ; to move to a location and to bid
  ; and to bid for an action (not necessarily to press its buttons)
  intention
  ; and the following are related variables
  best-node ;a data structure containing the best action and the bidding value (as well as the plan)
  target-patch
  know-buttons-in-charge; the percentage of the knownledge each agent acuired for the button(s) it in charge of.
  ;
]


patches-own[
  potential-infor;if the agent is at that patch, with its set vision, the amount of information it at most may get.
  ]

; =================================================================
; ========================== The Setup part =======================
; =================================================================

to setup
  clear-all
  ;set noise 12; the randomly set points in each button that belongs to solution.
  ; set noise-dis 8; the randomly set points in each button that not belongs to solution.
  set color-list n-of num-agents [yellow magenta blue red pink brown grey];just for the sake of telling each agent apart
  set succeed-initialise-game false
  set can-walk true
  setup-ticks
  open-file; set up the goal pattern.
  setup-time
  setup-button
  setup-agents
  assign-buttons
  show-vision;show the agents' vision by * mark.
  setup-bidding
  setup-patches
  set trying true
  set time 0
  reset-timer
end

to setup-ticks
  reset-ticks
  set ticks-per-hour 0
  if (can-walk) [set ticks-per-hour (ticks-per-hour + 1)]

  set ticks-per-hour (ticks-per-hour + 1); to locate to a patch on the first hour of a day
  set ticks-per-hour (ticks-per-hour + 4); 4 sticks corresponding to: bid, observe, execute, learn
end

to setup-time
  set day 0
  set hour 0
  set bidding-day 0
end

to setup-bidding
  set bidding []
  foreach buttons[
    set bidding (fput 0 bidding)
    ]

end

; to load the goal pattern

to open-file

  file-open pattern-name
  set goal list [] []
  let delim ","

  set csv file-read-line
  let tmp split csv delim

  set width read-from-string item 0 tmp
  set height read-from-string item 1 tmp
  set-patch-size 250 / width
  resize-world 0 (width - 1) 0 ( height - 1)

  let x 0
  let y height - 1
  output-print "Goal:"
  while [not file-at-end?]
  [
    set csv file-read-line

    output-print csv
    set tmp split csv delim
    foreach tmp
    [
      let positive first goal
      let negative last goal

      ifelse (? = "1")
      [
        ; ask patch x y [set pcolor green]
        ; positive
        set goal (list (fput (x + y * width + 1 ) positive) negative)
        set x x + 1
        if (x = width)
        [
          set x 0
          set y y - 1
        ]
      ]
      [if (? = "0")
        [
          ; negative
          set goal (list positive (fput (x + y * width + 1 ) negative))
          set x x + 1
          if (x = width)
          [
            set x 0
            set y y - 1
          ]
        ]
      ]
    ]
  ]
  output-print "============================"
  file-close
end

to-report split [ string delim ]
  report reduce [
    ifelse-value (?2 = delim)
      [ lput "" ?1 ]
      [ lput word last ?1 ?2 but-last ?1 ]
  ] fput [""] n-values (length string) [ substring string ? (? + 1) ]
end

; to load and display the goal
to load-and-display-goal
  clear-all
  open-file
  foreach (first goal) [
    let x getx ?
    let y gety ?
    ask patch x y [set pcolor green]
    ]
end


to setup-patches
  ask patches[set pcolor black ]
end


to setup-button

  set noise (noise_pct * 100)
  set buttons-chosen-before []
  ; the total number of buttons =  num-agent * buttons-each
  ; we choose the first half and one more of the buttons as the plan

  let solution-buttons [] ; the solution plan to be achieved

  ;change the goal representation so patches to be set to black are represented as a negative number
  let goal-combination first goal
  foreach (last goal) [set goal-combination lput ( -1 * ? ) goal-combination]
  let total-buttons buttons-each * num-agents
  set num-hours min list ( floor ( total-buttons / 2 ) + 1 ) 4 ; the total number of steps for this plan, which is 1 + half of the total number of buttons

  ;----------------------------------------------------------
  ; Part one: buttons leading to solution

  let choose-num floor (( length goal-combination ) / ( num-hours - 1 )) ; the least number of propositions in each button

  ; here we use floor to avoid running out of propositions before the tidy up step (the last step)
  foreach n-values ( num-hours - 1 ) [?] ;each button that leads to solution without the step to tidy up the randomness

  [
   let remain-g-c goal-combination
   let chosen n-of choose-num remain-g-c
   set remain-g-c (remove chosen remain-g-c ) ; the remaining ones to be satisfied/choosen in further steps

   let pos []
   let neg []
   foreach chosen [

     ifelse ( ( ?  ) > 0)[
       set pos (lput ( ? ) pos)
     ][
     set neg  lput  (-1 * ?)  neg ]
   ] ; initialise the pair of pos and neg


  ;-----------------------------------------
  ; buttons with random values towards the goal
  let noise-vals []
  ifelse (noise <= (length goal-combination)) [
     set noise-vals n-of noise (n-values (length goal-combination) [?]);randomly choose positions in the goal with the number of noise
    ][
    set noise-vals (n-values (length goal-combination) [?])
    ;set noise-vals n-of (length goal-combination) (n-values (length goal-combination) [?]);randomly choose positions in the goal with the number of noise
    ]

   ; check if the random positions is already in the buttons, if not add it to the button.
   foreach noise-vals [
     ifelse ((member? (? + 1) pos) or (member? (? + 1) neg) )[

       ][
       ifelse (random 2 > 0)[
         set pos fput (? + 1) pos
         ][
         set neg fput (? + 1) neg
         ]
       ]
     ]
   set solution-buttons fput (list pos neg) solution-buttons
   ]



  foreach solution-buttons [ perform-action  ? ]
 ; a tidy up button
  let last-pos []
  let last-neg []
   ask patches [
    let index (width * pycor + pxcor + 1)
    if ((pcolor = black) and (member? index (first goal)))[set last-pos (lput index (last-pos))] ; should be green and is green now
    if ((pcolor = green) and (member? index (last goal)))[set last-neg (lput index (last-neg))]; should be black but is green now
    ]

   let last-btn (list last-pos last-neg)
   if (debug)[
     show last-btn
     show "^^^^^^^^^^^^^^^^^^"

     ]
   set solution-buttons lput (last-btn) solution-buttons
   perform-action last-btn

  ;----------------------------------------------------------
  ; Part 2: buttons not leading to patterns,i.e. disturbing the agents.

   let disturbing-buttons []
   let noise-dis  (choose-num + noise) ; the number of propositions in the disturbing buttons

      foreach n-values  ( buttons-each * num-agents - num-hours ) [?][
        let noise-dis-vals []
        ifelse (noise-dis <= length goal-combination)[
          set noise-dis-vals n-of noise-dis (n-values (length goal-combination) [? + 1]);randomly choose the elements
        ][
        set noise-dis-vals (n-values (length goal-combination) [? + 1])
        ;set noise-dis-vals n-of (length goal-combination) (n-values (length goal-combination) [?]);randomly choose the elements
        ]

        let pos-d  []
        let neg-d  []
        foreach noise-dis-vals [
          ifelse (random 2 > 0)[set pos-d fput ? pos-d]
          [set neg-d fput ? neg-d];randomly set the sign (on/off) to the elements
        ]

        set disturbing-buttons fput (list pos-d neg-d ) disturbing-buttons
        ]
   ;show length first (last disturbing-buttons)
    if (decidable)[
      ; reset the last button such that it lights up all the grids that have never been turned on.
      let light-so-far []
      foreach ( sentence  solution-buttons disturbing-buttons )[
         set light-so-far remove-duplicates ( sentence light-so-far first ? ); sumsming the grids that have been on.
         ]
      foreach (n-values (width * height) [? + 1])[
        if (not (member? ? light-so-far)) [
          set disturbing-buttons replace-item (length disturbing-buttons - 1 ) disturbing-buttons list (fput ? first (last disturbing-buttons) )(remove ? last (last disturbing-buttons))
          ]
        ]
    ]

    set buttons sentence solution-buttons disturbing-buttons ; append the disturbing buttons to the solution buttons

end


to setup-agents
  ;let all-black [];get the index of all the patches
  ;ask patches [set all-black (fput (get-patch-index self) all-black)]

  create-turtles num-agents [
    set observation []
    set desire "light up pathes as the goal"
    set intention "empty"
    set know-buttons-in-charge 0
    set label who
    setxy random-xcor random-ycor
     face patch-here
      move-to patch-here
    ; set the observation to black everywhere

    ;initialize the knowledge of actions,
    set action-knowledge []
    let k-tmp (list [] [])
    foreach n-values (length buttons)[?] [
      set action-knowledge (fput k-tmp action-knowledge)
      ]
    set personal-plan []
    ]
    foreach (n-values num-agents [?]) [ ask turtle ? [ set color item ? color-list] ];set different colors to agents.

end




to show-vision
  ask patches [set plabel ""]
  ;visulize of the vision,setting plabels in the vision
   ask turtles [
    set own-color color
    let oc own-color

       ask patches in-cone-nowrap (vision-radius * width / 100) 360
          [
;            set pcolor pcolor + 1; this code trace the routes(and vision) the agents go, you can delete it if you don't like it.
           set plabel-color oc
           set plabel "*"    ]
      ]
end

to-report get-patch-index [p]
  ifelse ([pcolor] of p = green) [report ([pycor] of p * width + [pxcor] of p) + 1]
  [report ([pycor] of p * width + [pxcor] of p + 1 ) * -1]
end



;==============the assignment of buttons to turtles============================================================
; Randomly assigned. The serial number for the button is the sequence of the buttons
; in the matrix "button-all", it is always that the first half or first (half + 0.5)
; buttons is the solution buttons.
;
to assign-buttons; randomly assign the buttons to the turtles
   let remain-bt buttons; variables remained when assigning buttons to agents one by one
   ask turtles[
     set buttons-assigned []
     foreach n-values buttons-each [?][
       let n-button ( random  (length remain-bt ))
       set buttons-assigned lput ((position  (item n-button remain-bt) buttons ) ) buttons-assigned
       set remain-bt (remove (item n-button remain-bt) remain-bt)
   ]
  ]
   ;anounce to all the agents the owner of the buttons
   let owner []
   foreach n-values (length buttons)[?] [
      set owner (fput -1 owner)
      ]
    ask turtles [
      foreach buttons-assigned[
        set owner replace-item ? owner who

        ]
     ]
   ask turtles[
     set button-owners owner
    ]


end


to perform-action [act]
  if (debug)[
    show act
    show "act-------------------------"
  ]

  let pos first act
  let neg last act
  foreach pos [

    let x getx ?
    let y gety ?

    if (debug)
    [
      show "---pos x y----"
      show ?
      show x
      show y]
    ask patch x y [set pcolor green]
    ]

    foreach neg [

    let y gety ?
    let x getx ?
    if (debug)[
      show "---neg x y----"
      show ?
      show x
      show y]
    ask patch x y [set pcolor black]
    ]
end

; =================================================================
; ========================== the "go" part ==========================
; =================================================================

to go

   update-desire
   update-intention
   update-belief
   exe-action
   set time timer
   if (hour = 0 and ticks = 0)[setup-ticks]
   tick
   if (ticks = ticks-per-hour)
   [set hour  (hour + 1)
     reset-ticks]

   if (hour = num-hours)
   [set day (day + 1)
     set hour 0]
   ; tick for communication
   if (can-communicate-at-night and hour = num-hours - 1 and ticks = 0)
   [set ticks-per-hour (ticks-per-hour + 1)]
   ;[if (day = 0 and hour = 0 and ticks = 0)[set ticks-per-hour (ticks-per-hour + 1)]]

   ; remove the tick from the second hour
   if ((hour = 1) and (ticks = 0))[set ticks-per-hour (ticks-per-hour - 1)]
   ; if the game is not initialised yet, give it a tick to set intention from empty to "to locate"
   if (succeed-initialise-game = false) [set ticks-per-hour (ticks-per-hour + 1)]
   ; once the game is initialised, this additional tick will never be added
   if (succeed-initialise-game = true and ticks = 1 and hour = 1 and day = 0) [set ticks-per-hour (ticks-per-hour - 1)]
   ; for a new day, we need an extra tick to locate itself
   if (hour = 0 and ticks = 0) [set ticks-per-hour (ticks-per-hour + 1)]

   if ((hour = 0) and (ticks  = 0))
   [
     if (knowledge-threshold < total-knowledge * 100) [set trying false]
     set buttons-chosen-before []
     ask patches [
       set pcolor black
       set plabel ""; todo
       ]
     ask turtles [set personal-plan []]
     ]

  ifelse not any? turtles
  [ stop ]
  [ set succeed-initialise-game true ]

  if (trying = false and hour = 0 and ticks = 0) [set bidding-day (bidding-day + 1)]

end

;=============== the BDI section ===================

to update-belief

  if all? turtles [intention = "to observe"] [
    observe
    ]
  if all? turtles [intention = "to observe and learn"] [
    observe-and-learn
    ]
end

to update-desire

  if(check-goal)
  [ask turtles [set desire "stop"]]
end


to update-intention
  ; this function is to provide a logical flow of the change of agent's intention
  ; with the impact from knowldege, time, desire, etc.
  ask turtles [
    ifelse (intention = "empty")
    [set intention "to locate"]
    [
      ifelse (desire = "stop");========================================to stop
      [set intention "self-upgrade"]
      [ifelse (intention = "to locate") ;==============================to locate
        [ifelse(trying)
          [set intention "to choose a random action"]
          [set intention "to bid"]
        ][ifelse (intention = "to choose a random action");===============to choose a random action
          [set intention "to observe"]
          [ifelse (intention = "to bid");==============================to bid
            [set intention "to observe"]
            [ifelse (intention =  "to observe");===========================to observe
              [set intention "to execute"]
              [ifelse (intention = "to execute")
                [set intention "to observe and learn"]
                [ifelse (intention = "to observe and learn");============to observe and learn
                  [ifelse (hour <= num-hours and can-walk)
                    [set intention "to move"]
                    [ifelse (hour = num-hours - 1 and can-communicate-at-night)
                      [set intention "to communicate"]
                      [
                        ifelse(hour = 0)
                        [set intention "to locate"]
                        [
                           ifelse (trying)
                           [set intention "to choose a random action"]
                           [set intention "to bid"]
                         ]

                      ]
                    ]
                  ]
                  [ifelse (intention = "to move");=======================to move
                    [
                      ifelse(can-communicate-at-night and (hour = num-hours - 1) and (ticks != 0))
                      [set intention "to communicate"]
                      [
                        ifelse (hour = num-hours - 1)
                        [set intention "to locate"]
                        [
                          ifelse (trying)
                          [set intention "to choose a random action"]
                          [set intention "to bid"]
                          ]
                       ]
                    ]
                    [ifelse (intention = "to communicate");==============to communicate
                      [set intention "to locate"]
                      [show "error!"]
                    ]
                  ]
                ]
              ]
            ]
          ]
        ]
      ]
    ]
  ]
end


to exe-action
   ; Note that there are two kinds of actions, the collective actions, these actions require
   ; a good synchronisation. That is, these agents are performing actions together or with
   ; restrictions of time. For example, communication requires all agents to be listening
   ; while bidding requires agents to come up with a bidding value and bidding action before
   ; making a group decision about the action to perform next.
   ;===============<collective actions>=======================
   if all? turtles [intention = "to bid" or intention = "to choose a random action"]
   [
     ifelse (not trying)
     [bid]
     [set bidding (n-values (length buttons) [0])]; if we have not reached the knowledge threshold, then we randomly select


     let max-value (max bidding)
     set button-chosen (one-of (filter [((item ? bidding)= max-value) and not (member? ? buttons-chosen-before)] n-values (length buttons)[?]))
     ; choose one of those with the best bidding value
     set buttons-chosen-before (fput button-chosen buttons-chosen-before)
     ; find the owner of button-chosen  and ask the agent to perform the action
     let owner 0
     foreach n-values num-agents [?]
     [if (member? button-chosen ([buttons-assigned] of (turtle ?)))
       [set owner ?]
     ]
     ask turtle owner
     [
       set personal-plan (fput button-chosen personal-plan)
       ask other turtles
       [set personal-plan (fput -1 personal-plan)]
     ]
   ]

   if all? turtles [intention = "to communicate"]; set up a meeting!
   [
     communicate
     ask turtles [update-average-individual-knowledge]
   ]

  ;==============<individual actions>====================
  ask turtles [
      ifelse (intention = "to move");============================to move
      [walk]
      [
        ifelse (intention = "to locate");=======================to locate
        [
          locate
;          show "set up location"

          ] ;  a random location
        [
          ifelse (intention = "self-upgrade"); =================to upgrade
          [
            output-program
            set pattern-and-plan (list goal personal-plan)
            die
            ]
          [if (intention = "to execute");======================= to execute an action
            [
              ifelse (((first personal-plan) = -1) or ((first personal-plan) = -2))
              [
                ;show "nothing to do here"
                ]
              [perform-action (item (first personal-plan) buttons)]
            ]
          ]
        ]
      ]
    ]

  show-vision

end

; to calculate the total (action) knowledge obtained by agents on average
to-report total-knowledge
  let pct 0
  ask turtles [
    set pct (pct + know-buttons-in-charge)
    ]
  set pct (pct / num-agents)
  report pct
end


to update-average-individual-knowledge; the average knownledge of the buttons each agent in charge of.

    ;let total-indi-know 0; the knowldege of all the buttons it
    set know-buttons-in-charge 0
    foreach buttons-assigned[
      let n length first (item ? action-knowledge)
      set know-buttons-in-charge (know-buttons-in-charge + n / (width * height))
    ]

    set know-buttons-in-charge (know-buttons-in-charge / buttons-each)
end

; check if the goal is reached. If reached, the game will terminates.
; The goal should not be reached when the agents are trying
to-report check-goal ; check if the current situation is the same as the goal
  let sign true
  foreach (first goal)[
    let x getx ?
    let y gety ?
    if (not (([pcolor] of (patch x y)) = green))[set sign false]
    ]
  foreach (last goal)[
    let x getx ?
    let y gety ?
    if (([pcolor] of (patch x y)) = green)[set sign false]
    ]
  if (trying) [report false]
  report sign
end

; two helping function to get the xcor and ycor of the patch according to its index
to-report getx [n]
   report (remainder (n - 1) width)
end

to-report gety [n]
  report ( floor ((n - 1) / width))
end

to observe
   ask turtles [
    let vision (patches in-cone-nowrap (vision-radius * width / 100) 360) ; the agent's vision
    let vision-indexes []
    ask vision [
      set vision-indexes fput (get-patch-index self)  vision-indexes
            ]
   set observation vision-indexes
   update-average-individual-knowledge
   ]
end

to observe-and-learn ; ask each agent to change the vision and vision index
  ask turtles [

    let vision (patches in-cone-nowrap ((vision-radius * width / 100) * width / 100) 360) ; the agent's vision
    let vision-indexes []
    ask vision [
      set vision-indexes fput (get-patch-index self)  vision-indexes
;      show self
      ]

;    show vision
;    show vision-indexes
    ; compare vision-indexes and observation to learn

    ; Step 1: obtain those not changed
    let know-false last (item button-chosen action-knowledge)
    let know-true first (item button-chosen action-knowledge)

    let not-changed  []
    if (not ((modes (sentence observation vision-indexes)) = (sentence observation vision-indexes))) and (not ((modes (sentence observation vision-indexes)) = vision-indexes))
    [set not-changed (modes (sentence observation vision-indexes))]


;    show "observation and vision-index"
;    show observation
;    show vision-indexes
;
;    show "not changed"
;    show not-changed

    let new-know-false []
    foreach not-changed [
      ifelse (? > 0)
      [set new-know-false fput ((? - 1) * 3 + 2) new-know-false]
      [set new-know-false fput (((? * -1) - 1) * 3 + 1) new-know-false]]; compute the new knowledge obtained from vision and observation
    set know-false remove-duplicates (sentence know-false new-know-false) ; extract information and add to belief of this action remove-duplicates

;    show "know false"
;    show know-false
;
    ; Step 2: obtain those changed

    let tmp (sentence (map [? * -1] observation) vision-indexes)
    let changed []
    if (not (modes tmp = tmp)) [set changed modes tmp] ; be careful about this line. if there is no repeated element then it would simply return the original list back!!!

    let new-know-true []
    foreach changed [
      ifelse (? > 0)
      [set new-know-true fput ((? - 1) * 3 + 1) new-know-true]
      [set new-know-true fput (((? * -1) - 1) * 3 + 2) new-know-true]]; compute the new knowledge obtained from vision and observation

    set know-true (remove-duplicates (sentence know-true new-know-true))

    ; Before we changed the knowledge about the action

    ; if we know that the action does not have any effect in both cases when a certain patch is on or off. Then we have say it has no effect
    foreach (n-values (width * height) [?])[
      ; if the other two are both members of know-false then we add itself to know true. That is, we know the effect of this action on this patch.

      if((member? (? * 3 + 1) know-false) and (member? (? * 3 + 2) know-false) and not (member? (? * 3 + 3) know-true))[

        set know-true (fput (? * 3 + 3) know-true)
        set know-false (remove (? * 3 + 1) know-false)
        set know-false (remove (? * 3 + 2) know-false)

        ]
      ]

    set know-true remove-duplicates know-true
    set know-false remove-duplicates know-false

    ; replace the knowledge of the action
    set action-knowledge replace-item button-chosen action-knowledge (list know-true know-false)
    ; and finally, set vision-indexes as the new observation
    ;set observation vision-indexes; TODO: what if after walk, there is no information about new local pathes?
    ]
end

; ===============================================================================
; ========================== the communicate and walk part ======================
; ===============================================================================


to communicate
   ; to combine all the action-button of every agent, getting a learning result:action-communication.
   let integration []

   foreach n-values (length buttons) [?][
   ; for each agent, we take the all their knowledge
   let know-true []
   let know-false []
   ask turtles [
     set know-true (remove-duplicates sentence know-true first (item ? action-knowledge))
     set know-false (remove-duplicates sentence know-false last (item ? action-knowledge))
     ]
   ; TODO: extract information from know-false to know-true

   set integration (lput (list know-true know-false) integration)
   ]

   ask turtles [
     set action-knowledge integration
     update-average-individual-knowledge
     ]
end


; ===============================================================================
; ========================== the bidding and planning part =======================
; ===============================================================================

; introduce a node structure for depth-first searching as planning
; it is a 3-tuple as follows:
; the bidding value
; the plan so far
; the world

to bid ; calculate the bidding value for each agent for each action
  ;a new bidding round
  reset-bidding

  ; ********* depth-first searching as planning *********

  ; initialise the planning part
  ; 1) construct an instance of the date structure
  ask turtles [
  let world-now represent-visable-world
  let current-node obtain-node (calculate-bidding world-now) buttons-chosen-before world-now

  ; 2) invoke the recursive method for planning
  depth-first-planning current-node

  ; 3) extract information from the best-node
  if (not (best-node = [])) [
    let act-best item (length buttons-chosen-before) (reverse item 1 best-node)
    if (item act-best bidding < (item 0 best-node)) [set bidding replace-item act-best bidding (item 0 best-node)]; then update the bidding
    ]
  ; change the bidding
  ]
end

; the result is a pair of action and the bidding value
to depth-first-planning [current-node]
  ; first, obtain the node with the best bidding value
  let stack (fput current-node [])
  set best-node []
  depth-first-planning-rec stack
end

to depth-first-planning-rec [stack]
  ifelse(not (stack = []))[
    let node (first stack)
    ; extract the information from a node
    let bv item 0 node
    let pl item 1 node ; the list of actions performed so far
    let wd item 2 node

    ; find all the actions performable in this world (i.e. not in the plan)
    ; the variable acts is the remaining buttons to be chosen for this hour
    let acts (n-values length buttons [?])
    foreach pl [
      set acts (remove ? acts);
      ]


   ifelse (length pl < num-hours) [ ; test if the node is a leaf node or an internal node
      foreach acts [
        let pl' (fput ? pl)
        let wd' (expected-world wd (item ? action-knowledge))
        let bv' calculate-bidding wd'
        let node' obtain-node bv' pl' wd'

          ifelse ( length pl' = num-hours)
          [
            ifelse (best-node = [])
            [set best-node node']
            [if ( bv' > (item 0 best-node))[set best-node node']] ; if it is better than the best node
          ][
            ifelse (not(wd' = []))[ ; avoid nodes where there is no knowledge
              ; add to the stack

              set stack (fput node' stack); add the child
              depth-first-planning-rec stack
              ][
                if (debug)[show "branch terminate because there is no knowledge here to do any prediction"]
              ]
          ]
      ]
      set stack remove node stack
    ]
    [ ; it is a leaf node and the plan is too long
      set stack remove node stack
      ]
    ][
  ]; else if the stack is empty then do nothing

end


to-report obtain-node [v p w]
  let node (fput w [])
  set node (fput p node)
  set node (fput v node)
  report node
end


to reset-bidding
  set bidding []
  foreach buttons [
    set bidding (fput 0 bidding)
    ]
end

; calculate the bidding function without learning factor
to-report calculate-bidding [world-after] ;  compare it with the goal and calculate a value for bidding
  let goal-on first goal
  let goal-off last goal
  let bidding-value 0
  foreach world-after[
     if (member? ? goal-on) [set bidding-value (bidding-value + 1)]
     if (member? ? goal-off) [set bidding-value (bidding-value - 1)]
     if (member? (? * -1) goal-off) [set bidding-value (bidding-value + 1)]
     if (member? (? * -1) goal-on) [set bidding-value (bidding-value - 1)]
    ]
  ; TODO: add the learning values on

  report bidding-value
end




to-report represent-visable-world ; to give the index of visable patches (for performing action in mind later)
  let vision-indexes []
  ; first obtain the list of visable patches
  let vision (patches in-cone-nowrap (vision-radius * width / 100) 360)
  ask vision[
    set vision-indexes fput (get-patch-index self)  vision-indexes
  ]

  ; obtain vision index
  report vision-indexes
end

; expand according to a given action

to-report expected-world [world act]; to perform an action according to the agent's knowledge
  ;show "the knowledge of the action is as follows"
  ;show act
  ; extract the certain effect of this action
  ; first the know-true part

  let expected []

  let know-true first act;
  let know-false last act;

  foreach world [
    ; ==== the certain part of the expected world
    ; first, there is no effect,
    if ((member? (3 * (? - 1) + 3) know-true) or (member? (3 * ((? * -1) - 1) + 3) know-true))
    [
      set expected (fput ? expected)] ; if the agent knows that the action has
                                      ; no effect on this patch then it keeps it in the expected world
    ]

     ; the agent also knows what is going to be true and false according to its knowledge of the action
    foreach know-true [
      ; get the index
      let index (floor (? / 3)) + 1
      ; get the color
      if ((remainder ? 3) = 1) [set expected (fput index expected)]
      if ((remainder ? 3) = 2) [set expected (fput (index * -1) expected)]
      ; if it is green then keep it positive, it black then keep it negative
      ]
    ; the rest is not sure for the agent.
  set expected (remove-duplicates expected)

  report expected
end

; randomly locate these agents to the center of a patch
to locate
  setxy random-xcor random-ycor
  face patch-here
  move-to patch-here
end

to walk; moves to the neighbor or current patch which has the most potential information to aquire.
  ;--------------local variables----------------
  ;vision-index: the index of the vision of the agent
  ;vision-known-index: if the agent was at each neighbor patch which would have an effect on current assigned button

  let neighbor sort neighbors
  foreach (sentence neighbor patch-here)[;neighbor patches(at most 8 for non-boundary patches) and current patch

    let vision-index []
    let world (patches in-cone-nowrap width 360)
    ask world [if ((distancexy [pxcor] of ? [pycor] of ?) <= (vision-radius * width / 100))
      [set vision-index lput  ( pxcor + pycor * width + 1) vision-index]];if the agent is at this patch, its vision.
    let amount [];the amount of information it at most will get in the specific patch neighbor, for each button it owns

    foreach buttons-assigned[
      let world-known map [floor( ? / 3 )] (item 0 ( item ?  action-knowledge ))
      let vision-known-index []
      if (not (modes (sentence world-known vision-index) = (sentence world-known vision-index)))
        [set vision-known-index ( modes (sentence world-known vision-index) )]; the visionindex that already in agent's knowledge.

       set amount (lput ((length vision-index) - (length vision-known-index)) amount )
     ];the amount of information a agent at most could aquire for this button at this patch.

    ask ? [set potential-infor mean amount]
    ; this is to calculate the mean value(potential information) of all the buttons it is incharge of for each neighbor and current location.

    ]
    set target-patch max-one-of neighbors [potential-infor]
    uphill potential-infor;
end

; a simple function for the interface
to-report gamming-status
  ifelse (trying)
  [report "trying"]
  [report "bidding"]

end

; this is the self-upgrade function where the agents update their programs according to the goal specified
; the output program is a program specification which can be further implemented in any language.
; the output is a Java (multi-thread) like description for each agent

to output-program
   output-type "Personal-plan of Agent " output-type who output-print ":"

   let personal-plan-in-order reverse personal-plan
   ;First, output plans except last one.
   let next-hour 0
   foreach but-last personal-plan-in-order [
     ifelse ( ? = -1)
     [ ifelse (next-hour != 0)[
        if (item (next-hour - 1) personal-plan-in-order != -1)
        [output-print "sleep;"]
        ]
        [output-print "sleep;"]
     ]
     [output-type "press Button " output-type ?
      ;to figure out who owns next executing button

     ifelse (item ( next-hour + 1) personal-plan-in-order != -1)
        [output-print ", continues;"
         ];keep awake
        [ output-type "; notifies Agent "
          output-type item (item ( next-hour + 1) (reverse buttons-chosen-before)) button-owners
          output-print ";"

            ]

      ]
     set next-hour next-hour + 1
     ]

   ;Second, output last plans
   ifelse (last personal-plan-in-order = -1)
   [
    if (last (but-last personal-plan-in-order) != -1)
       [output-print "sleep;"]
    output-print "check the result and exit."] ; to confirm
   [output-type "press Button "
    output-type last  personal-plan-in-order
    output-print "; notify all other agents: Goal Achieved."
    output-print "check results and exit."]
    output-print "========================================"

end
@#$#@#$#@
GRAPHICS-WINDOW
381
79
640
359
-1
-1
62.5
1
30
1
1
1
0
0
0
1
0
3
0
3
1
1
1
ticks
30.0

SLIDER
165
172
315
205
buttons-each
buttons-each
1
3
2
1
1
NIL
HORIZONTAL

BUTTON
29
553
106
586
NIL
go
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
112
553
184
586
NIL
go
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
16
430
104
464
NIL
setup
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
16
172
154
205
num-agents
num-agents
3
5
3
1
1
NIL
HORIZONTAL

SLIDER
17
214
154
247
vision-radius
vision-radius
0
100
80
10
1
NIL
HORIZONTAL

MONITOR
225
530
314
575
day
day
17
1
11

BUTTON
112
430
217
463
button 1
perform-action item 0 buttons
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
222
429
327
462
button 2
perform-action item 1 buttons
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
112
466
217
499
button 3
perform-action item 2 buttons
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
222
466
327
499
button 4
perform-action item 3 buttons
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

MONITOR
693
119
982
164
buttons of Agent 0
[buttons-assigned] of turtle 0
17
1
11

BUTTON
133
83
254
131
load and display
load-and-display-goal
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
165
215
314
248
noise_pct
noise_pct
10
20
20
1
1
NIL
HORIZONTAL

BUTTON
259
82
357
134
clear display
ask patches [set pcolor black]
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

MONITOR
16
468
112
513
total buttons
num-agents * buttons-each
17
1
11

MONITOR
224
579
315
624
hour
hour
17
1
11

MONITOR
17
671
200
716
plan so far
reverse buttons-chosen-before
17
1
11

PLOT
336
370
665
524
Agents' knowledge about their buttons
total hour
knowledge (%)
0.0
10.0
0.0
10.0
true
true
"" ""
PENS
"Agent 0" 1.0 0 -11085214 true "" "ifelse (not (count turtles = 0)) [plot [know-buttons-in-charge * 100] of turtle 0\nset-plot-pen-color ([color] of turtle 0)] [plot 0]"
"Agent 1" 1.0 0 -13791810 true "" "ifelse (not (count turtles = 0)) [plot [know-buttons-in-charge * 100] of turtle 1\nset-plot-pen-color ([color] of turtle 1)] [plot 0]"
"Agent 2" 1.0 2 -16644859 true "" "ifelse (not (count turtles = 0)) [plot [know-buttons-in-charge * 100] of turtle 2\nset-plot-pen-color ([color] of turtle 2)] [plot 0]"
"Average" 1.0 0 -16777216 true "" "plot (total-knowledge * 100)"

SLIDER
17
255
208
288
knowledge-threshold
knowledge-threshold
40
50
46
1
1
%
HORIZONTAL

MONITOR
18
621
199
666
bidding for current execution
bidding
17
1
11

MONITOR
172
341
311
386
hours per day (max 4)
num-hours
17
1
11

TEXTBOX
22
58
313
76
Step 1: load a file (test.txt for example)
12
0.0
1

TEXTBOX
22
152
233
182
Step 2: initialise the parameters
12
0.0
1

TEXTBOX
20
409
343
428
Step 3: setup the game and initialise the buttons
12
0.0
1

TEXTBOX
27
526
189
545
Step 4: play the game!
12
0.0
1

TEXTBOX
241
513
309
531
calendar
12
0.0
1

TEXTBOX
45
596
195
614
bidding and planning
12
0.0
1

CHOOSER
20
84
127
129
pattern-name
pattern-name
"test2.txt" "smile.txt" "sad.txt" "pi.txt"
0

TEXTBOX
383
55
550
75
Step 5: evaluation
12
0.0
1

SWITCH
216
256
315
289
debug
debug
1
1
-1000

SWITCH
15
299
323
332
can-communicate-at-night
can-communicate-at-night
0
1
-1000

TEXTBOX
74
16
968
43
Multi-agent Epistemic Action Learning for Planning and Self-upgrading
24
0.0
1

SWITCH
17
348
161
381
decidable
decidable
0
1
-1000

MONITOR
695
177
983
222
knowledge of agent 0
[action-knowledge] of turtle 0
17
1
11

MONITOR
729
635
879
680
move to target patch
[target-patch] of turtle 0
17
1
11

TEXTBOX
692
59
1049
108
Additional Information:\nThe belief, desire and intention of agent 0\n1) Belief
12
0.0
1

MONITOR
693
234
983
279
observation of turtle 0
[observation] of turtle 0
17
1
11

TEXTBOX
698
288
886
311
2) Desire
12
0.0
1

MONITOR
693
311
983
356
desire
[desire] of turtle 0
17
1
11

TEXTBOX
697
369
885
392
3) Intention
12
0.0
1

MONITOR
726
545
817
590
bidding value
first [best-node] of turtle 0
17
1
11

MONITOR
825
544
922
589
bidding action
item hour (reverse item 1 ([best-node] of turtle 0))
17
1
11

MONITOR
478
541
566
586
status
gamming-status
17
1
11

MONITOR
725
468
890
513
knowledge percentage
round (([know-buttons-in-charge] of turtle 0 ) * 1000)  / 10
17
1
11

MONITOR
725
395
959
440
intention
[intention] of turtle 0
17
1
11

TEXTBOX
727
449
983
479
(1) increase knowledge about actions
12
0.0
1

TEXTBOX
726
521
964
539
(2) to bid according to its knowledge
12
0.0
1

TEXTBOX
728
598
1004
628
(3) to move to the patch where it can possibly know more about the effect of actions
12
0.0
1

TEXTBOX
676
69
691
714
|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n|\n
12
0.0
1

MONITOR
726
725
913
770
personal plan
reverse ([personal-plan] of turtle 0)
17
1
11

TEXTBOX
727
691
989
724
(4) to obtain a personal plan for self-upgrading.
12
0.0
1

MONITOR
216
684
326
729
ticks per hour
ticks-per-hour
17
1
11

OUTPUT
344
613
653
771
10

TEXTBOX
390
596
540
614
Step 6: self-upgrading
12
0.0
1

MONITOR
224
629
314
674
ticks
ticks
17
1
11

TEXTBOX
708
449
723
749
  /\n |\n |\n |\n |\n |\n |\n |\n |\n/\n\\\n |\n |\n |\n |\n |\n |\n |\n |\n  \\
12
0.0
1

MONITOR
571
540
667
585
bidding days
bidding-day
17
1
11

MONITOR
344
540
473
585
total knowledge (%)
round (total-knowledge * 1000) / 10
17
1
11

MONITOR
182
734
342
779
time to complete the task
time
17
1
11

@#$#@#$#@
## WHAT IS IT?

This is a demo about a first attempt combining epistemic action learning with planning and self-upgrading for adaptive agents in BDI framework.

#### Description

There are some agents in this game assigned a task to press some buttons to light up the patch as required (the goal). The agents each got assigned some buttons at the beginning of the game. The agents can decide to perform only one action in one hour. A day consists of several hours. The agents then choose a location and start the game from the first hour. During a trying period, the agents randomly choose actions to perform. After that the agent start to bid about actions to be performed. The owner of the winning action will be notified to perform the action. The agents record the bidding history and once the goal is achieved, the agent then convert this bidding history to a partial plan and further convert to a program to upgrade itself.

#### What is an action? How are actions learnt?

In this game we consider only precondition-free action. By this we mean the precondition/requirement to perform the action is always satisfied. In this project we take pressing buttons as our actions. The agents are required to understand the postcondition of buttons. That is, the effect of the buttons. The action may turn a patch to green or turn a patch black. The agents compare patches before and after the action and extract knowledge about the action. More backgroud about action learning is in the project report as attached. The following is a guidance about this program.

## THINGS TO TRY

Users are encouraged to load the files provided to test the program. There are four files in total in the repository. Note that the pi.txt file may take a long time to run.

## HOW TO USE IT

The interface has been designed to be intuitive. As such, the interface follows a flow of buttons, sliders and monitors that an user might need to navigate the program and watch the simulation. The interface consists of the following steps:

### Step 1

load a pattern and test it on the patches using the two buttons "load and display" and "clear display". Please note that the "pi.txt" can be consume a long time.

The following are attributes and buttons related to this step:

pattern_name: This input box takes in the name of the file that contains the description of the goal pattern. the format is as follows:
1) The file is a simple txt file. The first line of the file always consists of 2 values, the height and the width of the world.
2) The file follows with a comma separated logical matrix, with the a value of 1 denoting an “on” pixel and a value of zero for an “off” pixel.

Load and display: This button loads the file, and displays it in the viewer for the user to see the end goal design.

the goal is in a green-black representation: it is represented as a pair of list of the goal pixels. The first sublist of the list is the collection of all the valid pixels, while the second sublist of the list is the collection of all the non valid pixels.

Clear display: This button simply clears the displays.

### Step 2

There are some parameters to be initialised before setting up the game.

num_agents: This slider controls how many agents are there in the world to solve the problem.

button_each: This slider controls how many buttons each agent gets.

vision_radius: This slider controls how far an agent can see and observe the environment.

num_hours: This slider controls how many hours make up the day in the environment.

noise_pct: This slider controls how much disturbance (in percentage) is added to the search in order for it to branch into a tree, rather than becoming a linear path to the goal.

decidable: this decides if all the patches can be turn "on" by at least one button.

### Step 3

This step is somply a set up step. Four example buttons generated are avaliable for mannual tests (together with the "clear display" button).

setup: This button sets up the world by initialising the world to its primitive state, loading the goal pattern in memory, spawning the agents and initialising their goals, beliefs, desires, intentions and button configurations, etc.

total buttons: This monitor shows how many buttons in total are there for the goal pattern to be generated. This is determined by multiplying the number of buttons each agent gets with the number of agents.

button 1 - 4: these buttons are generated buttons leading towards the goal: pressing these buttons sequentially would lead to the goal pattern but the agents do not know about this. More specifially, these are the example buttons that the agents get access too (each have access to some of them). Pressing them sequentially would turn on all the valid pixels and turns off all the invalid pixels. Pressing the first button will light up some pixels with some additional noise, while the next button will turn on some additional valid and invalid button, till button 3. If there are only four hours then pressing button 4 will turn off all the invalid pixels and make sure only the valid pixels of the goal configuration remains.

### Step 4

There are two ways to play the game: to do it step by step or run the game automatically.

go: This is a once button, and so it advances the world by one tick. The belief, intention, desire of agents may change. Note that this does not necessarily takes you to the next hour.

go (forever variant): This is a forever button variant, hence it continuously calls the go method and advances the ticks till the user stops it manually. it maybe the case that the agents got stuck because of too little information about actions. This game was designed in a way that these agents would not know the whole plan. So these agents will not be able to distinguish different executions. Therefore, repeated executions are allowed to happen.

Day: This monitor tracks the day.

Hour: This monitor tracks the hour.

plan so far: This monitor shows the most optimal plan found so far that is nearest to the goal node. This also represents the actions during the past few hours.

bidding: This monitor shows the bidding values of each buttons. It is clear to find out which button has won the bidding.

### Step 5

Apart from the patches we also provide a graphical representation of the knowledge of the first two agents and the overall knowledge of all the agents. The x-axis is the total hours taken while the y-axis is the agent's knowledge in percentage. This was calculated by dividing the length of each action's "know true" knowledge by the total number of patches. Notice that there is a chance that the knowledge can not go to 100%. That is, the action can remain undecidable even if the buttons are set to be decidable.

total knowledge: this number is a rough represenation of the overall knowledge of agent's knowledge. This is provided to be compared with the knowledge threshold.

status: there are two status, bidding and trying. When the game is in trying status, even if the agent's reach the goal by accident the agents will not be informed anything. The game continues.

bidding days: the total number of days the agents have been bidding.

### Step 6

Here we also provide a sketchy representation of the distributed upgrading programs. Each agent knows the goal and knows what to do at what time. The agent will pass on notification and wakes each other up to perform actions. When the agents finished pressing the last button, the agent would notify every other agent and they all check if there is anything mismatching the goal.

## Additional Information

Some additional information about the belief, intention and desire (of agent 0) is provided alongside.
### Belief

The belief consists of the agent's knowledge about the buttons assigned to it, a representation of the action knowledge as well as the world it just observed.

### Desire
The desire is represented as a string of text. The agent would like to light up the pattern and generate a program to upgrade itself according to the actions and knowledge provided and stop once complete.

### Intention

There are four parts of the intention

1) the agent intend to increase its knowledge about the buttons (especially the buttons it is in charge of).

2) the agent intend to bid for the best action according to its knowledge. This button might not be to press its buttons.

3) the agent is eager to observe the effect of the buttons. Agents are assumed to be free tomove around in this bounded area.

4) the agent would like to record the bidding result. Once informed a valid plan, the agent would like to generate a specification to further update itself accordingly.


## To report a bug
Robert White: ai.robert.wangshuai@gmail.com
@#$#@#$#@
default
true
0
Polygon -7500403 true true 150 5 40 250 150 205 260 250

airplane
true
0
Polygon -7500403 true true 150 0 135 15 120 60 120 105 15 165 15 195 120 180 135 240 105 270 120 285 150 270 180 285 210 270 165 240 180 180 285 195 285 165 180 105 180 60 165 15

arrow
true
0
Polygon -7500403 true true 150 0 0 150 105 150 105 293 195 293 195 150 300 150

box
false
0
Polygon -7500403 true true 150 285 285 225 285 75 150 135
Polygon -7500403 true true 150 135 15 75 150 15 285 75
Polygon -7500403 true true 15 75 15 225 150 285 150 135
Line -16777216 false 150 285 150 135
Line -16777216 false 150 135 15 75
Line -16777216 false 150 135 285 75

bug
true
0
Circle -7500403 true true 96 182 108
Circle -7500403 true true 110 127 80
Circle -7500403 true true 110 75 80
Line -7500403 true 150 100 80 30
Line -7500403 true 150 100 220 30

butterfly
true
0
Polygon -7500403 true true 150 165 209 199 225 225 225 255 195 270 165 255 150 240
Polygon -7500403 true true 150 165 89 198 75 225 75 255 105 270 135 255 150 240
Polygon -7500403 true true 139 148 100 105 55 90 25 90 10 105 10 135 25 180 40 195 85 194 139 163
Polygon -7500403 true true 162 150 200 105 245 90 275 90 290 105 290 135 275 180 260 195 215 195 162 165
Polygon -16777216 true false 150 255 135 225 120 150 135 120 150 105 165 120 180 150 165 225
Circle -16777216 true false 135 90 30
Line -16777216 false 150 105 195 60
Line -16777216 false 150 105 105 60

car
false
0
Polygon -7500403 true true 300 180 279 164 261 144 240 135 226 132 213 106 203 84 185 63 159 50 135 50 75 60 0 150 0 165 0 225 300 225 300 180
Circle -16777216 true false 180 180 90
Circle -16777216 true false 30 180 90
Polygon -16777216 true false 162 80 132 78 134 135 209 135 194 105 189 96 180 89
Circle -7500403 true true 47 195 58
Circle -7500403 true true 195 195 58

circle
false
0
Circle -7500403 true true 0 0 300

circle 2
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240

cow
false
0
Polygon -7500403 true true 200 193 197 249 179 249 177 196 166 187 140 189 93 191 78 179 72 211 49 209 48 181 37 149 25 120 25 89 45 72 103 84 179 75 198 76 252 64 272 81 293 103 285 121 255 121 242 118 224 167
Polygon -7500403 true true 73 210 86 251 62 249 48 208
Polygon -7500403 true true 25 114 16 195 9 204 23 213 25 200 39 123

cylinder
false
0
Circle -7500403 true true 0 0 300

dot
false
0
Circle -7500403 true true 90 90 120

face happy
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 255 90 239 62 213 47 191 67 179 90 203 109 218 150 225 192 218 210 203 227 181 251 194 236 217 212 240

face neutral
false
0
Circle -7500403 true true 8 7 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Rectangle -16777216 true false 60 195 240 225

face sad
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 168 90 184 62 210 47 232 67 244 90 220 109 205 150 198 192 205 210 220 227 242 251 229 236 206 212 183

fish
false
0
Polygon -1 true false 44 131 21 87 15 86 0 120 15 150 0 180 13 214 20 212 45 166
Polygon -1 true false 135 195 119 235 95 218 76 210 46 204 60 165
Polygon -1 true false 75 45 83 77 71 103 86 114 166 78 135 60
Polygon -7500403 true true 30 136 151 77 226 81 280 119 292 146 292 160 287 170 270 195 195 210 151 212 30 166
Circle -16777216 true false 215 106 30

flag
false
0
Rectangle -7500403 true true 60 15 75 300
Polygon -7500403 true true 90 150 270 90 90 30
Line -7500403 true 75 135 90 135
Line -7500403 true 75 45 90 45

flower
false
0
Polygon -10899396 true false 135 120 165 165 180 210 180 240 150 300 165 300 195 240 195 195 165 135
Circle -7500403 true true 85 132 38
Circle -7500403 true true 130 147 38
Circle -7500403 true true 192 85 38
Circle -7500403 true true 85 40 38
Circle -7500403 true true 177 40 38
Circle -7500403 true true 177 132 38
Circle -7500403 true true 70 85 38
Circle -7500403 true true 130 25 38
Circle -7500403 true true 96 51 108
Circle -16777216 true false 113 68 74
Polygon -10899396 true false 189 233 219 188 249 173 279 188 234 218
Polygon -10899396 true false 180 255 150 210 105 210 75 240 135 240

house
false
0
Rectangle -7500403 true true 45 120 255 285
Rectangle -16777216 true false 120 210 180 285
Polygon -7500403 true true 15 120 150 15 285 120
Line -16777216 false 30 120 270 120

leaf
false
0
Polygon -7500403 true true 150 210 135 195 120 210 60 210 30 195 60 180 60 165 15 135 30 120 15 105 40 104 45 90 60 90 90 105 105 120 120 120 105 60 120 60 135 30 150 15 165 30 180 60 195 60 180 120 195 120 210 105 240 90 255 90 263 104 285 105 270 120 285 135 240 165 240 180 270 195 240 210 180 210 165 195
Polygon -7500403 true true 135 195 135 240 120 255 105 255 105 285 135 285 165 240 165 195

line
true
0
Line -7500403 true 150 0 150 300

line half
true
0
Line -7500403 true 150 0 150 150

pentagon
false
0
Polygon -7500403 true true 150 15 15 120 60 285 240 285 285 120

person
false
0
Circle -7500403 true true 110 5 80
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 195 90 240 150 225 180 165 105
Polygon -7500403 true true 105 90 60 150 75 180 135 105

plant
false
0
Rectangle -7500403 true true 135 90 165 300
Polygon -7500403 true true 135 255 90 210 45 195 75 255 135 285
Polygon -7500403 true true 165 255 210 210 255 195 225 255 165 285
Polygon -7500403 true true 135 180 90 135 45 120 75 180 135 210
Polygon -7500403 true true 165 180 165 210 225 180 255 120 210 135
Polygon -7500403 true true 135 105 90 60 45 45 75 105 135 135
Polygon -7500403 true true 165 105 165 135 225 105 255 45 210 60
Polygon -7500403 true true 135 90 120 45 150 15 180 45 165 90

sheep
false
15
Circle -1 true true 203 65 88
Circle -1 true true 70 65 162
Circle -1 true true 150 105 120
Polygon -7500403 true false 218 120 240 165 255 165 278 120
Circle -7500403 true false 214 72 67
Rectangle -1 true true 164 223 179 298
Polygon -1 true true 45 285 30 285 30 240 15 195 45 210
Circle -1 true true 3 83 150
Rectangle -1 true true 65 221 80 296
Polygon -1 true true 195 285 210 285 210 240 240 210 195 210
Polygon -7500403 true false 276 85 285 105 302 99 294 83
Polygon -7500403 true false 219 85 210 105 193 99 201 83

square
false
0
Rectangle -7500403 true true 30 30 270 270

square 2
false
0
Rectangle -7500403 true true 30 30 270 270
Rectangle -16777216 true false 60 60 240 240

star
false
0
Polygon -7500403 true true 151 1 185 108 298 108 207 175 242 282 151 216 59 282 94 175 3 108 116 108

target
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240
Circle -7500403 true true 60 60 180
Circle -16777216 true false 90 90 120
Circle -7500403 true true 120 120 60

tree
false
0
Circle -7500403 true true 118 3 94
Rectangle -6459832 true false 120 195 180 300
Circle -7500403 true true 65 21 108
Circle -7500403 true true 116 41 127
Circle -7500403 true true 45 90 120
Circle -7500403 true true 104 74 152

triangle
false
0
Polygon -7500403 true true 150 30 15 255 285 255

triangle 2
false
0
Polygon -7500403 true true 150 30 15 255 285 255
Polygon -16777216 true false 151 99 225 223 75 224

truck
false
0
Rectangle -7500403 true true 4 45 195 187
Polygon -7500403 true true 296 193 296 150 259 134 244 104 208 104 207 194
Rectangle -1 true false 195 60 195 105
Polygon -16777216 true false 238 112 252 141 219 141 218 112
Circle -16777216 true false 234 174 42
Rectangle -7500403 true true 181 185 214 194
Circle -16777216 true false 144 174 42
Circle -16777216 true false 24 174 42
Circle -7500403 false true 24 174 42
Circle -7500403 false true 144 174 42
Circle -7500403 false true 234 174 42

turtle
true
0
Polygon -10899396 true false 215 204 240 233 246 254 228 266 215 252 193 210
Polygon -10899396 true false 195 90 225 75 245 75 260 89 269 108 261 124 240 105 225 105 210 105
Polygon -10899396 true false 105 90 75 75 55 75 40 89 31 108 39 124 60 105 75 105 90 105
Polygon -10899396 true false 132 85 134 64 107 51 108 17 150 2 192 18 192 52 169 65 172 87
Polygon -10899396 true false 85 204 60 233 54 254 72 266 85 252 107 210
Polygon -7500403 true true 119 75 179 75 209 101 224 135 220 225 175 261 128 261 81 224 74 135 88 99

ufo top
false
0
Circle -1 true false 15 15 270
Circle -16777216 false false 15 15 270
Circle -7500403 true true 75 75 150
Circle -16777216 false false 75 75 150
Circle -7500403 true true 60 60 30
Circle -7500403 true true 135 30 30
Circle -7500403 true true 210 60 30
Circle -7500403 true true 240 135 30
Circle -7500403 true true 210 210 30
Circle -7500403 true true 135 240 30
Circle -7500403 true true 60 210 30
Circle -7500403 true true 30 135 30
Circle -16777216 false false 30 135 30
Circle -16777216 false false 60 210 30
Circle -16777216 false false 135 240 30
Circle -16777216 false false 210 210 30
Circle -16777216 false false 240 135 30
Circle -16777216 false false 210 60 30
Circle -16777216 false false 135 30 30
Circle -16777216 false false 60 60 30

vacuum-cleaner
true
0
Polygon -2674135 true false 75 90 105 150 165 150 135 135 105 135 90 90 75 90
Circle -2674135 true false 105 135 30
Rectangle -2674135 true false 75 105 90 120

wheel
false
0
Circle -7500403 true true 3 3 294
Circle -16777216 true false 30 30 240
Line -7500403 true 150 285 150 15
Line -7500403 true 15 150 285 150
Circle -7500403 true true 120 120 60
Line -7500403 true 216 40 79 269
Line -7500403 true 40 84 269 221
Line -7500403 true 40 216 269 79
Line -7500403 true 84 40 221 269

wolf
false
0
Polygon -16777216 true false 253 133 245 131 245 133
Polygon -7500403 true true 2 194 13 197 30 191 38 193 38 205 20 226 20 257 27 265 38 266 40 260 31 253 31 230 60 206 68 198 75 209 66 228 65 243 82 261 84 268 100 267 103 261 77 239 79 231 100 207 98 196 119 201 143 202 160 195 166 210 172 213 173 238 167 251 160 248 154 265 169 264 178 247 186 240 198 260 200 271 217 271 219 262 207 258 195 230 192 198 210 184 227 164 242 144 259 145 284 151 277 141 293 140 299 134 297 127 273 119 270 105
Polygon -7500403 true true -1 195 14 180 36 166 40 153 53 140 82 131 134 133 159 126 188 115 227 108 236 102 238 98 268 86 269 92 281 87 269 103 269 113

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270

@#$#@#$#@
NetLogo 5.3
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
default
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0
Line -7500403 true 150 150 90 180
Line -7500403 true 150 150 210 180

shape-sensor
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0

@#$#@#$#@
0
@#$#@#$#@
