(module data racket
  (provide/contract
   [struct block ([x number?] [y number?] [color COLOR/C])]
   [struct posn ([x number?] [y number?])]
   [struct tetra ([center POSN/C] [blocks BSET/C])]
   [struct world ([tetra TETRA/C] [blocks BSET/C])]
   [posn=? (POSN/C POSN/C . -> . boolean?)]
   [COLOR/C any/c]
   [POSN/C any/c]
   [BLOCK/C any/c]
   [TETRA/C any/c]
   [WORLD/C any/c]
   [BSET/C any/c])
  (define BSET/C (listof BLOCK/C))
  (define COLOR/C symbol?)
  (define POSN/C (struct/c posn number? number?))
  (define BLOCK/C (struct/c block number? number? COLOR/C))
  (define TETRA/C (struct/c tetra POSN/C BSET/C))
  (define WORLD/C (struct/c world TETRA/C BSET/C))
  
  (struct posn (x y))
  (struct block (x y color))
  (struct tetra (center blocks))
  (struct world (tetra blocks))
  
  (define (posn=? p1 p2)
    (and (= (posn-x p1) (posn-x p2))
         (= (posn-y p1) (posn-y p2)))))

(module consts racket
  (provide/contract
   [block-size integer?]
   [board-width integer?]
   [board-height integer?])
  (define block-size 20)
  (define board-height 20)
  (define board-width 10))

(module block racket
  (provide/contract
   [block-rotate-ccw (POSN/C BLOCK/C . -> . BLOCK/C)]
   [block-rotate-cw (POSN/C BLOCK/C . -> . BLOCK/C)]
   [block=? (BLOCK/C BLOCK/C . -> . boolean?)]
   [block-move (number? number? BLOCK/C . -> . BLOCK/C)])
  (require (submod ".." data))
  
  ;; block=? : Block Block -> Boolean
  ;; Determines if two blocks are the same (ignoring color).
  (define (block=? b1 b2)
    (and (= (block-x b1) (block-x b2))
         (= (block-y b1) (block-y b2))))
  
  ;; block-move : Number Number Block -> Block
  (define (block-move dx dy b)
    (block (+ dx (block-x b))
           (+ dy (block-y b))
           (block-color b)))
  
  ;; block-rotate-ccw : Posn Block -> Block
  ;; Rotate the block 90 counterclockwise around the posn.
  (define (block-rotate-ccw c b)
    (block (+ (posn-x c) (- (posn-y c) (block-y b)))
           (+ (posn-y c) (- (block-x b) (posn-x c)))
           (block-color b)))
  
  ;; block-rotate-cw : Posn Block -> Block
  ;; Rotate the block 90 clockwise around the posn.
  (define (block-rotate-cw c b)
    (block-rotate-ccw c (block-rotate-ccw c (block-rotate-ccw c b)))))

(module list-fun racket
  (provide/contract
   [max (number? number? . -> . number?)]
   [min (number? number? . -> . number?)]
   [ormap ([BLOCK/C . -> . boolean?] (listof any/c) . -> . boolean?)]
   [andmap ([BLOCK/C . -> . boolean?] (listof any/c) . -> . boolean?)]
   [map ([BLOCK/C . -> . BLOCK/C] BSET/C . -> . BSET/C)]
   [filter ([BLOCK/C . -> . boolean?] BSET/C . -> . BSET/C)]
   [append (BSET/C BSET/C . -> . BSET/C)]
   [length ((listof any/c) . -> . integer?)]
   [foldr ([BLOCK/C BSET/C . -> . BSET/C] BSET/C BSET/C . -> . BSET/C)]
   [foldr-i ([BLOCK/C image? . -> . image?] image? BSET/C . -> . image?)]
   [foldr-n ((BLOCK/C number? . -> . number?) number? BSET/C . -> . number?)])
  (require (submod ".." image) (submod ".." data)))

(module bset racket
  (provide/contract
   [blocks-contains? (BSET/C BLOCK/C . -> . boolean?)]
   [blocks=? (BSET/C BSET/C . -> . boolean?)]
   [blocks-subset? (BSET/C BSET/C . -> . boolean?)]
   [blocks-intersect (BSET/C BSET/C . -> . BSET/C)]
   [blocks-count (BSET/C . -> . number?)]
   [blocks-overflow? (BSET/C . -> . boolean?)]
   [blocks-move (number? number? BSET/C . -> . BSET/C)]
   [blocks-rotate-cw (POSN/C BSET/C . -> . BSET/C)]
   [blocks-rotate-ccw (POSN/C BSET/C . -> . BSET/C)]
   [blocks-change-color (BSET/C COLOR/C . -> . BSET/C)]
   [blocks-row (BSET/C number? . -> . BSET/C)]
   [full-row? (BSET/C number? . -> . boolean?)]
   [blocks-union (BSET/C BSET/C . -> . BSET/C)]
   [blocks-max-x (BSET/C . -> . number?)]
   [blocks-min-x (BSET/C . -> . number?)]
   [blocks-max-y (BSET/C . -> . number?)])
  (require (submod ".." data) (submod ".." block) (submod ".." list-fun) (submod ".." consts))
  
  ;; blocks-contains? : BSet Block -> Boolean
  ;; Determine if the block is in the set of blocks.
  (define (blocks-contains? bs b)
    (ormap (λ (c) (block=? b c)) bs))
  
  ;; blocks-subset? : BSet BSet -> Boolean
  ;; is every element in bs1 also in bs2?
  (define (blocks-subset? bs1 bs2)
    (andmap (λ (b) (blocks-contains? bs2 b)) bs1))
  
  ;; blocks=? : BSet BSet -> Boolean
  ;; Determine if given sets of blocks are equal.
  (define (blocks=? bs1 bs2)
    (and (blocks-subset? bs1 bs2)
         (blocks-subset? bs2 bs1)))
  
  ;; blocks-intersect : BSet BSet -> BSet
  ;; Return the set of blocks that appear in both sets.
  (define (blocks-intersect bs1 bs2)
    (filter (λ (b) (blocks-contains? bs2 b)) bs1))
  
  ;; blocks-count : BSet -> Nat
  ;; Return the number of blocks in the set.
  (define (blocks-count bs)
    (length bs))  ;; No duplicates, cardinality = length.
  
  ;; blocks-move : Number Number BSet -> BSet
  ;; Move each block by the given X & Y displacement.
  (define (blocks-move dx dy bs)
    (map (λ (b) (block-move dx dy b)) bs))
  
  ;; blocks-rotate-ccw : Posn BSet -> BSet
  ;; Rotate the blocks 90 counterclockwise around the posn.
  (define (blocks-rotate-ccw c bs)
    (map (λ (b) (block-rotate-ccw c b)) bs))
  
  ;; blocks-rotate-cw : Posn BSet -> BSet
  ;; Rotate the blocks 90 clockwise around the posn.
  (define (blocks-rotate-cw c bs)
    (map (λ (b) (block-rotate-cw c b)) bs))
  
  ;; blocks-change-color : BSet Color -> BSet
  (define (blocks-change-color bs c)
    (map (λ (b) (block (block-x b) (block-y b) c))
         bs))
  
  ;; blocks-row : BSet Number -> BSet
  ;; Return the set of blocks in the given row.
  (define (blocks-row bs i)
    (filter (λ (b) (= i (block-y b))) bs))
  
  ;; full-row? : BSet Nat -> Boolean
  ;; Are there a full row of blocks at the given row in the set.
  (define (full-row? bs i)
    (= board-width (blocks-count (blocks-row bs i))))
  
  ;; blocks-overflow? : BSet -> Boolean
  ;; Have any/c of the blocks reach over the top of the board?
  (define (blocks-overflow? bs)
    (ormap (λ (b) (<= (block-y b) 0)) bs))
  
  ;; blocks-union : BSet BSet -> BSet
  ;; Union the two sets of blocks.
  (define (blocks-union bs1 bs2)
    (foldr (λ (b bs)
             (cond [(blocks-contains? bs b) bs]
                   [else (cons b bs)]))
           bs2
           bs1))
  
  ;; blocks-max-y : BSet -> Number
  ;; Compute the maximum y coordinate;
  ;; if set is empty, return 0, the coord of the board's top edge.
  (define (blocks-max-y bs)
    (foldr-n (λ (b n) (max (block-y b) n)) 0 bs))
  
  ;; blocks-min-x : BSet -> Number
  ;; Compute the minimum x coordinate;
  ;; if set is empty, return the coord of the board's right edge.
  (define (blocks-min-x bs)
    (foldr-n (λ (b n) (min (block-x b) n)) board-width bs))
  
  ;; blocks-max-x : BSet -> Number
  ;; Compute the maximum x coordinate;
  ;; if set is empty, return 0, the coord of the board's left edge.
  (define (blocks-max-x bs)
    (foldr-n (λ (b n) (max (block-x b) n)) 0 bs)))

(module elim racket
  (provide/contract
   [eliminate-full-rows (BSET/C . -> . BSET/C)])
  (require (submod ".." data) (submod ".." bset) (submod ".." consts))
  ;; eliminate-full-rows : BSet -> BSet
  ;; Eliminate all full rows and shift down appropriately.
  (define (eliminate-full-rows bs)
    (elim-row bs board-height 0))
  
  (define (elim-row bs i offset)
    (cond [(< i 0) empty]
          [(full-row? bs i)   (elim-row bs (sub1 i) (add1 offset))]
          [else (blocks-union (elim-row bs (sub1 i) offset)
                              (blocks-move 0 offset (blocks-row bs i)))])))

(module tetras racket
  (provide/contract ;[tetras (listof TETRA/C)]
   [tetra-move (integer? integer? TETRA/C . -> . TETRA/C)]
   [tetra-rotate-ccw (TETRA/C . -> . TETRA/C)]
   [tetra-rotate-cw (TETRA/C . -> . TETRA/C)]
   [tetra-overlaps-blocks? (TETRA/C BSET/C . -> . boolean?)]
   [build-tetra-blocks (COLOR/C number? number? integer? integer? integer? integer? integer? integer? integer? integer?
                                . -> .  TETRA/C)]
   [tetra-change-color (TETRA/C COLOR/C . -> . TETRA/C)])
  (require (submod ".." bset) (submod ".." data) (submod ".." consts) (submod ".." block))
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Tetras
  
  ;; tetra-move : Number Number Tetra -> Tetra
  ;; Move the Tetra by the given X & Y displacement.
  (define (tetra-move dx dy t)
    (tetra (posn (+ dx (posn-x (tetra-center t)))
                 (+ dy (posn-y (tetra-center t))))
           (blocks-move dx dy (tetra-blocks t))))
  
  ;; tetra-rotate-ccw : Tetra -> Tetra
  ;; Rotate the tetra 90 degrees counterclockwise around its center.
  (define (tetra-rotate-ccw t)
    (tetra (tetra-center t)
           (blocks-rotate-ccw (tetra-center t)
                              (tetra-blocks t))))
  
  ;; tetra-rotate-cw : Tetra -> Tetra
  ;; Rotate the tetra 90 degrees clockwise around its center.
  (define (tetra-rotate-cw t)
    (tetra (tetra-center t)
           (blocks-rotate-cw (tetra-center t)
                             (tetra-blocks t))))
  
  ;; tetra-overlaps-blocks? : Tetra BSet -> Boolean
  ;; Is the tetra on any/c of the blocks?
  (define (tetra-overlaps-blocks? t bs)
    (false? (false? (blocks-intersect (tetra-blocks t) bs))))
  
  ;; tetra-change-color : Tetra Color -> Tetra
  ;; Change the color of the given tetra.
  (define (tetra-change-color t c)
    (tetra (tetra-center t)
           (blocks-change-color (tetra-blocks t) c)))
  
  (define (build-tetra-blocks color xc yc x1 y1 x2 y2 x3 y3 x4 y4)
    (tetra-move 3 0 
                (tetra (posn xc yc)
                       (list (block x1 y1 color)
                             (block x2 y2 color)
                             (block x3 y3 color)
                             (block x4 y4 color))))))

(module world racket
  (provide/contract [world-key-move (WORLD/C string? . -> . WORLD/C)]
           [next-world (WORLD/C . -> . WORLD/C)]
           [ghost-blocks (WORLD/C . -> . BSET/C)])
  (require (submod ".." data) (submod ".." bset) (submod ".." block) (submod ".." tetras) (submod ".." aux) (submod ".." elim) (submod ".." consts))
  
  ;; touchdown : World -> World
  ;; Add the current tetra's blocks onto the world's block list,
  ;; and create a new tetra.
  (define (touchdown w)
    (world (list-pick-random tetras)
           (eliminate-full-rows (blocks-union (tetra-blocks (world-tetra w))
                                              (world-blocks w)))))
  
  ;; world-jump-down : World -> World
  ;; Take the current tetra and move it down until it lands.
  (define (world-jump-down w)
    (cond [(landed? w) w]
          [else (world-jump-down (world (tetra-move 0 1 (world-tetra w))
                                        (world-blocks w)))]))
  
  ;; landed-on-blocks? : World -> Boolean
  ;; Has the current tetra landed on blocks?
  ;; I.e., if we move the tetra down 1, will it touch any/c existing blocks?
  (define (landed-on-blocks? w)
    (tetra-overlaps-blocks? (tetra-move 0 1 (world-tetra w))
                            (world-blocks w)))
  
  ;; landed-on-floor? : World -> Boolean
  ;; Has the current tetra landed on the floor?
  (define (landed-on-floor? w)
    (= (blocks-max-y (tetra-blocks (world-tetra w)))
       (sub1 board-height)))
  
  ;; landed? : World -> Boolean
  ;; Has the current tetra landed?
  (define (landed? w)
    (or (landed-on-blocks? w)
        (landed-on-floor? w)))
  
  ;; next-world : World -> World
  ;; Step the world, either touchdown or move the tetra down on step.
  (define (next-world w)
    (cond [(landed? w) (touchdown w)]
          [else (world (tetra-move 0 1 (world-tetra w))
                       (world-blocks w))]))
  
  ;; try-new-tetra : World Tetra -> World
  ;; Make a world with the new tetra *IF* if doesn't lie on top of some other
  ;; block or lie off the board. Otherwise, no change.
  (define (try-new-tetra w new-tetra)
    (cond [(or (<  (blocks-min-x (tetra-blocks new-tetra)) 0)
               (>= (blocks-max-x (tetra-blocks new-tetra)) board-width)
               (tetra-overlaps-blocks? new-tetra (world-blocks w)))
           w]
          [else (world new-tetra (world-blocks w))]))
  
  ;; world-move : Number Number World -> World
  ;; Move the Tetra by the given X & Y displacement, but only if you can.
  ;; Otherwise stay put.
  (define (world-move dx dy w)
    (try-new-tetra w (tetra-move dx dy (world-tetra w))))
  
  ;; world-rotate-ccw : World -> World
  ;; Rotate the Tetra 90 degrees counterclockwise, but only if you can.
  ;; Otherwise stay put.
  (define (world-rotate-ccw w)
    (try-new-tetra w (tetra-rotate-ccw (world-tetra w))))
  
  ;; world-rotate-cw : World -> World
  ;; Rotate the Tetra 90 degrees clockwise, but only if you can.
  ;; Otherwise stay put.
  (define (world-rotate-cw w)
    (try-new-tetra w (tetra-rotate-cw (world-tetra w))))
  
  ;; ghost-blocks : World -> BSet
  ;; Gray blocks representing where the current tetra would land.
  (define (ghost-blocks w)
    (tetra-blocks (tetra-change-color (world-tetra (world-jump-down w))
                                      'gray)))
  
  ;; world-key-move : World KeyEvent -> World
  ;; Move the world according to the given key event.
  (define (world-key-move w k)
    (cond [(equal? k "left") (world-move neg-1 0 w)]
          [(equal? k "right") (world-move 1 0 w)]
          [(equal? k "down") (world-jump-down w)]
          [(equal? k "a") (world-rotate-ccw w)]
          [(equal? k "s") (world-rotate-cw w)]
          [else w])))

(module image racket
  (provide/contract
   [image? (any/c . -> . boolean?)]
   [overlay (image? image? . -> . image?)]
   [circle (number? number? string? . -> . image?)]
   [rectangle (number? number? COLOR/C COLOR/C . -> . image?)]
   [place-image (image? number? number? image? . -> . image?)]
   [empty-scene (number? number? . -> . image?)])
  (require (submod ".." data))
  (struct image (impl)))

(module aux racket
  (require (submod ".." data))
  (provide/contract
   [list-pick-random ((listof TETRA/C) . -> . TETRA/C)]
   [neg-1 integer?] ;; ha!
   [tetras (listof TETRA/C)]))

(module visual racket
  (provide/contract
   [world->image (WORLD/C . -> . image?)]
   [blocks->image (BSET/C . -> . image?)]
   [block->image (BLOCK/C . -> . image?)]
   [place-block (BLOCK/C image? . -> . image?)])
  (require (submod ".." image) (submod ".." data) (submod ".." consts) (submod ".." world) (submod ".." list-fun) (submod ".." aux))
  
  ;; Visualize whirled peas
  ;; World -> Scene
  (define (world->image w)
    (place-image (blocks->image (append (tetra-blocks (world-tetra w))
                                        (append (ghost-blocks w)
                                                (world-blocks w))))
                 0 0 
                 (empty-scene (* board-width block-size)
                              (* board-height block-size))))
  
  ;; BSet -> Scene
  (define (blocks->image bs)
    (foldr-i (λ (b img)
               (cond [(<= 0 (block-y b)) (place-block b img)]
                     [else img]))
             (empty-scene (add1 (* board-width block-size)) 
                          (add1 (* board-height block-size)))
             bs))
  
  ;; Visualizes a block.
  ;; Block -> Image
  (define (block->image b)
    (overlay 
     (rectangle (add1 block-size) (add1 block-size) 'solid (block-color b))
     (rectangle (add1 block-size) (add1 block-size) 'outline 'black)))
  
  ;; Block Scene -> Scene
  (define (place-block b scene)
    (place-image (block->image b)
                 (+ (* (block-x b) block-size) (/ block-size 2))
                 (+ (* (block-y b) block-size) (/ block-size 2))
                 scene))
  
  (define (world0)
    (world (list-pick-random tetras) #f)))
