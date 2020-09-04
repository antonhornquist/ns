
(define op-sequence-1
  `(
    (tempo 130 bpm)
    (kit b ,bassdrum s ,snare h ,hihat)
    (sequence
      (b  1  -  -  -  5  -  -  -  9  -  -  -  13 -  15 -  )
      (s  -  -  -  -  5  -  -  -  -  -  -  -  13 -  15 16 )
      (h  -  -  3  -  -  -  7  -  -  -  11 -  -  -  15 -  ))))

(define op-sequence-2
  `(
    (tempo 130 bpm)
    (kit bd ,bassdrum sn ,snare ch ,hihat)
    (sequence
      (mt  1  2  3  4  5  6  7  8  9  10 11 12 13 14 15 16 )
      (bd  x  -  -  -  x  -  -  -  x  -  -  -  x  -  x  -  )
      (sn  -  -  -  -  x  -  -  -  -  -  -  -  x  -  x  x  )
      (ch  -  -  x  -  -  -  x  -  -  -  x  -  -  -  x  -  ))))

(define op-sequence-2
  `(
    (tempo 130 bpm)
    (kit bd ,bassdrum sn ,snare ch ,hihat)
    (sequence
      (mt 1 2 3 4 5 6 7 8 1 2 3 4 5 6 7 8 )
      (bd x - - - x - - - x - - - x - x - )
      (sn - - - - x - - - - - - - x - x x )
      (ch - - x - - - x - - - x - - - x - ))))

