; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);
(make-event
 (er-progn
  (set-deferred-ttag-notes t state)
  (value '(value-triple :invisible))))

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/custom" :dir :system :ttags :all)

;; guard-checking-on is in *protected-system-state-globals* so any
;; changes are reverted back to what they were if you try setting this
;; with make-event. So, in order to avoid the use of progn! and trust
;; tags (which would not have been a big deal) in custom.lisp, I
;; decided to add this here.
;; 
;; How to check (f-get-global 'guard-checking-on state)
;; (acl2::set-guard-checking :nowarn)
(acl2::set-guard-checking :all)

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(set-inhibit-warnings! "Invariant-risk" "theory")

(in-package "ACL2")
(redef+)
(defun print-ttag-note (val active-book-name include-bookp deferred-p state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp deferred-p))
  state)

(defun print-deferred-ttag-notes-summary (state)
  (declare (xargs :stobjs state))
  state)

(defun notify-on-defttag (val active-book-name include-bookp state)
  (declare (xargs :stobjs state)
	   (ignore val active-book-name include-bookp))
  state)
(redef-)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
(definec len2 (x :tl) :nat
  (if (endp x)
      0
    (+ 1 (len2 (rest x)))))

(definec app2 (a :tl b :tl) :tl
  (if (endp a)
      b
    (cons (first a) (app2 (rest a) b))))

(defdata digit (oneof 0 1 2 3 4 5 6 7 8 9))
;(defdata leading-digit (oneof 1 2 3 4 5 6 7 8 9))
(defdata lod (listof digit))
(defdata PLN (cons digit lod))
(defdata NLN (cons '- PLN))
(defdata LN (oneof PLN NLN))



;(set-defunc-termination-strictp nil)
;(set-defunc-function-contract-strictp nil)
;(set-defunc-body-contracts-strictp nil)

;;(definec ltn-measure (l :nelod) :nat
  ;;(len2 l))

;(set-termination-method :measure)
;(set-well-founded-relation n<)
;(set-defunc-typed-undef nil)
;(set-defunc-generalize-contract-thm nil)
;(set-gag-mode nil)

(definec last-n (n :int) :PLN
  (list (mod (abs n) 10)))

(definec first-n (n :nat) :nat
  (/ (- n (mod n 10)) 10))

;(set-defunc-termination-strictp nil)
;(set-defunc-function-contract-strictp nil)
;(set-defunc-body-contracts-strictp nil)

;(defthm lod-rdc-len2 (implies (and (lodp x) (consp x)) (equal (len2 x) (+ (len2 (rdc x)) 1))))
;(defthm PLN-rdc-len2 (implies (and (PLNp x) (consp x)) (equal (len2 x) (+ (len2 (rdc x)) 1))))


#|
(definec list-to-number-p (l :PLN) :nat
  :function-contract-hints (("Goal" :HANDS-OFF (LAST-N car last rdc)))
  (cond
   ((endp (cdr l)) (car (last l)))
   (t (+ (car (last l)) (* 10 (list-to-number-p (rdc l)))))))

(definec list-to-number (l :LN) :int
  (cond
   ((NLNp l) (- (list-to-number-p (cdr l))))
   (t (list-to-number-p l))))

(DEFTHM LIST-TO-NUMBER-P-CONTRACT
         (IMPLIES (FORCE (PLNP L))
                  (INTEGERP (LIST-TO-NUMBER-P L))))
|#
(defthm PLN-TL (implies (PLNp x) (tlp x)))

(defthm LOD-app2 (implies (and (lodp x) (lodp y)) (lodp (app2 x y))))

(defthm PLN-app2 (implies (and (PLNp x) (PLNp y)) (PLNp (app2 x y))))

;(set-defunc-termination-strictp nil)
;(set-defunc-function-contract-strictp nil)
;(set-defunc-body-contracts-strictp nil)

(Set-defunc-timeout 120)

(PROGN
 (ENCAPSULATE
   NIL
   (ENCAPSULATE
        ((ACL2S-PLN-UNDEFINED (X Y)
                              T
                              :GUARD (AND (SYMBOLP X) (TRUE-LISTP Y))))
        (LOCAL (DEFUN ACL2S-PLN-UNDEFINED (X Y)
                      (DECLARE (IGNORABLE X Y))
                      '(0)))
        (DEFTHM ACL2S-PLN-UNDEFINED-PLNP
                (PLNP (ACL2S-PLN-UNDEFINED X Y))
                :RULE-CLASSES ((:TYPE-PRESCRIPTION) (:REWRITE))))
   (DEFUN ACL2S-PLN-UNDEFINED-ATTACHED (X Y)
          (DECLARE (XARGS :GUARD (AND (SYMBOLP X) (TRUE-LISTP Y))))
          (PROG2$ (CGEN::CW? (SHOW-CONTRACT-VIOLATIONS?)
                             "~|**Input contract  violation in ~x0**: ~x1 ~%"
                             'ACL2S-PLN-UNDEFINED-ATTACHED
                             (CONS X Y))
                  '(0)))
   (DEFATTACH ACL2S-PLN-UNDEFINED
              ACL2S-PLN-UNDEFINED-ATTACHED))
 (ENCAPSULATE
    NIL
    (WITH-OUTPUT
         :OFF :ALL :ON (ERROR)
         (DEFUN NUMBER-TO-LIST-P (N)
                (DECLARE (XARGS :GUARD (NATP N)
                                :VERIFY-GUARDS NIL
                                :NORMALIZE NIL
                                :TIME-LIMIT 90))
                (MBE :LOGIC (IF (NATP N)
                                (COND ((< (/ N 10) 1) (LAST-N N))
                                      (T (APP2 (NUMBER-TO-LIST-P (FIRST-N N))
                                               (LAST-N N))))
                                (ACL2S-PLN-UNDEFINED 'NUMBER-TO-LIST-P
                                                     (LIST N)))
                     :EXEC (COND ((< (/ N 10) 1) (LAST-N N))
                                 (T (APP2 (NUMBER-TO-LIST-P (FIRST-N N))
                                          (LAST-N N))))))))
 (DEFTHM NUMBER-TO-LIST-P-CONTRACT-1
         (IMPLIES (FORCE (NATP N))
                  (PLNP (NUMBER-TO-LIST-P N)))
         :HINTS (("Goal" :HANDS-OFF (LAST-N APP2))))
 (ENCAPSULATE
    NIL
    (WITH-OUTPUT
         :OFF :ALL :ON (ERROR)
         (VERIFY-GUARDS NUMBER-TO-LIST-P
                        :GUARD-DEBUG T
                        :HINTS (("Goal" :DO-NOT-INDUCT T
                                        :DO-NOT '(GENERALIZE FERTILIZE)))))))

(definec number-to-list-p (n :nat) :PLN
  :function-contract-hints (("Goal" :HANDS-OFF (LAST-N APP2)))
  (cond
   ((< (/ n 10) 1) (last-n n))
   (t (app2 (number-to-list-p (first-n n)) (last-n n)))))

(definec number-to-list (n :int) :LN
  (cond
   ((< n 0) (cons '- (number-to-list-p (- n))))
   (t (number-to-list-p n))))

;(set-defunc-termination-strictp nil)
;(set-defunc-function-contract-strictp nil)
;(set-defunc-body-contracts-strictp nil)

;(defthm car-last-PLN (implies (and (PLNP x) (consp x)) (natp (car (last x)))))

(definec last-l (l :PLN) :nat
  :ic (consp l)
  (if (PLNp (cdr l)) (last-l (cdr l)) (car l)))

(definec RDC (l :PLN) :lod
  (cond
   ((endp (cdr l)) nil)
   (t (cons (car l) (RDC (cdr l))))))

(definec first-l (l :PLN) :PLN
  :ic (consp (cdr l))
  (rdc l))

;(defthm first-l-PLN (implies (and (PLNp x) (consp (cdr x))) (PLNp (first-l x))))

(definec list-to-number-p (l :PLN) :nat
  :function-contract-hints (("Goal" :HANDS-OFF (rdc)))
  (cond
   ((endp (cdr l)) (last-l l))
   (t (+ (last-l l) (* 10 (list-to-number-p (rdc l)))))))

(definec list-to-number (l :LN) :int
  (cond
   ((NLNp l) (- (list-to-number-p (cdr l))))
   (t (list-to-number-p l))))

(test? (implies (intp x) (equal (list-to-number (number-to-list x)) x)))

(defthm int-add-list (implies (and (LNp x) (LNp y)) (intp (binary-+ (list-to-number f) (list-to-number s)))))
(defthm LN-add-list (implies (AND (FORCE (LNP F)) (FORCE (LNP S))) (LNp (number-to-list (binary-+ (list-to-number f) (list-to-number s))))))

(definec abs-list (l :LN) :LN
  (cond
   ((equal (car l) '-) (cdr l))
   (t l)))

(definec negate-list (l :LN) :LN
  (number-to-list (* -1 (list-to-number l))))

;(set-defunc-function-contract-strictp nil)
(definec add-lists (f :LN s :LN) :LN
  :function-contract-hints (("Goal" :USE (LN-add-list add-lists) :hands-off (lnp digitp)) ("Goal'" :expand ((add-lists f s))))
  (number-to-list (binary-+ (list-to-number f) (list-to-number s))))
;(set-defunc-function-contract-strictp t)

(defthm int-sub-list (implies (and (LNp x) (LNp y)) (intp (- (list-to-number f) (list-to-number s)))))
(defthm LN-sub-list (implies (AND (FORCE (LNP F)) (FORCE (LNP S))) (LNp (number-to-list (- (list-to-number f) (list-to-number s))))))

(definec sub-lists (f :LN s :LN) :LN
  :function-contract-hints (("Goal" :USE (LN-sub-list sub-lists) :hands-off (lnp digitp)) ("Goal'" :expand ((sub-lists f s))))
  (number-to-list (- (list-to-number f) (list-to-number s))))

(defthm LN-expt-list (implies (AND (FORCE (LNP l)) (FORCE (NATP x)) #|(< x 5)|#) (LNp (number-to-list (* (list-to-number l) (expt 10 x))))))

(definec list-pow-ten (l :LN x :nat) :LN
  #|:ic (< x 5)|#
  :function-contract-hints (("Goal" :USE (LN-expt-list list-pow-ten) :hands-off (lnp digitp binary-*))) ;("Goal'" :expand ((sub-lists f s))))
  (number-to-list (* (list-to-number l) (expt 10 x))))

(defthm int-mult-list (implies (and (LNp x) (LNp y)) (intp (* (list-to-number f) (list-to-number s)))))
(defthm LN-mult-list (implies (AND (FORCE (LNP F)) (FORCE (LNP S))) (LNp (number-to-list (* (list-to-number f) (list-to-number s))))))

(definec mult-lists (f :LN s :LN) :LN
  :function-contract-hints (("Goal" :USE (LN-mult-list mult-lists) :hands-off (lnp digitp)))
  (number-to-list (* (list-to-number f) (list-to-number s))))

;;(acl2s-defaults :set testing-enabled nil)
#|
(definec karatsuba (f :LN s :LN) :LN
  :ic (and (<= (len2 f) 2) (<= (len2 s) 2))
  (cond
   ((and (< (car f) 0) (< (car s) 0)) (karatsuba (abs-list f) (abs-list s)))
   ((< (car s) 0) (negate-list (karatsuba f (abs-list s))))
   ((< (car f) 0) (negate-list (karatsuba (abs-list f) s)))
   ((or (equal (len2 f) 1) (equal (len2 s) 1)) (number-to-list (* (list-to-number f) (list-to-number s))))
   (t (app2 (karatsuba (first-half f) (first-half s)) (app2 (add-lists (add-lists (karatsuba (sub-lists (second-half f) (first-half f)) (sub-lists (first-half s) (second-half s))) (karatsuba (first-half f) (first-half s))) (karatsuba (second-half f) (second-half s))) (karatsuba (second-half f) (second-half s)))))))
;;most functional version, but is basically just a bunch of conversions and doesn't take advantage of list properties very well
|#

#|(DEFTHM KARATSUBA2-1-P-help
         (IMPLIES (AND (FORCE (LNP F))
                       (FORCE (LNP S))
                       (FORCE (EQUAL (LEN2 F) 1))
                       (FORCE (EQUAL (LEN2 S) 1)))
                  (LNP (mult-lists F S))))|#

(definec karatsuba2-1 (f :LN s :LN) :LN
  :function-contract-hints (("Goal" :hands-off (lnp digitp)))
  :ic (and (or (and (equal (len2 f) 1) (PLNp f)) (and (equal (len2 f) 2) (NLNp f))) (or (and (equal (len2 s) 1) (PLNp s)) (or (equal (len2 s) 1) (NLNp s))))
  (mult-lists f s))

(definec first-half (l :PLN) :PLN
  :ic (equal (len2 l) 2)
   (list (car l)))

(definec second-half (l :PLN) :PLN
  :ic (equal (len2 l) 2)
  :oc (equal (len2 (second-half l)) 1)
    (cdr l))

(defthm PLN-k2-ac (implies (and (plnp f) (plnp s) (equal (len2 f) 2) (equal (len2 s) 2)) (plnp (karatsuba2-1 (first-half f) (first-half s)))))

(definec karatsuba2-ac (f :PLN s :PLN) :PLN
  :function-contract-hints (("Goal" :USE (PLN-k2-ac karatsuba2-ac) :hands-off (plnp digitp)))
  :ic (and (equal (len2 f) 2) (equal (len2 s) 2))
  (karatsuba2-1 (first-half f) (first-half s)))

(definec karatsuba2-fp (f :PLN s :PLN) :PLN
  :function-contract-hints (("Goal" :USE (PLN-k2-ac karatsuba2-ac) :hands-off (plnp digitp)))
  :ic (and (equal (len2 f) 2) (equal (len2 s) 2))
  (list-pow-ten (karatsuba2-ac f s) 2))

(defthm PLN-k2-bd-1 (implies (and (plnp f) (equal (len2 f) 2) (plnp s) (equal (len2 s) 2)) (and (equal (len2 (second-half f)) 1) (equal (len2 (second-half s)) 1) (plnp (second-half f)) (plnp (second-half s))))
  :HINTS (("Goal" :hands-off (plnp digitp))))

(defthm PLN-k2-bd-2 (implies (and (plnp f) (equal (len2 f) 1) (plnp s) (equal (len2 s) 1)) (plnp (karatsuba2-1 f s)))
  :HINTS (("Goal" :hands-off (plnp digitp))))

(defthm PLN-k2-bd (implies (and (plnp f) (equal (len2 f) 2) (plnp s) (equal (len2 s) 2)) (plnp (karatsuba2-1 (second-half f) (second-half s))))
  :HINTS (("Goal" :use (PLN-k2-bd-1 PLN-k2-bd-2) :hands-off (plnp digitp))))


(acl2s-defaults :set testing-enabled nil)
(set-defunc-function-contract-strictp nil)
(definec karatsuba2-bd (f :PLN s :PLN) :PLN
  :function-contract-hints (("Goal" :USE (PLN-K2-BD KARATSUBA2-BD)
                         :HANDS-OFF (PLNP DIGITP)))
  :ic (and (equal (len2 f) 2) (equal (len2 s) 2))
  (karatsuba2-1 (second-half f) (second-half s)))

(DEFTHM KARATSUBA2-BD-CONTRACT
         (IMPLIES (AND (FORCE (PLNP F))
                       (FORCE (PLNP S))
                       (FORCE (EQUAL (LEN2 F) 2))
                       (FORCE (EQUAL (LEN2 S) 2)))
                  (PLNP (KARATSUBA2-BD F S)))
         :HINTS (("Goal" :USE (PLN-K2-BD KARATSUBA2-BD)
                         :HANDS-OFF (PLNP DIGITP))))

(acl2s-defaults :set testing-enabled t)
(set-defunc-function-contract-strictp t)

(defthm PLN-k2-a+b-1 (implies (and (plnp f) (equal (len2 f) 2)) (and (equal (len2 (second-half f)) 1) (plnp (second-half f)))))

(defthm PLN-k2-a+b-2 (implies (and (plnp f) (equal (len2 f) 1) (plnp s) (equal (len2 s) 1)) (plnp (add-lists f s))))

(defthm PLN-k2-a+b (implies (and (plnp f) (equal (len2 f) 2) (equal (len2 (second-half f)) 1) (plnp (second-half f)) (equal (len2 (first-half f)) 1) (plnp (first-half f))) (plnp (add-lists (first-half f) (second-half f))))
  :HINTS (("Goal" :use (PLN-k2-a+b-1 PLN-k2-a+b-2) :hands-off (plnp digitp))))

(acl2s-defaults :set testing-enabled nil)
(set-defunc-function-contract-strictp nil)
(definec karatsuba2-a+b (f :PLN) :PLN
  :function-contract-hints (("Goal" :USE (PLN-K2-a+b PLN-K2-a+b-1 PLN-K2-a+b-2 KARATSUBA2-a+b) :HANDS-OFF (PLNP DIGITP)))
  :ic (equal (len2 f) 2)
  (add-lists (first-half f) (second-half f)))
(acl2s-defaults :set testing-enabled t)
(set-defunc-function-contract-strictp t)

(DEFTHM KARATSUBA2-A+B-CONTRACT
         (IMPLIES (AND (FORCE (PLNP F))
                       (FORCE (EQUAL (LEN2 F) 2)))
                  (PLNP (KARATSUBA2-A+B F)))
         :HINTS (("Goal" :USE (PLN-K2-A+B PLN-K2-A+B-1
                                          PLN-K2-A+B-2 KARATSUBA2-A+B)
                         :HANDS-OFF (PLNP DIGITP))))
#|
(defthm PLN-k2-c+d-1 (implies (and (plnp s) (equal (len2 s) 2)) (and (equal (len2 (second-half s)) 1) (plnp (second-half s)))))

(defthm PLN-k2-c+d (implies (and (plnp s) (equal (len2 s) 2) (equal (len2 (second-half s)) 1) (plnp (second-half s)) (equal (len2 (first-half s)) 1) (plnp (first-half s))) (plnp (add-lists (first-half s) (second-half s))))
  :HINTS (("Goal" :use (PLN-k2-c+d-1 PLN-k2-a+b-2) :hands-off (plnp digitp))))

(acl2s-defaults :set testing-enabled nil)
(set-defunc-function-contract-strictp nil)
(definec karatsuba2-c+d (s :PLN) :PLN
  :function-contract-hints (("Goal" :USE (PLN-K2-c+d PLN-K2-c+d-1 PLN-K2-a+b-2 KARATSUBA2-c+d) :HANDS-OFF (PLNP DIGITP)))
  :ic (equal (len2 s) 2)
  (add-lists (first-half s) (second-half s)))
(acl2s-defaults :set testing-enabled t)
(set-defunc-function-contract-strictp t)

(DEFTHM KARATSUBA2-c+d-CONTRACT
         (IMPLIES (AND (FORCE (PLNP s))
                       (FORCE (EQUAL (LEN2 s) 2)))
                  (PLNP (KARATSUBA2-A+B s)))
         :HINTS (("Goal" :USE (PLN-K2-c+d PLN-K2-c+d-1
                                          PLN-K2-A+B-2 KARATSUBA2-c+d)
                         :HANDS-OFF (PLNP DIGITP))))
|#
(defthm PLN-k2-mp1-1 (implies (and (plnp f) (plnp s)) (plnp (mult-lists f s)))
  :HINTS (("Goal"  :hands-off (plnp digitp))))

(defthm PLN-k2-mp1-2 (implies (and (plnp f) (equal (len2 f) 2)) (plnp (karatsuba2-a+b f)))
  :HINTS (("Goal"  :hands-off (plnp digitp))))

(defthm PLN-k2-mp1-3 (implies (and (plnp s) (equal (len2 s) 2)) (plnp (karatsuba2-a+b s)))
  :HINTS (("Goal" :hands-off (plnp digitp))))

(defthm PLN-k2-mp1-4 (implies (and (plnp f) (equal (len2 f) 2) (plnp s) (equal (len2 s) 2)) (and (plnp (karatsuba2-a+b f)) (plnp (karatsuba2-a+b s))))
  :HINTS (("Goal"  :hands-off (plnp digitp))))

(defthm PLN-k2-mp1 (implies (and (plnp f) (equal (len2 f) 2) (plnp s) (equal (len2 s) 2)) (plnp (mult-lists (karatsuba2-a+b f) (karatsuba2-a+b s))))
  :HINTS (("Goal" :use (PLN-k2-bd-1 PLN-k2-mp1-2 PLN-k2-mp1-3 PLN-k2-mp1-4) :hands-off (plnp digitp))))



(definec LN-int-equiv (x :LN y :int) :boolean
  (and (equal (list-to-number x) y) (equal x (number-to-list y))))

(defthm LN-int-equiv-test-1 (implies (and (LNp x) (intp y) (LN-int-equiv x y)) (LN-int-equiv (number-to-list y) (list-to-number x)))
  :HINTS (("Goal" :hands-off (digitp lnp))))

(defthm ltn-ntl-opposites-1 (implies (and (intp x) (LN-int-equiv (number-to-list x) x)) (equal (list-to-number (number-to-list x)) x))
  :HINTS (("Goal" :hands-off (digitp lnp))))

(defthm LN-int-equiv-test-2 (implies (and (LNp x) (intp y) (LN-int-equiv x y)) (LN-int-equiv (number-to-list (list-to-number x)) (list-to-number (number-to-list y))))
  :HINTS (("Goal" :hands-off (digitp lnp))))

(defthm ltn-ntl-opposites-2 (implies (and (intp x) (intp y) (LN-int-equiv (number-to-list x) y)) (equal (list-to-number (number-to-list x)) y))
  :HINTS (("Goal" :hands-off (digitp lnp))))
#|
(defthm ltn-ntl-opposites-3 (implies (and (intp x) (intp y) (LN-int-equiv (number-to-list x) y)) (equal (number-to-list x) (number-to-list y)))
  :HINTS (("Goal" :hands-off (digitp lnp))))

(defthm ltn-ntl-opposites-4 (implies (and (intp x) (intp y) (equal (identity x) y)) (equal (number-to-list x) (number-to-list y)))
  :HINTS (("Goal" :hands-off (digitp lnp))))

(defthm ltn-ntl-opposites-5 (implies (and (intp x) (intp y) (equal (number-to-list x) (number-to-list y))) (equal (identity x) y))
  :HINTS (("Goal" :hands-off (digitp lnp))))

(defthm ltn-ntl-opposites-6 (implies (intp x) (equal (list-to-number (number-to-list x)) x))
  :HINTS (("Goal" :hands-off (digitp lnp))))|#

(defthm LN-int-mult-equiv-1 (implies (and (intp x) (LN-int-equiv (number-to-list x) x) (LN-int-equiv (number-to-list (* x x)) (* x x))) (equal (list-to-number (mult-lists (number-to-list x) (number-to-list x))) (* x x)))
  :HINTS (("Goal" :use ((:instance mult-lists-definition-rule (f (number-to-list x)) (s (number-to-list x))) ltn-ntl-opposites-1) :hands-off (digitp lnp binary-*))))

(defthm LN-int-add-equiv-1 (implies (and (intp x) (LN-int-equiv (number-to-list x) x) (LN-int-equiv (number-to-list (+ x x)) (+ x x))) (equal (list-to-number (add-lists (number-to-list x) (number-to-list x))) (+ x x)))
  :HINTS (("Goal" :use ((:instance mult-lists-definition-rule (f (number-to-list x)) (s (number-to-list x))) ltn-ntl-opposites-1) :hands-off (digitp lnp))))

(defthm LN-int-sub-equiv-1 (implies (and (intp x) (LN-int-equiv (number-to-list x) x) (LN-int-equiv (number-to-list (- x x)) (- x x))) (equal (list-to-number (sub-lists (number-to-list x) (number-to-list x))) (- x x)))
  :HINTS (("Goal" :use ((:instance mult-lists-definition-rule (f (number-to-list x)) (s (number-to-list x))) ltn-ntl-opposites-1) :hands-off (digitp lnp))))#|ACL2s-ToDo-Line|#



(defthm ltn-ntl-opposites-3 (implies (and (LNp x) (LN-int-equiv x (list-to-number x))) (equal (number-to-list (list-to-number x)) x))
  :HINTS (("Goal" :hands-off (digitp lnp))))

(defthm LN-int-equiv-test-3 (implies (intp x) (LN-int-equiv (number-to-list x) x))
  :HINTS (("Goal" :use (LN-int-equiv-test-1) :hands-off (digitp lnp))))














(acl2s-defaults :set testing-enabled nil)
;(set-defunc-function-contract-strictp nil)

(definec karatsuba2-mp-1 (f :PLN s :PLN) :PLN
  :function-contract-hints (("Goal" :use (PLN-k2-mp1) :hands-off (plnp digitp)))
  :ic (and (equal (len2 f) 2) (equal (len2 s) 2))
  (mult-lists (karatsuba2-a+b f) (karatsuba2-a+b s)))
(acl2s-defaults :set testing-enabled t)
(set-defunc-function-contract-strictp t)

(DEFTHM KARATSUBA2-MP-1-CONTRACT
         (IMPLIES (AND (FORCE (PLNP F))
                       (FORCE (PLNP S))
                       (FORCE (EQUAL (LEN2 F) 2))
                       (FORCE (EQUAL (LEN2 S) 2)))
                  (PLNP (KARATSUBA2-MP-1 F S)))
         :HINTS (("Goal" :use (PLN-k2-mp1 PLN-k2-mp1-1 PLN-k2-mp1-2 PLN-k2-mp1-3 PLN-k2-mp1-4) :hands-off (plnp digitp))))

(definec karatsuba2-2-p (f :PLN s :PLN) :PLN
  :function-contract-hints (("Goal" :hands-off (plnp digitp)))
  :ic (and (equal (len2 f) 2) (equal (len2 s) 2))
  (add-lists (karatsuba2-fp f s) (add-lists (list-pow-ten (add-lists (add-lists (karatsuba2-1 (sub-lists (second-half f) (first-half f)) (sub-lists (first-half s) (second-half s))) (karatsuba2-1 (first-half f) (first-half s))) (karatsuba2-1 (second-half f) (second-half s))) 1) (karatsuba2-bd f s))))

(definec karatsuba2-2 (f :LN s :LN) :LN
  :ic (and (or (and (<= (len2 f) 2) (PLNp f)) (and (<= (len2 f) 3) (NLNp f))) (or (and (<= (len2 s) 2) (PLNp s)) (and (<= (len2 s) 3) (NLNp s))))
  (cond
   ((and (equal (car f) '-) (equal (car s) '-)) (karatsuba2 (abs-list f) (abs-list s)))
   ((equal (car s) '-) (negate-list (karatsuba2 f (abs-list s))))
   ((equal (car f) '-) (negate-list (karatsuba2 (abs-list f) s)))
   ((or (equal (len2 f) 1) (equal (len2 s) 1)) (mult-lists f s))
   (t (add-lists (list-pow-ten (karatsuba2 (first-half f) (first-half s)) (len2 f)) (add-lists (list-pow-ten (add-lists (add-lists (karatsuba2 (sub-lists (second-half f) (first-half f)) (sub-lists (first-half s) (second-half s))) (karatsuba2 (first-half f) (first-half s))) (karatsuba2 (second-half f) (second-half s))) (/ (len2 f) 2)) (karatsuba2 (second-half f) (second-half s)))))))
#|
;;only works on things that multiply to < 999?
(definec karatsuba-only-list-stuff (f :LN s :LN) :LN
  :ic (and (<= (len2 f) 2) (<= (len2 s) 2) (implies (== (len2 f) 2) (> (list-to-number f) 0)) (implies (== (len2 s) 2) (> (list-to-number s) 0)))
  (cond
   ((or (equal (len2 f) 1) (equal (len2 s) 1)) (number-to-list (* (list-to-number f) (list-to-number s))))
   (t (app2 (karatsuba-only-list-stuff (first-half f) (first-half s)) (app2 (add-lists (add-lists (karatsuba-only-list-stuff (sub-lists (second-half f) (first-half f)) (sub-lists (first-half s) (second-half s))) (karatsuba-only-list-stuff (first-half f) (first-half s))) (karatsuba-only-list-stuff (second-half f) (second-half s))) (karatsuba-only-list-stuff (second-half f) (second-half s)))))))
|#
(defthm 
  final 
  (implies 
   (and (intp x) (intp y)) 
   (equal 
    (list-to-number (karatsuba2 (number-to-list x) (number-to-list x))) 
    (* x y))))