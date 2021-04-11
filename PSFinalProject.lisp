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
;;Overall data definitions

;;A digit is simply one of the digits in base 10 numbers
(defdata digit (oneof 0 1 2 3 4 5 6 7 8 9))

;;A lod is a list of digits
(defdata lod (listof digit))

;;A PLN is a positive list number, or a non empty list of digits representing a natural number
(defdata PLN (cons digit lod))

;;A NLN is a negative list number or the - sign cons-ed onto the from of a positive list number to indicate it is now negative
(defdata NLN (cons '- PLN))

;;A LN is a list number which is either a PLN or NLN and capable of representing any integer
(defdata LN (oneof PLN NLN))

;;--------------------DATA DEF EXAMPLE TEST----------------;;

(test? (digitp 1))

(test? (lodp '()))

(test? (lodp '(1 2 3 4)))

(test? (PLNp '(1 2 3 4)))

(test? (NLNp '(- 1 2 3 4)))

(test? (LNp '(1 2 3 4)))

(test? (LNp '(- 1 2 3 4)))

(test? (implies (PLNp x) (and (lodp x) (digitp (car x)))))

(test? (implies (NLNp x) (and (lodp (cdr x)) (equal '- (car x)))))

(test? (implies (LNp x) (or (PLNp x) (NLNp x))))

;;--------------------BASIC FUNCTIONS------------------------;;

(definec len2 (x :tl) :nat
  (if (endp x)
      0
    (+ 1 (len2 (rest x)))))

(definec app2 (a :tl b :tl) :tl
  (if (endp a)
      b
    (cons (first a) (app2 (rest a) b))))

;;-------------------First-and-last-number------------------;;

;;Gets the last digit in a number as a PLN
(definec last-n (n :int) :PLN
  (list (mod (abs n) 10)))

;;gets all but the last digit in a number stays as a natural number
(definec first-n (n :nat) :nat
  (/ (- n (mod n 10)) 10))

(test? (equal (last-n 123) '(3)))

(test? (equal (first-n 123) 12))

;;-------------------NUMBER-TO-LIST-------------------------;;

;;Proves that PLNs are true lists
(defthm PLN-TL (implies (PLNp x) (tlp x)))

;;proves that appending two lists of digits gives you a list of digits
(defthm LOD-app2 (implies (and (lodp x) (lodp y)) (lodp (app2 x y))))

;;extends the above lemma to PLN's
(defthm PLN-app2 (implies (and (PLNp x) (PLNp y)) (PLNp (app2 x y))))

;;Give definitions a little more time to process
(Set-defunc-timeout 120)

;;I don't understand this but it dodges some preprocess error thing
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

;;The number to list function that only deals with natural numbers and converts them PLN's this lets use use the lemmas about app2
(definec number-to-list-p (n :nat) :PLN
  :function-contract-hints (("Goal" :HANDS-OFF (LAST-N APP2)))
  (cond
   ((< (/ n 10) 1) (last-n n))
   (t (app2 (number-to-list-p (first-n n)) (last-n n)))))

;;A wrapper for converting numbers to lists that deals with negative numbers and makes them positive because PLNs are easier to work with
(definec number-to-list (n :int) :LN
  (cond
   ((< n 0) (cons '- (number-to-list-p (- n))))
   (t (number-to-list-p n))))

(test? (equal (number-to-list 123) '(1 2 3)))

(test? (equal (number-to-list -123) '(- 1 2 3)))

;;--------------------------------LAST-L, RDC, and FIRST-L--------------------------------;;

;;Gets the last digit in a PLN and returns it as a nat
(definec last-l (l :PLN) :nat
  :ic (consp l)
  (if (PLNp (cdr l)) (last-l (cdr l)) (car l)))

;;gets all but the last element of a PLN
(definec RDC (l :PLN) :lod
  (cond
   ((endp (cdr l)) nil)
   (t (cons (car l) (RDC (cdr l))))))

;;Gets all but the last elements of a PLN assuming the PLN has more than two elements so the result can't be empty
(definec first-l (l :PLN) :PLN
  :ic (consp (cdr l))
  (rdc l))

(test? (equal (last-l '(1 2 3)) 3))

(test? (equal (RDC '(1)) '()))

(test? (equal (first-l '(1 2 3)) '(1 2)))

(test? (implies (and (PLNP x) (>= (len2 x) 2)) (equal (app2 (first-l x) (cons (last-l x) '())) x)))

;;------------------------------LIST-TO-NUMBER---------------------------------------------;;

;;List-to-number with PLNs 
(definec list-to-number-p (l :PLN) :nat
  :function-contract-hints (("Goal" :HANDS-OFF (rdc)))
  (cond
   ((endp (cdr l)) (last-l l))
   (t (+ (last-l l) (* 10 (list-to-number-p (rdc l)))))))

;;A wrapper for converting lists to numbers, deals with the NLN case so we can only work with PLNs when we are doing recursive calls
(definec list-to-number (l :LN) :int
  (cond
   ((NLNp l) (- (list-to-number-p (cdr l))))
   (t (list-to-number-p l))))

;;tests that converting to a list then back to a number creates the same number
(test? (implies (intp x) (equal (list-to-number (number-to-list x)) x)))

;;----------------------------ABS-LIST, and NEGATE-LIST-------------------------------------;;

;;Takes the absolute value of a list 
(definec abs-list (l :LN) :PLN
  (cond
   ((equal (car l) '-) (cdr l))
   (t l)))

;;Negates the value of a list
(definec negate-list (l :LN) :LN
  (number-to-list (* -1 (list-to-number l))))

(test? (equal (abs-list '(- 1 2 3 4)) '(1 2 3 4)))

(test? (equal (negate-list '(- 1 2 3 4)) '(1 2 3 4)))

(test? (equal (negate-list '(1 2 3 4)) '(- 1 2 3 4)))

;;------------------------------ADD-LISTS--------------------------------------------------;;

;;Two lemmas to help with the definition of add-lists

;;A lemma proving that the sum of two list numbers converted to numbers is always integer
(defthm int-add-list (implies (and (LNp x) (LNp y)) (intp (binary-+ (list-to-number f) (list-to-number s)))))

;;Extends the above lemma to prove that the body of add-lists always produces a list number as its result
(defthm LN-add-list (implies (AND (FORCE (LNP F)) (FORCE (LNP S))) (LNp (number-to-list (binary-+ (list-to-number f) (list-to-number s))))))

;;adds two lists to each other then converts it back to a list
(definec add-lists (f :LN s :LN) :LN
  :function-contract-hints (("Goal" :USE (LN-add-list add-lists) :hands-off (lnp digitp)) ("Goal'" :expand ((add-lists f s))))
  (number-to-list (binary-+ (list-to-number f) (list-to-number s))))

(test? (equal (add-lists '(1 2) '(3 4)) '(4 6)))

(test? (equal (add-lists '(4 5) '(3 4)) '(7 9)))

;;------------------------------SUB-LISTS----------------------------------------------;;

;;Two lemmas to help with the definition of sub-lists

;;A lemma proving that the difference of two list numbers converted to numbers is always integer
(defthm int-sub-list (implies (and (LNp x) (LNp y)) (intp (- (list-to-number f) (list-to-number s)))))

;;Extends the above lemma to prove that the body of sub-lists always produces a list number as its result
(defthm LN-sub-list (implies (AND (FORCE (LNP F)) (FORCE (LNP S))) (LNp (number-to-list (- (list-to-number f) (list-to-number s))))))

;;subtracts two lists from each other then converts them back to lists
(definec sub-lists (f :LN s :LN) :LN
  :function-contract-hints (("Goal" :USE (LN-sub-list sub-lists) :hands-off (lnp digitp)) ("Goal'" :expand ((sub-lists f s))))
  (number-to-list (- (list-to-number f) (list-to-number s))))

(test? (equal (sub-lists '(1 2) '(3 4)) '(- 2 2)))

(test? (equal (sub-lists '(4 5) '(3 4)) '(1 1)))

;;---------------------------LIST-POW-TEN-------------------------------------------;;

;;Proves that the body of list-pow-ten always outputs a list number, helps with the function contract of list-pow-ten
(defthm LN-expt-list (implies (AND (FORCE (LNP l)) (FORCE (NATP x))) (LNp (number-to-list (* (list-to-number l) (expt 10 x))))))

;;raises the list to the given power
(definec list-pow-ten (l :LN x :nat) :LN
  :function-contract-hints (("Goal" :USE (LN-expt-list list-pow-ten) :hands-off (lnp digitp binary-*))) ;("Goal'" :expand ((sub-lists f s))))
  (number-to-list (* (list-to-number l) (expt 10 x))))

(test? (equal (list-pow-ten '(4 5) 2) '(4 5 0 0)))

;;-------------------------------MULT-LISTS--------------------------------------;;

;;Two lemmas to help with the definition of mult-lists

;;A lemma proving that the product of two list numbers converted to numbers is always integer
(defthm int-mult-list (implies (and (LNp x) (LNp y)) (intp (* (list-to-number f) (list-to-number s)))))

;;Extends the above lemma to prove that the body of mult-lists always produces a list number as its result
(defthm LN-mult-list (implies (AND (FORCE (LNP F)) (FORCE (LNP S))) (LNp (number-to-list (* (list-to-number f) (list-to-number s))))))

;;Multiplies the value of two lists
(definec mult-lists (f :LN s :LN) :LN
  :function-contract-hints (("Goal" :USE (LN-mult-list mult-lists) :hands-off (lnp digitp)))
  (number-to-list (* (list-to-number f) (list-to-number s))))

(test? (equal (mult-lists '(1 2) '(3 4)) '(4 0 8)))

(test? (equal (mult-lists '(4 5) '(3 4)) '(1 5 3 0)))

;;--------------------------------FURTHER DEFINITIONS AND LEMMAS------------------;;

;;Checks that a list number is equivalent to an integer
(definec LN-int-equiv (x :LN y :int) :boolean
  (and (equal (list-to-number x) y) (equal x (number-to-list y))))

(test? (LN-int-equiv '(1 2 3) 123))
(test? (not (LN-int-equiv '(1 2 3) 321)))

;;Provided with the fact that a list number is equivalent to an integer then we can prove that the integer converted to 
;;a list is equivalent to the list converted to a number
(defthm LN-int-equiv-test-1 (implies (and (LNp x) (intp y) (LN-int-equiv x y)) (LN-int-equiv (number-to-list y) (list-to-number x)))
  :HINTS (("Goal" :hands-off (digitp lnp))))

;;Provided with the fact that x converted to a list is equivalent to x then we can prove that list to number and number to list are inverse
;;operations, and converting a number to a list then back will yeild the same number
(defthm ltn-ntl-opposites-1 (implies (and (intp x) (LN-int-equiv (number-to-list x) x)) (equal (list-to-number (number-to-list x)) x))
  :HINTS (("Goal" :hands-off (digitp lnp))))


#|(defthm LN-int-equiv-test-2 (implies (and (LNp x) (intp y) (LN-int-equiv x y)) (LN-int-equiv (number-to-list (list-to-number x)) (list-to-number (number-to-list y))))
  :HINTS (("Goal" :hands-off (digitp lnp))))|#

;;Further prove that list-to-number and number-to-list are inverses by using two different integer variables
(defthm ltn-ntl-opposites-2 (implies (and (intp x) (intp y) (LN-int-equiv (number-to-list x) y)) (equal (list-to-number (number-to-list x)) y))
  :HINTS (("Goal" :hands-off (digitp lnp))))

;;These two work but make annoying rewrite rules and HIDE wasn't working for some reason
#|
(defthm ltn-ntl-opposites-3 (implies (and (intp x) (intp y) (LN-int-equiv (number-to-list x) y)) (equal (number-to-list x) (number-to-list y)))
  :HINTS (("Goal" :hands-off (digitp lnp))))

(defthm ltn-ntl-opposites-4 (implies (and (intp x) (intp y) (equal (identity x) y)) (equal (number-to-list x) (number-to-list y)))
  :HINTS (("Goal" :hands-off (digitp lnp))))|#

;;Proves that list number multiplication is equivalent to normal multiplication on integer
(defthm LN-int-mult-equiv (implies (and (intp x) (LN-int-equiv (number-to-list x) x) (LN-int-equiv (number-to-list (* x x)) (* x x))) (equal (list-to-number (mult-lists (number-to-list x) (number-to-list x))) (* x x)))
  :HINTS (("Goal" :use ((:instance mult-lists-definition-rule (f (number-to-list x)) (s (number-to-list x))) ltn-ntl-opposites-1) :hands-off (digitp lnp binary-*))))

;;Proves that list number addition is equivalent to normal addition on integers
(defthm LN-int-add-equiv (implies (and (intp x) (LN-int-equiv (number-to-list x) x) (LN-int-equiv (number-to-list (+ x x)) (+ x x))) (equal (list-to-number (add-lists (number-to-list x) (number-to-list x))) (+ x x)))
  :HINTS (("Goal" :use ((:instance mult-lists-definition-rule (f (number-to-list x)) (s (number-to-list x))) ltn-ntl-opposites-1) :hands-off (digitp lnp))))

;;Proves that list number subtraction is equivalent to normal subtraction on integers
(defthm LN-int-sub-equiv (implies (and (intp x) (LN-int-equiv (number-to-list x) x) (LN-int-equiv (number-to-list (- x x)) (- x x))) (equal (list-to-number (sub-lists (number-to-list x) (number-to-list x))) (- x x)))
  :HINTS (("Goal" :use ((:instance mult-lists-definition-rule (f (number-to-list x)) (s (number-to-list x))) ltn-ntl-opposites-1) :hands-off (digitp lnp))))

;;Proves that raising a list to a power of ten is equivalent to raising an integer to a power of ten
;;NOTE: This actually just takes 140 seconds to prove, it works eventually though
(defthm LN-int-expt-equiv (implies (and (intp x) (natp y) (LN-int-equiv (number-to-list x) x) (LN-int-equiv (number-to-list (* x (expt 10 y))) (* x (expt 10 y)))) (equal (list-to-number (list-pow-ten (number-to-list x) y)) (* x (expt 10 y))))
  :HINTS (("Goal" :use ((:instance list-pow-ten-definition-rule (l (number-to-list x)) (x y)) ltn-ntl-opposites-1) :hands-off (digitp lnp binary-*))))

;;uses a recursive function to prove that PLN's can work like true lists in their recursive structure, and by extension induction scheme
(definec sum-digits-p (x :PLN) :nat 
  (cond
   ((endp (cdr x)) (car x))
   (t (+ (car x) (sum-digits-p (cdr x))))))

;;A wrapper for sum digits so it can handle NLNs
(definec sum-digits (x :LN) :nat 
  (if (NLNp x) (sum-digits-p (cdr x)) (sum-digits-p x)))

(test? (equal (sum-digits '(1 2 3)) 6))

(test? (equal (sum-digits '(- 1 2 3)) 6))

(set-gag-mode nil)

;;We can prove a basic property about our recursive function using forced recursion on true lists because list numbers are true lists
(defthm recursive-PLN-functions (implies (and (PLNp x) (>= (len2 x) 2)) (equal (sum-digits x) (+ (car x) (sum-digits (cdr x)))))
  :hints (("Goal" :induct (tlp x) :hands-off (digitp))))#|ACL2s-ToDo-Line|#

