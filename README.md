# cs2800FinalProjectDraft
ACL2 Files for my CS2800 final

Both files need to be run in ACL2s, I used eclipse so I would recommend that.
Both files take a fairly long time to run(shouldn't be more than 10 minutes) and finish all of the proofs.

Karatsuba.lisp was essentially my scratch space for this project so its pretty unorganized and not everything will run. The overall goal in that file was to prove the equivalency of karatsuba multiplication, and the multiplication built into acl2s but I got super stuck and everything required like 6 defthms and 5 minutes of proving time to run in logic mode so I pivoted to proving some interesting properties about the list numbers data type I defined. 

PSFinalProject.lisp was what I pivoted to after getting stuck with the karatsuba stuff. It is much more organized and everything in that file should run successfully, but it will take quite a bit of time to do so. In this file I have all the neccessary data definitions to be able to represent any integer as what I called a list number which is a true list of base ten digits with the symbol '- on front if the number is negative. I also defined functions to perform multiplication, addition, subtraction, and raising the list number to a power of ten, and proved their equivalency to the built in version of these functions. In addition to try and prove that my failures with karatsuba weren't for lack of effort of understanding I defined an additional recursive function that sums all the digits in a list number, and I proved a theorem forcing induction on true lists in order to prove that (tlp x) is a valid induction sceme for these list numbers.
