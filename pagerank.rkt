#lang racket

;; Assignment 1: Implementing PageRank
;;
;; PageRank is a popular graph algorithm used for information
;; retrieval and was first popularized as an algorithm powering
;; the Google search engine. Details of the PageRank algorithm will be
;; discussed in class. Here, you will implement several functions that
;; implement the PageRank algorithm in Racket.
;;
;; Hints: 
;; 
;; - For this assignment, you may assume that no graph will include
;; any "self-links" (pages that link to themselves) and that each page
;; will link to at least one other page.
;;
;; - you can use the code in `testing-facilities.rkt` to help generate
;; test input graphs for the project. The test suite was generated
;; using those functions.
;;
;; - You may want to define "helper functions" to break up complicated
;; function definitions.

(provide graph?
         pagerank?
         num-pages
         num-links
         get-backlinks
         mk-initial-pagerank
         step-pagerank
         iterate-pagerank-until
         rank-pages)

(define (flatten-list lst)
  (cond ((null? lst) '())
        ((pair? lst)
         (append (flatten-list (car lst)) (flatten-list (cdr lst))))
        (else (list lst))))

;; This program accepts graphs as input. Graphs are represented as a
;; list of links, where each link is a list `(,src ,dst) that signals
;; page src links to page dst.
;; (-> any? boolean?)
(define (graph? glst)
  (and (list? glst)
       (andmap
        (lambda (element)
          (match element
                 [`(,(? symbol? src) ,(? symbol? dst)) #t]
                 [else #f]))
        glst)))

;; Our implementation takes input graphs and turns them into
;; PageRanks. A PageRank is a Racket hash-map that maps pages (each 
;; represented as a Racket symbol) to their corresponding weights,
;; where those weights must sum to 1 (over the whole map).
;; A PageRank encodes a discrete probability distribution over pages.
;;
;; The test graphs for this assignment adhere to several constraints:
;; + There are no "terminal" nodes. All nodes link to at least one
;; other node.
;; + There are no "self-edges," i.e., there will never be an edge `(n0
;; n0).
;; + To maintain consistenty with the last two facts, each graph will
;; have at least two nodes.
;; + There will be no "repeat" edges. I.e., if `(n0 n1) appears once
;; in the graph, it will not appear a second time.
;;
;; (-> any? boolean?)
(define (pagerank? pr)
  (and (hash? pr)
       (andmap symbol? (hash-keys pr))
       (andmap rational? (hash-values pr))
       ;; All the values in the PageRank must sum to 1. I.e., the
       ;; PageRank forms a probability distribution.
       (= 1 (foldl + 0 (hash-values pr)))))

;; Takes some input graph and computes the number of pages in the
;; graph. For example, the graph '((n0 n1) (n1 n2)) has 3 pages, n0,
;; n1, and n2.
;;
;; (-> graph? nonnegative-integer?)
(define (num-pages graph)
  (length (remove-duplicates (flatten-list graph))))

;; Takes some input graph and computes the number of links emanating
;; from page. For example, (num-links '((n0 n1) (n1 n0) (n0 n2)) 'n0)
;; should return 2, as 'n0 links to 'n1 and 'n2.
;;
;; (-> graph? symbol? nonnegative-integer?)
(define (num-links graph page)
  (define (l count graph page)
    (if (null? graph)
        count
        (if (eq? (car (car graph)) page)
            (l (add1 count) (cdr graph) page)
            (l count (cdr graph) page))))
  (l 0 graph page))

;; Calculates a set of pages that link to page within graph. For
;; example, (get-backlinks '((n0 n1) (n1 n2) (n0 n2)) n2) should
;; return (set 'n0 'n1).
;;
;; (-> graph? symbol? (set/c symbol?))
(define (get-backlinks graph page)
  (define (gb? gbset graph page)
    (if (null? graph)
        (list->set gbset)
        (cond [(eq? (car(cdr (car graph))) page)
               (gb? (append (list (car (car graph))) gbset) (cdr graph) page)]
              [else (gb? gbset (cdr graph) page)])))
  (gb? '() graph page))

;; Generate an initial pagerank for the input graph g. The returned
;; PageRank must satisfy pagerank?, and each value of the hash must be
;; equal to (/ 1 N), where N is the number of pages in the given
;; graph.
;; (-> graph? pagerank?)
(define (mk-initial-pagerank graph)
  (define (inithash lst n)
    (map (lambda (x) (cons x n))
         lst))
  (make-immutable-hash (inithash (remove-duplicates (flatten-list graph)) (/ 1 (num-pages graph)))))
;(mk-initial-pagerank'((n2 n0) (n1 n4) (n4 n0) (n1 n3) (n2 n1) (n0 n1) (n3 n4) (n0 n4) (n4 n1) (n4 n2) (n1 n0)))

;; Perform one step of PageRank on the specified graph. Return a new
;; PageRank with updated values after running the PageRank
;; calculation. The next iteration's PageRank is calculated as
;;
;; NextPageRank(page-i) = (1 - d) / N + d * S
;;
;; Where:
;;  + d is a specified "dampening factor." in range [0,1]; e.g., 0.85
;;  + N is the number of pages in the graph
;;  + S is the sum of P(page-j) for all page-j.
;;  + P(page-j) is CurrentPageRank(page-j)/NumLinks(page-j)
;;  + NumLinks(page-j) is the number of outbound links of page-j
;;  (i.e., the number of pages to which page-j has links).
;;
;; (-> pagerank? rational? graph? pagerank?)
;(define (step-pagerank pr d graph)
(define (s d pr sum backlinks graph hashlst)
  (if (set-empty? backlinks)
      (append hashlst (list (+ (/ (- 1 d) (num-pages graph)) (* d sum))))
      (s d pr (+ sum (/ (hash-ref pr (set-first backlinks)) (num-links graph (set-first backlinks)))) (set-rest backlinks) graph hashlst)))
(define (newhashlst d pr prlst graph hashlst)
  (if (null? prlst)
      hashlst
      (newhashlst d pr (cdr prlst) graph (s d pr 0 (get-backlinks graph (car prlst)) graph hashlst))))
(define (setnewpairs lst1 lst2 )
  (map (lambda (i j) (cons i j)) lst1 lst2))

(define (step-pagerank pr d graph)  
  (make-immutable-hash (setnewpairs (hash-keys pr) (newhashlst d pr (hash-keys pr) graph '()))))

;(step-pagerank (step-pagerank r0 (/ 85 100) g0) (/ 85 100) g0)
;(get-backlinks g0 (car (hash-keys r0)))
;(num-links g0 'n4)
;; Iterate PageRank until the largest change in any page's rank is
;; smaller than a specified delta.
;;
;; (-> pagerank? rational? graph? rational? pagerank?)
(define (compare prlst1 prlst2 delta)
  (< (apply max (map (lambda (i j) (abs (- i j))) prlst1 prlst2)) delta))
         
(define (iterate-pagerank-until pr d graph delta)
  (if (equal? (compare (hash-values pr) (hash-values (step-pagerank pr d graph)) delta) #t)
      (step-pagerank pr d graph)
      (iterate-pagerank-until (step-pagerank pr d graph) d graph delta)))
           
;(iterate-pagerank-until r0 (/ 85 100) g0 (/ 1 10))
;(define s1 (step-pagerank r0 (/ 85 100) g0))
;(define s2 (step-pagerank s1 (/ 85 100) g0))
;(step-pagerank s2 (/ 85 100) g0)

;; Given a PageRank, returns the list of pages it contains in ranked
;; order (from least-popular to most-popular) as a list. You may
;; assume that the none of the pages in the pagerank have the same
;; value (i.e., there will be no ambiguity in ranking)
;;
;; (-> pagerank? (listof symbol?))

(define (sort-pages pr lst)
  (if (hash-empty? pr)
      lst
      (sort-pages (hash-remove pr (car (argmin cdr (hash->list pr)))) (append lst (list (car (argmin cdr (hash->list pr))))))))
(define (rank-pages pr)
  (sort-pages pr '()))