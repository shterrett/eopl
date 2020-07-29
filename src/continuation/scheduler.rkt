#lang racket

(require data/queue)

(struct scheduler
  (ready-queue
   [final-answer #:mutable]
   max-time-slice
   [time-remaining #:mutable]
   ))

(define initialize-scheduler!
  (λ (t)
     (scheduler (make-queue)
                'uninitialized
                t
                t)
     ))

(define place-on-ready-queue!
  (λ (sch th)
     (enqueue! (scheduler-ready-queue sch) th)))

(define run-next-thread
  (λ (sch)
    (if (queue-empty? (scheduler-ready-queue sch))
        (scheduler-final-answer sch)
        (let ((nt (dequeue! (scheduler-ready-queue sch))))
          (set-scheduler-time-remaining! sch (- (scheduler-time-remaining sch) 1))
          (nt)))))

(define set-final-answer!
  (λ (sch v)
     (set-scheduler-final-answer! sch v)))

(define time-expired?
  (λ (sch)
     (zero? (scheduler-time-remaining sch))))

(define decrement-timer!
  (λ (sch)
     (set-scheduler-time-remaining! sch (- (scheduler-time-remaining sch) 1))))

(module+ test
  (require rackunit)
  (let ((s (initialize-scheduler! 5)))
    (check-equal? (scheduler-max-time-slice s)
                  5
                  "initialize max time")
    (check-equal? (scheduler-time-remaining s)
                  5
                  "initialize time remaining"))
  (let ((s (initialize-scheduler! 5)))
    (place-on-ready-queue! s 'a)
    (place-on-ready-queue! s 'b)
    (check-equal? (queue->list (scheduler-ready-queue s))
                  '(a b)
                  "enqueues jobs"))
  (let ((s (initialize-scheduler! 1)))
    (check-equal? (time-expired? s)
                  #f
                  "time not expired")
    (decrement-timer! s)
    (check-equal? (time-expired? s)
                  #t
                  "now time expired"))
  (let* ((s (initialize-scheduler! 1))
        (p (mcons 'a 'b))
        (f (λ () (set-mcar! p 'c))))
    (place-on-ready-queue! s f)
    (run-next-thread s)
    (check-equal? p (mcons 'c 'b)))
)
