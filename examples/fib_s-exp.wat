(module
  (export "fib" (func $fib))
  (export "fib_iter" (func $fib_iter))
  ;; Definition of fib using the canonical definition with recursion
  (func $fib (param $n i32) (result i32)
    (if (i32.le_s (local.get $n) (i32.const 0))
      (return (i32.const 0))
    )
    (if (i32.eq (local.get $n) (i32.const 1))
      (return (i32.const 1))
    )
    (return 
      (i32.add
        (call $fib
          (i32.sub
            (local.get $n)
            (i32.const 2)
          )
        )
        (call $fib
          (i32.sub
            (local.get $n)
            (i32.const 1)
          )
        )
      )
    )
  )

  ;; More efficient implementation of fib using loops
  (func $fib_iter (param $n i32) (result i32)
    (local $x i32)
    (local $y i32)
    (local $i i32)

    i32.const 0
    local.set $x

    i32.const 1
    local.set $y

    i32.const 0
    local.set $i

    ;; while i < n:
    ;;   x, y = y, x + y
    ;;   i = i + 1
    (block $break
      (loop $continue
        (br_if $break (i32.ge_s (local.get $i) (local.get $n)))

        local.get $y
        (i32.add (local.get $x) (local.get $y))
        local.set $y ;; y := x + y
        local.set $x ;; x := y (old value)
        (i32.add (local.get $i) (i32.const 1))
        local.set $i
        br $continue
      )
    )

    (return (local.get $x))
  )
)
