(module
  (export "fib" (func $fib))
  (export "fib_iter" (func $fib_iter))
  ;; Definition of fib using the mathematical definition with recursion
  (func $fib (param $n i32) (result i32)
    local.get $n
    i32.const 0
    i32.le_s 
    if ;; n <= 0?
      i32.const 0
      return
    end
    local.get $n
    i32.const 1
    i32.eq
    if ;; n == 1?
      i32.const 1
      return
    end
    local.get $n
    i32.const 2
    i32.sub
    call $fib ;; fib(n - 2)
    local.get $n
    i32.const 1
    i32.sub
    call $fib ;; fib(n - 1)
    i32.add
    return ;; fib(n - 2) + fib(n - 1)
  )
  ;; More efficient implementation of fib using a loop
  (func $fib_iter (param $n i32) (result i32)
    (local $x i32)
    (local $y i32)
    (local $i i32)
    i32.const 0
    local.set $x ;; x := 0
    i32.const 1
    local.set $y ;; y := 1
    i32.const 0
    local.set $i ;; i := 0
    ;; while i < n:
    ;;   x, y = y, x + y
    ;;   i = i + 1
    block  ;; label = @1
      loop  ;; label = @2
        local.get $i
        local.get $n
        i32.ge_s
        br_if 1 ;; i >= n? @1  
        local.get $y
        local.get $x
        local.get $y
        i32.add
        local.set $y ;; y := x + y
        local.set $x ;; x := y (old value)
        local.get $i
        i32.const 1
        i32.add
        local.set $i ;; i := i + 1
        br 0 ;; @2
      end
    end
    local.get $x
    return
  )
)
