(module
  (export "fib" (func $fib))
  (export "fib_iter" (func $fib_iter))
  ;; Definition of fib using the canonical definition with recursion
  (func $fib (param $n i32) (result i32)
    local.get $n
    i32.const 0
    i32.le_s
    if  ;; label = @1
      i32.const 0
      return
    end
    local.get $n
    i32.const 1
    i32.eq
    if  ;; label = @1
      i32.const 1
      return
    end
    local.get $n
    i32.const 2
    i32.sub
    call $fib
    local.get $n
    i32.const 1
    i32.sub
    call $fib
    i32.add
    return
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
    block  ;; label = @1
      loop  ;; label = @2
        local.get $i
        local.get $n
        i32.ge_s
        br_if 1 (;@1;)
        local.get $y
        local.get $x
        local.get $y
        i32.add
        local.set $y
        local.set $x
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br 0 (;@2;)
      end
    end
    local.get $x
    return
  )
)
