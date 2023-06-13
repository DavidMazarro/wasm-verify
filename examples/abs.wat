(module
  (export "abs" (func $abs))
  (export "abs_s_exp" (func $abs_s_exp))
  (func $abs (param $n i32) (result i32)
    local.get $n
    i32.const 0
    i32.ge_s
    if
      local.get $n
      return
    end
    local.get $n
    i32.const -1
    i32.mul
    return
  )
  (func $abs_s_exp (param $n i32) (result i32)
    (if (i32.ge_s (local.get $n) (i32.const 0))
      (then
        (return (local.get $n))
      )
    )
    (return (i32.mul (local.get $n) (i32.const -1)))
  )
)
