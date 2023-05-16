(module
  (export "abs" (func $abs))
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
)
