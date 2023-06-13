(module
   (export "cfg_example" (func $cfg_example))
   (func $cfg_example (param $n i32) (result i32)
      local.get $n
      i32.const 5
      i32.sub
      i32.const 0
      i32.ge_s
      if (result i32)
        local.get $n
        i32.const 2
        i32.mul
      else
        local.get $n
        i32.const 3
        i32.mul
      end
      i32.const 1
      i32.add
      return
   )
)
