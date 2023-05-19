(module
   (export "example_br_table" (func $example_br_table))
   (func $example_br_table (param $n i32) (result i32)
      (block $case1
        (block $case2
          (block $case3
            local.get $n
            (br_table $case1 $case2 $case3)
          )
          i32.const 30
          return
        )
        i32.const 20
        return
      )
      i32.const 10
      return
   )
)
