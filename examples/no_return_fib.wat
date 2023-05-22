(module
  (type (;0;) (func (param i32)))
  (func (;0;) (type 0) (param i32)
    (local i32 i32 i32)
    i32.const 0
    local.set 1
    i32.const 1
    local.set 2
    i32.const 0
    local.set 3
    block  ;; label = @1
      loop  ;; label = @2
        local.get 3
        local.get 0
        i32.ge_s
        br_if 1 (;@1;)
        local.get 2
        local.get 1
        local.get 2
        i32.add
        local.set 2
        local.set 1
        local.get 3
        i32.const 1
        i32.add
        local.set 3
        br 0 (;@2;)
      end
    end)
  (export "no_return_fib" (func 0)))
