(module
  (memory 0 10)
  (global (mut i32) (i32.const 0))
  (table 3 funcref)
  (func
    i32.const 1298093134
    i32.const -57053579
    i32.add
    call_indirect (type 0)
    i32.const 871819597
    i32.const 95711456
    i32.const -591067814
    i32.add
    i32.add
    call_indirect (type 0)
  )
  (func
    i32.const 0
    f32.load offset=2
    drop
  )
  (func (param i32) (result i32)
    local.get 0
    i32.load
    i32.load
  )
  (func (param i32) (result i32)
    local.get 0
    i32.load
    i32.load
    i32.load
  )
  (func (param i32) (result i32)
    local.get 0
    i32.load
    i32.load
    i32.load
    i32.load
  )
  (func (param i32) (result i32)
    local.get 0
    i32.load
    i32.load
    i32.load
    i32.load
    i32.load
  )
  (func (param i32) (result i32)
    local.get 0
    i32.load
    i32.load
    i32.load
    i32.load
    i32.load
    i32.load
  )
  (type (;0;) (func))
  (type (;1;) (func (param i32 i32) (result i32)))
  (func $sum (;1;) (type 1) (param i32 i32) (result i32)
    (local i32)
    i32.const 0
    local.set 2
    block ;; label = @1
      local.get 1
      i32.eqz
      br_if 0 (;@1;)
      loop ;; label = @2
        local.get 0
        i32.load
        local.get 2
        i32.add
        local.set 2
        local.get 0
        i32.const 4
        i32.add
        local.set 0
        local.get 1
        i32.const -1
        i32.add
        local.tee 1
        br_if 0 (;@2;)
      end
    end
    local.get 2
  )
  (func (param i32) (result i32)
    local.get 0
    i32.load)
  (func (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.add
    i32.load)
  (func (param i32 i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.mul
    local.get 2
    i32.add
    i32.load)
  (func (param i32 i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.mul
    local.get 2
    i32.add
    i32.load)
;;  (func (param i32) (result i32)
;;    (i32.load (i32.shl (local.get 0) (i32.const 3))))
  (func (param i32)
    local.get 0
    call_indirect (type 0)
    i32.const 256256
    call_indirect (type 0)
  )
  (func
    (local i32)
    local.get 0
    call_indirect (type 0)
  )
  (func
    i32.const 0
    call_indirect (type 0)
    i32.const 1
    call_indirect (type 0)
    i32.const 100000
    call_indirect (type 0)
    i32.const -1
    call_indirect (type 0)
  )
  (func (;0;) (param f64 i64)
    (local f32 i32)
    block ;; label = @1
      i64.const -4616467772769793536
      i32.const 6095113
      br_table 0 (;@1;) 1 (;@0;) 1 (;@0;)
      drop
    end
  )
  (func (;0;) (type 0)
    i32.const 0
    i32.const 1000
    i32.store
    i32.const 0
    i32.load
    call_indirect (type 0)
  )
  (func (;0;) (type 0)
    i32.const 0
    i32.const -1000
    i32.store
    i32.const 0
    i32.load
    call_indirect (type 0)
  )
  (func (;0;) (type 0)
    i32.const -472723405
    global.set 0
    global.get 0
    call_indirect (type 0)
  )
)