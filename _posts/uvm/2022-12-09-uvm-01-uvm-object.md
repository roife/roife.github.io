---
layout: "post"
title: "「UVM 学习」UVM Object"
subtitle: "UVM Object"
author: "roife"
date: 2022-12-09

tags: ["IC 验证@集成电路", "集成电路@Tags", "UVM@集成电路", "SystemVerilog@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 基类介绍

- `uvm_void`：所有 UVM 类的基类
- `uvm_root`：隐式的顶级组件，可以用 `uvm_top` 来访问
  - 如果父组件为 `null`（`super.new(name, null)`），那么这个组件会自动成为 `uvm_top` 的子组件
- `uvm_report_object`：提供了报告相关的接口
- `uvm_component`：在 `uvm_object` 和 `uvm_report_object` 的基础上提供了下面的功能
  - 组织层次结构
  - 定义不同的 phase
  - 打印报告
  - 将组件相关的事务记录存入数据库
  - 工厂模式相关方法（根据给定类型创建新对象）
- `uvm_transaction`：扩展了 `uvm_object`，提供了计时和记录的接口

# 常用宏

## `util` 宏

`util` 宏用于在工厂中注册 object 或者 component，以便在运行时创建对象。

- `uvm_object_utils(C)` 用于注册 `uvm_object` 或 `uvm_transaction`
- `uvm_component_utils(C)` 用于注册 `uvm_component`

`util` 宏将会被扩展为一系列 `*_begin` 和 `*_end` 方法。以 `uvm_object_utils` 为例：

```verilog
`define uvm_object_utils(T)
  `uvm_object_utils_begin(T)
  `uvm_object_utils_end

`define uvm_object_utils_begin(T)
   `m_uvm_object_registry_internal(T, T)    // Implement the functions "get_type()" and "get_object_type()"
   `m_uvm_object_create_func(T)             // Implement the function "create()"
   `m_uvm_get_type_name_func(T)             // Implement the function "get_type_name()"
   `uvm_field_utils_begin(T)				// Implement field automation macros

`define uvm_object_utils_end
     end
endfunction
```

其中，`*_begin` 又调用了四个宏：
- 实现 `get_type`
- 实现 `create`
- 实现 `get_type_name`
- 在 UVM 工厂中注册 UVM

```verilog
// Implement the functions "get_type()" and "get_object_type()"
`define m_uvm_object_registry_internal(T,S)
   typedef uvm_object_registry#(T,`"S`") type_id;
   static function type_id get_type();
     return type_id::get();
   endfunction
   virtual function uvm_object_wrapper get_object_type();
     return type_id::get();
   endfunction

// Implement the function "create()"
`define m_uvm_object_create_func(T)
   function uvm_object create (string name="");
     T tmp;
`ifdef UVM_OBJECT_DO_NOT_NEED_CONSTRUCTOR
     tmp = new();
     if (name!="")
       tmp.set_name(name);
`else
     if (name=="") tmp = new();
     else tmp = new(name);
`endif
     return tmp;
   endfunction

// Implement the function "get_type_name()"
`define m_uvm_get_type_name_func(T)
   const static string type_name = `"T`";
   virtual function string get_type_name ();
     return type_name;
   endfunction

// Implement field automation macros
`define uvm_field_utils_begin(T)
   function void __m_uvm_field_automation (uvm_object tmp_data__,
                                     int what__,
                                     string str__);
```

对于参数化的类则应该使用 `uvm_object_param_utils_*`。

在 UVM 中，如果要给 objects 创建对象，通常也推荐使用这里的 `create(name)` 方法。

## `field` 宏

`uvm_field_*` 相关的宏能对类的属性进行操作，并自动实现 `copy`、`compare`、`print` 之类的属性。

但是这些宏可能会影响仿真的性能，因此通常来说不推荐使用。一般更推荐使用 `do_*` 这样的回调钩子来实现。

```verilog
class ABC extends uvm_object;
    rand bit [15:0]     m_addr;
    rand bit [15:0]     m_data;

    `uvm_object_utils_begin(ABC)
        `uvm_field_int(m_addr, UVM_DEFAULT)
        `uvm_field_int(m_data, UVM_DEFAULT)
    `uvm_object_utils_end

    function new(string name = "ABC");
        super.new(name);
    endfunction
endclass
```

这些宏一般至少会接受两个参数：
- `name`：表示变量的名字
- `flag`：控制自动生成的实现的一些参数
  - 控制生成的方法
    - `UVM_ALL_ON`：使用所有操作
    - `UVM_DEFAULT`：等价于 `UVM_ALL_ON`
    - `UVM_NOCOPY`：实现 `copy` 时不拷贝该变量
    - `UVM_NOCOMPARE`：实现 `compare` 时不比较该变量
    - `UVM_NOPRINT`：实现 `print` 时不打印该变量  Do not print the given variable
    - `UVM_NOPACK`：实现 `pack` 时不打包该变量
    - `UVM_REFERENCE`：只对句柄进行操作，例如拷贝时不会实现深拷贝等
  - 控制变量类型：`UVM_BIN`、`UVM_DEC`、`UVM_HEX`、`UVM_OCT`、`UVM_STRING`、`UVM_TIME`

# `object` 相关操作

## `print`

使用 `field` 宏注册的变量可以通过自动生成的 `obj.print()` 方法进行打印。默认会打印成表格的形式，例如：

```verilog
`uvm_object_utils_begin(Object)
    `uvm_field_enum(e_bool, m_bool,	UVM_DEFAULT)
    `uvm_field_int (m_mode, UVM_DEFAULT)
    `uvm_field_sarray_int(m_data, UVM_DEFAULT)
    `uvm_field_queue_int(m_queue, UVM_DEFAULT)
    `uvm_field_string(m_name, UVM_DEFAULT)
`uvm_object_utils_end
```

```
-------------------------------------
Name       Type          Size  Value
-------------------------------------
obj        Object        -     @1899
  m_bool   e_bool        32    TRUE
  m_mode   integral      4     'hd
  m_data   sa(integral)  4     -
    [0]    integral      8     'h6c
    [1]    integral      8     'hf4
    [2]    integral      8     'he
    [3]    integral      8     'h58
  m_queue  da(integral)  3     -
    [0]    integral      16    'h3cb6
    [1]    integral      16    'h9ae9
    [2]    integral      16    'hd31d
  m_name   string        3     obj
-------------------------------------
```

### `do_print`

由于自动生成的宏仿真起来太慢了，所以一般会主动实现 `do_print` 这个回调方法。`print` 方法会自动调用 `do_print`。在 `do_print` 宏中可以控制需要打印哪些变量。

```verilog
class Object extends uvm_object;
    rand e_bool               m_bool;
    rand bit[3:0]             m_mode;
    string                    m_name;

    // 但是不使用 field 宏

    // Use "do_print" instead of the automation macro
    `uvm_object_utils(Object)

    virtual function void do_print(uvm_printer printer);
        super.do_print(printer);
        printer.print_string("m_bool", m_bool.name());
        printer.print_field_int("m_mode", m_mode, $bits(m_mode), UVM_HEX);
        printer.print_string("m_name", m_name);
    endfunction
endclass
```

此时和默认生成的 `print` 一样，会打印出表格形式的结果。

### `sprint`

`sprint` 类似于 `print`，但是不会直接打印，而是将要打印的内容作为字符串返回。

```verilog
`uvm_info($sformatf("Contents: %s", obj.sprint()), UVM_LOW)
```

### `convert2string`

重载 `convert2string` 方法可以通知打印的格式，但是需要在 tb 中手动调用。

```verilog
class Object extends uvm_object;
    rand byte                 m_data[4];
    string                    m_name;

    // ...

    // Use "do_print" instead of the automation macro
    `uvm_object_utils(Object)

    virtual function string convert2string();
        string contents = "";

        $sformat(contents, "%s m_name=%s", contents, m_name);
        foreach(m_data[i]) begin
            $sformat(contents, "%s m_data[%0d]=0x%0h", contents, i, m_data[i]);
        end
        return contents;
    endfunction
endclass
```

```verilog
// tb
`uvm_info(get_type_name(), $sformatf("%s", obj.convert2string()), UVM_LOW)
```

## `copy`

UVM 中默认生成的拷贝函数是**深拷贝**，用法形如 `target.copy(source)`。

### `do_copy`

```verilog
class Object extends uvm_object;
    rand e_bool              m_bool;
    rand byte                m_data[4];
    string                   m_name;
    rand Packet              m_pkt;

    // ...

    `uvm_object_utils(Object)

    // 需要转换成子类型后，才能访问对应的 fields
    virtual function void do_copy(uvm_object rhs);
        Object _obj;
        super.do_copy(rhs);
        $cast(_obj, rhs);

        m_bool    = _obj.m_bool;
        m_data    = _obj.m_data;
        m_name    = _obj.m_name;
        m_pkt.copy(_obj.m_pkt);
   endfunction
endclass
```

### `clone`

`clone` 和 `copy` 类似，但是 `clone` 会返回一个拷贝后的对象（`copy` 则是复制到已有的对象中）。

```verilog
$cast(obj2, obj1.clone())
```

## `compare`

`compare` 的用法类似，`obj1.compare(obj2)`，可以比较两个对象。

### `do_compare`

```verilog
virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
    bit res;
    Packet _pkt;

    $cast(_pkt, rhs);
    super.do_compare(_pkt, comparer);

    res = super.do_compare(_pkt, comparer) & m_addr == _pkt.m_addr;
    return res;
endfunction
```

## `pack`/`unpack`

- `pack`：将对象打包成 bits 数组
- `pack_bytes`：将对象打包成 bytes 数组
- `pack_ints`：将对象打包成 int 数组

对应还有 `unpack`、`unpack_bytes`、`unpack_ints`。

用法形如 `pkt.pack(bits)` 以及 `pkt.unpack(bits)`。

### `do_pack`/`do_unpack`

```verilog
virtual function void do_pack(uvm_packer packer);
    super.do_pack(packer);
    packer.pack_field_int(m_addr, $bits(m_addr));
    packer.pack_field_int(m_wdata, $bits(m_wdata));
endfunction

virtual function void do_unpack(uvm_packer packer);
    super.do_pack(packer);
    m_addr = packer.unpack_field_int($bits(m_addr));
    m_wdata = packer.unpack_field_int($bits(m_wdata));
endfunction
```
