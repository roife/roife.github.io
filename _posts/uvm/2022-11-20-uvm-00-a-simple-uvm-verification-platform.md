---
layout: "post"
title: "「UVM 学习」UVM 验证平台介绍"
subtitle: "一个简单的 UVM 验证平台介绍"
author: "roife"
date: 2022-11-20

tags: ["IC 验证@集成电路", "集成电路@Tags", "UVM@集成电路", "SystemVerilog@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 验证平台的组成

一个验证平台应该包含下面几个部分：
- DUT：（Design Under Test）待测试的 RTL 组件
- TB：（Testbench）测试环境
  + Driver：驱动 DUT 与 reference model 的输入
  + Scoreboard：检查 DUT 的输出与预期行为是否一致
  + Monitor：收集 DUT 的输出，并传递给 scoreboard
  + Reference model：参考模型，可以给出预期行为

此外，UVM 还引入了 agent 与 sequence 的概念。

![UVM 验证平台](/img/in-post/post-uvm/uvm-verification-platform.png){:height="400px" width="400px"}

## UVM 的类层次

![UVM Class Hierarchy](/img/in-post/post-uvm/uvm-class-hierarchy.png){:height="500px" width="500px"}

- `uvm_object`：一般是测试用例的配置，可以拷贝、比较和打印的对象
- `uvm_component`：各种组件的父类

# 仅有 driver 的简单验证平台

UVM 中的 driver 需要继承 `uvm_driver`。

```verilog
// my_driver.sv
class my_driver extends uvm_driver;
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    extern virtual task main_phase(uvm_phase phase);
endclass

task my_driver::main_phase(uvm_phase phase);
    // 编写测试代码
    // 这个文件接下来会被直接 include 进 top_tb
    // 因此可以直接用 top_tb.dut 访问 DUT，但是一般更推荐用虚接口
endtask
```

- 所有继承自 `uvm_component` 的类的 `new` 方法都有两个参数，第一个是类名 `name`，第二个是父类 `parent`
- UVM 中运行验证的部分都在 phase 中完成，命名为 `xxx_phase`，其带有一个 `uvm_phase` 类型的参数 `phase`

一个完整的验证平台如下：

```verilog
`timescale 1ns/1ps`
`include "uvm_macros.svh"

import uvm_pkg::*;

`include "my_driver.sv"

module top_tb;
    // 定义信号
    dut my_dut(/* 信号 */);

    initial begin // 测试平台
        my_driver drv;
        drv = new ("drv", null);
        drv.main_phase(null);
        $finish();
    end

    initial begin // 时钟信号
        clk = 0;
        forever #100 clk = ~clk;
    end

    initial begin // 初始化
        rst = 1'b0;
        #1000;
        rst = 1'b1;
    end
endmodule
```

## `uvm_info`

UVM 中的 `uvm_info` 用于打印信息，其格式为 `uvm_info(tag, message, verbosity)`。
- `tag`：信息的标签，用于过滤信息
- `message`：信息内容
- `verbosity`：信息的冗余级别，用于过滤信息，可以是 `UVM_LOW`（更关键）、`UVM_MEDIUM` 或 `UVM_HIGH`（默认不显示）

此外，还有 `uvm_warning`、`uvm_error`、`uvm_fatal` 等方法，用于打印警告、错误、致命错误。

## Factory 机制

Factory 机制能自动创建对象，并自动调用类中的函数和任务。

```verilog
// my_driver.sv
class my_driver extends uvm_driver;
    `uvm_component_utils(my_driver) // 注册当前类

    // ...
endclass
```

调用宏 `uvm_component_utils` 之后，会将类名 `my_driver` 注册到 Factory 中，这样就可以让 UVM 自动创建类的实例了。所有派生自 `uvm_component` 的类都应该使用 `uvm_component_utils` 宏注册。

使用 factory 后，需要对 tb 进行一些修改：

```verilog
// top_tb.sv

module top_tb;
    // ...
    initial begin
        run_test("my_driver");
    end
    // ...
endmodule
```

`run_test` 语句会自动调用 factory 创建类的实例，并且实例化会自动触发 `main_phase` 任务。此时 `my_driver` 对应的实例并不在 `top_tb` 中，而是由 UVM 进行管理。

## Objection 机制

但是在上面这个例子中，虽然调用了 `main_phase` 方法，但是并没有实际运行测试。这是因为有 Objection 机制的存在。

UVM 中通过 objection 机制来控制验证平台的关闭。在每个 phase 中，UVM 会检查是否 `raise_objection`，如果没有则自动关闭验证平台；否则，等待 `drop_objection`。并且 `raise_objection` 必须出现在第一个消耗时间的语句之前。

```verilog
// my_driver.sv

// my_driver 定义

task my_driver::main_phase(uvm_phase phase);
    phase.raise_objection(this); // 阻止验证平台关闭
    // ...
    phase.drop_objection(this); // 允许验证平台关闭
endtask
```

`drop_objection` 类似于 `$finish()`。

## config_db 机制

使用 factory 让 UVM 来托管验证后，就无法直接访问验证中的信号了，这让虚接口之类的特性用起来比较麻烦。这时就需要使用 `config_db` 机制

UVM 中的 config_db 机制用于配置对象，可以通过 `uvm_config_db` 类来访问。用 `set` 来设置配置，用 `get` 获取配置。

```verilog
// top_tb.sv
module top_tb;
    my_if input_if(clk, rst_n);

    initial begin
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top", "vif", input_if);
        run_test("my_driver");
    end
    
    // ...
endmodule
```

```verilog
// my_driver.sv
class my_driver extends uvm_driver;
    virtual my_if vif;
    
    virtual function build_phase(uvm_phase phase);
        super.build_phase(phase);
        uvm_config_db#(virtual my_if)::get(this, "", "vif", vif);
    endfunction
    
    // ...
endclass
```

这里的 `build_phase` 也是 UVM 内建的 phase，会自动在 `new` 之后、`main_phase` 之前调用。注意在 `build_phase` 中需要调用 `super.build_phase`。`build_phase` 与 `main_phase` 的区别是前者是一个 function，不能消耗时间；后者是一个 task，可以消耗时间。

`config_db` 的 `get` 与 `set` 分别有四个参数，格式如下：

```verilog
uvm_config_db#(type)::[get/set](scope, inst_name, field_name, var);
```

- `scope`：配置的作用域，如果为 `null` 则表示全局作用域（和第二个参数一起组成完整路径）
- `inst_name`：实例名，即在作用域下的实例名称
- `field_name`：标识，可以是任意字符串，但是 `set` 和它对应接收的 `get` 必须一致
- `var`：`set` 时为要设置的值，`get` 时将值保存到哪个变量上

# 为验证平台加入组件

## transaction

验证平台中的不同组件之间通过 transaction 传递信息。transaction 是一个类，用于描述一个数据包。在不同的验证平台中，transaction 的定义可能不同。

```verilog
// my_transaction.sv
class my_transaction extends uvm_sequence_item;
    rand bit [7:0] data;
    
    function new(string name = "my_transaction");
        super.new(name);
    endfunction
    
    `uvm_object_utils(my_transaction)
endclass
```

这里有几个需要注意的地方：
- `uvm_sequence_item` 是 transaction 的基类
- 这里用 `uvm_object_utils` 宏来注册 transaction；这是因为 transaction 的生命周期不会贯穿整个验证平台，因此需要继承自 `uvm_object`（即 `uvm_sequence_item` 的父类），而不是 `uvm_component`

定义完 transaction 之后，就可以在 driver 中使用了。

```verilog
// my_driver.sv
task my_driver::main_phase(uvm_phase phase);
    phase.raise_objection(this);
    
    my_transaction tr;
    tr = new("tr");
    tr.randomize();
    
    // 用 transaction 驱动 vif
    // ...
    
    phase.drop_objection(this);
endtask
```

## env

假设已经创建好了 reference model、scoreboard 等组件，需要让验证平台对其实例化。但是由于 driver 是由 `run_test` 启动了，和 `top_tb` 已经没有关系了，因此无法直接访问到这些组件。

因此一般会创建一个 env 来表示验证平台中的环境，并**连接各个组件**；在 `run_test` 不再启动 `my_driver`，而是启动这个环境，由环境创建 driver、monitor 等部分，再进行测试。env 也是一个类，继承自 `uvm_env`。

```verilog
// my_env.sv
class my_env extends uvm_env;
    my_driver driver;
    // ...
    
    function new(string name = "my_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        driver = my_driver::type_id::create("drv", this);
    endfunction
    
    `uvm_component_utils(my_env)
endclass
```

此处使用了 `type_name::type_id::create` 的方法对 `my_driver` 进行了实例化。在 UVM 中，只有在 factory 中注册的类才能使用这种方法进行实例化。

### 组件树

实例化时传递了两个参数，分别对应 `my_driver::new(string name, uvm_component parent)` 中的两个参数。其中，第二个参数可以指定组件的父组件（这里是 `this`），这样可以构造出一棵组件树（在 `run_test` 中也会自动创建一样的一棵组件树，创建的实例本身是树根）。

树根的名字固定为 `uvm_test_top`，即此处 `uvm_env` 实例化是给的名字是 `uvm_test_top` 而非 `my_env`。对应的，`config_db` 中 `set` 传参时也需要把第二个参数改成 `uvm_test_top.drv`。

目前整个验证平台存在两个 `build_phase`，分别是 `my_env` 和 `drv`，二者是父子关系，UVM 会默认先执行父组件的 `build_phase`，再执行子组件的 `build_phase`。

## monitor

Driver 可以将 transaction 传递给 DUT，而 monitor 则可以将 DUT 的输出转换为 transaction，从而可以和 reference model 进行比较。

```verilog
// my_monitor.sv
class my_monitor extends uvm_monitor;
    virtual my_if vif;
    
    `uvm_component_utils(my_monitor) // 注册
    
    function new(string name = "my_monitor", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        uvm_config_db#(virtual my_if)::get(this, "", "vif", vif
    endfunction
    
    virtual task main_phase(uvm_phase phase);
        my_transaction tr;
        phase.raise_objection(this);
        
        forever begin
            tr = new("tr");
            // 从 vif 中获取 transaction
            // ...
        end
        
        phase.drop_objection(this);
    endtask
endclass
```

所有的 monitor 都应该派生自 `uvm_monitor`。并且由于 monitor 在整个验证过程中都会存在，因此是一个 component，需要在 `build_phase` 中获取 `vif`。

## agent

一个验证平台上 driver 和 monitor 的代码往往高度相似，因为他们一般是处理同一个协议的，因此二者可以封装在一起，即封装成一个 agent。

```verilog
// my_agent.sv
class my_agent extends uvm_agent;
    my_driver driver;
    my_monitor monitor;

    `uvm_component_utils(my_agent)

    function new(string name = "my_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (is_active) begin
            driver = my_driver::type_id::create("drv", this);
        end
        monitor = my_monitor::type_id::create("mon", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
    endfunction
endclass
```

类似的，agent 也是一个 component。

`is_active` 是 `UVM_AGENT` 中的一个成员变量：

```verilog
typedef enum bit {
    UVM_ACTIVE = 0,
    UVM_PASSIVE
} uvm_active_passive_enum;

uvm_active_passive_enum is_active = UVM_ACTIVE;
```

在这里，当 `is_active` 为 `UVM_ACTIVE` 时为 active agent，此时需要同时进行驱动和监视；反之，是需要收集数据时，可以使用 `UVM_PASSIVE`。

使用 agent 进行封装后，在 env 中可以直接使用 agent，而不需要再使用 driver 和 monitor。

```verilog
i_agt = my_agent::type_id::create("i_agt", this);
o_agt = my_agent::type_id::create("o_agt", this);
i_agt.is_active = UVM_ACTIVE;
o_agt.is_active = UVM_PASSIVE;
```

此时的组件树变成了三层：
- `uvm_test_top`（`my_env`）
  - `i_agt`
    - `drv`
    - `mon`
  - `o_agt`
    - `mon`

UVM 要求组件树必须在 `build_phase` 结束前构建完成，否则会报错（当然也可以在 `new` 中完成，因为 `new` 在 `build_phase` 前进行，当然，此时不能先赋值 `is_active` 再调用 `build_phase`，需要用 `config_db`）。

## reference_model

reference model 用于对 DUT 的输出进行比较，从而判断 DUT 是否正确。

```verilog
// my_model.sv
class my_model extends uvm_component;
    uvm_blocking_get_port #(my_transaction) port;
    uvm_analysis_port #(my_transaction) ap;

    `uvm_component_utils(my_model)

    function new(string name = "my_model", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        port = new("port", this);
        ap = new("ap", this);
    endfunction

    virtual task main_phase(uvm_phase phase);
        phase.raise_objection(this);

        super.main_phase(phase);

        my_transaction tr;
        my_transaction new_tr;

        forever begin
            port.get(tr);
            // ...
            ap.write(new_tr);
        end

        phase.drop_objection(this);
    endtask
endclass
```

### 连接端口与 FIFO 队列

此处，`uvm_analysis_port` 用于发送数据的端口，其中 `#()` 内的是数据的类型，通过 `ap.write(obj)` 来发送数据；`uvm_blocking_get_port` 用于接收数据的端口，通过 `port.get(obj)` 得到数据。

不同的组件都通过这样的端口通信，因此需要在 `my_monitor` 等组件中添加这样的端口。由于前面将 monitor 和 driver 封装到了 agent 中，因此还要在 agent 中添加这样的端口。但是在 agent 中不需要实例化了，因为 agent 是一个抽象的封装，所以可以直接在 `connect_phase` 中将 `my_monitor` 的端口对象赋值给 agent 的句柄。

```verilog
// my_agent.sv
function void my_agent::connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    ap = mon.ap;
endfunction
```

定义好端口后，需要将两个组件的对应端口连接起来。例如此处需要将 `my_monitor` 的输出（即给 DUT 的输入）和 `my_model` 的输入相连接。此处使用 FIFO 队列充当两个接口间的缓冲区，定义在 `my_env` 中。

```verilog
// my_env.sv
class my_env extends uvm_env;
    // 定义 FIFO 队列
    uvm_tlm_analysis_fifo #(my_transaction) agt_mdl_fifo;
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // ...
        agt_mdl_fifo = new("agt_mdl_fifo", this);
    endfunction
    
    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        // ...
        // 连接 FIFO 端口
        i_agt.ap.connect(agt_mdl_fifo.analysis_export);
        mdl.port.connect(agt_mdl_fifo.blocking_get_export);
    endfunction
    
    // ...
endclass
```

这里 FIFO 的类型为 `uvm_tlm_analysis_fifo`，其中 `#()` 内的是数据的类型，通过 `agt_mdl_fifo.write(obj)` 来发送数据；通过 `agt_mdl_fifo.get(obj)` 来接收数据。

这里还引入了 `connect_phase`，用于连接组件。`connect_phase` 在 `build_phase` 之后立刻执行，并且执行顺序与 `build_phase` 恰好相反，先执行叶子节点的 `connect_phase`，再执行父节点的 `connect_phase`，这样能保证上层组件拿到的没有空指针。

## scoreboard

scoreboard 用于对 DUT 的输出进行比较，从而判断 DUT 是否正确。

```verilog
// my_scoreboard.sv
class my_scoreboard extends uvm_scoreboard;
    my_transaction expect_queue[$];
    uvm_blocking_get_port #(my_transaction) exp_port;
    uvm_analysis_port #(my_transaction) act_port;
    
    `uvm_component_utils(my_scoreboard)
    
    function new(string name = "my_scoreboard", uvm_component parent = null);
        super.new(name, parent);
    endfunction
    
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        exp_port = new("exp_port", this);
        act_port = new("act_port", this);
    endfunction
    
    virtual task main_phase(uvm_phase phase);
        my_transaction get_expect, get_actual, tmp_tran;
        bit result;
        
        super.main_phase(phase);
        
        fork
            forever begin
                exp_port.get(get_expect);
                expect_queue.push_back(get_expect);
            end
            forever begin
                act_port.get(get_actual);
                if (expect_queue.size() > 0) begin
                    tmp_tran = expect_queue.pop_front();
                    result = tmp_tran.compare(get_actual);
                    
                    if (result) begin
                        // SUCCESSFUL
                    end else begin
                        // FAILED
                    end
                end else begin
                    // EXPECT QUEUE IS NOT EMPTY
                end
            end
    endtask
endclass
```

上面是一个 scoreboard 的实现。`my_scoreboard` 的数据有两个来源，分别是 reference model 和 `o_agt` 的输出。因此这里定义了两个端口。在 `main_phase` 中建立了两个线程，分别用于接收两个端口的数据。

这里假设 DUT 处理有延时，所以比较慢；而 reference model 处理速度快，所以需要将 reference model 的输出先存入队列中，等待 DUT 的输出。当另一个线程收到 DUT 的数据后，就从队列中取出元素进行比较。

## field_automation

在验证的时候经常会用到 transaction 的 `print`、`compare` 等操作对字段进行操作，因此 UVM 提供了 `uvm_field_automation` 类来简化这些操作。

```verilog
// my_transaction.sv
class my_transaction extends uvm_sequence_item;
    rand bit [47:0] dmac;
    rand bit [47:0] smac;
    // ...
    rand byte payload[];
    
    `uvm_object_utils(my_transaction)
        `uvm_field_int(dmac, UVM_ALL_ON)
        `uvm_field_int(smac, UVM_ALL_ON)
        `uvm_field_array_int(payload, UVM_ALL_ON)
        // ...
    `uvm_object_new
endclass
```

具体的注册宏与类型有关。通过这样注册字段，就可以直接调用 `copy`、`compare`、`print`、`pack_bytes`、`unpack_bytes` 等方法。

# sequence

Sequence 机制用于产生激励，然后用 driver 来驱动 transaction。其机制分为两部分：sequence 和 sequencer。

## Sequencer

```verilog
// my_sequence.sv
class my_sequencer extends uvm_sequencer #(my_transaction);
    `uvm_component_utils(my_sequencer)

    function new(string name = "my_sequencer", uvm_component parent = null);
        super.new(name, parent);
    endfunction
endclass
```

Sequencer 派生自 `uvm_sequencer`，在继承时需要指明类的参数，并且也是一个 component。

前面在定义 `my_driver` 时，直接从 `uvm_driver` 派生，但是实际上一般会从 `uvm_driver#(type)` 派生，这样就可以直接使用 `uvm_driver` 中预先定义好的一些成员。

```verilog
// my_driver.sv
class my_driver extends uvm_driver#(my_transaction)
    // ...
endclass
```

由于 sequencer 和 driver 关系密切，因此也需要将 sequencer 加入到 agent 中。

## Sequence

Sequence 并不属于验证平台的组件，而是一个 `uvm_object`，其生命周期比 `my_transaction` 稍长，在需要产生 transaction 时被创建，并且在所有的 transaction 都发送完后被销毁。

```verilog
// my_sequence.sv
class my_sequence extends uvm_sequence #(my_transaction);
    my_transaction my_trans;
    `uvm_object_utils(my_sequence)

    function new(string name="my_sequence");
        super.new(name);
    endfunction

    virtual task body();
        repeat (10) begin
            `uvm_do(my_trans)
        end
    endtask
endclass
```

Sequence 派生自 `uvm_sequence`，并且在类的参数中指明 transaction 的类型。每个 sequence 都有一个 `body` 方法，在 sequence 启动后会自动执行，用于产生 transaction。此处使用了 `uvm_do` 宏，会自动创建一个新的对象、进行随机化并传递给 sequencer。

### 向 driver 发送请求

在 sequence 向 sequencer 发送 transaction 前，需要先发送一个请求；sequencer 将这个请求放在仲裁队列中：
- 如果仲裁队列中有发送请求，但是 driver 没有申请 transaction，那么 sequencer 会一直等待，直到 driver 请求了 transaction，再批准 sequence 产生 transaction 并交给 sequencer
- 如果仲裁队列中没有发送请求，但是 driver 申请了 transaction，那么 sequencer 会等待 sequence 的状态，直到收到了 sequence 的发送请求

### 连接 driver 与 sequencer

为了能够在 driver 和 sequencer 之间进行通信，可以直接使用 `uvm_driver` 中定义的 `seq_item_port` 和 `uvm_sequencer` 中定义的 `seq_item_export`，二者可以在 agent 中通过 `connect` 方法进行连接：

```verilog
// my_agent.sv
class my_agent extends uvm_agent;
    my_driver drv;
    my_sequencer sqr;
    my_monitor mon;
    // ...

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        if (is_active == UVM_ACTIVE) begin
            drv.seq_item_port.connect(sqr.seq_item_export);
        end
        ap = mon.ap;
    endfunction
endclass
```

连接好以后，driver 就可以通过 `get_next_item` 向 sequencer 请求 transaction。这里还可以使用 `try_get_next_item`，如果 sequencer 中没有 transaction，那么就会返回 `null`，而不会一直阻塞，这样在没有数据时就可以让出总线。

```verilog
// my_driver.sv
class my_driver extends uvm_driver#(my_transaction)
    // ...

    virtual task main_phase(uvm_phase phase);
        phase.raise_objection(this);
        vif.data <= 8'b0;
        vif.valid <= 1'b0;
        while (!vif.rst) @(posedge vif.clk);
        forever begin
            seq_item_port.get_next_item(req);
            vif.data <= req.data;
            vif.valid <= 1'b1;
            @(posedge vif.clk);
            vif.valid <= 1'b0;
            seq_item_port.item_done();
        end
        phase.drop_objection(this);
    endtask
endclass
```

这里的 `item_done()` 方法相当于握手机制，会通知 sequencer，transaction 已经发送完毕。此时在 sequence 中的 `uvm_do` 宏才算完成一次执行，开始下一次循环。

### 连接 sequence 与 sequencer

要让 sequence 向 sequencer 发送 transaction，需要在某个 component 的 `main_phase` 中创建 sequence（例如 sequencer 或者 env 中），并与 sequencer 相连接。

```verilog
// my_env.sv
class my_env extends uvm_env;
    // ...

    virtual task main_phase(uvm_phase phase);
        my_sequence seq;
        phase.raise_objection(this);
        
        seq = my_sequence::type_id::create("seq");
        seq.start(i_agt.sqr);
        
        phase.drop_objection(this);
    endtask
endclass
```

使用 `start(sequencer)` 方法就能启动 sequence，sequence 会自动向 sequencer 发送 transaction。如果是在 sequencer 中创建 sequence，那么可以直接使用 `start(this)`。

另外需要注意的是此处使用了 `raise_objection`。在 UVM 中，通常只会在 sequence 出现的地方需要 `raise_objection` 和 `drop_objection`。

## `default_sequence`

使用 `default_sequence` 后就可以不用手动创建 sequence 了。类似上面的方案，在 env 中使用 `default_sequence` 创建：

```verilog
// my_env.sv
class my_env extends uvm_env;
    // ...

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        uvm_config_db#(uvm_object_wrapper)::set(
            this,
            "i_agt.sqr.main_phase",
            "default_sequence",
            my_sequence::type_id::get()
        );
    endfunction
endclass
```

此处同样使用 `uvm_config_db` 的 `set` 方法进行实现：
- 类型参数变成 `uvm_object_wrapper`
- 第一个参数从 `null` 变成 `this`，第二个参数变成 sequencer 的 `main_phase` 方法，二者共同组成了路径；使用 `default_sequence` 时要求路径必须指定到 `phase` 级别
- 第三个参数表示标识
- 第四个参数表示创建 `my_sequence` 的对象

使用了 `default_sequence` 后，不需要在 sequencer 中使用 `get` 来接收了，UVM 能够自动处理好。

# `base_test`

前面的组件树中以 `env` 为根，但是在实际的测试中，通常以 `uvm_test` 派生的类为树根。这个类通常被称为 `base_test`，它的作用是创建 `env`，并且在 `run_phase` 中启动 `env`。

```verilog
// base_test.sv
class base_test extends uvm_test;
    my_env env;

    function new(string name = "base_test", uvm_component parent = null);
        super.new(name,parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
       super.build_phase(phase);
       env = my_env::type_id::create("env", this);
       uvm_config_db#(uvm_object_wrapper)::set(
           this,
           "env.i_agt.sqr.main_phase",
           "default_sequence",
           my_sequence::type_id::get()
       );
    endfunction // build_phase

    virtual function void report_phase(uvm_phase phase);
        uvm_report_server server;
        super.report_phase(phase);

        server = get_report_server();

        int err_num;
        err_num = server.get_severity_count(UVM_ERROR);

        if (err_num != 0) $display("TEST CASE FAILED");
        else $display("TEST CASE PASSED");
    endfunction // report_phase

    `uvm_component_utils(base_test)
endclass
```

`base_test` 派生自 `uvm_test`，因此需要用 `uvm_component_utils` 宏来注册到 factory 中。

这里设置了 `default_sequence`，其他地方就不需要再设置了。

这段代码中的 `report_phase` 也是 UVM 内建的，它可以根据 `UVM_ERROR` 的数量来打印信息，在 `main_phase` 结束之后执行。

![UVM Tree](/img/in-post/post-uvm/uvm-tree.png){:height="600px" width="600px"}

对应的，`top_tb` 中应该启动 `base_test`，并且在 `uvm_config_db` 中设置的路径需要改变。

```verilog
// top_tb.sv
initial begin
    run_test("base_test");
end
```

# 使用命令行指定测试用例

UVM 中，对 DUT 的激励被称为测试向量或 pattern，一种激励作为一个测试用例。而不同的测试用例可能会存在于不同的 sequence 中，因此测试平台需要能够支持启动不同的 sequence。最方便的方法便是通过修改命令行参数来启动不同的 sequence。

在 UVM 中，使用 `run_test` 时如果不指定具体的 sequence，那么就会自动寻找命令行参数中的 `UVM_TEST_NAME` 选项来启动对应的 sequence。

例如：

```verilog
// top_tb.sv
initial begin
    run_test();
end
```

```shell
<sim command>
... +UVM_TEST_NAME=my_case0
```
