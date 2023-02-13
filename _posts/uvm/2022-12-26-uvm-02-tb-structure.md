---
layout: "post"
title: "「UVM 学习」UVM Testbench 与 UVM Components"
subtitle: "UVM Testbench 的结构、组成以及相关组件"
author: "roife"
date: 2022-12-09

tags: ["IC 验证@集成电路", "集成电路@Tags", "UVM@集成电路", "SystemVerilog@编程语言"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# Top TB

## 一个简单的 UVM TB

```verilog
module tb_top;
    import uvm_pkg::*;

    bit clk;
    always #10 clk <= ~clk;

    dut_if         dut_if1  (clk);
    dut_wrapper    dut_wr0  (._if (dut_if1));

    initial begin
        uvm_config_db #(virtual dut_if)::set (null, "uvm_test_top", "dut_if", dut_if1);
        run_test ("base_test"); // 运行测试
    end

    initial begin
        $dumpvars;
        $dumpfile("dump.vcd");
    end
endmodule
```

## 产生时钟信号

常见的 DUT 通常会包含多时钟域，因此需要产生多个可配置的时钟信号，例如使用 `module`。

```verilog
// Module level clock generation
module clk_main (...);
    // ...
endmodule

// Instantiated and connected to an interface
module tb_top;
    bit clk_main_out;

    clk_main u_clk_main_0 ( .out (clk_main_out), ...);

    dut_if dut_if0 ( clk_main_out, ...);
endmodule
```

但是 `module` 不能直接用层次路径来访问，所以通常会用 `agent` 来包装。

```verilog
class clk_agent extends uvm_agent;
    clk_cfg m_clk_cfg;

    virtual function void build_phase(uvm_phase ph qqase);
        super.build_phase(phase);
        // Get clk_cfg object and build this agent accordingly
    endfunction
endclass

class base_test extends uvm_test;
    clk_cfg m_clk_cfg;

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        m_clk_cfg.m_freq = 500;
    endfunction
endclass
```

## 产生复位信号

有两种常见的复位模式：
- 软件复位（通常通过寄存器模型来处理，由 reset agent 负责）
- 硬件复位（reset 按键，同样可以由 reset agent 负责）

```verilog
class reset_agent extends uvm_agent;
    reset_cfg m_reset_cfg;

    // Rest of the code
endclass

class my_sequence extends uvm_sequence;
    virtual task body();
        hw_reset_seq    m_hw_reset_seq;

        // Call the required kind of reset sequence in test scenario
        m_hw_reset_seq.start(p_sequencer);
    endtask
endclass
```

## 驱动/采样内部信号

一些 TB 组件可能需要驱动或者采样 DUT 内部网络的信号，这可以通过 `assign` 来绑定到外部的接口：

```verilog
interface gen_if;
    logic [99:0]    signals;
endinterface

module tb_top;
    gen_if  u_if0 ();
    des     u_des   ( ... );

    // Assign an internal net to a generic interface signal
    assign u_if0.signals[23] = u_des.u_xyz.u_abc.status;
endmodule
```

# Testcases

一般一个 DUT 会有多个对应的 testcases，这些 testcases 被统一放在容器 Environment 中。每个 testcases 可以使用自己的配置来操作 agents、更改变量的值、使用不同的 sequences 生成数据等。

## 编写 test

```verilog
// 1. 声明一个继承自 `uvm_test' 的类
class my_test extends uvm_test;
    // 2. 使用 `uvm_component_utils 可以增加可重用性
    `uvm_component_utils (my_test)

    // 3. 定义 new 方法
    function new (string name = "my_test", uvm_component parent = null);
        super.new (name, parent);
    endfunction

    // 4. 声明其它 components
    my_env   m_top_env;  // environment
    my_cfg   m_cfg0;     // confuguration

    // 5. 定义 build phase 初始化对象
    virtual function void build_phase (uvm_phase phase);
        super.build_phase (phase);

        // 使用 type_id::create 来创建对象
        m_top_env  = my_env::type_id::create ("m_top_env", this);
        m_cfg0     = my_cfg::type_id::create ("m_cfg0", this);

        // 配置 components
        set_cfg_params ();

        // 存储 config_dv
        uvm_config_db #(my_cfg) :: set (this, "m_top_env.my_agent", "m_cfg0", m_cfg0);
    endfunction

    // 在结束时打印组件层次
    virtual function void end_of_elaboration_phase (uvm_phase phase);
        uvm_top.print_topology ();
    endfunction

    // 6. 使用 sequence 生成数据
    virtual task run_phase (uvm_phase phase);
        my_seq m_seq = my_seq::type_id::create ("m_seq");
        super.run_phase(phase);

        // raise_objection 防止 task 被自动关闭
      	phase.raise_objection (this);
        m_seq.start (m_env.seqr);    // sequence
      	phase.drop_objection (this);
    endtask

    // ...
endclass
```

## 运行测试

```verilog
// 一个全局 task，用于运行测试
task run_test (string test_name="");
    uvm_root top;
    uvm_coreservice_t cs;

cs = uvm_coreservice_t::get();
    top = cs.get_root();
    top.run_test(test_name);
endtask


initial begin
    run_test("base_test");
end
```

如果 `run_test` 的参数为空，那么会调用运行参数中的 `+UVM_TESTNAME`。

## 继承测试

```verilog
class dv_wr_rd_register_test extends base_test;
    `uvm_component_utils (dv_wr_rd_register_test)

    function new(string name = "dv_wr_rd_register_test");
        super.new(name);
    endfunction

    // 使用另一个 sequence
    virtual task run_phase(uvm_phase phase);
        wr_rd_reg_seq   m_wr_rd_reg_seq = wr_rd_reg_seq::type_id::create("m_wr_rd_reg_seq");

        super.run_phase(phase);
        phase.raise_objection(this);
        m_wr_rd_reg_seq.start(m_env.seqr);
        phase.drop_objection(this);
    endtask
endclass
```

此处必须要重载 `new` 方法。

# UVM 组件

## UVM Environment

UVM env 包含了一系列验证相关的组件以及它们的默认配置，甚至也允许在 env 里包含小的 env。虽然这些组件也能放在 `uvm_test` 中，但是这样需要为每个 testcase 都重新实现一遍，降低了可重用性。

![UVM Environment](/img/in-post/post-uvm/uvm-environment.png){:height="400px" width="400px"}

```verilog
// 1. 继承自 `uvm_test'
class my_env extends uvm_env ;
    // 2. 使用 uvm_component_utils 增加可重用性
    `uvm_component_utils (my_env)

    // 3. 定义 env 内的其它 components
    my_agent             m_agnt0;
    my_scoreboard        m_scbd0;

    // 4. 定义 new 方法
    function new (string name, uvm_component parent);
        super.new (name, parent);
    endfunction : new

    // 5. 定义 build_phase 创建并初始化对象
    virtual function void build_phase (uvm_phase phase);
        super.build_phase (phase);
        // 创建 env 内的对象
        m_agnt0 = my_agent::type_id::create ("my_agent", this);
        m_scbd0 = my_scoreboard::type_id::create ("my_scoreboard", this);

        // [Optional] 从 uvm_config_db 中获取配置
        if (uvm_config_db #(env_cfg)::get(this, "", "env_cfg", m_env_cfg))
            `uvm_fatal ("build_phase", "Did not get a configuration object for env")
            
        // [Optional] 将配置传到子部件内
    endfunction : build_phase

    virtual function void connect_phase (uvm_phase phase);
        // 连接 scoreboard 与 agent
        m_agnt0.m_mon0.item_collected_port.connect (m_scbd0.data_export);
    endfunction

endclass
```

## UVM Driver

UVM driver 负责将 sequencer 产生的信号驱动到 interface 中。

```verilog
// 1. 继承自 uvm_driver
// 参数 mydata 表示 transaction item 的类型，是可选的
class my_driver extends uvm_driver #(my_data);
    // 2. 使用 uvm_component_utils 注册
    `uvm_component_utils (my_driver)

    // 3. 定义 new 方法
    function new (string name = "my_driver", uvm_component parent = null);
        super.new (name, parent);
    endfunction

    // 4. 定义虚接口
    // 接口对象在 build_phase() 时通过 uvm_config_db 进行获取
    virtual if_name vif;

    // 5. 定义 build_phase 从 config_db 中获取接口
    virtual function void build_phase (uvm_phase phase);
        super.build_phase (phase);
        if (! uvm_config_db #(virtual if_name) :: get (this, "", "vif", vif))
            `uvm_fatal (get_type_name (), "Didn't get handle to virtual interface if_name")
    endfunction : build_phase

    // 6. 定义 run_phase 负责驱动数据
    virtual task run_phase (uvm_phase phase);
        // 循环下面的过程
        // 1. 从 sequencer 中获取 item
        // 2. 用获得的数据驱动 DUTinterface
        // 3. 结束驱动

        my_data data_obj;
        super.run_phase (phase);

        forever begin
            `uvm_info (get_type_name (), $sformatf ("Waiting for data from sequencer"), UVM_MEDIUM)
            seq_item_port.get_next_item (data_obj);
            // 驱动信号 drive_item (data_obj);
            seq_item_port.item_done ();
        end
    endtask
endclass
```

### driver 与 sequencer 连接

UVM driver 是一个参数化的类，其参数为可以驱动的 transaction 对象的类型。

UVM driver 对象有一个 TLM 端口，端口类型为 `uvm_seq_item_pull_port`，端口名为 `seq_item_port`。此端口可以接收来自 `uvm_sequencer` 的参数化 request 对象。并且 driver 还能通过 `rsp_port` 并为其提供 response 对象。

```verilog
// env 的 connect_phase()
virtual function void connect_phase ();
   m_drv0.seq_item_port.connect (m_seqr0.seq_item_export);
endfunction
```

通常 request 和 response 对象的类型是相同的（即 `item` 的类型），但是也可以显式指定来让二者的类型不同来给 sequencer 的 `export` 端口做一些分析。此时需要连接 `RSP` 端口：

```verilog
class uvm_driver #(type REQ = uvm_sequence_item, type RSP = REQ) extends uvm_component;
```

### UVM driver 与 sequencer 间的握手

UVM driver 可以用下面的方法与 sequencer 进行交互：
- `get_next_item`：阻塞方法，用于请求一个 item，直到从 sequencer 得到了对象；得到对象后应该调用 `item_done` 表示收到请求
- `try_next_item`：非阻塞方法，用于请求一个对象，如果没有对象则返回 `null`；**成功得到对象**后应该调用 `item_done` 表示收到请求
- `item_done`：非阻塞方法，用于完成握手；在调用 `get_next_item` 和 `try_next_item`（成功得到对象后）调用

#### 握手模型

有两种模型用于 UVM driver 和 sequencer 通信。

##### `get_next_item` - `by item_done`

在这种模型中，driver 获取对象并完成驱动后才返回应答信号，因此 sequence 的 `finish_item` 调用会在 driver 返回 `item_done` 后才结束。

```verilog
virtual task run_phase (uvm_phase phase);
    my_data req_item;

    forever begin
        // 1. 从 sequencer 获取对象
        seq_item_port.get_next_item (req_item);

        // 2. 驱动信号
        @(posedge vif.clk);
        vif.en <= 1;
        // 将信号驱动到接口的端口

        // 3. 通知 sequence 已完成处理
        seq_item_port.item_done();
        // finish_item 方法结束
    end
    // ...
endtask
```

#### `get` - `put`

在这种模型中，driver 获得对象后马上返回应答信号，然后才开始驱动对象，并用 `put` 调用表明结束。Sequence 的 `finish_item` 方法会在调用 `get` 方法后立刻结束。

```verilog
virtual task run_phase (uvm_phase phase);
    my_data req_item;

    forever begin
        // 1. 获取对象
        seq_item_port.get (req_item);
        // finish_item 方法结束

        // 2. 驱动信号
        @(posedge vif.clk);
        vif.en = 1;
        // 将信号驱动到接口的端口

        // 3. 通知 sequence 完成驱动
        seq_item_port.put (rsp_item);
    end
endtask
```


## UVM Sequencer

Sequencer 能够生成 transaction 并发送到 driver。Sequencer 在定义时可以带上一个或两个参数，其中 

```verilog
class uvm_sequencer #(type REQ = uvm_sequence_item, RSP = REQ) extends uvm_sequencer_param_base #(REQ, RSP);
```
