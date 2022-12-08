---
layout: "post"
title: "「System Verilog」 09 线程及通信"
subtitle: "Thread & Communication"
author: "roife"
date: 2022-10-28

tags: ["System Verilog@编程语言", "集成电路@Tags", "SV for Verification@读书笔记"]
lang: zh
catalog: true
header-image: ""
header-style: text
---

# 线程

SV 的测试平台隶属于 `program`，其中所有的代码都从 `initial` 语句开始执行。Verilog 中的语句可以分为两种：`begin...end` 中的语句会顺序执行，而 `fork...join` 中的语句会并行执行。

此外，SV 还引入了 `fork...join_none` 和 `fork...join_any` 语句。

![fork-join](/img/in-post/post-system-verilog/fork-join.png)

## `fork...join`

`fork...join` 块中的所有语句会并发执行。在 `fork...join` 中可以嵌入 `begin...end` 语句来表示需要顺序执行的块：

```verilog
initial begin
    // thread_1 与 thread_2 并发执行
    // begin...end 块内会顺序执行
    fork
        begin:thread_1
            // 顺序执行
        end
        begin:thread_2
            // 顺序执行
        end
    join
end
```

可以给语句加上延时 `#` 来控制执行的顺序。

只有 `fork...join` 中的所有语句都执行完毕，才会执行 `join` 之后的语句。

## `fork...join_none`

`fork...join_none` 在执行子线程时，父线程会继续执行。

```verilog
initial begin
    // thread_1 与 thread_2 并发执行
    fork
        begin:thread_1
        end

        begin:thread_2
        end
    join_none
    // 父线程继续执行
end
```

## `fork...join_any`

`fork...join_any` 在任意一个子线程执行完毕时，就开始恢复父线程的执行（其他没有执行完毕的子线程不受影响，继续执行）。

```verilog
initial begin
    // thread_1 与 thread_2 并发执行
    fork
        begin:thread_1
        end

        begin:thread_2
        end
    join_any
    // 某个子线程执行完毕后，父线程继续执行
end
```

## 使用 `automatic` 捕获变量

由于 `fork...join` 不会像闭包一样自动捕获变量，因此下面这个创建线程的循环可能会出现问题。

```verilog
for (int i = 0; i < 3; i++) begin
    fork
        // 可能先创建了三个线程，然后运行线程中的语句。
        // 输出 2 2 2
        $write(i);
    join_none
end
```

因此在循环中创建线程时，推荐用 `automatic` 来捕获当前的变量。

```verilog
for (int i = 0; i < 3; i++) begin
    fork
        automatic int j = i;
        $write(j);
    join_none
end
```

或者设置为 `automatic program`，然后直接用局部变量捕获。

```verilog
program automatic p;
    for (int i = 0; i < 3; i++) begin
        int j = i;
        fork
            $write(j);
        join_none
    end
endprogram
```

## 等待子线程

使用 `wait fork` 语句可以等待当前线程 fork 出来的所有子线程（不包括子线程的子线程）结束，然后再继续执行。

## 终止线程

用 `disable LABEL` 可以终止 `fork...join` 语句中的所有线程。

例如下面这个程序可以实现检测总线地址，并在超时后直接终止执行的功能。

```verilog
fork
    begin
        fork: timeout_block
            begin
                wait (bus.cb.addr == tr.addr);
                $display("Addr match");
            end
            #TIME_OUT $display("[TIMEOUT]");
        join_any

        disable timeout_block;
    end
join_none
```

用 `disable fork` 可以终止当前线程 fork 出来的所有子线程（包括子线程的子线程）。使用 `disable fork` 时可能会产生误杀，因此通常会用 `fork...join` 来包裹当前需要作用的语句块，保证指终止指定范围内的线程。

```verilog
task jobs（）;
    fork : guard_fork
        begin
            fork
                begin
                    #10;
                    $display("delay 10ns");
                end
                begin
                    #20;
                    $display("delay 20ns");
                end
            join_any
            disable fork
        end
    join : guard_fork
endtask
```

需要注意的是，如果某个 `task_1` 内部会产生线程 `sub_thread`，而且该 `task_1` 被调用了多次（即产生了多个 `sub_thread`）。如果某个 `sub_thread` 调用了 `disable task_1`，那么它会终止所有的 `task_1`，而不是只终止自己。

# 线程通信

## 事件 `event`

SV 中的事件变量会指向事件对象，也可以被赋为 `null`。变量被创建时也会指向一个对应的事件对象。同时，事件可以被当作参数传入子程序或者类内（不用加 `ref`）。

### 事件触发与等待

Verilog 中可以使用 `->` 来触发事件，并且用 `@(event)` 等待事件。然而 Verilog 中的触发是一瞬间的（零宽度的脉冲），如果在 `@` 前触发了事件，那么可能会导致线程在事件触发后阻塞。因此 SV 中加入了 `triggered` 函数来避免竞争，可以使用 `wait(event.triggered())` 来判断**当前时间步长内**事件是否被触发。

```verilog
module tb;
    // 创建一个名为 `event_a` 的事件，并创建一个事件对象
    event event_a;

    initial begin
        // 使用 -> 触发事件
        #20 -> event_a;
    end

    initial begin
        // 使用 @ 等待事件
        @(event_a);
        $display ("[%0t] Thread2: received event_a trigger ", $time);
    end

    initial begin
        // 使用 triggered 等待事件
        wait(event_a.triggered());
        $display ("[%0t] Thread3: received event_a trigger", $time);
    end
endmodule
```

### 等待多个事件

如果希望等待一个事件数组内的所有事件完成，可以将事件传入子程序，然后通过 `fork...join_none` 和 `wait fork` 完成。

```verilog
event done[N];

initial begin
    foreach (thread[i]) begin
        thread[i] = new();
        thread[i].start(done[i]);
    end

    foreach (thread[i]) begin
        fork
            automatic int k = i;
            wait (done[k].triggered());
        join_none
    end
    wait fork;
end
```

### 等待顺序事件

用 `wait_order(event_1, event_2, ..., event_n)` 可以监测 `n` 个事件是否按顺序执行。语法如下：

```verilog
wait_order(event_1, event_2, ..., event_n)
    // if events are triggered in order
else
    // if events are triggered out of order
```

### 合并事件（赋值）

事件间的赋值语句 `event_a = event_b` 会导致所有等待 `event_a` 的线程都会等待 `event_b`（相当于等待的事件被替换了）。

## 旗语（信号量）

用 `semaphore` 可以创建一个旗语。
- `sem = new(n)` 旗语有 `n` 把钥匙
- `sem.get(k)` 获取 `k` 把钥匙（`sem -= k`）
- `sem.put(k)` 归还 `k` 把钥匙（`sem += k`）

类似信号量，使用 `get` 时如果钥匙不够则会阻塞。
- `sem.try_get(k)` 尝试获取 `k` 把钥匙，如果不够则返回 `0`，否则返回 `1`

## 信箱（`mailbox`）

信箱有点像 unix 中的管道，是一个 FIFO 队列，可以在一端放入数据，另一端取出数据。SV 中的信箱可以放入任意类型的数据。

信箱可以是有限的，也可以是无限的，区别在于创建时有没有指定大小。对于容量有限的信箱，当信箱满了之后如果接收端没有取出，那么发送端会阻塞。

用 `mailbox` 可以创建一个信箱。
- `mbx = new(size)` 如果 `size > 0` 则创建容量为 `size` 的信箱，否则创建一个无限大的信箱
- `int num()` 返回信箱中的信息数量
- `mbx.get(ref singular msg)` 与 `int mbx.try_get(ref singular msg)` ：接受信息（后者不会阻塞，并返回是否成功接收）
- `mbx.get(ref singular msg)` 与 `int mbx.try_get(ref singular msg)` ：拷贝顶部的信息但不取出（后者不会阻塞，并返回是否成功接收）
- `mbx.put(singular msg)` 与 `int mbx.try_put(singular msg)` ：发送信息（后者不会阻塞，并返回是否成功发送）

### 参数化信箱

在定义信箱时可以传入参数，以说明信箱中数据的类型：

```verilog
mailbox #(string) string_mbx;
```