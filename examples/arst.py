from nmigen.fhdl import *
from nmigen.back import rtlil, verilog


class ClockDivisor:
    def __init__(self, factor):
        self.v = Signal(factor)
        self.o = Signal()

    def get_fragment(self, platform):
        m = Module()
        m.d.sync += self.v.eq(self.v + 1)
        m.d.comb += self.o.eq(self.v[-1])
        return m.lower(platform)


sync = ClockDomain(async_reset=True)
ctr  = ClockDivisor(factor=16)
frag = ctr.get_fragment(platform=None)
# print(rtlil.convert(frag, ports=[sync.clk, sync.reset, ctr.o], clock_domains={"sync": sync}))
print(verilog.convert(frag, ports=[sync.clk, sync.reset, ctr.o], clock_domains={"sync": sync}))
