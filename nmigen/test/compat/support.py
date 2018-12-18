from ...compat import *
# from ...compat.fhdl import verilog


class SimCase:
    def setUp(self, *args, **kwargs):
        self.tb = self.TestBench(*args, **kwargs)

    # def test_to_verilog(self):
    #     verilog.convert(self.tb)

    def run_with(self, generator):
        run_simulation(self.tb, generator)
