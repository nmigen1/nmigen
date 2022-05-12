from nmigen import Elaboratable, Array, Record, Signal, Module
from nmigen.cli import main


class GPIO(Elaboratable):
    """GPIO demo class, takes an Array of pins and a bus Record.
    reading is combinatorial, writing to the GPIO pins is latched (sync)
    """
    def __init__(self, pins, bus):
        self.pins = Array(pins)
        self.bus  = bus

    def elaborate(self, platform):
        m = Module()
        # output (reading) is combinatorial, done all the time
        m.d.comb += self.bus.r_data.eq(self.pins[self.bus.addr])
        # input (writing) to the GPIOs is done only on "write-enable"
        with m.If(self.bus.we):
            m.d.sync += self.pins[self.bus.addr].eq(self.bus.w_data)
        return m


if __name__ == "__main__":
    # declare number of GPIOs and the width
    n_pins = 8
    gpio_width = 8
    # create a bus from a  Record for the read/write access to the GPIOs
    bus = Record([
        ("addr",   n_pins.bit_length()-1),
        ("r_data", gpio_width),
        ("w_data", gpio_width),
        ("we",     1),
    ])
    # create an array of pins and pass them to the GPIO class.
    pins = [Signal(gpio_width) for i in range(n_pins)]
    gpio = GPIO(pins, bus)
    # convenient function to either run simulation or generate verilog/ilang
    main(gpio, ports=pins + [bus.addr, bus.r_data, bus.w_data, bus.we])
