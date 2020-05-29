from abc import abstractproperty

from ..hdl import *
from ..lib.cdc import ResetSynchronizer
from ..build import *


__all__ = ["LatticeICE40Platform"]


class LatticeICE40Platform(TemplatedPlatform):
    """
    IceStorm toolchain
    ------------------

    Required tools:
        * ``yosys``
        * ``nextpnr-ice40``
        * ``icepack``

    The environment is populated by running the script specified in the environment variable
    ``NMIGEN_ENV_IceStorm``, if present.

    Available overrides:
        * ``verbose``: enables logging of informational messages to standard error.
        * ``read_verilog_opts``: adds options for ``read_verilog`` Yosys command.
        * ``synth_opts``: adds options for ``synth_ice40`` Yosys command.
        * ``script_after_read``: inserts commands after ``read_ilang`` in Yosys script.
        * ``script_after_synth``: inserts commands after ``synth_ice40`` in Yosys script.
        * ``yosys_opts``: adds extra options for ``yosys``.
        * ``nextpnr_opts``: adds extra options for ``nextpnr-ice40``.
        * ``add_pre_pack``: inserts commands at the end in pre-pack Python script.
        * ``add_constraints``: inserts commands at the end in the PCF file.

    Build products:
        * ``{{name}}.rpt``: Yosys log.
        * ``{{name}}.json``: synthesized RTL.
        * ``{{name}}.tim``: nextpnr log.
        * ``{{name}}.asc``: ASCII bitstream.
        * ``{{name}}.bin``: binary bitstream.

    iCECube2 toolchain
    ------------------

    This toolchain comes in two variants: ``LSE-iCECube2`` and ``Synplify-iCECube2``.

    Required tools:
        * iCECube2 toolchain
        * ``tclsh``

    The environment is populated by setting the necessary environment variables based on
    ``NMIGEN_ENV_iCECube2``, which must point to the root of the iCECube2 installation, and
    is required.

    Available overrides:
        * ``verbose``: enables logging of informational messages to standard error.
        * ``lse_opts``: adds options for LSE.
        * ``script_after_add``: inserts commands after ``add_file`` in Synplify Tcl script.
        * ``script_after_options``: inserts commands after ``set_option`` in Synplify Tcl script.
        * ``add_constraints``: inserts commands in SDC file.
        * ``script_after_flow``: inserts commands after ``run_sbt_backend_auto`` in SBT
          Tcl script.

    Build products:
        * ``{{name}}_lse.log`` (LSE) or ``{{name}}_design/{{name}}.htm`` (Synplify): synthesis log.
        * ``sbt/outputs/router/{{name}}_timing.rpt``: timing report.
        * ``{{name}}.edf``: EDIF netlist.
        * ``{{name}}.bin``: binary bitstream.
    """

    toolchain = None # selected when creating platform

    device  = abstractproperty()
    package = abstractproperty()

    # IceStorm templates

    _nextpnr_device_options = {
        "iCE40LP384": "--lp384",
        "iCE40LP1K":  "--lp1k",
        "iCE40LP4K":  "--lp8k",
        "iCE40LP8K":  "--lp8k",
        "iCE40HX1K":  "--hx1k",
        "iCE40HX4K":  "--hx8k",
        "iCE40HX8K":  "--hx8k",
        "iCE40UP5K":  "--up5k",
        "iCE40UP3K":  "--up5k",
        "iCE5LP4K":   "--u4k",
        "iCE5LP2K":   "--u4k",
        "iCE5LP1K":   "--u4k",
    }
    _nextpnr_package_options = {
        "iCE40LP4K":  ":4k",
        "iCE40HX4K":  ":4k",
        "iCE40UP3K":  "",
        "iCE5LP2K":   "",
        "iCE5LP1K":   "",
    }

    _icestorm_required_tools = [
        "yosys",
        "nextpnr-ice40",
        "icepack",
    ]
    _icestorm_file_templates = {
        **TemplatedPlatform.build_script_templates,
        "{{name}}.il": r"""
            # {{autogenerated}}
            {{emit_rtlil()}}
        """,
        "{{name}}.debug.v": r"""
            /* {{autogenerated}} */
            {{emit_debug_verilog()}}
        """,
        "{{name}}.ys": r"""
            # {{autogenerated}}
            {% for file in platform.iter_extra_files(".v") -%}
                read_verilog {{get_override("read_verilog_opts")|options}} {{file}}
            {% endfor %}
            {% for file in platform.iter_extra_files(".sv") -%}
                read_verilog -sv {{get_override("read_verilog_opts")|options}} {{file}}
            {% endfor %}
            {% for file in platform.iter_extra_files(".il") -%}
                read_ilang {{file}}
            {% endfor %}
            read_ilang {{name}}.il
            {{get_override("script_after_read")|default("# (script_after_read placeholder)")}}
            synth_ice40 {{get_override("synth_opts")|options}} -top {{name}}
            {{get_override("script_after_synth")|default("# (script_after_synth placeholder)")}}
            write_json {{name}}.json
        """,
        "{{name}}.pcf": r"""
            # {{autogenerated}}
            {% for port_name, pin_name, attrs in platform.iter_port_constraints_bits() -%}
                set_io {{port_name}} {{pin_name}}
            {% endfor %}
            {% for net_signal, port_signal, frequency in platform.iter_clock_constraints() -%}
                set_frequency {{net_signal|hierarchy(".")}} {{frequency/1000000}}
            {% endfor%}
            {{get_override("add_constraints")|default("# (add_constraints placeholder)")}}
        """,
    }
    _icestorm_command_templates = [
        r"""
        {{invoke_tool("yosys")}}
            {{quiet("-q")}}
            {{get_override("yosys_opts")|options}}
            -l {{name}}.rpt
            {{name}}.ys
        """,
        r"""
        {{invoke_tool("nextpnr-ice40")}}
            {{quiet("--quiet")}}
            {{get_override("nextpnr_opts")|options}}
            --log {{name}}.tim
            {{platform._nextpnr_device_options[platform.device]}}
            --package
                {{platform.package|lower}}{{platform._nextpnr_package_options[platform.device]|
                                            default("")}}
            --json {{name}}.json
            --pcf {{name}}.pcf
            --asc {{name}}.asc
        """,
        r"""
        {{invoke_tool("icepack")}}
            {{verbose("-v")}}
            {{name}}.asc
            {{name}}.bin
        """
    ]

    # iCECube2 templates

    _icecube2_required_tools = [
        "yosys",
        "synthesis",
        "synpwrap",
        "tclsh",
    ]
    _icecube2_file_templates = {
        **TemplatedPlatform.build_script_templates,
        "build_{{name}}.sh": r"""
            # {{autogenerated}}
            set -e{{verbose("x")}}
            if [ -n "${{platform._toolchain_env_var}}" ]; then
                # LSE environment
                export LD_LIBRARY_PATH=${{platform._toolchain_env_var}}/LSE/bin/lin64:$LD_LIBRARY_PATH
                export PATH=${{platform._toolchain_env_var}}/LSE/bin/lin64:$PATH
                export FOUNDRY=${{platform._toolchain_env_var}}/LSE
                # Synplify environment
                export LD_LIBRARY_PATH=${{platform._toolchain_env_var}}/sbt_backend/bin/linux/opt/synpwrap:$LD_LIBRARY_PATH
                export PATH=${{platform._toolchain_env_var}}/sbt_backend/bin/linux/opt/synpwrap:$PATH
                export SYNPLIFY_PATH=${{platform._toolchain_env_var}}/synpbase
                # Common environment
                export SBT_DIR=${{platform._toolchain_env_var}}/sbt_backend
            else
                echo "Variable ${{platform._toolchain_env_var}} must be set" >&2; exit 1
            fi
            {{emit_commands("sh")}}
        """,
        "{{name}}.v": r"""
            /* {{autogenerated}} */
            {{emit_verilog()}}
        """,
        "{{name}}.debug.v": r"""
            /* {{autogenerated}} */
            {{emit_debug_verilog()}}
        """,
        "{{name}}_lse.prj": r"""
            # {{autogenerated}}
            -a SBT{{platform.family}}
            -d {{platform.device}}
            -t {{platform.package}}
            {{get_override("lse_opts")|options|default("# (lse_opts placeholder)")}}
            {% for file in platform.iter_extra_files(".v") -%}
                -ver {{file}}
            {% endfor %}
            -ver {{name}}.v
            -sdc {{name}}.sdc
            -top {{name}}
            -output_edif {{name}}.edf
            -logfile {{name}}_lse.log
        """,
        "{{name}}_syn.prj": r"""
            # {{autogenerated}}
            {% for file in platform.iter_extra_files(".v", ".sv", ".vhd", ".vhdl") -%}
                add_file -verilog {{file|tcl_escape}}
            {% endfor %}
            add_file -verilog {{name}}.v
            add_file -constraint {{name}}.sdc
            {{get_override("script_after_add")|default("# (script_after_add placeholder)")}}
            impl -add {{name}}_design -type fpga
            set_option -technology SBT{{platform.family}}
            set_option -part {{platform.device}}
            set_option -package {{platform.package}}
            {{get_override("script_after_options")|default("# (script_after_options placeholder)")}}
            project -result_format edif
            project -result_file {{name}}.edf
            impl -active {{name}}_design
            project -run compile
            project -run map
            project -run fpga_mapper
            file copy -force -- {{name}}_design/{{name}}.edf {{name}}.edf
        """,
        "{{name}}.sdc": r"""
            # {{autogenerated}}
            {% for net_signal, port_signal, frequency in platform.iter_clock_constraints() -%}
                {% if port_signal is not none -%}
                    create_clock -name {{port_signal.name|tcl_escape}} -period {{1000000000/frequency}} [get_ports {{port_signal.name|tcl_escape}}]
                {% else -%}
                    create_clock -name {{net_signal.name|tcl_escape}} -period {{1000000000/frequency}} [get_nets {{net_signal|hierarchy("/")|tcl_escape}}]
                {% endif %}
            {% endfor %}
            {{get_override("add_constraints")|default("# (add_constraints placeholder)")}}
        """,
        "{{name}}.tcl": r"""
            # {{autogenerated}}
            set device {{platform.device}}-{{platform.package}}
            set top_module {{name}}
            set proj_dir .
            set output_dir .
            set edif_file {{name}}
            set tool_options ":edifparser -y {{name}}.pcf"
            set sbt_root $::env(SBT_DIR)
            append sbt_tcl $sbt_root "/tcl/sbt_backend_synpl.tcl"
            source $sbt_tcl
            run_sbt_backend_auto $device $top_module $proj_dir $output_dir $tool_options $edif_file
            {{get_override("script_after_file")|default("# (script_after_file placeholder)")}}
            file copy -force -- sbt/outputs/bitmap/{{name}}_bitmap.bin {{name}}.bin
            exit
        """,
        "{{name}}.pcf": r"""
            # {{autogenerated}}
            {% for port_name, pin_name, attrs in platform.iter_port_constraints_bits() -%}
                set_io {{port_name}} {{pin_name}}
            {% endfor %}
        """,
    }
    _lse_icecube2_command_templates = [
        r"""synthesis -f {{name}}_lse.prj""",
        r"""tclsh {{name}}.tcl""",
    ]
    _synplify_icecube2_command_templates = [
        r"""synpwrap -prj {{name}}_syn.prj -log {{name}}_syn.log""",
        r"""tclsh {{name}}.tcl""",
    ]

    # Common logic

    def __init__(self, *, toolchain="IceStorm"):
        super().__init__()

        assert toolchain in ("IceStorm", "LSE-iCECube2", "Synplify-iCECube2")
        self.toolchain = toolchain

    @property
    def family(self):
        if self.device.startswith("iCE40"):
            return "iCE40"
        if self.device.startswith("iCE5"):
            return "iCE5"
        assert False

    @property
    def _toolchain_env_var(self):
        if self.toolchain == "IceStorm":
            return f"NMIGEN_ENV_{self.toolchain}"
        if self.toolchain in ("LSE-iCECube2", "Synplify-iCECube2"):
            return f"NMIGEN_ENV_iCECube2"
        assert False

    @property
    def required_tools(self):
        if self.toolchain == "IceStorm":
            return self._icestorm_required_tools
        if self.toolchain in ("LSE-iCECube2", "Synplify-iCECube2"):
            return self._icecube2_required_tools
        assert False

    @property
    def file_templates(self):
        if self.toolchain == "IceStorm":
            return self._icestorm_file_templates
        if self.toolchain in ("LSE-iCECube2", "Synplify-iCECube2"):
            return self._icecube2_file_templates
        assert False

    @property
    def command_templates(self):
        if self.toolchain == "IceStorm":
            return self._icestorm_command_templates
        if self.toolchain == "LSE-iCECube2":
            return self._lse_icecube2_command_templates
        if self.toolchain == "Synplify-iCECube2":
            return self._synplify_icecube2_command_templates
        assert False

    @property
    def default_clk_constraint(self):
        # Internal high-speed oscillator: 48 MHz / (2 ^ div)
        if self.default_clk == "SB_HFOSC":
            return Clock(48e6 / 2 ** self.hfosc_div)
        # Internal low-speed oscillator: 10 KHz
        elif self.default_clk == "SB_LFOSC":
            return Clock(10e3)
        # Otherwise, use the defined Clock resource.
        return super().default_clk_constraint

    def create_missing_domain(self, name):
        # For unknown reasons (no errata was ever published, and no documentation mentions this
        # issue), iCE40 BRAMs read as zeroes for ~3 us after configuration and release of internal
        # global reset. Note that this is a *time-based* delay, generated purely by the internal
        # oscillator, which may not be observed nor influenced directly. For details, see links:
        #  * https://github.com/cliffordwolf/icestorm/issues/76#issuecomment-289270411
        #  * https://github.com/cliffordwolf/icotools/issues/2#issuecomment-299734673
        #
        # To handle this, it is necessary to have a global reset in any iCE40 design that may
        # potentially instantiate BRAMs, and assert this reset for >3 us after configuration.
        # (We add a margin of 5x to allow for PVT variation.) If the board includes a dedicated
        # reset line, this line is ORed with the power on reset.
        #
        # If an internal oscillator is selected as the default clock source, the power-on-reset
        # delay is increased to 100 us, since the oscillators are only stable after that long.
        #
        # The power-on reset timer counts up because the vendor tools do not support initialization
        # of flip-flops.
        if name == "sync" and self.default_clk is not None:
            m = Module()

            # Internal high-speed clock: 6 MHz, 12 MHz, 24 MHz, or 48 MHz depending on the divider.
            if self.default_clk == "SB_HFOSC":
                if not hasattr(self, "hfosc_div"):
                    raise ValueError("SB_HFOSC divider exponent (hfosc_div) must be an integer "
                                     "between 0 and 3")
                if not isinstance(self.hfosc_div, int) or self.hfosc_div < 0 or self.hfosc_div > 3:
                    raise ValueError("SB_HFOSC divider exponent (hfosc_div) must be an integer "
                                     "between 0 and 3, not {!r}"
                                     .format(self.hfosc_div))
                clk_i = Signal()
                m.submodules += Instance("SB_HFOSC",
                                         i_CLKHFEN=1,
                                         i_CLKHFPU=1,
                                         p_CLKHF_DIV="0b{0:b}".format(self.hfosc_div),
                                         o_CLKHF=clk_i)
                delay = int(100e-6 * self.default_clk_frequency)
            # Internal low-speed clock: 10 KHz.
            elif self.default_clk == "SB_LFOSC":
                clk_i = Signal()
                m.submodules += Instance("SB_LFOSC",
                                         i_CLKLFEN=1,
                                         i_CLKLFPU=1,
                                         o_CLKLF=clk_i)
                delay = int(100e-6 * self.default_clk_frequency)
            # User-defined clock signal.
            else:
                clk_i = self.request(self.default_clk).i
                delay = int(15e-6 * self.default_clk_frequency)

            if self.default_rst is not None:
                rst_i = self.request(self.default_rst).i
            else:
                rst_i = Const(0)

            # Power-on-reset domain
            m.domains += ClockDomain("por", reset_less=True, local=True)
            timer = Signal(range(delay))
            ready = Signal()
            m.d.comb += ClockSignal("por").eq(clk_i)
            with m.If(timer == delay):
                m.d.por += ready.eq(1)
            with m.Else():
                m.d.por += timer.eq(timer + 1)

            # Primary domain
            m.domains += ClockDomain("sync")
            m.d.comb += ClockSignal("sync").eq(clk_i)
            if self.default_rst is not None:
                m.submodules.reset_sync = ResetSynchronizer(~ready | rst_i, domain="sync")
            else:
                m.d.comb += ResetSignal("sync").eq(~ready)

            return m

    def should_skip_port_component(self, port, attrs, component):
        # On iCE40, a differential input is placed by only instantiating an SB_IO primitive for
        # the pin with z=0, which is the non-inverting pin. The pinout unfortunately differs
        # between LP/HX and UP series:
        #  * for LP/HX, z=0 is DPxxB   (B is non-inverting, A is inverting)
        #  * for UP,    z=0 is IOB_xxA (A is non-inverting, B is inverting)
        if attrs.get("IO_STANDARD", "SB_LVCMOS") == "SB_LVDS_INPUT" and component == "n":
            return True
        return False

    def _get_io_buffer(self, m, pin, port, attrs, *, i_invert=False, o_invert=False,
                       invert_lut=False):
        def get_dff(clk, d, q):
            m.submodules += Instance("$dff",
                p_CLK_POLARITY=1,
                p_WIDTH=len(d),
                i_CLK=clk,
                i_D=d,
                o_Q=q)

        def get_ineg(y, invert):
            if invert_lut:
                a = Signal.like(y, name_suffix="_x{}".format(1 if invert else 0))
                for bit in range(len(y)):
                    m.submodules += Instance("SB_LUT4",
                        p_LUT_INIT=Const(0b01 if invert else 0b10, 16),
                        i_I0=a[bit],
                        i_I1=Const(0),
                        i_I2=Const(0),
                        i_I3=Const(0),
                        o_O=y[bit])
                return a
            elif invert:
                a = Signal.like(y, name_suffix="_n")
                m.d.comb += y.eq(~a)
                return a
            else:
                return y

        def get_oneg(a, invert):
            if invert_lut:
                y = Signal.like(a, name_suffix="_x{}".format(1 if invert else 0))
                for bit in range(len(a)):
                    m.submodules += Instance("SB_LUT4",
                        p_LUT_INIT=Const(0b01 if invert else 0b10, 16),
                        i_I0=a[bit],
                        i_I1=Const(0),
                        i_I2=Const(0),
                        i_I3=Const(0),
                        o_O=y[bit])
                return y
            elif invert:
                y = Signal.like(a, name_suffix="_n")
                m.d.comb += y.eq(~a)
                return y
            else:
                return a

        if "GLOBAL" in attrs:
            is_global_input = bool(attrs["GLOBAL"])
            del attrs["GLOBAL"]
        else:
            is_global_input = False
        assert not (is_global_input and i_invert)

        if "i" in pin.dir:
            if pin.xdr < 2:
                pin_i  = get_ineg(pin.i,  i_invert)
            elif pin.xdr == 2:
                pin_i0 = get_ineg(pin.i0, i_invert)
                pin_i1 = get_ineg(pin.i1, i_invert)
        if "o" in pin.dir:
            if pin.xdr < 2:
                pin_o  = get_oneg(pin.o,  o_invert)
            elif pin.xdr == 2:
                pin_o0 = get_oneg(pin.o0, o_invert)
                pin_o1 = get_oneg(pin.o1, o_invert)

        if "i" in pin.dir and pin.xdr == 2:
            i0_ff = Signal.like(pin_i0, name_suffix="_ff")
            i1_ff = Signal.like(pin_i1, name_suffix="_ff")
            get_dff(pin.i_clk, i0_ff, pin_i0)
            get_dff(pin.i_clk, i1_ff, pin_i1)
        if "o" in pin.dir and pin.xdr == 2:
            o1_ff = Signal.like(pin_o1, name_suffix="_ff")
            get_dff(pin.o_clk, pin_o1, o1_ff)

        for bit in range(len(port)):
            io_args = [
                ("io", "PACKAGE_PIN", port[bit]),
                *(("p", key, value) for key, value in attrs.items()),
            ]

            if "i" not in pin.dir:
                # If no input pin is requested, it is important to use a non-registered input pin
                # type, because an output-only pin would not have an input clock, and if its input
                # is configured as registered, this would prevent a co-located input-capable pin
                # from using an input clock.
                i_type =     0b01 # PIN_INPUT
            elif pin.xdr == 0:
                i_type =     0b01 # PIN_INPUT
            elif pin.xdr > 0:
                i_type =     0b00 # PIN_INPUT_REGISTERED aka PIN_INPUT_DDR
            if "o" not in pin.dir:
                o_type = 0b0000   # PIN_NO_OUTPUT
            elif pin.xdr == 0 and pin.dir == "o":
                o_type = 0b0110   # PIN_OUTPUT
            elif pin.xdr == 0:
                o_type = 0b1010   # PIN_OUTPUT_TRISTATE
            elif pin.xdr == 1 and pin.dir == "o":
                o_type = 0b0101   # PIN_OUTPUT_REGISTERED
            elif pin.xdr == 1:
                o_type = 0b1101   # PIN_OUTPUT_REGISTERED_ENABLE_REGISTERED
            elif pin.xdr == 2 and pin.dir == "o":
                o_type = 0b0100   # PIN_OUTPUT_DDR
            elif pin.xdr == 2:
                o_type = 0b1100   # PIN_OUTPUT_DDR_ENABLE_REGISTERED
            io_args.append(("p", "PIN_TYPE", C((o_type << 2) | i_type, 6)))

            if hasattr(pin, "i_clk"):
                io_args.append(("i", "INPUT_CLK",  pin.i_clk))
            if hasattr(pin, "o_clk"):
                io_args.append(("i", "OUTPUT_CLK", pin.o_clk))

            if "i" in pin.dir:
                if pin.xdr == 0 and is_global_input:
                    io_args.append(("o", "GLOBAL_BUFFER_OUTPUT", pin.i[bit]))
                elif pin.xdr < 2:
                    io_args.append(("o", "D_IN_0",  pin_i[bit]))
                elif pin.xdr == 2:
                    # Re-register both inputs before they enter fabric. This increases hold time
                    # to an entire cycle, and adds one cycle of latency.
                    io_args.append(("o", "D_IN_0",  i0_ff[bit]))
                    io_args.append(("o", "D_IN_1",  i1_ff[bit]))
            if "o" in pin.dir:
                if pin.xdr < 2:
                    io_args.append(("i", "D_OUT_0", pin_o[bit]))
                elif pin.xdr == 2:
                    # Re-register negedge output after it leaves fabric. This increases setup time
                    # to an entire cycle, and doesn't add latency.
                    io_args.append(("i", "D_OUT_0", pin_o0[bit]))
                    io_args.append(("i", "D_OUT_1", o1_ff[bit]))

            if pin.dir in ("oe", "io"):
                io_args.append(("i", "OUTPUT_ENABLE", pin.oe))

            if is_global_input:
                m.submodules["{}_{}".format(pin.name, bit)] = Instance("SB_GB_IO", *io_args)
            else:
                m.submodules["{}_{}".format(pin.name, bit)] = Instance("SB_IO", *io_args)

    def get_input(self, pin, port, attrs, invert):
        self._check_feature("single-ended input", pin, attrs,
                            valid_xdrs=(0, 1, 2), valid_attrs=True)
        m = Module()
        self._get_io_buffer(m, pin, port, attrs, i_invert=invert)
        return m

    def get_output(self, pin, port, attrs, invert):
        self._check_feature("single-ended output", pin, attrs,
                            valid_xdrs=(0, 1, 2), valid_attrs=True)
        m = Module()
        self._get_io_buffer(m, pin, port, attrs, o_invert=invert)
        return m

    def get_tristate(self, pin, port, attrs, invert):
        self._check_feature("single-ended tristate", pin, attrs,
                            valid_xdrs=(0, 1, 2), valid_attrs=True)
        m = Module()
        self._get_io_buffer(m, pin, port, attrs, o_invert=invert)
        return m

    def get_input_output(self, pin, port, attrs, invert):
        self._check_feature("single-ended input/output", pin, attrs,
                            valid_xdrs=(0, 1, 2), valid_attrs=True)
        m = Module()
        self._get_io_buffer(m, pin, port, attrs, i_invert=invert, o_invert=invert)
        return m

    def get_diff_input(self, pin, p_port, n_port, attrs, invert):
        self._check_feature("differential input", pin, attrs,
                            valid_xdrs=(0, 1, 2), valid_attrs=True)
        m = Module()
        # See comment in should_skip_port_component above.
        self._get_io_buffer(m, pin, p_port, attrs, i_invert=invert)
        return m

    def get_diff_output(self, pin, p_port, n_port, attrs, invert):
        self._check_feature("differential output", pin, attrs,
                            valid_xdrs=(0, 1, 2), valid_attrs=True)
        m = Module()
        # Note that the non-inverting output pin is not driven the same way as a regular
        # output pin. The inverter introduces a delay, so for a non-inverting output pin,
        # an identical delay is introduced by instantiating a LUT. This makes the waveform
        # perfectly symmetric in the xdr=0 case.
        self._get_io_buffer(m, pin, p_port, attrs, o_invert=    invert, invert_lut=True)
        self._get_io_buffer(m, pin, n_port, attrs, o_invert=not invert, invert_lut=True)
        return m

    # Tristate bidirectional buffers are not supported on iCE40 because it requires external
    # termination, which is different for differential pins configured as inputs and outputs.

    # CDC primitives are not currently specialized for iCE40. It is not known if iCECube2 supports
    # the necessary attributes; nextpnr-ice40 does not.
