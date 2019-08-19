import os
import subprocess

from . import rtlil


__all__ = ["YosysError", "convert", "convert_fragment"]


class YosysError(Exception):
    pass


def _convert_il_text(il_text, strip_src):
    try:
        popen = subprocess.Popen([os.getenv("YOSYS", "yosys"), "-q", "-"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            encoding="utf-8")
    except FileNotFoundError as e:
        if os.getenv("YOSYS"):
            raise YosysError("Could not find Yosys in {} as specified via the YOSYS environment "
                             "variable".format(os.getenv("YOSYS"))) from e
        else:
            raise YosysError("Could not find Yosys in PATH. Place `yosys` in PATH or specify "
                             "path explicitly via the YOSYS environment variable") from e

    attr_map = []
    if strip_src:
        attr_map.append("-remove src")

    verilog_text, error = popen.communicate("""
# Convert nMigen's RTLIL to readable Verilog.
read_ilang <<rtlil
{}
rtlil
proc_prune
proc_init
proc_arst
proc_dff
proc_clean
memory_collect
attrmap {}
write_verilog -norename
""".format(il_text, " ".join(attr_map)))
    if popen.returncode:
        raise YosysError(error.strip())
    else:
        return verilog_text


def convert_fragment(*args, strip_src=False, **kwargs):
    il_text = rtlil.convert_fragment(*args, **kwargs)
    return _convert_il_text(il_text, strip_src)


def convert(*args, strip_src=False, **kwargs):
    il_text = rtlil.convert(*args, **kwargs)
    return _convert_il_text(il_text, strip_src)
