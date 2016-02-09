from distutils.core import setup
from distutils.extension import Extension
from Cython.Build import cythonize
import numpy

extensions = [
      Extension("plover", ["plover.pyx"],
                include_dirs=[numpy.get_include()],
                libraries=["plover", "prelude", "qr"])]
setup(
  ext_modules = cythonize(extensions, gdb_debug=True)
)
