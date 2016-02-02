from distutils.core import setup
from distutils.extension import Extension
from Cython.Build import cythonize
import numpy

setup(
  ext_modules = cythonize([
      Extension("plover", ["plover.pyx"],
                include_dirs=[numpy.get_include()],
                libraries=["plover", "prelude"])])
)
