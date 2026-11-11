cmake_minimum_required(VERSION 4.0)

project(forsyde-skepu-tests LANGUAGES CXX)

find_package(SkePU HINTS /opt/skepu3/usr/local/lib/cmake)

set(srcpath "compiler-output")
file(GLOB paths "${srcpath}/*.cpp")
foreach(path ${paths})
	get_filename_component(name ${path} NAME_WE)
	get_filename_component(file ${path} NAME)
	skepu_add_executable(${name}_serial SKEPUSRC "${srcpath}/${file}")
	skepu_add_executable(${name}_omp OpenMP SKEPUSRC "${srcpath}/${file}")
	skepu_add_executable(${name}_ocl OpenCL SKEPUSRC "${srcpath}/${file}")
endforeach()
