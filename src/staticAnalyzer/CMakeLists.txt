add_library(PostgresChecker MODULE "")
target_compile_options(PostgresChecker PRIVATE -fno-rtti)
target_include_directories(PostgresChecker
    PRIVATE
        ${CLANG_INCLUDE_DIRS}
        ${LLVM_INCLUDE_DIRS}
)
target_sources(PostgresChecker PRIVATE ${CMAKE_CURRENT_LIST_DIR}/PostgresChecker.cpp)

install(TARGETS PostgresChecker DESTINATION lib)

