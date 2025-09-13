cmake_minimum_required(VERSION 3.20)
project(CA CXX)


set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# 👇 вот это добавь
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

include(FetchContent)

# === CPR (HTTP) ===
FetchContent_Declare(
  cpr
  GIT_REPOSITORY https://github.com/libcpr/cpr.git
  GIT_TAG 1.10.5
)
set(CPR_USE_SYSTEM_CURL OFF CACHE BOOL "" FORCE)
set(BUILD_CPR_TESTS OFF CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(cpr)

# === nlohmann/json (JSON-парсер) ===
FetchContent_Declare(
  json
  URL https://github.com/nlohmann/json/releases/download/v3.11.3/json.tar.xz
)
FetchContent_MakeAvailable(json)

add_executable(CA src/main.cpp)
target_link_libraries(CA PRIVATE cpr::cpr nlohmann_json::nlohmann_json)
