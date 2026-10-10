#include "grids.hpp"
#include <boost/version.hpp>
int main() {
    std::cout << "CERTIFICATE BP=" << BP << " M=" << M
              << " BOOST=" << BOOST_LIB_VERSION
              << " OMP_MAX_THREADS=" << omp_get_max_threads() << std::endl;
    try { run_certificate(); }
    catch (const std::exception& err) {
        std::cerr << "CERTIFICATE ERROR: " << err.what() << std::endl;
        return 1;
    }
    return 0;
}
