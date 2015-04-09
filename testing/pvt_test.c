#include "track.h"
#include "common.h"
#include "constants.h"
#include "linear_algebra.c"

void pvt(int n_used, double sat_pos[n_used][3], navigation_measurement_t nav_meas[n_used], double rx_state[3], double correction[4], double G[n_used][4], double X[4][n_used]);

static double pvt_solve(double rx_state[],
                        const u8 n_used,
                        const navigation_measurement_t nav_meas[n_used],
                        double correction[4])
{
  double H[4][4];
  double p_pred[n_used];

  /* Vector of prediction errors */
  double omp[n_used];

  /* G is a geometry matrix tells us how our pseudoranges relate to
   * our state estimates -- it's the Jacobian of d(p_i)/d(x_j) where
   * x_j are x, y, z, Δt. */
  double G[n_used][4];
  double Gtrans[4][n_used];
  double GtG[4][4];

  /* H is the square of the Jacobian matrix; it tells us the shape of
     our error (or, if you prefer, the direction in which we need to
     move to get a better solution) in terms of the receiver state. */

  /* X is just H * Gtrans -- it maps our pseudoranges onto our
   * Jacobian update */
  double X[4][n_used];

  double tempv[3];
  double los[3];
  double xk_new[3];
  double tempd;

  for (u8 j=0; j<4; j++) {
    correction[j] = 0.0;
  }

  for (u8 j = 0; j < n_used; j++) {
    /* The satellite positions need to be corrected for Earth's rotation during
     * the signal time of flight. */
    /* TODO: Explain more about how this corrects for the Sagnac effect. */

    /* Magnitude of range vector converted into an approximate time in secs. */
    vector_subtract(3, rx_state, nav_meas[j].sat_pos, tempv);
    double tau = vector_norm(3, tempv) / GPS_C;

    /* Rotation of Earth during time of flight in radians. */
    double wEtau = GPS_OMEGAE_DOT * tau;

    /* Apply linearlised rotation about Z-axis which will adjust for the
     * satellite's position at time t-tau. Note the rotation is through
     * -wEtau because it is the ECEF frame that is rotating with the Earth and
     * hence in the ECEF frame free falling bodies appear to rotate in the
     * opposite direction.
     *
     * Making a small angle approximation here leads to less than 1mm error in
     * the satellite position. */
    xk_new[0] = nav_meas[j].sat_pos[0] + wEtau * nav_meas[j].sat_pos[1];
    xk_new[1] = nav_meas[j].sat_pos[1] - wEtau * nav_meas[j].sat_pos[0];
    xk_new[2] = nav_meas[j].sat_pos[2];

    /* Line of sight vector. */
    vector_subtract(3, xk_new, rx_state, los);

    /* Predicted range from satellite position and estimated Rx position. */
    p_pred[j] = vector_norm(3, los);

    /* omp means "observed minus predicted" range -- this is E, the
     * prediction error vector (or innovation vector in Kalman/LS
     * filtering terms).
     */
    omp[j] = nav_meas[j].pseudorange - p_pred[j];

    /* Construct a geometry matrix.  Each row (satellite) is
     * independently normalized into a unit vector. */
    for (u8 i=0; i<3; i++) {
      G[j][i] = -los[i] / p_pred[j];
    }

    /* Set time covariance to 1. */
    G[j][3] = 1;

  } /* End of channel loop. */

  /* Solve for position corrections using batch least-squares.  When
   * all-at-once least-squares estimation for a nonlinear problem is
   * mixed with numerical iteration (not time-series recursion, but
   * iteration on a single set of measurements), it's basically
   * Newton's method.  There's a reasonably clear explanation of this
   * in Wikipedia's article on GPS.
   */

  /* Gt := G^{T} */
  matrix_transpose(n_used, 4, (double *) G, (double *) Gtrans);
  /* GtG := G^{T} G */
  matrix_multiply(4, n_used, 4, (double *) Gtrans, (double *) G, (double *) GtG);
  /* H \elem \mathbb{R}^{4 \times 4} := GtG^{-1} */
  matrix_inverse(4, (const double *) GtG, (double *) H);
  /* X := H * G^{T} */
  matrix_multiply(4, 4, n_used, (double *) H, (double *) Gtrans, (double *) X);
  /* correction := X * E (= X * omp) */
  matrix_multiply(4, n_used, 1, (double *) X, (double *) omp, (double *) correction);
}

void pvt2(int n_used, double sat_pos[n_used][3],
          navigation_measurement_t nav_meas[n_used], double rx_state[3],
          double correction[4], double *G, double *X)
{
  double H[4][4];
  //navigation_measurement_t nav_meas[n_used];
  //for (int i = 0; i < n_used; i++) {
  //  for (int x = 0; x < 3; x++) {
  //    nav_meas[i].sat_pos[x] = sat_pos[i][x];
  //  }
  //  nav_meas[i].pseudorange = pseudo[i];
  //}

  pvt_solve(rx_state, n_used, nav_meas, correction);
}
