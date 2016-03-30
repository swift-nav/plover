cimport libc.stdlib
from libcpp cimport bool
from prelude cimport (u16, s32)

cdef extern from "plover_main.h":
  enum: MAX_STATE_DIM

  ctypedef struct gnss_signal_t:
      u16 sat
      u16 code

  ctypedef struct filter_state:
      s32 num_sats
      gnss_signal_t ref
      gnss_signal_t sats [MAX_STATE_DIM]
      bool invalid
      double x [MAX_STATE_DIM]
      double P [MAX_STATE_DIM * MAX_STATE_DIM]
      double sigma

  ctypedef struct measurement:
      double pseudoranges
      double carrier_phases
      double snr
      gnss_signal_t sat_id

cdef extern from "plover_main.c":
    void kalman_predict_ (const s32 dim, const double * x, const double * P, const double * F, const double * Q, double * x_new, double * P_new);
    void kalman_update_ (const s32 dim, const s32 dim, const double * x, const double * P, const double * y, const double * H, const double * R, double * x_new, double * P_new);

    s32 matrix_inverse (const s32 dim, const double * x, double * y);
    void print_all_ (const s32 dim, const double * innovation, const double * S, const double * Si, const double * K, const double * x_new, const double * P_new);
    void observation_model_ (const s32 sats, const double * pseudoranges, const double * carrier_phases, const double * x, const double * base_pos, const double * sat_positions, const double sig_cp, const double sig_pr, double * y, double * H, double * R);
    void sigtest (gnss_signal_t * const x);
