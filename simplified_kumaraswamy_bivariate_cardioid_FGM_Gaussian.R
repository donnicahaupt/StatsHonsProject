# =============================================================================
# KUMARASWAMY(beta, 2) BIVARIATE CARDIOID MODEL
# FGM AND GAUSSIAN COPULA DEPENDENCE
# =============================================================================
#
# PURPOSE
# -------
# This script investigates a parsimonious bivariate cardioid mixture model:
#
#   X_j ~ Kumaraswamy(beta_j, 2),        j = 1, 2
#   rho_j = X_j / 2,
#   Theta_j | X_j ~ Cardioid(mu_j, rho_j).
#
# Because 0 < X_j < 1, rho_j is automatically restricted to (0, 1/2), which
# is the admissible non-negative concentration range for the cardioid model.
# There is therefore NO additional free delta_j parameter.
#
# Dependence between X_1 and X_2 is introduced using either:
#
#   (1) the FGM copula, with lambda in [-1, 1], or
#   (2) the Gaussian copula, with correlation r in (-1, 1).
#
# Both copulas give the same observable angular form
#
# f(theta1, theta2)
#   = 1/(2*pi)^2 *
#     [1 + m1*c1 + m2*c2 + E(X1*X2)*c1*c2],
#
# where
#   m_j = E(X_j) = 2*beta_j^2 / [(beta_j + 1)(2*beta_j + 1)],
#   c_j = cos(theta_j - mu_j).
#
# The reduced/effective coefficients are
#   A = m1/2,
#   B = m2/2,
#   C = E(X1*X2)/4,
#   D = C - A*B = Cov(X1, X2)/4.
#
# For the FGM copula,
#   E(X1*X2) = m1*m2 + lambda*q1*q2,
# where
#   q(beta) = -2*beta^2*(7*beta + 1) /
#             [(beta + 1)(2*beta + 1)(3*beta + 1)(4*beta + 1)].
#
# For the Gaussian copula, E(X1*X2) is evaluated numerically using
# Gauss-Legendre quadrature.
#
# RECOMMENDED WORKFLOW
# --------------------
# 1. Run Sections 0-8 to define all functions.
# 2. Run Section 9 for single-dataset examples and MLE checks.
# 3. Run Section 10 for identifiability checks.
# 4. Run Sections 11-13 for dependence plots, heatmaps and torus plots.
# 5. Set RUN_SIMULATION_STUDY <- TRUE in Section 14 and rerun Sections 14-17.
# 6. Section 17 writes LaTeX tables that can be copied directly into Overleaf.
#
# The FGM model is retained as the baseline. The Gaussian copula is the main
# stronger-dependence extension.
#
# =============================================================================


# =============================================================================
# 0. PACKAGES AND USER SETTINGS
# =============================================================================

# Install once if required:
# install.packages(c("ggplot2", "plotly", "dplyr", "tidyr", "xtable", "reticulate"))

library(ggplot2)
library(plotly)
library(dplyr)
library(tidyr)
library(xtable)
library(reticulate)

# Numerical quadrature used for Gaussian-copula cross moments.
# Increasing this improves accuracy but slows estimation.
QUAD_N <- 45

# Reproducibility
BASE_SEED <- 2026



# =============================================================================
# Parameters: run either Simulation One or Simulation Two
# =============================================================================

#-------------------------
# Simulation One
#-------------------------

#Main marginal/location parameters used throughout the examples.
BETA1_TRUE <- 0.70
BETA2_TRUE <- 0.90
MU1_TRUE <- pi / 4
MU2_TRUE <- 5 * pi / 4

# FGM example:
# lambda is the raw FGM dependence parameter, restricted to [-1, 1].
FGM_LAMBDA_TRUE <- 0.90

# Gaussian example:
# We specify the dependence strength using Kendall's tau because it is easier
# to compare across copula families. The raw Gaussian parameter is r.
GAUSSIAN_TAU_TRUE <- (2/pi)*asin(0.9)

#-------------------------
# Simulation Two 
#-------------------------
# #Main marginal/location parameters used throughout the examples.
# BETA1_TRUE <- 0.5
# BETA2_TRUE <- 0.3
# MU1_TRUE <- pi / 2
# MU2_TRUE <- pi / 3
# 
# # FGM example:
# # lambda is the raw FGM dependence parameter, restricted to [-1, 1].
# FGM_LAMBDA_TRUE <- 0.7
# 
# # Gaussian example:
# # We specify the dependence strength using Kendall's tau because it is easier
# # to compare across copula families. The raw Gaussian parameter is r.
# GAUSSIAN_TAU_TRUE <- (2/pi)*asin(0.7)
#------------------------------------------------------------------------


# Single-dataset example size
EXAMPLE_N <- 500

# Simulation-study settings.
# Keep FALSE while developing/testing the code.
RUN_SIMULATION_STUDY <- TRUE

SIM_N_VALUES <- c(100, 250, 500, 1000, 2500, 5000, 10000)
SIM_B <- 200
SIM_N_STARTS <- 8


# =============================================================================
# 1. BASIC CIRCULAR UTILITIES
# =============================================================================

wrap_angle <- function(theta) {
  theta %% (2 * pi)
}


circular_mean <- function(theta) {
  wrap_angle(
    Arg(
      mean(
        exp(1i * theta),
        na.rm = TRUE
      )
    )
  )
}


# Signed shortest difference between two angles, in [-pi, pi].
circular_difference <- function(estimate, truth) {
  atan2(
    sin(estimate - truth),
    cos(estimate - truth)
  )
}


# Circular standard deviation. Useful for descriptive summaries of angle errors.
circular_sd <- function(theta) {

  R <- Mod(
    mean(
      exp(1i * theta),
      na.rm = TRUE
    )
  )

  R <- max(R, .Machine$double.eps)

  sqrt(-2 * log(R))
}


# =============================================================================
# 2. KUMARASWAMY(beta, 2) MARGINAL QUANTITIES
# =============================================================================
#
# If X ~ Kumaraswamy(beta, 2), then
#
#   f(x) = 2 * beta * x^(beta - 1) * (1 - x^beta),   0 < x < 1
#   F(x) = 1 - (1 - x^beta)^2
#   Q(u) = [1 - (1 - u)^(1/2)]^(1/beta)
#   E(X) = 2 * B(1 + 1/beta, 2)
#        = 2*beta^2 / [(beta + 1)(2*beta + 1)]
#
# The mean is strictly increasing in beta, since
#
#   dm/dbeta = (6*beta^2 + 4*beta) / (2*beta^2 + 3*beta + 1)^2 > 0,
#
# with m -> 0 as beta -> 0 and m -> 1 as beta -> infinity. Solving the
# quadratic 2(1 - m) beta^2 - 3 m beta - m = 0 for its positive root gives
#
#   beta = [3m + sqrt(m^2 + 8m)] / [4(1 - m)].
#
# This one-to-one mapping is central to structural identifiability.

# Density, CDF and quantile function of Kumaraswamy(beta, 2).
dkumaraswamy2 <- function(x, beta) {
  2 * beta * x^(beta - 1) * (1 - x^beta)
}


pkumaraswamy2 <- function(x, beta) {
  1 - (1 - x^beta)^2
}


# Numerically stable: 1 - sqrt(1 - u) = -expm1(0.5 * log1p(-u)).
qkumaraswamy2 <- function(u, beta) {
  (-expm1(0.5 * log1p(-u)))^(1 / beta)
}


m_kumaraswamy <- function(beta) {

  if (any(beta <= 0)) {
    stop("beta must be positive.")
  }

  2 * beta^2 /
    (
      (beta + 1) *
      (2 * beta + 1)
    )
}


beta_from_m <- function(m) {

  if (any(m <= 0 | m >= 1)) {
    stop("m must lie strictly between 0 and 1.")
  }

  (3 * m + sqrt(m^2 + 8 * m)) /
    (4 * (1 - m))
}


# FGM-specific dependence-transmission quantity:
#
# q(beta)
#   = E[X{1 - 2F(X)}]
#   = 2*E[X(1 - X^beta)^2] - E(X)
#   = -2*beta^2*(7*beta + 1) /
#     [(beta + 1)(2*beta + 1)(3*beta + 1)(4*beta + 1)].
#
# q(beta) is negative for beta > 0. Its magnitude determines how strongly
# the FGM parameter lambda survives into the observable angular density.

q_kumaraswamy <- function(beta) {

  if (any(beta <= 0)) {
    stop("beta must be positive.")
  }

  -2 * beta^2 * (7 * beta + 1) /
    (
      (beta + 1) *
      (2 * beta + 1) *
      (3 * beta + 1) *
      (4 * beta + 1)
    )
}


# Numerical check of the closed-form m(beta) and q(beta).
verify_kumaraswamy_moments <- function(beta) {

  m_numeric <- integrate(
    function(x) {
      x * dkumaraswamy2(x, beta)
    },
    lower = 0,
    upper = 1
  )$value

  q_numeric <- integrate(
    function(x) {
      x *
        (1 - 2 * pkumaraswamy2(x, beta)) *
        dkumaraswamy2(x, beta)
    },
    lower = 0,
    upper = 1
  )$value

  data.frame(
    beta = beta,
    m_closed = m_kumaraswamy(beta),
    m_numeric = m_numeric,
    q_closed = q_kumaraswamy(beta),
    q_numeric = q_numeric
  )
}


# Optional formula checks:
# verify_kumaraswamy_moments(0.7)
# verify_kumaraswamy_moments(1)
# verify_kumaraswamy_moments(2)


# =============================================================================
# 3. COPULA DEFINITIONS
# =============================================================================
#
# We use a common argument called "dep":
#
#   copula = "fgm"      -> dep = lambda, lambda in [-1, 1]
#   copula = "gaussian" -> dep = r,      r in (-1, 1)
#
# Kendall's tau:
#
#   FGM:      tau = 2*lambda/9, so |tau| <= 2/9.
#   Gaussian: tau = (2/pi) * asin(r), so |tau| < 1.
#
# This immediately illustrates why the Gaussian copula can represent much
# stronger latent dependence than the FGM copula.


# -----------------------------------------------------------------------------
# 3.1 FGM copula
# -----------------------------------------------------------------------------

# Exact simulation from the FGM copula on the uniform scale.
# Conditional on U = u,
#
#   P(V <= v | U = u)
#     = v + lambda*(1 - 2u)*v*(1 - v).
#
# The quadratic equation is inverted analytically.

rfgm_uniform <- function(n, lambda) {

  if (abs(lambda) > 1) {
    stop("For the FGM copula, lambda must lie in [-1, 1].")
  }

  u <- runif(n)
  w <- runif(n)

  a <- lambda * (1 - 2 * u)

  v <- numeric(n)

  independence_case <- abs(a) < 1e-12
  v[independence_case] <- w[independence_case]

  dependent_case <- !independence_case

  discriminant <-
    (1 + a[dependent_case])^2 -
    4 * a[dependent_case] * w[dependent_case]

  # Numerically stable form of the required quadratic root.
  v[dependent_case] <-
    2 * w[dependent_case] /
    (
      1 +
      a[dependent_case] +
      sqrt(pmax(discriminant, 0))
    )

  v <- pmin(pmax(v, 0), 1)

  data.frame(u = u, v = v)
}


fgm_tau <- function(lambda) {

  if (any(abs(lambda) > 1)) {
    stop("For the FGM copula, lambda must lie in [-1, 1].")
  }

  2 * lambda / 9
}


fgm_lambda_from_tau <- function(tau) {

  if (any(abs(tau) > 2 / 9)) {
    stop("FGM only permits |Kendall tau| <= 2/9.")
  }

  9 * tau / 2
}


# -----------------------------------------------------------------------------
# 3.2 Gaussian copula
# -----------------------------------------------------------------------------

dgaussian_copula <- function(u, v, r) {

  if (abs(r) >= 1) {
    stop("For the Gaussian copula, |r| must be less than 1.")
  }

  if (abs(r) < 1e-12) {
    return(rep(1, length(u)))
  }

  z1 <- qnorm(u)
  z2 <- qnorm(v)

  log_density <-
    -0.5 * log(1 - r^2) +
    (
      2 * r * z1 * z2 -
      r^2 * (z1^2 + z2^2)
    ) /
    (
      2 * (1 - r^2)
    )

  exp(log_density)
}


rgaussian_copula <- function(n, r) {

  if (abs(r) >= 1) {
    stop("For the Gaussian copula, |r| must be less than 1.")
  }

  z1 <- rnorm(n)

  z2 <-
    r * z1 +
    sqrt(1 - r^2) * rnorm(n)

  data.frame(
    u = pnorm(z1),
    v = pnorm(z2)
  )
}


gaussian_tau <- function(r) {

  if (any(abs(r) >= 1)) {
    stop("For the Gaussian copula, |r| must be less than 1.")
  }

  2 / pi * asin(r)
}


gaussian_r_from_tau <- function(tau) {

  if (any(abs(tau) >= 1)) {
    stop("For the Gaussian copula, |Kendall tau| must be less than 1.")
  }

  sin(pi * tau / 2)
}


# -----------------------------------------------------------------------------
# 3.3 Common copula helpers
# -----------------------------------------------------------------------------

dep_to_tau <- function(dep, copula = c("fgm", "gaussian")) {

  copula <- match.arg(copula)

  if (copula == "fgm") {
    return(fgm_tau(dep))
  }

  gaussian_tau(dep)
}


tau_to_dep <- function(tau, copula = c("fgm", "gaussian")) {

  copula <- match.arg(copula)

  if (copula == "fgm") {
    return(fgm_lambda_from_tau(tau))
  }

  gaussian_r_from_tau(tau)
}


copula_dep_bounds <- function(copula = c("fgm", "gaussian")) {

  copula <- match.arg(copula)

  if (copula == "fgm") {
    return(c(-0.999999, 0.999999))
  }

  # A computational bound; the theoretical Gaussian parameter is (-1, 1).
  c(-0.995, 0.995)
}


simulate_copula_uniforms <- function(
    n,
    dep,
    copula = c("fgm", "gaussian")) {

  copula <- match.arg(copula)

  if (copula == "fgm") {
    return(rfgm_uniform(n = n, lambda = dep))
  }

  rgaussian_copula(n = n, r = dep)
}


# =============================================================================
# 4. GAUSS-LEGENDRE QUADRATURE FOR THE GAUSSIAN CROSS MOMENT
# =============================================================================
#
# For the Gaussian copula,
#
#   E(X1*X2)
#     = double integral
#       Q_1(u) Q_2(v) c_r(u,v) du dv,
#
# where Q_j(u) = [1 - (1 - u)^(1/2)]^(1/beta_j) is the Kumaraswamy(beta_j, 2)
# quantile function. There is no simple elementary closed form, so we
# evaluate it accurately using two-dimensional Gauss-Legendre quadrature.

gauss_legendre <- function(n = 45) {

  if (n < 2) {
    stop("n must be at least 2.")
  }

  i <- seq_len(n - 1)

  off_diag <- i / sqrt(4 * i^2 - 1)

  J <- matrix(0, nrow = n, ncol = n)

  J[cbind(i, i + 1)] <- off_diag
  J[cbind(i + 1, i)] <- off_diag

  eig <- eigen(J, symmetric = TRUE)

  ord <- order(eig$values)

  nodes_standard <- eig$values[ord]
  weights_standard <- 2 * eig$vectors[1, ord]^2

  # Transform [-1, 1] to [0, 1].
  nodes <- (nodes_standard + 1) / 2
  weights <- weights_standard / 2

  list(
    nodes = nodes,
    weights = weights
  )
}


make_quad2 <- function(n = 45) {

  q <- gauss_legendre(n)

  grid <- expand.grid(
    u = q$nodes,
    v = q$nodes
  )

  weight_matrix <- outer(
    q$weights,
    q$weights
  )

  list(
    u = grid$u,
    v = grid$v,
    weights = as.vector(weight_matrix)
  )
}


quad_fit <- make_quad2(QUAD_N)


# =============================================================================
# 5. CROSS MOMENTS AND EFFECTIVE PARAMETERS A, B, C, D
# =============================================================================

# -----------------------------------------------------------------------------
# 5.1 FGM: closed-form cross moment
# -----------------------------------------------------------------------------

cross_moment_fgm <- function(beta1, beta2, lambda) {

  m1 <- m_kumaraswamy(beta1)
  m2 <- m_kumaraswamy(beta2)

  q1 <- q_kumaraswamy(beta1)
  q2 <- q_kumaraswamy(beta2)

  m1 * m2 + lambda * q1 * q2
}


# -----------------------------------------------------------------------------
# 5.2 Gaussian: numerical cross moment
# -----------------------------------------------------------------------------

cross_moment_gaussian <- function(
    beta1,
    beta2,
    r,
    quad = quad_fit) {

  if (abs(r) < 1e-12) {
    return(
      m_kumaraswamy(beta1) *
      m_kumaraswamy(beta2)
    )
  }

  x1 <- qkumaraswamy2(quad$u, beta1)
  x2 <- qkumaraswamy2(quad$v, beta2)

  copula_values <- dgaussian_copula(
    u = quad$u,
    v = quad$v,
    r = r
  )

  sum(
    quad$weights *
    x1 *
    x2 *
    copula_values
  )
}


# -----------------------------------------------------------------------------
# 5.3 Common cross-moment interface
# -----------------------------------------------------------------------------

cross_moment_kumaraswamy <- function(
    beta1,
    beta2,
    dep,
    copula = c("fgm", "gaussian"),
    quad = quad_fit) {

  copula <- match.arg(copula)

  if (copula == "fgm") {
    return(
      cross_moment_fgm(
        beta1 = beta1,
        beta2 = beta2,
        lambda = dep
      )
    )
  }

  cross_moment_gaussian(
    beta1 = beta1,
    beta2 = beta2,
    r = dep,
    quad = quad
  )
}


effective_parameters <- function(
    beta1,
    beta2,
    dep,
    copula = c("fgm", "gaussian"),
    quad = quad_fit) {

  copula <- match.arg(copula)

  m1 <- m_kumaraswamy(beta1)
  m2 <- m_kumaraswamy(beta2)

  EXY <- cross_moment_kumaraswamy(
    beta1 = beta1,
    beta2 = beta2,
    dep = dep,
    copula = copula,
    quad = quad
  )

  c(
    m1 = m1,
    m2 = m2,
    EXY = EXY,
    A = m1 / 2,
    B = m2 / 2,
    C = EXY / 4,
    D = (EXY - m1 * m2) / 4
  )
}


# Check Gaussian quadrature against Monte Carlo simulation.
verify_gaussian_cross_moment <- function(
    beta1,
    beta2,
    r,
    n_mc = 200000,
    seed = 123,
    quad = quad_fit) {

  set.seed(seed)

  uv <- rgaussian_copula(n = n_mc, r = r)

  x1 <- qkumaraswamy2(uv$u, beta1)
  x2 <- qkumaraswamy2(uv$v, beta2)

  quadrature <- cross_moment_gaussian(
    beta1 = beta1,
    beta2 = beta2,
    r = r,
    quad = quad
  )

  data.frame(
    beta1 = beta1,
    beta2 = beta2,
    r = r,
    quadrature = quadrature,
    monte_carlo = mean(x1 * x2),
    difference = mean(x1 * x2) - quadrature
  )
}


# =============================================================================
# 6. CARDIOID SIMULATION AND OBSERVED BIVARIATE DENSITY
# =============================================================================

# Observation-specific cardioid sampler.
#
# f(theta | mu, rho)
#   = [1 + 2*rho*cos(theta - mu)]/(2*pi),
# with 0 <= rho <= 1/2.
#
# Rejection sampling uses Uniform(0, 2*pi) as the proposal.

rcardioid_variable <- function(rho, mu) {

  n <- length(rho)

  if (length(mu) == 1) {
    mu <- rep(mu, n)
  }

  if (length(mu) != n) {
    stop("mu must have length 1 or the same length as rho.")
  }

  if (any(rho < 0 | rho > 0.5)) {
    stop("Every rho must lie in [0, 0.5].")
  }

  output <- numeric(n)
  remaining <- seq_len(n)

  while (length(remaining) > 0) {

    candidate <- runif(
      length(remaining),
      0,
      2 * pi
    )

    rho_current <- rho[remaining]
    mu_current <- mu[remaining]

    acceptance_probability <-
      (
        1 +
        2 *
        rho_current *
        cos(candidate - mu_current)
      ) /
      (
        1 +
        2 * rho_current
      )

    accepted <-
      runif(length(remaining)) <=
      acceptance_probability

    if (any(accepted)) {

      output[remaining[accepted]] <- candidate[accepted]
      remaining <- remaining[!accepted]
    }
  }

  output
}


# Complete hierarchical simulator.
#
# Step 1: simulate dependent uniforms from the chosen copula.
# Step 2: transform with Q_j(u) = [1 - (1 - u)^(1/2)]^(1/beta_j) to obtain
#         Kumaraswamy(beta_j, 2) latent variables.
# Step 3: set rho_j = X_j/2.
# Step 4: simulate the conditional cardioid angles.

rbiv_cardioid_kumaraswamy <- function(
    n,
    beta1,
    beta2,
    dep,
    mu1,
    mu2,
    copula = c("fgm", "gaussian")) {

  copula <- match.arg(copula)

  uv <- simulate_copula_uniforms(
    n = n,
    dep = dep,
    copula = copula
  )

  x1 <- qkumaraswamy2(uv$u, beta1)
  x2 <- qkumaraswamy2(uv$v, beta2)

  rho1 <- x1 / 2
  rho2 <- x2 / 2

  theta1 <- rcardioid_variable(
    rho = rho1,
    mu = mu1
  )

  theta2 <- rcardioid_variable(
    rho = rho2,
    mu = mu2
  )

  data.frame(
    theta1 = theta1,
    theta2 = theta2,
    x1 = x1,
    x2 = x2,
    rho1 = rho1,
    rho2 = rho2
  )
}


# Observable bivariate angular density.

dbiv_cardioid_kumaraswamy <- function(
    theta1,
    theta2,
    beta1,
    beta2,
    dep,
    mu1,
    mu2,
    copula = c("fgm", "gaussian"),
    quad = quad_fit,
    log = FALSE) {

  copula <- match.arg(copula)

  if (beta1 <= 0 || beta2 <= 0) {

    if (log) {
      return(rep(-Inf, max(length(theta1), length(theta2))))
    }

    return(rep(0, max(length(theta1), length(theta2))))
  }

  dep_bounds <- copula_dep_bounds(copula)

  if (dep < dep_bounds[1] || dep > dep_bounds[2]) {

    if (log) {
      return(rep(-Inf, max(length(theta1), length(theta2))))
    }

    return(rep(0, max(length(theta1), length(theta2))))
  }

  n <- max(length(theta1), length(theta2))

  theta1 <- rep_len(theta1, n)
  theta2 <- rep_len(theta2, n)

  effective <- effective_parameters(
    beta1 = beta1,
    beta2 = beta2,
    dep = dep,
    copula = copula,
    quad = quad
  )

  c1 <- cos(theta1 - mu1)
  c2 <- cos(theta2 - mu2)

  numerator <-
    1 +
    effective["m1"] * c1 +
    effective["m2"] * c2 +
    effective["EXY"] * c1 * c2

  density <- numerator / (2 * pi)^2

  if (log) {

    output <- rep(-Inf, n)

    valid <- density > 0 & is.finite(density)

    output[valid] <- log(density[valid])

    return(output)
  }

  pmax(density, 0)
}


# =============================================================================
# 7. MAXIMUM LIKELIHOOD ESTIMATION
# =============================================================================
#
# The same MLE machinery is used for both copulas.
#
# Estimated parameters:
#   beta1 > 0,
#   beta2 > 0,
#   dep     = lambda (FGM) or r (Gaussian),
#   mu1, mu2 in [0, 2*pi).
#
# Moment-based starting values are used first, followed by multiple random
# starts to reduce the chance of selecting a poor local optimum.


# -----------------------------------------------------------------------------
# 7.1 Moment-based starting values
# -----------------------------------------------------------------------------

moment_start_kumaraswamy <- function(
    data,
    copula = c("fgm", "gaussian"),
    quad = quad_fit) {

  copula <- match.arg(copula)

  resultant1 <- mean(exp(1i * data$theta1))
  resultant2 <- mean(exp(1i * data$theta2))

  mu1 <- wrap_angle(Arg(resultant1))
  mu2 <- wrap_angle(Arg(resultant2))

  # For the marginal cardioid,
  # |E(exp(i*Theta_j))| = A_j = m_j/2.
  m1_hat <- 2 * Mod(resultant1)
  m2_hat <- 2 * Mod(resultant2)

  m1_hat <- min(max(m1_hat, 0.02), 0.98)
  m2_hat <- min(max(m2_hat, 0.02), 0.98)

  beta1 <- beta_from_m(m1_hat)
  beta2 <- beta_from_m(m2_hat)

  # E[cos(Theta1-mu1) cos(Theta2-mu2)] = C = E(X1*X2)/4.
  C_hat <- mean(
    cos(data$theta1 - mu1) *
    cos(data$theta2 - mu2)
  )

  target_EXY <- 4 * C_hat

  dep_bounds <- copula_dep_bounds(copula)

  objective <- function(dep) {

    EXY <- cross_moment_kumaraswamy(
      beta1 = beta1,
      beta2 = beta2,
      dep = dep,
      copula = copula,
      quad = quad
    )

    (EXY - target_EXY)^2
  }

  dep_start <- optimize(
    objective,
    interval = dep_bounds
  )$minimum

  list(
    beta1 = beta1,
    beta2 = beta2,
    dep = dep_start,
    mu1 = mu1,
    mu2 = mu2
  )
}


# -----------------------------------------------------------------------------
# 7.2 Negative log likelihood
# -----------------------------------------------------------------------------

nll_kumaraswamy <- function(
    par,
    theta1,
    theta2,
    copula = c("fgm", "gaussian"),
    quad = quad_fit) {

  copula <- match.arg(copula)

  beta1 <- exp(par[1])
  beta2 <- exp(par[2])
  dep <- par[3]

  mu1 <- wrap_angle(par[4])
  mu2 <- wrap_angle(par[5])

  log_density <- dbiv_cardioid_kumaraswamy(
    theta1 = theta1,
    theta2 = theta2,
    beta1 = beta1,
    beta2 = beta2,
    dep = dep,
    mu1 = mu1,
    mu2 = mu2,
    copula = copula,
    quad = quad,
    log = TRUE
  )

  if (any(!is.finite(log_density))) {
    return(1e12)
  }

  -sum(log_density)
}


# -----------------------------------------------------------------------------
# 7.3 Multi-start MLE
# -----------------------------------------------------------------------------

fit_kumaraswamy_cardioid <- function(
    data,
    copula = c("fgm", "gaussian"),
    n_starts = 15,
    seed = 123,
    quad = quad_fit,
    beta_bounds = c(0.02, 30)) {

  copula <- match.arg(copula)

  dep_bounds <- copula_dep_bounds(copula)

  initial <- moment_start_kumaraswamy(
    data = data,
    copula = copula,
    quad = quad
  )

  lower <- c(
    log(beta_bounds[1]),
    log(beta_bounds[1]),
    dep_bounds[1],
    0,
    0
  )

  upper <- c(
    log(beta_bounds[2]),
    log(beta_bounds[2]),
    dep_bounds[2],
    2 * pi,
    2 * pi
  )

  base_start <- c(
    log(initial$beta1),
    log(initial$beta2),
    initial$dep,
    initial$mu1,
    initial$mu2
  )

  set.seed(seed)

  results <- vector("list", n_starts)
  fit_objects <- vector("list", n_starts)

  for (s in seq_len(n_starts)) {

    if (s == 1) {

      start <- base_start

    } else {

      start <- base_start

      start[1:2] <-
        start[1:2] +
        rnorm(2, mean = 0, sd = 0.5)

      start[3] <- runif(
        1,
        dep_bounds[1] * 0.9,
        dep_bounds[2] * 0.9
      )

      start[4] <- wrap_angle(
        initial$mu1 +
        runif(1, -0.7, 0.7)
      )

      start[5] <- wrap_angle(
        initial$mu2 +
        runif(1, -0.7, 0.7)
      )
    }

    start <- pmin(pmax(start, lower), upper)

    fit <- try(
      optim(
        par = start,
        fn = nll_kumaraswamy,
        theta1 = data$theta1,
        theta2 = data$theta2,
        copula = copula,
        quad = quad,
        method = "L-BFGS-B",
        lower = lower,
        upper = upper,
        control = list(
          maxit = 3000,
          factr = 1e7
        )
      ),
      silent = TRUE
    )

    if (
      !inherits(fit, "try-error") &&
      is.finite(fit$value)
    ) {

      beta1 <- exp(fit$par[1])
      beta2 <- exp(fit$par[2])
      dep <- fit$par[3]
      mu1 <- wrap_angle(fit$par[4])
      mu2 <- wrap_angle(fit$par[5])

      effective <- effective_parameters(
        beta1 = beta1,
        beta2 = beta2,
        dep = dep,
        copula = copula,
        quad = quad
      )

      results[[s]] <- data.frame(
        start = s,
        beta1 = beta1,
        beta2 = beta2,
        dep = dep,
        tau = dep_to_tau(dep, copula),
        mu1 = mu1,
        mu2 = mu2,
        A = unname(effective["A"]),
        B = unname(effective["B"]),
        C = unname(effective["C"]),
        D = unname(effective["D"]),
        nll = fit$value,
        logLik = -fit$value,
        convergence = fit$convergence
      )

      fit_objects[[s]] <- fit
    }
  }

  valid <- !vapply(results, is.null, logical(1))

  if (!any(valid)) {
    stop("No optimisation run succeeded.")
  }

  result_table <- do.call(
    rbind,
    results[valid]
  )

  fit_objects <- fit_objects[valid]

  ordering <- order(result_table$nll)

  result_table <- result_table[ordering, ]
  fit_objects <- fit_objects[ordering]

  best_fit <- fit_objects[[1]]

  hessian <- try(
    optimHess(
      par = best_fit$par,
      fn = nll_kumaraswamy,
      theta1 = data$theta1,
      theta2 = data$theta2,
      copula = copula,
      quad = quad
    ),
    silent = TRUE
  )

  list(
    best = result_table[1, ],
    all_fits = result_table,
    best_optim = best_fit,
    hessian = hessian,
    copula = copula,
    moment_start = initial
  )
}


# =============================================================================
# 8. IDENTIFIABILITY AND CONDITIONAL DEPENDENCE PROFILES
# =============================================================================

# Numerical Jacobian of a vector-valued function.
numerical_jacobian <- function(fun, x, step = 1e-5) {

  f0 <- fun(x)

  J <- matrix(
    0,
    nrow = length(f0),
    ncol = length(x)
  )

  for (j in seq_along(x)) {

    h <- step * max(1, abs(x[j]))

    xp <- x
    xm <- x

    xp[j] <- xp[j] + h
    xm[j] <- xm[j] - h

    J[, j] <-
      (
        fun(xp) -
        fun(xm)
      ) /
      (2 * h)
  }

  J
}


# Checks the local mapping
#
#   (beta1, beta2, dependence parameter) -> (A, B, C).
#
# Full numerical rank 3 is evidence of local identifiability at that point.

identifiability_check <- function(
    beta1,
    beta2,
    dep,
    copula = c("fgm", "gaussian"),
    quad = quad_fit) {

  copula <- match.arg(copula)

  mapping <- function(p) {

    effective <- effective_parameters(
      beta1 = p[1],
      beta2 = p[2],
      dep = p[3],
      copula = copula,
      quad = quad
    )

    unname(
      effective[c("A", "B", "C")]
    )
  }

  J <- numerical_jacobian(
    fun = mapping,
    x = c(beta1, beta2, dep)
  )

  singular_values <- svd(J)$d

  list(
    jacobian = J,
    singular_values = singular_values,
    rank = sum(
      singular_values >
      max(singular_values) * 1e-8
    ),
    condition_number =
      max(singular_values) /
      min(singular_values)
  )
}


# IMPORTANT:
# This is a CONDITIONAL dependence profile because beta1, beta2, mu1 and mu2
# are held fixed while the dependence parameter is varied. A full profile
# likelihood would re-estimate all nuisance parameters at every fixed dep.

profile_dependence_fixed_margins <- function(
    data,
    beta1,
    beta2,
    mu1,
    mu2,
    copula = c("fgm", "gaussian"),
    dep_grid,
    quad = quad_fit) {

  copula <- match.arg(copula)

  logLik <- vapply(
    dep_grid,
    function(dep) {

      sum(
        dbiv_cardioid_kumaraswamy(
          theta1 = data$theta1,
          theta2 = data$theta2,
          beta1 = beta1,
          beta2 = beta2,
          dep = dep,
          mu1 = mu1,
          mu2 = mu2,
          copula = copula,
          quad = quad,
          log = TRUE
        )
      )
    },
    numeric(1)
  )

  data.frame(
    dep = dep_grid,
    tau = vapply(
      dep_grid,
      dep_to_tau,
      numeric(1),
      copula = copula
    ),
    logLik = logLik,
    relative_logLik = logLik - max(logLik)
  )
}


# =============================================================================
# 9. SINGLE-DATASET EXAMPLES: SIMULATION AND MLE
# =============================================================================

# Convert the requested Gaussian Kendall tau to the raw Gaussian parameter r.
GAUSSIAN_R_TRUE <- gaussian_r_from_tau(GAUSSIAN_TAU_TRUE)

true_fgm <- list(
  beta1 = BETA1_TRUE,
  beta2 = BETA2_TRUE,
  dep = FGM_LAMBDA_TRUE,
  mu1 = MU1_TRUE,
  mu2 = MU2_TRUE
)

true_gaussian <- list(
  beta1 = BETA1_TRUE,
  beta2 = BETA2_TRUE,
  dep = GAUSSIAN_R_TRUE,
  mu1 = MU1_TRUE,
  mu2 = MU2_TRUE
)


cat("\n============================================================\n")
cat("TRUE EFFECTIVE PARAMETERS: FGM\n")
cat("============================================================\n")

print(
  effective_parameters(
    beta1 = true_fgm$beta1,
    beta2 = true_fgm$beta2,
    dep = true_fgm$dep,
    copula = "fgm"
  ),
  digits = 7
)


cat("\n============================================================\n")
cat("TRUE EFFECTIVE PARAMETERS: GAUSSIAN\n")
cat("============================================================\n")

print(
  effective_parameters(
    beta1 = true_gaussian$beta1,
    beta2 = true_gaussian$beta2,
    dep = true_gaussian$dep,
    copula = "gaussian"
  ),
  digits = 7
)


# Optional Gaussian quadrature validation.
# Run this once after changing QUAD_N.
#
# verify_gaussian_cross_moment(
#   beta1 = BETA1_TRUE,
#   beta2 = BETA2_TRUE,
#   r = GAUSSIAN_R_TRUE,
#   n_mc = 200000
# )


# -----------------------------------------------------------------------------
# 9.1 FGM single dataset
# -----------------------------------------------------------------------------

set.seed(BASE_SEED)

data_fgm <- rbiv_cardioid_kumaraswamy(
  n = EXAMPLE_N,
  beta1 = true_fgm$beta1,
  beta2 = true_fgm$beta2,
  dep = true_fgm$dep,
  mu1 = true_fgm$mu1,
  mu2 = true_fgm$mu2,
  copula = "fgm"
)

fit_fgm <- fit_kumaraswamy_cardioid(
  data = data_fgm,
  copula = "fgm",
  n_starts = 20,
  seed = 101
)

cat("\n============================================================\n")
cat("FGM SINGLE-DATASET MLE\n")
cat("============================================================\n")

print(fit_fgm$best, digits = 7)


# -----------------------------------------------------------------------------
# 9.2 Gaussian single dataset
# -----------------------------------------------------------------------------

set.seed(BASE_SEED)

data_gaussian <- rbiv_cardioid_kumaraswamy(
  n = EXAMPLE_N,
  beta1 = true_gaussian$beta1,
  beta2 = true_gaussian$beta2,
  dep = true_gaussian$dep,
  mu1 = true_gaussian$mu1,
  mu2 = true_gaussian$mu2,
  copula = "gaussian"
)

fit_gaussian <- fit_kumaraswamy_cardioid(
  data = data_gaussian,
  copula = "gaussian",
  n_starts = 20,
  seed = 102
)

cat("\n============================================================\n")
cat("GAUSSIAN SINGLE-DATASET MLE\n")
cat("============================================================\n")

print(fit_gaussian$best, digits = 7)


# -----------------------------------------------------------------------------
# 9.3 Simple recovery table for one fitted dataset
# -----------------------------------------------------------------------------

make_single_recovery_table <- function(
    fit,
    true_values) {

  copula <- fit$copula

  true_effective <- effective_parameters(
    beta1 = true_values$beta1,
    beta2 = true_values$beta2,
    dep = true_values$dep,
    copula = copula
  )

  truth <- c(
    beta1 = true_values$beta1,
    beta2 = true_values$beta2,
    dep = true_values$dep,
    tau = dep_to_tau(true_values$dep, copula),
    mu1 = true_values$mu1,
    mu2 = true_values$mu2,
    A = unname(true_effective["A"]),
    B = unname(true_effective["B"]),
    C = unname(true_effective["C"]),
    D = unname(true_effective["D"])
  )

  estimate <- c(
    beta1 = fit$best$beta1,
    beta2 = fit$best$beta2,
    dep = fit$best$dep,
    tau = fit$best$tau,
    mu1 = fit$best$mu1,
    mu2 = fit$best$mu2,
    A = fit$best$A,
    B = fit$best$B,
    C = fit$best$C,
    D = fit$best$D
  )

  error <- estimate - truth

  error["mu1"] <- circular_difference(
    estimate["mu1"],
    truth["mu1"]
  )

  error["mu2"] <- circular_difference(
    estimate["mu2"],
    truth["mu2"]
  )

  data.frame(
    parameter = names(truth),
    truth = as.numeric(truth),
    estimate = as.numeric(estimate),
    error = as.numeric(error),
    row.names = NULL
  )
}


single_recovery_fgm <- make_single_recovery_table(
  fit = fit_fgm,
  true_values = true_fgm
)

single_recovery_gaussian <- make_single_recovery_table(
  fit = fit_gaussian,
  true_values = true_gaussian
)

cat("\nFGM single-dataset recovery:\n")
print(single_recovery_fgm, digits = 6, row.names = FALSE)

cat("\nGaussian single-dataset recovery:\n")
print(single_recovery_gaussian, digits = 6, row.names = FALSE)


# =============================================================================
# 10. LOCAL IDENTIFIABILITY CHECKS
# =============================================================================

id_fgm <- identifiability_check(
  beta1 = true_fgm$beta1,
  beta2 = true_fgm$beta2,
  dep = true_fgm$dep,
  copula = "fgm"
)

id_gaussian <- identifiability_check(
  beta1 = true_gaussian$beta1,
  beta2 = true_gaussian$beta2,
  dep = true_gaussian$dep,
  copula = "gaussian"
)

cat("\n============================================================\n")
cat("LOCAL IDENTIFIABILITY CHECK: FGM\n")
cat("============================================================\n")
cat("Rank:", id_fgm$rank, "out of 3\n")
cat("Singular values:\n")
print(id_fgm$singular_values, digits = 7)
cat("Condition number:", id_fgm$condition_number, "\n")

cat("\n============================================================\n")
cat("LOCAL IDENTIFIABILITY CHECK: GAUSSIAN\n")
cat("============================================================\n")
cat("Rank:", id_gaussian$rank, "out of 3\n")
cat("Singular values:\n")
print(id_gaussian$singular_values, digits = 7)
cat("Condition number:", id_gaussian$condition_number, "\n")


# =============================================================================
# 11. DEPENDENCE TRANSMISSION: FGM VERSUS GAUSSIAN
# =============================================================================
#
# D = C - A*B = Cov(X1, X2)/4 is the part of the observable angular
# interaction that is attributable to latent dependence.
#
# FGM can only reach |tau| <= 2/9. The Gaussian copula can approach |tau| = 1.

make_dependence_transmission_data <- function(
    beta1 = BETA1_TRUE,
    beta2 = BETA2_TRUE) {

  # FGM range on Kendall's tau scale.
  tau_fgm <- seq(
    -2 / 9,
    2 / 9,
    length.out = 101
  )

  dep_fgm <- vapply(
    tau_fgm,
    tau_to_dep,
    numeric(1),
    copula = "fgm"
  )

  D_fgm <- vapply(
    dep_fgm,
    function(dep) {
      effective_parameters(
        beta1 = beta1,
        beta2 = beta2,
        dep = dep,
        copula = "fgm"
      )["D"]
    },
    numeric(1)
  )

  # Gaussian range.
  tau_gaussian <- seq(
    -0.85,
    0.85,
    length.out = 151
  )

  dep_gaussian <- vapply(
    tau_gaussian,
    tau_to_dep,
    numeric(1),
    copula = "gaussian"
  )

  D_gaussian <- vapply(
    dep_gaussian,
    function(dep) {
      effective_parameters(
        beta1 = beta1,
        beta2 = beta2,
        dep = dep,
        copula = "gaussian"
      )["D"]
    },
    numeric(1)
  )

  bind_rows(
    data.frame(
      tau = tau_fgm,
      D = as.numeric(D_fgm),
      copula = "FGM"
    ),
    data.frame(
      tau = tau_gaussian,
      D = as.numeric(D_gaussian),
      copula = "Gaussian"
    )
  )
}


dependence_transmission_data <- make_dependence_transmission_data()

dependence_transmission_data$copula <- factor(
  dependence_transmission_data$copula,
  levels = c("Gaussian", "FGM")
)


dependence_transmission_plot <- ggplot(
  dependence_transmission_data,
  aes(
    x = tau,
    y = D,
    linetype = copula,
    colour = copula
  )
) +
  geom_line(linewidth = 1) +
  geom_hline(
    yintercept = 0,
    linetype = "dotted"
  ) +
  scale_colour_manual(
    values = c("FGM" = "red", "Gaussian" = "black")   # <- choose colours here
  )+
  scale_linetype_manual(
    values = c("FGM" = "solid", "Gaussian" = "22")
  )+
  labs(
    title = "Transmission of latent copula dependence",
    subtitle = expression(
      beta[1] == 0.7 * "," ~ beta[2] == 0.9
    ),
    x = expression("Kendall's " * tau),
    y = expression(D == C - AB),
    linetype = "Copula",
    colour = "Copula"
  ) +
  theme_minimal()

print(dependence_transmission_plot)

# =============================================================================
# 12. HEATMAPS: FGM AND GAUSSIAN EXAMPLES
# =============================================================================

make_density_grid <- function(
    beta1,
    beta2,
    dep,
    mu1,
    mu2,
    copula = c("fgm", "gaussian"),
    grid_size = 180,
    quad = quad_fit) {
  
  copula <- match.arg(copula)
  
  theta1 <- seq(0, 2 * pi, length.out = grid_size)
  theta2 <- seq(0, 2 * pi, length.out = grid_size)
  
  grid <- expand.grid(
    theta1 = theta1,
    theta2 = theta2
  )
  
  grid$density <- dbiv_cardioid_kumaraswamy(
    theta1 = grid$theta1,
    theta2 = grid$theta2,
    beta1 = beta1,
    beta2 = beta2,
    dep = dep,
    mu1 = mu1,
    mu2 = mu2,
    copula = copula,
    quad = quad
  )
  
  grid
}


# =============================================================================
# 12.1 COLOUR SCALE AND CONTOUR SETTINGS
# =============================================================================

# heatmap_colours <- c(
#   "#ffffcc",
#   "#ffeda0",
#   "#fed976",
#   "#feb24c",
#   "#fd8d3c",
#   "#f03b20",
#   "#bd0026"
# )

# colours <- list(
#   list(0.00, "#0d0887"),
#   list(0.18, "#6a00a8"),
#   list(0.36, "#b12a90"),
#   list(0.54, "#e16462"),
#   list(0.72, "#fca636"),
#   list(0.88, "#f0f921"),
#   list(1.00, "#fcffa4")
# )

# colours <- list(
#   list(0.00, "#000004"),
#   list(0.15, "#2c115f"),
#   list(0.32, "#721f81"),
#   list(0.50, "#b73779"),
#   list(0.68, "#f1605d"),
#   list(0.85, "#feb078"),
#   list(1.00, "#fcfdbf")
# )

#FGM_HEATMAP_LAMBDAS <- c(0, 0.3, 0.6, 0.9)
FGM_HEATMAP_LAMBDAS <- c(-0.9, -0.3, 0.5, 0.8)

#GAUSSIAN_HEATMAP_TAUS <- c(0, 0.3, 0.6, 0.8)
GAUSSIAN_HEATMAP_TAUS <- c(-0.9, -0.3, 0.5, 0.8)


# =============================================================================
# 12.2 GENERATE ALL DENSITY GRIDS
# =============================================================================

fgm_grids <- lapply(
  FGM_HEATMAP_LAMBDAS,
  function(lambda_value) {
    
    make_density_grid(
      beta1 = BETA1_TRUE,
      beta2 = BETA2_TRUE,
      dep = lambda_value,
      mu1 = MU1_TRUE,
      mu2 = MU2_TRUE,
      copula = "fgm"
    )
  }
)

gaussian_grids <- lapply(
  GAUSSIAN_HEATMAP_TAUS,
  function(tau_value) {
    
    make_density_grid(
      beta1 = BETA1_TRUE,
      beta2 = BETA2_TRUE,
      dep = gaussian_r_from_tau(tau_value),
      mu1 = MU1_TRUE,
      mu2 = MU2_TRUE,
      copula = "gaussian"
    )
  }
)


# =============================================================================
# 12.3 COMMON DENSITY SCALE AND CONTOUR LEVELS
# =============================================================================

all_grids <- c(fgm_grids, gaussian_grids)

all_densities <- unlist(
  lapply(all_grids, function(z) z$density)
)

density_limits <- range(all_densities, finite = TRUE)

density_contours <- seq(
  density_limits[1],
  density_limits[2],
  length.out = 9
)

density_contours <- density_contours[
  -c(1, length(density_contours))
]


# =============================================================================
# 12.4 HEATMAP FUNCTION WITH CONTOUR LINES
# =============================================================================

plot_density_heatmap <- function(
    grid,
    title,
    subtitle = NULL,
    angle_data = NULL,
    max_points = 300,
    density_limits = range(grid$density, finite = TRUE),
    contour_breaks = NULL) {
  
  if (is.null(contour_breaks)) {
    
    contour_breaks <- seq(
      density_limits[1],
      density_limits[2],
      length.out = 9
    )
    
    contour_breaks <- contour_breaks[
      -c(1, length(contour_breaks))
    ]
  }
  
  p <- ggplot(
    grid,
    aes(x = theta1, y = theta2)
  ) +
    geom_raster(aes(fill = density)) +
    
    geom_contour(
      aes(z = density),
      breaks = contour_breaks,
      colour = "white",
      linewidth = 0.75,
      alpha = 0.85
    ) +
    
    geom_contour(
      aes(z = density),
      breaks = contour_breaks,
      colour = "#292929",
      linewidth = 0.30,
      alpha = 0.9
    ) +
    
    # scale_fill_gradientn(
    #   colours = heatmap_colours,
    #   limits = density_limits,
    #   name = "Density"
    # ) +
    scale_fill_viridis_c() +
    
    scale_x_continuous(
      breaks = c(0, pi, 2 * pi),
      labels = c("0", "\u03c0", "2\u03c0"),
      limits = c(0, 2 * pi),
      expand = c(0, 0)
    ) +
    
    scale_y_continuous(
      breaks = c(0, pi, 2 * pi),
      labels = c("0", "\u03c0", "2\u03c0"),
      limits = c(0, 2 * pi),
      expand = c(0, 0)
    ) +
    
    coord_equal() +
    
    labs(
      title = title,
      subtitle = subtitle,
      x = expression(theta[1]),
      y = expression(theta[2])
    ) +
    
    theme_minimal(base_size = 12) +
    
    theme(
      panel.grid = element_blank(),
      panel.border = element_rect(
        colour = "grey30",
        fill = NA,
        linewidth = 0.4
      ),
      plot.title = element_text(
        face = "bold",
        size = 12
      ),
      legend.position = "right"
    )
  
  if (!is.null(angle_data)) {
    
    point_data <- angle_data
    
    if (is.finite(max_points) &&
        nrow(point_data) > max_points) {
      
      point_data <- point_data[
        sample(seq_len(nrow(point_data)), max_points),
        ,
        drop = FALSE
      ]
    }
    
    p <- p +
      geom_point(
        data = point_data,
        aes(x = theta1, y = theta2),
        inherit.aes = FALSE,
        colour = "black",
        size = 0.65,
        alpha = 0.35
      )
  }
  
  p
}


# =============================================================================
# 12.5 FOUR-PANEL COMPARISON FUNCTION
# =============================================================================

plot_four_heatmaps <- function(
    grids,
    panel_labels,
    title,
    density_limits,
    contour_breaks) {
  
  combined <- do.call(
    rbind,
    lapply(seq_along(grids), function(i) {
      
      z <- grids[[i]]
      
      z$panel <- panel_labels[i]
      
      z
    })
  )
  
  combined$panel <- factor(
    combined$panel,
    levels = panel_labels
  )
  
  ggplot(
    combined,
    aes(x = theta1, y = theta2)
  ) +
    geom_raster(aes(fill = density)) +
    
    geom_contour(
      aes(z = density),
      breaks = contour_breaks,
      colour = "white",
      linewidth = 0.75,
      alpha = 0.85
    ) +
    
    geom_contour(
      aes(z = density),
      breaks = contour_breaks,
      colour = "#292929",
      linewidth = 0.30,
      alpha = 0.9
    ) +
    
    facet_wrap(~panel, nrow = 2, ncol = 2) +
    
    scale_fill_viridis_c() + 
    
    scale_x_continuous(
      breaks = c(0, pi, 2 * pi),
      labels = c("0", "\u03c0", "2\u03c0"),
      limits = c(0, 2 * pi),
      expand = c(0, 0)
    ) +
    
    scale_y_continuous(
      breaks = c(0, pi, 2 * pi),
      labels = c("0", "\u03c0", "2\u03c0"),
      limits = c(0, 2 * pi),
      expand = c(0, 0)
    ) +
    
    coord_equal() +
    
    labs(
      title = title,
      x = expression(theta[1]),
      y = expression(theta[2])
    ) +
    
    theme_minimal(base_size = 12) +
    
    theme(
      panel.grid = element_blank(),
      panel.border = element_rect(
        colour = "grey30",
        fill = NA,
        linewidth = 0.4
      ),
      strip.text = element_text(
        face = "bold",
        size = 11
      ),
      plot.title = element_text(
        face = "bold",
        size = 13
      ),
      legend.position = "right"
    )
}


# =============================================================================
# 12.6 FGM HEATMAPS
# =============================================================================

fgm_labels <- paste0(
  "\u03bb = ",
  FGM_HEATMAP_LAMBDAS,
  "; \u03c4 = ",
  round(fgm_tau(FGM_HEATMAP_LAMBDAS), 3)
)

heatmap_fgm <- plot_four_heatmaps(
  grids = fgm_grids,
  panel_labels = fgm_labels,
  title = "FGM-copula Kumaraswamy cardioid",
  density_limits = density_limits,
  contour_breaks = density_contours
)

print(heatmap_fgm)

ggsave(
  "FGM_heatmaps_contours.pdf",
  heatmap_fgm,
  width = 8.5,
  height = 8
)



# =============================================================================
# 12.7 GAUSSIAN HEATMAPS
# =============================================================================

gaussian_labels <- paste0(
  "\u03c4 = ",
  GAUSSIAN_HEATMAP_TAUS,
  "; r = ",
  round(
    gaussian_r_from_tau(GAUSSIAN_HEATMAP_TAUS),
    3
  )
)

heatmap_gaussian <- plot_four_heatmaps(
  grids = gaussian_grids,
  panel_labels = gaussian_labels,
  title = "Gaussian-copula Kumaraswamy cardioid",
  density_limits = density_limits,
  contour_breaks = density_contours
)

print(heatmap_gaussian)

ggsave(
  "Gaussian_heatmaps_contours.pdf",
  heatmap_gaussian,
  width = 8.5,
  height = 8
)

# # =============================================================================
# # 13. TOROIDAL DENSITY PLOTS
# # =============================================================================

torus_density_plot <- function(
    beta1,
    beta2,
    dep,
    mu1,
    mu2,
    copula = c("fgm", "gaussian"),
    R = 2.2,
    r_minor = 0.8,
    n1 = 120,
    n2 = 90,
    quad = quad_fit,
    density_limits = NULL,
    camera = list(
      eye    = list(x = 0, y = 0, z = 2.5),
      up = list(x = 0, y = 0, z = 1)
    ),
    show_colourbar = TRUE) {
  
  copula <- match.arg(copula)
  
  theta1 <- seq(0, 2 * pi, length.out = n1)
  theta2 <- seq(0, 2 * pi, length.out = n2)
  
  T1 <- matrix(
    rep(theta1, times = n2),
    nrow = n1,
    ncol = n2
  )
  
  T2 <- matrix(
    rep(theta2, each = n1),
    nrow = n1,
    ncol = n2
  )
  
  X <- (R + r_minor * cos(T2)) * cos(T1)
  Y <- (R + r_minor * cos(T2)) * sin(T1)
  Z <- r_minor * sin(T2)
  
  density <- matrix(
    dbiv_cardioid_kumaraswamy(
      theta1 = as.vector(T1),
      theta2 = as.vector(T2),
      beta1 = beta1,
      beta2 = beta2,
      dep = dep,
      mu1 = mu1,
      mu2 = mu2,
      copula = copula,
      quad = quad
    ),
    nrow = n1,
    ncol = n2
  )
  
  if (is.null(density_limits)) {
    density_limits <- range(density, finite = TRUE)
  }
  
  
  plot_ly(
    x = X,
    y = Y,
    z = Z,
    surfacecolor = density,
    type = "surface",
    colorscale = "Viridis",
    cmin = density_limits[1],
    cmax = density_limits[2],
    showscale = show_colourbar,
    colorbar = list(
      title = list(text = "Density"),
      len = 0.65,
      thickness = 15
    ),
    hoverinfo = "skip"
  ) |>
    layout(
      scene = list(
        camera = camera,
        aspectmode = "data",
        xaxis = list(visible = FALSE),
        yaxis = list(visible = FALSE),
        zaxis = list(visible = FALSE)
      ),
      margin = list(
        l = 0, r = 0, b = 0, t = 0
      )
    )
}



# =============================================================================
# 13.1 TORUS PLOTS FOR ALL DEPENDENCE SCENARIOS
# =============================================================================

torus_camera <- list(
  eye    = list(x = 0, y = 0, z = 2.5),
  up = list(x = 0, y = 0, z = 1)
)

fgm_torus_plots <- lapply(
  seq_along(FGM_HEATMAP_LAMBDAS),
  function(i) {
    
    torus_density_plot(
      beta1 = BETA1_TRUE,
      beta2 = BETA2_TRUE,
      dep = FGM_HEATMAP_LAMBDAS[i],
      mu1 = MU1_TRUE,
      mu2 = MU2_TRUE,
      copula = "fgm",
      density_limits = density_limits,
      camera = torus_camera,
      show_colourbar = FALSE
    )
  }
)

gaussian_torus_plots <- lapply(
  seq_along(GAUSSIAN_HEATMAP_TAUS),
  function(i) {
    
    torus_density_plot(
      beta1 = BETA1_TRUE,
      beta2 = BETA2_TRUE,
      dep = gaussian_r_from_tau(
        GAUSSIAN_HEATMAP_TAUS[i]
      ),
      mu1 = MU1_TRUE,
      mu2 = MU2_TRUE,
      copula = "gaussian",
      density_limits = density_limits,
      camera = torus_camera,
      show_colourbar = FALSE
    )
  }
)


# =============================================================================
# 13.2 COMBINED TORUS FIGURES WITH FOUR INDEPENDENT 3D SCENES
# =============================================================================

plot_four_tori <- function(
    grids,
    panel_labels,
    title,
    density_limits,
    R = 2.2,
    r_minor = 0.8) {
  
  camera <- list(
    eye    = list(x = 0, y = 0, z = 2.5),
    up = list(x = 0, y = 0, z = 1),
    center = list(x = 0, y = 0, z = 0)
  )
  
  scene_names <- c(
    "scene", "scene2", "scene3", "scene4"
  )
  
  domains <- list(
    list(x = c(0.00, 0.47), y = c(0.54, 0.97)),
    list(x = c(0.53, 1.00), y = c(0.54, 0.97)),
    list(x = c(0.00, 0.47), y = c(0.04, 0.47)),
    list(x = c(0.53, 1.00), y = c(0.04, 0.47))
  )
  
  p <- plotly::plot_ly()
  
  scene_layouts <- list()
  annotations <- list()
  
  for (i in seq_len(4)) {
    
    grid <- grids[[i]]
    
    theta1 <- sort(unique(grid$theta1))
    theta2 <- sort(unique(grid$theta2))
    
    n1 <- length(theta1)
    n2 <- length(theta2)
    
    T1 <- matrix(
      rep(theta1, times = n2),
      nrow = n1,
      ncol = n2
    )
    
    T2 <- matrix(
      rep(theta2, each = n1),
      nrow = n1,
      ncol = n2
    )
    
    X <- (R + r_minor * cos(T2)) * cos(T1)
    Y <- (R + r_minor * cos(T2)) * sin(T1)
    Z <- r_minor * sin(T2)
    
    density <- matrix(
      grid$density,
      nrow = n1,
      ncol = n2
    )
    
    p <- plotly::add_surface(
      p,
      x = X,
      y = Y,
      z = Z,
      surfacecolor = density,
      scene = scene_names[i],
      colorscale = "Viridis",
      cmin = density_limits[1],
      cmax = density_limits[2],
      showscale = (i == 4),
      colorbar = list(
        title = list(text = "Density"),
        len = 0.40,
        thickness = 15,
        x = 1.03,
        y = 0.25
      ),
      hoverinfo = "skip",
      lighting = list(
        ambient = 0.85,
        diffuse = 0.6,
        specular = 0.05
      )
    )
    
    scene_layouts[[scene_names[i]]] <- list(
      domain = domains[[i]],
      camera = camera,
      aspectmode = "data",
      xaxis = list(visible = FALSE),
      yaxis = list(visible = FALSE),
      zaxis = list(visible = FALSE)
    )
    
    annotations[[i]] <- list(
      x = mean(domains[[i]]$x),
      y = domains[[i]]$y[2] + 0.015,
      xref = "paper",
      yref = "paper",
      text = panel_labels[i],
      showarrow = FALSE,
      font = list(size = 15, color = "black")
    )
  }
  
  layout_args <- c(
    list(
      p,
      title = list(text = title),
      annotations = annotations,
      showlegend = FALSE,
      width = 1100,
      height = 950,
      margin = list(
        l = 15, r = 65, b = 10, t = 85
      )
    ),
    scene_layouts
  )
  
  do.call(plotly::layout, layout_args)
}


# =============================================================================
# 13.3 GENERATE THE COMBINED FIGURES
# =============================================================================

fgm_torus_combined <- plot_four_tori(
  grids = fgm_grids,
  panel_labels = fgm_labels,
  title = "FGM-copula Kumaraswamy cardioid",
  density_limits = density_limits
)

gaussian_torus_combined <- plot_four_tori(
  grids = gaussian_grids,
  panel_labels = gaussian_labels,
  title = "Gaussian-copula Kumaraswamy cardioid",
  density_limits = density_limits
)

print(fgm_torus_combined)
print(gaussian_torus_combined)


# =============================================================================
# 13.4 SAVE INTERACTIVE HTML FILES
# =============================================================================

htmlwidgets::saveWidget(
  fgm_torus_combined,
  "kum_FGM_torus_comparison.html",
  selfcontained = TRUE
)

htmlwidgets::saveWidget(
  gaussian_torus_combined,
  "kum_Gaussian_torus_comparison.html",
  selfcontained = TRUE
)


# =============================================================================
# 13.5 SAVE STATIC FIGURES FOR THE THESIS
# =============================================================================
reticulate::py_install('plotly')
reticulate::py_install('kaleido')


plotly::save_image(
  fgm_torus_combined,
  "kum_FGM_torus_comparison.png",
  width = 1100,
  height = 950,
  scale = 2
)

plotly::save_image(
  gaussian_torus_combined,
  "kum_Gaussian_torus_comparison.png",
  width = 1100,
  height = 950,
  scale = 2
)

# =============================================================================
# 14. MONTE CARLO PARAMETER-RECOVERY STUDY
# =============================================================================
#
# The function below works for either copula and stores:
#
#   beta1, beta2, dep, tau, mu1, mu2, A, B, C, D
#
# for every successful fit.
#
# IMPORTANT:
# The Gaussian model is much slower than the FGM model because the Gaussian
# cross moment is evaluated numerically inside the likelihood.
#
# For code development:
#   B = 20 or 30
#
# For final reported results:
#   B >= 100 is preferable if computation time permits.

run_recovery_study <- function(
    copula = c("fgm", "gaussian"),
    true_values,
    n_values = c(100, 250, 500, 1000, 2500),
    B = 50,
    n_starts = 8,
    seed = 2026,
    quad = quad_fit) {

  copula <- match.arg(copula)

  set.seed(seed)

  results <- list()
  counter <- 1

  true_tau <- dep_to_tau(
    true_values$dep,
    copula
  )

  for (n in n_values) {

    for (b in seq_len(B)) {

      simulated <- rbiv_cardioid_kumaraswamy(
        n = n,
        beta1 = true_values$beta1,
        beta2 = true_values$beta2,
        dep = true_values$dep,
        mu1 = true_values$mu1,
        mu2 = true_values$mu2,
        copula = copula
      )

      fit <- try(
        fit_kumaraswamy_cardioid(
          data = simulated,
          copula = copula,
          n_starts = n_starts,
          seed = seed + 10000 * n + b,
          quad = quad
        ),
        silent = TRUE
      )

      if (!inherits(fit, "try-error")) {

        results[[counter]] <- data.frame(
          n = n,
          replication = b,
          beta1 = fit$best$beta1,
          beta2 = fit$best$beta2,
          dep = fit$best$dep,
          tau = fit$best$tau,
          mu1 = fit$best$mu1,
          mu2 = fit$best$mu2,
          A = fit$best$A,
          B = fit$best$B,
          C = fit$best$C,
          D = fit$best$D,
          true_tau = true_tau,
          convergence = fit$best$convergence
        )

        counter <- counter + 1
      }

      message(
        toupper(copula),
        ": n = ",
        n,
        ", replication ",
        b,
        " of ",
        B
      )
    }
  }

  if (length(results) == 0) {
    stop("No simulation fits succeeded.")
  }

  do.call(rbind, results)
}


# -----------------------------------------------------------------------------
# 14.1 Run the simulation studies
# -----------------------------------------------------------------------------

if (RUN_SIMULATION_STUDY) {

  recovery_fgm <- run_recovery_study(
    copula = "fgm",
    true_values = true_fgm,
    n_values = SIM_N_VALUES,
    B = SIM_B,
    n_starts = SIM_N_STARTS,
    seed = BASE_SEED
  )

  recovery_gaussian <- run_recovery_study(
    copula = "gaussian",
    true_values = true_gaussian,
    n_values = SIM_N_VALUES,
    B = SIM_B,
    n_starts = SIM_N_STARTS,
    seed = BASE_SEED
  )
}


# =============================================================================
# 15. FULL RECOVERY SUMMARIES
# =============================================================================
#
# Circular errors are used for mu1 and mu2.
#
# For each parameter and n we report:
#   truth,
#   mean estimate,
#   bias,
#   SD,
#   MSE,
#   RMSE,
#   number of successful fits.
#
# A, B, C and D are stored directly in the simulation output. Using unname()
# for their true values prevents the old "A.A", "B.B", "C.C", "D.D" naming bug.

summarise_full_recovery <- function(
    recovery_results,
    true_values,
    copula = c("fgm", "gaussian"),
    quad = quad_fit) {

  copula <- match.arg(copula)

  true_effective <- effective_parameters(
    beta1 = true_values$beta1,
    beta2 = true_values$beta2,
    dep = true_values$dep,
    copula = copula,
    quad = quad
  )

  truth <- c(
    beta1 = true_values$beta1,
    beta2 = true_values$beta2,
    dep = true_values$dep,
    tau = dep_to_tau(true_values$dep, copula),
    mu1 = true_values$mu1,
    mu2 = true_values$mu2,
    A = unname(true_effective["A"]),
    B = unname(true_effective["B"]),
    C = unname(true_effective["C"]),
    D = unname(true_effective["D"])
  )

  parameter_order <- c(
    "beta1",
    "beta2",
    "dep",
    "tau",
    "mu1",
    "mu2",
    "A",
    "B",
    "C",
    "D"
  )

  n_values <- sort(unique(recovery_results$n))

  output <- list()
  index <- 1

  for (n_value in n_values) {

    current <- recovery_results[
      recovery_results$n == n_value,
    ]

    for (parameter in parameter_order) {

      estimates <- current[[parameter]]
      true_value <- unname(truth[parameter])

      if (parameter %in% c("mu1", "mu2")) {

        errors <- circular_difference(
          estimates,
          true_value
        )

        mean_estimate <- circular_mean(estimates)

        bias <- circular_difference(
          mean_estimate,
          true_value
        )

        sd_value <- sd(
          errors,
          na.rm = TRUE
        )

        mse <- mean(
          errors^2,
          na.rm = TRUE
        )

      } else {

        errors <- estimates - true_value

        mean_estimate <- mean(
          estimates,
          na.rm = TRUE
        )

        bias <- mean(
          errors,
          na.rm = TRUE
        )

        sd_value <- sd(
          estimates,
          na.rm = TRUE
        )

        mse <- mean(
          errors^2,
          na.rm = TRUE
        )
      }

      output[[index]] <- data.frame(
        n = n_value,
        parameter = parameter,
        truth = true_value,
        mean_estimate = mean_estimate,
        bias = bias,
        SD = sd_value,
        MSE = mse,
        RMSE = sqrt(mse),
        successful_fits = sum(is.finite(estimates))
      )

      index <- index + 1
    }
  }

  output <- do.call(rbind, output)
  rownames(output) <- NULL

  output
}


# Dependence-boundary diagnostics.
#
# Boundary pile-up is important because a weakly informed dependence parameter
# often leads to estimates at the edge of the admissible parameter space.

summarise_dependence_boundaries <- function(
    recovery_results,
    copula = c("fgm", "gaussian"),
    tolerance = 1e-4) {

  copula <- match.arg(copula)

  bounds <- copula_dep_bounds(copula)

  n_values <- sort(
    unique(recovery_results$n)
  )

  output <- lapply(
    n_values,
    function(n_value) {

      current <- recovery_results[
        recovery_results$n == n_value,
      ]

      true_tau <- unique(current$true_tau)[1]

      data.frame(
        n = n_value,
        number_fits = nrow(current),
        lower_boundary = mean(
          current$dep <= bounds[1] + tolerance
        ),
        upper_boundary = mean(
          current$dep >= bounds[2] - tolerance
        ),
        either_boundary = mean(
          current$dep <= bounds[1] + tolerance |
          current$dep >= bounds[2] - tolerance
        ),
        correct_sign = mean(
          sign(current$tau) ==
          sign(true_tau)
        )
      )
    }
  )

  do.call(rbind, output)
}


# -----------------------------------------------------------------------------
# 15.1 Build summaries after running the simulation study
# -----------------------------------------------------------------------------

if (RUN_SIMULATION_STUDY) {

  summary_fgm <- summarise_full_recovery(
    recovery_results = recovery_fgm,
    true_values = true_fgm,
    copula = "fgm"
  )

  summary_gaussian <- summarise_full_recovery(
    recovery_results = recovery_gaussian,
    true_values = true_gaussian,
    copula = "gaussian"
  )

  boundary_fgm <- summarise_dependence_boundaries(
    recovery_results = recovery_fgm,
    copula = "fgm"
  )

  boundary_gaussian <- summarise_dependence_boundaries(
    recovery_results = recovery_gaussian,
    copula = "gaussian"
  )

  cat("\n============================================================\n")
  cat("FGM RECOVERY SUMMARY\n")
  cat("============================================================\n")
  print(summary_fgm, digits = 6, row.names = FALSE)

  cat("\n============================================================\n")
  cat("GAUSSIAN RECOVERY SUMMARY\n")
  cat("============================================================\n")
  print(summary_gaussian, digits = 6, row.names = FALSE)

  cat("\nFGM dependence-boundary diagnostics:\n")
  print(boundary_fgm, digits = 5, row.names = FALSE)

  cat("\nGaussian dependence-boundary diagnostics:\n")
  print(boundary_gaussian, digits = 5, row.names = FALSE)
}

# =============================================================================
# HELPER: parameter label lookups for plot facets
# =============================================================================

param_labeller <- function(copula = c("fgm", "gaussian")) {
  copula <- match.arg(copula)
  dep_label <- if (copula == "fgm") "lambda" else "r"
  c(
    beta1 = "beta[1]",
    beta2 = "beta[2]",
    dep    = dep_label,
    tau    = "tau",
    mu1    = "mu[1]",
    mu2    = "mu[2]",
    A      = "A",
    B      = "B",
    C      = "C",
    D      = "D"
  )
}

# as_labeller() + label_parsed is the correct ggplot2 idiom for math facet strips
make_param_labeller <- function(copula = c("fgm", "gaussian")) {
  copula <- match.arg(copula)
  as_labeller(param_labeller(copula), label_parsed)
}

# =============================================================================
# 16. SIMULATION-STUDY PLOTS
# =============================================================================

make_recovery_long <- function(recovery_results) {

  recovery_results |>
    select(
      n,
      beta1,
      beta2,
      dep,
      tau,
      mu1,
      mu2,
      A,
      B,
      C,
      D
    ) |>
    pivot_longer(
      cols = -n,
      names_to = "parameter",
      values_to = "estimate"
    )
}


make_truth_plot_data <- function(
    true_values,
    copula = c("fgm", "gaussian"),
    quad = quad_fit) {

  copula <- match.arg(copula)

  true_effective <- effective_parameters(
    beta1 = true_values$beta1,
    beta2 = true_values$beta2,
    dep = true_values$dep,
    copula = copula,
    quad = quad
  )

  data.frame(
    parameter = c(
      "beta1",
      "beta2",
      "dep",
      "tau",
      "mu1",
      "mu2",
      "A",
      "B",
      "C",
      "D"
    ),
    truth = c(
      true_values$beta1,
      true_values$beta2,
      true_values$dep,
      dep_to_tau(true_values$dep, copula),
      true_values$mu1,
      true_values$mu2,
      unname(true_effective["A"]),
      unname(true_effective["B"]),
      unname(true_effective["C"]),
      unname(true_effective["D"])
    )
  )
}


plot_parameter_recovery <- function(
    recovery_results,
    true_values,
    copula = c("fgm", "gaussian")) {

  copula <- match.arg(copula)
  copula_name <- if (copula == "fgm") "FGM" else "Gaussian"

  recovery_long <- make_recovery_long(
    recovery_results
  )

  truth_data <- make_truth_plot_data(
    true_values = true_values,
    copula = copula
  )

  lkp <- param_labeller(copula)
  recovery_long$parameter <- factor(recovery_long$parameter, levels = names(lkp))
  truth_data$parameter    <- factor(truth_data$parameter,    levels = names(lkp))
  
  
  ggplot(
    recovery_long,
    aes(
      x = factor(n),
      y = estimate
    )
  ) +
    geom_boxplot(outlier.alpha = 0.25) +
    geom_hline(
      data = truth_data,
      aes(yintercept = truth),
      linetype = "dashed"
    ) +
    facet_wrap(
      ~parameter,
      scales = "free_y",
      labeller = make_param_labeller(copula)
    ) +
    labs(
      title = paste0(
        "Parameter recovery: ",
        copula_name,
        "-copula Kumaraswamy model"
      ),
      x = "Sample size",
      y = "Estimate"
    ) +
    theme_minimal()
}


plot_summary_measure <- function(
    summary_data,
    measure = c("bias", "MSE"),
    copula = c("fgm", "gaussian")) {

  measure <- match.arg(measure)
  copula <- match.arg(copula)

  copula_name <- if (copula == "fgm") "FGM" else "Gaussian"
  
  lkp <- param_labeller(copula)
  summary_data$parameter <- factor(summary_data$parameter, levels = names(lkp))
  
  plot_object <- ggplot(
    summary_data,
    aes(
      x = n,
      y = .data[[measure]]
    )
  ) +
    geom_line() +
    geom_point() +
    facet_wrap(
      ~parameter,
      scales = "free_y",
      labeller = make_param_labeller(copula)
    ) +
    scale_x_continuous(
      breaks = sort(
        unique(summary_data$n)
      )
    ) +
    labs(
      title = paste0(
        measure,
        " across sample sizes: ",
        copula_name,
        " copula"
      ),
      x = "Sample size",
      y = measure
    ) +
    theme_minimal()

  if (measure == "bias") {
    plot_object <- plot_object +
      geom_hline(
        yintercept = 0,
        linetype = "dashed"
      )
  }

  plot_object
}


if (RUN_SIMULATION_STUDY) {

  print(
    plot_parameter_recovery(
      recovery_results = recovery_fgm,
      true_values = true_fgm,
      copula = "fgm"
    )
  )

  print(
    plot_parameter_recovery(
      recovery_results = recovery_gaussian,
      true_values = true_gaussian,
      copula = "gaussian"
    )
  )

  print(
    plot_summary_measure(
      summary_data = summary_fgm,
      measure = "bias",
      copula = "fgm"
    )
  )

  print(
    plot_summary_measure(
      summary_data = summary_fgm,
      measure = "MSE",
      copula = "fgm"
    )
  )

  print(
    plot_summary_measure(
      summary_data = summary_gaussian,
      measure = "bias",
      copula = "gaussian"
    )
  )

  print(
    plot_summary_measure(
      summary_data = summary_gaussian,
      measure = "MSE",
      copula = "gaussian"
    )
  )
}


# =============================================================================
# 17. LATEX / XTABLE OUTPUT FOR OVERLEAF
# =============================================================================
#
# Three tables are written for each copula:
#
#   *_model_parameter_recovery.tex
#       beta1, beta2, dependence parameter, Kendall tau, mu1, mu2
#
#   *_effective_parameter_recovery.tex
#       A, B, C, D
#
#   *_boundary_diagnostics.tex
#       dependence-boundary pile-up and sign recovery
#
# The same LaTeX is also printed to the R console.
#
# Mathematical parameter labels are deliberately retained using
# sanitize.text.function = identity.


format_recovery_for_latex <- function(
    summary_data,
    copula = c("fgm", "gaussian"),
    table = c("model", "effective")) {

  copula <- match.arg(copula)
  table <- match.arg(table)

  if (table == "model") {

    keep <- c(
      "beta1",
      "beta2",
      "dep",
      "tau",
      "mu1",
      "mu2"
    )

    parameter_labels <- c(
      beta1 = "$\\beta_1$",
      beta2 = "$\\beta_2$",
      dep = if (copula == "fgm") "$\\lambda$" else "$r$",
      tau = "$\\tau$",
      mu1 = "$\\mu_1$",
      mu2 = "$\\mu_2$"
    )

  } else {

    keep <- c("A", "B", "C", "D")

    parameter_labels <- c(
      A = "$A$",
      B = "$B$",
      C = "$C$",
      D = "$D$"
    )
  }

  summary_data |>
    filter(parameter %in% keep) |>
    mutate(
      parameter = factor(
        parameter,
        levels = keep
      )
    ) |>
    arrange(n, parameter) |>
    mutate(
      Parameter = unname(
        parameter_labels[
          as.character(parameter)
        ]
      )
    ) |>
    select(
      n,
      Parameter,
      truth,
      mean_estimate,
      bias,
      SD,
      MSE,
      RMSE,
      successful_fits
    ) |>
    rename(
      `True` = truth,
      `Mean estimate` = mean_estimate,
      `Bias` = bias,
      `SD` = SD,
      `MSE` = MSE,
      `RMSE` = RMSE,
      `Fits` = successful_fits
    )
}


print_and_write_xtable <- function(
    table_data,
    caption,
    label,
    filename,
    digits_after_decimal = 4) {

  xt <- xtable(
    table_data,
    caption = caption,
    label = label,
    align = c(
      "l",
      "r",
      "l",
      rep("r", ncol(table_data) - 2)
    )
  )

  # row names + n + Parameter are not decimal-valued columns.
  digits(xt) <- c(
    0,
    0,
    0,
    rep(
      digits_after_decimal,
      ncol(table_data) - 3
    ),
    0
  )

  cat("\n\n")
  print(
    xt,
    include.rownames = FALSE,
    sanitize.text.function = identity,
    table.placement = "!ht",
    comment = FALSE
  )

  print(
    xt,
    file = filename,
    include.rownames = FALSE,
    sanitize.text.function = identity,
    table.placement = "!ht",
    comment = FALSE
  )

  invisible(xt)
}

# -----------------------------------------------------------------------------
# LaTeX output for dependence-boundary diagnostics
# -----------------------------------------------------------------------------
#
# The boundary tables have a different structure from the parameter-recovery
# tables, so they are handled by a separate small helper function.

format_boundary_for_latex <- function(boundary_data) {
  
  boundary_data |>
    rename(
      `n` = n,
      `Number of fits` = number_fits,
      `Lower boundary` = lower_boundary,
      `Upper boundary` = upper_boundary,
      `Either boundary` = either_boundary,
      `Correct sign` = correct_sign
    )
}


print_and_write_boundary_xtable <- function(
    table_data,
    caption,
    label,
    filename) {
  
  xt <- xtable(
    table_data,
    caption = caption,
    label = label,
    align = c(
      "l",   # row names
      "r",   # n
      "r",   # number of fits
      "r",   # lower boundary
      "r",   # upper boundary
      "r",   # either boundary
      "r"    # correct sign
    )
  )
  
  # digits() includes an entry for the unused row-name column.
  # n and number of fits are integers; the remaining quantities
  # are proportions and are shown to two decimal places.
  digits(xt) <- c(
    0,
    0,
    0,
    2,
    2,
    2,
    2
  )
  
  cat("\n\n")
  
  print(
    xt,
    include.rownames = FALSE,
    sanitize.text.function = identity,
    table.placement = "!ht",
    comment = FALSE
  )
  
  print(
    xt,
    file = filename,
    include.rownames = FALSE,
    sanitize.text.function = identity,
    table.placement = "!ht",
    comment = FALSE
  )
  
  invisible(xt)
}


if (RUN_SIMULATION_STUDY) {

  # ---------------------------------------------------------------------------
  # FGM LaTeX tables
  # ---------------------------------------------------------------------------

  fgm_model_table <- format_recovery_for_latex(
    summary_data = summary_fgm,
    copula = "fgm",
    table = "model"
  )

  fgm_effective_table <- format_recovery_for_latex(
    summary_data = summary_fgm,
    copula = "fgm",
    table = "effective"
  )

  print_and_write_xtable(
    table_data = fgm_model_table,
    caption = paste0(
      "Parameter recovery for the FGM-copula Kumaraswamy bivariate ",
      "cardioid model."
    ),
    label = "tab:fgm_kumaraswamy_recovery",
    filename = "fgm_kumaraswamy_model_parameter_recovery.tex"
    # label = "tab:fgm_kumaraswamy_recovery2",
    # filename = "fgm_kumaraswamy_model_parameter_recovery2.tex"
  )

  print_and_write_xtable(
    table_data = fgm_effective_table,
    caption = paste0(
      "Recovery of the effective parameters for the FGM-copula ",
      "Kumaraswamy bivariate cardioid model."
    ),
    label = "tab:fgm_kumaraswamy_effective_recovery",
    filename = "fgm_kumaraswamy_effective_parameter_recovery.tex"
    # label = "tab:fgm_kumaraswamy_effective_recovery2",
    # filename = "fgm_kumaraswamy_effective_parameter_recovery2.tex"
  )

  # ---------------------------------------------------------------------------
  # Gaussian LaTeX tables
  # ---------------------------------------------------------------------------

  gaussian_model_table <- format_recovery_for_latex(
    summary_data = summary_gaussian,
    copula = "gaussian",
    table = "model"
  )

  gaussian_effective_table <- format_recovery_for_latex(
    summary_data = summary_gaussian,
    copula = "gaussian",
    table = "effective"
  )

  print_and_write_xtable(
    table_data = gaussian_model_table,
    caption = paste0(
      "Parameter recovery for the Gaussian-copula Kumaraswamy bivariate ",
      "cardioid model."
    ),
    label = "tab:gaussian_kumaraswamy_recovery",
    filename = "gaussian_kumaraswamy_model_parameter_recovery.tex"
    # label = "tab:gaussian_kumaraswamy_recovery2",
    # filename = "gaussian_kumaraswamy_model_parameter_recovery2.tex"
  )

  print_and_write_xtable(
    table_data = gaussian_effective_table,
    caption = paste0(
      "Recovery of the effective parameters for the Gaussian-copula ",
      "Kumaraswamy bivariate cardioid model."
    ),
    label = "tab:gaussian_kumaraswamy_effective_recovery",
    filename = "gaussian_kumaraswamy_effective_parameter_recovery.tex"
    # label = "tab:gaussian_kumaraswamy_effective_recovery2",
    # filename = "gaussian_kumaraswamy_effective_parameter_recovery2.tex"
  )
  
  # ---------------------------------------------------------------------------
  # Dependence-boundary diagnostic tables
  # ---------------------------------------------------------------------------
  
  fgm_boundary_table <-
    format_boundary_for_latex(
      boundary_fgm
    )
  
  gaussian_boundary_table <-
    format_boundary_for_latex(
      boundary_gaussian
    )
  
  
  print_and_write_boundary_xtable(
    table_data = fgm_boundary_table,
    caption = paste0(
      "Dependence-boundary diagnostics for the FGM-copula ",
      "Kumaraswamy bivariate cardioid model."
    ),
    label = "tab:fgm_kumaraswamy_boundary",
    filename = "fgm_kumaraswamy_boundary_diagnostics.tex"
    # label = "tab:fgm_kumaraswamy_boundary2",
    # filename = "fgm_kumaraswamy_boundary_diagnostics2.tex"
  )
  
  
  print_and_write_boundary_xtable(
    table_data = gaussian_boundary_table,
    caption = paste0(
      "Dependence-boundary diagnostics for the Gaussian-copula ",
      "Kumaraswamy bivariate cardioid model."
    ),
    label = "tab:gaussian_kumaraswamy_boundary",
    filename = "gaussian_kumaraswamy_boundary_diagnostics.tex"
    # label = "tab:gaussian_kumaraswamy_boundary2",
    # filename = "gaussian_kumaraswamy_boundary_diagnostics2.tex"
  )

  cat("\nLaTeX files written to the current working directory:\n")
  cat("  fgm_kumaraswamy_model_parameter_recovery.tex\n")
  cat("  fgm_kumaraswamy_effective_parameter_recovery.tex\n")
  cat("  fgm_kumaraswamy_boundary_diagnostics.tex\n")
  cat("  gaussian_kumaraswamy_model_parameter_recovery.tex\n")
  cat("  gaussian_kumaraswamy_effective_parameter_recovery.tex\n")
  cat("  gaussian_kumaraswamy_boundary_diagnostics.tex\n")
}

# =============================================================================
# 18. OPTIONAL: DEPENDENCE PROFILE EXAMPLES
# =============================================================================
#
# These are CONDITIONAL profiles: the fitted marginal parameters and locations
# are held fixed. They are useful for visualising how much information the
# sample contains about the copula dependence parameter.


# FGM conditional profile.
profile_fgm <- profile_dependence_fixed_margins(
  data = data_fgm,
  beta1 = fit_fgm$best$beta1,
  beta2 = fit_fgm$best$beta2,
  mu1 = fit_fgm$best$mu1,
  mu2 = fit_fgm$best$mu2,
  copula = "fgm",
  dep_grid = seq(-0.999, 0.999, length.out = 201)
)

profile_fgm_plot <- ggplot(
  profile_fgm,
  aes(
    x = dep,
    y = relative_logLik
  )
) +
  geom_line() +
  geom_hline(
    yintercept = -1.92,
    linetype = "dashed"
  ) +
  geom_vline(
    xintercept = true_fgm$dep,
    linetype = "dotted"
  ) +
  labs(
    title = "FGM conditional dependence profile",
    subtitle = "Dotted line: true lambda",
    x = expression(lambda),
    y = "Relative log-likelihood"
  ) +
  theme_minimal()

print(profile_fgm_plot)


# Gaussian conditional profile shown on Kendall's tau scale.
profile_gaussian <- profile_dependence_fixed_margins(
  data = data_gaussian,
  beta1 = fit_gaussian$best$beta1,
  beta2 = fit_gaussian$best$beta2,
  mu1 = fit_gaussian$best$mu1,
  mu2 = fit_gaussian$best$mu2,
  copula = "gaussian",
  dep_grid = seq(-0.98, 0.98, length.out = 201)
)

profile_gaussian_plot <- ggplot(
  profile_gaussian,
  aes(
    x = tau,
    y = relative_logLik
  )
) +
  geom_line() +
  geom_hline(
    yintercept = -1.92,
    linetype = "dashed"
  ) +
  geom_vline(
    xintercept = GAUSSIAN_TAU_TRUE,
    linetype = "dotted"
  ) +
  labs(
    title = "Gaussian conditional dependence profile",
    subtitle = "Dotted line: true Kendall tau",
    x = expression("Kendall's " * tau),
    y = "Relative log-likelihood"
  ) +
  theme_minimal()

print(profile_gaussian_plot)


# =============================================================================
# END OF SCRIPT
# =============================================================================
