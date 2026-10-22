# =============================================================================
# BIVARIATE CARDIOID MODEL II(C): FGM BIVARIATE BETA
# =============================================================================

library(xtable)
# ---------------------------------------------------------
# HELPER: FGM MOMENT INTEGRAL FOR BETA DISTRIBUTION
# ---------------------------------------------------------
# Computes q_x = \int_0^1 x * (1 - 2 * F(x)) * f(x) dx
calc_q_beta <- function(shape1, shape2) {
  integrand <- function(x) {
    x * (1 - 2 * pbeta(x, shape1, shape2)) * dbeta(x, shape1, shape2)
  }
  # tryCatch ensures optimizer doesn't crash if it probes extreme parameter bounds
  res <- tryCatch({
    integrate(integrand, lower = 0, upper = 1, rel.tol = 1e-4)$value
  }, error = function(e) {
    0 
  })
  return(res)
}

# ---------------------------------------------------------
# GENERATE LATENT (X, Y) FROM FGM BETA
# ---------------------------------------------------------

simulate_fgm_beta <- function(n, alpha, beta, gamma, omega, lambda) {
  # Generate U and W from Uniform(0,1)
  u <- runif(n)
  w <- runif(n)
  
  # Generate V from the conditional FGM copula c_v(u) = w
  # This results in solving the quadratic equation: a*v^2 + b*v + c = 0
  a_qe <- lambda * (1 - 2 * u)
  b_qe <- -(1 + a_qe)
  c_qe <- w
  
  v <- ifelse(
    a_qe == 0, 
    w, 
    (-b_qe - sqrt(b_qe^2 - 4 * a_qe * c_qe)) / (2 * a_qe)
  )
  
  # Transform (U, V) to (X, Y) using Beta inverse CDF
  x <- qbeta(u, alpha, beta)
  y <- qbeta(v, gamma, omega)
  
  return(data.frame(x = x, y = y))
}

# ---------------------------------------------------------
# GENERATE THETA_1 AND THETA_2 (REJECTION SAMPLING)
# ---------------------------------------------------------

simulate_cardioid_rejection <- function(n, mu, rho) {
  thetas <- numeric(n)
  accepted <- 0
  
  while(accepted < n) {
    # Proposal: Uniform(0, 2*pi)
    theta_prop <- runif(1, 0, 2 * pi)
    u_acc <- runif(1)
    
    c <- cos(theta_prop - mu)
    
    # Target density proportional to (1 + 2 * rho * cos(theta - mu))
    # Maximum value of the density is at theta = mu => (1 + 2 * rho)
    ratio <- (1 + 2 * rho * c) / (1 + 2 * rho)
    
    if (u_acc <= ratio) {
      accepted <- accepted + 1
      thetas[accepted] <- theta_prop
    }
  }
  return(thetas)
}

# ---------------------------------------------------------
# COMBINED DATA GENERATION
# ---------------------------------------------------------

generate_model_IIc_data <- function(n, mu1, mu2, alpha, beta, gamma, omega, 
                                    delta1, delta2, lambda) {
  # Generate (X, Y) from FGM Beta
  latent_vars <- simulate_fgm_beta(n, alpha, beta, gamma, omega, lambda)
  
  # Generate Theta 1 and Theta 2 given X and Y
  theta1 <- sapply(latent_vars$x, function(x) {
    simulate_cardioid_rejection(1, mu1, x * delta1)
  })
  
  theta2 <- sapply(latent_vars$y, function(y) {
    simulate_cardioid_rejection(1, mu2, y * delta2)
  })
  
  return(data.frame(theta1 = theta1, theta2 = theta2))
}

# ---------------------------------------------------------
# NEGATIVE LOG-LIKELIHOOD WITH TRANSFORMATIONS
# ---------------------------------------------------------

bivariate_cardioid_nll <- function(params, data) {
  # Unconstrained parameters (eta)
  eta_alpha <- params[1]
  eta_beta <- params[2]
  eta_gamma <- params[3]
  eta_omega <- params[4]
  eta_delta1 <- params[5]
  eta_delta2 <- params[6]
  eta_lambda <- params[7]
  mu1 <- params[8]   # Assuming mu is optimized directly
  mu2 <- params[9]
  
  # Apply transformations to enforce constraints
  alpha <- exp(eta_alpha)
  beta <- exp(eta_beta)
  gamma <- exp(eta_gamma)
  omega <- exp(eta_omega)
  
  delta1 <- 0.5 * tanh(eta_delta1)
  delta2 <- 0.5 * tanh(eta_delta2)
  lambda <- tanh(eta_lambda)
  
  # Calculate Beta Moments & q values
  EX <- alpha / (alpha + beta)
  EY <- gamma / (gamma + omega)
  
  qx <- calc_q_beta(alpha, beta)
  qy <- calc_q_beta(gamma, omega)
  
  EXY <- EX * EY + lambda * qx * qy
  
  # Compute Joint PDF
  c1 <- cos(data$theta1 - mu1)
  c2 <- cos(data$theta2 - mu2)
  
  pdf_vals <- (1 / (2 * pi))^2 * (
    1 + 2 * delta1 * c1 * EX + 2 * delta2 * c2 * EY 
    + 4 * delta1 * delta2 * c1 * c2 * EXY
  )
  
  # Ensure strict positivity to avoid log(0) or NA issues in optim
  pdf_vals[pdf_vals <= 0] <- .Machine$double.eps
  
  # Return Negative Log-Likelihood
  return(-sum(log(pdf_vals)))
}

# =============================================================================
# MULTI-START MLE & IDENTIFIABILITY SIMULATION STUDY
# =============================================================================

# ---------------------------------------------------------
# CALCULATE OBSERVABLE COEFFICIENTS (A, B, C, D)
# ---------------------------------------------------------

calc_observable_ABCD <- function(alpha, beta, gamma, omega, 
                                 delta1, delta2, lambda) {
  # Beta means
  EX <- alpha / (alpha + beta)
  EY <- gamma / (gamma + omega)
  
  # Beta FGM moment components via numerical integration
  qx <- calc_q_beta(alpha, beta)
  qy <- calc_q_beta(gamma, omega)
  
  EXY <- EX * EY + lambda * qx * qy
  
  A <- delta1 * EX
  B <- delta2 * EY
  C <- delta1 * delta2 * EXY
  D <- C - A * B
  
  if(any(is.na(c(EX, EY, qx, qy, EXY, A, B, C)))) {
    message(sprintf("NA triggered at: alpha=%.3f, beta=%.3f, gamma=%.3f, omega=%.3f, lambda=%.3f", 
                    alpha, beta, gamma, omega, lambda))
  }
  
  return(c(A = A, B = B, C = C, D = D))
}

# ---------------------------------------------------------
# MULTI-START MLE FOR MODEL II(c): BIVARIATE BETA
# ---------------------------------------------------------

run_multistart_mle_IIc <- function(data, num_starts) {
  results <- data.frame()
  
  for(i in 1:num_starts) {
    # Generate random starting values for the unconstrained eta parameters
    initial_eta <- c(
      eta_alpha = rnorm(1, 0, 0.5), eta_beta = rnorm(1, 0, 0.5),
      eta_gamma = rnorm(1, 0, 0.5), eta_omega = rnorm(1, 0, 0.5),
      eta_delta1 = rnorm(1, 0, 0.5), eta_delta2 = rnorm(1, 0, 0.5),
      eta_lambda = rnorm(1, 0, 0.5),
      mu1 = pi, mu2 = pi # Fix mu for stability in identifying A,B,C,D
    )
    
    # Run optimization
    fit <- optim(
      par = initial_eta, 
      fn = bivariate_cardioid_nll, 
      data = data, 
      method = "L-BFGS-B",
      lower = c(log(0.01), log(0.01), log(0.01), log(0.01), 
                0, 0, -1, pi - 0.2, pi - 0.2),
      upper = c(log(30.0), log(30.0), log(30.0), log(30.0),  
                0.5,  0.5, 1, pi + 0.2, pi + 0.2),
      control = list(maxit = 2000)
    )
    
    # Back-transform estimates
    est_alpha <- exp(fit$par[1])
    est_beta <- exp(fit$par[2])
    est_gamma <- exp(fit$par[3])
    est_omega <- exp(fit$par[4])
    est_delta1 <- 0.5 * tanh(fit$par[5])
    est_delta2 <- 0.5 * tanh(fit$par[6])
    est_lambda <- tanh(fit$par[7])
    
    # Calculate corresponding A, B, C, D
    abcd <- calc_observable_ABCD(est_alpha, est_beta, est_gamma, est_omega, 
                                 est_delta1, est_delta2, est_lambda)
    
    # Store results
    results <- rbind(results, data.frame(
      NLL = fit$value,
      alpha = est_alpha, beta = est_beta, 
      gamma = est_gamma, omega = est_omega,
      delta1 = est_delta1, delta2 = est_delta2, lambda = est_lambda,
      A = abcd[1], B = abcd[2], C = abcd[3] 
      #,D = abcd[4]
    ))
  }
  rownames(results) <- NULL
  return(results)
}

# =============================================================================
# EXECUTING THE SIMULATION STUDIES
# =============================================================================

set.seed(123)

true_params_IIc <- list(mu1 = pi, mu2 = pi, alpha = 2, beta = 2, gamma = 3,
                        omega = 3, delta1 = 0.3, delta2 = 0.2, lambda = 0.5)

mle_results_IIc_full <- data.frame()

for(n in c(250, 500, 1000, 2500, 5000, 10000)){
  sim_data_IIc <- generate_model_IIc_data(n, true_params_IIc$mu1, 
                                          true_params_IIc$mu2, 
                                          true_params_IIc$alpha, 
                                          true_params_IIc$beta, 
                                          true_params_IIc$gamma, 
                                          true_params_IIc$omega, 
                                          true_params_IIc$delta1, 
                                          true_params_IIc$delta2, 
                                          true_params_IIc$lambda)
  
  mle_results_IIc <- run_multistart_mle_IIc(sim_data_IIc, num_starts = 10)
  mle_results_IIc$Run <- 1:nrow(mle_results_IIc)
  mle_results_IIc <- mle_results_IIc[order(mle_results_IIc$NLL), ]
  mle_results_IIc$n <- n
  mle_results_IIc <- mle_results_IIc[, c("n", "Run", setdiff(names(mle_results_IIc),c("n","Run")))]
  mle_results_IIc_full <- rbind(mle_results_IIc_full, mle_results_IIc)
}

rownames(mle_results_IIc_full) <- NULL

library(xtable)
print(xtable(mle_results_IIc_full,
             caption = "MLE optimization results for Model II(c) FGM Beta",
             label = "tab:multistart_iic_beta",
             digits = c(rep(0,3),rep(3,11))),
      file = "mle_iic_beta_results_tbl.tex",
      include.rownames = FALSE,
      hline.after = c(-1, 0, 10, 20, 30, 40, 50))
