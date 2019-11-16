.datatable.aware=TRUE
library(PerformanceAnalytics)
library(robust)

#' Function to create a balanced data set (same number of observatons in each month)
#'
#' @name fit.balanced.panel
#' @title fit.balanced.panel
#' @encoding UTF-8
#' @concept factor models for attribution and risk
#' @param .dates name of the data.table of rawdata
#' @param .ids name of the identifier field that will be used for row names
#' @param .dates name of the date field that will be used as column names
#'
#' @return data.table with equal number of observations in each month
#'
#' @examples
#' balanced <- fit.balanced.panel(rawdata, "symbol", "datadate")
#' @author Roger J. Bos, \email{roger.bos@@gmail.com}
#' @export
fit.balanced.panel <- function(.data, .ids, .dates) {
  individuals = unique(.data[, get(.ids)])
  datetimes = unique(.data[, get(.dates)])
  
  balanced = data.table(expand.grid(individuals, datetimes))
  setnames(balanced, c(.ids, .dates))
  setkeyv(balanced, c(.ids, .dates))
  setkeyv(.data, c(.ids, .dates))
  return(.data[balanced])
}

#' @description Function to perform cross-sectional standardization of raw data (vectorized)
#' @name fit.zscore
#' @title fit.zscore
#' @encoding UTF-8
#' @concept factor models for attribution and risk
#' @param x vector of data to be standardized
#' @param dte vector of dates (or anything else) used to partition the data
#' @param w optional vector of weights used to calculate weighted mean, defaults to equal weighted
#' @param grp optional vector of group designations used to standardize within groups, defaults to a signle group
#' @param rob.stats logical parameter to subtract the the median rather than the mean, defaults to FALSE
#'
#' @return vector of standardized data with a mean near zero and a standard deviation near one
#'
#' @examples
#' fit.zscore(x = data[['mcap']), dte = data[[date]]), w = data[['weight']]), rob.stats = TRUE)
#' @author Roger J. Bos, \email{roger.bos@@gmail.com}
#' @export
fit.zscore <- function(x, dte, w = 1, grp = 1, rob.stats = FALSE) {
  # x = fma_rawdata$fma.pex; dte=fma_rawdata$datadate; w=1; grp=1; rob.stats=TRUE
  
  dt <- data.table(x, w, dte=as.factor(dte), grp)
  if (rob.stats) {
    dt[, xbar := median(w * x, na.rm = TRUE), by = list(dte, grp)]
    suppressWarnings(dt[, out := (x - xbar) / mad(x, center = xbar, na.rm = TRUE), by = list(dte, grp)])
  } else {
    dt[, out := (x - weighted.mean(x, w, na.rm = TRUE)) / sd(x, na.rm = TRUE), by = list(dte, grp)]
  }
  return(dt[['out']])
  
}

#' @description Function to create a data.table (wide format) from a column of long format, uses reshape2::dcast()
#' @name fit.data.cast
#' @title fit.data.cast
#' @encoding UTF-8
#' @concept factor models for attribution and risk
#' @param datMat data.table of rawdata
#' @param item string name of the data items to extract
#' @param id.var string name of the identifier that will make up the row names
#' @param date.var string name of the dates that will make up the column names
#' @param reverse logical to reverse the dates in the output, so the first column will be the most recent date, defaults to FALSE
#'
#' @return data.table with the first column being the ids and the subsequent columns being the data 'item'
#'
#' @examples
#' load("data/Stock.df.Rdata")
#' retMat <- fit.data.cast(stock, item='RETURN', id.var = 'TICKER', date.var = 'DATE', reverse = TRUE)
#' @author Roger J. Bos, \email{roger.bos@@gmail.com}
#' @export
fit.data.cast <- function(datMat, item, id.var, date.var, reverse = FALSE) {
  fmla <- substitute(id ~ date.var, list(id = as.name(id.var), date.var = as.name(date.var)))
  x <- reshape2::dcast(datMat, eval(fmla), value.var=item, fun.aggregate = mean)
  if (reverse) setcolorder(x, c(1, ncol(x):2))
  return(x)
}



#' @description Function to calculate factor returns for portfolio attribution analysis.  The code has been adapted from the factorAnalyticsAddons package (Uthaisaad, 2017).
#' @name fit.attribution
#' @title fit.attribution
#' @encoding UTF-8
#' @concept factor models for attribution and risk
#' @param date.var string name of the date column
#' @param id.var string name of the id column
#' @param return.var string name of the return column
#' @param weight.var string name of the weight column
#' @param exposures.var vector of string name(s) of the column(s) to use as exposures (attributes)
#' @param rob.stats logical
#' @param full.resid.cov logical
#' @param z.score logical
#' @param strReturns logical
#' @param resid.EWMA logical
#'
#' @return data.table
#'
#' @examples
#' fit <- fit.attribution(fitdata = stock, date.var = 'DATE', id.var = 'TICKER', return.var = 'RETURN',
#'   weight.var = 'LOG.MARKETCAP', exposure.vars = c('NET.SALES','BOOK2MARKET','GICS.SECTOR'),
#'   rob.stats = TRUE, full.resid.cov = FALSE, z.score = FALSE,
#'   stdReturn = TRUE, resid.EWMA = TRUE)
#' @references \url{https://github.com/chindhanai/factorAnalyticsAddons}
#' @author Roger J. Bos, \email{roger.bos@@gmail.com}
#' @export
fit.attribution <- function(fitdata, date.var, id.var, return.var, exposure.vars,
                            weight.var=NULL, rob.stats = FALSE, full.resid.cov=FALSE, z.score = FALSE,
                            stdReturn = FALSE, resid.EWMA = FALSE, lambda = .9, ...) {
  
  # record the call as an element to be returned
  this.call <- match.call()
  if (!is.data.table(fitdata)) fitdata <- as.data.table(fitdata)
  cols <- c(id.var, date.var)
  setkeyv(fitdata, cols)
  
  # extract unique time periods from data
  fitdata[[date.var]] <- as.Date(fitdata[[date.var]])
  alldates <- fitdata[[date.var]]
  Dates <- unique(alldates)
  TP <- length(Dates)
  if (TP < 2) {
    stop("Invalid args: at least 2 unique time periods are required to fit the factor model")
  }
  
  # extract asset names from data
  id.names <- sort(unique(fitdata[[id.var]]))
  N <- length(id.names)
  
  rawReturns <- fit.data.cast(fitdata, item = return.var, id.var = id.var, date.var = date.var)
  rawReturns[is.na(rawReturns)] <- 0
  ids <- rawReturns[, 1]
  rawReturns <- rawReturns[, -1]

  # Standardize the returns if stdReturn = TRUE
  if (stdReturn) {
    sdReturns <- apply(rawReturns, 1, sd, na.rm = TRUE)
    sdReturns[sdReturns == 0] <- median(sdReturns)
    sigmaGarch <- as.matrix(rawReturns)
    for (i in 1:N) {
      ts <- rawReturns[i, ] ^ 2
      var_past_2 <- 0
      tmp <- sapply(ts, function(x) var_past_2 <<- (1 - 0.10 - 0.81) * sdReturns[i] ^ 2 + 0.10 * x + 0.81 * var_past_2)
      sigmaGarch[i, ] <- tmp
    }
    sigmaGarch <- sqrt(sigmaGarch)
    tmp <- rawReturns / sigmaGarch
    tmp <- data.table(ids, rawReturns / sigmaGarch)
    long <- reshape2::melt(tmp, id.vars = 'ids', variable.name = date.var, value.name = 'returnStd')
    long[[date.var]] <- as.Date(long[[date.var]])
    names(long)[1] <- id.var
    fitdata <- merge(fitdata, long, by = c(id.var, date.var), all.x = TRUE)
  } else {
    fitdata[['returnStd']] <- fitdata[[return.var]]
  }
  
  loadings <- fitdata[, ..exposure.vars]
  which.numeric <- sapply(loadings, is.numeric)
  exposures.num <- exposure.vars[which.numeric]
  exposures.char <- exposure.vars[!which.numeric]
  
  # Convert numeric exposures to z-scores
  if (z.score) {
    if (!is.null(weight.var)) {
      fitdata[[weight.value]] <- fitdata[[weight.var]]
      # Weight exposures within each period using weight.var
      fitdata[, weight := weight.value / sum(weight.value), by = date.var]
    } else {
      fitdata[, weight := 1]
    }
    # Calculate z-scores looping through all numeric exposures
    for (i in exposures.num) {
      std.expo.num <- fit.zscore(x = unlist(fitdata[[i]]),
                                 dte = unlist(fitdata[[date.var]]),
                                 w = unlist(fitdata[['weight']]),
                                 rob.stats = rob.stats)
      fitdata[[i]] <- std.expo.num
    }
  }

  if (length(exposures.char)) {

    # Add groups to fitdata for use in attribution function
    inds <- sort(unique(fitdata[[exposures.char]]))
    suppressWarnings(fitdata[, (inds) := lapply(inds, function(x) ifelse(get(exposures.char) == x, 1, 0))])

    contrasts.list <- lapply(seq(length(exposures.char)), function(i)
      function(n) contr.treatment(n, contrasts = FALSE))
    names(contrasts.list) <- exposures.char

    # number of factors including Market and dummy variables
    factor.names <- c(exposures.num, paste(inds, sep = ""))

  } else {
    factor.names <- exposures.num
  }

  # Determine factor model formula to be passed to lm
  # Remove Intercept as it introduces rank deficiency in the exposure matrix.
  fm.formula <- formula(paste("returnStd ~ -1 + ", paste(exposure.vars, collapse = "+")))

  fit.lm <- function(mdate) {

    # mdate = '2003-08-29'
    cols <- c(date.var, id.var, 'returnStd', exposure.vars, 'W')
    load <- fitdata[fitdata[[date.var]] == mdate, ..cols]
    if (length(exposures.char)) {
      mod <- lm(formula = fm.formula, data = load, contrasts = contrasts.list, na.action = na.omit, weights=W)
    } else {
      mod <- lm(formula = fm.formula, data = load, na.action = na.omit, weights = W)
    }
    # print(length(mod$coefficients))
    # print(mdate)
    return(list(coef = list(mod$coefficients), residuals = list(mod$residuals), r2 = summary(mod)$r.squared))
  }

  fitdata[, W := 1]
  fitdata[, tmp_datadate := fitdata[[date.var]]]
  reg.list <- fitdata[, fit.lm(tmp_datadate), by = tmp_datadate]
  fitdata[, tmp_datadate := NULL]

  # time series of factor returns = estimated coefficients in each period
  # rbind the list tolerating column name changes / missing
  # https://stackoverflow.com/questions/16962576/how-can-i-rbind-vectors-matching-their-column-names
  factor.returns <- do.call(rbind, lapply(reg.list$coef, function(x) x[match(names(reg.list$coef[[1]]), names(x))]))

  residuals <- t(do.call("rbind", reg.list$residuals))
  colnames(residuals) <- as.character(Dates)
  rownames(residuals) <- id.names

  r2 <- reg.list$r2
  names(r2) <- as.character(Dates)

  # exposure matrix B or beta for the last time period - N x K
  cols <- c(date.var, 'returnStd', exposure.vars)
  loadings <- fitdata[fitdata[[date.var]] == max(alldates), ..cols]
  beta <- model.matrix(fm.formula, data=loadings)
  rownames(beta) <- id.names

  # Try to make sure matrices confirm, remove any column that has NAs for the most recent time period
  beta.names <- data.frame(desc = colnames(beta))
  tmp <- merge(t(factor.returns), beta.names, by.x=0, by.y='desc', all.y=TRUE)
  tmp.names <- tmp$Row.names
  factor.returns.fixed <- t(tmp[, -1])
  colnames(factor.returns.fixed) <- tmp.names
  factor.returns.fixed[is.na(factor.returns.fixed)] <- 0
  factor.returns <- factor.returns.fixed

  stopifnot(all(colnames(factor.returns) %in% colnames(beta)))

  # Shorten the Sector / Country names
  if (length(exposures.char) > 0) {
    colnames(beta) = gsub(exposures.char, "", colnames(beta))
    colnames(factor.returns) <- gsub(exposures.char, "", colnames(factor.returns))
  }
  if (length(exposure.vars) > 1) rownames(factor.returns) <- as.character(Dates)

  # factor and residual covariances
  factor.cov <- cov(factor.returns)
  resid.var <- try(apply(coredata(residuals), 1, var))
  if (full.resid.cov) {
    resid.cov <- cov(residuals)
  } else {
    resid.cov <- try(diag(resid.var))
  }

  # return covariance estimated by the factor model
  # (here beta corresponds to the exposure of last time period, TP)
  return.cov <- beta %*% t(factor.cov) %*% t(beta) + resid.cov

  # Create list of return values.
  return(list(beta = beta,
              factor.returns = factor.returns,
              residuals = residuals,
              r2 = r2,
              factor.cov = factor.cov,
              resid.cov = resid.cov,
              return.cov = return.cov,
              resid.var = resid.var,
              call = this.call,
              fitdata = fitdata,
              exposure.vars = exposure.vars,
              weight.var = weight.var,
              date.var = date.var,
              return.var = return.var,
              id.var = id.var,
              id.names = id.names,
              factor.names = factor.names,
              exposures.char = exposures.char,
              time.periods = TP))


  
}

#' @description Helper function to show contributions nicely.  The periodic contributions from attribution cannot be cummulated to longer time periods so the carino adjustment is made as per Carino (1999).
#' @name fit.contribution
#' @title fit.contribution
#' @param fit list output from \code{"fit.attribution"}
#' @param bm.wgt.var string name of benchmark weight column (in fitdata passed to \code{"fit.attribution"})
#' @param port.wgt.var string name of portfolio weight column (in fitdata passed to \code{"fit.attribution"})
#'
#' @return list of periodic returns and summary returns
#'
#' @examples
#' stock <- as.data.table(stock)
#' stock[TICKER %in% c('SUNW','ORCL','MSFT'), portfolioWeight := 1/3, by=DATE]
#' stock[is.na(portfolioWeight), portfolioWeight := 0]
#' stock[, benchmarkWeight := 1/.N, by=DATE]
#' fit <- fit.attribution(fitdata = stock, date.var = 'DATE', id.var = 'TICKER', return.var = 'RETURN',
#'                        weight.var = 'LOG.MARKETCAP', exposure.vars = c('NET.SALES','BOOK2MARKET','GICS.SECTOR'),
#'                        rob.stats = TRUE, full.resid.cov = FALSE, z.score = FALSE,
#'                        stdReturn = TRUE, resid.EWMA = TRUE)
#' cfit <-fit.contribution(fit, bm.wgt.var = 'benchmarkWeight', port.wgt.var = 'portfolioWeight')
#' @references David R Carino, Combining Attribution Effects Over Time, The Journal of Performance Measurement, pages 5 - 14.
#' @author Roger J. Bos, \email{roger.bos@@gmail.com}
#' @export
fit.contribution <- function(fit, bm.wgt.var, port.wgt.var) {
  
  
  cols <- c(fit[['id.var']], fit[['date.var']], fit[['return.var']], fit[['factor.names']], bm.wgt.var, port.wgt.var)
  x <- fit[['fitdata']][, ..cols]
  x[, datadate := get(fit[['date.var']])]
  x[, portfolioWgt := get(port.wgt.var)]
  x[is.na(portfolioWgt), portfolioWgt := 0]
  x[, benchmarkWgt := get(bm.wgt.var)]
  x[is.na(benchmarkWgt), benchmarkWgt := 0]
  
  x[, portRet  := portfolioWgt * get(fit[['return.var']])]
  x[, benchRet := benchmarkWgt * get(fit[['return.var']])]
  portRet  <- x[, .(portRet  = sum(portRet )), datadate]
  benchRet <- x[, .(benchRet = sum(benchRet)), datadate]
  setkey(portRet, datadate)
  setkey(benchRet, datadate)
  
  active <- merge(portRet, benchRet, all=TRUE)
  active[, activeRet := portRet - benchRet]
  
  # Active exposures
  x[, activeWgt := portfolioWgt - benchmarkWgt]
  
  cols <- fit$factor.names
  ex <- x[, lapply(.SD, function(x) x * activeWgt), .SDcols = cols]
  act.expo <- rowsum(x = ex, group = x$datadate)
  
  # Carino scaling coefficient
  cum_portRet <- prod(1 + active$portRet) - 1
  cum_benchRet <- prod(1 + active$benchRet) - 1
  active[, carino := ((log(1+portRet) - log(1+benchRet)) / (portRet - benchRet)) /
           ((log(1+cum_portRet) - log(1+cum_benchRet)) / (cum_portRet - cum_benchRet))]
  carinoMat <- matrix(data=active[['carino']], nrow=nrow(active), ncol=ncol(act.expo))
  
  factor.returns <- coredata(fit$factor.returns)
  factor.returns[is.na(factor.returns)] <- 0
  
  contrib_orig <- act.expo * factor.returns
  resid_orig <- active$activeRet - rowSums(contrib_orig, na.rm = TRUE)
  contrib <- act.expo * factor.returns * carinoMat
  resid <- resid_orig * active$carino
  
  returns_orig <- data.table(contribution = contrib_orig, Residual = resid_orig,
                             Date=portRet$datadate, Portfolio.Return = portRet$portRet, Benchmark.Return = benchRet$benchRet,
                             Active.Return = active$activeRet)
  names(returns_orig)[1:length(fit$factor.names)] <- fit$factor.names
  setcolorder(returns_orig, "Date")
  returns_orig <- as.xts(returns_orig)
  
  returns <- data.table(contribution=contrib, Residual=resid,
                        Date=portRet$datadate, Portfolio.Return = portRet$portRet, Benchmark.Return = benchRet$benchRet,
                        Active.Return = active$activeRet)
  names(returns)[1:length(fit$factor.names)] <- fit$factor.names
  setcolorder(returns, "Date")
  returns <- as.xts(returns)
  
  Total.Return <- colSums(returns)
  Total.Return[['Portfolio.Return']] <- cum_portRet
  Total.Return[['Benchmark.Return']] <- cum_benchRet
  Total.Return[['Active.Return']] <- cum_portRet - cum_benchRet
  
  # Don't need time zone, but we set TZ so we don't get flooded with warnings
  index(returns_orig) <- as.POSIXct(index(returns_orig), tz=Sys.getenv("TZ"))
  tzone(returns_orig) <- Sys.getenv("TZ")
  returns.table <- rbind('Total Return' = Total.Return,
                         PerformanceAnalytics::table.AnnualizedReturns(returns_orig),
                         PerformanceAnalytics::maxDrawdown(returns_orig))
  returns.table$Active.Return <- returns.table$Portfolio.Return - returns.table$Benchmark.Return
  returns.table$Residual[1] <- returns.table$Active.Return[1] - sum(returns.table[1, 1:(match("Residual", names(returns.table))-1)])
  
  return(list(returns = round(returns_orig, 4), returns.table = round(returns.table, 4)))
}

#' @description Function to calculate fundamental risk model. The code has been adapted from Kakushadze and Yu (2016).
#' @name fit.fundamental
#' @encoding UTF-8
#' @concept factor models for attribution and risk
#' @param date.var string name of the date column
#' @param id.var string name of the id column
#' @param return.var string name of the return column
#' @param weight.var string name of the weight column (used in regressions to estimate factor returns).
#' @param exposures.var vector of string name(s) of the column(s) to use as exposures (attributes)
#' @param rob.stats logical
#' @param z.score logical
#' @param strReturns logical
#' @param calc.inv logical
#' @param cov.wgt logical
#' @param parkinson logical
#'
#' @return list of risk model outputs where
#' *specific.risk* is the vector idiosyncratic volatility (or specific risk),
#' *factor.returns* is the matrix of factor returns estimated by the risk model,
#' *factor.loadings* is the matrix of factor loadings,
#' *factor.cov* is the matrix of factor covariances,
#' *cov.mat** is the matrix of variance/covariances,
#' *inverse.cov* is the inverse of the variance/covariance matrix, and
#' *fitdata* is the matrix of input data.
#'
#' @examples
#' fit <- fit.fundamental(fitdata = stock, date.var = 'DATE', id.var = 'TICKER', return.var = 'RETURN',
#'                        weight.var = 'LOG.MARKETCAP', exposure.vars = c('NET.SALES','BOOK2MARKET','GICS.SECTOR'),
#'                        rob.stats = TRUE, z.score = FALSE, stdReturn = TRUE, calc.inv = TRUE, cov.wgt = FALSE, parkinson = FALSE)
#' @references Kakushadze, Zura and Yu, Willie, Multifactor Risk Models and Heterotic CAPM (January 24, 2016). The Journal of Investment Strategies 5(4) (2016) 1-49. Available at SSRN: \url{https://ssrn.com/abstract=2722093}
#' @author Roger J. Bos, \email{roger.bos@@gmail.com}
#' @export
fit.fundamental <- function (fitdata, date.var, id.var, return.var, exposure.vars,
                             weight.var = NULL, rob.stats = FALSE,
                             z.score = FALSE, stdReturn = TRUE,
                             calc.inv = TRUE, cov.wgt = FALSE,
                             parkinson = FALSE) {
  
  if (!is.data.table(fitdata)) fitdata <- as.data.table(fitdata)
  
  # Calculate historical volatility
  sigma <- fitdata[, sd(get(return.var), na.rm=TRUE), by = id.var]
  setnames(sigma, "V1", "sigma")
  # Make sure sigma is not zero
  sigma[sigma==0, sigma := median(sigma)]
  
  # Normalize the returns (so we are estimating the
  # correlation matrix instead of the covariance matrix)
  fitdata <- fitdata[sigma, on = id.var]
  fitdata[, retVar := get(return.var) / sigma]
  fitdata[is.na(retVar), retVar := 0]
  
  # Utilize fit.attribution to calculate factor returns, etc.
  fa <- fit.attribution(fitdata = fitdata,
                        date.var = date.var,
                        id.var = id.var,
                        return.var = 'retVar',
                        exposure.vars = exposure.vars,
                        weight.var = weight.var,
                        rob.stats = rob.stats,
                        full.resid.cov = FALSE,
                        z.score = z.score,
                        stdReturn = stdReturn)

  exposures.char <- fa$exposures.char

  # Get factor returns from fit.attribution
  factor.returns <- fa$factor.returns
  factor.returns[is.na(factor.returns)] <- 0
  
  # Calculate factor cov from factor returns
  if (cov.wgt) {
    # Decay rate of .02 over the number of months
    factor.cov <- cov.wt(factor.returns, wt = exp(-.02 * nrow(factor.returns):1))
  } else {
    factor.cov <- var(factor.returns, factor.returns)
  }
  
  # Get factor returns from fit.attribution
  factor.loadings <- fa$beta
  
  # Calculate covariance matrix
  covmat <- factor.loadings %*% factor.cov %*% t(factor.loadings)
  
  # Get specific variance from fit.attribution
  resid.var <- fa$resid.var
  tr1 <- sqrt(resid.var + diag(covmat))
  sigmaVec = sigma[['sigma']] / tr1
  # Apply scaling to specific variance and factor loadings per equation 39
  spec.var <- resid.var * sigmaVec^2
  factor.loadings <- factor.loadings * sigmaVec
  
  # If requested, calculate Parkinson volatility and use max(spec.var, Parkinson)
  if (parkinson) {
    tmp <- fitdata[, log(High / Low)^2 / (4 * log(2)), by=.(id.var, date.var)]
    Park <- tmp[, mean(V1, na.rm=TRUE), by = id.var]
    # Applying scaling to Parkinson volatility
    Parkinson <- Park[, V1 * sigmaVec^2]
    idx <- Parkinson > spec.var
    idx[is.na(idx)] <- FALSE
    sum(idx)
    #cbind(spec.var, Park)
    spec.var[idx] <- Parkinson[idx]
  }
  
  # Apply scaling to covariance matrix per equation 52
  cov.mat <- diag(spec.var) + t(covmat * sigmaVec) * sigmaVec
  
  if (calc.inv) {
    v <- factor.loadings / spec.var
    d <- solve(factor.cov) + t(factor.loadings) %*% v
    inverse.cov <- diag(1 / spec.var) - v %*% solve(d) %*% t(v)
  } else {
    inverse.cov <- NULL
  }
  
  return(list(specific.risk = sqrt(spec.var),
              factor.returns = factor.returns,
              factor.loadings = factor.loadings,
              factor.cov = factor.cov,
              cov.mat = cov.mat,
              inverse.cov = inverse.cov,
              fitdata = fitdata,
              exposures.char = exposures.char))
  
}

#' @description Function to calculate statistical risk model (using princiap component analysis). The code has been adapted from Kakushadze and Yu (2017).
#' @name fit.statistical
#' @title fit.statistical
#' @encoding UTF-8
#' @concept factor models for attribution and risk
#' @param retMat matrix (or data.table/data.frame) of returns.  Does not matter if the dates are in ascending or descending order.
#' @param use.cor boolean to use correlation matrix instead of covariance matrix, default is FALSE
#' @param erank boolean to use the effective rank instead of minimization algorithm, default is FALSE
#'
#' @return list of risk model outputs where
#' *specific.risk* is the vector idiosyncratic volatility (or specific risk),
#' *factor.loadings* is the matrix of loadings,
#' *factor.cov* is the matrix of factor covariances,
#' *cov.mat** is the matrix of variance/covariances,
#' *inverse.cov* is the inverse of the variance/covariance matrix,
#' *princomp* is the matrix of principal components (eigenvectors) of the fitted risk model,
#' *dates* is the vector of the dates used to estimate the risk model, and
#' *id* is the vector is ids representing the securities in the estimation universe.
#'
#' @examples
#' retMat <- fit.data.cast(stock, item='RETURN', id.var = 'TICKER', date.var = 'DATE', reverse = TRUE)
#' fit <- fit.statistical(retMat)
#' names(fit)
#' @references Kakushadze, Zura and Yu, Willie, Statistical Risk Models (February 14, 2016). The Journal of Investment Strategies 6(2) (2017) 1-40. Available at SSRN: \url{https://ssrn.com/abstract=2732453}
#' @author Roger J. Bos, \email{roger.bos@@gmail.com}
#' @export
fit.statistical <- function (retMat, use.cor = FALSE, erank = FALSE) {
  
  fitdata <- retMat
  dates <- names(retMat[, -1])
  id <- retMat[, 1]
  retMat <- as.matrix(retMat[, -1])
  sigma <- apply(retMat, 1, sd)
  # prevent sigma from being negative
  sigma[sigma == 0] <- mean(sigma[sigma > 0])
  
  if (use.cor) retMat <- retMat / sigma
  x <- var(t(retMat), t(retMat))
  x[is.na(x)] <- 0
  tv <- diag(x)
  e <- eigen(x)
  
  if (erank == TRUE) {
    
    # Effective Rank from Section 3.2
    er <- .calc.erank(e$values, FALSE)
    k <- min(round(er), ncol(retMat) - 2)
    factor.loadings <- t(t(e$vectors[, 1:k]) * sqrt(e$values[1:k]))
    x.f <- factor.loadings %*% t(factor.loadings)
    x.s <- tv - diag(x.f)
    x.s[x.s < 0] <- 0
    spec.risk <- sqrt(x.s)
    cov.mat <- diag(x.s) + x.f
    
  } else {
    
    # Minimization Algo from Section 3.1
    k1 <- 1
    x1 <- 0
    g.prev <- 999
    for (k in k1:(ncol(retMat) - 1)) {
      factor.loadings <- t(sqrt(e$values[k1:k]) * t(e$vectors[, k1:k]))
      x.f <- factor.loadings %*% t(factor.loadings)
      x.s <- tv - diag(x.f)
      x.s[x.s < 1e-8] <- 1e-8
      
      z <- x.s / tv
      # prevent z from being Inf
      z[is.infinite(z)] <- NA
      z[is.na(z)] <- max(z, na.rm=TRUE)
      z[z < 1e-8] <- 1e-8
      
      g <- abs(sqrt(min(z)) + sqrt(max(z)) - 1)
      if(is.na(g)) break
      if(g > g.prev) break
      g.prev <- g
      spec.risk <- sqrt(x.s)
      cov.mat <- diag(x.s) + x.f + x1
    }
    
  } # end minimization
  
  fac.cov <- diag(1, k)
  y.s <- 1 / spec.risk^2
  fac.load1 <- y.s * factor.loadings
  inv.cov <- diag(y.s) - fac.load1 %*% solve(diag(1, ncol(factor.loadings)) + t(factor.loadings) %*% fac.load1) %*% t(fac.load1)
  
  if (use.cor) {
    spec.risk <- sigma * spec.risk
    factor.loadings <- sigma * factor.loadings
    cov.mat <- sigma * t(sigma * cov.mat)
    inv.cov <- t(inv.cov / sigma) / sigma
  }
  
  return(list(specific.risk = spec.risk,
              factor.loadings = factor.loadings,
              factor.cov = fac.cov,
              cov.mat = cov.mat,
              inverse.cov = inv.cov,
              princomp = e$vectors[, 1:ncol(factor.loadings)],
              dates = dates,
              id = id))
}





#' @description Function to create risk model report from fundamental or statistical risk model output
#' @name fit.risk.summary.report
#' @title fit.risk.summary.report
#' @encoding UTF-8
#' @concept factor models for attribution and risk
#' @param riskmod object returned by fit.fundamental() or fit.statistical()
#' @param bm.wgt.var benchmark weights, can be either of string of the name of the variable that contains the weights or a vector of the weights
#' @param port.wgt.var portfolio weights, can be either of string of the name of the variable that contains the weights or a vector of the weights
#' @param filename if not NULL, results will be saved to a CSV file with the given filename
#'
#' @return list of portfolioTbl and securityTbl.
#' The portfolio table contains the following data items for the portfolio:
#' *Portfolio.Holdings* - number of portfolio holdings
#' *Benchmark.Holdings* - number of benchmark holdings
#' *Total.Risk* - predicted standard deviation of the portfolio, aka absolute risk
#' *Benchmark.Risk* - predicted standard deviation of the benchmark
#' *Active.Risk* - predicted tracing error of the portfolio to the benchmark
#' *R.Squared* - the fraction of portfolio varinace explained by the benchmark
#' *Predicted.Beta* - forecasted beta based on the risk model
#' *Specific.Risk.Pct* - percent of *Total.Risk* not explaned by the risk model factors, aka idiosyncratic risk
#' *Factor.Risk.Pct* - percent of *Total.Risk* explaned by the risk model factors
#' The security table contains the following data items for each security:
#' *portfolio.wgt* - each stock's weight in the portfolio
#' *benchmark.wgt* - each stock's weight in the benchmark
#' *active.wgt* - each stock's active weight (portfolio minus benchmark)
#' *ivol* - each stock's idiosyncratic volatility, aka stock specific risk
#' *predicted.beta* - each stock's predicted beta
#' *risk.contribution* - each stock's contribution to *Total.Risk*
#' *factor.exposures* - each stock's exposure to each factor in the risk model
#'
#' @examples
#'
#' ### Statistical
#'
#' retMat <- fit.data.cast(stock, item='RETURN', id.var = 'TICKER', date.var = 'DATE', reverse = TRUE)
#' fit <- fit.statistical(retMat)
#'
#' stock <- as.data.table(stock)
#' stock[TICKER %in% c('SUNW','ORCL','MSFT'), portfolioWeight := 1/3, by=DATE]
#' stock[is.na(portfolioWeight), portfolioWeight := 0]
#' stock[, benchmarkWeight := 1/.N, by=DATE]
#' cols <- c("TICKER","portfolioWeight")
#' portfolioWeight <- stock[DATE == max(DATE), ..cols]
#' cols <- c("TICKER","benchmarkWeight")
#' benchmarkWeight <- stock[DATE == max(DATE), ..cols]
#'
#' risk <- fit.risk.summary.report(riskmod = fit, bm.wgt.var = benchmarkWeight, port.wgt.var = portfolioWeight, filename = NULL)
#' risk$portfolioTbl
#' risk$securityTbl[Portfolio.Wgt > 0, ]
#'
#'
#' ### Fundamental
#'
#' stock <- as.data.table(stock)
#' stock[TICKER %in% c('SUNW','ORCL','MSFT'), portfolioWeight := 1/3, by=DATE]
#' stock[is.na(portfolioWeight), portfolioWeight := 0]
#' stock[, benchmarkWeight := 1/.N, by=DATE]
#' fit <- fit.fundamental(fitdata = stock, date.var = 'DATE', id.var = 'TICKER', return.var = 'RETURN',
#'                        weight.var = 'LOG.MARKETCAP', exposure.vars = c('NET.SALES','BOOK2MARKET','GICS.SECTOR'),
#'                        rob.stats = TRUE, z.score = FALSE, stdReturn = TRUE, calc.inv = TRUE, cov.wgt = FALSE, parkinson = FALSE)
#'
#' stock <- as.data.table(stock)
#' stock[TICKER %in% c('SUNW','ORCL','MSFT'), portfolioWeight := 1/3, by=DATE]
#' stock[is.na(portfolioWeight), portfolioWeight := 0]
#' stock[, benchmarkWeight := 1/.N, by=DATE]
#' cols <- c("TICKER","portfolioWeight")
#' portfolioWeight <- stock[DATE == max(DATE), ..cols]
#' cols <- c("TICKER","benchmarkWeight")
#' benchmarkWeight <- stock[DATE == max(DATE), ..cols]
#'
#' risk <- fit.risk.summary.report(riskmod = fit, bm.wgt.var = benchmarkWeight, port.wgt.var = portfolioWeight, filename = NULL)
#' risk$portfolioTbl
#' risk$securityTbl[Portfolio.Wgt > 0, ]
#'
#' @author Roger J. Bos, \email{roger.bos@@gmail.com}
#' @export
fit.risk.summary.report <- function(riskmod, bm.wgt.var, port.wgt.var, filename = NULL) {
  
  # Annualization factor
  if (!is.null(riskmod$dates)) {
    multi <- ifelse(abs(mean(diff(as.Date(riskmod$dates)), na.rm=TRUE)) >= 28, sqrt(12), sqrt(250))
  } else {
    multi <- ifelse(abs(mean(diff(as.Date(row.names(riskmod$factor.returns))), na.rm=TRUE)) >= 28, sqrt(12), sqrt(250))
  }
  
  # Get security names
  if (!is.null(riskmod$id)) {
    id <- c(riskmod$id)
  } else {
    id <- names(riskmod$specific.risk)
  }
  
  # Organize weights in the same order as the other data
  wgt <- as.data.table(x = id)
  setkey(wgt, id)
  setkeyv(bm.wgt.var, names(bm.wgt.var)[1])
  setkeyv(port.wgt.var, names(port.wgt.var)[1])
  wgt <- wgt[port.wgt.var]
  wgt <- wgt[bm.wgt.var]
  setnames(wgt, c('id','portWgt','benchWgt'))
  wgt[, activeWgt := portWgt - benchWgt]
  
  # Get main components from risk model
  specific.risk <- riskmod$specific.risk # * multi
  specific.risk[is.na(specific.risk)] <- 0
  covmat <- riskmod$cov.mat
  factcov <- riskmod$factor.cov
  
  # Security Exposure
  fact.load<- riskmod$factor.loadings
  fact.load[is.na(fact.load)] <- 0
  
  # Ending Portfolio Exposure
  expo.port <- wgt[, portWgt] %*% fact.load
  
  # Ending Benchmark Exposure
  expo.bench <- wgt[, benchWgt] %*% fact.load
  
  # Ending Active Exposure
  expo.active <- wgt[, activeWgt] %*% fact.load
  
  # Absolute Risk (Std Dev) - scale by multi to annualize
  AR.P = as.vector(sqrt(expo.port %*% factcov %*% t(expo.port) + sum(wgt[, portWgt]^2  %*% specific.risk^2))) * multi
  AR.B = as.vector(sqrt(expo.bench %*% factcov %*% t(expo.bench) + sum(wgt[, benchWgt]^2 %*% specific.risk^2))) * multi
  
  # Marginal Factor Variance
  V <- 2 * factcov %*% t(expo.active)
  
  # Factor Risk (Variance)
  FR.S <- as.vector(wgt[, activeWgt] * fact.load %*% factcov %*% t(expo.active))
  FR.P <- as.vector((expo.active * .5) %*% V) # <- sum(FR.S) # also <- (wgt[, activeWgt] %*% fact.load) %*% factcov %*% t(wgt[, activeWgt] %*% fact.load)
  
  # Stock Specific Risk (Variance)
  SSR.S <- wgt[, activeWgt]^2 * specific.risk^2
  SSR.P <- sum(SSR.S)
  
  # Total Risk
  TR.S <- FR.S + SSR.S
  TR.P <- FR.P + SSR.P
  
  # Predicted Tracking Error (Std Dev) - scale by multi to annualize
  TE <- sqrt(TR.P) * multi
  
  # R-Squared
  R2 <- (((AR.P^2 + AR.B^2 - TE^2) / 2) / (AR.P + AR.B))^2
  
  # Percent Factor Risk
  pct.S.FR <- FR.S / TR.P
  pct.P.FR <- FR.P / TR.P
  FR.S.factor <- (wgt[, activeWgt] %*% fact.load) %*% factcov * (wgt[, activeWgt] %*% fact.load)
  pct.P.FR.factor <- FR.S.factor / TR.P
  
  # Contribution to Tracking Error
  cTE.S <- TR.S / TR.P * TE
  
  # Contribution to Tracking Error - Factor Contribution
  cTE.S.FR = FR.S / TR.P * TE
  
  # Contribution to Tracking Error - Stock Specific Risk
  cTE.S.SSR = SSR.S / TR.P * TE
  
  # # Predicted Beta of the portfolio
  numer <- t(wgt[, portWgt]) %*% fact.load %*% factcov %*% t(fact.load) %*% wgt[, benchWgt] + t(wgt[, portWgt]) %*% specific.risk %*% specific.risk %*% wgt[, benchWgt]
  denom <- t(wgt[, benchWgt]) %*% fact.load %*% factcov %*% t(fact.load) %*% wgt[, benchWgt] + t(wgt[, benchWgt]) %*% specific.risk %*% specific.risk %*% wgt[, benchWgt]
  predicted.beta <- as.vector(numer / denom)
  pred.beta <- list()
  N <- wgt[, .N]
  for (ii in 1:N) {
    pWgt <- rep(0, N)
    pWgt[ii] <- 1
    numer <- t(pWgt) %*% fact.load %*% factcov %*% t(fact.load) %*% wgt[, benchWgt] + t(pWgt) %*% specific.risk %*% specific.risk %*% wgt[, benchWgt]
    denom <- t(wgt[, benchWgt]) %*% fact.load %*% factcov %*% t(fact.load) %*% wgt[, benchWgt] + t(wgt[, benchWgt]) %*% specific.risk %*% specific.risk %*% wgt[, benchWgt]
    pred.beta[[ii]] <- numer / denom
  }
  pred.beta <- as.vector(do.call("rbind", pred.beta))
  pred.beta[pred.beta < -.5] <- -.5
  pred.beta[pred.beta > 3.5] <- 3.5
  
  riskTbl <- data.table(Portfolio.Holdings = wgt[portWgt != 0, .N],
                        Benchmark.Holdings = wgt[benchWgt != 0, .N],
                        Total.Risk = round(AR.P * 100, 2),
                        Benchmark.Risk = round(AR.B * 100, 2),
                        Predicted.Tracking.Error = round(TE * 100, 2),
                        #R.Squared = round(R2, 2),
                        Predicted.Beta = round(predicted.beta, 2),
                        Specific.Risk.Pct = round(100 - pct.P.FR * 100, 2),
                        Factor.Risk.Pct = round(pct.P.FR * 100, 2))
  
  if (is.character(riskmod$exposures.char)) {
    echar <- unique(fa$fitdata[, fa$exposures.char, with=FALSE])
    # echarsum <  sum(pct.P.FR.factor[colnames(pct.P.FR.factor) %in% unlist(echar)])
    echarTbl <- data.table(echar = sum(pct.P.FR.factor[colnames(pct.P.FR.factor) %in% unlist(echar)])) * 100
    names(echarTbl) <- fa$exposures.char %+% ".Risk.Pct"
    riskTbl <- cbind(riskTbl, echarTbl)
  }

  varianceTbl <- data.table('Factor %' = round(pct.P.FR.factor, 2) * 100)
  if (names(varianceTbl)[1] == "Factor %.V1") names(varianceTbl) <- gsub(".V", ".Blind", names(varianceTbl))
  
  exposureTbl <- data.table(Act.Expo = round(expo.active * 100, 4))
  if (names(exposureTbl)[1] == "Act.Expo.V1") names(exposureTbl) <- gsub(".V", ".Blind", names(exposureTbl))
  
  securityTbl <- data.table(Security = id,
                            Portfolio.Wgt = round(wgt[, portWgt] * 100, 2) ,
                            Benchmark.Wgt = round(wgt[, benchWgt] * 100, 2),
                            Active.Wgt = round(wgt[, activeWgt] * 100, 2),
                            Ivol = round(riskmod$specific.risk * 100, 2),
                            Predicted.Beta = round(pred.beta, 2),
                            Risk.Contribution = round((TR.S / TR.P) * 100, 2),
                            Fact.Expo = round(fact.load * 100, 2))
  if (names(securityTbl)[8]=='Fact.Expo.V1') names(securityTbl) <- gsub(".V", ".Blind", names(securityTbl))
  #names(securityTbl)
  
  if (!is.null(filename)) {
    write.table(x="Portfolio Risk Summary generated " %+% today(), file=filename, append=FALSE,row.names = FALSE, col.names = FALSE, sep=",")
    write.table(x="Risk Characteristics",                          file=filename, append=TRUE, row.names = FALSE, col.names = FALSE, sep=",")
    write.table(x=t(riskTbl),                                      file=filename, append=TRUE, row.names = TRUE,  col.names = FALSE, sep=",")
    write.table(x="Risk as % of Variance",                         file=filename, append=TRUE, row.names = FALSE, col.names = FALSE, sep=",")
    write.table(x=t(varianceTbl),                                  file=filename, append=TRUE, row.names = TRUE,  col.names = FALSE, sep=",")
    write.table(x="Active Exposure",                               file=filename, append=TRUE, row.names = FALSE, col.names = FALSE, sep=",")
    write.table(x=t(exposureTbl),                                  file=filename, append=TRUE, row.names = TRUE,  col.names = FALSE, sep=",")
    write.table(x="Security Table",                                file=filename, append=TRUE, row.names = FALSE, col.names = FALSE, sep=",")
    suppressWarnings(write.table(x=securityTbl,                    file=filename, append=TRUE, row.names = FALSE, sep=","))
  }
  
  return(list(portfolioTbl = cbind(riskTbl, varianceTbl, exposureTbl), securityTbl = securityTbl))
}

