% Generated by roxygen2: do not edit by hand
% Please edit documentation in R/fit.factor.models.R
\docType{package}
\encoding{UTF-8}
\name{fit.attribution}
\alias{fit.attribution}
\alias{fit.attribution-package}
\title{fit.attribution}
\usage{
fit.attribution(fitdata, date.var, id.var, return.var, exposure.vars,
  weight.var = NULL, rob.stats = FALSE, full.resid.cov = FALSE,
  z.score = FALSE, stdReturn = FALSE, resid.EWMA = FALSE,
  lambda = 0.9, ...)
}
\arguments{
\item{date.var}{string name of the date column}

\item{id.var}{string name of the id column}

\item{return.var}{string name of the return column}

\item{weight.var}{string name of the weight column}

\item{rob.stats}{logical}

\item{full.resid.cov}{logical}

\item{z.score}{logical}

\item{resid.EWMA}{logical}

\item{exposures.var}{vector of string name(s) of the column(s) to use as exposures (attributes)}

\item{strReturns}{logical}
}
\value{
An object with S3 class "fir.factor.models" containing:

beta a matrix of security exposures for the last time period

factor.returns a matrix of factor returns by date

residuals a list of regression residuals by date

r2 a vector of regression R-squared values

factor.cov a matrix of factor variances / covariances

resid.cov a matrix of residual variances / covariances

return.cov a matrix of return variances / covariances

resid.var a vector of residual variances

call the function call

fitdata a data.table of data to use for attribution

exposure.vars a vector of string names of factors to use for attribution

weight.var = weight.var,

date.var a string name of the column with dates

return.var a string name of the column with returns

id.var a string name of the column with IDs

id.names a vector of security names or IDs

factor.names a vector of factor names

exposures.char the name of the grouping column, if applicable

time.periods a vector of the dates
}
\description{
Function to calculate factor returns for portfolio attribution analysis.  The code has been adapted from the factorAnalyticsAddons package (Uthaisaad, 2017).
}
\examples{
fit <- fit.attribution(fitdata = stock, date.var = 'DATE', id.var = 'TICKER', return.var = 'RETURN',
  weight.var = 'LOG.MARKETCAP', exposure.vars = c('NET.SALES','BOOK2MARKET','GICS.SECTOR'),
  rob.stats = TRUE, full.resid.cov = FALSE, z.score = FALSE,
  stdReturn = TRUE, resid.EWMA = TRUE)
}
\references{
\url{https://github.com/chindhanai/factorAnalyticsAddons}
}
\author{
Roger J. Bos, \email{roger.bos@gmail.com}
}
\concept{factor models for attribution and risk}
