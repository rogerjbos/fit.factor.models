% Generated by roxygen2: do not edit by hand
% Please edit documentation in R/fit.factor.models.R
\encoding{UTF-8}
\name{fit.data.cast}
\alias{fit.data.cast}
\title{fit.data.cast}
\usage{
fit.data.cast(datMat, item, id.var, date.var, reverse = FALSE)
}
\arguments{
\item{datMat}{data.table of rawdata}

\item{item}{string name of the data items to extract}

\item{id.var}{string name of the identifier that will make up the row names}

\item{date.var}{string name of the dates that will make up the column names}

\item{reverse}{logical to reverse the dates in the output, so the first column will be the most recent date, defaults to FALSE}
}
\value{
data.table with the first column being the ids and the subsequent columns being the data 'item'
}
\description{
Function to create a data.table (wide format) from a column of long format, uses reshape2::dcast()
}
\examples{
load("data/Stock.df.Rdata")
retMat <- fit.data.cast(stock, item='RETURN', id.var = 'TICKER', date.var = 'DATE', reverse = TRUE)
}
\author{
Roger J. Bos, \email{roger.bos@gmail.com}
}
\concept{factor models for attribution and risk}
