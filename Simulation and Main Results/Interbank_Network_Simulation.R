library(MASS)
library(igraph)
library(xtable)
library(plyr)
library(parallel)
library(stargazer)


rm(list = ls())

############################################
######### THE PARAMETERS OF THE SYSTEM #####
############################################

# define how man bank in the network there are
d = 20

# define over how many periods to simulate the transactions
T = 31

bad.prop = 0.2
big.prop = 0.3
bad.d <- floor(bad.prop*d)
big.d <- floor(bad.prop*d)
good.d <- d-bad.d
small.d <- d-(big.d + bad.d)

set.seed(2004)
SCALE = 1
Mu1 <- round(c(runif(bad.d+small.d,1,2),runif(big.d,3,4)),2)*SCALE
Mu2 <- round(Mu1*0.5,2)

# set the covariance matrix
sig1 <- round(c(runif(bad.d,0.5,1),runif(small.d,0.5,1),runif(big.d ,1,2)),2)*SCALE
sig2 <- sig1 # assume that both regimes have the same volatilities

p.borrow1 <-  round(pnorm(0,Mu1,sig1),2)
p.borrow2 <-  round(pnorm(0,Mu2,sig1),2)

# order banks to be randomly sampled
banks.order <- sample(1:d)
Mu1 <- Mu1[banks.order];
Mu2 <- Mu2[banks.order];
sig1 <- sig1[banks.order]
sig2 <- sig1

Mu1; Mu2
# set the correlation matrix
d1 <- floor(0.5*d) # split banks into cluster into the correlation matrix
d2 <- d-d1


# set the correlation for each cluster
rho1 <- 0.5
rho2 <- 0.5
between.rho <- 0

# transition probabilities between the two states
p1 <- round(runif(d,0.9,0.99),2)
p2 <- round(runif(d,0.6,0.7),2)

# create a transition matrix for each bank
P <- numeric()
for(i in 1:d) {
  P[i] <-  list(rbind(c(p1[i],1-p1[i]),c(1-p2[i],p2[i])))
}


############ Table 1:  Identifying the Inherent Network Structure ###########

table1 <- cbind(Mu1,Mu2,sig1,p.borrow1,p.borrow2,p1,p2)
xtable(table1)


##########################################################################################################

##########################################################
##################### SIMULATION #########################
##########################################################

######################### PAYMENT SIMULATION ######################################

payment_sim <- function(Mu1,Mu2,sig1,sig2,rho1,rho2,between.rho,P,T,shock.bank,shock.t,shock.k) {
  d <- length(Mu1)

  # given the mus and sigmas, generate the payment simulation
  rho.m1 <- matrix(rho1,d1,d1);diag(rho.m1) <- 1
  rho.m2 <- matrix(rho2,d2,d2);diag(rho.m2) <- 1
  rho.m3 <- matrix(between.rho,d1,d2)
  rho.m <- rbind(cbind(rho.m1,rho.m3),cbind(t(rho.m3),rho.m2))
  
  Sig1 <- diag(sig1)%*%rho.m%*%diag(sig1)
  Sig2 <- Sig1
  
  # make the transition on the entity level indepedent
  {
  # function for transition
  s0 <- rep(1,d)
  st <- function(state) {
    P.state <- lapply(1:d,function(i) P[[i]][state[i],])
    return(unlist(lapply(P.state,function(p) sample(1:2,1,prob = p))))
  } 
  
  # S is the transition for each bank over time
  S <- t(as.matrix(s0))
  for(t. in 2:T) {
    S <- rbind(S,st(S[t.-1,]))
  }
  
  # generate the data
  X1 <- mvrnorm(T,Mu1,Sig1)
  #set.seed(seed)
  X2 <- mvrnorm(T,Mu2,Sig2)
  
  X <- matrix(NA,T,d)
  s1.index <- which(S==1,arr.ind = T)
  s2.index <- which(S==2,arr.ind = T)
  X[s1.index[,1],s1.index[,2]] <- X1[s1.index[,1],s1.index[,2]]
  X[s2.index[,1],s2.index[,2]] <- X2[s2.index[,1],s2.index[,2]]

  any(apply(X,1,sum) < 0 )
  }
  # --> add shock <--- 
  X[shock.t,shock.bank] = X[shock.t,shock.bank] - shock.k*abs(X[shock.t,shock.bank])
  
  # keep X0 as exogenous X
  X0 <- X
  
  # check how many times there is not sufficient funds in the market
  # for the GAP condition
  
  # then what happen is that borrowing would create any distress
  Y <- matrix(0,nrow(X),ncol(X))
  
  W1 <- matrix(0,d,d) # weights of nodes as binary values
  W2 <- matrix(0,d,d) # weights of nodes as capital value
  
  # take the index of those banks that borrow
  ij.list <- numeric()
  IJ <- numeric()
  
  # keep track of the dropped banks
  drop.t.i <- numeric()
  
  # which ever bank does not find sufficient liquidity leaves the network
  
  # start loop
  i <- 1
  while(i < nrow(X)) {
    # reset the index matrix to 
    
    
    ij <- numeric()
    
    if( any(X[i,]<0) ) { # condition for borrowing
      
      j <- which(X[i,]<0) # the distressed bank index
      k <- which(!X[i,]<0) # the lending banks index
      
      x.j <- X[i,j]
      x.k <- X[i,k]
      # the most distressed bank borrows first and so on
      #it borrows from most liquid bank
      oj <- order(x.j)
      ok <- order(x.k,decreasing =T)
      # sort them accordigly
      j <- j[oj]
      k <- k[ok]
      
      x.k <- X[i,k] # banks surplus
      
      borrow.needed <- rep(0,d)
      borrow.needed[j] <- -X[i,j]
      
      # insufficient supply of funds
      if(sum(x.k) - sum(borrow.needed) < 0)  { 
        cat("insufficient aggregate liquidity at time ",i,"\n")   
        # find which is the problematic bank
        # drop the bank that has the largest need of liquidity
        drop.i <- which(borrow.needed == max(borrow.needed))
        
        # but before we do, we let it to dry up liquidity
        j. <- drop.i
        # find all the banks with which j. interacted in the past
        if(length(IJ) > 0) {
          k <- unique(c(IJ[IJ[,1] == j.,2]),c(IJ[IJ[,2] == j.,1])) # index all previous partners
          k <- k[order(X[i,k],decreasing  = T)] 
          k <- k[X[i,k]>0] # keep the ones with positive net
        }
        
        # what if there is no one?
        if( length(k) == 0 || length(IJ) == 0) {
            cat("there is no to lend to ",j.,"\n")
          k <- j.
        }
        
        # look at the other banks with whom the bank interacted
        # the following loop iterates through all former partners with positive net
        while( sum(X[i,k]) > 0  & borrow.needed[j.] > 0) { # in this case the banks dries up liquidity
          
          k. <- k[order(X[i,k],decreasing =T)][1]
          cat(j.," is drying up ",k.,"\n")
          
          # this is to signal the time slots in which more than one bank
          # were needed to supply liquidity to the same bank
          #if(X[i,k.] < borrow.needed[j.]) cat(i,i,"more than one bank needed","\n")
          # order according to most liquid
          # consider the case where there is shortfall in liquidity
          k.lent <- min(X[i,k.],borrow.needed[j.])
          Y[i,j.] <- Y[i,j.] + k.lent  # can not borrow more than what needed or the lending bank has to offer
          X[i,j.] <- X[i,j.] + k.lent # lend
          
          # update on the lender side
          X[i,k.] <- X[i,k.] - k.lent # lend
          # weighting matrix counts the times of borrowing
          W1[k.,j.] <- W1[k.,j.] + 1
          # weighting matrix counts the amounts of borrowing
          W2[k.,j.] <- W2[k.,j.] + k.lent
          ij <- rbind(ij,c(k.,j.))
          
          # since bank j. will drop next period, it won't pay back and its
          # counterpart will suffer a loss
          # then don't update the next period
          
          # update the needed borrowing
          borrow.needed[j.] <- -X[i,j.]
        }
        
        drop.t.i <- rbind(drop.t.i,c(i,drop.i))
        X[i:nrow(X),drop.i] <- 0
        # make sure to stop the economy in case all banks drop
        if(length(drop.t.i[,2]) == d) break
        next # goes back into the loop at the same time to see whether other banks would be dropped
      }
      
      else {
        for(j. in j) {
          while( X[i,j.] < 0) {
            k. <- k[order(X[i,k],decreasing =T)][1]
            # this is to signal the time slots in which more than one bank
            # were needed to supply liquidity to the same bank
            # if(X[i,k.] < borrow.needed[j.]) cat(i,i,"more than one bank needed","\n")
            # order according to most liquid
            # consider the case where there is shortfall in liquidity
            k.lent <- min(X[i,k.],borrow.needed[j.])
            Y[i,j.] <- Y[i,j.] + k.lent  # can not borrow more than what needed or the lending ban has to offer
            X[i,j.] <- X[i,j.] + k.lent # lend
            
            # update on the lender side
            X[i,k.] <- X[i,k.] - k.lent # lend
            # weighting matrix counts the times of borrowing
            W1[k.,j.] <- W1[k.,j.] + 1
            # weighting matrix counts the amounts of borrowing
            W2[k.,j.] <- W2[k.,j.] + k.lent
            ij <- rbind(ij,c(k.,j.))
            X[i+1,j.] <- X[i+1,j.] - k.lent # pay back
            X[i+1,k.] <- X[i+1,k.] + k.lent # get back 
            # update the needed borrowing
            borrow.needed[j.] <- -X[i,j.]
          }
        }
      }
    }
    
    if(length(ij)>0) {
      rownames(ij) <- rep(i,nrow(ij))
      IJ <- rbind(IJ,ij)
      ij.list[i] <- list(ij)
    }
    i <- i+1
    
  }  # end of loop
  
  
  #######################
  
  ### NETWORK RELATED DEFINITIONS
  m1 <- (W1) # adjacency matrix for the count
  m2 <- (W2) # adjacency matrix for the amount
  d. <- 1:d
  
  # drop those banks that do nothing
  if( length(IJ) > 0 ) {
    active.banks <- d.[d. %in% c(unique(IJ[,1]),unique(IJ[,2]))]
    m1 <- m1[active.banks,active.banks]
    m2 <- m2[active.banks,active.banks]
    colnames(m1) <- active.banks; rownames(m1) <- active.banks
    colnames(m2) <- active.banks; rownames(m2) <- active.banks  
  }
  
  ## FINALLY STACK ALTOGETHER IN A LIST
  list(term.i = i-1,Y.mat = Y, X.mat = X, X0.mat = X0, S.mat = S,IJ.mat = IJ, M1 = m1, M2 = m2, banks.dropped = drop.t.i)
  } 

### SUMMARIZE THE NETWORK FOR A GIVEN RUN
network.summary <- function(network.i) {
  term.i <- network.i$term.i # denotes when the simulation was terminated
  Y <-  network.i$Y.mat
  Y <- Y[1:term.i,]
  X <-  network.i$X.mat
  X <- X[1:term.i,]
  IJ <-  network.i$IJ.mat
  if(length(IJ) == 0) return(NA)
  m1 <- network.i$M1
  m2 <- network.i$M2
  
  dropped.banks   <- network.i$banks.dropped
  n <- 0
  failed.banks <- NA
  if(length(dropped.banks ) > 0) {
    dbanks <- dropped.banks[,2] 
    n <- length(dbanks)
    failed.banks <- paste(dbanks,collapse = ",")
    }
  
  lend = apply(m1,1,sum) # lenders
  top5.lend = sort(lend,decreasing = TRUE)[1:5]
  top5.lend <- paste(sort(as.numeric(names(top5.lend))),collapse = ",")
  
  borrow = apply(m1,2,sum) # borrowers
  top5.borrow = sort(borrow,decreasing = TRUE)[1:5]
  top5.borrow <- paste(sort(as.numeric(names(top5.borrow))),collapse = ",")
  IJ.table = table(apply(IJ,1,function(x) paste(x,collapse = "->")))
  top.pairs <-  paste(names(which(IJ.table == max(IJ.table))), collapse = " , ")
  
  result <- data.frame(length = term.i,avg_amount = mean(Y[Y>0]), total_borrow = sum(m1), n_failed = n,failed_banks = failed.banks,top_borrow = top5.borrow, top_lend = top5.lend, common_pairs = top.pairs )
  return(result)
}

##### PLOT NETWORK #####
plot.network <- function(FF) {
  Y = FF$Y.mat
  X = FF$X.mat
  X0 = FF$X0.mat
  S = FF$S.mat
  banks.dropped <- FF$banks.dropped
  i = FF$term.i
  
  m1 = FF$M1
  m2 = FF$M2
  # for the graph plot
  net2=graph.adjacency(m2,mode="directed",weighted=TRUE,diag=FALSE) 
  # highlight the seized banks
  node.col = rep("lightgreen",ncol(m1))
  if( length(banks.dropped) > 0 ) {
    node.col[banks.dropped[,2]] <- "red"
  }
  
  names(node.col) <- colnames(m1)
  
  # distinguish size among banks
  node.size <- Mu1[ as.numeric(colnames(m1))]^2 + 10
  names(node.size) <- colnames(m1)
  
  plot.net <- plot.igraph(net2,vertex.label=V(net2)$name,layout=layout.fruchterman.reingold, vertex.label.color="black",edge.color="black",edge.width=E(net2)$weight/(mean(Y[Y>0])), edge.arrow.size=0.5, vertex.size=node.size,vertex.color = node.col )
  return(plot.net)
  }


#######################################################################################################


############ Table 4: Risk Analysis for Quasi Autarky versus Full Integration Networks ###########

N = 1000
table1.a.sum <- table1.b.sum <- numeric()
for (n.shock in c(0,1,2,4)) {
  cat("This is ",n.shock, " banks shocked out of 4","\n")
  # shock analysis
  shock.t <- 10
  shock.k <- 10 # zero means no shock
  shock.bank <- numeric()
  # fix everything in the payment.sim function 
 
  sim.q.f <- function(i.sim) {
    quasi.f <- function() payment_sim(Mu1,Mu2,sig1,sig2,0.5,0.5,0,P,T,shock.bank,shock.t,shock.k)
    full.f <- function() payment_sim(Mu1,Mu2,sig1,sig2,0.25,0.25,0.25,P,T,shock.bank,shock.t,shock.k)
    #seed <- unclass(as.POSIXct(strptime(date(),"%c"))) + i.sim
    seed <- i.sim
    set.seed(seed)
    shock.bank <- sample(c(3,4,18,19),n.shock)
    list(quasi.f(),full.f())
    }
  
  list.summary <- mclapply(1:N,sim.q.f)
    
  network.list.quasi <- lapply(list.summary,function(x) x[[1]])
  network.list.full <- lapply(list.summary,function(x) x[[2]])
  
  list.summary.quasi <- lapply(network.list.quasi,network.summary)
  list.summary.full <- lapply(network.list.full,network.summary)
  
  summary.df.q <- ldply(list.summary.quasi,data.frame)
  summary.df.f <- ldply(list.summary.full,data.frame)
  
  # summarize numerical results
  F.quasi <- summary.df.q$n_failed
  F.full <- summary.df.f$n_failed
  
  sum.F <- function(x)  rbind(mean(x),quantile(x,0.99))

  table1.a.sum <- cbind(table1.a.sum,  sum.F(F.quasi)  )
  table1.b.sum <- cbind(table1.b.sum,  sum.F(F.full)  )
    
  }

########## FIGURE 2 ###############
plot.network(network.list.quasi[[1]])
plot.network(network.list.full[[1]])


#### TABLE 4 FULL INTEGRATION VS. QUASI AUTARKY SUMMARY
rbind(table1.a.sum,table1.b.sum)

################### SENSITIVITY ANALYSIS ###############

# consider different values for correlation coefficients
N <- 1000

rho1.seq <- seq(0.5,0.9,length = 10) 
rho2.seq <- seq(-0.5,0.5,length = 10)
RHO_mat <- expand.grid(rho1.seq,rho2.seq) 
colnames(RHO_mat) <- c("Within","Between")

# repeat the same function above, but with repsect to different rhos
sensitivity_rho1_rho2 <- function(rho_in,rho_between) { 
  result <- numeric()
  
  for (n.shock in c(0,1,2,4)) {
    cat("This is ",n.shock, " banks shocked out of 4","\n")
    # shock analysis
    shock.t <- 10
    shock.k <- 10 # zero means no shock
    shock.bank <- numeric()
    
    # fix everything in the payment.sim function 
    sim.q.f <- function(i.sim) {
      net.f <- function() payment_sim(Mu1,Mu2,sig1,sig2,rho_in,rho_in,rho_between,P,T,shock.bank,shock.t,shock.k)
      seed <- i.sim
      set.seed(seed)
      shock.bank <- sample(c(3,4,18,19),n.shock)
      return(net.f())
      }
    
    list.summary <- mclapply(1:N,sim.q.f)
    list.summary2 <- lapply(list.summary,network.summary)
    summary.df <- ldply(list.summary2,data.frame)

    # summarize numerical results
    Fails <- summary.df$n_failed
    result.n <- data.frame(rho_in = rho_in, rho_between  =  rho_between, n.shock, F_bar = mean(Fails), Q99 = quantile(Fails,0.99))
    result <- rbind(result,result.n)
    }
  return(result)
  }


main_ds_list <- mclapply(  1:nrow(RHO_mat), function(index) {cat("######################### ",index,"\n"); return(sensitivity_rho1_rho2(RHO_mat[index,"Within"],RHO_mat[index,"Between"])) } )

###################################
############ CONTOUR ##############
###################################
DS <- ldply(main_ds_list,data.frame)
DS.list <- dlply(DS,"n.shock",data.frame)


#### FIGURE 4 PANEL A #######
ds.plot <- DS.list[[1]]
X <- unique(ds.plot$rho_in)
Y <- unique(ds.plot$rho_between)
Z <- matrix(ds.plot$F_bar,length(X))
filled.contour(x = X,y = Y, z = Z,zlim = range(DS$F_bar))

#### FIGURE 4 PANEL B #######
ds.plot <- DS.list[[4]]
X <- unique(ds.plot$rho_in)
Y <- unique(ds.plot$rho_between)
Z <- matrix(ds.plot$F_bar,length(X))
filled.contour(x = X,y = Y, z = Z,zlim = range(DS$F_bar))

#### FIGURE 4 PANEL C #######
ds.plot <- DS.list[[1]]
X <- unique(ds.plot$rho_in)
Y <- unique(ds.plot$rho_between)
Z <- matrix(ds.plot$Q99,length(X))
filled.contour(x = X,y = Y, z = Z,zlim = range(DS$Q99))


#### FIGURE 4 PANEL D #######
ds.plot <- DS.list[[4]]
X <- unique(ds.plot$rho_in)
Y <- unique(ds.plot$rho_between)
Z <- matrix(ds.plot$Q99,length(X))
filled.contour(x = X,y = Y, z = Z,zlim = range(DS$Q99))



##############################################
############ REGRESSION RESULTS ##############
##############################################

#### AVERAGE FAILURE ########
lm.list1 <- lapply(DS.list, function(DS.I)  lm(F_bar ~I(rho_in*rho_between), data = DS.I   )  )
lm.list2 <- lapply(DS.list, function(DS.I)  lm(F_bar ~I(rho_in*rho_between) + I((rho_in*rho_between)^2) , data = DS.I   )  )


lm.list <- list()
lm.list[seq(1,7,by = 2)] <- lm.list1
lm.list[seq(2,8,by = 2)] <- lm.list2
stargazer(lm.list)


#### 99 QUANTILE #######
lm.list1 <- lapply(DS.list, function(DS.I)  lm(Q99 ~I(rho_in*rho_between), data = DS.I   )  )
lm.list2 <- lapply(DS.list, function(DS.I)  lm(Q99 ~I(rho_in*rho_between) + I((rho_in*rho_between)^2) , data = DS.I   )  )

lm.list <- list()
lm.list[seq(1,7,by = 2)] <- lm.list1
lm.list[seq(2,8,by = 2)] <- lm.list2
stargazer(lm.list)

