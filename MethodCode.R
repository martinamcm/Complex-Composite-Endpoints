library(MASS)
library(stats)
library(mvtnorm)
library(nlme)
library(boot)
#library(car)
library(matrixcalc)
#library(profvis)
library(numDeriv)
library(R2Cuba)
library(optimx)
library(brglm)
library(Matrix)

###LATENT VARIABLE CODE FOR FOUR DIMENSIONAL COMPOSITE ENDPOINT
###COMPONENTS: TWO CONTINUOUS, ONE ORDINAL, ONE BINARY 

##STARTING VALUES

X<-c() #Add based on data
dat<-data.frame(id,treat,Z1,Z2,Z3ord,Z4ord,Z10,Z20) ## ORDER OF DATA INPUT

##LIKELIHOOD FUNCTION

f<-function(X,dat)
{
  
  dat<-dat[!is.na(dat[,3]),]
  
  #parameters
  alpha0 <- X[1]
  alpha1 <- X[2]
  beta0 <- X[3]
  beta1 <- X[4]
  gamma1 <- X[5]
  psi0 <- X[6]
  psi1 <- X[7]
  
  #covariance parameters
  sig1 <- exp(X[8]) 
  sig2 <- exp(X[9]) 
  rho12 <- 2*inv.logit(X[10])-1
  rho13 <- 2*inv.logit(X[11])-1
  rho14 <- 2*inv.logit(X[12])-1
  rho23 <- 2*inv.logit(X[13])-1
  rho24 <- 2*inv.logit(X[14])-1
  rho34 <- 2*inv.logit(X[15])-1
  
  #ordinal cutoffs
  tau13 <- X[16]
  tau23 <- X[17]
  tau33 <- X[18]
  tau43 <- X[19]
  
  #addition baseline parameters
  alpha2 <- X[20]
  beta2 <- X[21]
  
  
  #Known cutoffs
  tau03 <- -Inf 
  tau53 <- +Inf
  tau04 <- -Inf
  tau14<- 0
  tau24<- +Inf
  
  #model means
  muz1<-alpha0+alpha1*dat[,2]+alpha2*dat[,7]
  muz2<-beta0+beta1*dat[,2]+beta2*dat[,8]
  muz3<-gamma1*dat[,2]#+gamma2*dat[,9]
  muz4<-psi0+psi1*dat[,2]
  
  #conditional means
  muz3cond <- muz3+((rho13-rho12*rho23)*(dat[,3]-muz1)/(sig1*(1-(rho12)^2)))+((rho23-rho13*rho12)*(dat[,4]-muz2)/(sig2*(1-(rho12)^2)))
  muz4cond <- muz4+((rho14-rho12*rho24)*(dat[,3]-muz1)/(sig1*(1-(rho12)^2)))+((rho24-rho14*rho12)*(dat[,4]-muz2)/(sig2*(1-(rho12)^2)))
  
  #condational covariance
  matcond11 <- 1-(((rho13)^2-2*rho12*rho13*rho23+(rho23)^2)/(1-(rho12)^2))
  matcond12 <- rho34-((rho13*rho14-rho13*rho12*rho24-rho12*rho14*rho23+rho23*rho24)/(1-(rho12)^2))
  matcond22 <- 1-(((rho14)^2-2*rho12*rho14*rho24+(rho24)^2)/(1-(rho12)^2))
  Sigcond <- matrix(c(matcond11, matcond12, matcond12, matcond22), nrow=2, ncol=2) 
  Sigcond2 <-(Sigcond*t(Sigcond))^0.5
  
  #continuous bivariate covariance
  
  matbiv11 <- (sig1)^2
  matbiv12 <- rho12*sig1*sig2
  matbiv22 <- (sig2)^2
  Sigbiv   <- matrix(c(matbiv11, matbiv12, matbiv12, matbiv22), nrow=2, ncol=2)
  Sigbiv <- (Sigbiv*t(Sigbiv))^0.5
  
  #upperlimits
  mu11<-matrix(c(tau13-muz3cond, tau14-muz4cond), ncol=2)
  mu01<-matrix(c(tau03-muz3cond, tau14-muz4cond), ncol=2)
  mu10<-matrix(c(tau13-muz3cond, tau04-muz4cond), ncol=2)
  mu00<-matrix(c(tau03-muz3cond, tau04-muz4cond), ncol=2)
  mu21<-matrix(c(tau23-muz3cond, tau14-muz4cond), ncol=2)
  mu20<-matrix(c(tau23-muz3cond, tau04-muz4cond), ncol=2)
  mu31<-matrix(c(tau33-muz3cond, tau14-muz4cond), ncol=2)
  mu30<-matrix(c(tau33-muz3cond, tau04-muz4cond), ncol=2)
  mu41<-matrix(c(tau43-muz3cond, tau14-muz4cond), ncol=2)
  mu40<-matrix(c(tau43-muz3cond, tau04-muz4cond), ncol=2)
  mu51<-matrix(c(tau53-muz3cond, tau14-muz4cond), ncol=2)
  mu50<-matrix(c(tau53-muz3cond, tau04-muz4cond), ncol=2)
  mu12<-matrix(c(tau13-muz3cond, tau24-muz4cond), ncol=2)
  mu02<-matrix(c(tau03-muz3cond, tau24-muz4cond), ncol=2)
  mu22<-matrix(c(tau23-muz3cond, tau24-muz4cond), ncol=2)
  mu32<-matrix(c(tau33-muz3cond, tau24-muz4cond), ncol=2)
  mu42<-matrix(c(tau43-muz3cond, tau24-muz4cond), ncol=2)
  mu52<-matrix(c(tau53-muz3cond, tau24-muz4cond), ncol=2)
  
  pr11<-apply(mu11,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  pr01<-apply(mu01,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  pr10<-apply(mu10,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  pr00<-apply(mu00,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  pr21<-apply(mu21,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  pr20<-apply(mu20,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  pr31<-apply(mu31,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  pr30<-apply(mu30,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  pr41<-apply(mu41,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  pr40<-apply(mu40,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  pr51<-apply(mu51,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  pr50<-apply(mu50,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  pr12<-apply(mu12,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  pr02<-apply(mu02,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  pr22<-apply(mu22,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  pr32<-apply(mu32,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  pr42<-apply(mu42,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  pr52<-apply(mu52,1,function(x){return(pmvnorm(lower=c(-Inf,-Inf),upper=x,mean=c(0,0),sigma = Sigcond2))})
  prz12<-dmvnorm(cbind(dat[,3],dat[,4]), c(mean(muz1), mean(muz2)), Sigbiv)
  
  ##Likelihood function
  
  #components of likelihood, w=1,..5 (ordinal); k=1,2 (binary)
  l1<-log(pr11-pr01-pr10+pr00)+log(prz12)#w=1,k=1
  l2<-log(pr21-pr11-pr20+pr10)+log(prz12)#w=2, k=1
  l3<-log(pr31-pr21-pr30+pr20)+log(prz12)#w=3, k=1
  l4<-log(pr41-pr31-pr40+pr30)+log(prz12)#w=4, k=1
  l5<-log(pr51-pr41-pr50+pr40)+log(prz12)#w=5, k=1
  l6<-log(pr12-pr02-pr11+pr01)+log(prz12)#w=1, k=2
  l7<-log(pr22-pr12-pr21+pr11)+log(prz12)#w=2, k=2
  l8<-log(pr32-pr22-pr31+pr21)+log(prz12)#w=3, k=2
  l9<-log(pr42-pr32-pr41+pr31)+log(prz12)#w=4, k=2
  l10<-log(pr52-pr42-pr51+pr41)+log(prz12)#w=5, k=2
  
  data0 <- cbind(dat[,5],dat[,6],l1)#1,1
  data1 <- cbind(dat[,5],dat[,6],l2)#2,1
  data2 <- cbind(dat[,5],dat[,6],l3)#3,1
  data3 <- cbind(dat[,5],dat[,6],l4)#4,1
  data4 <- cbind(dat[,5],dat[,6],l5)#5,1
  data5 <- cbind(dat[,5],dat[,6],l6)#1,2
  data6 <- cbind(dat[,5],dat[,6],l7)#2,2
  data7 <- cbind(dat[,5],dat[,6],l8)#3,2
  data8 <- cbind(dat[,5],dat[,6],l9)#4,2
  data9 <- cbind(dat[,5],dat[,6],l10)#5,2
  
  #1,1
  data0[data0[,1]==1,3]<-0 #2,1==0
  data0[data0[,1]==2,3]<-0 #3,1==0
  data0[data0[,1]==3,3]<-0 #4,1==0
  data0[data0[,1]==4,3]<-0 #5,1==0
  data0[data0[,2]==1,3]<-0 #,1==0
  
  #2,1
  data1[data1[,1]==0,3]<-0 #1,1==0
  data1[data1[,1]==2,3]<-0 #3,1==0
  data1[data1[,1]==3,3]<-0 #4,1==0
  data1[data1[,1]==4,3]<-0 #5,1==0
  data1[data1[,2]==1,3]<-0 #1,2==0
  
  #3,1
  data2[data2[,1]==0,3]<-0 #1,1==0
  data2[data2[,1]==1,3]<-0 #2,1==0
  data2[data2[,1]==3,3]<-0 #4,1==0
  data2[data2[,1]==4,3]<-0 #5,1==0
  data2[data2[,2]==1,3]<-0 #1,2==0
  
  #4,1
  data3[data3[,1]==0,3]<-0 #1,1==0
  data3[data3[,1]==1,3]<-0 #2,1==0
  data3[data3[,1]==2,3]<-0 #3,1==0
  data3[data3[,1]==4,3]<-0 #5,1==0
  data3[data3[,2]==1,3]<-0 #1,2==0
  
  #5,1
  data4[data4[,1]==0,3]<-0 #1,1==0
  data4[data4[,1]==1,3]<-0 #2,1==0
  data4[data4[,1]==2,3]<-0 #3,1==0
  data4[data4[,1]==3,3]<-0 #4,1==0
  data4[data4[,2]==1,3]<-0 #1,2==0
  
  #1,2
  data5[data5[,2]==0,3]<-0 #1,1==0
  data5[data5[,1]==1,3]<-0 #2,1==0
  data5[data5[,1]==2,3]<-0 #3,1==0
  data5[data5[,1]==3,3]<-0 #4,1==0
  data5[data5[,1]==4,3]<-0 #5,1==0
  
  #2,2
  data6[data6[,2]==0,3]<-0 #1,1==0
  data6[data6[,1]==0,3]<-0 #2,1==0
  data6[data6[,1]==2,3]<-0 #3,1==0
  data6[data6[,1]==3,3]<-0 #4,1==0
  data6[data6[,1]==4,3]<-0 #5,1==0
  
  #3,2
  data7[data7[,2]==0,3]<-0 #1,1==0
  data7[data7[,1]==0,3]<-0 #2,1==0
  data7[data7[,1]==1,3]<-0 #3,1==0
  data7[data7[,1]==3,3]<-0 #4,1==0
  data7[data7[,1]==4,3]<-0 #5,1==0
  
  #4,2
  data8[data8[,2]==0,3]<-0 #1,2==0
  data8[data8[,1]==0,3]<-0 #1,1==0
  data8[data8[,1]==1,3]<-0 #2,1==0
  data8[data8[,1]==2,3]<-0 #3,1==0
  data8[data8[,1]==4,3]<-0 #5,1==0
  
  #5,2
  data9[data9[,2]==0,3]<-0 #1,1==0
  data9[data9[,1]==0,3]<-0 #2,1==0
  data9[data9[,1]==1,3]<-0 #3,1==0
  data9[data9[,1]==2,3]<-0 #4,1==0
  data9[data9[,1]==3,3]<-0 #5,1==0
  
  
  t0 <- sum(data0[,3])
  t1 <- sum(data1[,3])
  t2 <- sum(data2[,3])
  t3 <- sum(data3[,3])
  t4 <- sum(data4[,3])
  t5 <- sum(data5[,3])
  t6 <- sum(data6[,3])
  t7 <- sum(data7[,3])
  t8 <- sum(data8[,3])
  t9 <- sum(data9[,3])
  
  #-log(likelihood)
  Tfinal<-sum(t0)+sum(t1)+sum(t2)+sum(t3)+sum(t4)+sum(t5)+sum(t6)+sum(t7)+sum(t8)+sum(t9)
  
  return(-Tfinal)
}

lowerlim <- c(-Inf,-Inf,-Inf,-Inf,-Inf,-Inf,-Inf,-Inf,-Inf,-Inf,-Inf,-Inf,-Inf,-Inf,-Inf,-Inf,-Inf,-Inf,-Inf)
upperlim <- c(+Inf,+Inf,+Inf,+Inf,+Inf,+Inf,+Inf,+Inf,+Inf,+Inf,+Inf,+Inf,+Inf,+Inf,+Inf,+Inf,+Inf,+Inf,+Inf)



############################
##PROBABILITY OF RESPONSE###
############################


##INTEGRAND
integrand<-function(Zint,meantreat,meanuntreat,mle)
{
  
  sigmahat=matrix(nrow=4,ncol=4)
  sigmahat[1,1]=(exp(mle[8]))^2
  sigmahat[2,1]=(2*inv.logit(mle[10])-1)*(exp(mle[8]))*exp(mle[9])
  sigmahat[3,1]=(2*inv.logit(mle[11])-1)*(exp(mle[8]))
  sigmahat[4,1]=(2*inv.logit(mle[12])-1)*(exp(mle[9]))
  sigmahat[1,2]=sigmahat[2,1]
  sigmahat[2,2]=(exp(mle[9]))^2
  sigmahat[3,2]=(2*inv.logit(mle[13])-1)*(exp(mle[9]))
  sigmahat[4,2]=(2*inv.logit(mle[14])-1)*(exp(mle[9]))
  sigmahat[1,3]=sigmahat[3,1]
  sigmahat[2,3]=sigmahat[3,2]
  sigmahat[3,3]=1
  sigmahat[4,3]=2*inv.logit(mle[15])-1
  sigmahat[1,4]=sigmahat[4,1]
  sigmahat[2,4]=sigmahat[4,2]
  sigmahat[3,4]=sigmahat[4,3]
  sigmahat[4,4]=1
  
  xtreat<-cbind(-meantreat[,1]+Zint[1], -meantreat[,2]+Zint[2], -meantreat[,3]+Zint[3], -meantreat[,4]+Zint[4])
  xuntreat<-cbind(-meanuntreat[,1]+Zint[1],-meanuntreat[,2]+Zint[2],-meanuntreat[,3]+Zint[3],-meanuntreat[,4]+Zint[4])
  
  pdftreat=dmvnorm(xtreat, mean=c(0,0,0,0),sigma=sigmahat)
  pdfuntreat=dmvnorm(xuntreat, mean=c(0,0,0,0),sigma=sigmahat)
  
  return(c(mean(pdftreat),mean(pdfuntreat)))
}


####PROBABILITY OF SUCCESS

probofsuccess<-function(mle,n,dat,eta)
{
  n=n
  
  meantreat=cbind(cbind(rep(1,n),rep(1,n),dat[,7])%*%c(mle[1:2],mle[20]),cbind(rep(1,n),rep(1,n),dat[,8])%*%c(mle[3:4],mle[21]),rep(1,n)*mle[5],
                  cbind(rep(1,n),rep(1,n))%*%mle[6:7])   
  meanuntreat=cbind(cbind(rep(1,n),rep(0,n),dat[,7])%*%c(mle[1:2],mle[20]),cbind(rep(1,n),rep(0,n),dat[,8])%*%c(mle[3:4],mle[21]),rep(0,n)*mle[5],
                    cbind(rep(1,n),rep(0,n))%*%mle[6:7])     
  
  #lower and upper bounds
  minmean1=min(c(meantreat[,1],meanuntreat[,1]))
  minmean2=min(c(meantreat[,2],meanuntreat[,2]))
  minmean3=min(c(meantreat[,3],meanuntreat[,3]))
  minmean4=min(c(meantreat[,4],meanuntreat[,4]))
  
  maxmean1=max(c(meantreat[,1],meanuntreat[,1]))
  maxmean2=max(c(meantreat[,2],meanuntreat[,2]))
  maxmean3=max(c(meantreat[,3],meanuntreat[,3]))
  maxmean4=max(c(meantreat[,4],meanuntreat[,4]))
  
  lower=c(qnorm(1e-15,minmean1,exp(mle[8])),qnorm(1e-15,minmean2,exp(mle[9])),qnorm(1e-15,minmean3,1),qnorm(1e-15,minmean4,1))
    upper=c(eta[1],eta[2],eta[3],eta[4])
  
  a=cuhre(4,2,integrand=integrand,meantreat=meantreat,meanuntreat=meanuntreat,
          mle=mle,lower=lower,upper=upper,flags=list(verbose=0,final=1,pseudo.random=0,mersenne.seed=NULL))
 
  #return(c(a$value[1]-a$value[2],a$value[1],a$value[2])) ##RISK DIFFERENCE
  return(c((log(a$value[1]/(1-a$value[1]))-log(a$value[2]/(1-a$value[2]))),a$value[1],a$value[2])) ##LOG-ODDS
  #return(log(a$value[1]/a$value[2])) ##LOG RISK RATIO
}


#### PARTIAL DERIVATIVES

partials<-function(mle,n,dat,eta)
{
  p=length(mle)
  fit1<-probofsuccess(mle,n,dat,eta)
  fit<-fit1[1]
  partials.augbin<-as.vector(rep(0,p))
  
  for(i in 1:p){
    valueupdate=mle
    valueupdate[i]=valueupdate[i]+0.000001
    updateprob=probofsuccess(valueupdate,n,dat,eta)[1]
    partials.augbin[i]=(updateprob-fit)/0.000001
  }
  
  return(c(partials.augbin,fit1))
}



### AUGMENTED BINARY METHOD

##BOX-COX TRANSFORM FOR CONTINUOUS COMPONENT

boxcoxtransform=function(y,lambda)
{
  return((y^lambda-1)/lambda)
}


###INTEGRAND

integrand.aug<-function(acrn,meantreated,meanuntreated,Sigma,failure1,baseline1,baseline2)
{
  n=length(baseline1)
  
  f1treat=inv.logit(cbind(rep(1,n),baseline1,baseline2,rep(1,n))%*%failure1$coefficient)
  f1untreat=inv.logit(cbind(rep(1,n),baseline1,baseline2,rep(0,n))%*%failure1$coefficient)
  
  pdftreat=dnorm(-meantreated[,1]+acrn[1], mean=0,sd=Sigma)
  pdfuntreat=dnorm(-meanuntreated[,1]+acrn[1], mean=0,sd=Sigma)
  
  return(c(mean((1-f1treat)*pdftreat),mean((1-f1untreat)*pdfuntreat)))
  
}

##PROBABILITY OF SUCCESS

probofsuccess.aug=function(continuous,baseline1,baseline2,failure1,dich)
{
  
  n=length(baseline1)
  
  meantreated=cbind(rep(1,n),rep(1,n),baseline1,baseline2)%*%continuous$coefficient
  
  meanuntreated=cbind(rep(1,n),rep(0,n),baseline1,baseline2)%*%continuous$coefficient
  
  
  #find lower and upper points for integration:
  maxmean1=max(c(meantreated[,1],meanuntreated[,1]))
  minmean1=min(c(meantreated[,1],meanuntreated[,1]))
  
  
  #integrate
  
  a=cuhre(1,2,integrand=integrand.aug,meantreated=meantreated,meanuntreated=meanuntreated,Sigma=summary(continuous)$sigma,failure1=failure1,baseline1=baseline1,baseline2=baseline2,
          lower=qnorm(1e-08,minmean1,summary(continuous)$sigma),upper=dich,flags=list(verbose=0,final=1,pseudo.random=0,mersenne.seed=NULL))
  
  #return(c(a$value[1]-a$value[2],a$value[1],a$value[2])) ### RISK DIFFERENCE
  return(c((log(a$value[1]/(1-a$value[1]))-log(a$value[2]/(1-a$value[2]))),a$value[1],a$value[2])) ## LOG-ODDS
  
}


###PARTIAL DERIVATIVES

get.partials<-function(continuous,baseline1,baseline2,failure1,dich)
{
  
  fit=probofsuccess.aug(continuous,baseline1,baseline2,failure1,dich)
  fit1=fit[1]
  augbin.partials=as.vector(rep(0,8))
  
  
  #split in to three separate models
  
  #continuous model
  
  for(i in 1:4)
  {
    
    valueupdate1=continuous
    valueupdate1$coefficient[i]=valueupdate1$coefficient[i]+0.000001
    
    updateprob=probofsuccess.aug(valueupdate1,baseline1,baseline2,failure1,dich)[1]
    
    augbin.partials[i]=(updateprob-fit1)/0.000001
    
  }
  
  #failure model1
  
  for(i in 1:4)
  {
    
    valueupdate2=failure1
    valueupdate2$coefficient[i]=valueupdate2$coefficient[i]+0.000001
    
    updateprob=probofsuccess.aug(continuous,baseline1,baseline2,valueupdate2,dich)[1]
    
    augbin.partials[i+4]=(updateprob-fit1)/0.000001
  }
  
  return(c(augbin.partials,fit))
}


#### STANDARD BINARY METHOD

differenceinprob.binary=function(glm1,t,x1,x2)
{
  #get fitted probs for each arm from model:
  
  fittedvalues.control=as.double(inv.logit(cbind(rep(1,length(t[t==0])),rep(0,length(t[t==0])),x1[t==0],x2[t==0])%*%glm1$coef))
  
  fittedvalues.exp=as.double(inv.logit(cbind(rep(1,length(t[t==1])),rep(1,length(t[t==1])),x1[t==1],x2[t==1])%*%glm1$coef))
  
  
  return(c(log(mean(fittedvalues.exp,na.rm=T)/(1-mean(fittedvalues.exp,na.rm=T)))-log(mean(fittedvalues.control,na.rm=T)/(1-mean(fittedvalues.control,na.rm=T))),mean(fittedvalues.exp,na.rm=T),mean(fittedvalues.control,na.rm=T))) ###LOG-ODDS

  #return(c(mean(fittedvalues.exp,na.rm=T)-mean(fittedvalues.control,na.rm=T), mean(fittedvalues.exp,na.rm=T), mean(fittedvalues.control,na.rm=T))) ### RISK DIFFERENCE
  #return(log(mean(fittedvalues.exp,na.rm=T)/mean(fittedvalues.control,na.rm=T))) ### LOG RISK RATIO
}


## PARTIAL DERIVATIVES

partialderivatives.binary=function(glm1,t,x1,x2)
{
  
  value1=differenceinprob.binary(glm1,t,x1,x2)
  value=value1[1]
  
  partials=rep(0,4)
  
  tempglm1=glm1
  tempglm1$coef[1]=tempglm1$coef[1]+0.00001
  
  partials[1]=(differenceinprob.binary(tempglm1,t,x1,x2)[1]-value)/0.00001
  
  tempglm1=glm1
  tempglm1$coef[2]=tempglm1$coef[2]+0.00001
  
  partials[2]=(differenceinprob.binary(tempglm1,t,x1,x2)[1]-value)/0.00001
  
  tempglm1=glm1
  tempglm1$coef[3]=tempglm1$coef[3]+0.00001
  
  partials[3]=(differenceinprob.binary(tempglm1,t,x1,x2)[1]-value)/0.00001
  
  tempglm1=glm1
  tempglm1$coef[4]=tempglm1$coef[4]+0.00001
  
  partials[4]=(differenceinprob.binary(tempglm1,t,x1,x2)[1]-value)/0.00001
  
  return(c(value,partials,value1[2],value1[3]))
  
  
}



##### CALCULATE PROBABILITY OF SUCCESS USING LATENT VARIABLE METHOD

  n=dim(dat)[1]
  
  eta=c() ##SET DICHOTOMISATION THRESHOLDS BASED ON DATA
  mlefit=optimx(X,f,lower=lowerlim,upper=upperlim,method="nlminb",dat=dat,eta=eta,control=list(rel.tol=1e-12))
  mle<-coef(mlefit[1,])
  hess<-attr(mlefit,"details")["nlminb",]$nhatend
  mlecov=ginv(hess)
  mlecov<-nearPD(mlecov)$mat
  se<-sqrt(diag(mlecov))
  part<-partials(mle,n,dat,eta)
  mean<-part[22]
  parts<-part[1:21]
  variance=t(parts)%*%mlecov%*%parts
  variance=variance[1,1]
  
  CI<-c(mean-1.96*sqrt(variance),mean,mean+1.96*sqrt(variance),part[23],part[24])

  
  
  ##AUGMENTED BINARY
  dichotomisationthreshold=eta[1] ###SET BASED ON DATA
  cont<-dat$Z1
  dat$myresp<-ifelse(dat$Z2<=(eta[2]) & dat$Z3ord!=3 & dat$Z3ord!=4 & dat$Z4ord==0,0,1) ### SET BINARY RESPONSE  CRITERIA BASED ON DATA
  failure<-dat$myresp
  baselinediseaseactivity<-dat$Z10
  baseline2<-dat$Z20
  arm<-dat$treat
  patientid<-dat$id
  
  #fit continuous model
  continuousmodel=gls(Z1~treat+Z10+Z20,data=dat)
  
  #first model - all patients:
  failuremodel1=glm(myresp~Z10+Z20+treat,family="binomial",data=dat)
  
  partial.aug=get.partials(continuousmodel,baselinediseaseactivity,baseline2,failuremodel1,dichotomisationthreshold)  
  
  mean.aug=partial.aug[9]
  partials.aug=partial.aug[1:8]
  
  covariance.aug=matrix(0,8,8)
  covariance.aug[1:4,1:4]=continuousmodel$varBeta
  covariance.aug[5:8,5:8]=summary(failuremodel1)$cov.unscaled
  variance.aug=t(partials.aug)%*%covariance.aug%*%partials.aug
  
  #confidence interval for difference in mean probability of success
  CI.augbin=c(mean.aug-1.96*sqrt(variance.aug),mean.aug,mean.aug+1.96*sqrt(variance.aug),partial.aug[10],partial.aug[11])
  
  
  ###STANDARD BINARY
  
  dat$resp<-ifelse(dat$Z1<=(eta[1]) & dat$Z2<=(eta[2]) & dat$Z3ord!=3 & dat$Z3ord!=4 & dat$Z4ord==0, 1,0) ##SET BASED ON DATA
  success.binary=dat$resp
  
  glm1=glm(success.binary~treat+Z10+Z20,family="binomial")
  
  partial.binary=partialderivatives.binary(glm1,treat,Z10,Z20)
  mean.binary=partial.binary[1]
  partials.binary=partial.binary[2:5]
  covariance=summary(glm1)$cov.unscaled
  var.binary=t(partials.binary)%*%covariance%*%partials.binary
  
  CI.binary=c(mean.binary-1.96*sqrt(var.binary),mean.binary,mean.binary+1.96*sqrt(var.binary),partial.binary[6],partial.binary[7])



