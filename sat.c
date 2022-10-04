#include <stdio.h>
#include <stdlib.h>

const int nformula = 1000000;
const int ntorf = 200;
const int ntrail = 100;
const int debug = 0;/*on=1, off=0*/
const int checkans = 1;
const int checkformula =0;

typedef struct typeTorfBeta {
  int torf;
  int trail[ntrail];
  int up[ntorf];/*unit propagationで真偽が決まった変数*/
} typeTorf;

void newfgets(char*, FILE*);
int rformula(int*, int*, int*, int*);

void blank(int);
void makeImplicationGraph(typeTorf*, int*, int, int);
void mekeLearndClause(typeTorf*, int, int*, int);
int checkUip(typeTorf*, int, int);
int searchFuip(typeTorf*, int, int);
int fanswer(int*, typeTorf*, int*, int, int*, int*, int, int*, int*, int*);
int fanswer0(int*, typeTorf*, int*, int, int*, int*, int, int*, int*, int*);

void printans(int, int, typeTorf*);

int main() {
  char str[256], var[256];
  int  formula[nformula], ntf[ntorf], ntff[ntorf],
       cclause[ntrail],/*矛盾が起きた節*/
       numofvar, numofclause, count, i, j, l, m,
       learndClause[ntorf], lastNumOfFormula;
  typeTorf allTorf[ntorf]; /*真>0,偽<0*/
  
  /*初期化*/
  for (i=0;i<ntorf;i++) {
    allTorf[i].torf = 0;
    for (j=0;j<ntrail;j++) allTorf[i].trail[j] = 0;
    for (j=0;j<ntorf;j++) allTorf[i].up[j] = -1;
  }
  for (i=0;i<nformula;i++) formula[i] = 0;
  for (i=0;i<ntrail;i++) {cclause[i] = 0; learndClause[i] = 0;}
  for (i=0;i<ntorf;i++) {ntf[i]=0;ntff[i]=0;}
  /*論理式の読み込み*/
  rformula(formula, &numofvar, &numofclause, &lastNumOfFormula);  
  /*解を探す*/ 
  if (fanswer0(formula, allTorf, &numofclause, 1, ntf,
	      ntff, 0, cclause, learndClause, &lastNumOfFormula
	      ) == -1) {
    for (i=1;i<numofvar+1;i++) {
      if (allTorf[i].torf == 0) printf("x_%d=true or false\n", i);
      else printf("x_%d=%s\n", i, (allTorf[i].torf>0 ? "true" : "false"));
    }
    printans(checkans, numofvar, allTorf);
  } else printf("answer is not found\n");
  
  return 0;
}





/*コメントが来たら読み飛ばすfgets関数の作成*/
void newfgets(char *str, FILE *fp) {
  for (;fgets(str, 256, fp)!= NULL;) if (str[0]!='c') break;
}

int rformula(int *formula, int *numofvar,
	     int *numofclause, int *lastNumOfFormula) {
  char str[256], *str2, var[256];
  int  i, k, l, last=0;/*last=formulaにおいて追加する際にどこに入れるか*/
  FILE *fp;
  
  /*ファイルのオープン*/
  printf("ファイル名を入力してください>>");
  fgets(str, 256, stdin);
  for (i=0;str[i]!='\n';i++);
  str[i] = '\0';
  fp = fopen(str, "r");
 
  /*ファイルからpスタートの文字の行まで移動<-newfgetsのおかげで1回で読み込める*/
  newfgets(str, fp);
  /*変数数と節数の検索*/
  str2 = str + 6;
  
  for (i=0;str2[i]!=' ';i++) str[i] = str2[i];
  str[i++] = '\0';
  *numofvar = atoi(str);
  printf("変数の数=%d\n", *numofvar);
  
  str2 += i;   
  for (i=0;str2[i]!='\n';i++) str[i] = str2[i];
  str[i] = '\0';
  *numofclause = atoi(str);
  printf("節の数=%d\n", *numofclause);

  /*各節の読み込み*/
  for (i = 1;i<=*numofclause;i++) {
    newfgets(str, fp);
    /*printf("str=%s\n", str);*/
    for (k=0;str[k]!='\0';k++) {
      for (l=0;str[k]!=' '&&str[k]!='\n';) var[l++] = str[k++];    
      var[l] = '\0';
      formula[last++] = atoi(var);
    }
  }
  *lastNumOfFormula = last;
  if (checkformula) {
    printf("{");
    for (i=0;i<last+1;i++) printf("%d,", formula[i]);
    printf("%d}\n", formula[last+1]);
  }
  return 1;
}

void blank(int n) {
  int i;
  for (i=0;i<n;i++) printf(" ");
}





void makeImplicationGraph(typeTorf *allTorf, int *clause, int level, int var) {
  int i, j, l, m;
  
  if (clause[0]!=0) {
    /*trail(clause)の各変数がどの変数によってupを行ったのかを調べる*/
    for (i=0;clause[i]!=0;i++) {
      if (abs(clause[i])!=var) {
	for (j=0;allTorf[abs(clause[i])].up[j]!=-1&&
	       allTorf[abs(clause[i])].up[j]!=var;j++);
	if (allTorf[abs(clause[i])].up[j]!=var) {
	  allTorf[abs(clause[i])].up[j++] = var;
	  allTorf[abs(clause[i])].up[j] = -1;
	}
      }
    }
    /*trailの各変数がどの変数からupを行ったのか調べる*/
    for (i=0;clause[i]!=0;i++) {
      /*変数のレベルが現在のレベル以下なら行わない*/
      /*var以外の変数に対して行う*/
      if (abs(allTorf[abs(clause[i])].torf)==level&&abs(clause[i])!=var) {
	makeImplicationGraph(allTorf, allTorf[abs(clause[i])].trail,
			     level, abs(clause[i]));
      }
    }
  }
}

void makeLearnedClause(typeTorf *allTorf, int var,
		       int *learndClause, int level) {
  int i, j, l, m;
 
  /*upするときに使った低レベルの変数は学習節に加える*/
  for (i=0;allTorf[var].trail[i]!=0;i++)
    if (abs(allTorf[abs(allTorf[var].trail[i])].torf)!=level) {
      /*既に含まれていたら加えない*/
      for (j=0;
	   learndClause[j]!=0&&
	     learndClause[j]!=allTorf[var].trail[i];
	   j++);
      if (learndClause[j]==0) {
	learndClause[j++] = allTorf[var].trail[i];
	learndClause[j]=0;
      }
    }
  /*varによってupを行った結果得られた変数に対して追加を行う*/
  for (i=0;allTorf[var].up[i]!=-1;i++)
    makeLearnedClause(allTorf, allTorf[var].up[i], learndClause, level);
}

int checkUip(typeTorf *allTorf, int uip, int var) { /*uip=チェックしたい変数、var=現在の変数*/
  int i, x;/*x=cheakUipの返り値*/
  /*varからボトムに行けるならuipではない*/
  for (i=0;allTorf[var].up[i]!=-1&&allTorf[var].up[i]!=0;i++);
  if (allTorf[var].up[i]==0) return 0;
  else {
    /*ボトムがないならvar以降のルートでボトムに行けるか確認する*/
    for (i=0;allTorf[var].up[i]!=-1;i++) {
      if (allTorf[var].up[i]!=uip) {
	/*1つでもボトムに行けるルートがあったらuipではない*/
	if (!checkUip(allTorf, uip, allTorf[var].up[i])) return 0;
      }
    }
    /*ボトムに行けるルートがないなら現段階ではuipの可能性がある*/
    return uip;
  }
}

int searchFuip(typeTorf *allTorf, int var, int startVar) {
  int i, fuip;
  if (var==0) return 0;
  else {
    fuip = searchFuip(allTorf, allTorf[var].up[0], startVar);
    if (fuip) return fuip;
    else if (var == startVar) return startVar;
    else return checkUip(allTorf, var, startVar);
  }
}

/*返り値0->upで矛盾が起きた
       n->レベルnに戻って欲しい
       （その関数で学習節を作った、実際に戻るのはn-1）
       -1->成功*/
int fanswer(int *formula, typeTorf allTorf[ntorf], int *numofclause,
	    int n, int *ntf, int *ntff, int nownum, int *cclause,
	    int *learndClause, int *lastNumOfFormula) {
  int i, k, fans, count,/*no true false formula*/
      j=0,/*今見ている論理式の場所*/
      startClause,/*節の最初*/
      l,m,p,/*小さいfor文で使う*/
      sOfNtorfc,
      /*論理式の中で節が真にも偽にもなっていない節の最初
        (start of true or false clause)*/
      countc=0,/*真にも偽にもなっていない節があったかどうか*/
      startNtf=nownum,
      /*真にも偽にもなっていない節があった場合の見割り当て変数(ntf,ntff)の最初*/
      upc=1,/*まだ単位伝搬ができるかどうか*/
      fuip,
    returnLevel,/*戻りたいレベル*/
    returnValue;/*返り値*/
  if (debug) {
    printf("lebel=%d, lastNumOfFormula=%d, numofclause=%d\n",
	   n, *lastNumOfFormula, *numofclause);
    printf("formula={");
    for (i=0;i<100;i++) printf("%d,", formula[i]); printf("}\n");
    printf("torf={");
    for (i=0;i<51;i++) printf("%d,", allTorf[i].torf); printf("}\n");   
  }
  for (;upc;) {
    upc = 0;
    countc = 0;
    j = 0;
    nownum = startNtf;
    for (i=0;i<*numofclause;i++) {
      /*新しい仮定なしで節が真になるかの確認（真偽値が定まっていないものの確認）*/
      count = 0;
      startClause = j;
      if (!countc) {sOfNtorfc = j; startNtf = nownum;}
      /*真偽不明の節がなかったら更新*/
      for (;formula[j]!=0;j++) {
	/*true,falseを正負で表すなら節の中の変数が
          真になるかは掛け算が正になるかで判断できる？*/
	if ((formula[j] > 0 && allTorf[formula[j]].torf > 0) ||
	    (formula[j] < 0 && allTorf[-formula[j]].torf < 0)) {
	  if (debug) {
	    blank(n);
	    printf("節は真です\n");
	  }
	  nownum = nownum - count;
	  break;
	}
	if (allTorf[abs(formula[j])].torf==0) {
	  ntf[nownum] = abs(formula[j]); /*変数の番号*/
	  ntff[nownum++] = j; /*論理式における変数の位置*/
	  count++;
	}
      }
      /*節が真にならなかった場合（節の最後（０）まで確認した場合）*/
      if (j!=0&&formula[j-1]!=0&&formula[j]==0) {
	/*真偽値が定まっていないものが０（矛盾）*/
	if (count == 0) {
	  for (m=0;formula[startClause]!=0;)
	    cclause[m++] = formula[startClause++];
	  cclause[m] = 0;
	  if (debug) {
	    blank(n);
	    printf("矛盾が発生しました\n");
	  }
	  return 0;
	  /*                        １（真偽値が決まる）*/
	} else if(count == 1) {
	  /*trailへの代入*/
	  for (m=0;formula[startClause]!=0;)
	    allTorf[ntf[nownum-1]].trail[m++] = formula[startClause++];
	  allTorf[ntf[nownum-1]].trail[m] = 0;
	  /*unit propagation*/
	  if (formula[ntff[nownum-1]] > 0) allTorf[ntf[nownum-1]].torf = n;
	  else allTorf[ntf[nownum-1]].torf = -n;
	  if (debug) {
	    blank(n);
	    printf("unit propagationによりx_%dに%sを割り当てます\n",
		   ntf[nownum-1], (allTorf[ntf[nownum-1]].torf>0 ?
				   "true" : "false"));
	    blank(n);
	    printf("節は(");
	    for(l=0;allTorf[ntf[nownum-1]].trail[l]!=0;l++)
	      printf("%d,", allTorf[ntf[nownum-1]].trail[l]);
	    printf(")\n");
	  }
	  nownum--;
	  upc = 1;
	  /*　　　　　　　　　　　　　　２以上で初めてなら残しておく*/
	} else if (!countc) {
	  countc = count;
	} else nownum = nownum - count;
      } else for (;formula[j]!=0;j++);/*節の最後まで確認していない場合最後まで進む*/
      j++;
    }
  }
  /*論理式が真にならなかったらどれか1つを決定する*/
  if (!countc) return -1;
  else {
    /*０番目が真になるように割り当て矛盾したら１番目、２、３、、、
          という風に割り当てていき全て矛盾したら終了（今は2回目以降はやらない）*/
    for(k=0;k<countc;k++) {
      allTorf[ntf[startNtf+k]].trail[0] = 0;
      if (formula[ntff[startNtf+k]] > 0)
	allTorf[ntf[startNtf+k]].torf = n+1;
      else allTorf[ntf[startNtf+k]].torf = -(n+1);
      if (debug) {
	blank(n);
	printf("x_%dに%sを割り当てます（仮定）\n",
	       ntf[startNtf+k],
	       (allTorf[ntf[startNtf+k]].torf>0 ? "true" : "false"));
      }
      /*n+1レベルの実行（戻ってきたら必ず決定以外は削除）*/
      for (returnValue=fanswer(formula, allTorf, numofclause,
			       n+1, ntf, ntff, nownum, cclause,
			       learndClause, lastNumOfFormula);
	   returnValue==n+1;
	   returnValue=fanswer(formula, allTorf, numofclause,
			       n+1, ntf, ntff, nownum, cclause,
			       learndClause, lastNumOfFormula)) {
	for (l=0;l<ntorf;l++) {
	  if (abs(allTorf[l].torf)==n+1) {
	    allTorf[l].torf=0;
	    allTorf[l].trail[0] = 0;
	  }
	}
	if (formula[ntff[startNtf+k]] > 0)
	allTorf[ntf[startNtf+k]].torf = n+1;
	else allTorf[ntf[startNtf+k]].torf = -(n+1);
      }
      /*⬇returnValueの場合分け⬇*/
      if (returnValue==-1) return -1;
      else if (returnValue<n+1&&returnValue>0) {
	for (l=0;l<ntorf;l++) {
	  if (abs(allTorf[l].torf)==n+1) {
	    allTorf[l].torf=0;
	    allTorf[l].trail[0] = 0;
	  }
	}
	return returnValue;
      } else if (returnValue>n+1||returnValue<-1)	{
	if (debug) {blank(n);printf("error:returnValue=%d", returnValue);}
	return -1;}
      else if (returnValue == 0) {
	if (debug) {
	  blank(n);
	  printf("x_%dへの%sの割り当て（仮定）で矛盾が起きたました\n",
		 ntf[startNtf+k],
		 (allTorf[ntf[startNtf+k]].torf>0 ? "true" : "false"));
	}
	/*Implication graphの作成*/
	for (l=0;l<ntorf;l++) allTorf[l].up[0] = -1;
	if (debug) {
	  blank(n);
	  printf("cclause={");
	    for (l=0;cclause[l]!=0;l++) printf("%d,", cclause[l]);
	  printf("}\n");
	  blank(n);
	  printf("allTorf.trail=\n{");
	  for (l=0;l<=50;l++) {
	    printf("%d=%d(", l, allTorf[l].torf);
	    for (m=0;allTorf[l].trail[m]!=0;m++)
	      printf("%d,", allTorf[l].trail[m]);
	    printf(")\n ");
	  }
	  printf("}\n");
	}
	makeImplicationGraph(allTorf, cclause, n+1, 0);
	if (debug) {
	  blank(n);
	  printf("allTorf.up=\n{");
	  for (l=0;l<=50;l++) {
	    printf("%d=%d(", l, allTorf[l].torf);
	    for (m=0;allTorf[l].up[m]!=-1;m++)
	      printf("%d,", allTorf[l].up[m]);
	    printf(")\n ");
	  }
	  printf("}\n");
	}
	/*uipの探索*/
	fuip=searchFuip(allTorf, ntf[startNtf+k], ntf[startNtf+k]);
	if (fuip==0) {blank(n);printf("error:fuip=0\n"); return -1;}
	if (debug)printf("first UIP =%d\n",fuip);	
	/*仮学習節の作成*/
	/*ボトムのtrailを作っていないのでtrailでの低レベル変数は先に加える*/
	p=0;
	for (m=0;cclause[m]!=0;m++) {
	  if (abs(allTorf[abs(cclause[m])].torf)!=n+1)
	    learndClause[p++]=cclause[m];
	}
	learndClause[p]=0;
	/*残りの仮学習節の作成*/
	for (m=0;allTorf[fuip].up[m]!=-1;m++)
	makeLearnedClause(allTorf, allTorf[fuip].up[m], learndClause, n+1);
	if (debug) {
	  for (l=0;learndClause[l]!=0;l++) printf("%d, ",learndClause[l]);
	  printf("\n");
	}
	/*どのレベルに戻ればいいかの探索*/
	l=1;
	for (m=0;learndClause[m]!=0;m++)
	  if (abs(allTorf[abs(learndClause[m])].torf)>l)
	      l=abs(allTorf[abs(learndClause[m])].torf);
	if (debug) printf("l=%d\n", l);
	returnLevel = l;
	learndClause[0]=0;

	/*戻るレベル以下の仮定の否定を加える*/
	for (m=2;m<=l;m++) {
	  for (p=0;abs(allTorf[p].torf)!=m||allTorf[p].trail[0]!=0;p++);
	  if (allTorf[p].torf < 0) learndClause[m-2] = p;
	  else learndClause[m-2] = -p;
	}
	/*fuipの否定を加える*/
	if (allTorf[fuip].torf < 0) learndClause[l-1] = fuip;
	else learndClause[l-1] = -fuip;
	learndClause[l] = 0;
	if (debug) {
	  for (m=0;learndClause[m]!=0;m++)printf("%d,", learndClause[m]);
	  printf("←最終的なlearndClause\n");
	}
	/*学習節の論理式への追加*/
	*numofclause = *numofclause + 1;
	for (m=0;m<l+1;m++) {
	  formula[*lastNumOfFormula]=learndClause[m];
	  *lastNumOfFormula = *lastNumOfFormula + 1;
	}	
	/*この後（深さn+1以上）で割り当てたものの削除*/
	for (l=0;l<ntorf;l++) {
	  if (abs(allTorf[l].torf)==n+1) {
	    allTorf[l].torf=0;
	    allTorf[l].trail[0] = 0;
	  }
	}
       	learndClause[0] = 0;
	return returnLevel;
      }
      /*⬆returnLevelの場合分け⬆*/
    }
    if (debug) {
      blank(n);
      printf("全ての変数割り当てで矛盾が起きました\n");
    }
    return returnLevel;   
  }
  return -1;
}

/*fansのスタート（無決定でupをしてもらうため）*/
int fanswer0(int *formula, typeTorf allTorf[ntorf], int *numofclause,
	    int n, int *ntf, int *ntff, int nownum, int *cclause,
	    int *learndClause, int *lastNumOfFormula) {
  int l, m, returnValue;
  for (returnValue=fanswer(formula, allTorf, numofclause, 1,
			   ntf, ntff, 0, cclause, learndClause,
			   lastNumOfFormula
			   );
       returnValue!=0&&returnValue!=-1;
       returnValue=fanswer(formula, allTorf, numofclause, 1,
			   ntf, ntff, 0, cclause, learndClause,
			   lastNumOfFormula));
  for (l=0;l<ntorf;l++) allTorf[l].up[0] = -1;
	if (debug) {
	  blank(n);
	  printf("cclause={");
	    for (l=0;cclause[l]!=0;l++) printf("%d,", cclause[l]);
	  printf("}\n");
	  blank(n);
	  printf("allTorf.trail=\n{");
	  for (l=0;l<=50;l++) {
	    printf("%d=%d(", l, allTorf[l].torf);
	    for (m=0;allTorf[l].trail[m]!=0;m++)
	      printf("%d,", allTorf[l].trail[m]);
	    printf(")\n ");
	  }
	  printf("}\n");
	}
	if (debug) {
	  blank(n);
	  printf("allTorf.up=\n{");
	  for (l=0;l<=50;l++) {
	    printf("%d=%d(", l, allTorf[l].torf);
	    for (m=0;allTorf[l].up[m]!=-1;m++)
	      printf("%d,", allTorf[l].up[m]);
	    printf(")\n ");
	  }
	  printf("}\n");
	}
  return returnValue;
}

void printans(int a, int numofvar, typeTorf *allTorf) {
  int i, j;
  if (a) {
    printf("{");
    for (i=0;i<=numofvar;i++) {
      printf("%d(", allTorf[i].torf);
      for (j=0;allTorf[i].trail[j]!=0;j++)
	printf("%d,", allTorf[i].trail[j]);
      printf(")\n ");
    }
    printf("}\n");

    printf("{");
    for (i=0;i<numofvar;i++) {
      printf("%d,", allTorf[i].torf);
    }
    printf("%d}\n", allTorf[i].torf);
  }
}

/*
printf("--- ---\n");
*/

/*
printf("{");
for (l=0;l<=20;l++) {
  printf("%d(", allTorf[l].torf);
  for (m=0;allTorf[l].trail[m]!=0;m++)
    printf("%d,", allTorf[l].trail[m]);
  printf(")\n ");
 }
printf("}\n");
printf("{");
for (l=0;l<=20;l++) {
  printf("%d(", allTorf[l].torf);
  for (m=0;allTorf[l].up[m]!=-1;m++)
    printf("%d,", allTorf[l].up[m]);
  printf(")\n ");
 }
printf("}\n");
*/
