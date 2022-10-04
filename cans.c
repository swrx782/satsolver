#include <stdio.h>
#include <stdlib.h>

void newfgets(char*, FILE*);
int rformula(int*, int*, int*);

void cans(int, int*, int*);

const int nformula =10000;
const int ntorf =101;

int main() {
  int formula[nformula], numofvar, numofclause,
    torf[]={0,11,11,-16,7,11,-15,-8,11,-7,0,11,11,0,6,0,-5,11,6,11,12,-11,-6,11,11,6,-11,-8,15,-14,0,12,6,12,4,-11,-13,11,-10,7,-3,0,11,11,-11,-2,-7,-7,9,7,11}, i;
  
  for (i=0;i<nformula;i++) formula[i] = 0;
  
  rformula(formula, &numofvar, &numofclause);
  cans(numofclause, formula, torf);
}

void newfgets(char *str, FILE *fp) {
  for (;fgets(str, 256, fp)!= NULL;) {
    if (str[0]!='c') {break;}
  }
}

int rformula(int *formula, int *numofvar, int *numofclause) {
  char str[256], *str2, var[256];
  int  i, k, l, last=0;
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
  
  return 1;
}

void cans(int numofclause, int *formula, int *torf) {
  int i, count, j=0;
  for (i=0;i<numofclause;i++) {
    /*printf("i=%d\n", i);*/
    count = 0;
    /*新しい仮定なしで節が真になるかの確認（真偽値が定まっていないものの確認）*/
    for (;formula[j]!=0;j++) {
      /*printf("formula[%d]=%d, torf[%d]=%d\n", j,
	     formula[j], formula[j], torf[abs(formula[j])]);*/
      /*t,fを正負で表すなら節の中の変数が真になるかは掛けて正になるかで判断できる？*/
      if ((formula[j] > 0 && torf[formula[j]] > 0) ||
	  (formula[j] < 0 && torf[-formula[j]] < 0)) count++;
    }
    /*printf("count=%d\n", count);*/
    if (!count) {printf("矛盾が発生しました(i=%d)\n", i); break;}
    j++;
  }
  printf("解は論理式を満たしています\n");
}
