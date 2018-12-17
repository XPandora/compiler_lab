%{
/* Lab2 Attention: You are only allowed to add code in this file and start at Line 26.*/
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "errormsg.h"
#include "absyn.h"
#include "y.tab.h"

int charPos=1;

int yywrap(void)
{
 charPos=1;
 return 1;
}

void adjust(void)
{
 EM_tokPos=charPos;
 charPos+=yyleng;
}

/*
* Please don't modify the lines above.
* You can add C declarations of your own below.
*/

int commentCount = 0;

/* @function: getstr
 * @input: a string literal
 * @output: the string value for the input which has all the escape sequences 
 * translated into their meaning.
 */
char *getstr(const char *str)
{
  int len = strlen(str);
  if(len == 2){
    return "";
  }
  //delete qutation
  char *oldContent = (char *)checked_malloc(len-2);
  char *newContent = (char *)checked_malloc(len-2);
  strncpy(oldContent,str+1,len-2);

  for(int oldpos = 0,newpos = 0;oldpos<len-2;oldpos++,newpos++){
    if(oldContent[oldpos]!= '\\'){
      newContent[newpos] = oldContent[oldpos];
      continue;
    }
    oldpos++;
    switch(oldContent[oldpos]){
      case 'n':
        newContent[newpos] = '\n';
        break;
      case 't':
        newContent[newpos] = '\t';
        break;
      case '\\':
        newContent[newpos] = '\\';
        break;
      case '"':
        newContent[newpos] = '"';
        break;
      case ' ':
      case '\n':
      case '\t':
        while(oldContent[oldpos] == ' '| oldContent[oldpos] == '\n'| oldContent[oldpos] == '\t'){
          oldpos++;
        }
        if(oldContent[oldpos] != '\\'){
          EM_error(charPos,"illegal character");
          return NULL;
        }
        newpos--;
        break;
      case '0':
      case '1':
      case '2':
      case '3':
      case '4':
      case '5':
      case '6':
      case '7':
      case '8':
      case '9':
        {
          int d1 = oldContent[oldpos] - '0';
          int d2 = oldContent[oldpos+1] - '0';
          int d3 = oldContent[oldpos+2] - '0';
          newContent[newpos] = 100 * d1 + 10 * d2 + d3;
          oldpos += 2;
          break;
        }
      case '^':
        oldpos++;
        char c = oldContent[oldpos];
        if(c>='@'&&c<='_'){
          newContent[newpos] = c - 'A' + 1;
        }
        else{
          EM_error(charPos,"illegal character");
        }
        break;
      default:
        EM_error(charPos,"illegal character");
    }
  }
  free(oldContent);
	return newContent;
}

%}
  /* You can add lex definitions here. */ 
digit [0-9]
letter [a-zA-Z]
%Start COMMENT

%%
  /* 
  * Below is an example, which you can wipe out
  * and write reguler expressions and actions of your own.
  */ 

<INITIAL>"while" {adjust();return WHILE;}
<INITIAL>"for" {adjust();return FOR;}
<INITIAL>"to" {adjust();return TO;}
<INITIAL>"break" {adjust();return BREAK;}
<INITIAL>"let" {adjust();return LET;}
<INITIAL>"in" {adjust();return IN;}
<INITIAL>"end" {adjust();return END;}
<INITIAL>"function" {adjust();return FUNCTION;}
<INITIAL>"var" {adjust();return VAR;}
<INITIAL>"type" {adjust();return TYPE;}
<INITIAL>"array" {adjust();return ARRAY;}
<INITIAL>"if" {adjust();return IF;}
<INITIAL>"then" {adjust();return THEN;}
<INITIAL>"else" {adjust();return ELSE;}
<INITIAL>"do" {adjust();return DO;}
<INITIAL>"of" {adjust();return OF;}
<INITIAL>"nil" {adjust();return NIL;}
<INITIAL>"," {adjust();return COMMA;}
<INITIAL>":" {adjust();return COLON;}
<INITIAL>";" {adjust();return SEMICOLON;}
<INITIAL>"(" {adjust();return LPAREN;}
<INITIAL>")" {adjust();return RPAREN;}
<INITIAL>"[" {adjust();return LBRACK;}
<INITIAL>"]" {adjust();return RBRACK;}
<INITIAL>"{" {adjust();return LBRACE;}
<INITIAL>"}" {adjust();return RBRACE;}
<INITIAL>"." {adjust();return DOT;}
<INITIAL>"+" {adjust();return PLUS;}
<INITIAL>"-" {adjust();return MINUS;}
<INITIAL>"*" {adjust();return TIMES;}
<INITIAL>"/" {adjust();return DIVIDE;}
<INITIAL>"=" {adjust();return EQ;}
<INITIAL>"<>" {adjust();return NEQ;}
<INITIAL>"<" {adjust();return LT;}
<INITIAL>"<=" {adjust();return LE;}
<INITIAL>">" {adjust();return GT;}
<INITIAL>">=" {adjust();return GE;}
<INITIAL>"&" {adjust();return AND;}
<INITIAL>"|" {adjust();return OR;}
<INITIAL>":=" {adjust();return ASSIGN;}
<INITIAL>"\n" {adjust(); EM_newline(); continue;}
<INITIAL>" "|"\t" {adjust();continue;}
<INITIAL>{letter}({letter}|{digit}|_)* {adjust();yylval.sval = String(yytext);return ID;}
<INITIAL>{digit}+ {adjust();yylval.ival = atoi(yytext);return INT;}
<INITIAL>\"([^\"]*(\\\")*)*\" {adjust();yylval.sval = getstr(yytext);return STRING;}
<INITIAL>. {adjust();EM_error(charPos,"illegal character");}
<INITIAL>"/*" {adjust();commentCount++;BEGIN COMMENT;}
<COMMENT>"*/" {adjust();commentCount--;if (commentCount == 0) BEGIN INITIAL;}
<COMMENT>"/*" {adjust();commentCount++;}
<COMMENT>. {adjust();}
<COMMENT>"\n" {adjust();EM_newline();continue;}

