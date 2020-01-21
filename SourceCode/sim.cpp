#include <iostream>
#include <stdio.h>
#include <string>
#include <sstream>
#include <stdlib.h>
#include <fstream>
#include <math.h>
#include <iomanip>
#include <cmath>
#include<bits/stdc++.h> 

using namespace std;

string file, predictor, branchaddress, actual_outcome;
stringstream ss;
int position, branch_historyreg, temp_reg, index_bits, history_bits, M2, N, M1, K, BTB_size, BTB_assoc, access, misprediction, btb_hit, btb_miss, i, BTB, hit_flag;
long branch_address, index_bimodal, index_gshare, index_chooser, index_btb, temp_index, tag;
int LRU_counter(), tag_store[5000][5000], blockinvalid, mispredictionduemiss;

struct pred_table{   
int counter;
string prediction;
}bimodal[50000],gshare[50000],chooser[50000];

class Tagstore{                                       
public:
long tag;
int counter;  
char validbit = 'I';
};
Tagstore tagstore[5000][5000];                         

void initialize(){
for(int i=0; i<pow(2,M2); ++i)
bimodal[i].counter = 2;
for(int i=0; i<pow(2,M1); ++i)
gshare[i].counter = 2 ;
for(int i=0; i<pow(2,K); ++i)
chooser[i].counter = 1;
if(BTB){
for(int i=0; i<(BTB_size/(4*BTB_assoc)); ++i){          
for(int j=0; j<BTB_assoc; ++j){
tagstore[i][j].counter = j;
tagstore[i][j].validbit = 'I';
}
}
}
}

void getbranchindex(){
access++;       
position        = branchaddress.find(' ');
actual_outcome  = branchaddress.substr(position+1, 1);
branchaddress   = branchaddress.substr(0, position);    
branch_address  = stol(branchaddress, nullptr, 16);
branch_address  = branch_address/4;
if (predictor == "bimodal"){
index_bimodal = fmod(branch_address, pow (2, M2)); 
}
else if (predictor == "gshare"){
temp_index   = fmod(branch_address, pow (2, M1)); 
temp_reg     = branch_historyreg * pow(2, (M1-N));  
index_gshare = temp_index ^ temp_reg;
}
else{
index_bimodal = fmod(branch_address, pow (2, M2));
temp_index    = fmod(branch_address, pow (2, M1)); 
temp_reg      = branch_historyreg * pow (2, (M1-N));  
index_gshare  = temp_index ^ temp_reg;
index_chooser = fmod(branch_address, pow(2,K)); 
}
if(BTB){
index_btb = fmod(branch_address, (BTB_size/(4*BTB_assoc)));
tag   = branch_address/(BTB_size/(4*BTB_assoc));
}
}

int readbtb(){                                            
for(i=0; i<BTB_assoc; ++i){
if ((tag == tagstore[index_btb][i].tag) && (tagstore[index_btb][i].validbit == 'V')){
btb_hit++;
hit_flag++;
LRU_counter();
}
}
if(hit_flag == 0){                                          
btb_miss++; 
for(i=0; i<BTB_assoc; ++i){ 
if(tagstore[index_btb][i].validbit == 'I'){
blockinvalid++; 
LRU_counter();    
tagstore[index_btb][i].tag = tag;
tagstore[index_btb][i].validbit = 'V';
}
}
if(blockinvalid == 0){
int k = LRU_counter();
tagstore[index_btb][k].tag = tag;
tagstore[index_btb][k].validbit = 'V';
}
blockinvalid=0;
}
return hit_flag;
}

int LRU_counter(){                                           
static int currentread_miss = 0;
if(hit_flag){
int j = i;
int temp = tagstore[index_btb][i].counter;
for(i=0; i<BTB_assoc; ++i){
if(tagstore[index_btb][i].counter < temp){
++tagstore[index_btb][i].counter;
}
}
tagstore[index_btb][j].counter = 0;
return 0;
}
else if((btb_miss != currentread_miss)){
int temp = -1;   
for(i=0; i<BTB_assoc; ++i){
if(tagstore[index_btb][i].counter > temp){
temp = tagstore[index_btb][i].counter;
}
}
for(i=0; i<BTB_assoc; ++i){
if(temp != tagstore[index_btb][i].counter){
tagstore[index_btb][i].counter++;
}
else{
tagstore[index_btb][i].counter = 0;
}
}
currentread_miss = btb_miss;
for(i=0; i<BTB_assoc; ++i){
if(tagstore[index_btb][i].counter== 0){
return i;
}   
}
}
return 0;
}

string make_prediction(int count){
string prediction;    
if (count>=2)
prediction = "t";
else if (count<2)
prediction = "n"; 
return prediction;
}

int update_pred_table(int count){    
if(actual_outcome == "t"){
if(count<3)
count++; 
} 
else if (actual_outcome == "n"){
if (count>0)
count--;   
} 
return count;
}

void update_branch_historyreg(){
if(actual_outcome == "t")
branch_historyreg = (branch_historyreg/2)+pow(2,N-1);
else if(actual_outcome == "n")
branch_historyreg = (branch_historyreg/2);
}

int update_choosertable(int count, string prediction1, string prediction2){
if((actual_outcome == prediction1) && (actual_outcome != prediction2)){
if(count>0)
count--;
}
else if((actual_outcome != prediction1) && (actual_outcome == prediction2)){
if(count<3)
count++;    
} 
else if(((actual_outcome != prediction1) && (actual_outcome != prediction2)) || ((actual_outcome == prediction1) && (actual_outcome == prediction2))){
count=count+0;    
}
return count;   
}

void get_misprediction(string prediction){    
if(actual_outcome != prediction)
misprediction++;
}

void branch_predict_process(){
if (predictor == "bimodal"){     
bimodal[index_bimodal].prediction = make_prediction(bimodal[index_bimodal].counter);
bimodal[index_bimodal].counter = update_pred_table(bimodal[index_bimodal].counter);
get_misprediction(bimodal[index_bimodal].prediction);
}
else if (predictor == "gshare"){   
gshare[index_gshare].prediction = make_prediction(gshare[index_gshare].counter);
gshare[index_gshare].counter = update_pred_table(gshare[index_gshare].counter);
update_branch_historyreg();
get_misprediction(gshare[index_gshare].prediction);   
}
else if (predictor == "hybrid"){
bimodal[index_bimodal].prediction = make_prediction(bimodal[index_bimodal].counter);
gshare[index_gshare].prediction = make_prediction(gshare[index_gshare].counter);
if ((chooser[index_chooser].counter == 0)||(chooser[index_chooser].counter == 1)){
bimodal[index_bimodal].counter = update_pred_table(bimodal[index_bimodal].counter);
get_misprediction(bimodal[index_bimodal].prediction);
}
else if ((chooser[index_chooser].counter == 2)||(chooser[index_chooser].counter == 3)){
gshare[index_gshare].counter = update_pred_table(gshare[index_gshare].counter);
get_misprediction(gshare[index_gshare].prediction);  
}
update_branch_historyreg();   
chooser[index_chooser].counter = update_choosertable(chooser[index_chooser].counter, bimodal[index_bimodal].prediction, gshare[index_gshare].prediction);   
}
}

void display(string predictionmodel, int index, pred_table contents[]){
transform(predictionmodel.begin(), predictionmodel.end(), predictionmodel.begin(), ::toupper);
cout <<"FINAL "<<predictionmodel<<" CONTENTS"<<endl; 
for(int i=0; i<pow(2,index); ++i)
cout<<i<<" "<<contents[i].counter<<endl; 
}

void displaybtb(){
cout << "FINAL BTB CONTENTS";
cout <<endl;
if(BTB_assoc !=1){
for(i=0; i<(BTB_size/(4*BTB_assoc)); i++){
cout << "  set   " << dec << i  << ':' <<'\t';
int k = 0;
int m = 0;
for(int j=0; j<BTB_assoc; j++){
for(int l=0; l<BTB_assoc; l++){
if((tagstore[i][l].counter == m) && (tagstore[i][l].tag !=0)){   
tag_store[i][k] = tagstore[i][l].tag;
cout << hex << tag_store[i][k] << " ";
}
}    
k++;
m++;
}
cout << endl;
}
}
if(BTB_assoc == 1){
for(i=0; i<(BTB_size/(4*BTB_assoc)); i++){
cout << "set  " << '\t' << dec << i  << ':' <<'\t';
for(int j=0; j<BTB_assoc; j++){
cout << hex << tagstore[i][j].tag << " ";
cout <<endl;
}    
}
}
cout <<endl;
cout <<dec;
}

void getbranchaddress(string file){
ifstream readfile (file);
if(!readfile) {
cout << "Cannot open file.\n";
}
while (getline(readfile, branchaddress)){
getbranchindex();
if (BTB){
switch(readbtb())
{
    case 0 : if(actual_outcome == "t")
             mispredictionduemiss++;
             break;
    case 1 : branch_predict_process();
             break;         
}
hit_flag=0;
}
else
branch_predict_process();
//break;
}
readfile.close();
}

int main(int argc, char* argv[]) {
char* predictor_type   = argv[1];
ss << predictor_type;
ss >> predictor;
if (predictor == "bimodal"){
M2                 = stoi(argv[2]);
BTB_size           = stoi(argv[3]);
BTB_assoc          = stoi(argv[4]);
char* trace_file       = argv[5];
M1 = 0;
K = 0;
stringstream ss; ss << trace_file; ss >> file;
cout <<"COMMAND"<<endl<<"./sim "<<predictor<<" "<<M2<<" "<<BTB_size<<" "<<BTB_assoc<<" "<<trace_file<<endl;
}
else if (predictor == "gshare"){
M1                 = stoi(argv[2]);
N                  = stoi(argv[3]);
BTB_size           = stoi(argv[4]);
BTB_assoc          = stoi(argv[5]);
char* trace_file       = argv[6];
M2 = 0;
stringstream ss; ss << trace_file; ss >> file;
cout <<"COMMAND"<<endl<<"./sim "<<predictor<<" "<<M1<<" "<<N<<" "<<BTB_size<<" "<<BTB_assoc<<" "<<trace_file<<endl;
}
else{
K                  = stoi(argv[2]);
M1                 = stoi(argv[3]);
N                  = stoi(argv[4]);
M2                 = stoi(argv[5]);
BTB_size           = stoi(argv[6]);
BTB_assoc          = stoi(argv[7]);
char* trace_file       = argv[8]; 
stringstream ss; ss << trace_file; ss >> file;
cout <<"COMMAND"<<endl<<"./sim "<<predictor<<" "<<K<<" "<<M1<<" "<<N<<" "<<M2<<" "<<BTB_size<<" "<<BTB_assoc<<" "<<trace_file<<endl;
}
if (BTB_assoc || BTB_size)
BTB = 1;
initialize();
getbranchaddress(file);
cout <<"OUTPUT"<<endl;
if (!BTB){
cout <<" number of predictions: "<<access<<endl;
cout <<" number of mispredictions: "<<misprediction<<endl;
cout <<" misprediction rate: "<<'\t';
printf ("%0.2f",((float)(misprediction)/access)*100);
cout <<"%"<<endl;
}
else{
cout <<"size of BTB: "<<BTB_size<<endl;
cout <<"number of branches: "<<access<<endl;
cout <<"number of predictions from branch predictor: "<<btb_hit<<endl;
cout <<"number of mispredictions from branch predictor: "<<misprediction<<endl;
cout <<"number of branches miss in BTB and taken: "<<mispredictionduemiss<<endl;
cout <<"total mispredictions: "<<(misprediction + mispredictionduemiss)<<endl;
cout <<"misprediction rate: "<<'\t';
printf ("%0.2f",((float)(misprediction + mispredictionduemiss)/access)*100);
cout <<"%"<<endl;
displaybtb();
}
if(predictor == "bimodal")
display(predictor, M2, bimodal);
else if(predictor == "gshare")
display(predictor, M1, gshare);
else if(predictor == "hybrid"){
display("chooser", K, chooser);
display("gshare", M1, gshare);     
display("bimodal", M2, bimodal);
} 
return 0;
}


