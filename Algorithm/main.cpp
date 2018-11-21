/* 
 * File:   main.cpp
 * Author: c3156840
 */

#include <cstdlib>
#include <iostream>
#include <fstream>
#include <ilcplex/ilocplex.h>
#include <sys/time.h>
#include <ctime>
#include <math.h>   
#include <vector>
#include <iomanip> 

using namespace std;

/*------------------------------------------------------------------------------
 
 -----------------------------Public Variables----------------------------------
 
 -----------------------------------------------------------------------------*/
#define Output_Precision 20
#define CPLEX_Relative_Gap 1.0e-6
#define CONVTOL 1.0e-12
#define Num_threads 1 
#define Time_Limit 3600 
#define Negative_infinity -1000000
#define Positive_infinity 1000000
#define epsilon 1.0e-6
#define Abs_Optimal_Tol 1.0e-6
#define Rel_Optimal_Tol 1.0e-6
#define denominator 1.0e-6


char* LP_file_name;
char* IP_file_name;
int N_Variables;
int N_Objectives;
struct timeval startTime, endTime;
double totalTime(0);
double clock_Run_time(0);
double clock_start_time;
double* Y;
double run_start;
double run_time;
double T_limit;
double Global_UB;
double Global_LB;
double UB;
bool Initial_infeasible;
vector <int> Integer_variables;
bool It_is_Added;
int k_val;
int pow_val;
int Number_of_Constraints;
int Nodes_explored=0;
int Nodes_proned=0;
int Nodes_inf=0;
double Initial_GLB=0;
/*------------------------------------------------------------------------------
 
 ------------------------Declaring CPLEX information----------------------------
 
 -----------------------------------------------------------------------------*/
ILOSTLBEGIN
typedef IloArray<IloNumVarArray> NumVar2DArray;
IloEnv env;
IloModel model(env);
IloObjective cost(env);
IloNumVar Ratio_Var(env, -IloInfinity, +IloInfinity, ILOFLOAT);

IloRangeArray rngs(env);
IloSOS1Array sos1(env);
IloSOS2Array sos2(env);
IloNumVarArray dec_var(env);
IloExprArray ObjF(env);
IloObjective object(env);
IloCplex cplex(env);
IloExpr Expr_Int(env);
IloExpr Expr_Lp(env);
IloRangeArray Bounds(env);
IloExpr Math(env);
IloExpr IntMath(env);
IloModel Intmodel(env);
IloCplex Intcplex(Intmodel);
IloObjective Intobj(env);

IloNumVarArray Int_dec_var(env);
IloRangeArray Int_constraint(env);
IloSOS1Array Intsos1(env);
IloSOS2Array Intsos2(env);
IloExprArray IntObjF(env);
IloRangeArray Binary_point(env);
IloRangeArray Tabulist(env);
IloRangeArray IntTabulist(env);
IloRangeArray IntBounds(env);

/*------------------------------------------------------------------------------
 
 ------------------------------------Functions-----------------------------------
 
 -----------------------------------------------------------------------------*/


void Reading_LP_File_and_Generating_CPLEX_Variables() {
    Intcplex.importModel(Intmodel, IP_file_name, Intobj, Int_dec_var, Int_constraint, Intsos1, Intsos2);
    Intsos1.clear();
    Intsos1.end();
    Intsos2.clear();
    Intsos2.end();
    Intmodel.remove(Intobj);
    cplex.importModel(model, LP_file_name, object, dec_var, rngs, sos1, sos2);
    N_Variables = dec_var.getSize();
    ObjF.end();
    IntObjF.end();
    ObjF = IloExprArray(env, N_Objectives);
    IntObjF = IloExprArray(env, N_Objectives);
    cplex.end();
    Intcplex.end();
    cplex = IloCplex(env);
    Intcplex = IloCplex(env);
    Y = new double [N_Objectives];
    for (int i = 0; i < N_Variables; i++) {
        if (Int_dec_var[i].getType() == 3) {
            Integer_variables.push_back(i);

            rngs.add(dec_var[i]<=1);  
            rngs.add(dec_var[i]>=0);
            
        }else if(Int_dec_var[i].getType() == 1){
            cout<<"** CONVERT INTEGER Variables to Binary"<<endl;
        }
    }
    Intmodel.remove(Int_constraint);
    model.remove(rngs);
    for (int i = 0; i < N_Objectives; i++) {
        ObjF[i] = rngs[0].getExpr();
        IntObjF[i] = Int_constraint[0].getExpr();
        rngs.remove(0);
        Int_constraint.remove(0);
    }
    Number_of_Constraints= Int_constraint.getSize() - N_Objectives;
    Intmodel.add(Int_constraint);
    model.add(rngs);
    Expr_Int.clear();
    Expr_Lp.clear();
    for (int i = 0; i < N_Objectives; i++) {
        Expr_Int += IntObjF[i];
        Expr_Lp += ObjF[i];
    }
    Intobj = IloMaximize(env, Expr_Int);
    Intmodel.add(Intobj);
    model.remove(object);
}



void Initial_SOCP() {
    run_start = clock();
    IloNumVar Small_lambda_var(env, 0.0, +IloInfinity, ILOFLOAT);
    cost = IloMaximize(env, Small_lambda_var);
    model.add(cost);
    IloNumVar Large_lambda_var(env, 0.0, +IloInfinity, ILOFLOAT);
    model.add(Small_lambda_var <= Large_lambda_var);
    for (int i = 0; i <= N_Objectives; i++) {
        pow_val = pow(2, i);
        k_val = i;
        if (pow_val >= N_Objectives) {
            break;
        }
    }
    NumVar2DArray Tau_var(env, k_val);
    for (int i = 0; i < k_val; i++) {
        Tau_var[i] = IloNumVarArray(env, pow_val);
    }
    for (int i = 0; i < k_val; i++) {
        for (int j = 0; j < pow_val; j++) {
            Tau_var[i][j] = IloNumVar(env, 0.0, +IloInfinity, ILOFLOAT);
        }
    }
    model.add(Large_lambda_var * Large_lambda_var - Tau_var[k_val - 1][0] * Tau_var[k_val - 1][1] <= 0);
    for (int i = 1; i <= k_val - 1; i++) {
        for (int j = 0; j < pow(2, k_val - i); j++) {
            model.add(Tau_var[i][j] * Tau_var[i][j] - Tau_var[i - 1][2 * j] * Tau_var[i - 1][2 * j + 1] <= 0);
        }
    }
    for (int j = 0; j < pow_val; j++) {
        if (j < N_Objectives) {
            model.add(Tau_var[0][j] == ObjF[j]);
        } else {
            model.add(Tau_var[0][j] == Large_lambda_var);
        }
    }
    cplex.extract(model);
    cplex.setOut(env.getNullStream());
    cplex.setParam(IloCplex::Threads, Num_threads);
    cplex.setParam(IloCplex::TiLim, T_limit);
    cplex.setParam(IloCplex::Param::Barrier::QCPConvergeTol, CONVTOL);
    cplex.setParam(IloCplex::EpGap, CPLEX_Relative_Gap);
    Initial_infeasible = 0;
    if (cplex.solve()) {
        Global_UB = pow(cplex.getObjValue(), N_Objectives);
    } else {
        Initial_infeasible = 1;
        cout<<"Infeasible"<<endl;
    }
    run_time = clock() - run_start;
    run_time = run_time / CLOCKS_PER_SEC;
    T_limit -= run_time;
    if (T_limit < 0) {
        T_limit = 0;
    }
}

class Node {
public:
//    vector <IloExpr> Tabu;
//    vector <IloExpr> IntTabu;
    double* LB_for_Obj;
    double* Value_Obj;
    bool Infeasible;
    double UB;
    double LB;
    int Identifier;
    double cutter;
    

    Node() {
        LB_for_Obj = new double [N_Objectives];
        Value_Obj = new double [N_Objectives];
        for (int i = 0; i < N_Objectives; i++) {
            LB_for_Obj[i] = Negative_infinity;
            Value_Obj[i] = Negative_infinity;
        }
        Infeasible = 0;
        cutter= Positive_infinity;
    }

    void Reinitializing_The_Node(Node* Parent, int identifier) {
//        Tabu = Parent->Tabu;
//        IntTabu = Parent->IntTabu;
        for (int i = 0; i < N_Objectives; i++) {
            LB_for_Obj[i] = Parent->LB_for_Obj[i];
        }
        Identifier = identifier;
        LB_for_Obj[Identifier] = Parent->Value_Obj[Identifier];
        cutter = Parent->cutter;
        UB=Parent->UB;
    }

    void Node_UB_Finder() {
        Nodes_explored++;
        run_start = clock();
        Bounds.clear();
        IntBounds.clear();
        Bounds.add(Expr_Lp <= (cutter*(1 + epsilon)));
        IntBounds.add(Expr_Int <= (cutter*(1 + epsilon)));

        for (int i = 0; i < N_Objectives; i++) {
            Bounds.add(ObjF[i] >= LB_for_Obj[i] - epsilon);
            IntBounds.add(IntObjF[i] >= LB_for_Obj[i] - epsilon);
        }

        model.add(Tabulist);
        model.add(Bounds);
        cplex.clear();
        cplex.extract(model);
        cplex.setOut(env.getNullStream());
        cplex.setParam(IloCplex::Threads, Num_threads);
        cplex.setParam(IloCplex::TiLim, T_limit);
        cplex.setParam(IloCplex::Param::Barrier::QCPConvergeTol, CONVTOL);
        cplex.setParam(IloCplex::EpGap, CPLEX_Relative_Gap);
        if (cplex.solve()) {
            UB = pow(cplex.getObjValue(), N_Objectives);
        } else {
            Infeasible = 1;
            Nodes_inf++;
        }
        cplex.clear();
        model.remove(Tabulist);
        model.remove(Bounds);
        Bounds.clear();
        run_time = clock() - run_start;
        run_time = run_time / CLOCKS_PER_SEC;
        T_limit -= run_time;
        if (T_limit < 0) {
            T_limit = 0;
        }
    }

    void Node_LB_Finder() {
        run_start = clock();
        Intmodel.add(IntTabulist);
        Intmodel.add(IntBounds);
        Intcplex.clear();
        Intcplex.extract(Intmodel);
        Intcplex.setOut(env.getNullStream());
        Intcplex.setParam(IloCplex::Threads, Num_threads);
        Intcplex.setParam(IloCplex::TiLim, T_limit);
        Intcplex.setParam(IloCplex::Param::Barrier::QCPConvergeTol, CONVTOL);
        Intcplex.setParam(IloCplex::EpGap, CPLEX_Relative_Gap);
        Math.clear();
        IntMath.clear();
        Binary_point.clear();
        if (Intcplex.solve()) {
            for (int i = 0; i < N_Objectives; i++) {
                    Value_Obj[i] = Intcplex.getValue(IntObjF[i]);
                }
            cutter= Intcplex.getObjValue();
            for (int i = 0; i < Integer_variables.size(); i++) {
                Binary_point.add(dec_var[Integer_variables.at(i)] == Intcplex.getValue(Int_dec_var[Integer_variables.at(i)]));
                if (Intcplex.getValue(Int_dec_var[Integer_variables.at(i)]) >= 1 - epsilon) {
                    Math += (1 - dec_var[Integer_variables.at(i)]);
                    IntMath += (1 - Int_dec_var[Integer_variables.at(i)]);
                } else {
                    Math += dec_var[Integer_variables.at(i)];
                    IntMath += (Int_dec_var[Integer_variables.at(i)]);
                }
            }
            Tabulist.add(Math >= 1);
            IntTabulist.add(IntMath >= 1);
            Math.clear();
            IntMath.clear();
        } else {
            Infeasible = 1;
            Nodes_inf++;
        }
        Intcplex.clear();
        Intmodel.remove(IntTabulist);
        Intmodel.remove(IntBounds);
        IntBounds.clear();
        run_time = clock() - run_start;
        run_time = run_time / CLOCKS_PER_SEC;
        T_limit -= run_time;
        if (T_limit < 0) {
            T_limit = 0;
        }
        run_start = clock();
        if (Infeasible == 0) {
            model.add(Binary_point);
            cplex.clear();
            cplex.extract(model);
            cplex.setOut(env.getNullStream());
            cplex.setParam(IloCplex::Threads, Num_threads);
            cplex.setParam(IloCplex::TiLim, T_limit);
            cplex.setParam(IloCplex::Param::Barrier::QCPConvergeTol, CONVTOL);
            cplex.setParam(IloCplex::EpGap, CPLEX_Relative_Gap);
            if (cplex.solve()) {
                LB = pow(cplex.getObjValue(), N_Objectives);
            }
            cplex.clear();
            model.remove(Binary_point);
        }
        Binary_point.clear();
        run_time = clock() - run_start;
        run_time = run_time / CLOCKS_PER_SEC;
        T_limit -= run_time;
        if (T_limit < 0) {
            T_limit = 0;
        }
    }

    virtual ~Node() {
        delete [] LB_for_Obj;
        delete [] Value_Obj;
    }
};

vector <Node*>Tree_of_Nodes;

void Writing_Output(){
    ofstream OutputFile;
    OutputFile.open("Output.txt", ios::app);
    OutputFile<<IP_file_name<<" GLB= "<< std::setprecision(10) << Global_LB<< " GUB= "<< Global_UB<<" Gap= "<< (Global_UB-Global_LB)/Global_UB << " #VAR= "<< N_Variables - N_Objectives << " #Const= "<< Number_of_Constraints<< " Time= "<< (clock_Run_time / CLOCKS_PER_SEC)<<" Open= "<<Tree_of_Nodes.size()<<" Explored= "<<Nodes_explored<<" Inf= "<<Nodes_inf<<" Pruned= "<<Nodes_proned;
    if(Global_LB>=Initial_GLB-epsilon && Global_LB <= Initial_GLB + epsilon){
        OutputFile<<" Initial optimality= "<<1<<endl;
    }else{
        OutputFile<<" Initial optimality= "<<0<<endl;
    }
    OutputFile.close();
}

void Create_Node_Zero(Node* Node_Zero) {
    run_start = clock();
    Node_Zero->UB = Global_UB;
    Intcplex.extract(Intmodel);
    Intcplex.setOut(env.getNullStream());
    Intcplex.setParam(IloCplex::Threads, Num_threads);
    Intcplex.setParam(IloCplex::TiLim, T_limit);
    Intcplex.setParam(IloCplex::Param::Barrier::QCPConvergeTol, CONVTOL);
    Intcplex.setParam(IloCplex::EpGap, CPLEX_Relative_Gap);
    Math.clear();
    IntMath.clear();
    Binary_point.clear();
    if (Intcplex.solve()) {
        for (int i = 0; i < N_Objectives; i++) {
                Node_Zero->Value_Obj[i] = Intcplex.getValue(IntObjF[i]);
            }
        Node_Zero->cutter = Intcplex.getObjValue();
        for (int i = 0; i < Integer_variables.size(); i++) {
            Binary_point.add(dec_var[Integer_variables.at(i)] == Intcplex.getValue(Int_dec_var[Integer_variables.at(i)]));
            if (Intcplex.getValue(Int_dec_var[Integer_variables.at(i)]) >= 1 - epsilon) {
                Math += (1 - dec_var[Integer_variables.at(i)]);
                IntMath += (1 - Int_dec_var[Integer_variables.at(i)]);
            } else {
                Math += dec_var[Integer_variables.at(i)];
                IntMath += (Int_dec_var[Integer_variables.at(i)]);
            }
        }
        Tabulist.add(Math >= 1);
        IntTabulist.add(IntMath >= 1);
        Math.clear();
        IntMath.clear();
    } else {
        Node_Zero->Infeasible = 1;
    }
    Intcplex.clear();
    run_time = clock() - run_start;
    run_time = run_time / CLOCKS_PER_SEC;
    T_limit -= run_time;
    if (T_limit < 0) {
        T_limit = 0;
    }

    run_start = clock();
    if (Node_Zero->Infeasible == 0) {
        model.add(Binary_point);
        cplex.extract(model);
        cplex.setOut(env.getNullStream());
        cplex.setParam(IloCplex::Threads, Num_threads);
        cplex.setParam(IloCplex::TiLim, T_limit);
        cplex.setParam(IloCplex::Param::Barrier::QCPConvergeTol, CONVTOL);
        cplex.setParam(IloCplex::EpGap, CPLEX_Relative_Gap);
        if (cplex.solve()) {
            Node_Zero->LB = pow(cplex.getObjValue(), N_Objectives);
        }
        model.remove(Binary_point);
    } else {
        cout << "Integer Infeasible" << endl;
    }
    cplex.clear();
    Binary_point.clear();
    run_time = clock() - run_start;
    run_time = run_time / CLOCKS_PER_SEC;
    T_limit -= run_time;
    if (T_limit < 0) {
        T_limit = 0;
    }
}

void Add_The_Node_To_Tree(Node* New_Generated_Node) {
    run_start = clock();
    Node * New_Node[N_Objectives];

        //*********//
        for (int i = 0; i < N_Objectives; i++) {
            New_Node[i] = new Node;
            New_Node[i]->Reinitializing_The_Node(New_Generated_Node, i);
        }
    
    
    It_is_Added = 0;
    for (int i = 1; i < Tree_of_Nodes.size(); i++) {
        if (New_Generated_Node->UB > Tree_of_Nodes.at(i)->UB + epsilon) {
            for (int j = 0; j < N_Objectives; j++) {
                Tree_of_Nodes.insert(Tree_of_Nodes.begin() + i, New_Node[j]);
        }
            
            It_is_Added = 1;
            break;
        }
    }
    if (It_is_Added == 0) {
        for (int j = 0; j < N_Objectives; j++) {
                Tree_of_Nodes.push_back( New_Node[j]);
        }
    }
    run_time = clock() - run_start;
    run_time = run_time / CLOCKS_PER_SEC;
    T_limit -= run_time;
    if (T_limit < 0) {
        T_limit = 0;
    }
}

void Branch_and_bound() {
    while (T_limit > 0 && Tree_of_Nodes.size() > 0 && (Global_UB > Global_LB + Abs_Optimal_Tol) && (Global_UB - Global_LB) / (Global_UB + denominator) > Rel_Optimal_Tol) {
        Tree_of_Nodes.front()->Node_UB_Finder();
        if (Tree_of_Nodes.front()->Infeasible == 0 && Tree_of_Nodes.front()->UB > Global_LB) {
                Tree_of_Nodes.front()->Node_LB_Finder();
                if (Tree_of_Nodes.front()->Infeasible == 0) {
                    if(Global_LB< Tree_of_Nodes.front()->LB){
                        Global_LB= Tree_of_Nodes.front()->LB;
                    }
                    Add_The_Node_To_Tree(Tree_of_Nodes.front());
                }
            } else {
            if(Tree_of_Nodes.front()->UB <= Global_LB){
                Nodes_proned++;
            }
            }
        IntBounds.clear();
        Tree_of_Nodes.front()->~Node();
        Tree_of_Nodes.erase(Tree_of_Nodes.begin());
        Global_UB=Tree_of_Nodes.front()->UB;
        
        if (Global_UB <= Global_LB + Abs_Optimal_Tol || Tree_of_Nodes.size() == 0 || (Global_UB - Global_LB) / (Global_UB + denominator) <= Rel_Optimal_Tol) {
            Global_UB = Global_LB;
        }
    }
}

int main(int argc, char *argv[]) {
    //---------------------------Preparation Phase------------------------------
    IP_file_name = argv[1];
    LP_file_name = argv[2];
    N_Objectives = atoi(argv[3]);
    T_limit = Time_Limit;
    
    Reading_LP_File_and_Generating_CPLEX_Variables();
    Global_LB = Negative_infinity;
    Global_UB = Positive_infinity;
    gettimeofday(&startTime, NULL);
    clock_start_time = clock();
    Initial_SOCP();
    if (Initial_infeasible == 0) {
        Node* Initial_Node = new Node;
        Create_Node_Zero(Initial_Node);
        if (Global_LB < Initial_Node->LB) {
            Global_LB = Initial_Node->LB;
            Initial_GLB=Initial_Node->LB;
        }
        if (Initial_Node->Infeasible == 0) {
            Add_The_Node_To_Tree(Initial_Node);
            Branch_and_bound();
        }
    } else {
        cout << "Infeasible" << endl;
    }
    gettimeofday(&endTime, NULL);
    clock_Run_time += (clock() - clock_start_time);
    totalTime += ((endTime.tv_sec - startTime.tv_sec) * 1000000L);
    totalTime += (endTime.tv_usec - startTime.tv_usec);
    Writing_Output();
    return 0;
}

