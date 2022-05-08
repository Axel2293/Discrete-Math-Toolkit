

from cProfile import label
from cgitb import text
from tkinter import Label,Button, StringVar,ttk,Entry,Frame,Tk, Text
from tkinter import *
from turtle import width


from PIL import Image, ImageTk 

import re
from setuptools import Command
from tabulate import tabulate


 
# ===== Count the number of n variables in expresion
def vars_n(exp):
    array=["P","Q","R","S","U","W","X","Y","Z"]
    cont = 0
    var_total = 0     
    for i in array:
        if i in exp:
            var_total += 1
            cont += 1
    #print(var_total)
    return(var_total)

# ======= Obtain all n variables in one list
def vars_list(proposition):
    array=["P","Q","R","S","U","W","X","Y","Z"]
    li=[]
    cont=0
    for i in range(len(proposition)):
        for l in range(len(array)):
            if proposition[i] in array[0+l]:
                if proposition[i] not in (li):
                    li.append(proposition[i])
                cont+=1
    return li

## ======= Obtain counter of sub-expresions in a expresion 
def ver_sub_str(sub_str):
    i=0
    cont=0
    cont_sub=0
    for i in range(len(sub_str)):
        if sub_str[0+cont] == "(":
            cont+=1;
            cont_sub+=1;
        else:
            cont+=1
    return cont_sub

#===== Extract sub-expresions in a string
def extract_sub(sub_str):
    #print("FUNC: ",sub_str)
    for j in range(len(sub_str)):
        if sub_str.count("(")>sub_str.count(")"):
            sub_str+=")"
    if ver_sub_str(sub_str)>1:
        sub_str=sub_str[1:-1]
    add=re.findall(r'\(.*?\)', sub_str)
    ##print (add)
    return add

#======= Denial of a variable, just returns an atomic expresion like ~p

li_not=list()
def atomic_not(exp):
    global li_not
    if exp.count("~") >=1:
        i=0
        for i in range(len(exp)):
            temp_not=""
            if exp[i]=="~" and exp[i-1]=="(" and exp[i+1]!="(":
                temp_not+=exp[i-1]
                temp_not+=exp[i]
                temp_not+=exp[i+1]
                temp_not+=")"
                li_not.append(temp_not)
            elif exp[i]=="~" and exp[i-1]!="(" and exp[i+1]!="(":
                temp_not+="("
                temp_not+=exp[i]
                temp_not+=exp[i+1]
                temp_not+=")"
                li_not.append(temp_not)

#======= Biconditional formating for replacement with logical equivalent (USELES AFTER posibility of using "==")
def biconditional(exp):
    #Equivalente lógico (p→q)^(q→p)
    temp=exp
    for i in range(len(exp)):
        # p Bicondicional q
        remp=""
        var1=""
        var2=""
        format_bi=""
        # p BI q
        if exp[i] =="↔" and exp[i-2]!="~" and exp[i+1]!="~" and exp[i+1]!="(" and exp[i-1]!=")":
            #print("1")
            remp=exp[(i-2):(i+3)]
            var1=exp[i-1]
            var2=exp[i+1]
            format_bi="(({0}→{1})^({1}→{0}))".format(var1,var2)
            temp=temp.replace(remp,format_bi)
        # ~p BI ~q
        elif exp[i] =="↔" and exp[i-2]=="~" and exp[i+1]=="~" and exp[i+1]!="(" and exp[i-1]!=")":
            #print("2")
            #print("2",exp[(i-3):(i+4)])
            remp=exp[(i-3):(i+4)]
            var1="~"+exp[i-1]
            var2="~"+exp[i+2]
            format_bi="(({0}→{1})^({1}→{0}))".format(var1,var2)
            temp=temp.replace(remp,format_bi)
        # ~p BI q
        elif exp[i] =="↔" and exp[i-2]=="~" and exp[i+1]!="~" and exp[i+1]!="(" and exp[i-1]!=")":
            #print("3")
            remp=exp[(i-3):(i+3)]
            var1="~"+exp[i-1]
            var2=exp[i+1]
            format_bi="(({0}→{1})^({1}→{0}))".format(var1,var2)
            temp=temp.replace(remp,format_bi)
        # p BI ~q
        elif exp[i] =="↔" and exp[i-2]!="~" and exp[i+1]=="~" and exp[i+1]!="(" and exp[i-1]!=")":
            #print("4")
            var1=exp[i-1]
            var2="~"+exp[i+2]
            format_bi="(({0}→{1})^({1}→{0}))".format(var1,var2)
            remp=exp[(i-2):(i+4)]
            temp=temp.replace(remp,format_bi)
        #print("BI : ",temp)
    return temp

#======= Main function (Checks for implications, evaluates and controls the sub-expresion process, creates the table)
def main(exp):
    global li_imp,li_not
    temp_imp=""
    rows=[]
    encabezado=[]
    exp=biconditional(exp)
    ## En caso de tener implicacion remplazamos por el equivalente lógico: (Var→Var) = (~Var or Var)
    for i in range(len(exp)):
        # p implicación q
        remp=""
        temp_imp=""
        if exp[i] =="→" and exp[i-2]!="~" and exp[i+1]!="~":
            #print("1", )
            remp=exp[(i-2):(i+3)]
            temp_imp+="(~";
            temp_imp+=exp[i-1];
            temp_imp+="V"
            temp_imp+=exp[i+1];
            temp_imp+=")";
            #print(remp," : ", temp_imp)
            exp=exp.replace(remp,temp_imp)

        # ~p imp ~q
        elif exp[i] =="→" and exp[i-2]=="~" and exp[i+1]=="~":
            #print("2",exp[(i-3):(i+4)])
            remp=exp[(i-3):(i+4)]
            temp_imp+="(";
            #temp_imp+=exp[i-2];
            temp_imp+=exp[i-1];
            temp_imp+="V"
            temp_imp+="(";
            temp_imp+=exp[i+1];
            temp_imp+=exp[i+2];
            temp_imp+="))";
            exp=exp.replace(remp,temp_imp)
        # ~p imp q
        elif exp[i] =="→" and exp[i-2]=="~" and exp[i+1]!="~":
            remp=exp[(i-3):(i+3)]
            #print("3", remp)
            temp_imp+="(~(";
            temp_imp+=exp[i-2];
            temp_imp+=exp[i-1];
            temp_imp+=")";
            temp_imp+="V"
            temp_imp+=exp[i+1];
            temp_imp+=")";
            exp=exp.replace(remp,temp_imp)
        # p imp ~q
        elif exp[i] =="→" and exp[i-2]!="~" and exp[i+1]=="~":
            #print("4",exp[(i-2):(i+4)])
            remp=exp[(i-2):(i+4)]
            temp_imp+="(~";
            temp_imp+=exp[i-1];
            temp_imp+="V"
            temp_imp+=exp[i+1];
            temp_imp+=exp[i+2];
            temp_imp+=")";
            exp=exp.replace(remp,temp_imp)

    ##   Obtenemos las negaciones simples (~var)
    li_not=[]
    atomic_not(exp)

    """
    El metodo de Findall fue obtenido de los ejemplos de programas proporcionados por el profesor como apoyo
    """
    res = re.findall(r'\(.*?\)', exp)

    ##  Incomplete perenthesis (this repeats alot during the MAIN)
    for i in range(len(res)):
        if res[i].count("(")>res[i].count(")"):
            res[i]+=")"
    i=0
    cont=0
    cont_sub=0
    add=""
    array=["^","v","+","~","↔"]

    ## Cicling to obtain the sub-strings
    for g_sub in res:
        i=0
        cont=0
        cont_sub=0
        cont_sub_exp=0
        for i in range(len(g_sub)):

            if g_sub[0+cont] == "(":
                cont+=1;
                cont_sub+=1;
            else:
                cont+=1

            if g_sub[0+i] in array:
                cont_sub_exp+=1
        if cont_sub>1 and cont_sub_exp>=2:
            i=""

            g_sub=g_sub[1:-1]

            add=re.findall(r'\(.*?\)', g_sub)
            for i in add:
                res.append(i)
                k=0
                for k in range(len(res)):
                    if res[k].count("(")>res[k].count(")"):
                        res[k]+=")"
                while ver_sub_str(i)>1:
                    i=extract_sub(i)
                    k=0
                    if type(i) == str():
                        res.append(i)
                    elif type(i)== list():
                        for k in i:
                            res.append(i)
                    j=0
                    for j in range(len(res)):
                        if res[j].count("(")>res[j].count(")"):
                            res[j]+=")"


    # Complete parenthesis
    for i in range(len(res)):
        if res[i].count("(")>res[i].count(")"):
            res[i]+=")"
    l=0
    cont=0

    ## Delete extra parenthesis ((p^q))
    for l in res:
        if l[0:2]=="((" and l[-2:]=="))":
            res[0+cont]=res[0+cont].replace("((","(")
            res[0+cont]=res[0+cont].replace("))",")")
            cont+=1
        cont+=1

    exp_final=list()

    #   Cleaning of repeated denials of variables
    temp=[]
    k=""
    for k in li_not:
        if k not in temp:
            temp.append(k)
    lin_not=temp

    ## Add denial sub-expresions to final list
    i=""
    for i in li_not:
        exp_final.append(i)
    #  order from bigger to samaller (lenght of characters)
    i=""
    ordenados_len=sorted(res, key=len)
    for i in ordenados_len:
        exp_final.append(i)

    # If we don´t get the typed expresion we add it to the final list
    if exp not in exp_final:
        exp_final.append(exp)
    


    ##     Max number of combinations
    max_combinations=2**vars_n(exp)

    ##     Order variables on alphabetic order
    tokens=sorted(vars_list(exp))

    #  Combine list of denials and sub-expresions
    k=""
    temp=[]
    for k in exp_final:
        if k not in temp:
            temp.append(k)
    exp_final=temp
    res=""
    i=""

    #  Header for out table
    encabezado=[]
    for i in tokens:
        encabezado.append(i)
    i=""
    for i in exp_final:
        encabezado.append(i)



    rows=[]
    i=0
    li_combi_fin=[]
    li_eval_final=[]
    table=""
    """
    The used method of using binary to obtan the combinations of every variable was obtained from the added
    youtube video
    """
    """
    Usamos Binario para obtener las combinaciones de True y False que asignaremos a cada variable
    Este método fue idea de Sluiter que explica en un video como realizar esto
    Link: https://www.youtube.com/watch?v=rf30vfA7NTA&t=490s&ab_channel=ProgrammingwithProfessorSluiter
    """

    for i in range(0, max_combinations):
        CBN=bin(i)[2:].zfill(vars_n(exp))
        li_combi=[]

        # Remplazamos valores binarios de 0 y 1 para tener True y False, tambien obtenemos la lista de combinaciones
        for letter in str(CBN):
            if letter =="0":
                letter=False
            else:
                letter=True
            li_combi.append(letter)
        li_combi_fin.append(li_combi)
        
        # obtenemos las combinaciones para las variables
        row_evaluar=li_combi_fin[i]
        row_fin=[]
        i=""
        #  Agregamos la combinacion de variables a nuestra fila de evaluaciones
        for i in row_evaluar:
            row_fin.append(i)

        #Evaluamos cada expresion en nuestra lista separada
        for ev_sub_exp in exp_final:
            cont=0
            for var_rempl in tokens:
                if var_rempl in ev_sub_exp:
                    ev_sub_exp=ev_sub_exp.replace(str(var_rempl),str(row_evaluar[0+cont]))
                    #print("REP: ",ev_sub_exp)
                    cont+=1
                else:
                    cont+=1
            #remplazamos los conectivos logicos básicos
            ev_sub_exp=ev_sub_exp.replace("^","&")
            ev_sub_exp=ev_sub_exp.replace("V","|")
            ev_sub_exp=ev_sub_exp.replace("+","^")
            ev_sub_exp=ev_sub_exp.replace("↔","==")
            temp_eval_sub=[]
            i_temp=eval(str(ev_sub_exp))
            #en caso de tener negaciones
            if str(i_temp) =="-1":
                i_temp=True
            elif str(i_temp) =="-2":
                i_temp=False
            elif str(i_temp)=="1":
                i_temp=True
            elif str(i_temp)=="0":
                i_temp=False
            
            temp_eval_sub.append(i_temp)
            row_fin.append(temp_eval_sub)

        #  Obtenemos las filas finales
        rows.append(row_fin)

    ## ======== Tabulamos la tabla de verdad con nuestro HEADER(variables y expresiones) y las filas(Valores T-F para variables y evaluaciones)
    #  Libreria de Sergei Astanin https://github.com/astanin/python-tabulate
    truth_table.insert(END,tabulate(rows,headers=encabezado,tablefmt='pretty'))

        #End section of TTG
#==========================================================================================#
        #Start section SETS
# Recieves the set and returs the total number of elements CARDINALIDAD
def cardinalidad(set_prueba):
    non_set=[]
    set_prueba=list(set_prueba)
    for i in range(len(set_prueba)):
        if set_prueba[i] not in non_set:
            non_set.append(set_prueba[i])
    return len(non_set)


#================UNION=========

    # 3 sets UNION
def union(set_a, set_b, set_c):
    set_a=list(set_a)
    set_b=list(set_b)
    set_c=list(set_c)

    res=list()
    # AUB
    res=set_a
    for i in range(len(set_b)):
        if set_b[i] not in res:
            res.append(set_b[i])
    i=0
    for i in range(len(set_c)):
        if set_c[i] not in res:
            res.append(set_c[i])
    return set(res)
    
    # 2 sets union
def union_2(set_1, set_2):
    set_1=list(set_1)
    set_2=list(set_2)
    res=list()

    res=set_1
    for i in range(len(set_2)):
        if set_2[i] not in res:
            res.append(set_2[i])
    
    return res
## =====INTERSECCION=============
def inter_3(set_1, set_2, set_3):
    set_1=list(set_1)
    set_2=list(set_2)
    set_3=list(set_3)
    res=list()
    res_1_2=list()
    res_1_2=inter_2(set_1,set_2)
    for i in range(len(set_3)):
        if set_3[i] in res_1_2:
            res.append(set_3[i])
    return res

def inter_2(set_1,set_2):
    set_1=list(set_1)
    set_2=list(set_2)
    res=list()
    
    for i in range(len(set_2)):
        if set_2[i] in set_1:
            res.append(set_2[i])
    return res

#====Diferencia============
def diferencia(set_1,set_2):
    set_1=list(set_1)
    set_2=list(set_2)
    res=list()
    #  s1  -  s2    
    for i in range(len (set_1)):
        if set_1[i] in set_2:
            pass
        elif set_1[i] not in set_2:
            res.append(set_1[i])
    return res
#===Diferencia simétrica==
def dif_sim(set_1, set_2):
    set_1=list(set_1)
    set_2=list(set_2)
    # Using equivalent (A-B) Union (B-A)
    temp_1=diferencia(set_1,set_2)
    temp_2=diferencia(set_2, set_1)
    res=union_2(temp_1, temp_2)
    return res
    
    #End section of sets
#=========================================================
    #Start section of sucesiones

#Calculates the aₖ given k

def general_termsKN(n, k, ak):
    global final_res
    n=int(n)
    k=int(k)
    if k<=n:
        final_res+="Termino a({}) = {:.4f}\n".format(k,general_term(k, ak))
        general_termsKN(n,k+1,ak)
    else: 
        return 0


def general_term(k, ak):
    ak.replace("k", str(k))
    return eval(ak)


    #Global var for the result
final_res="""Los terminos aₖ se muestran aqui"""
# Sum of the aₖ terms (k to n) RECURSIVE
def sum_ak(n, k, ak):
    global final_res
    n=int(n)
    k=int(k)
    sum=float()
    if k<=n:
        sum=general_term(k,ak)
        # Limit to 4 decimals the shown result
        final_res+="Termino a({}) = {:.4f}\n".format(k,sum)
        #Calculations with recursive function
        sum+=sum_ak(n,k+1,ak)
        return sum
    else:
        return 0

# Product of the aₖ terms (k to n) RECURSIVE
def product_ak(n, k ,ak):
    global final_res
    n=int(n)
    k=int(k)
    product=float()
    if k<=n: 
        product=general_term(k,ak)
        # Limit to 4 decimals the shown result
        final_res+="Termino a({}) = {:.4f}\n".format(k,product)
        #Calculations with recursive function
        product= product*sum_ak(n,k+1,ak)
        return product
    else:
        return 0


# ================RELATIONS===================================

    # Dominio 
def x_obtain(relation):
    x_list=list()
    for i in range(len(relation)):
        if relation[i][0] not in x_list:
            x_list.append(relation[i][0])

    return x_list

    # Condominio
def y_obtain(relation):
    y_list=list()
    for i in range(len(relation)):
        if relation[i][1] not in y_list:
            y_list.append(relation[i][1])
    return y_list

def reflexivity(relation):
    refex_res=list()
    x_values=x_obtain(relation)

    for i in range(len(x_values)):
        refex_res.append(0)

    for i in range(len(x_values)):
        for j in range(len (relation)):
            if x_values[i] == relation[j][1]:
                refex_res[i]=1
    
    print(refex_res)
    cont=0
    for c in range(len(refex_res)):
        if refex_res[c]==1:
            cont+=1
    if cont==len(x_values):
        return 1
    else:
        return 0

def symmetry(relation):

    sym_list=list()
    cont=0
    for i in range(len(relation)):
        sym_list.append(0)

    for i in range(len (relation)):
        for j in range(len(relation)):
            if relation[i][0] == relation[j][1] and relation[i][1] == relation[j][0]:
                sym_list[i]=1

    for c in range(len(sym_list)):
        if sym_list[c]==1:
            cont+=1
    if cont==len(relation):
        return 1
    else:
        return 0

def transitivity(relation):
    res_trans=list()
    rels_yz=0
    for i in range(len(relation)):
        res_trans.append(0)

    cont=0
    for i in range(len(relation)):
        x=relation[i][0]
        y=relation[i][1]
        z=""
        # print("Verifying x,y: ", relation[i])
        cont=0
        rels_yz=0
        for j in range(len(relation)):

            if relation[j][0]==y:
                z=relation[j][1]
                rels_yz+=1
                # print("\tFound y,z :", relation[j])
                for c in range(len(relation)):

                    if relation[c][0] == x and relation[c][1] == z:
                        cont+=1
                        # print("\t\tYES")
                        break
                    # else:
                        # print("\t\tNot found  [",x,",",z,"] VER: ", relation[c] )
        if cont==rels_yz:
            # print("\tRELACION ES TRANSITIVA")
            res_trans[i]=1

    cont=0
    for i in range(len(res_trans)):
        if res_trans[i]==1:
            cont+=1
    if cont==len(relation):
        return 1
    else:
        return 0

# Verifies if a viven relation comes from a FUNCTION (x with more than one y value does not come from a fuction)
def function(relation):

    fun_res=list()
    x_list=x_obtain(relation)
    temp=list()

    for i in range(len(x_list)):
        cont=0
        temp=list()
        for j in range(len(relation)):
            if x_list[i]==relation[j][0]:
                temp.append(relation[j])
        if len(temp)==1:
            fun_res.append(1)
        else:
            fun_res.append(0)
        print(temp)

    
    cont=0
    for i in range(len(fun_res)):
        if fun_res[i]==1:
            cont+=1
    if cont==len(relation):
        return 1
    else:
        return 0





ventana=Tk()

ventana.title("FCC TOOLKIT 2022")
ventana.geometry("800x600")
ventana.config(bg="white")

exp=""
operator_selec=[]
union_op=["A∪B", "A∪C","B∪C", "A∪(B∪C)"]
int_op=["A∩B", "A∩C", "B∩C", "A∩(B∩C)"]
dif_op=["A-B", "A-C", "B-C"]
dif_sim_op=["A∆B","B∆C","A∆C"]
card=["|A|", "|B|", "|C|"]


#TTG section
def get_prop():
    exp=""
    exp= exp_entry.get()
    exp=exp.upper()
    exp=exp.replace(" ", "")
    truth_table.delete("1.0", "end")
    try:
        main(exp)
    except:
        truth_table.insert(END,"=          Error         =")

def insert_op(operation):
    exp_entry.insert(END, operation)

#SETS section
def update_options(selection):
    global union_op, int_op, dif_op, dif_sim_op,card
    
    if selection=="Union":
        operator_selec=union_op
    elif selection=="Interseccion":
        operator_selec=int_op
    elif selection=="Diferencia":
        operator_selec=dif_op
    elif selection=="Diferencia simetrica":
        operator_selec=dif_sim_op
    elif selection=="Cardinalidad":
        operator_selec=card
    else:
        print("No funciono jeje")
    selec_option.config(values=operator_selec)
    selec_option.current(0)
def str_list(string_set):
    final_set_list=list(string_set.split(","))
    return final_set_list

def calculate_result():
    global union_op, int_op, dif_op, dif_sim_op,card
        #Seleccion del usuario
    selection=selec_option.get()
        #Sets a trabajar str a list
    set_a_fu=str_list(sets_a.get())
    set_b_fu=str_list(sets_b.get())
    set_c_fu=str_list(sets_c.get())
    res_text=selec_option.get()
    try:
        if selection in union_op:
                #Case if 3 operation vars
            if selection==union_op[-1]:
                res=union(set_a_fu,set_b_fu,set_c_fu)
                res_text="Union A∪(B∪C) = {0}".format(res)                
                set_res.set(res_text)
                #Cases if 2 sets
            elif selection==union_op[0]:
                res=union_2(set_a_fu, set_b_fu)
                res_text="Union A∪B = {0}".format(res)
                set_res.set(res_text)
            elif selection==union_op[1]:
                res=union_2(set_a_fu, set_c_fu)
                res_text="Union A∪C = {0}".format(res)
                set_res.set(res_text)
            elif selection==union_op[2]:
                res=union_2(set_b_fu, set_c_fu)
                res_text="Union B∪C = {0}".format(res)
                set_res.set(res_text)
        elif selection in int_op:
            if selection==int_op[-1]:
                res=inter_3(set_a_fu,set_b_fu,set_c_fu)
                res_text="Interseccion A∩(B∩C) = {0}".format(res)                
                set_res.set(res_text)
                #Cases if 2 sets
            elif selection==int_op[0]:
                res=inter_2(set_a_fu, set_b_fu)
                res_text="Interseccion A∩B = {0}".format(res)
                set_res.set(res_text)
            elif selection==int_op[1]:
                res=inter_2(set_a_fu, set_c_fu)
                res_text="UInterseccion A∩C = {0}".format(res)
                set_res.set(res_text)
            elif selection==int_op[2]:
                res=inter_2(set_b_fu, set_c_fu)
                res_text="Interseccion B∩C = {0}".format(res)
                set_res.set(res_text)
        elif selection in dif_op:
            if selection==dif_op[0]:
                res=diferencia(set_a_fu, set_b_fu)
                res_text="Diferencia A-B = {0}".format(res)
                set_res.set(res_text)
            elif selection==dif_op[1]:
                res=diferencia(set_a_fu, set_c_fu)
                res_text="Diferencia A-C = {0}".format(res)
                set_res.set(res_text)
            elif selection==dif_op[2]:
                res=diferencia(set_b_fu, set_c_fu)
                res_text="Diferencia B-C = {0}".format(res)
                set_res.set(res_text)
        elif selection in dif_sim_op:
            if selection==dif_sim_op[0]:
                res=dif_sim(set_a_fu, set_b_fu)
                res_text="Diferencia simetrica A∆B = {0}".format(res)
                set_res.set(res_text)
            elif selection==dif_sim_op[1]:
                res=dif_sim(set_a_fu, set_c_fu)
                res_text="Diferencia simetrica A∆C = {0}".format(res)
                set_res.set(res_text)
            elif selection==dif_sim_op[2]:
                res=dif_sim(set_b_fu, set_c_fu)
                res_text="Diferencia simetrica B∆C = {0}".format(res)
                set_res.set(res_text)
        elif selection in card:
            if selection==card[0]:
                res=cardinalidad(set_a_fu)
                res_text="Cardinalidad |A| = {0}".format(res)
                set_res.set(res_text)
            elif selection==card[1]:
                res=cardinalidad(set_b_fu)
                res_text="Cardinalidad |B| = {0}".format(res)
                set_res.set(res_text)
            elif selection==card[2]:
                res=cardinalidad(set_c_fu)
                res_text="Cardinalidad |C| = {0}".format(res)
                set_res.set(res_text)
        else:
            res_lable.config(text="!Error!")
    except:
        res_lable.config(text="!Error!")


#=====SUCCESIONS===============================================
def ak_operations(opt):
    global final_res
    final_res=""
    sum_res=0
    str_sum=str()
    product_res=0
    str_product=str()
    result_ak.delete("1.0", "end")
    

    try:
        if opt==1:
            sum_res=sum_ak(n_lim.get(), k_lim.get(), ak_user.get())
            str_sum="Suma = {:.6f}".format(sum_res)
            sum_res_entry.set(str_sum)
        elif opt==2:
            product_res=product_ak(n_lim.get(), k_lim.get(), ak_user.get())
            str_product="Producto = {:.6f}".format(product_res)
            product_res_entry.set(str_product)
        elif opt==3:
            general_termsKN(n_lim.get(), k_lim.get(), ak_user.get())

        result_ak.insert("end", final_res)
    except:
        result_ak.insert("end", """ERROR : Intenta cuidar tus valores de n y k""")


def clean_output():
    result_ak.delete("1.0", "end")
    product_res_entry.set("Producto :")
    sum_res_entry.set("Suma :")

# ===========RELATIONS====================================================
def relations_main():
    try:
        raw_re=r_entry.get()
        R=re.findall(r'\(.*?\)', raw_re)
        # Delete all the parenthesis and make lists inside lists with "x","y"
        for i in range(len(R)):
            R[i]=R[i].replace("(", "")
            R[i]=R[i].replace(")", "")
            R[i]=R[i].split(",")
        
        #   Dominio
        x=x_obtain(R)
        print(x)
        r_domain.delete("1.0", "end")
        r_domain.insert("end", "Dominio : {")
        for i in range(len (x)):
            r_domain.insert("end", x[i])
            if i+1!=len(x):
                r_domain.insert("end", ",")
        r_domain.insert("end", "}")
        
        #    Condominio
        y=y_obtain(R)
        r_condomain.delete("1.0", "end")
        r_condomain.insert("end", "Condominio : {")
        for i in range(len (y)):
            r_condomain.insert("end", y[i])
            if i+1!=len(y):
                r_condomain.insert("end", ",")
        r_condomain.insert("end", "}")


        reflex_res=reflexivity(R)

        sym_res=symmetry(R)

        trans_res=transitivity(R)


        if reflex_res:
            reflex.config(text="Reflexividad : SI")
        else:
            reflex.config(text="Reflexividad : NO")
        if sym_res:
            sym.config(text="Simetria : SI")
        else:
            sym.config(text="Simetria : NO")
        if trans_res:
            trans.config(text="Transitividad : SI")
        else:
            trans.config(text="Transitividad : NO")


    except:
        r_domain.delete("1.0", "end")
        r_domain.insert("end","ERROR")
        r_condomain.delete("1.0", "end")
        r_condomain.insert("end","ERROR")
        reflex.config(text="ERROR")
        sym.config(text="ERROR")
        trans.config(text="ERROR")

#============MENU======================
def change_menu(option):
    if option==1:
        t_t_m.place_forget()
        frame_tt.place_forget()
        sets_frame.place_forget()
        suceciones_frame.place_forget()
        relat_frame.place_forget()
        info.place(x=50, y=240)
    elif option==2:
        info.place_forget()
        sets_frame.place_forget()
        suceciones_frame.place_forget()
        relat_frame.place_forget()
        t_t_m.place(x=50, y=180)
        frame_tt.place(x=50, y=300)
    elif option==3:
        info.place_forget()
        t_t_m.place_forget() 
        frame_tt.place_forget()
        suceciones_frame.place_forget()
        relat_frame.place_forget()
        sets_frame.place(x=50, y=180)
    elif option==4:
        info.place_forget()
        t_t_m.place_forget() 
        frame_tt.place_forget()
        sets_frame.place_forget()
        relat_frame.place_forget()
        suceciones_frame.place(x=50, y=180)
    elif option==5:
        info.place_forget()
        t_t_m.place_forget() 
        frame_tt.place_forget()
        sets_frame.place_forget()
        suceciones_frame.place_forget()
        relat_frame.place(x=50, y=180)

##========Up MENU==========================================
mnu=Frame(ventana, width=950, height=100, background="grey")
mnu.pack(side="top")
etiqueta1=Label(mnu, text="MENU", font="Helvetica 20", background="grey")
etiqueta1.place(x=20, y=15)

    #-----Buttons------------------------------------
boton_info=Button(mnu, text="INFO", height=2, width=8, 
    command=lambda:[change_menu(1)])
boton_info.place(x=20,y=55)
boton_ttm=Button(mnu, text="Tablas De Verdad", height=2, width=15, 
    command=lambda: [change_menu(2)])
boton_ttm.place(x=110,y=55)
boton_sets=Button(mnu, text="Conjuntos", height=2, width=10, 
    command=lambda:[change_menu(3)])
boton_sets.place(x=250, y=55)

boton_suc=Button(mnu ,text="Sucesiones", height=2, width=11,
    command=lambda:[change_menu(4)])
boton_suc.place(x=360, y=55)

boton_suc=Button(mnu ,text="Relaciones", height=2, width=11,
    command=lambda:[change_menu(5)])
boton_suc.place(x=480, y=55)

## ========== INFO ==========================================
info=Frame(ventana, width=760, height=500, background="Black")
info.place(x=20, y=180)
welcome=Label(info, text="Fundamentos de ciencias computacionales\n ToolKit", font="Arial 27 bold", )
welcome.pack(side="top")


#=============Truth table generator section==================
t_t_m=Frame(ventana, width=760,
    height=120,
    background="grey")
etiqueta_exp=Label(t_t_m, 
    text="Pon tu proposición", 
    font="Helvetica 20",
    background="grey")
etiqueta_exp.place(
    x=10,
    y=10)

    # Buttons of operators
and_button=Button(t_t_m,
    text="^",
    command=lambda:[insert_op('^')]).place(
        x=40,
        y=80)
or_button=Button(t_t_m,
    text="V",
    command=lambda:[insert_op('V')]).place(
        x=70,
        y=80)
xor_button=Button(t_t_m,
    text="+",
    command=lambda:[insert_op('+')]).place(
        x=100,
        y=80)
implication_button=Button(t_t_m,
    text="→",
    command=lambda:[insert_op('→')]).place(
        x=130,
        y=80)
biconditional_button=Button(t_t_m,
    text="↔",
    command=lambda:[insert_op('↔')]).place(
        x=160,
        y=80)

exp_strvar=StringVar()
exp_entry=Entry(t_t_m, 
    width=40,
    textvariable=exp_strvar)
exp_entry.place(
    x=30,
    y=50)
boton_ttm=Button(t_t_m, 
    text="Generar Tabla de Verdad", 
    height=1, 
    width=30, 
    command=lambda: [get_prop() ])
boton_ttm.place(
    x=300, 
    y=48)
        # Available operands for user to see
rules_tt=Label(t_t_m,
    text="Operadores: \n•And- ^\n•Or- v\n•Xor- +\n•Implicación- →\n•Bicondicional- ↔")
rules_tt.place(
    x=530, 
    y=15)
        #Placement of truth table on screen
frame_tt=Frame(ventana)

    # Scrollable table
y_scroll_tt=Scrollbar(frame_tt, orient='vertical')
y_scroll_tt.pack(side=RIGHT, fill="y")
x_scroll_tt=Scrollbar(frame_tt, orient='horizontal')
x_scroll_tt.pack(side='bottom', fill='x')
    
    # Text Truth Table
truth_table=Text(frame_tt,
    height=15, 
    yscrollcommand=y_scroll_tt.set, 
    xscrollcommand=x_scroll_tt.set, 
    wrap=NONE)
truth_table.pack(side=LEFT)

    # Commands of the Scrollbars
y_scroll_tt.config(command=truth_table.yview)
x_scroll_tt.config(command=truth_table.xview)


#=======================SETS=======================================
sets_frame=Frame(ventana, width=760, height=400, background="grey")

tag_sets=Label(sets_frame, 
    text="Conjuntos:", 
    font="Helvetica 20", 
    background="grey")
tag_sets.place(x=0, y=0)
seta_label=Label(sets_frame, text="A={")
seta_label.place(x=10,y=40)
setb_label=Label(sets_frame, text="B={")
setb_label.place(x=10,y=80)
setc_label=Label(sets_frame, text="C={")
setc_label.place(x=10,y=120)

## --------ENTRY FOR SETS OF USER----------##
sets_a=Entry(sets_frame, width=25)
sets_a.place(x=40, y=40)
sets_b=Entry(sets_frame, width=25)
sets_b.place(x=40, y=80)
sets_c=Entry(sets_frame, width=25)
sets_c.place(x=40, y=120)

#---------Operaciones Disponibles----------------
tag_operator=Label(sets_frame, 
    text="Operadores: ", 
    font="Helvetica 20", 
    background="grey")
tag_operator.place(x=0, y=160)
operators=["Union", "Interseccion", "Diferencia", "Diferencia simetrica", "Cardinalidad"]
op_selec=ttk.Combobox(sets_frame,
    state="",
    values=operators)
op_selec.current(0)
op_selec.place(x=200, y=170)
bot_act=Button(sets_frame, 
    text="Actualizar operaciones", 
    command=lambda:[update_options(op_selec.get())])
bot_act.place(x=410, y=170)

#----------Opciones------------
tag_options=Label(sets_frame, 
    text="Operaciones: ", 
    font="Helvetica 20", 
    background="grey")
tag_options.place(x=0, y=200)


selec_option=ttk.Combobox(sets_frame)
selec_option.place(x=200, y=210)

##---------Calcular resultado---------------
res_buttton= Button(sets_frame, 
    text="Calcular resultado", 
    command=lambda:[calculate_result()])
res_buttton.place(x=410, y=210)
#sets_frame.after(1000,print("Hola"))
#update_options(op_selec.get())
#op_selec.bind("<<ComoboxSelected>>", update_options(op_selec.get()))    
#---------Show result---------------
set_res=StringVar()
set_res.set("Result is shown here")
res_lable=Entry(sets_frame, 
    textvariable=set_res,
    width=70)
res_lable.place(x=0, y=270)

#======= Sucesiones ========================================

#    IMAGES
sum_img=ImageTk.PhotoImage(Image.open("sum.png"))
product_img=ImageTk.PhotoImage(Image.open("product.png"))
term_img=ImageTk.PhotoImage(Image.open("ak.png"))

suceciones_frame=Frame(ventana, width=680, 
    height=680, 
    background="grey")

# Buttons as images (Sum, product, terms)
sum_img_buton=Button(suceciones_frame, 
    image=sum_img,
    command=lambda:[ak_operations(1)]).place(x=150, y=35)
product_img_buton=Button(suceciones_frame, 
    image=product_img,
    command=lambda:[ak_operations(2)]).place(x=230, y=40)
term_img_buton=Button(suceciones_frame, 
    image=term_img,
    command=lambda:[ak_operations(3)]).place(x=310, y=55)

# n superior limit
n_text=Label(suceciones_frame,
    text="n = ",
    font="Helvetica 15",
    background="grey")
n_text.place(x=20, y=12)
n_lim=Entry(suceciones_frame, width=10)
n_lim.place(x=60, y=10)

# k inferior limit (start point)

k_text=Label(suceciones_frame, 
    text="k = ",
    font="Helvetica 15",
    background="grey")

k_text.place(x=20, y=50)
k_lim=Entry(suceciones_frame, width=10)
k_lim.place(x=60, y=50)

# aₖ the general term of the user

ak_text=Label(suceciones_frame,
    text="aₖ = ",
    font="Helvetica 15",
    background="grey").place(
                        x=20, 
                        y=85)
ak_user=Entry(suceciones_frame, width=10)
ak_user.place(x=60, y=87)
# Options
opt_lab=Label(suceciones_frame,
    text="Presiona la opcion a calcular",
    font="Helvetica 15").place(x=150, y=0)



# Results of the ak terms, not sum or product results

ak_ext_frame=Frame(suceciones_frame)
ak_ext_frame.place(x=10, y=140)
scroll_ak=Scrollbar(ak_ext_frame, 
    orient="vertical")
scroll_ak.pack(side=RIGHT, fill="y")

result_ak=Text(ak_ext_frame, yscrollcommand=scroll_ak.set, width=37, height=15)
result_ak.insert("end", final_res)
result_ak.pack(side=LEFT)
     
scroll_ak.config(command=result_ak.yview)

sum_res_entry=StringVar()
sum_res_screen=Entry(suceciones_frame, width=30, textvariable=sum_res_entry, state="readonly")
sum_res_screen.place(x=350, y=150)

product_res_entry=StringVar()
product_res_screen=Entry(suceciones_frame, width=30, textvariable=product_res_entry, state="readonly")
product_res_screen.place(x=350, y=200)

clean_results=Button(suceciones_frame, 
    text="Limpiar salidas",
    command=lambda:[clean_output()])
clean_results.place(x=350, y=250)


#==================RELATIONS=================

relat_frame=Frame(ventana ,width=680, height=400)

rel_labl=Label(relat_frame, text="Relación =")
rel_labl.place(x=1, y=0)

r_entry=Entry(relat_frame, width=40)
r_entry.place(x=20, y=20)

r_calculate=Button(relat_frame, text="Calcular", command=relations_main)
r_calculate.place(x=280, y=15)

# DOMAIN
domain_frame=Frame(relat_frame, width=370, height=60)
domain_frame.place(x=20, y=60)

y_scrolldomain_R=Scrollbar(domain_frame, orient='vertical')
y_scrolldomain_R.pack(side=RIGHT, fill="y")

r_domain=Text(domain_frame, width=40, heigh=6, yscrollcommand=y_scrolldomain_R.set)
r_domain.insert("end","Dominio : { }")
r_domain.pack(side=LEFT)

y_scrolldomain_R.config(command=r_domain.yview)

# CONDOMAIN
condomain_frame=Frame(relat_frame, width=370, height=120 )
condomain_frame.place(x=20, y=200)

y_scrollcondomain_R=Scrollbar(condomain_frame, orient='vertical')
y_scrollcondomain_R.pack(side=RIGHT, fill="y")

r_condomain=Text(condomain_frame, width=40, heigh=6, yscrollcommand=y_scrollcondomain_R.set)
r_condomain.insert("end","Condominio : { }")
r_condomain.pack(side=LEFT)

y_scrollcondomain_R.config(command=r_condomain.yview)

# REFLEXIVITY
reflex=Label(relat_frame, text="Reflexividad : ", background="white")
reflex.place(x=400, y=20)

# SYMMETRY
sym=Label(relat_frame, text="Simetría : ", background="white")
sym.place(x=400, y=60)

# TRANSITIVITY
trans=Label(relat_frame, text="Transitividad : ", background="white")
trans.place(x=400, y=100)



#========Main loop
ventana.mainloop()