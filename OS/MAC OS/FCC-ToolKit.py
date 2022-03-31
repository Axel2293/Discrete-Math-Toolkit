

from tkinter import *
from tkinter import ttk
import re
from setuptools import Command
from tabulate import tabulate


 
# ===== Count the number of n variables in expresion
def vars_n(exp):
    array=["P","Q","R","S","U","W","X","Y","Z"]
    cont=0
    var_total=0     
    for i in array:
        if i in exp:
            var_total+=1
            cont+=1
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
    truth_table.config(text=tabulate(rows,headers=encabezado,tablefmt='pretty'))

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

ventana=Tk()

ventana.title("FCC TOOLKIT 2022")
ventana.iconbitmap("Tkinter.ico")
ventana.geometry("800x600")
ventana.config(bg="white")

exp=""
operator_selec=[]
union_op=["A∪B", "A∪C","B∪C", "A∪(B∪C)"]
int_op=["A∩B", "A∩C", "B∩C", "A∩(B∩C)"]
dif_op=["A-B", "A-C", "B-C"]
dif_sim_op=["A∆B","B∆C","A∆C"]
card=["|A|", "|B|", "|C|"]

def get_prop():
    exp=""
    exp= exp_entry.get()
    exp=exp.upper()
    exp=exp.replace(" ", "")
    truth_table.config(text="")
    try:
        main(exp)
    except:
        truth_table.config(text="=          Error         =")

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
    final_set_list=list()
    for i in range(len(string_set)):
        if string_set[i]!=",":
            final_set_list.append(string_set[i])
        else:
            pass
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
                res_lable.config(text=res_text)
                #Cases if 2 sets
            elif selection==union_op[0]:
                res=union_2(set_a_fu, set_b_fu)
                res_text="Union A∪B = {0}".format(res)
                res_lable.config(text=res_text)
            elif selection==union_op[1]:
                res=union_2(set_a_fu, set_c_fu)
                res_text="Union A∪C = {0}".format(res)
                res_lable.config(text=res_text)
            elif selection==union_op[2]:
                res=union_2(set_b_fu, set_c_fu)
                res_text="Union B∪C = {0}".format(res)
                res_lable.config(text=res_text)
        elif selection in int_op:
            if selection==int_op[-1]:
                res=inter_3(set_a_fu,set_b_fu,set_c_fu)
                res_text="Interseccion A∩(B∩C) = {0}".format(res)                
                res_lable.config(text=res_text)
                #Cases if 2 sets
            elif selection==int_op[0]:
                res=inter_2(set_a_fu, set_b_fu)
                res_text="Interseccion A∩B = {0}".format(res)
                res_lable.config(text=res_text)
            elif selection==int_op[1]:
                res=inter_2(set_a_fu, set_c_fu)
                res_text="UInterseccion A∩C = {0}".format(res)
                res_lable.config(text=res_text)
            elif selection==int_op[2]:
                res=inter_2(set_b_fu, set_c_fu)
                res_text="Interseccion B∩C = {0}".format(res)
                res_lable.config(text=res_text)
        elif selection in dif_op:
            if selection==dif_op[0]:
                res=diferencia(set_a_fu, set_b_fu)
                res_text="Diferencia A-B = {0}".format(res)
                res_lable.config(text=res_text)
            elif selection==dif_op[1]:
                res=diferencia(set_a_fu, set_c_fu)
                res_text="Diferencia A-C = {0}".format(res)
                res_lable.config(text=res_text)
            elif selection==dif_op[2]:
                res=diferencia(set_b_fu, set_c_fu)
                res_text="Diferencia B-C = {0}".format(res)
                res_lable.config(text=res_text)
        elif selection in dif_sim_op:
            if selection==dif_op[0]:
                res=dif_sim(set_a_fu, set_b_fu)
                res_text="Diferencia simetrica A∆B = {0}".format(res)
                res_lable.config(text=res_text)
            elif selection==dif_op[1]:
                res=dif_sim(set_a_fu, set_c_fu)
                res_text="Diferencia simetrica A∆C = {0}".format(res)
                res_lable.config(text=res_text)
            elif selection==dif_op[2]:
                res=dif_sim(set_b_fu, set_c_fu)
                res_text="Diferencia simetrica B∆C = {0}".format(res)
                res_lable.config(text=res_text)
        elif selection in card:
            if selection==card[0]:
                res=cardinalidad(set_a_fu)
                res_text="Cardinalidad |A| = {0}".format(res)
                res_lable.config(text=res_text)
            elif selection==card[1]:
                res=cardinalidad(set_b_fu)
                res_text="Cardinalidad |B| = {0}".format(res)
                res_lable.config(text=res_text)
            elif selection==card[2]:
                res=cardinalidad(set_c_fu)
                res_text="Cardinalidad |C| = {0}".format(res)
                res_lable.config(text=res_text)
        else:
            res_lable.config(text="!Error!")
    except:
        res_lable.config(text="!Error!")
##========Up MENU==========================================
mnu=Frame(ventana, width=950, height=150, background="grey")
mnu.pack(side="top")
etiqueta1=Label(mnu, text="MENU", font="Helvetica 20")
etiqueta1.place(x=20, y=20)
boton_info=Button(mnu, text="INFO", height=2, width=8, 
    command=lambda:[t_t_m.place_forget(),frame_tt.place_forget(),sets_frame.place_forget(),info.place(x=50, y=240)])
boton_info.place(x=20,y=55)
boton_ttm=Button(mnu, text="Tablas De Verdad", height=2, width=15, 
    command=lambda: [info.place_forget(),sets_frame.place_forget(),t_t_m.place(x=50, y=180),frame_tt.place(x=50, y=300)])
boton_ttm.place(x=150,y=55)
boton_sets=Button(mnu, text="Conjuntos", height=2, width=10, 
    command=lambda:[info.place_forget(), t_t_m.place_forget(), sets_frame.place(x=50, y=180)])
boton_sets.place(x=340, y=55)


## ========== INFO ==========================================
info=Frame(ventana, width=760, height=500, background="Black")
info.place(x=20, y=180)
welcome=Label(info, text="Fundamentos de ciencias computacionales\n ToolKit", font="Arial 35 bold", )
welcome.pack(side="top")


#=============Truth table generator section==================
t_t_m=Frame(ventana, width=760, height=120, background="grey")
etiqueta_exp=Label(t_t_m, text="Pon tu proposición", font="Helvetica 20",background="grey")
etiqueta_exp.pack(side="left",)
exp_entry=Entry(t_t_m, width=35)
exp_entry.pack(side="left")
boton_ttm=Button(t_t_m, text="Generar TT", height=1, width=10, command=lambda: [get_prop(), ])
boton_ttm.pack(side="left")
        # Available operands for user to see
rules_tt=Label(t_t_m,text="Operadores: \n•And- ^\n•Or- v\n•Xor- +\n•Implicación- →\n•Bicondicional- ↔")
rules_tt.pack(side="right",anchor=NW)
        #Placement of truth table on screen
frame_tt=Frame(ventana,width=760, height=300, background="grey")
truth_table=Label(frame_tt)
truth_table.pack(fill="x", expand=True,anchor=NW)

#========Sets=============================
sets_frame=Frame(ventana, width=760, height=400, background="grey")

tag_sets=Label(sets_frame, text="Conjuntos", font="Helvetica 20")
tag_sets.place(x=0, y=0)
seta_label=Label(sets_frame, text="A={")
seta_label.place(x=10,y=40)
setb_label=Label(sets_frame, text="B={")
setb_label.place(x=10,y=80)
setc_label=Label(sets_frame, text="C={")
setc_label.place(x=10,y=120)
    ## ===ENTRY FOR SETS OF USER=== ##
sets_a=Entry(sets_frame, width=25)
sets_a.place(x=40, y=40)
sets_b=Entry(sets_frame, width=25)
sets_b.place(x=40, y=80)
sets_c=Entry(sets_frame, width=25)
sets_c.place(x=40, y=120)

#=====Operaciones Disponibles=====================#
tag_operator=Label(sets_frame, text="Operadores", font="Helvetica 20")
tag_operator.place(x=0, y=160)
operators=["Union", "Interseccion", "Diferencia", "Diferencia simetrica", "Cardinalidad"]
op_selec=ttk.Combobox(sets_frame,
    state="",
    values=operators)
op_selec.current(0)
op_selec.place(x=150, y=160)
bot_act=Button(sets_frame, text="Guardar", command=lambda:[update_options(op_selec.get())])
bot_act.place(x=370, y=160)

#====Opciones=====================================
tag_options=Label(sets_frame, text="Operaciones", font="Helvetica 20")
tag_options.place(x=0, y=200)


selec_option=ttk.Combobox(sets_frame)
selec_option.place(x=150, y=200)

##=====Calcular resultado============
res_buttton= Button(sets_frame, text="Calcular resultado", command=lambda:[calculate_result()])
res_buttton.place(x=370, y=200)
#sets_frame.after(1000,print("Hola"))
#update_options(op_selec.get())
#op_selec.bind("<<ComoboxSelected>>", update_options(op_selec.get()))    
#=======Show result==================
res_lable=Label(sets_frame, text="Result is shown here")
res_lable.place(x=0, y=240)
#========Main loop
ventana.mainloop()