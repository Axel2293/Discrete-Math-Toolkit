

from tkinter import NW, Button, Entry, Frame, Label, Tk
import re
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
    





ventana=Tk()

ventana.title("FCC TOOLKIT 2022")
ventana.iconbitmap("Tkinter.ico")
ventana.geometry("800x600")
ventana.config(bg="white")

exp=""
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


##========Up MENU==========================================
mnu=Frame(ventana, width=950, height=150, background="grey")
mnu.pack(side="top")
etiqueta1=Label(mnu, text="MENU", font="Helvetica 20")
etiqueta1.place(x=20, y=20)
boton_info=Button(mnu, text="INFO", height=2, width=8, command=lambda:[t_t_m.place_forget(),frame_tt.place_forget(),info.place(x=50, y=240)])
boton_info.place(x=20,y=55)
boton_ttm=Button(mnu, text="Tablas De Verdad", height=2, width=15, command=lambda: [info.place_forget(),t_t_m.place(x=50, y=180),frame_tt.place(x=50, y=300)])
boton_ttm.place(x=150,y=55)
boton_sets=Button(mnu, text="Conjuntos", height=2, width=10, command=lambda:["POR DEFINIR"])
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

#========Main loop
ventana.mainloop()