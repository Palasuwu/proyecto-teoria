import re
import graphviz
from collections import deque, defaultdict
from itertools import product

class Estado:
    _contador = 0
    
    def __init__(self, es_aceptacion=False):
        self.id = Estado._contador
        Estado._contador += 1
        self.es_aceptacion = es_aceptacion
        self.transiciones = {}  # símbolo -> conjunto de estados
    
    def agregar_transicion(self, simbolo, estado):
        if simbolo not in self.transiciones:
            self.transiciones[simbolo] = set()
        self.transiciones[simbolo].add(estado)
    
    def __repr__(self):
        return f"q{self.id}" + ("(acept)" if self.es_aceptacion else "")

class AFN:
    def __init__(self, inicio, aceptacion):
        self.inicio = inicio
        self.aceptacion = aceptacion  # Ahora es un conjunto de estados
        self.estados = set()
        self.alfabeto = set()
        self._recolectar_estados_y_alfabeto()
    
    def _recolectar_estados_y_alfabeto(self):
        visitados = set()
        pila = [self.inicio]
        
        while pila:
            estado = pila.pop()
            if estado.id in visitados:
                continue
                
            visitados.add(estado.id)
            self.estados.add(estado)
            
            for simbolo, destinos in estado.transiciones.items():
                if simbolo != 'ε':
                    self.alfabeto.add(simbolo)
                for destino in destinos:
                    if destino.id not in visitados:
                        pila.append(destino)
    
    def cerradura_epsilon(self, estados):
        pila = list(estados)
        resultado = set(estados)
        
        while pila:
            estado = pila.pop()
            if 'ε' in estado.transiciones:
                for destino in estado.transiciones['ε']:
                    if destino not in resultado:
                        resultado.add(destino)
                        pila.append(destino)
        
        return resultado
    
    def mover(self, estados, simbolo):
        resultado = set()
        for estado in estados:
            if simbolo in estado.transiciones:
                resultado.update(estado.transiciones[simbolo])
        return resultado
    
    def simular(self, cadena):
        actual = self.cerradura_epsilon({self.inicio})
        
        for simbolo in cadena:
            actual = self.cerradura_epsilon(self.mover(actual, simbolo))
        
        return any(estado.es_aceptacion for estado in actual)
    
    def to_dot(self, nombre="AFN"):
        dot = graphviz.Digraph(nombre, format='png')
        dot.attr(rankdir='LR')
        
        # Estado inicial
        dot.node('start', '', shape='point', width='0')
        dot.edge('start', str(self.inicio.id))
        
        # Estados
        for estado in self.estados:
            shape = 'doublecircle' if estado.es_aceptacion else 'circle'
            dot.node(str(estado.id), str(estado.id), shape=shape)
        
        # Transiciones
        for estado in self.estados:
            for simbolo, destinos in estado.transiciones.items():
                for destino in destinos:
                    dot.edge(str(estado.id), str(destino.id), label=simbolo)
        
        return dot

class AFD:
    def __init__(self, estados, inicio, aceptacion, transiciones, alfabeto):
        self.estados = estados
        self.inicio = inicio
        self.aceptacion = aceptacion
        self.transiciones = transiciones  # (estado, simbolo) -> estado
        self.alfabeto = alfabeto
    
    def simular(self, cadena):
        actual = self.inicio
        for simbolo in cadena:
            if (actual, simbolo) not in self.transiciones:
                return False
            actual = self.transiciones[(actual, simbolo)]
        return actual in self.aceptacion
    
    def to_dot(self, nombre="AFD"):
        dot = graphviz.Digraph(nombre, format='png')
        dot.attr(rankdir='LR')
        
        # Estado inicial
        dot.node('start', '', shape='point', width='0')
        dot.edge('start', str(self.inicio))
        
        # Estados
        for estado in self.estados:
            shape = 'doublecircle' if estado in self.aceptacion else 'circle'
            dot.node(str(estado), str(estado), shape=shape)
        
        # Transiciones
        for (origen, simbolo), destino in self.transiciones.items():
            dot.edge(str(origen), str(destino), label=simbolo)
        
        return dot

def insertar_concatenacion(expresion):
    simbolos = list(expresion)
    resultado = []
    
    for i in range(len(simbolos) - 1):
        resultado.append(simbolos[i])
        
        # Reglas para insertar el operador de concatenación (.)
        actual = simbolos[i]
        siguiente = simbolos[i + 1]
        
        cond1 = actual not in ['|', '(']  # Actual no es | o (
        cond2 = siguiente not in ['|', '*', ')', '+', '?']  # Siguiente no es |, *, ), +, ?
        cond3 = actual != 'ε' and siguiente != 'ε'  # Ninguno es epsilon
        
        if cond1 and cond2 and cond3:
            resultado.append('.')
    
    resultado.append(simbolos[-1])
    return ''.join(resultado)

def shunting_yard(expresion):
    precedencia = {
        '|': 1,
        '.': 2,
        '*': 3,
        '+': 3,
        '?': 3
    }
    
    operadores = set(['|', '.', '*', '+', '?'])
    output = []
    pila = []
    
    i = 0
    while i < len(expresion):
        c = expresion[i]
        
        if c == '\\':  # Carácter de escape
            if i + 1 < len(expresion):
                output.append(expresion[i+1])
                i += 2
                continue
            else:
                i += 1
                continue
        
        if c == '(':
            pila.append(c)
        elif c == ')':
            while pila and pila[-1] != '(':
                output.append(pila.pop())
            if pila and pila[-1] == '(':
                pila.pop()  # Eliminar el '('
        elif c in operadores:
            while (pila and pila[-1] in operadores and 
                   precedencia[pila[-1]] >= precedencia[c]):
                output.append(pila.pop())
            pila.append(c)
        else:
            output.append(c)
        
        i += 1
    
    while pila:
        output.append(pila.pop())
    
    return ''.join(output)

def thompson(postfix):
    pila = []
    
    for c in postfix:
        if c == '.':
            afn2 = pila.pop()
            afn1 = pila.pop()
            
            # Conectar el estado de aceptación de afn1 al inicio de afn2
            for estado_aceptacion in afn1.aceptacion:
                estado_aceptacion.es_aceptacion = False
                estado_aceptacion.agregar_transicion('ε', afn2.inicio)
            
            pila.append(AFN(afn1.inicio, afn2.aceptacion))
            
        elif c == '|':
            afn2 = pila.pop()
            afn1 = pila.pop()
            
            # Crear nuevo estado inicial y de aceptación
            inicio = Estado()
            aceptacion = Estado(True)
            
            # Conectar nuevo inicio a los inicios de afn1 y afn2
            inicio.agregar_transicion('ε', afn1.inicio)
            inicio.agregar_transicion('ε', afn2.inicio)
            
            # Conectar estados de aceptación de afn1 y afn2 al nuevo estado de aceptación
            for estado_aceptacion in afn1.aceptacion:
                estado_aceptacion.es_aceptacion = False
                estado_aceptacion.agregar_transicion('ε', aceptacion)
            
            for estado_aceptacion in afn2.aceptacion:
                estado_aceptacion.es_aceptacion = False
                estado_aceptacion.agregar_transicion('ε', aceptacion)
            
            pila.append(AFN(inicio, {aceptacion}))
            
        elif c == '*':
            afn = pila.pop()
            
            # Crear nuevo estado inicial y de aceptación
            inicio = Estado()
            aceptacion = Estado(True)
            
            # Conectar nuevo inicio al inicio del AFN y al nuevo estado de aceptación
            inicio.agregar_transicion('ε', afn.inicio)
            inicio.agregar_transicion('ε', aceptacion)
            
            # Conectar estados de aceptación al inicio del AFN y al nuevo estado de aceptación
            for estado_aceptacion in afn.aceptacion:
                estado_aceptacion.es_aceptacion = False
                estado_aceptacion.agregar_transicion('ε', afn.inicio)
                estado_aceptacion.agregar_transicion('ε', aceptacion)
            
            pila.append(AFN(inicio, {aceptacion}))
            
        else:
            # Símbolo básico
            inicio = Estado()
            aceptacion = Estado(True)
            inicio.agregar_transicion(c, aceptacion)
            pila.append(AFN(inicio, {aceptacion}))
    
    return pila.pop()

def subconjuntos(afn):
    # Inicialización
    estado_inicial = frozenset(e.id for e in afn.cerradura_epsilon({afn.inicio}))
    por_visitar = deque([estado_inicial])
    visitados = set([estado_inicial])
    
    # Mapeo de conjuntos de estados a IDs de AFD
    estados_afd = {}
    transiciones_afd = {}
    estados_aceptacion_afd = set()
    
    # Alfabeto del AFN (sin epsilon)
    alfabeto = afn.alfabeto
    
    # Convertir IDs a estados reales
    id_a_estado = {estado.id: estado for estado in afn.estados}
    
    while por_visitar:
        conjunto_actual = por_visitar.popleft()
        estados_afd[conjunto_actual] = conjunto_actual
        
        # Verificar si es estado de aceptación
        if any(id_a_estado[id_estado].es_aceptacion for id_estado in conjunto_actual):
            estados_aceptacion_afd.add(conjunto_actual)
        
        for simbolo in alfabeto:
            # Mover y aplicar cerradura epsilon
            movidos = set()
            for id_estado in conjunto_actual:
                estado = id_a_estado[id_estado]
                if simbolo in estado.transiciones:
                    for destino in estado.transiciones[simbolo]:
                        movidos.add(destino.id)
            
            if movidos:
                conjunto_destino = frozenset(e.id for e in afn.cerradura_epsilon(
                    {id_a_estado[id_] for id_ in movidos}))
                
                transiciones_afd[(conjunto_actual, simbolo)] = conjunto_destino
                
                if conjunto_destino not in visitados:
                    visitados.add(conjunto_destino)
                    por_visitar.append(conjunto_destino)
    
    # Simplificar nombres de estados
    estado_id_map = {estado: i for i, estado in enumerate(estados_afd.keys())}
    inicio_afd = estado_id_map[estado_inicial]
    aceptacion_afd = {estado_id_map[estado] for estado in estados_aceptacion_afd}
    estados_afd_simplificados = set(estado_id_map.values())
    
    transiciones_simplificadas = {}
    for (origen, simbolo), destino in transiciones_afd.items():
        transiciones_simplificadas[(estado_id_map[origen], simbolo)] = estado_id_map[destino]
    
    return AFD(estados_afd_simplificados, inicio_afd, aceptacion_afd, 
               transiciones_simplificadas, alfabeto)

def minimizar_afd(afd_original):
    # Implementación del algoritmo de minimización de Hopcroft
    if not afd_original.aceptacion:
        # Si no hay estados de aceptación, el AFD mínimo tiene un solo estado
        nuevos_estados = {0}
        nuevo_inicio = 0
        nueva_aceptacion = set()
        nuevas_transiciones = {}
        
        return AFD(nuevos_estados, nuevo_inicio, nueva_aceptacion, 
                   nuevas_transiciones, afd_original.alfabeto)
    
    P = [set(afd_original.aceptacion), afd_original.estados - afd_original.aceptacion]
    W = [set(afd_original.aceptacion), afd_original.estados - afd_original.aceptacion]
    
    while W:
        A = W.pop(0)
        
        for c in afd_original.alfabeto:
            X = set()
            for estado in afd_original.estados:
                if (estado, c) in afd_original.transiciones and afd_original.transiciones[(estado, c)] in A:
                    X.add(estado)
            
            if not X:
                continue
                
            nuevas_particiones = []
            for Y in P:
                interseccion = Y & X
                diferencia = Y - X
                
                if interseccion and diferencia:
                    nuevas_particiones.append(interseccion)
                    nuevas_particiones.append(diferencia)
                    
                    if Y in W:
                        W.remove(Y)
                        W.append(interseccion)
                        W.append(diferencia)
                    else:
                        if len(interseccion) <= len(diferencia):
                            W.append(interseccion)
                        else:
                            W.append(diferencia)
                else:
                    nuevas_particiones.append(Y)
            
            P = nuevas_particiones
    
    # Crear nuevo AFD minimizado
    estado_a_grupo = {}
    for i, grupo in enumerate(P):
        for estado in grupo:
            estado_a_grupo[estado] = i
    
    nuevos_estados = set(range(len(P)))
    nuevo_inicio = estado_a_grupo[afd_original.inicio]
    nueva_aceptacion = set()
    
    for estado in afd_original.aceptacion:
        nueva_aceptacion.add(estado_a_grupo[estado])
    
    nuevas_transiciones = {}
    for (origen, simbolo), destino in afd_original.transiciones.items():
        nuevo_origen = estado_a_grupo[origen]
        nuevo_destino = estado_a_grupo[destino]
        nuevas_transiciones[(nuevo_origen, simbolo)] = nuevo_destino
    
    return AFD(nuevos_estados, nuevo_inicio, nueva_aceptacion, nuevas_transiciones, afd_original.alfabeto)

def procesar_expresion(expresion, cadena, nombre_archivo=None):
    # Resetear contador de estados
    Estado._contador = 0
    
    # Paso 1: Insertar operadores de concatenación
    exp_con_concatenacion = insertar_concatenacion(expresion)
    print(f"Expresión con concatenación: {exp_con_concatenacion}")
    
    # Paso 2: Convertir a postfix
    postfix = shunting_yard(exp_con_concatenacion)
    print(f"Notación postfix: {postfix}")
    
    # Paso 3: Construir AFN con Thompson
    try:
        afn = thompson(postfix)
        print("AFN construido")
        
        # Generar imagen del AFN
        dot_afn = afn.to_dot("AFN")
        if nombre_archivo:
            dot_afn.render(f"{nombre_archivo}_afn", cleanup=True)
            print(f"Imagen del AFN guardada como {nombre_archivo}_afn.png")
        
        # Paso 4: Convertir a AFD
        afd = subconjuntos(afn)
        print("AFD construido")
        
        # Generar imagen del AFD
        dot_afd = afd.to_dot("AFD")
        if nombre_archivo:
            dot_afd.render(f"{nombre_archivo}_afd", cleanup=True)
            print(f"Imagen del AFD guardada como {nombre_archivo}_afd.png")
        
        # Paso 5: Minimizar AFD
        afd_min = minimizar_afd(afd)
        print("AFD minimizado")
        
        # Generar imagen del AFD minimizado
        dot_afd_min = afd_min.to_dot("AFD_min")
        if nombre_archivo:
            dot_afd_min.render(f"{nombre_archivo}_afd_min", cleanup=True)
            print(f"Imagen del AFD minimizado guardada como {nombre_archivo}_afd_min.png")
        
        # Simular cadena en todos los autómatas
        resultado_afn = "sí" if afn.simular(cadena) else "no"
        resultado_afd = "sí" if afd.simular(cadena) else "no"
        resultado_afd_min = "sí" if afd_min.simular(cadena) else "no"
        
        print(f"\nResultados para la cadena '{cadena}':")
        print(f"AFN: {resultado_afn}")
        print(f"AFD: {resultado_afd}")
        print(f"AFD minimizado: {resultado_afd_min}")
        
        return afn, afd, afd_min
        
    except Exception as e:
        print(f"Error al procesar la expresión: {e}")
        return None, None, None

def main():
    # Ejemplo de uso
    expresion = "(b|b)*abb(a|b)*"
    cadena = "babbaaaa"
    
    print("Procesando expresión regular:", expresion)
    print("Cadena a evaluar:", cadena)
    
    # Procesar la expresión regular
    afn, afd, afd_min = procesar_expresion(expresion, cadena, "ejemplo")
    
    # Leer desde archivo si se proporciona
    import sys
    if len(sys.argv) > 1:
        nombre_archivo = sys.argv[1]
        try:
            with open(nombre_archivo, 'r') as f:
                lineas = f.readlines()
            
            for i, linea in enumerate(lineas):
                partes = linea.strip().split(',')
                if len(partes) == 2:
                    exp, cad = partes
                    print(f"\nProcesando expresión {i+1}: {exp} con cadena: {cad}")
                    procesar_expresion(exp, cad, f"expresion_{i+1}")
        except FileNotFoundError:
            print(f"Archivo {nombre_archivo} no encontrado")
        except Exception as e:
            print(f"Error al leer el archivo: {e}")

if __name__ == "__main__":
    main()