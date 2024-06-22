

	# 1.- Definir Conjuntos
	# 2.- Definir Variables de Decisión
	# 3.- Definir Parámetros
	# 4.- Establecer Función Objetivo
	# 5.- Definir Restricciones
			
			# DEFINIR CONJUNTOS



param CantidadProductos;
param CantidadSucursales;
param CantidadVehiculos;
param DiasDeLaSemana;
		
	# Para definir los conjuntos, necesito decirle a el ampl que corresponde, se le asigna una letra a cada set para recorrer en cada caso
set Productos := 1..CantidadProductos;						# i -> Productos
set Sucursales := 1..CantidadSucursales;					# j -> Sucursales
set SucursalesSubset := 2..CantidadSucursales;				# k -> SucursalesSubset
set Vehiculos := 1..CantidadVehiculos;						# l -> Vehiculos
set Dias := 1..DiasDeLaSemana;								# m -> Dias

			# DEFINIR VARIABLES DE DECISION
			
	#Cantidad de producto P comprada en la semana.
var UnidadesCompradas{i in Productos} >= 0, integer;

	#Unidades de  producto P vendidas en determinada sucursal S el día d de la semana
var UnidadesVendidas{i in Productos, j in Sucursales, m in Dias} >= 0, integer;

	#Cantidad de producto P trasladada desde la sucursal matriz,
	#hacia determinada sucursal en determinado vehículo en el día d de la semana 
var MovimientosProductos{i in Productos, k in SucursalesSubset, l in Vehiculos, m in Dias} >= 0, integer;

	#Inventario al final de día d asociado al producto P en determinada sucursal
var InventarioFinal{i in Productos, j in Sucursales, m in Dias} >= 0, integer;

	#Cantidad de viajes realizados en día “d” en determinado vehículo V a cualquier sucursal, sin incluir “S1”
var CantidadViajes{k in SucursalesSubset, l in Vehiculos, m in Dias} >= 0, integer;

	#Variable para actualizar los días de entrega
var BinarioEntrega{i in Productos, m in Dias} binary;


			# DEFINIR PARÁMETROS 
			
	#Volumen de carga del vehículo "l" (litros)
param VolumenCargaVehiculo{l in Vehiculos};

	#Volumen asociado al producto “i” determinado (litros)
param VolumenProducto{i in Productos};

	#Stock máximo de producto “i” en la sucursal “j”
param StockMaximo{i in Productos, j in Sucursales};

	#Precio de compra unitario del producto “i”
param PrecioCompra{i in Productos};

	#Precio de venta del producto “i” en determinado local “j”
param PrecioVenta{i in Productos, j in Sucursales};

	#Costo de transporte en el vehículo “l” desde sucursal matriz hasta cualquier sucursal “k” considerar que no se considera la sucursal matriz
param CostoTransporte{k in SucursalesSubset, l in Vehiculos};

	#Día de entrega asociado al producto “i”
param DiaDeEntrega{i in Productos};

	#Demanda del producto “i” en cada sucursal “j” durante el día “m” determinado
param DemandaProductoSucursal{i in Productos, j in Sucursales, m in Dias};

	#Inventario inicial de producto “i” en la sucursal “j”
param InventarioInicialSucursal{i in Productos, j in Sucursales};

			# ESTABLECER FUNCION OBJETIVO
			
maximize Z: sum{i in Productos, j in Sucursales, m in Dias} PrecioVenta[i,j]*UnidadesVendidas[i,j,m] - sum{i in Productos} PrecioCompra[i]*UnidadesCompradas[i] - sum{k in SucursalesSubset, l in Vehiculos, m in Dias}CostoTransporte[k,l]*CantidadViajes[k,l,m];
			
			# ESTABLECER RESTRICCIONES
			
	# (1) RESTRICCION VARIABLE BINARIA BINARIOENTREGA
s.t. RestriccionBinarioEntrega{i in Productos, m in Dias}:
 	BinarioEntrega[i,m] = if m = DiaDeEntrega[i] then 1 else 0;

	# (2) RESTRICCION DE VIAJES CON BALANCE DE LAS CARGAS
s.t. RestriccionViajesCargas{k in SucursalesSubset, l in Vehiculos, m in Dias}:
    sum{i in Productos} MovimientosProductos[i,k,l,m] * VolumenProducto[i] <= CantidadViajes[k,l,m] * VolumenCargaVehiculo[l];

	# (3) RESTRICCION NIVELES DE INVENTARIO PARA CADA SUCURSAL 
s.t. RestriccionInventario{i in Productos, j in Sucursales, m in Dias}:
	InventarioFinal[i,j,m] <= StockMaximo[i,j];

	# (4)(3.1.1) Inventario en la sucursal S1, para el primer día de la semana
s.t. RestriccionInventarioS1D1{i in Productos}: 
	InventarioInicialSucursal[i,1] + UnidadesCompradas[i] * BinarioEntrega[i,1] - UnidadesVendidas[i,1,1] - sum{k in SucursalesSubset, l in Vehiculos} MovimientosProductos[i,k,l,1] = InventarioFinal[i,1,1];
			
	# (5)(3.1.2) Inventario en la sucursal S1, para “cualquier” día de la semana 
s.t. RestriccionInventarioS1Dn{i in Productos, m in Dias: m > 1}:
    InventarioFinal[i,1,m-1] + UnidadesCompradas[i] * BinarioEntrega[i,m] - UnidadesVendidas[i,1,m] - sum{k in SucursalesSubset, l in Vehiculos} MovimientosProductos[i,k,l,m] = InventarioFinal[i,1,m];

	# (6)(3.2.1) RESTRICCION DE INVENTARIO EN LA SUCURSAL SN PARA EL PRIMER DIA DE LA SEMANA 
s.t. RestriccionInventarioSnD1{i in Productos, k in SucursalesSubset}:
    InventarioInicialSucursal[i,k] + sum{l in Vehiculos} MovimientosProductos[i,k,l,1] - UnidadesVendidas[i,k,1] = InventarioFinal[i,k,1];
		
	# (7)(3.2.2) RESTRICCION DE INVENTARIO EN LA SUCURSAL SN PARA CUALQUIER DIA N DISTINTO DE 1
s.t. RestriccionInventarioSnDn{i in Productos, k in SucursalesSubset, m in Dias: m > 1}:
    InventarioFinal[i,k,m-1] + sum{l in Vehiculos} MovimientosProductos[i,k,l,m] - UnidadesVendidas[i,k,m] = InventarioFinal[i,k,m];

	# (8)(4) RESTRICCION DE VENTAS 
s.t. RestriccionVentas{i in Productos, j in Sucursales, m in Dias}:
	 UnidadesVendidas[i,j,m] <= DemandaProductoSucursal[i,j,m];
