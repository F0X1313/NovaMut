# NovaMut — Sistema de gestión para mutuales

Aplicación de escritorio para administrar una mutual: socios, proveedores, compras en cuotas, cobros por descuento, liquidación mensual, reportes en PDF, credenciales y padrón para INAES.

Desarrollado por **Diego Alejandro Fernandez** y **Joshua Giuliano Venticinque**. La usa una mutual real en el día a día (versión 4.0).

## Tecnologías
- **Python 3** con **CustomTkinter** (interfaz gráfica)
- **SQLite** (base de datos local, con migraciones automáticas de esquema)
- **ReportLab** (reportes y credenciales en PDF)
- **PyInstaller** (ejecutable para Windows)

## Funcionalidades
- Alta, baja y modificación de socios y proveedores
- Compras en cuotas y cobros por descuento, con liquidación mensual
- Reportes y exportación a PDF y CSV
- Padrón para INAES
- Backups automáticos con rotación

## Seguridad
- Contraseñas con **PBKDF2-SHA256** (260.000 iteraciones y salt aleatorio por usuario)
- 4 roles con permisos por nivel: Superadmin, Admin, Operador, Consulta
- Bloqueo de la cuenta durante 15 minutos después de 5 intentos fallidos
- Cambio de clave obligatorio en el primer ingreso
- Registro de auditoría y de accesos

## Cómo ejecutarlo
```bash
pip install -r requirements.txt
python novamut.py
```
La primera vez crea una base vacía con el usuario `admin` / `admin` y pide cambiar la clave.

## Documentación
- [Manual de usuario](Manual%20de%20usuario%20de%20NovaMut.pdf)
- [Manual técnico](Manual%20t%C3%A9cnico%20de%20NovaMut.pdf)

> La base de datos y los backups no forman parte del repositorio porque contienen datos reales de la mutual.

## Licencia
El código está publicado como portfolio. Todos los derechos reservados por sus autores: no se permite usarlo, copiarlo ni distribuirlo sin autorización.
