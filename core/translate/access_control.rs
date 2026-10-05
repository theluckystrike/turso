//! Bytecode for role statements, and the privilege checks that run when a
//! statement is prepared.
//!
//! Privileges are checked when a statement is prepared, against the role that
//! is current at that time. Changing the role makes prepared statements
//! prepare again, so a statement always runs with the privileges of the
//! current role.
//!
//! Ownership and `GRANT` do not exist yet, so a role that is not a superuser
//! has no privileges on any database object. It may still run statements that
//! touch no database object, such as `SELECT 1`, and switch roles.

use std::sync::Arc;

use turso_ext::VTabKind;
use turso_parser::ast;

use crate::access_control::{CREATE_ROLES_TABLE_SQL, ROLES_TABLE_NAME};
use crate::schema::{BTreeTable, Schema, SEQ_BACKING_TABLE_PREFIX};
use crate::storage::pager::CreateBTreeFlags;
use crate::translate::emitter::Resolver;
use crate::translate::schema::{emit_schema_entry, SchemaEntryType, SQLITE_TABLEID};
use crate::vdbe::builder::{CursorType, ProgramBuilder};
use crate::vdbe::insn::{to_u32, Cookie, InsertFlags, Insn, RegisterOrLiteral};
use crate::vtab::VirtualTableType;
use crate::{bail_parse_error, Connection, LimboError, Result, MAIN_DB_ID};

/// Fails if the current role may not run `stmt` at all. Statements that pass
/// are checked again by [`check_storage_access`] once they are compiled.
pub fn check_statement_privileges(
    stmt: &ast::Stmt,
    resolver: &Resolver,
    connection: &Connection,
) -> Result<()> {
    if resolver
        .schema()
        .roles
        .is_superuser(connection.current_role())
    {
        return Ok(());
    }
    let denial = match stmt {
        ast::Stmt::Select(_)
        | ast::Stmt::Insert { .. }
        | ast::Stmt::Update(_)
        | ast::Stmt::Delete { .. }
        | ast::Stmt::Begin { .. }
        | ast::Stmt::Commit { .. }
        | ast::Stmt::Rollback { .. }
        | ast::Stmt::Savepoint { .. }
        | ast::Stmt::Release { .. }
        | ast::Stmt::SetRole { .. } => return Ok(()),
        ast::Stmt::CreateTable {
            temporary: true, ..
        }
        | ast::Stmt::CreateView {
            temporary: true, ..
        }
        | ast::Stmt::CreateTrigger {
            temporary: true, ..
        } => "permission denied to create temporary objects".to_string(),
        ast::Stmt::CreateTable { tbl_name, .. } => schema_denial(tbl_name),
        ast::Stmt::CreateView { view_name, .. }
        | ast::Stmt::CreateMaterializedView { view_name, .. } => schema_denial(view_name),
        ast::Stmt::CreateVirtualTable(create) => schema_denial(&create.tbl_name),
        ast::Stmt::CreateSequence { seq_name, .. } => schema_denial(seq_name),
        ast::Stmt::CreateType { .. } | ast::Stmt::CreateDomain { .. } => {
            "permission denied for schema public".to_string()
        }
        ast::Stmt::CreateIndex { tbl_name, .. } => {
            format!("must be owner of table {}", tbl_name.as_str())
        }
        ast::Stmt::CreateTrigger { tbl_name, .. } => {
            format!("permission denied for table {}", tbl_name.name.as_str())
        }
        ast::Stmt::AlterTable(alter) => {
            format!("must be owner of table {}", alter.name.name.as_str())
        }
        ast::Stmt::DropTable { tbl_name, .. } => {
            format!("must be owner of table {}", tbl_name.name.as_str())
        }
        ast::Stmt::DropIndex { idx_name, .. } => {
            format!("must be owner of index {}", idx_name.name.as_str())
        }
        ast::Stmt::DropView { view_name, .. } => {
            format!("must be owner of view {}", view_name.name.as_str())
        }
        ast::Stmt::DropTrigger { trigger_name, .. } => {
            format!("must be owner of trigger {}", trigger_name.name.as_str())
        }
        ast::Stmt::DropType { type_name, .. } => format!("must be owner of type {type_name}"),
        ast::Stmt::DropDomain { domain_name, .. } => {
            format!("must be owner of type {domain_name}")
        }
        ast::Stmt::DropSequence { seq_name, .. } => {
            format!("must be owner of sequence {}", seq_name.name.as_str())
        }
        ast::Stmt::CreateRole { .. } => "permission denied to create role".to_string(),
        ast::Stmt::Pragma {
            name,
            body: Some(_),
        } => format!(
            "permission denied to set parameter \"{}\"",
            name.name.as_str()
        ),
        ast::Stmt::Pragma { name, body: None } => {
            format!("permission denied to examine \"{}\"", name.name.as_str())
        }
        ast::Stmt::Analyze { .. } => "permission denied to run ANALYZE".to_string(),
        ast::Stmt::Vacuum { .. } => "permission denied to run VACUUM".to_string(),
        ast::Stmt::Reindex { .. } => "permission denied to run REINDEX".to_string(),
        ast::Stmt::Optimize { .. } => "permission denied to run OPTIMIZE".to_string(),
        ast::Stmt::Attach { .. } => "permission denied to attach a database".to_string(),
        ast::Stmt::Detach { .. } => "permission denied to detach a database".to_string(),
    };
    Err(LimboError::PermissionDenied(denial))
}

fn schema_denial(name: &ast::QualifiedName) -> String {
    let schema = match &name.db_name {
        Some(db_name) if db_name.as_str() != "main" => db_name.as_str(),
        _ => "public",
    };
    format!("permission denied for schema {schema}")
}

/// Fails if the compiled program reads or writes a database object that the
/// current role has no privileges on. Every access to stored data goes
/// through one of the instructions checked here, so a statement cannot reach
/// an object without being checked.
pub fn check_storage_access(
    program: &ProgramBuilder,
    resolver: &Resolver,
    connection: &Connection,
) -> Result<()> {
    if resolver
        .schema()
        .roles
        .is_superuser(connection.current_role())
    {
        return Ok(());
    }
    for (insn, _) in &program.insns {
        let (db, root_page) = match insn {
            Insn::OpenRead { db, root_page, .. } => (*db, Some(*root_page)),
            Insn::OpenWrite {
                db,
                root_page: RegisterOrLiteral::Literal(root_page),
                ..
            } => (*db, Some(*root_page)),
            Insn::OpenWrite { db, .. } => (*db, None),
            Insn::ClearBtree { db, root, .. } | Insn::Destroy { db, root, .. } => {
                (*db, Some(*root))
            }
            Insn::CreateBtree { db, .. } => (*db, None),
            _ => continue,
        };
        let object = root_page.and_then(|root_page| {
            resolver.with_schema(db, |schema| object_with_root_page(schema, root_page))
        });
        let denial = match object {
            Some(object) => format!("permission denied for {object}"),
            None => "permission denied to access database storage".to_string(),
        };
        return Err(LimboError::PermissionDenied(denial));
    }
    for virtual_table in &program.opened_virtual_tables {
        let created_by_user = virtual_table.kind == VTabKind::VirtualTable
            && matches!(virtual_table.vtab_type, VirtualTableType::External(_));
        if created_by_user {
            return Err(LimboError::PermissionDenied(format!(
                "permission denied for table {}",
                virtual_table.name
            )));
        }
    }
    Ok(())
}

/// Describes the object stored at `root_page` the way PostgreSQL names it in
/// a permission error, for example `table t` or `sequence s`. An index is
/// described by the table it belongs to.
fn object_with_root_page(schema: &Schema, root_page: i64) -> Option<String> {
    let table_name = schema
        .tables
        .values()
        .filter_map(|table| table.btree())
        .find(|table| table.root_page == root_page)
        .map(|table| table.name.clone())
        .or_else(|| {
            schema
                .indexes
                .values()
                .flatten()
                .find(|index| index.root_page == root_page)
                .map(|index| index.table_name.clone())
        })?;
    if let Some(sequence_name) = table_name.strip_prefix(SEQ_BACKING_TABLE_PREFIX) {
        return Some(format!("sequence {sequence_name}"));
    }
    if schema.materialized_view_names.contains(&table_name) {
        return Some(format!("materialized view {table_name}"));
    }
    Some(format!("table {table_name}"))
}

/// Switches the connection to `role_name`, or back to the session role when
/// `role_name` is `None`. The role is looked up when the statement runs.
pub fn translate_set_role(role_name: Option<String>, program: &mut ProgramBuilder) {
    program.emit_insn(Insn::SetRole { role_name });
}

/// Creates a role that is not a superuser and cannot log in.
pub fn translate_create_role(
    role_name: &str,
    resolver: &Resolver,
    program: &mut ProgramBuilder,
) -> Result<()> {
    if resolver.schema().roles.get_by_name(role_name).is_some() {
        bail_parse_error!("role \"{role_name}\" already exists");
    }
    let superuser = false;
    let can_login = false;

    let (roles_table, roles_root_page) = emit_roles_table_if_missing(resolver, program)?;
    let roles_cursor_id = program.alloc_cursor_id(CursorType::BTreeTable(roles_table));
    program.emit_insn(Insn::OpenWrite {
        cursor_id: roles_cursor_id,
        root_page: roles_root_page,
        db: MAIN_DB_ID,
    });

    let id_reg = program.alloc_register();
    program.emit_insn(Insn::NewRowid {
        cursor: roles_cursor_id,
        rowid_reg: id_reg,
        prev_largest_reg: 0,
    });
    let first_column_reg = program.alloc_registers(4);
    program.emit_insn(Insn::Null {
        dest: first_column_reg,
        dest_end: None,
    });
    program.emit_insn(Insn::String8 {
        value: role_name.to_string(),
        dest: first_column_reg + 1,
    });
    program.emit_insn(Insn::Integer {
        value: superuser as i64,
        dest: first_column_reg + 2,
    });
    program.emit_insn(Insn::Integer {
        value: can_login as i64,
        dest: first_column_reg + 3,
    });
    let record_reg = program.alloc_register();
    program.emit_insn(Insn::MakeRecord {
        start_reg: to_u32(first_column_reg),
        count: to_u32(4),
        dest_reg: to_u32(record_reg),
        index_name: None,
        affinity_str: None,
    });
    program.emit_insn(Insn::Insert {
        cursor: roles_cursor_id,
        key_reg: id_reg,
        record_reg,
        flag: InsertFlags::new(),
        table_name: ROLES_TABLE_NAME.to_string(),
    });

    program.emit_insn(Insn::AddRole {
        db: MAIN_DB_ID,
        id_reg,
        name: role_name.to_string(),
        superuser,
        can_login,
    });
    program.emit_insn(Insn::SetCookie {
        db: MAIN_DB_ID,
        cookie: Cookie::SchemaVersion,
        value: (resolver.schema().schema_version + 1) as i32,
        p5: 0,
    });
    Ok(())
}

/// Returns the roles table and its root page. If the table does not exist
/// yet, emits bytecode that creates it and returns the register that will
/// hold its root page.
fn emit_roles_table_if_missing(
    resolver: &Resolver,
    program: &mut ProgramBuilder,
) -> Result<(Arc<BTreeTable>, RegisterOrLiteral<i64>)> {
    if let Some(table) = resolver.schema().get_btree_table(ROLES_TABLE_NAME) {
        let root_page = RegisterOrLiteral::Literal(table.root_page);
        return Ok((table, root_page));
    }

    let root_page_reg = program.alloc_register();
    program.emit_insn(Insn::CreateBtree {
        db: MAIN_DB_ID,
        root: root_page_reg,
        flags: CreateBTreeFlags::new_table(),
    });

    let schema_table = resolver
        .schema()
        .get_btree_table(SQLITE_TABLEID)
        .expect("sqlite_schema always exists");
    let schema_cursor_id = program.alloc_cursor_id(CursorType::BTreeTable(schema_table));
    program.emit_insn(Insn::OpenWrite {
        cursor_id: schema_cursor_id,
        root_page: 1i64.into(),
        db: MAIN_DB_ID,
    });
    emit_schema_entry(
        program,
        resolver,
        schema_cursor_id,
        None,
        SchemaEntryType::Table,
        ROLES_TABLE_NAME,
        ROLES_TABLE_NAME,
        root_page_reg,
        Some(CREATE_ROLES_TABLE_SQL.to_string()),
    )?;
    program.emit_insn(Insn::ParseSchema {
        db: schema_cursor_id,
        where_clause: Some(format!(
            "tbl_name = '{ROLES_TABLE_NAME}' AND type != 'trigger'"
        )),
        trigger_target_database_id: None,
    });

    let table = Arc::new(BTreeTable::from_sql(CREATE_ROLES_TABLE_SQL, 0)?);
    Ok((table, RegisterOrLiteral::Register(root_page_reg)))
}
