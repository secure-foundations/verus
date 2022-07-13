pub const QUERY: &str = "%%query%%";
pub const PREFIX_LABEL: &str = "%%location_label%%";
pub const GLOBAL_PREFIX_LABEL: &str = "%%global_location_label%%";
pub const SWITCH_LABEL: &str = "%%switch_label%%";
pub const FUNCTION: &str = "%%Function%%";
pub const LAMBDA: &str = "%%lambda%%";
pub const CHOOSE: &str = "%%choose%%";
pub const HOLE: &str = "%%hole%%";
pub const APPLY: &str = "%%apply%%";
pub const SKOLEM_ID_PREFIX: &str = "skolem";

pub fn mk_skolem_id(qid: &str) -> String {
    format!("{}_{}", crate::def::SKOLEM_ID_PREFIX, qid)
}
