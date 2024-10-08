#[cfg(target_os = "linux")]
pub mod linux_pmemfile_t;
#[cfg(target_os = "windows")]
pub mod windows_pmemfile_t;
pub mod pmemmock_t;
pub mod pmemspec_t;
pub mod pmemspec2_t;
pub mod pmemutil_v;
pub mod pmcopy_t;
pub mod subregion_v;
pub mod wrpm_v;
pub mod crc_t;
pub mod traits_t;
pub mod frac_v;
pub mod pmemadapt_v;
pub mod pmem_prophspec_v;
// pub mod pmem_prophwrap_v;
