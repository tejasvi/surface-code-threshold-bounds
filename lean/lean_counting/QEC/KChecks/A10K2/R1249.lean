import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4996 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4996 = true := by
  decide +kernel

theorem tot4996 : totK PA10K2 A10K2.t4996 = [410741934011, 1728527587536, 2031325469773, 588825114354, 32846095359, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4997 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4997 = true := by
  decide +kernel

theorem tot4997 : totK PA10K2 A10K2.t4997 = [26834297668, 794730264641, 2015793973235, 1550194559278, 381622932687, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4998 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4998 = true := by
  decide +kernel

theorem tot4998 : totK PA10K2 A10K2.t4998 = [271188200059, 1123031738330, 1799014089191, 1315349564277, 234951272153, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4999 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4999 = true := by
  decide +kernel

theorem tot4999 : totK PA10K2 A10K2.t4999 = [583891508502, 1841041418285, 1817325107608, 534841270491, 31941609474, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
