import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7320 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7320 = true := by
  decide +kernel

theorem tot7320 : totK PA10K2 A10K2.t7320 = [0, 0, 0, 288457583395, 1547271869755, 2087030456591, 597051281257, 38148714322, 0, 0] := by
  decide +kernel

theorem rows7321 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7321 = true := by
  decide +kernel

theorem tot7321 : totK PA10K2 A10K2.t7321 = [0, 0, 310758541238, 900367915762, 1024153216579, 1343799011676, 899938354059, 161289734307, 5976421810, 0] := by
  decide +kernel

theorem rows7322 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7322 = true := by
  decide +kernel

theorem tot7322 : totK PA10K2 A10K2.t7322 = [0, 0, 499725545621, 1870526448683, 1978193855906, 541647335361, 31989350221, 0, 0, 0] := by
  decide +kernel

theorem rows7323 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7323 = true := by
  decide +kernel

theorem tot7323 : totK PA10K2 A10K2.t7323 = [0, 0, 0, 645716181936, 2070859714536, 1757617152749, 403728266853, 25351274858, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
