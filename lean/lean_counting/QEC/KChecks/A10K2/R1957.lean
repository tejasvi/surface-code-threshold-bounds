import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7828 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7828 = true := by
  decide +kernel

theorem tot7828 : totK PA10K2 A10K2.t7828 = [0, 0, 327737319032, 1528840315703, 2189216338090, 883759786963, 71412904379, 0, 0, 0] := by
  decide +kernel

theorem rows7829 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7829 = true := by
  decide +kernel

theorem tot7829 : totK PA10K2 A10K2.t7829 = [0, 0, 0, 552154647753, 2024361309088, 2012733456364, 442627288267, 13231026584, 0, 0] := by
  decide +kernel

theorem rows7830 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7830 = true := by
  decide +kernel

theorem tot7830 : totK PA10K2 A10K2.t7830 = [0, 320479959089, 1066052707069, 1072320178200, 891159266821, 1093566815368, 507418605586, 49137536365, 0, 0] := by
  decide +kernel

theorem rows7831 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7831 = true := by
  decide +kernel

theorem tot7831 : totK PA10K2 A10K2.t7831 = [0, 529396659332, 1863308256061, 1873741099127, 485440716441, 17689376838, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
