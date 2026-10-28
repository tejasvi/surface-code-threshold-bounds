import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7368 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7368 = true := by
  decide +kernel

theorem tot7368 : totK PA10K2 A10K2.t7368 = [0, 0, 295757175837, 1387003134382, 2188690496949, 1137824340681, 114620669192, 0, 0, 0] := by
  decide +kernel

theorem rows7369 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7369 = true := by
  decide +kernel

theorem tot7369 : totK PA10K2 A10K2.t7369 = [0, 0, 0, 604153625925, 2099079790682, 1956492605403, 392978702597, 12746179907, 0, 0] := by
  decide +kernel

theorem rows7370 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7370 = true := by
  decide +kernel

theorem tot7370 : totK PA10K2 A10K2.t7370 = [0, 0, 0, 522156852047, 1837858716787, 1886270283031, 489158648489, 31222411477, 0, 0] := by
  decide +kernel

theorem rows7371 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7371 = true := by
  decide +kernel

theorem tot7371 : totK PA10K2 A10K2.t7371 = [0, 0, 0, 455603336605, 1862419634186, 2002282551244, 499459065426, 32505898269, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
