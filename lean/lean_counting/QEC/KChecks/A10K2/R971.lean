import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3884 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3884 = true := by
  decide +kernel

theorem tot3884 : totK PA10K2 A10K2.t3884 = [0, 0, 476547934528, 1897218264388, 1989265666368, 458315675935, 26451220585, 0, 0, 0] := by
  decide +kernel

theorem rows3885 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3885 = true := by
  decide +kernel

theorem tot3885 : totK PA10K2 A10K2.t3885 = [0, 0, 480231640439, 1845919243684, 2085833762840, 665644945493, 31435538705, 0, 0, 0] := by
  decide +kernel

theorem rows3886 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3886 = true := by
  decide +kernel

theorem tot3886 : totK PA10K2 A10K2.t3886 = [0, 534634048466, 1823825274906, 1833183829879, 550750669674, 119132264590, 26048048901, 0, 0, 0] := by
  decide +kernel

theorem rows3887 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3887 = true := by
  decide +kernel

theorem tot3887 : totK PA10K2 A10K2.t3887 = [0, 238689799395, 1344612558619, 2198042494222, 1123074178531, 115875280511, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
