import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1356 = true := by
  decide +kernel

theorem tot1356 : totK PD2M8K2 D2M8K2.t1356 = [0, 83082256588, 369120940907, 413921890789, 50023991111, 0, 0, 0] := by
  decide +kernel

theorem rows1357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1357 = true := by
  decide +kernel

theorem tot1357 : totK PD2M8K2 D2M8K2.t1357 = [0, 159496736719, 464179865532, 255031540971, 20600643016, 0, 0, 0] := by
  decide +kernel

theorem rows1358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1358 = true := by
  decide +kernel

theorem tot1358 : totK PD2M8K2 D2M8K2.t1358 = [0, 166010054258, 454450262192, 249408944049, 16111946720, 0, 0, 0] := by
  decide +kernel

theorem rows1359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1359 = true := by
  decide +kernel

theorem tot1359 : totK PD2M8K2 D2M8K2.t1359 = [0, 0, 262895869841, 506236908033, 122029847862, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
