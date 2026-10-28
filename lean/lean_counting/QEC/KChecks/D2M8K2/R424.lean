import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1696 = true := by
  decide +kernel

theorem tot1696 : totK PD2M8K2 D2M8K2.t1696 = [0, 0, 0, 192238871382, 474070820722, 207562268590, 14510083306, 0] := by
  decide +kernel

theorem rows1697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1697 = true := by
  decide +kernel

theorem tot1697 : totK PD2M8K2 D2M8K2.t1697 = [0, 0, 0, 169814734983, 461059796206, 218519175706, 16632994142, 0] := by
  decide +kernel

theorem rows1698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1698 = true := by
  decide +kernel

theorem tot1698 : totK PD2M8K2 D2M8K2.t1698 = [0, 0, 0, 85891556825, 373523685346, 337471320470, 63983811803, 1369150432] := by
  decide +kernel

theorem rows1699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1699 = true := by
  decide +kernel

theorem tot1699 : totK PD2M8K2 D2M8K2.t1699 = [0, 0, 0, 0, 320361908136, 448137896558, 75544887691, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
