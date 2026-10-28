import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15772 = true := by
  decide +kernel

theorem tot15772 : totK PD2M8K2 D2M8K2.t15772 = [0, 0, 0, 217714023804, 495574761897, 164128699220, 7832068735, 0] := by
  decide +kernel

theorem rows15773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15773 = true := by
  decide +kernel

theorem tot15773 : totK PD2M8K2 D2M8K2.t15773 = [0, 0, 114819131042, 407247442229, 337862821816, 44486662326, 0, 0] := by
  decide +kernel

theorem rows15774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15774 = true := by
  decide +kernel

theorem tot15774 : totK PD2M8K2 D2M8K2.t15774 = [0, 0, 182413165824, 454752784063, 264811197345, 24819151869, 0, 0] := by
  decide +kernel

theorem rows15775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15775 = true := by
  decide +kernel

theorem tot15775 : totK PD2M8K2 D2M8K2.t15775 = [0, 0, 42131582902, 336580759928, 442722307907, 83365663903, 1198073392, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
