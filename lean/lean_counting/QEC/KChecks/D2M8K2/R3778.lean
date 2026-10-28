import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15112 = true := by
  decide +kernel

theorem tot15112 : totK PD2M8K2 D2M8K2.t15112 = [0, 201609230526, 455022612431, 213896126280, 17094477172, 0, 0, 0] := by
  decide +kernel

theorem rows15113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15113 = true := by
  decide +kernel

theorem tot15113 : totK PD2M8K2 D2M8K2.t15113 = [0, 19168557488, 323756367706, 460865134615, 80405806220, 1096505104, 0, 0] := by
  decide +kernel

theorem rows15114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15114 = true := by
  decide +kernel

theorem tot15114 : totK PD2M8K2 D2M8K2.t15114 = [0, 85548550316, 312090191895, 378357168579, 100947113914, 3884009855, 0, 0] := by
  decide +kernel

theorem rows15115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15115 = true := by
  decide +kernel

theorem tot15115 : totK PD2M8K2 D2M8K2.t15115 = [0, 170091064845, 464866276976, 267946983067, 21773147364, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
