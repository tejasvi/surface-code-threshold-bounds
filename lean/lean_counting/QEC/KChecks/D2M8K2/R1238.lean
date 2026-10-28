import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4952 = true := by
  decide +kernel

theorem tot4952 : totK PD2M8K2 D2M8K2.t4952 = [0, 0, 190058073987, 467718462503, 200010509263, 12206147664, 0, 0] := by
  decide +kernel

theorem rows4953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4953 = true := by
  decide +kernel

theorem tot4953 : totK PD2M8K2 D2M8K2.t4953 = [0, 0, 53712551904, 351132478996, 389887150232, 67022542244, 1369150432, 0] := by
  decide +kernel

theorem rows4954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4954 = true := by
  decide +kernel

theorem tot4954 : totK PD2M8K2 D2M8K2.t4954 = [0, 0, 104219365349, 445524868694, 298854050338, 23722650738, 0, 0] := by
  decide +kernel

theorem rows4955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4955 = true := by
  decide +kernel

theorem tot4955 : totK PD2M8K2 D2M8K2.t4955 = [0, 0, 200487040935, 466584928193, 212588085431, 12552144954, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
