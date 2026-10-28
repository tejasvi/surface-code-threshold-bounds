import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3944 = true := by
  decide +kernel

theorem tot3944 : totK PD2M8K2 D2M8K2.t3944 = [0, 0, 196396953860, 484840182111, 204312889750, 9352330548, 0, 0] := by
  decide +kernel

theorem rows3945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3945 = true := by
  decide +kernel

theorem tot3945 : totK PD2M8K2 D2M8K2.t3945 = [0, 150840131194, 360674802947, 234960801129, 117418168027, 13566920432, 0, 0] := by
  decide +kernel

theorem rows3946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3946 = true := by
  decide +kernel

theorem tot3946 : totK PD2M8K2 D2M8K2.t3946 = [0, 208588251881, 467965598869, 209836030808, 12430109507, 0, 0, 0] := by
  decide +kernel

theorem rows3947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3947 = true := by
  decide +kernel

theorem tot3947 : totK PD2M8K2 D2M8K2.t3947 = [0, 19348689120, 305445014785, 462491227607, 94603964885, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
