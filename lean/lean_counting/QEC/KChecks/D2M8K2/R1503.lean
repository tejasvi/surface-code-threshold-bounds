import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6012 = true := by
  decide +kernel

theorem tot6012 : totK PD2M8K2 D2M8K2.t6012 = [0, 193620096319, 476570245749, 224373327733, 13650779217, 0, 0, 0] := by
  decide +kernel

theorem rows6013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6013 = true := by
  decide +kernel

theorem tot6013 : totK PD2M8K2 D2M8K2.t6013 = [0, 19689835847, 303393134021, 463428722204, 104338010803, 1232398321, 0, 0] := by
  decide +kernel

theorem rows6014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6014 = true := by
  decide +kernel

theorem tot6014 : totK PD2M8K2 D2M8K2.t6014 = [0, 0, 215144900817, 496676010808, 170880273528, 4990385724, 0, 0] := by
  decide +kernel

theorem rows6015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6015 = true := by
  decide +kernel

theorem tot6015 : totK PD2M8K2 D2M8K2.t6015 = [0, 0, 189323744255, 471504640696, 205343421224, 12947917294, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
