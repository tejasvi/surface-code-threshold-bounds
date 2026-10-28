import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12004 = true := by
  decide +kernel

theorem tot12004 : totK PD2M8K2 D2M8K2.t12004 = [156254242361, 340059502157, 142337429789, 157276087376, 81046118049, 3882006667, 0, 0] := by
  decide +kernel

theorem rows12005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12005 = true := by
  decide +kernel

theorem tot12005 : totK PD2M8K2 D2M8K2.t12005 = [152530501726, 440783458219, 261336543279, 19250314998, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12006 = true := by
  decide +kernel

theorem tot12006 : totK PD2M8K2 D2M8K2.t12006 = [87574929976, 331953716424, 380771087231, 91498242848, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows12007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12007 = true := by
  decide +kernel

theorem tot12007 : totK PD2M8K2 D2M8K2.t12007 = [37755103912, 344160429529, 464342433011, 62143380295, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
