import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12556 = true := by
  decide +kernel

theorem tot12556 : totK PD2M8K2 D2M8K2.t12556 = [0, 0, 89085137309, 405633924137, 366202341028, 39021537229, 0, 0] := by
  decide +kernel

theorem rows12557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12557 = true := by
  decide +kernel

theorem tot12557 : totK PD2M8K2 D2M8K2.t12557 = [0, 0, 175141769035, 474468224919, 243207802131, 14456253282, 0, 0] := by
  decide +kernel

theorem rows12558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12558 = true := by
  decide +kernel

theorem tot12558 : totK PD2M8K2 D2M8K2.t12558 = [0, 0, 216290471234, 498759675858, 184209820992, 5115562507, 0, 0] := by
  decide +kernel

theorem rows12559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12559 = true := by
  decide +kernel

theorem tot12559 : totK PD2M8K2 D2M8K2.t12559 = [0, 0, 186406802844, 460879103301, 247779649463, 18772323198, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
