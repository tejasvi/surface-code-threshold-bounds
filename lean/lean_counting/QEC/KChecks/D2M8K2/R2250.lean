import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9000 = true := by
  decide +kernel

theorem tot9000 : totK PD2M8K2 D2M8K2.t9000 = [0, 12164753440, 316379988260, 498429174868, 58465621005, 0, 0, 0] := by
  decide +kernel

theorem rows9001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9001 = true := by
  decide +kernel

theorem tot9001 : totK PD2M8K2 D2M8K2.t9001 = [0, 169904179757, 438938862355, 271844947558, 28125932957, 0, 0, 0] := by
  decide +kernel

theorem rows9002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9002 = true := by
  decide +kernel

theorem tot9002 : totK PD2M8K2 D2M8K2.t9002 = [0, 216335811501, 493246293773, 205726199011, 8124058999, 0, 0, 0] := by
  decide +kernel

theorem rows9003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9003 = true := by
  decide +kernel

theorem tot9003 : totK PD2M8K2 D2M8K2.t9003 = [0, 183676772963, 476014777082, 228514894016, 14800781026, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
