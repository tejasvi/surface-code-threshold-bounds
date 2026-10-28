import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4236 = true := by
  decide +kernel

theorem tot4236 : totK PD2M8K2 D2M8K2.t4236 = [0, 0, 0, 81025935947, 417383018707, 360910992899, 47205345794, 0] := by
  decide +kernel

theorem rows4237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4237 = true := by
  decide +kernel

theorem tot4237 : totK PD2M8K2 D2M8K2.t4237 = [0, 0, 0, 0, 208023329787, 504012795808, 144267921325, 2437267027] := by
  decide +kernel

theorem rows4238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4238 = true := by
  decide +kernel

theorem tot4238 : totK PD2M8K2 D2M8K2.t4238 = [0, 0, 206411397169, 392253773546, 139885409956, 66936616508, 69057510705, 6701800220] := by
  decide +kernel

theorem rows4239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4239 = true := by
  decide +kernel

theorem tot4239 : totK PD2M8K2 D2M8K2.t4239 = [0, 0, 114393153260, 453821433474, 306649546942, 19705821604, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
