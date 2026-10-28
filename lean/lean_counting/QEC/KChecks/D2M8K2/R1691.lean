import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6764 = true := by
  decide +kernel

theorem tot6764 : totK PD2M8K2 D2M8K2.t6764 = [167426896901, 459279319556, 266502570181, 18677451572, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6765 = true := by
  decide +kernel

theorem tot6765 : totK PD2M8K2 D2M8K2.t6765 = [0, 226400396008, 493973213010, 168557282007, 8124795009, 0, 0, 0] := by
  decide +kernel

theorem rows6766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6766 = true := by
  decide +kernel

theorem tot6766 : totK PD2M8K2 D2M8K2.t6766 = [60922329505, 308249809620, 408239035519, 110538694380, 4881092576, 0, 0, 0] := by
  decide +kernel

theorem rows6767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6767 = true := by
  decide +kernel

theorem tot6767 : totK PD2M8K2 D2M8K2.t6767 = [167542880799, 441555068153, 274869241369, 30498722087, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
