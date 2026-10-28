import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15032 = true := by
  decide +kernel

theorem tot15032 : totK PD2M8K2 D2M8K2.t15032 = [0, 171952938072, 437575686300, 279788266967, 29900658212, 0, 0, 0] := by
  decide +kernel

theorem rows15033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15033 = true := by
  decide +kernel

theorem tot15033 : totK PD2M8K2 D2M8K2.t15033 = [0, 177855509545, 491457773348, 236830746106, 10417748186, 0, 0, 0] := by
  decide +kernel

theorem rows15034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15034 = true := by
  decide +kernel

theorem tot15034 : totK PD2M8K2 D2M8K2.t15034 = [0, 0, 223892214813, 456605849683, 202330243648, 18724171075, 0, 0] := by
  decide +kernel

theorem rows15035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15035 = true := by
  decide +kernel

theorem tot15035 : totK PD2M8K2 D2M8K2.t15035 = [0, 0, 178564792239, 491182791423, 213031208610, 4878316567, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
