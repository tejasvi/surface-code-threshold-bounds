import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3800 = true := by
  decide +kernel

theorem tot3800 : totK PD2M8K2 D2M8K2.t3800 = [49309689926, 220307671114, 430571771892, 194260584418, 8209296672, 0, 0, 0] := by
  decide +kernel

theorem rows3801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3801 = true := by
  decide +kernel

theorem tot3801 : totK PD2M8K2 D2M8K2.t3801 = [180634144336, 464828030480, 253085277868, 23042648846, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3802 = true := by
  decide +kernel

theorem tot3802 : totK PD2M8K2 D2M8K2.t3802 = [188941634775, 476951133155, 224435144846, 12523541424, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3803 = true := by
  decide +kernel

theorem tot3803 : totK PD2M8K2 D2M8K2.t3803 = [15862962898, 301438574539, 472146116678, 102005242475, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
