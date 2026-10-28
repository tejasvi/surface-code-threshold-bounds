import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5092 = true := by
  decide +kernel

theorem tot5092 : totK PD2M8K2 D2M8K2.t5092 = [0, 0, 186668463228, 447886222718, 209196115258, 16891742343, 0, 0] := by
  decide +kernel

theorem rows5093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5093 = true := by
  decide +kernel

theorem tot5093 : totK PD2M8K2 D2M8K2.t5093 = [0, 0, 50195586724, 360807879554, 360507584178, 61239517235, 1138244013, 0] := by
  decide +kernel

theorem rows5094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5094 = true := by
  decide +kernel

theorem tot5094 : totK PD2M8K2 D2M8K2.t5094 = [0, 0, 93184785870, 413679074689, 348090771367, 35232898516, 0, 0] := by
  decide +kernel

theorem rows5095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5095 = true := by
  decide +kernel

theorem tot5095 : totK PD2M8K2 D2M8K2.t5095 = [0, 0, 173764452113, 447351215863, 254813583168, 23842652625, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
