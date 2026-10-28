import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3700 = true := by
  decide +kernel

theorem tot3700 : totK PD2M8K2 D2M8K2.t3700 = [198685354040, 473502151289, 217678126832, 12523541424, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3701 = true := by
  decide +kernel

theorem tot3701 : totK PD2M8K2 D2M8K2.t3701 = [8125304319, 302251445055, 481686390840, 101168473330, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows3702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3702 = true := by
  decide +kernel

theorem tot3702 : totK PD2M8K2 D2M8K2.t3702 = [0, 200788670738, 465577427145, 195475667721, 12052611869, 0, 0, 0] := by
  decide +kernel

theorem rows3703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3703 = true := by
  decide +kernel

theorem tot3703 : totK PD2M8K2 D2M8K2.t3703 = [189370845208, 454559503605, 247604175202, 28800095950, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
