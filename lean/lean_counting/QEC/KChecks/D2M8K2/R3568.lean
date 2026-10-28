import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14272 = true := by
  decide +kernel

theorem tot14272 : totK PD2M8K2 D2M8K2.t14272 = [186282126101, 469590210537, 246961680807, 23003581512, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14273 = true := by
  decide +kernel

theorem tot14273 : totK PD2M8K2 D2M8K2.t14273 = [189051485379, 474310282719, 240019500371, 15232247554, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14274 = true := by
  decide +kernel

theorem tot14274 : totK PD2M8K2 D2M8K2.t14274 = [45093903507, 318820875530, 433855791948, 101337778920, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows14275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14275 = true := by
  decide +kernel

theorem tot14275 : totK PD2M8K2 D2M8K2.t14275 = [0, 216505239743, 484443034943, 182489259502, 7442000727, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
