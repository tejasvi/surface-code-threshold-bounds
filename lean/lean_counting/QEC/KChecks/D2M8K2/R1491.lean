import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5964 = true := by
  decide +kernel

theorem tot5964 : totK PD2M8K2 D2M8K2.t5964 = [0, 188719956867, 466662530115, 220069740813, 12259108933, 0, 0, 0] := by
  decide +kernel

theorem rows5965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5965 = true := by
  decide +kernel

theorem tot5965 : totK PD2M8K2 D2M8K2.t5965 = [0, 11817468257, 320200781806, 478691065686, 89322926712, 0, 0, 0] := by
  decide +kernel

theorem rows5966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5966 = true := by
  decide +kernel

theorem tot5966 : totK PD2M8K2 D2M8K2.t5966 = [0, 0, 192846112276, 472155649117, 187230404379, 8824320960, 0, 0] := by
  decide +kernel

theorem rows5967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5967 = true := by
  decide +kernel

theorem tot5967 : totK PD2M8K2 D2M8K2.t5967 = [0, 201307096399, 458366891549, 232453043581, 24856481497, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
