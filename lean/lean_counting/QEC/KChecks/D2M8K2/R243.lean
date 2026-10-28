import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t972 = true := by
  decide +kernel

theorem tot972 : totK PD2M8K2 D2M8K2.t972 = [0, 276953704590, 515332798427, 100557055231, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t973 = true := by
  decide +kernel

theorem tot973 : totK PD2M8K2 D2M8K2.t973 = [82236245000, 326661953811, 371355962253, 104958091443, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t974 = true := by
  decide +kernel

theorem tot974 : totK PD2M8K2 D2M8K2.t974 = [176128085211, 453601415798, 262271241914, 27408425996, 0, 0, 0, 0] := by
  decide +kernel

theorem rows975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t975 = true := by
  decide +kernel

theorem tot975 : totK PD2M8K2 D2M8K2.t975 = [70759785648, 328050561567, 407730088660, 95742837000, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
