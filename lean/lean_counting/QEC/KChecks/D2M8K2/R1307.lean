import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5228 = true := by
  decide +kernel

theorem tot5228 : totK PD2M8K2 D2M8K2.t5228 = [0, 0, 198195581411, 492262524905, 202893393969, 6596981871, 0, 0] := by
  decide +kernel

theorem rows5229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5229 = true := by
  decide +kernel

theorem tot5229 : totK PD2M8K2 D2M8K2.t5229 = [0, 0, 155042264559, 465835463564, 246540820597, 14936878817, 0, 0] := by
  decide +kernel

theorem rows5230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5230 = true := by
  decide +kernel

theorem tot5230 : totK PD2M8K2 D2M8K2.t5230 = [0, 0, 209889136184, 481710783742, 200679038719, 10460607274, 0, 0] := by
  decide +kernel

theorem rows5231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5231 = true := by
  decide +kernel

theorem tot5231 : totK PD2M8K2 D2M8K2.t5231 = [0, 0, 187316174525, 471120036222, 214264697891, 12319708528, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
