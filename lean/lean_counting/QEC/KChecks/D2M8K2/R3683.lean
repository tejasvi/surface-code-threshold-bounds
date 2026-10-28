import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14732 = true := by
  decide +kernel

theorem tot14732 : totK PD2M8K2 D2M8K2.t14732 = [169543068513, 455134395093, 257501184823, 18959421031, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14733 = true := by
  decide +kernel

theorem tot14733 : totK PD2M8K2 D2M8K2.t14733 = [0, 278445220870, 507869921777, 110020868017, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows14734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14734 = true := by
  decide +kernel

theorem tot14734 : totK PD2M8K2 D2M8K2.t14734 = [138123722682, 425692412694, 313183410489, 32696934811, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14735 = true := by
  decide +kernel

theorem tot14735 : totK PD2M8K2 D2M8K2.t14735 = [181541989681, 434567276936, 253686676108, 27164866636, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
