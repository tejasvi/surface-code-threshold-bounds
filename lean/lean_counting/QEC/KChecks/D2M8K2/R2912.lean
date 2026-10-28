import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11648 = true := by
  decide +kernel

theorem tot11648 : totK PD2M8K2 D2M8K2.t11648 = [54703274150, 321609429953, 410494372062, 95839441014, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows11649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11649 = true := by
  decide +kernel

theorem tot11649 : totK PD2M8K2 D2M8K2.t11649 = [0, 228682514054, 486958664079, 164649512238, 4763850746, 0, 0, 0] := by
  decide +kernel

theorem rows11650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11650 = true := by
  decide +kernel

theorem tot11650 : totK PD2M8K2 D2M8K2.t11650 = [0, 182799860219, 474318781753, 216507770897, 14605895437, 0, 0, 0] := by
  decide +kernel

theorem rows11651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11651 = true := by
  decide +kernel

theorem tot11651 : totK PD2M8K2 D2M8K2.t11651 = [0, 180414447086, 460719079537, 207356885889, 10735115630, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
