import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t424 = true := by
  decide +kernel

theorem tot424 : totK PD2M8K2 D2M8K2.t424 = [0, 153175177080, 453694022033, 269270252792, 17618284595, 0, 0, 0] := by
  decide +kernel

theorem rows425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t425 = true := by
  decide +kernel

theorem tot425 : totK PD2M8K2 D2M8K2.t425 = [84914276500, 256780957121, 375580031495, 176608705831, 8213711289, 0, 0, 0] := by
  decide +kernel

theorem rows426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t426 = true := by
  decide +kernel

theorem tot426 : totK PD2M8K2 D2M8K2.t426 = [178796849474, 460846900905, 249571941775, 22499796278, 0, 0, 0, 0] := by
  decide +kernel

theorem rows427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t427 = true := by
  decide +kernel

theorem tot427 : totK PD2M8K2 D2M8K2.t427 = [160792790028, 471812306552, 255521591122, 13615052294, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
