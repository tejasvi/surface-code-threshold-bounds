import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t668 = true := by
  decide +kernel

theorem tot668 : totK PD2M8K2 D2M8K2.t668 = [85054205109, 322461289126, 386193402905, 107555929070, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t669 = true := by
  decide +kernel

theorem tot669 : totK PD2M8K2 D2M8K2.t669 = [153718103570, 445581097959, 271741333738, 23616703790, 0, 0, 0, 0] := by
  decide +kernel

theorem rows670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t670 = true := by
  decide +kernel

theorem tot670 : totK PD2M8K2 D2M8K2.t670 = [182137505762, 466642454972, 251669665025, 18403099127, 0, 0, 0, 0] := by
  decide +kernel

theorem rows671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t671 = true := by
  decide +kernel

theorem tot671 : totK PD2M8K2 D2M8K2.t671 = [0, 256991435373, 496616159709, 128085811598, 1268739303, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
