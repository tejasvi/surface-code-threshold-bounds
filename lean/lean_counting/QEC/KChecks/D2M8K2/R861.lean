import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3444 = true := by
  decide +kernel

theorem tot3444 : totK PD2M8K2 D2M8K2.t3444 = [170141184774, 442346087022, 280582274814, 30498142501, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3445 = true := by
  decide +kernel

theorem tot3445 : totK PD2M8K2 D2M8K2.t3445 = [105922160267, 428910421519, 321990004104, 32067856833, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3446 = true := by
  decide +kernel

theorem tot3446 : totK PD2M8K2 D2M8K2.t3446 = [0, 297056371474, 520059794237, 98934094653, 1096156699, 0, 0, 0] := by
  decide +kernel

theorem rows3447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3447 = true := by
  decide +kernel

theorem tot3447 : totK PD2M8K2 D2M8K2.t3447 = [126224852308, 339315984106, 348027900350, 102853148538, 3880716147, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
