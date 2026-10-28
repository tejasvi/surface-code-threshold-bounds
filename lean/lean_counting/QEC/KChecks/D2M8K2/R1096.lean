import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4384 = true := by
  decide +kernel

theorem tot4384 : totK PD2M8K2 D2M8K2.t4384 = [0, 0, 15784068643, 317209893131, 445463839820, 83656164162, 1369150432, 0] := by
  decide +kernel

theorem rows4385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4385 = true := by
  decide +kernel

theorem tot4385 : totK PD2M8K2 D2M8K2.t4385 = [0, 0, 105882274612, 437558817910, 309000584527, 21776096234, 0, 0] := by
  decide +kernel

theorem rows4386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4386 = true := by
  decide +kernel

theorem tot4386 : totK PD2M8K2 D2M8K2.t4386 = [0, 0, 199062264621, 470553927521, 215878910843, 12552144954, 0, 0] := by
  decide +kernel

theorem rows4387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4387 = true := by
  decide +kernel

theorem tot4387 : totK PD2M8K2 D2M8K2.t4387 = [0, 0, 189654451710, 468144230885, 206659075889, 12593797338, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
