import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9420 = true := by
  decide +kernel

theorem tot9420 : totK PD2M8K2 D2M8K2.t9420 = [0, 123825068022, 447171165304, 308261251271, 20660773012, 0, 0, 0] := by
  decide +kernel

theorem rows9421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9421 = true := by
  decide +kernel

theorem tot9421 : totK PD2M8K2 D2M8K2.t9421 = [0, 0, 209754684130, 487329270969, 169524918297, 9528124131, 0, 0] := by
  decide +kernel

theorem rows9422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9422 = true := by
  decide +kernel

theorem tot9422 : totK PD2M8K2 D2M8K2.t9422 = [0, 86252406291, 337235076087, 366193642427, 90777040189, 3581949829, 0, 0] := by
  decide +kernel

theorem rows9423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9423 = true := by
  decide +kernel

theorem tot9423 : totK PD2M8K2 D2M8K2.t9423 = [0, 172190423217, 444423611787, 273198317158, 29699471555, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
