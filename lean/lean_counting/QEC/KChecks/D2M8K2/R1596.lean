import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6384 = true := by
  decide +kernel

theorem tot6384 : totK PD2M8K2 D2M8K2.t6384 = [0, 0, 90510743449, 361250883519, 328211242627, 56858843412, 1021600638, 0] := by
  decide +kernel

theorem rows6385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6385 = true := by
  decide +kernel

theorem tot6385 : totK PD2M8K2 D2M8K2.t6385 = [0, 0, 11210313144, 286165233393, 427821937157, 96848811207, 3552795014, 0] := by
  decide +kernel

theorem rows6386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6386 = true := by
  decide +kernel

theorem tot6386 : totK PD2M8K2 D2M8K2.t6386 = [0, 0, 202958803660, 483606498781, 194124054643, 11385413710, 0, 0] := by
  decide +kernel

theorem rows6387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6387 = true := by
  decide +kernel

theorem tot6387 : totK PD2M8K2 D2M8K2.t6387 = [0, 0, 195795424260, 482709353656, 210869263513, 8312660106, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
