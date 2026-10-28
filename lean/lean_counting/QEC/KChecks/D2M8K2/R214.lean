import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t856 = true := by
  decide +kernel

theorem tot856 : totK PD2M8K2 D2M8K2.t856 = [0, 85385970001, 280733007378, 376205981333, 132699343012, 7481811052, 0, 0] := by
  decide +kernel

theorem rows857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t857 = true := by
  decide +kernel

theorem tot857 : totK PD2M8K2 D2M8K2.t857 = [0, 168943381114, 453479579280, 252508945985, 22384269906, 0, 0, 0] := by
  decide +kernel

theorem rows858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t858 = true := by
  decide +kernel

theorem tot858 : totK PD2M8K2 D2M8K2.t858 = [0, 181015165609, 454131031604, 245872808455, 18079445805, 0, 0, 0] := by
  decide +kernel

theorem rows859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t859 = true := by
  decide +kernel

theorem tot859 : totK PD2M8K2 D2M8K2.t859 = [0, 0, 311184618265, 487517007539, 90929755450, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
