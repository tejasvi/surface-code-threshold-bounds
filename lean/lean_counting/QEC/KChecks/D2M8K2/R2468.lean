import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9872 = true := by
  decide +kernel

theorem tot9872 : totK PD2M8K2 D2M8K2.t9872 = [0, 177730668779, 444634596543, 260027617782, 27568714872, 0, 0, 0] := by
  decide +kernel

theorem rows9873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9873 = true := by
  decide +kernel

theorem tot9873 : totK PD2M8K2 D2M8K2.t9873 = [0, 182629914509, 457091755312, 234299436926, 17104814242, 0, 0, 0] := by
  decide +kernel

theorem rows9874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9874 = true := by
  decide +kernel

theorem tot9874 : totK PD2M8K2 D2M8K2.t9874 = [0, 74989312342, 350882477009, 393971030837, 77638960604, 1096505104, 0, 0] := by
  decide +kernel

theorem rows9875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9875 = true := by
  decide +kernel

theorem tot9875 : totK PD2M8K2 D2M8K2.t9875 = [0, 0, 287523819279, 511250734223, 101110638872, 1069412848, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
