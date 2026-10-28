import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8756 = true := by
  decide +kernel

theorem tot8756 : totK PD2M8K2 D2M8K2.t8756 = [0, 0, 254766398164, 478537372033, 143006699939, 9573250094, 0, 0] := by
  decide +kernel

theorem rows8757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8757 = true := by
  decide +kernel

theorem tot8757 : totK PD2M8K2 D2M8K2.t8757 = [0, 0, 196141879772, 459905534818, 237678314664, 23010439256, 0, 0] := by
  decide +kernel

theorem rows8758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8758 = true := by
  decide +kernel

theorem tot8758 : totK PD2M8K2 D2M8K2.t8758 = [0, 0, 201612912821, 469102080126, 218653009818, 10660803951, 0, 0] := by
  decide +kernel

theorem rows8759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8759 = true := by
  decide +kernel

theorem tot8759 : totK PD2M8K2 D2M8K2.t8759 = [0, 0, 193555676034, 465723998523, 215981610184, 11982551986, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
