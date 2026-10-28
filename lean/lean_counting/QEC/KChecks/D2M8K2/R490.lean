import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1960 = true := by
  decide +kernel

theorem tot1960 : totK PD2M8K2 D2M8K2.t1960 = [0, 0, 178283137366, 480912949348, 211496028846, 8669917095, 0, 0] := by
  decide +kernel

theorem rows1961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1961 = true := by
  decide +kernel

theorem tot1961 : totK PD2M8K2 D2M8K2.t1961 = [0, 0, 174767237904, 459704464780, 232684617705, 19331462227, 0, 0] := by
  decide +kernel

theorem rows1962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1962 = true := by
  decide +kernel

theorem tot1962 : totK PD2M8K2 D2M8K2.t1962 = [0, 0, 173511103334, 465783061068, 216623101072, 12955845008, 0, 0] := by
  decide +kernel

theorem rows1963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1963 = true := by
  decide +kernel

theorem tot1963 : totK PD2M8K2 D2M8K2.t1963 = [0, 0, 87479108234, 328361069875, 364374970422, 90962354342, 1369150432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
