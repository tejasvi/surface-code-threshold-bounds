import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1100 = true := by
  decide +kernel

theorem tot1100 : totK PD2M8K2 D2M8K2.t1100 = [0, 180160397577, 453082647421, 266792367711, 27977033009, 0, 0, 0] := by
  decide +kernel

theorem rows1101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1101 = true := by
  decide +kernel

theorem tot1101 : totK PD2M8K2 D2M8K2.t1101 = [0, 154966243927, 451493201590, 269781540208, 18163825615, 0, 0, 0] := by
  decide +kernel

theorem rows1102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1102 = true := by
  decide +kernel

theorem tot1102 : totK PD2M8K2 D2M8K2.t1102 = [0, 0, 250429815600, 480990788604, 153065110200, 8464368736, 0, 0] := by
  decide +kernel

theorem rows1103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1103 = true := by
  decide +kernel

theorem tot1103 : totK PD2M8K2 D2M8K2.t1103 = [0, 107923305858, 346161289459, 339557186813, 89610525129, 3575904516, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
