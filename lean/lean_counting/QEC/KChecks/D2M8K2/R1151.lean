import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4604 = true := by
  decide +kernel

theorem tot4604 : totK PD2M8K2 D2M8K2.t4604 = [0, 0, 171441945645, 403400631425, 225716099843, 76005163526, 7702325016, 0] := by
  decide +kernel

theorem rows4605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4605 = true := by
  decide +kernel

theorem tot4605 : totK PD2M8K2 D2M8K2.t4605 = [0, 0, 185705664440, 455056552662, 224122019953, 14234287867, 0, 0] := by
  decide +kernel

theorem rows4606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4606 = true := by
  decide +kernel

theorem tot4606 : totK PD2M8K2 D2M8K2.t4606 = [0, 0, 17498873409, 294575844838, 467153207782, 84756237992, 1310166938, 0] := by
  decide +kernel

theorem rows4607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4607 = true := by
  decide +kernel

theorem tot4607 : totK PD2M8K2 D2M8K2.t4607 = [0, 0, 103764244298, 388955512981, 382038764890, 42567815292, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
