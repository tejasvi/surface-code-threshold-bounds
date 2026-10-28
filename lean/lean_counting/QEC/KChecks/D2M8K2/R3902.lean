import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15608 = true := by
  decide +kernel

theorem tot15608 : totK PD2M8K2 D2M8K2.t15608 = [0, 0, 172072866573, 457790718281, 261767911758, 25454134109, 0, 0] := by
  decide +kernel

theorem rows15609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15609 = true := by
  decide +kernel

theorem tot15609 : totK PD2M8K2 D2M8K2.t15609 = [0, 89263107398, 235319987187, 352040824095, 213808148365, 17449007145, 0, 0] := by
  decide +kernel

theorem rows15610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15610 = true := by
  decide +kernel

theorem tot15610 : totK PD2M8K2 D2M8K2.t15610 = [0, 152962790648, 466429171214, 246827447267, 15936446759, 0, 0, 0] := by
  decide +kernel

theorem rows15611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15611 = true := by
  decide +kernel

theorem tot15611 : totK PD2M8K2 D2M8K2.t15611 = [0, 153130125640, 446370194671, 266297424612, 18230173285, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
