import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14808 = true := by
  decide +kernel

theorem tot14808 : totK PD2M8K2 D2M8K2.t14808 = [0, 246191805388, 452924329901, 196181759179, 21382878902, 0, 0, 0] := by
  decide +kernel

theorem rows14809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14809 = true := by
  decide +kernel

theorem tot14809 : totK PD2M8K2 D2M8K2.t14809 = [0, 162849582945, 491323273226, 232624782631, 7816749669, 0, 0, 0] := by
  decide +kernel

theorem rows14810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14810 = true := by
  decide +kernel

theorem tot14810 : totK PD2M8K2 D2M8K2.t14810 = [112859636424, 339944051456, 314991395157, 127371232101, 8209931632, 0, 0, 0] := by
  decide +kernel

theorem rows14811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14811 = true := by
  decide +kernel

theorem tot14811 : totK PD2M8K2 D2M8K2.t14811 = [172657275479, 441962157096, 276517393205, 30173504110, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
