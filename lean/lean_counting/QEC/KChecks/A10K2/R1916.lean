import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7664 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7664 = true := by
  decide +kernel

theorem tot7664 : totK PA10K2 A10K2.t7664 = [0, 0, 232865494112, 1125265085360, 2004806877817, 1386213183304, 244195264129, 11418542001, 0, 0] := by
  decide +kernel

theorem rows7665 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7665 = true := by
  decide +kernel

theorem tot7665 : totK PA10K2 A10K2.t7665 = [0, 0, 505888066736, 1833815436484, 2009988643303, 599541653566, 37831916145, 0, 0, 0] := by
  decide +kernel

theorem rows7666 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7666 = true := by
  decide +kernel

theorem tot7666 : totK PA10K2 A10K2.t7666 = [0, 0, 107440630134, 985011154454, 2183078015916, 1497087671763, 258117173372, 6586990447, 0, 0] := by
  decide +kernel

theorem rows7667 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7667 = true := by
  decide +kernel

theorem tot7667 : totK PA10K2 A10K2.t7667 = [0, 0, 0, 500239042547, 1925474312020, 2050851457225, 539120450422, 18818953403, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
