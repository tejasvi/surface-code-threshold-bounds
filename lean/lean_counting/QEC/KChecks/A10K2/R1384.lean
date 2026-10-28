import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5536 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5536 = true := by
  decide +kernel

theorem tot5536 : totK PA10K2 A10K2.t5536 = [0, 0, 119048527108, 1009519834532, 2202321310499, 1460421010409, 225368017517, 6904928264, 0, 0] := by
  decide +kernel

theorem rows5537 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5537 = true := by
  decide +kernel

theorem tot5537 : totK PA10K2 A10K2.t5537 = [0, 0, 404282802835, 1572716663163, 2010820334363, 871734904448, 82238109134, 0, 0, 0] := by
  decide +kernel

theorem rows5538 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5538 = true := by
  decide +kernel

theorem tot5538 : totK PA10K2 A10K2.t5538 = [0, 0, 378603266825, 1678877679649, 2130643714516, 760074085287, 56568080285, 0, 0, 0] := by
  decide +kernel

theorem rows5539 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5539 = true := by
  decide +kernel

theorem tot5539 : totK PA10K2 A10K2.t5539 = [0, 0, 105375790585, 838361609755, 2038429938185, 1620456417068, 283467502291, 7047025452, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
