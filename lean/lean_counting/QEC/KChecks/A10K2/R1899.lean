import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7596 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7596 = true := by
  decide +kernel

theorem tot7596 : totK PA10K2 A10K2.t7596 = [0, 0, 70039017234, 628311474778, 2007917675559, 1840023224169, 395735482833, 13364899180, 0, 0] := by
  decide +kernel

theorem rows7597 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7597 = true := by
  decide +kernel

theorem tot7597 : totK PA10K2 A10K2.t7597 = [0, 0, 539452731072, 1968340444115, 2059617635507, 570352808349, 30522118328, 0, 0, 0] := by
  decide +kernel

theorem rows7598 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7598 = true := by
  decide +kernel

theorem tot7598 : totK PA10K2 A10K2.t7598 = [0, 0, 215095608158, 1246584958353, 2197542653585, 1280098417700, 160813774087, 0, 0, 0] := by
  decide +kernel

theorem rows7599 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7599 = true := by
  decide +kernel

theorem tot7599 : totK PA10K2 A10K2.t7599 = [0, 0, 0, 537898020747, 1993775723517, 2114912858328, 505114520683, 19122223731, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
