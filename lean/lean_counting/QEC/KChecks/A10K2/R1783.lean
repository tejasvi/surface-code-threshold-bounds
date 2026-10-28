import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7132 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7132 = true := by
  decide +kernel

theorem tot7132 : totK PA10K2 A10K2.t7132 = [0, 0, 576631465933, 1772535387848, 1613773166459, 612656598952, 243812043997, 37310410385, 0, 0] := by
  decide +kernel

theorem rows7133 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7133 = true := by
  decide +kernel

theorem tot7133 : totK PA10K2 A10K2.t7133 = [0, 0, 290724629903, 1511639675640, 2176340386203, 855047214440, 67727243258, 0, 0, 0] := by
  decide +kernel

theorem rows7134 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7134 = true := by
  decide +kernel

theorem tot7134 : totK PA10K2 A10K2.t7134 = [0, 0, 0, 497189933732, 1806869495807, 1775541903503, 473925801065, 30831673886, 0, 0] := by
  decide +kernel

theorem rows7135 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7135 = true := by
  decide +kernel

theorem tot7135 : totK PA10K2 A10K2.t7135 = [0, 0, 410831171158, 1590064556668, 1973775340757, 811597146469, 75440906312, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
