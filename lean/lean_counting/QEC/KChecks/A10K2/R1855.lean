import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7420 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7420 = true := by
  decide +kernel

theorem tot7420 : totK PA10K2 A10K2.t7420 = [0, 0, 0, 374964317800, 1686299756989, 2080212076377, 775404335760, 65619212014, 0, 0] := by
  decide +kernel

theorem rows7421 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7421 = true := by
  decide +kernel

theorem tot7421 : totK PA10K2 A10K2.t7421 = [0, 0, 0, 112281665929, 864363647403, 2121883235649, 1502303743034, 241392774852, 6904928264, 0] := by
  decide +kernel

theorem rows7422 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7422 = true := by
  decide +kernel

theorem tot7422 : totK PA10K2 A10K2.t7422 = [0, 0, 0, 572137771939, 2077801543581, 1992591061076, 450972902855, 12707091879, 0, 0] := by
  decide +kernel

theorem rows7423 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7423 = true := by
  decide +kernel

theorem tot7423 : totK PA10K2 A10K2.t7423 = [0, 0, 0, 0, 818175706757, 2266003712109, 1639259419290, 241978035020, 6766355402, 0] := by
  decide +kernel

end QECKChecks.A10K2
