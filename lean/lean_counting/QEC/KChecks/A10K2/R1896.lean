import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7584 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7584 = true := by
  decide +kernel

theorem tot7584 : totK PA10K2 A10K2.t7584 = [0, 0, 672643542915, 2163827396719, 1834896219388, 346782737518, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows7585 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7585 = true := by
  decide +kernel

theorem tot7585 : totK PA10K2 A10K2.t7585 = [0, 0, 440926389062, 1735469275829, 2054688356655, 719005651583, 56143165367, 0, 0, 0] := by
  decide +kernel

theorem rows7586 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7586 = true := by
  decide +kernel

theorem tot7586 : totK PA10K2 A10K2.t7586 = [0, 0, 570317409404, 2007944488100, 1996373217576, 507491564760, 25214907704, 0, 0, 0] := by
  decide +kernel

theorem rows7587 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7587 = true := by
  decide +kernel

theorem tot7587 : totK PA10K2 A10K2.t7587 = [0, 0, 0, 760455783535, 2306216701759, 1657848442362, 255151440272, 6904928264, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
