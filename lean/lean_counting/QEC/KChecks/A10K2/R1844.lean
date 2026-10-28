import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7376 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7376 = true := by
  decide +kernel

theorem tot7376 : totK PA10K2 A10K2.t7376 = [0, 0, 0, 462611689169, 1854067736801, 1867857518802, 406678602615, 25371180993, 0, 0] := by
  decide +kernel

theorem rows7377 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7377 = true := by
  decide +kernel

theorem tot7377 : totK PA10K2 A10K2.t7377 = [0, 0, 500575738652, 1729671845496, 1913947033933, 668533624715, 87307979762, 5460492893, 0, 0] := by
  decide +kernel

theorem rows7378 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7378 = true := by
  decide +kernel

theorem tot7378 : totK PA10K2 A10K2.t7378 = [0, 0, 49043091436, 985820235357, 2175892653112, 1362106764979, 206778095525, 5393623172, 0, 0] := by
  decide +kernel

theorem rows7379 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7379 = true := by
  decide +kernel

theorem tot7379 : totK PA10K2 A10K2.t7379 = [0, 0, 374747736440, 1339758191720, 1779803132666, 1009361448816, 168626083080, 6034215561, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
