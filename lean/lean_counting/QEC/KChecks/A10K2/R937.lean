import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3748 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3748 = true := by
  decide +kernel

theorem tot3748 : totK PA10K2 A10K2.t3748 = [0, 0, 0, 740144105631, 2126125342246, 1612601397256, 371095799662, 25371180993, 0, 0] := by
  decide +kernel

theorem rows3749 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3749 = true := by
  decide +kernel

theorem tot3749 : totK PA10K2 A10K2.t3749 = [0, 0, 290498283436, 1145723532753, 1837743139313, 1249038217590, 208173338715, 5460492893, 0, 0] := by
  decide +kernel

theorem rows3750 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3750 = true := by
  decide +kernel

theorem tot3750 : totK PA10K2 A10K2.t3750 = [0, 0, 453828566602, 1760842578821, 1927175267477, 534099261256, 31614405859, 0, 0, 0] := by
  decide +kernel

theorem rows3751 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3751 = true := by
  decide +kernel

theorem tot3751 : totK PA10K2 A10K2.t3751 = [0, 0, 0, 948355975882, 2407133262428, 1203020989487, 83834858258, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
