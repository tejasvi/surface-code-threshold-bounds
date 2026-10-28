import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7184 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7184 = true := by
  decide +kernel

theorem tot7184 : totK PA10K2 A10K2.t7184 = [0, 108028446513, 987974529236, 2021464859772, 1328674436105, 301808558606, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows7185 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7185 = true := by
  decide +kernel

theorem tot7185 : totK PA10K2 A10K2.t7185 = [0, 314605185439, 1209290577574, 1852897609609, 1166415797002, 196483186193, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows7186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7186 = true := by
  decide +kernel

theorem tot7186 : totK PA10K2 A10K2.t7186 = [0, 505902438422, 1879950758292, 1835198626622, 446475265230, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7187 = true := by
  decide +kernel

theorem tot7187 : totK PA10K2 A10K2.t7187 = [0, 0, 855963203034, 2375021277516, 1343014978925, 120343572413, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
