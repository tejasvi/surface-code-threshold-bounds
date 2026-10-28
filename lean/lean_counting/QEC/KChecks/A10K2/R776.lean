import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3104 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3104 = true := by
  decide +kernel

theorem tot3104 : totK PA10K2 A10K2.t3104 = [0, 312139800791, 1097250380183, 1608208200531, 1445304303192, 557372482702, 50548650670, 0, 0, 0] := by
  decide +kernel

theorem rows3105 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3105 = true := by
  decide +kernel

theorem tot3105 : totK PA10K2 A10K2.t3105 = [0, 510881146888, 1838147700960, 1916107499279, 539384042152, 32256115688, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3106 = true := by
  decide +kernel

theorem tot3106 : totK PA10K2 A10K2.t3106 = [0, 0, 689945590973, 2095511625316, 1681926912602, 397751532257, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows3107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3107 = true := by
  decide +kernel

theorem tot3107 : totK PA10K2 A10K2.t3107 = [0, 280788281866, 1191722003731, 1926395800663, 1271060875748, 222057277472, 5809256573, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
