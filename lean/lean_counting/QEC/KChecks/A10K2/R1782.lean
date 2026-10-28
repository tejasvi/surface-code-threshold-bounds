import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7128 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7128 = true := by
  decide +kernel

theorem tot7128 : totK PA10K2 A10K2.t7128 = [0, 0, 271068345698, 1096753303338, 1950697560607, 1521390087796, 272669979141, 7047025452, 0, 0] := by
  decide +kernel

theorem rows7129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7129 = true := by
  decide +kernel

theorem tot7129 : totK PA10K2 A10K2.t7129 = [0, 0, 451698470309, 1857704017394, 2094968026806, 580440473842, 23385739874, 0, 0, 0] := by
  decide +kernel

theorem rows7130 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7130 = true := by
  decide +kernel

theorem tot7130 : totK PA10K2 A10K2.t7130 = [0, 0, 107213596712, 974055772656, 2145429776189, 1526185364977, 244634322406, 6066958478, 0, 0] := by
  decide +kernel

theorem rows7131 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7131 = true := by
  decide +kernel

theorem tot7131 : totK PA10K2 A10K2.t7131 = [0, 0, 0, 512188785835, 1914978879450, 1977822078546, 504091852378, 17732757243, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
