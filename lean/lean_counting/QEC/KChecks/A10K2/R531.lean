import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2124 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2124 = true := by
  decide +kernel

theorem tot2124 : totK PA10K2 A10K2.t2124 = [0, 918928096280, 2398286744308, 1278713961453, 113567685273, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2125 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2125 = true := by
  decide +kernel

theorem tot2125 : totK PA10K2 A10K2.t2125 = [507908548294, 1612698967495, 1735290732279, 890920453141, 188307289486, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2126 = true := by
  decide +kernel

theorem tot2126 : totK PA10K2 A10K2.t2126 = [84375141745, 920757995017, 2202540135317, 1593369453671, 296499527773, 6962742351, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2127 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2127 = true := by
  decide +kernel

theorem tot2127 : totK PA10K2 A10K2.t2127 = [0, 538134293105, 1908463050019, 1928136937738, 584578937470, 48278235682, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
