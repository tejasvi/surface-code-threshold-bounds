import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7872 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7872 = true := by
  decide +kernel

theorem tot7872 : totK PA10K2 A10K2.t7872 = [0, 0, 350469507776, 1281899604266, 1784014007387, 1117920030046, 192424336506, 6034215561, 0, 0] := by
  decide +kernel

theorem rows7873 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7873 = true := by
  decide +kernel

theorem tot7873 : totK PA10K2 A10K2.t7873 = [0, 0, 234501307853, 1452153496503, 2191585476086, 789271259099, 60214384836, 0, 0, 0] := by
  decide +kernel

theorem rows7874 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7874 = true := by
  decide +kernel

theorem tot7874 : totK PA10K2 A10K2.t7874 = [0, 0, 304160910350, 1202654143265, 1999067367346, 1154011437729, 176458076995, 6239673734, 0, 0] := by
  decide +kernel

theorem rows7875 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7875 = true := by
  decide +kernel

theorem tot7875 : totK PA10K2 A10K2.t7875 = [0, 0, 497687753329, 1902497016522, 2009610718206, 570087109341, 32317336324, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
