import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2924 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2924 = true := by
  decide +kernel

theorem tot2924 : totK PA10K2 A10K2.t2924 = [0, 0, 721550966133, 2167306163830, 1562333952710, 271486621255, 6904928264, 0, 0, 0] := by
  decide +kernel

theorem rows2925 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2925 = true := by
  decide +kernel

theorem tot2925 : totK PA10K2 A10K2.t2925 = [0, 423629393039, 1572144975470, 1973714858605, 838526218336, 82054764332, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2926 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2926 = true := by
  decide +kernel

theorem tot2926 : totK PA10K2 A10K2.t2926 = [0, 345090956614, 1604685320975, 2136833370035, 871040013132, 77176302380, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2927 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2927 = true := by
  decide +kernel

theorem tot2927 : totK PA10K2 A10K2.t2927 = [0, 163668966304, 964136889083, 2019650329975, 1481822168112, 262354789999, 7047025452, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
