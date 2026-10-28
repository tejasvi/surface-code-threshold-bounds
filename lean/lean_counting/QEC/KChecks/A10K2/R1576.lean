import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6304 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6304 = true := by
  decide +kernel

theorem tot6304 : totK PA10K2 A10K2.t6304 = [0, 436023790687, 1818072426108, 2143089446935, 630995362583, 24454642747, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6305 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6305 = true := by
  decide +kernel

theorem tot6305 : totK PA10K2 A10K2.t6305 = [0, 510015090104, 1846850260198, 2046002977468, 706997342669, 64040545475, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6306 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6306 = true := by
  decide +kernel

theorem tot6306 : totK PA10K2 A10K2.t6306 = [0, 202041260899, 1059866599911, 2029632815540, 1487750843772, 287079186146, 6904928264, 0, 0, 0] := by
  decide +kernel

theorem rows6307 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6307 = true := by
  decide +kernel

theorem tot6307 : totK PA10K2 A10K2.t6307 = [0, 526489761465, 1864729402646, 1936923639755, 550449176335, 31947994545, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
