import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5380 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5380 = true := by
  decide +kernel

theorem tot5380 : totK PA10K2 A10K2.t5380 = [0, 0, 325257928870, 1613857582556, 2131784534396, 745834894340, 56035958050, 0, 0, 0] := by
  decide +kernel

theorem rows5381 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5381 = true := by
  decide +kernel

theorem tot5381 : totK PA10K2 A10K2.t5381 = [0, 0, 0, 462590454733, 1779913417952, 1813504067992, 482871452789, 31082886609, 0, 0] := by
  decide +kernel

theorem rows5382 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5382 = true := by
  decide +kernel

theorem tot5382 : totK PA10K2 A10K2.t5382 = [0, 0, 446817029335, 1704920965343, 1961966078499, 671505059458, 59625743415, 0, 0, 0] := by
  decide +kernel

theorem rows5383 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5383 = true := by
  decide +kernel

theorem tot5383 : totK PA10K2 A10K2.t5383 = [0, 0, 280668530687, 1463201502884, 2085483869981, 745779551892, 44498074173, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
