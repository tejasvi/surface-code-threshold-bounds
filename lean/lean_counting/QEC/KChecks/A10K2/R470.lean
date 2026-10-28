import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1880 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1880 = true := by
  decide +kernel

theorem tot1880 : totK PA10K2 A10K2.t1880 = [0, 0, 486142690369, 1864470849728, 2029975432806, 566060699521, 24433330952, 0, 0, 0] := by
  decide +kernel

theorem rows1881 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1881 = true := by
  decide +kernel

theorem tot1881 : totK PA10K2 A10K2.t1881 = [0, 0, 0, 571150736105, 1968765054387, 1749245806140, 417990963357, 25371180993, 0, 0] := by
  decide +kernel

theorem rows1882 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1882 = true := by
  decide +kernel

theorem tot1882 : totK PA10K2 A10K2.t1882 = [0, 0, 412992599700, 1485035691621, 1883145739732, 929984833727, 159229757572, 5460492893, 0, 0] := by
  decide +kernel

theorem rows1883 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1883 = true := by
  decide +kernel

theorem tot1883 : totK PA10K2 A10K2.t1883 = [0, 0, 327331826266, 1631564909368, 2041086327138, 657249439447, 39144606383, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
