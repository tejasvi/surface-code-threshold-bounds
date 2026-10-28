import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2204 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2204 = true := by
  decide +kernel

theorem tot2204 : totK PA10K2 A10K2.t2204 = [0, 525363538111, 1970631865515, 1940076945002, 435500394943, 13816090359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2205 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2205 = true := by
  decide +kernel

theorem tot2205 : totK PA10K2 A10K2.t2205 = [0, 582549879177, 1907538103624, 1895360176495, 618211020868, 49180423016, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2206 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2206 = true := by
  decide +kernel

theorem tot2206 : totK PA10K2 A10K2.t2206 = [0, 371558514270, 1634531876607, 2130154378326, 823323955081, 70090120521, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2207 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2207 = true := by
  decide +kernel

theorem tot2207 : totK PA10K2 A10K2.t2207 = [0, 165236076505, 966586524924, 2062612672934, 1438294633873, 260846826854, 6904928264, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
