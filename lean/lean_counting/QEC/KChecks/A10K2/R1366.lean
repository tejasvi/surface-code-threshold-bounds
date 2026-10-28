import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5464 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5464 = true := by
  decide +kernel

theorem tot5464 : totK PA10K2 A10K2.t5464 = [0, 0, 771786875642, 2251876044641, 1679096248323, 289100881977, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows5465 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5465 = true := by
  decide +kernel

theorem tot5465 : totK PA10K2 A10K2.t5465 = [0, 0, 350041374007, 1549948870530, 2083501448281, 812035645414, 62378768877, 0, 0, 0] := by
  decide +kernel

theorem rows5466 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5466 = true := by
  decide +kernel

theorem tot5466 : totK PA10K2 A10K2.t5466 = [0, 0, 473413749271, 1843362757075, 1934296891969, 488750120225, 12917769548, 0, 0, 0] := by
  decide +kernel

theorem rows5467 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5467 = true := by
  decide +kernel

theorem tot5467 : totK PA10K2 A10K2.t5467 = [0, 0, 0, 576207282469, 1964386935493, 1730767966446, 415003147796, 25565504801, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
