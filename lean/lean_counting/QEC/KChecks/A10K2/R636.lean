import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2544 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2544 = true := by
  decide +kernel

theorem tot2544 : totK PA10K2 A10K2.t2544 = [0, 0, 518831205650, 1954376825887, 1837619669014, 417260815978, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows2545 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2545 = true := by
  decide +kernel

theorem tot2545 : totK PA10K2 A10K2.t2545 = [0, 425404870383, 1438114938707, 1734536185156, 895006094468, 171956966343, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows2546 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2546 = true := by
  decide +kernel

theorem tot2546 : totK PA10K2 A10K2.t2546 = [0, 370680369222, 1768577701722, 2052247178730, 592290724725, 32877822373, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2547 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2547 = true := by
  decide +kernel

theorem tot2547 : totK PA10K2 A10K2.t2547 = [0, 0, 729303682677, 2246598354282, 1445409893552, 156261638338, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
