import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2340 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2340 = true := by
  decide +kernel

theorem tot2340 : totK PA10K2 A10K2.t2340 = [0, 219378224878, 989742461179, 1885605200727, 1343073582718, 230086337014, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows2341 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2341 = true := by
  decide +kernel

theorem tot2341 : totK PA10K2 A10K2.t2341 = [0, 540990273596, 1933320311067, 1836799953961, 472091849117, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2342 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2342 = true := by
  decide +kernel

theorem tot2342 : totK PA10K2 A10K2.t2342 = [0, 0, 891329248902, 2358810739181, 1310938544053, 127409525241, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2343 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2343 = true := by
  decide +kernel

theorem tot2343 : totK PA10K2 A10K2.t2343 = [0, 546739207337, 1656943576849, 1716352349576, 850644380791, 174034395168, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
