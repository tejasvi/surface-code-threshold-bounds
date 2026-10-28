import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1668 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1668 = true := by
  decide +kernel

theorem tot1668 : totK PA10K2 A10K2.t1668 = [0, 416581648771, 1687451811672, 1994266824203, 593884033180, 24516663070, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1669 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1669 = true := by
  decide +kernel

theorem tot1669 : totK PA10K2 A10K2.t1669 = [0, 0, 565964011524, 1928377614696, 1723881843105, 390173482840, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows1670 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1670 = true := by
  decide +kernel

theorem tot1670 : totK PA10K2 A10K2.t1670 = [0, 405821549516, 1444333289220, 1747227716856, 934232646902, 168757796432, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows1671 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1671 = true := by
  decide +kernel

theorem tot1671 : totK PA10K2 A10K2.t1671 = [0, 444084427628, 1775041904645, 1960281028492, 560578265157, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
