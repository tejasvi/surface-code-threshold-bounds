import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4688 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4688 = true := by
  decide +kernel

theorem tot4688 : totK PA10K2 A10K2.t4688 = [0, 0, 605532579823, 2050609546702, 1927581048504, 448795382774, 13549732798, 0, 0, 0] := by
  decide +kernel

theorem rows4689 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4689 = true := by
  decide +kernel

theorem tot4689 : totK PA10K2 A10K2.t4689 = [0, 0, 279799475968, 1440906503590, 2180166195256, 1036802519516, 99465073353, 0, 0, 0] := by
  decide +kernel

theorem rows4690 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4690 = true := by
  decide +kernel

theorem tot4690 : totK PA10K2 A10K2.t4690 = [0, 0, 419043695193, 1623517983616, 2038575687091, 858909446488, 77356929332, 0, 0, 0] := by
  decide +kernel

theorem rows4691 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4691 = true := by
  decide +kernel

theorem tot4691 : totK PA10K2 A10K2.t4691 = [0, 0, 392205854611, 1686114125894, 2040797752072, 712248642693, 47808301808, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
