import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5984 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5984 = true := by
  decide +kernel

theorem tot5984 : totK PA10K2 A10K2.t5984 = [0, 591756298713, 2049748975153, 1983892727781, 427668507750, 12746179907, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5985 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5985 = true := by
  decide +kernel

theorem tot5985 : totK PA10K2 A10K2.t5985 = [0, 475759884403, 1702233015762, 1925992374291, 732705711382, 68825997017, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5986 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5986 = true := by
  decide +kernel

theorem tot5986 : totK PA10K2 A10K2.t5986 = [0, 360002622783, 1642685202161, 2073286658172, 692613486702, 49696803124, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5987 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5987 = true := by
  decide +kernel

theorem tot5987 : totK PA10K2 A10K2.t5987 = [0, 0, 498028339174, 1802076636288, 1738120176241, 473368595438, 30650496230, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
