import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4848 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4848 = true := by
  decide +kernel

theorem tot4848 : totK PA10K2 A10K2.t4848 = [0, 490900728221, 1799779016691, 1880443602909, 528478151316, 32470943963, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4849 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4849 = true := by
  decide +kernel

theorem tot4849 : totK PA10K2 A10K2.t4849 = [0, 476655371750, 1682569061324, 1883984913091, 581114038045, 50267370225, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4850 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4850 = true := by
  decide +kernel

theorem tot4850 : totK PA10K2 A10K2.t4850 = [0, 129616538616, 1315508925464, 2288175257775, 848062511636, 58503570348, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4851 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4851 = true := by
  decide +kernel

theorem tot4851 : totK PA10K2 A10K2.t4851 = [306130628101, 1011477706390, 1194307774537, 1130113991612, 847335518406, 198982557272, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
